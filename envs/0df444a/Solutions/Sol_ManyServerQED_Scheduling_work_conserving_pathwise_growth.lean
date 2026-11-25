-- Prove2me | solution 1 for ManyServerQED.Scheduling.work_conserving_pathwise_growth
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T18:17:51.911813+00:00
-- url     : https://prove2.me/submissions/a321499a-69e0-4b68-a71a-d00ae9f6b3a7

import Definitions.Def_ManyServerQED_Scheduling_Diffusion
import Theorems.Thm_TeschlODE_IVP_gronwall_generalized

open Function MeasureTheory Filter Topology
open Set intervalIntegral
open ManyServerQED.Scheduling

private noncomputable def damped (a : ℝ) (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-a * t) * ∫ s in (0 : ℝ)..t, Real.exp (a * s) * w s

private theorem damped_continuousOn (a : ℝ) (w : ℝ → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hw : IntervalIntegrable w volume 0 T) : ContinuousOn (damped a w) (Icc 0 T) := by
  have h : IntervalIntegrable (fun s => Real.exp (a * s) * w s) volume 0 T :=
    hw.continuousOn_mul (by fun_prop)
  unfold damped
  refine ContinuousOn.mul (by fun_prop) ?_
  simpa only [uIcc_of_le hT] using
    continuousOn_primitive_interval' h (left_mem_uIcc (a := (0 : ℝ)) (b := T))

private theorem damped_integral_eq (a : ℝ) (w : ℝ → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hw : IntervalIntegrable w volume 0 t) :
    damped a w t = ∫ s in (0 : ℝ)..t, (w s - a * damped a w s) := by
  let w' (s : ℝ) := Real.exp (a * s) * w s
  let pr (s : ℝ) := ∫ u in (0 : ℝ)..s, w' u
  let expo (s : ℝ) := Real.exp (-a * s)
  have hw' : IntervalIntegrable w' volume 0 t := hw.continuousOn_mul (by fun_prop)
  have hpr : AbsolutelyContinuousOnInterval pr 0 t :=
    hw'.absolutelyContinuousOnInterval_intervalIntegral (c := 0) left_mem_uIcc
  have he : AbsolutelyContinuousOnInterval expo 0 t :=
    (show ContDiff ℝ 1 expo by dsimp [expo]; fun_prop).contDiffOn.absolutelyContinuousOnInterval
  have hprod : AbsolutelyContinuousOnInterval (damped a w) 0 t := he.fun_mul hpr
  have hd := hprod.integral_deriv_eq_sub
  have heq :
      (∫ s in (0 : ℝ)..t, deriv (damped a w) s) =
        ∫ s in (0 : ℝ)..t, (w s - a * damped a w s) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hw'.ae_hasDerivAt_integral] with s hs hs'
    have hh : HasDerivAt pr (w' s) s := hs (uIoc_subset_uIcc hs') 0 left_mem_uIcc
    have he' : HasDerivAt expo ((-a) * expo s) s := by
      simpa only [expo, id_eq, mul_one, mul_comm (Real.exp (-a * s)) (-a)] using
        (((hasDerivAt_id s).const_mul (-a)).exp)
    have dh := (he'.mul hh).deriv
    change deriv (damped a w) s = _
    change deriv (damped a w) s = _ at dh
    rw [dh]
    have hcancel : expo s * Real.exp (a * s) = 1 := by
      dsimp [expo]
      rw [← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero]
    change -a * expo s * pr s + expo s * (Real.exp (a * s) * w s) =
      w s - a * (expo s * pr s)
    rw [← mul_assoc (expo s), hcancel, one_mul]
    ring
  rw [heq, show damped a w 0 = 0 by simp [damped], sub_zero] at hd
  exact hd.symm

private theorem damped_bound (a : ℝ) (ha : 0 ≤ a) (w : ℝ → ℝ) (t B : ℝ)
    (ht : 0 ≤ t) (hB : ∀ s ∈ Icc 0 t, |w s| ≤ B) : |damped a w t| ≤ B * t := by
  have hrepr : damped a w t = ∫ s in (0 : ℝ)..t, Real.exp (-a * (t - s)) * w s := by
    unfold damped
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only
    rw [← mul_assoc, ← Real.exp_add]
    ring_nf
  rw [hrepr, ← Real.norm_eq_abs]
  calc
    _ ≤ B * |t - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro s hs
      rw [uIoc_of_le ht] at hs
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
      refine (mul_le_of_le_one_left (abs_nonneg (w s)) ?_).trans (hB s ⟨hs.1.le, hs.2⟩)
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha)
        (sub_nonneg.mpr hs.2))
    _ = _ := by rw [sub_zero, abs_of_nonneg ht]


private theorem damped_unique (a : ℝ) (ha : 0 ≤ a) (w y : ℝ → ℝ)
    (T : ℝ) (hT : 0 ≤ T)
    (hw : ∀ t ∈ Icc 0 T, IntervalIntegrable w volume 0 t)
    (hy : ∀ t ∈ Icc 0 T, IntervalIntegrable y volume 0 t)
    (hEq : ∀ t ∈ Icc 0 T, y t = ∫ s in (0 : ℝ)..t, (w s - a * y s)) :
    ∀ t ∈ Icc 0 T, y t = damped a w t := by
  let z (t : ℝ) := y t - damped a w t
  have hx : ContinuousOn (damped a w) (Icc 0 T) := damped_continuousOn a w T hT (hw T ⟨hT, le_rfl⟩)
  have hz (t : ℝ) (ht : t ∈ Icc 0 T) : IntervalIntegrable z volume 0 t := by
    exact (hy t ht).sub ((hx.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1)
  have hs (t : ℝ) (ht : t ∈ Icc 0 T) : z t = -a * ∫ s in (0 : ℝ)..t, z s := by
    have hd : IntervalIntegrable (damped a w) volume 0 t :=
      (hx.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
    dsimp only [z]
    rw [damped_integral_eq a w t ht.1 (hw t ht), hEq t ht,
      intervalIntegral.integral_sub (hw t ht) ((hy t ht).const_mul a),
      intervalIntegral.integral_sub (hw t ht) (hd.const_mul a),
      intervalIntegral.integral_sub (hy t ht) hd]
    simp only [intervalIntegral.integral_const_mul]
    ring
  have hc' : ContinuousOn (fun t => ∫ s in (0 : ℝ)..t, z s) (Icc 0 T) := by
    simpa only [uIcc_of_le hT] using
      continuousOn_primitive_interval' (hz T ⟨hT, le_rfl⟩) (left_mem_uIcc (a := (0 : ℝ)) (b := T))
  have hc : ContinuousOn z (Icc 0 T) :=
    (continuousOn_const.mul hc').congr hs
  have hd : ContinuousOn (fun t => |z t|) (Icc 0 T) := hc.abs
  have hi (t : ℝ) (ht : t ∈ Icc 0 T) :
      |z t| ≤ 0 + ∫ s in (0 : ℝ)..t, a * |z s| := by
    rw [hs t ht, abs_mul, abs_neg, abs_of_nonneg ha, zero_add, intervalIntegral.integral_const_mul]
    exact mul_le_mul_of_nonneg_left (intervalIntegral.abs_integral_le_integral_abs ht.1) ha
  have hg := TeschlODE.IVP.gronwall_generalized (fun t => |z t|) (fun _ => 0) (fun _ => a)
    T hd continuousOn_const continuousOn_const (fun _ _ => ha) hi
  intro t ht
  have hb := hg.2 (fun _ _ _ _ _ => le_rfl) t ht
  have hzero : z t = 0 := abs_eq_zero.mp (le_antisymm (by simpa using hb) (abs_nonneg _))
  exact sub_eq_zero.mp hzero

private theorem damped_forcing_sign (a : ℝ) (ha : 0 ≤ a) (b : ℝ) (q y : ℝ → ℝ)
    (T : ℝ) (hT : 0 ≤ T)
    (hq : ∀ t ∈ Icc 0 T, IntervalIntegrable q volume 0 t)
    (hy : ∀ t ∈ Icc 0 T, IntervalIntegrable y volume 0 t)
    (hqn : ∀ t ∈ Icc 0 T, 0 ≤ q t)
    (hEq : ∀ t ∈ Icc 0 T, y t = ∫ s in (0 : ℝ)..t, (b * q s - a * y s)) :
    ∀ t ∈ Icc 0 T, (0 ≤ b → 0 ≤ y t) ∧ (b ≤ 0 → y t ≤ 0) := by
  intro t ht
  have hsol := damped_unique a ha (fun s => b * q s) y T hT (fun s hs => (hq s hs).const_mul b) hy hEq
    t ht
  have heq : y t = b * (Real.exp (-a * t) * ∫ s in (0 : ℝ)..t, Real.exp (a * s) * q s) := by
    rw [hsol, damped]
    have hint : (∫ s in (0 : ℝ)..t, Real.exp (a * s) * (b * q s)) =
        b * ∫ s in (0 : ℝ)..t, Real.exp (a * s) * q s := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro s _
      dsimp only
      ring
    rw [hint]
    ring
  have hp : 0 ≤ Real.exp (-a * t) * ∫ s in (0 : ℝ)..t, Real.exp (a * s) * q s :=
    mul_nonneg (Real.exp_nonneg _) (intervalIntegral.integral_nonneg ht.1 fun s hs =>
      mul_nonneg (Real.exp_nonneg _) (hqn s ⟨hs.1, hs.2.trans ht.2⟩))
  rw [heq]
  exact ⟨fun hb => mul_nonneg hb hp, fun hb => mul_nonpos_of_nonpos_of_nonneg hb hp⟩

theorem solution {k : ℕ} (μ θ : Fin k → ℝ) (a : ℝ) (ha : 0 < a)
    (hμ : ∀ i, 0 < μ i) (hμa : ∀ i, μ i ≤ a) (hθ : ∀ i, 0 ≤ θ i) (hθa : ∀ i, θ i ≤ a)
    (x w q : ℝ → Fin k → ℝ) (T B : ℝ) (hT : 0 ≤ T) (hB : 0 ≤ B)
    (hint : ∀ t ∈ Icc 0 T, ∀ i,
      IntervalIntegrable (fun s => x s i) volume 0 t ∧
      IntervalIntegrable (fun s => w s i) volume 0 t ∧
      IntervalIntegrable (fun s => q s i) volume 0 t)
    (hqn : ∀ t ∈ Icc 0 T, ∀ i, 0 ≤ q t i)
    (hq : ∀ t ∈ Icc 0 T, (∑ i, q t i) = max (∑ i, x t i) 0)
    (hw : ∀ t ∈ Icc 0 T, l1norm (w t) ≤ B)
    (hEq : ∀ t ∈ Icc 0 T, ∀ i, x t i = w t i +
      ∫ s in (0 : ℝ)..t, ((μ i - θ i) * q s i - μ i * x s i)) :
    ∀ t ∈ Icc 0 T, l1norm (x t) ≤ (k : ℝ) * (1 + a * T) ^ 2 * B := by
  let J (s : ℝ) (i : Fin k) : ℝ := damped (μ i) (fun t => w t i) s
  let v (s : ℝ) (i : Fin k) : ℝ := w s i - μ i * J s i
  let y (s : ℝ) (i : Fin k) : ℝ := x s i - v s i
  have hJ (t : ℝ) (ht : t ∈ Icc 0 T) (i : Fin k) :
      J t i = ∫ s in (0 : ℝ)..t, v s i :=
    damped_integral_eq _ _ t ht.1 (hint t ht i).2.1
  have hv_int (t : ℝ) (ht : t ∈ Icc 0 T) (i : Fin k) :
      IntervalIntegrable (fun s => v s i) volume 0 t := by
    have h := damped_continuousOn (μ i) (fun s => w s i) t ht.1 (hint t ht i).2.1
    exact (hint t ht i).2.1.sub ((h.intervalIntegrable_of_Icc ht.1).const_mul (μ i))
  have hy_int (t : ℝ) (ht : t ∈ Icc 0 T) (i : Fin k) :
      IntervalIntegrable (fun s => y s i) volume 0 t :=
    (hint t ht i).1.sub (hv_int t ht i)
  have hy_eq (t : ℝ) (ht : t ∈ Icc 0 T) (i : Fin k) :
      y t i = ∫ s in (0 : ℝ)..t, ((μ i - θ i) * q s i - μ i * y s i) := by
    have hE := hEq t ht i
    rw [intervalIntegral.integral_sub ((hint t ht i).2.2.const_mul _) ((hint t ht i).1.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hE
    simp only [y]
    rw [intervalIntegral.integral_sub ((hint t ht i).2.2.const_mul _) ((hy_int t ht i).const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    rw [show (∫ s in (0 : ℝ)..t, y s i) =
      (∫ s in (0 : ℝ)..t, x s i) - ∫ s in (0 : ℝ)..t, v s i from
        intervalIntegral.integral_sub (hint t ht i).1 (hv_int t ht i)]
    rw [← hJ t ht i]
    dsimp only [v]
    linarith
  have hsign (s : ℝ) (hs : s ∈ Icc 0 T) (i : Fin k) :
      (0 ≤ μ i - θ i → 0 ≤ y s i) ∧ (μ i - θ i ≤ 0 → y s i ≤ 0) :=
    damped_forcing_sign (μ i) (hμ i).le (μ i - θ i) (fun t => q t i) (fun t => y t i) T hT
      (fun t ht => (hint t ht i).2.2) (fun t ht => hy_int t ht i)
      (fun t ht => hqn t ht i) (fun t ht => hy_eq t ht i) s hs
  let c (i : Fin k) : ℝ := if 0 ≤ μ i - θ i then 1 / μ i else -(1 / a)
  let pos (s : ℝ) (i : Fin k) : ℝ := if 0 ≤ μ i - θ i then y s i else 0
  let D (s : ℝ) (i : Fin k) : ℝ := (μ i - θ i) * q s i - μ i * y s i
  have hnorm_y (s : ℝ) (hs : s ∈ Icc 0 T) (i : Fin k) : |y s i| ≤ a * (c i * y s i) := by
    by_cases h : 0 ≤ μ i - θ i
    · have hy := (hsign s hs i).1 h
      rw [abs_of_nonneg hy, show c i = 1 / μ i from if_pos h, ← mul_assoc, mul_one_div]
      exact le_mul_of_one_le_left hy ((one_le_div (hμ i)).2 (hμa i))
    · have hy := (hsign s hs i).2 (le_of_not_ge h)
      rw [abs_of_nonpos hy, show c i = -(1 / a) from if_neg h]
      field_simp [ha.ne']; rfl
  have hcomp (s : ℝ) (hs : s ∈ Icc 0 T) (i : Fin k) :
      c i * D s i ≤ q s i - pos s i := by
    by_cases h : 0 ≤ μ i - θ i
    · rw [show c i = 1 / μ i from if_pos h, show pos s i = y s i from if_pos h]
      dsimp only [D]
      have hn := mul_nonneg (hθ i) (hqn s hs i)
      rw [one_div, ← div_eq_inv_mul]
      apply (div_le_iff₀ (hμ i)).2
      nlinarith
    · rw [show c i = -(1 / a) from if_neg h, show pos s i = 0 from if_neg h, sub_zero]
      dsimp only [D]
      have hy := (hsign s hs i).2 (le_of_not_ge h)
      have hprod := mul_nonpos_of_nonneg_of_nonpos (hμ i).le hy
      have hle := mul_le_mul_of_nonneg_right (hθa i) (hqn s hs i)
      have hprod' := mul_nonneg (hμ i).le (hqn s hs i)
      calc
        _ = (-((μ i - θ i) * q s i - μ i * y s i)) / a := by ring
        _ ≤ _ := (div_le_iff₀ ha).2 (by nlinarith)
  have hpos (s : ℝ) (hs : s ∈ Icc 0 T) (i : Fin k) :
      0 ≤ pos s i ∧ y s i ≤ pos s i := by
    unfold pos
    split_ifs with h
    · exact ⟨(hsign s hs i).1 h, le_rfl⟩
    · exact ⟨le_rfl, (hsign s hs i).2 (le_of_not_ge h)⟩
  have hmax (s : ℝ) (hs : s ∈ Icc 0 T) :
      (∑ i, q s i) ≤ (∑ i, pos s i) + l1norm (v s) := by
    rw [hq s hs]
    apply max_le
    · calc
        (∑ i, x s i) ≤ ∑ i, (pos s i + |v s i|) := by
          apply Finset.sum_le_sum
          intro i _
          have h := (hpos s hs i).2
          dsimp only [y] at h
          linarith [le_abs_self (v s i)]
        _ = _ := by simp only [Finset.sum_add_distrib, l1norm]
    · exact add_nonneg (Finset.sum_nonneg (fun i _ => (hpos s hs i).1))
        (Finset.sum_nonneg (fun i _ => abs_nonneg (v s i)))
  have hdrift (s : ℝ) (hs : s ∈ Icc 0 T) :
      ∑ i, c i * D s i ≤ l1norm (v s) := by
    calc
      _ ≤ ∑ i, (q s i - pos s i) := Finset.sum_le_sum (fun i _ => hcomp s hs i)
      _ ≤ _ := by rw [Finset.sum_sub_distrib]; linarith [hmax s hs]
  have hvbound (s : ℝ) (hs : s ∈ Icc 0 T) : l1norm (v s) ≤ (k : ℝ) * (1 + a * T) * B := by
    have hi (i : Fin k) : |v s i| ≤ (1 + a * T) * B := by
      have hwi (u : ℝ) (hu : u ∈ Icc 0 s) : |w u i| ≤ B :=
        (Finset.single_le_sum (fun j _ => abs_nonneg (w u j)) (Finset.mem_univ i)).trans
          (hw u ⟨hu.1, hu.2.trans hs.2⟩)
      have hji : |J s i| ≤ B * T :=
        (damped_bound (μ i) (hμ i).le (fun s => w s i) s B hs.1 hwi).trans
          (mul_le_mul_of_nonneg_left hs.2 hB)
      have hprod : |μ i * J s i| ≤ a * (B * T) := by
        rw [abs_mul, abs_of_pos (hμ i)]
        exact mul_le_mul (hμa i) hji (abs_nonneg _) ha.le
      have habs : |v s i| ≤ |w s i| + |μ i * J s i| := by
        dsimp only [v]
        simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (w s i) (-(μ i * J s i))
      nlinarith [hwi s ⟨hs.1, le_rfl⟩]
    calc
      _ ≤ ∑ _i : Fin k, (1 + a * T) * B := Finset.sum_le_sum (fun i _ => hi i)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]
  let L := (k : ℝ) * (1 + a * T) * B
  intro t ht
  have hlint (i : Fin k) : IntervalIntegrable (fun s => c i * D s i) volume 0 t :=
    (((hint t ht i).2.2.const_mul _).sub ((hy_int t ht i).const_mul _)).const_mul _
  have hWeight : (∑ i, c i * y t i) = ∫ s in (0 : ℝ)..t, (∑ i, c i * D s i) := by
    rw [intervalIntegral.integral_finsetSum (fun i _ => hlint i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [intervalIntegral.integral_const_mul, hy_eq t ht i]
  have hsum_int : IntervalIntegrable (fun s => ∑ i, c i * D s i) volume 0 t := by
    have heq : (fun s => ∑ i, c i * D s i) = ∑ i, (fun s => c i * D s i) := by
      funext s
      rw [Finset.sum_apply]
    rw [heq]
    exact IntervalIntegrable.sum Finset.univ (fun i _ => hlint i)
  have hW : (∑ i, c i * y t i) ≤ L * T := by
    rw [hWeight]
    have he := intervalIntegral.integral_mono_on ht.1 hsum_int
      (intervalIntegrable_const (c := L)) (fun s hs => by
        have hsT : s ∈ Icc 0 T := ⟨hs.1, hs.2.trans ht.2⟩
        exact (hdrift s hsT).trans (hvbound s hsT))
    rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at he
    have hl : 0 ≤ L := by dsimp [L]; positivity
    exact he.trans ((mul_le_mul_of_nonneg_right ht.2 hl).trans_eq (mul_comm T L))
  have hy_bound : l1norm (y t) ≤ a * (L * T) := by
    calc
      _ ≤ ∑ i, a * (c i * y t i) := Finset.sum_le_sum (fun i _ => hnorm_y t ht i)
      _ = a * ∑ i, c i * y t i := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hW ha.le
  calc
    l1norm (x t) ≤ l1norm (y t) + l1norm (v t) := by
      unfold l1norm
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i _
      have he : x t i = y t i + v t i := by dsimp only [y]; ring
      nth_rw 1 [he]
      exact abs_add_le _ _
    _ ≤ a * (L * T) + L := add_le_add hy_bound (hvbound t ht)
    _ = _ := by dsimp [L]; ring
