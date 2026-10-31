-- Prove2me | solution 1 for LargeCongestion.Poisson.proposition_6_b
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T09:37:34.548995+00:00
-- url     : https://prove2.me/submissions/3e915a74-4858-4eac-8ce1-39ffef9e2525

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_LargeCongestion_Poisson_PoissonCalculus
import Theorems.Thm_LargeCongestion_Poisson_proposition_5_b

open MeasureTheory ProbabilityTheory LargeCongestion.Poisson Filter Set
open scoped Topology

namespace LCPProp6bAux

lemma pmf_nonneg (x : ℝ) (k : ℕ) : 0 ≤ poissonPmf x k := measureReal_nonneg

lemma pmf_le (x d : ℝ) (hx : 0 ≤ x) (hxd : x ≤ d) (k : ℕ) :
    poissonPmf x k ≤ Real.exp (d - x) * poissonPmf d k := by
  rw [poissonPmf_eq hx, poissonPmf_eq (hx.trans hxd)]
  have hk : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
  have : Real.exp (d - x) * (Real.exp (-d) * d ^ k / k.factorial) =
      Real.exp (-x) * d ^ k / k.factorial := by
    rw [← mul_div_assoc, ← mul_assoc, ← Real.exp_add]; ring_nf
  rw [this]
  apply div_le_div_of_nonneg_right _ hk.le
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx hxd k) (Real.exp_pos _).le

/-- `∑ h(k) x^k/k!` with the constant term removed: `∑_{k} h(k+1) x^{k+1}/(k+1)!`. -/
noncomputable def F1 (h : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑' k : ℕ, h (k + 1) * x ^ (k + 1) / ((k + 1).factorial : ℝ)

/-- The termwise derivative `∑_{k} h(k+1) x^k/k!`. -/
noncomputable def G (h : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑' k : ℕ, h (k + 1) * x ^ k / (k.factorial : ℝ)

lemma summ_u {d : ℝ} (hd : 0 ≤ d) (h : ℕ → ℝ)
    (A : Summable (fun k => |h k| * poissonPmf d k)) :
    Summable (fun k : ℕ => |h k| * d ^ k / (k.factorial : ℝ)) := by
  have := A.mul_left (Real.exp d)
  refine this.congr (fun k => ?_)
  rw [poissonPmf_eq hd, Real.exp_neg]
  have := Real.exp_pos d
  field_simp

lemma term_bound {d y : ℝ} (hy : |y| ≤ d) (a : ℝ) (k : ℕ) :
    ‖a * y ^ k / (k.factorial : ℝ)‖ ≤ |a| * d ^ k / (k.factorial : ℝ) := by
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow, Nat.abs_cast]
  have hk : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
  apply div_le_div_of_nonneg_right _ hk.le
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hy k) (abs_nonneg _)

lemma F1_cont {d : ℝ} (hd : 0 ≤ d) (h : ℕ → ℝ) (A0 : Summable (fun k => |h k| * poissonPmf d k)) :
    ContinuousOn (F1 h) (Icc (-d) d) := by
  unfold F1
  refine continuousOn_tsum (u := fun k => |h (k + 1)| * d ^ (k + 1) / ((k + 1).factorial : ℝ))
    (fun k => by fun_prop) ((summable_nat_add_iff 1).2 (summ_u hd h A0)) (fun k y hy => ?_)
  exact term_bound (abs_le.2 ⟨by linarith [hy.1], hy.2⟩) _ _

lemma G_cont {d : ℝ} (hd : 0 ≤ d) (h : ℕ → ℝ)
    (A1 : Summable (fun k => |h (k + 1)| * poissonPmf d k)) :
    ContinuousOn (G h) (Icc (-d) d) := by
  unfold G
  refine continuousOn_tsum (u := fun k => |h (k + 1)| * d ^ k / (k.factorial : ℝ))
    (fun k => by fun_prop) (summ_u hd (fun k => h (k + 1)) A1) (fun k y hy => ?_)
  exact term_bound (abs_le.2 ⟨by linarith [hy.1], hy.2⟩) _ _

lemma F1_hasDerivAt {d : ℝ} (hd : 0 < d) (h : ℕ → ℝ)
    (A1 : Summable (fun k => |h (k + 1)| * poissonPmf d k)) (y : ℝ) (hy : y ∈ Ioo (-d) d) :
    HasDerivAt (F1 h) (G h y) y := by
  unfold F1 G
  refine hasDerivAt_tsum_of_isPreconnected (u := fun k => |h (k + 1)| * d ^ k / (k.factorial : ℝ))
    (g := fun n z => h (n + 1) * z ^ (n + 1) / ((n + 1).factorial : ℝ))
    (g' := fun n z => h (n + 1) * z ^ n / (n.factorial : ℝ))
    (summ_u hd.le (fun k => h (k + 1)) A1) isOpen_Ioo isPreconnected_Ioo ?_ ?_
    (y₀ := 0) ⟨by linarith, hd⟩ ?_ hy
  · intro n z _
    have := ((hasDerivAt_pow (n + 1) z).const_mul (h (n + 1))).div_const
      (((n + 1).factorial : ℕ) : ℝ)
    refine this.congr_deriv ?_
    rw [Nat.factorial_succ]
    have hk : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
    push_cast
    field_simp
  · intro n z hz
    exact term_bound (abs_lt.2 ⟨hz.1, hz.2⟩).le _ _
  · simp

lemma F1_hasDerivWithin {d : ℝ} (hd : 0 < d) (h : ℕ → ℝ)
    (A0 : Summable (fun k => |h k| * poissonPmf d k))
    (A1 : Summable (fun k => |h (k + 1)| * poissonPmf d k)) (x : ℝ) (hx : x ∈ Icc 0 d) :
    HasDerivWithinAt (F1 h) (G h x) (Icc 0 d) x := by
  rcases hx.2.lt_or_eq with hlt | heq
  · exact (F1_hasDerivAt hd h A1 x ⟨by linarith [hx.1], hlt⟩).hasDerivWithinAt
  · rw [heq]
    have hmem : Ioo (-d) d ∈ 𝓝[<] d := Ioo_mem_nhdsLT (by linarith)
    have hdiff : DifferentiableOn ℝ (F1 h) (Ioo (-d) d) := fun y hy =>
      (F1_hasDerivAt hd h A1 y hy).differentiableAt.differentiableWithinAt
    have hcont : ContinuousWithinAt (F1 h) (Ioo (-d) d) d :=
      ((F1_cont hd.le h A0) d ⟨by linarith, le_rfl⟩).mono Ioo_subset_Icc_self
    have hG : Tendsto (G h) (𝓝[<] d) (𝓝 (G h d)) := by
      have h1 : Tendsto (G h) (𝓝[Ioo (-d) d] d) (𝓝 (G h d)) :=
        (((G_cont hd.le h A1) d ⟨by linarith, le_rfl⟩).mono Ioo_subset_Icc_self).tendsto
      exact h1.mono_left (nhdsWithin_le_of_mem hmem)
    have hlim : Tendsto (fun y => deriv (F1 h) y) (𝓝[<] d) (𝓝 (G h d)) := by
      refine hG.congr' ?_
      filter_upwards [hmem] with y hy
      exact (F1_hasDerivAt hd h A1 y hy).deriv.symm
    exact (hasDerivWithinAt_Iic_of_tendsto_deriv hdiff hcont hmem hlim).mono (fun y hy => hy.2)

lemma summ_x {d x : ℝ} (hx : x ∈ Icc 0 d) (g : ℕ → ℝ)
    (A : Summable (fun k => |g k| * poissonPmf d k)) :
    Summable (fun k => g k * poissonPmf x k) := by
  refine Summable.of_norm_bounded (A.mul_left (Real.exp (d - x))) (fun k => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pmf_nonneg _ _)]
  calc |g k| * poissonPmf x k ≤ |g k| * (Real.exp (d - x) * poissonPmf d k) :=
        mul_le_mul_of_nonneg_left (pmf_le x d hx.1 hx.2 k) (abs_nonneg _)
    _ = Real.exp (d - x) * (|g k| * poissonPmf d k) := by ring

lemma pm_formula {d x : ℝ} (hd : 0 ≤ d) (hx : x ∈ Icc 0 d) (h : ℕ → ℝ)
    (A0 : Summable (fun k => |h k| * poissonPmf d k)) :
    poissonMean h x = Real.exp (-x) * (h 0 + F1 h x) := by
  have hs : Summable (fun k : ℕ => h k * x ^ k / (k.factorial : ℝ)) :=
    Summable.of_norm_bounded (summ_u hd h A0)
      (fun k => term_bound (abs_le.2 ⟨by linarith [hx.1], hx.2⟩) _ _)
  unfold poissonMean F1
  have e1 : (fun k : ℕ => h k * poissonPmf x k) =
      fun k => Real.exp (-x) * (h k * x ^ k / (k.factorial : ℝ)) := by
    funext k; rw [poissonPmf_eq hx.1]; ring
  rw [e1, tsum_mul_left, hs.tsum_eq_zero_add]
  simp

lemma pm_shift_formula {d x : ℝ} (hd : 0 ≤ d) (hx : x ∈ Icc 0 d) (h : ℕ → ℝ) :
    ∑' k, h (k + 1) * poissonPmf x k = Real.exp (-x) * G h x := by
  unfold G
  rw [← tsum_mul_left]
  congr 1; funext k
  rw [poissonPmf_eq hx.1]; ring

lemma D1 {d : ℝ} (hd : 0 < d) (h : ℕ → ℝ)
    (A0 : Summable (fun k => |h k| * poissonPmf d k))
    (AΔ : Summable (fun k => |delta h k| * poissonPmf d k)) :
    ∀ x ∈ Icc 0 d, HasDerivWithinAt (poissonMean h) (poissonMean (delta h) x) (Icc 0 d) x := by
  have A1 : Summable (fun k => |h (k + 1)| * poissonPmf d k) := by
    refine Summable.of_nonneg_of_le (fun k => mul_nonneg (abs_nonneg _) (pmf_nonneg _ _))
      (fun k => ?_) (AΔ.add A0)
    rw [← add_mul]
    refine mul_le_mul_of_nonneg_right ?_ (pmf_nonneg _ _)
    unfold delta
    calc |h (k + 1)| = |(h (k + 1) - h k) + h k| := by ring_nf
      _ ≤ _ := abs_add_le _ _
  intro x hx
  have hφ : HasDerivWithinAt (fun y => Real.exp (-y) * (h 0 + F1 h y))
      (Real.exp (-x) * (-1) * (h 0 + F1 h x) + Real.exp (-x) * G h x) (Icc 0 d) x := by
    have he : HasDerivAt (fun y => Real.exp (-y)) (Real.exp (-x) * (-1)) x :=
      (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
    exact he.hasDerivWithinAt.mul ((F1_hasDerivWithin hd h A0 A1 x hx).const_add (h 0))
  have hval : poissonMean (delta h) x =
      Real.exp (-x) * (-1) * (h 0 + F1 h x) + Real.exp (-x) * G h x := by
    have s1 : Summable (fun k => h (k + 1) * poissonPmf x k) := summ_x hx _ A1
    have s0 : Summable (fun k => h k * poissonPmf x k) := summ_x hx _ A0
    unfold poissonMean
    have e : (fun k => delta h k * poissonPmf x k) =
        fun k => h (k + 1) * poissonPmf x k - h k * poissonPmf x k := by
      funext k; unfold delta; ring
    rw [e, s1.tsum_sub s0, pm_shift_formula hd.le hx h]
    have := pm_formula hd.le hx h A0
    unfold poissonMean at this
    rw [this]; ring
  rw [hval]
  exact hφ.congr (fun y hy => pm_formula hd.le hy h A0) (pm_formula hd.le hx h A0)

lemma C0 {d : ℝ} (hd : 0 < d) (h : ℕ → ℝ) (A0 : Summable (fun k => |h k| * poissonPmf d k)) :
    ContinuousOn (poissonMean h) (Icc 0 d) := by
  have : ContinuousOn (fun y => Real.exp (-y) * (h 0 + F1 h y)) (Icc 0 d) := by
    have hF := (F1_cont hd.le h A0).mono (Icc_subset_Icc (by linarith : -d ≤ 0) le_rfl)
    exact (Real.continuous_exp.comp continuous_neg).continuousOn.mul
      (continuousOn_const.add hF)
  exact this.congr (fun y hy => pm_formula hd.le hy h A0)

lemma main {d : ℝ} (hd : 0 < d) : ∀ (j : ℕ) (h : ℕ → ℝ),
    (∀ i ≤ j, Summable (fun k => |deltaPow i h k| * poissonPmf d k)) →
    ContDiffOn ℝ j (poissonMean h) (Icc 0 d) ∧
      ∀ x ∈ Icc 0 d, iteratedDerivWithin j (poissonMean h) (Icc 0 d) x =
        poissonMean (deltaPow j h) x := by
  intro j
  induction j with
  | zero =>
    intro h hA
    have A0 : Summable (fun k => |h k| * poissonPmf d k) := by
      simpa [deltaPow] using hA 0 le_rfl
    refine ⟨?_, ?_⟩
    · rw [Nat.cast_zero, contDiffOn_zero]; exact C0 hd h A0
    · intro x _; simp [iteratedDerivWithin_zero, deltaPow]
  | succ j ih =>
    intro h hA
    have A0 : Summable (fun k => |h k| * poissonPmf d k) := by
      simpa [deltaPow] using hA 0 (Nat.zero_le _)
    have AΔ : Summable (fun k => |delta h k| * poissonPmf d k) := by
      simpa [deltaPow] using hA 1 (by omega)
    have hA' : ∀ i ≤ j, Summable (fun k => |deltaPow i (delta h) k| * poissonPmf d k) := by
      intro i hi
      have := hA (i + 1) (by omega)
      simpa only [deltaPow, Function.iterate_succ_apply] using this
    obtain ⟨ihC, ihD⟩ := ih (delta h) hA'
    have hder := D1 hd h A0 AΔ
    have hU : UniqueDiffOn ℝ (Icc 0 d) := uniqueDiffOn_Icc hd
    have heq : ∀ x ∈ Icc 0 d, derivWithin (poissonMean h) (Icc 0 d) x = poissonMean (delta h) x :=
      fun x hx => (hder x hx).derivWithin (hU x hx)
    refine ⟨?_, ?_⟩
    · have hc : ((j + 1 : ℕ) : WithTop ℕ∞) = (j : WithTop ℕ∞) + 1 := by push_cast; rfl
      rw [hc, contDiffOn_succ_iff_derivWithin hU]
      refine ⟨fun x hx => (hder x hx).differentiableWithinAt, fun h' => ?_, ihC.congr heq⟩
      exact absurd h' (by simp)
    · intro x hx
      rw [iteratedDerivWithin_succ', iteratedDerivWithin_congr heq hx, ihD x hx]
      simp only [deltaPow, Function.iterate_succ_apply]

lemma summable_of_moment (g : ℕ → ℝ) (x : ℝ) (j : ℕ)
    (hm : Summable (fun k : ℕ => (k : ℝ) ^ j * |g k| * poissonPmf x k)) :
    Summable (fun k : ℕ => |g k| * poissonPmf x k) := by
  rw [← summable_nat_add_iff 1]
  have hm' := (summable_nat_add_iff 1).2 hm
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (abs_nonneg _) (pmf_nonneg _ _))
    (fun k => ?_) hm'
  have h1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) ^ j :=
    one_le_pow₀ (by push_cast; linarith [k.cast_nonneg (α := ℝ)])
  have h2 : 0 ≤ |g (k + 1)| * poissonPmf x (k + 1) := mul_nonneg (abs_nonneg _) (pmf_nonneg _ _)
  calc |g (k + 1)| * poissonPmf x (k + 1) ≤
      ((k + 1 : ℕ) : ℝ) ^ j * (|g (k + 1)| * poissonPmf x (k + 1)) := le_mul_of_one_le_left h2 h1
    _ = ((k + 1 : ℕ) : ℝ) ^ j * |g (k + 1)| * poissonPmf x (k + 1) := by ring

lemma moment_mono (g : ℕ → ℝ) (x : ℝ) (i j : ℕ) (hij : i ≤ j)
    (hm : Summable (fun k : ℕ => (k : ℝ) ^ j * |g k| * poissonPmf x k)) :
    Summable (fun k : ℕ => (k : ℝ) ^ i * |g k| * poissonPmf x k) := by
  rw [← summable_nat_add_iff 1] at hm ⊢
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (mul_nonneg (by positivity)
    (abs_nonneg _)) (pmf_nonneg _ _)) (fun k => ?_) hm
  have h1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by push_cast; linarith [k.cast_nonneg (α := ℝ)]
  have h2 : ((k + 1 : ℕ) : ℝ) ^ i ≤ ((k + 1 : ℕ) : ℝ) ^ j := pow_le_pow_right₀ h1 hij
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 (abs_nonneg _))
    (pmf_nonneg _ _)

end LCPProp6bAux

open LCPProp6bAux in
theorem solution (h : ℕ → ℝ) (dmax : ℝ) (hd : 0 < dmax) (j : ℕ)
    (hint : Summable (fun k : ℕ => |deltaPow j h k| * poissonPmf dmax k)) :
    ContDiffOn ℝ j (poissonMean h) (Set.Icc 0 dmax) ∧
      ∀ x ∈ Set.Icc 0 dmax,
        iteratedDerivWithin j (poissonMean h) (Set.Icc 0 dmax) x =
          poissonMean (deltaPow j h) x := by
  apply main hd j h
  intro i hi
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · subst hj0
    have : i = 0 := by omega
    subst this; exact hint
  · have hj1 := (proposition_5_b h dmax hd.le j hjpos).1.1 hint
    have hmomj := (proposition_5_b h dmax hd.le j hjpos).2.1 hj1
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · subst hi0
      simpa [deltaPow] using summable_of_moment h dmax j hmomj
    · have hmomi := moment_mono h dmax i j hi hmomj
      have hshi := (proposition_5_b h dmax hd.le i hipos).2.2 hmomi
      exact (proposition_5_b h dmax hd.le i hipos).1.2 hshi
