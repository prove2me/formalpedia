-- Prove2me | solution 1 for LeastSquaresTD.Absorbing.lemma5_lstd_limit
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T06:56:23.003929+00:00
-- url     : https://prove2.me/submissions/5c9f069d-fa8c-4058-ad89-aecf7a258d2b

import Definitions.Def_LeastSquaresTD_Absorbing_Estimator

open MeasureTheory Filter Topology

namespace LeastSquaresTD.Absorbing

namespace LLNAux

/-- deterministic interpolation -/
lemma interp (s : ℕ → ℝ) (hs : ∀ k, |s (k+1) - s k| ≤ 1)
    (h : ∀ r : ℕ, ∀ᶠ n : ℕ in atTop, |s ((n+1)^2)| ≤ (1 / ((r:ℝ)+1)) * ((n+1)^2 : ℕ)) :
    Tendsto (fun m : ℕ => s m / m) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨r, hr⟩ := exists_nat_gt (4 / ε)
  have hr' : 1 / ((r:ℝ)+1) < ε / 4 := by
    rw [div_lt_iff₀ (by positivity)]
    have : 4 / ε < r + 1 := by linarith
    rw [div_lt_iff₀ hε] at this
    nlinarith
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 (h r)
  obtain ⟨N2, hN2⟩ := exists_nat_gt (8 / ε)
  refine ⟨(max N1 N2 + 1)^2, fun m hm => ?_⟩
  set n := Nat.sqrt m with hn
  have hnm : n * n ≤ m := Nat.sqrt_le m
  have hmn : m < (n+1)*(n+1) := Nat.lt_succ_sqrt m
  have hnge : max N1 N2 + 1 ≤ n := by
    rw [hn]; apply Nat.le_sqrt'.2; exact hm
  have hn1 : N1 ≤ n - 1 := by omega
  have hn0 : 1 ≤ n := by omega
  -- write n = k + 1
  obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hk1 : N1 ≤ k := by omega
  have hbase := hN1 k hk1
  -- |s m - s (n^2)| ≤ m - n^2
  have hdiff : ∀ j d, |s (j + d) - s j| ≤ d := by
    intro j d
    induction d with
    | zero => simp
    | succ d ih =>
      have := hs (j + d)
      calc |s (j + (d+1)) - s j| = |(s (j + d + 1) - s (j+d)) + (s (j+d) - s j)| := by
            congr 1; rw [← add_assoc]; ring
        _ ≤ |s (j + d + 1) - s (j+d)| + |s (j+d) - s j| := abs_add_le _ _
        _ ≤ 1 + d := add_le_add this ih
        _ = ((d+1 : ℕ) : ℝ) := by push_cast; ring
  have hm' : m = (k+1)^2 + (m - (k+1)^2) := by
    have : (k+1)^2 ≤ m := by rw [← hk]; nlinarith
    omega
  have hd := hdiff ((k+1)^2) (m - (k+1)^2)
  rw [← hm'] at hd
  have hdle : ((m - (k+1)^2 : ℕ) : ℝ) ≤ 2 * (k+1) := by
    have : m - (k+1)^2 ≤ 2 * (k+1) := by
      have : m < (k+1+1)*(k+1+1) := by rw [← hk]; exact hmn
      nlinarith
    exact_mod_cast this
  have hmpos : (0:ℝ) < m := by
    have : 0 < m := by nlinarith
    exact_mod_cast this
  have hsm : |s m| ≤ (1 / ((r:ℝ)+1)) * ((k+1)^2 : ℕ) + 2 * (k+1) := by
    have : |s m| ≤ |s ((k+1)^2)| + |s m - s ((k+1)^2)| := by
      calc |s m| = |s ((k+1)^2) + (s m - s ((k+1)^2))| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    linarith
  have hk2 : (((k+1)^2 : ℕ) : ℝ) ≤ m := by
    have : (k+1)^2 ≤ m := by rw [← hk]; nlinarith
    exact_mod_cast this
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hmpos, div_lt_iff₀ hmpos]
  have hkr : 8 / ε < k + 1 := by
    have : (N2:ℝ) ≤ k := by exact_mod_cast (by omega : N2 ≤ k)
    linarith
  have hk8 : 8 < ε * (k+1) := by
    rw [div_lt_iff₀ hε] at hkr; linarith
  have hkpos : (0:ℝ) < k + 1 := by positivity
  have hcast : (((k+1)^2 : ℕ) : ℝ) = ((k:ℝ)+1)^2 := by push_cast; ring
  rw [hcast] at hsm hk2
  have hc1 : 1 / ((r:ℝ)+1) * ((k:ℝ)+1)^2 ≤ ε / 4 * m := by
    calc 1 / ((r:ℝ)+1) * ((k:ℝ)+1)^2 ≤ ε/4 * ((k:ℝ)+1)^2 :=
          mul_le_mul_of_nonneg_right hr'.le (by positivity)
      _ ≤ ε / 4 * m := mul_le_mul_of_nonneg_left hk2 (by positivity)
  have hc2 : 2 * ((k:ℝ)+1) ≤ ε / 4 * ((k:ℝ)+1)^2 := by
    nlinarith
  have hc3 : ε / 4 * ((k:ℝ)+1)^2 ≤ ε / 4 * m := mul_le_mul_of_nonneg_left hk2 (by positivity)
  calc |s m| ≤ _ := hsm
    _ ≤ ε / 4 * m + ε / 4 * m := by linarith
    _ < ε * m := by nlinarith

variable {Ω : Type*} [MeasurableSpace Ω]

/-- abstract martingale LLN with second-moment bound -/
lemma lln_abstract (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : ℕ → Ω → ℝ)
    (hb : ∀ k ω, |ξ k ω| ≤ 1) (hm : ∀ n, Measurable (fun ω => ∑ k ∈ Finset.range n, ξ k ω))
    (h2 : ∀ n, ∫ ω, (∑ k ∈ Finset.range n, ξ k ω)^2 ∂μ ≤ n) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, ξ k ω) / n) atTop (𝓝 0) := by
  set s : ℕ → Ω → ℝ := fun n ω => ∑ k ∈ Finset.range n, ξ k ω with hs
  have hsb : ∀ n ω, |s n ω| ≤ n := by
    intro n ω
    simp only [hs]
    calc |∑ k ∈ Finset.range n, ξ k ω| ≤ ∑ k ∈ Finset.range n, |ξ k ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range n, (1:ℝ) := Finset.sum_le_sum (fun k _ => hb k ω)
      _ = n := by simp
  have hint : ∀ n, Integrable (fun ω => (s n ω)^2) μ := by
    intro n
    refine Integrable.of_bound (C := (n:ℝ)^2) ((hm n).pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => ?_))
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hsb n ω) 2
  have key : ∀ r : ℕ, ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop,
      |s ((n+1)^2) ω| ≤ (1 / ((r:ℝ)+1)) * ((n+1)^2 : ℕ) := by
    intro r
    set ε : ℝ := 1 / ((r:ℝ)+1) with hε
    have hε0 : 0 < ε := by positivity
    set E : ℕ → Set Ω := fun n => {ω | (ε * ((n+1)^2 : ℕ))^2 ≤ (s ((n+1)^2) ω)^2} with hE
    have hEb : ∀ n, μ (E n) ≤ ENNReal.ofReal (1 / (ε^2 * ((n:ℝ)+1)^2)) := by
      intro n
      have hmk := mul_meas_ge_le_integral_of_nonneg (μ := μ)
        (f := fun ω => (s ((n+1)^2) ω)^2) (Filter.Eventually.of_forall (fun ω => sq_nonneg _))
        (hint ((n+1)^2)) ((ε * ((n+1)^2 : ℕ))^2)
      have hI := h2 ((n+1)^2)
      have hpos : (0:ℝ) < (ε * ((n+1)^2 : ℕ))^2 := by positivity
      have hreal : μ.real (E n) ≤ 1 / (ε^2 * ((n:ℝ)+1)^2) := by
        have h3 : (ε * ((n+1)^2 : ℕ))^2 * μ.real (E n) ≤ (((n+1)^2 : ℕ) : ℝ) := le_trans hmk hI
        have hc : (((n+1)^2 : ℕ) : ℝ) = ((n:ℝ)+1)^2 := by push_cast; ring
        rw [hc] at h3
        rw [hc] at hpos
        have : (ε * ((n:ℝ)+1)^2)^2 = ε^2 * ((n:ℝ)+1)^2 * ((n:ℝ)+1)^2 := by ring
        rw [this] at h3
        rw [le_div_iff₀ (by positivity)]
        have hn2 : (0:ℝ) < ((n:ℝ)+1)^2 := by positivity
        refine le_of_mul_le_mul_left ?_ hn2
        nlinarith [h3]
      calc μ (E n) = ENNReal.ofReal (μ.real (E n)) := (ofReal_measureReal (measure_ne_top _ _)).symm
        _ ≤ _ := ENNReal.ofReal_le_ofReal hreal
    have hsum : Summable (fun n : ℕ => 1 / (ε^2 * ((n:ℝ)+1)^2)) := by
      have := (Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num)
      have h1 := (summable_nat_add_iff 1).2 this
      have h2' := h1.mul_left (1 / ε^2)
      refine h2'.congr (fun n => ?_)
      push_cast
      field_simp
    have htsum : ∑' n, μ (E n) ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hEb)
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum]
      exact ENNReal.ofReal_ne_top
    filter_upwards [ae_eventually_notMem htsum] with ω hω
    filter_upwards [hω] with n hn
    simp only [hE, Set.mem_setOf_eq, not_le] at hn
    have : |s ((n+1)^2) ω| < ε * ((n+1)^2 : ℕ) := by
      apply abs_lt_of_sq_lt_sq _ (by positivity)
      exact hn
    exact this.le
  have hall := ae_all_iff.2 key
  filter_upwards [hall] with ω hω
  exact interp (fun n => s n ω) (fun k => by
    simp only [hs, Finset.sum_range_succ, add_sub_cancel_left]; exact hb k ω) hω

end LLNAux


section MC
open Matrix

variable {X Ω : Type*} [Fintype X] [DecidableEq X] [MeasurableSpace X] [MeasurableSingletonClass X]
  [MeasurableSpace Ω]

noncomputable def qw (C : Chain X) (S : X → ℝ) {n : ℕ} (xs : Fin (n+1) → X) : ℝ :=
  S (xs 0) * ∏ i : Fin n, C.P (xs i.castSucc) (xs i.succ)

lemma qw_nonneg (C : Chain X) (S : X → ℝ) (hS : ∀ x, 0 ≤ S x) {n : ℕ} (xs : Fin (n+1) → X) :
    0 ≤ qw C S xs :=
  mul_nonneg (hS _) (Finset.prod_nonneg (fun i _ => C.nonneg _ _))

lemma qw_snoc (C : Chain X) (S : X → ℝ) {n : ℕ} (xs : Fin (n+1) → X) (y : X) :
    qw C S (Fin.snoc xs y : Fin (n+2) → X) = qw C S xs * C.P (xs (Fin.last n)) y := by
  unfold qw
  rw [Fin.prod_univ_castSucc]
  have h0 : (Fin.snoc xs y : Fin (n+2) → X) 0 = xs 0 := by
    have := Fin.snoc_castSucc (α := fun _ => X) (p := xs) (x := y) (0 : Fin (n+1))
    simpa using this
  rw [h0]
  have h1 : ∀ i : Fin n, C.P ((Fin.snoc xs y : Fin (n+2) → X) i.castSucc.castSucc)
      ((Fin.snoc xs y : Fin (n+2) → X) i.castSucc.succ) = C.P (xs i.castSucc) (xs i.succ) := by
    intro i
    rw [Fin.snoc_castSucc, Fin.succ_castSucc, Fin.snoc_castSucc]
  simp only [h1]
  have h2 : (Fin.snoc xs y : Fin (n+2) → X) (Fin.last n).castSucc = xs (Fin.last n) :=
    Fin.snoc_castSucc (α := fun _ => X) (p := xs) (x := y) (Fin.last n)
  have h3 : (Fin.snoc xs y : Fin (n+2) → X) (Fin.last n).succ = y := by
    rw [Fin.succ_last]; exact Fin.snoc_last (α := fun _ => X) (p := xs) (x := y)
  rw [h2, h3]; ring

/-- the path vector -/
def pathV (Z : ℕ → Ω → X) (n : ℕ) (ω : Ω) : Fin (n+1) → X := fun i => Z i ω

lemma pathV_measurable {Z : ℕ → Ω → X} (hZ : ∀ n, Measurable (Z n)) (n : ℕ) :
    Measurable (pathV Z n) :=
  measurable_pi_iff.2 (fun i => hZ i)

variable (C : Chain X) (S : X → ℝ) (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : ℕ → Ω → X)

lemma path_real (hS : ∀ x, 0 ≤ S x) (hlaw : HasChainLaw C S μ Z) {n : ℕ} (xs : Fin (n+1) → X) :
    μ.real {ω | pathV Z n ω = xs} = qw C S xs := by
  have h := hlaw.2 n xs
  have : {ω | pathV Z n ω = xs} = {ω | ∀ i : Fin (n + 1), Z i ω = xs i} := by
    ext ω; simp [pathV, funext_iff]
  rw [this, Measure.real, h]
  exact ENNReal.toReal_ofReal (qw_nonneg C S hS xs)

lemma integrable_path (hZ : ∀ n, Measurable (Z n)) {n : ℕ} (F : (Fin (n+1) → X) → ℝ) :
    Integrable (fun ω => F (pathV Z n ω)) μ := by
  have hF : Measurable F := measurable_of_finite F
  have hb : ∃ B, ∀ v, |F v| ≤ B := by
    obtain ⟨B, hB⟩ := (Set.finite_range F).bddAbove
    obtain ⟨B', hB'⟩ := (Set.finite_range F).bddBelow
    exact ⟨max B (-B'), fun v => abs_le.2 ⟨by
      have := hB' ⟨v, rfl⟩; have := le_max_right B (-B'); linarith, by
      have := hB ⟨v, rfl⟩; have := le_max_left B (-B'); linarith⟩⟩
  obtain ⟨B, hB⟩ := hb
  exact Integrable.of_bound (C := B) (hF.comp (pathV_measurable hZ n)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ω => by rw [Real.norm_eq_abs]; exact hB _))

lemma integral_path (hS : ∀ x, 0 ≤ S x) (hlaw : HasChainLaw C S μ Z) {n : ℕ}
    (F : (Fin (n+1) → X) → ℝ) :
    ∫ ω, F (pathV Z n ω) ∂μ = ∑ xs, F xs * qw C S xs := by
  have hZ := hlaw.1
  have hV := pathV_measurable hZ n
  have hF : Measurable F := measurable_of_finite F
  rw [← integral_map hV.aemeasurable hF.aestronglyMeasurable]
  haveI : IsProbabilityMeasure (μ.map (pathV Z n)) := Measure.isProbabilityMeasure_map hV.aemeasurable
  rw [integral_fintype Integrable.of_finite]
  apply Finset.sum_congr rfl
  intro xs _
  rw [smul_eq_mul, mul_comm]
  congr 1
  rw [Measure.real, Measure.map_apply hV (measurableSet_singleton xs)]
  rw [← path_real C S μ Z hS hlaw xs]
  rfl


lemma orth (hS : ∀ x, 0 ≤ S x) (hlaw : HasChainLaw C S μ Z) (n : ℕ)
    (g : (Fin (n+1) → X) → ℝ) (h : X → X → ℝ) (hh : ∀ a, ∑ y, C.P a y * h a y = 0) :
    ∫ ω, g (pathV Z n ω) * h (Z n ω) (Z (n+1) ω) ∂μ = 0 := by
  set F : (Fin (n+2) → X) → ℝ := fun ys =>
    g (fun i => ys i.castSucc) * h (ys (Fin.last n).castSucc) (ys (Fin.last (n+1))) with hF
  have h1 : (fun ω => g (pathV Z n ω) * h (Z n ω) (Z (n+1) ω)) =
      fun ω => F (pathV Z (n+1) ω) := by
    funext ω; simp [hF, pathV]; exact Or.inl rfl
  rw [h1, integral_path C S μ Z hS hlaw]
  rw [← Equiv.sum_comp (Fin.snocEquiv (fun _ : Fin (n+2) => X))]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro xs _
  have h2 : ∀ y : X, F (Fin.snocEquiv (fun _ : Fin (n+2) => X) (y, xs)) *
      qw C S (Fin.snocEquiv (fun _ : Fin (n+2) => X) (y, xs)) =
      g xs * qw C S xs * (C.P (xs (Fin.last n)) y * h (xs (Fin.last n)) y) := by
    intro y
    have e : Fin.snocEquiv (fun _ : Fin (n+2) => X) (y, xs) = (Fin.snoc xs y : Fin (n+2) → X) := rfl
    rw [e, qw_snoc]
    simp only [hF]
    have e1 : (fun i : Fin (n+1) => (Fin.snoc xs y : Fin (n+2) → X) i.castSucc) = xs := by
      funext i; exact Fin.snoc_castSucc (α := fun _ => X) (p := xs) (x := y) i
    have e2 : (Fin.snoc xs y : Fin (n+2) → X) (Fin.last n).castSucc = xs (Fin.last n) :=
      Fin.snoc_castSucc (α := fun _ => X) (p := xs) (x := y) (Fin.last n)
    have e3 : (Fin.snoc xs y : Fin (n+2) → X) (Fin.last (n+1)) = y :=
      Fin.snoc_last (α := fun _ => X) (p := xs) (x := y)
    rw [e1, e2, e3]; ring
  simp_rw [h2]
  rw [← Finset.mul_sum, hh, mul_zero]

lemma xi_meas (hZ : ∀ n, Measurable (Z n)) (h : X → X → ℝ) (k : ℕ) :
    Measurable (fun ω => h (Z k ω) (Z (k+1) ω)) :=
  (measurable_of_finite (fun p : X × X => h p.1 p.2)).comp ((hZ k).prodMk (hZ (k+1)))

lemma S_meas (hZ : ∀ n, Measurable (Z n)) (h : X → X → ℝ) (n : ℕ) :
    Measurable (fun ω => ∑ k ∈ Finset.range n, h (Z k ω) (Z (k+1) ω)) :=
  Finset.measurable_sum _ (fun k _ => xi_meas Z hZ h k)

lemma S_bound (h : X → X → ℝ) (hb : ∀ a b, |h a b| ≤ 1) (n : ℕ) (ω : Ω) :
    |∑ k ∈ Finset.range n, h (Z k ω) (Z (k+1) ω)| ≤ n := by
  calc _ ≤ ∑ k ∈ Finset.range n, |h (Z k ω) (Z (k+1) ω)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range n, (1:ℝ) := Finset.sum_le_sum (fun k _ => hb _ _)
    _ = n := by simp

lemma second_moment (hS : ∀ x, 0 ≤ S x) (hlaw : HasChainLaw C S μ Z) (h : X → X → ℝ)
    (hh : ∀ a, ∑ y, C.P a y * h a y = 0) (hb : ∀ a b, |h a b| ≤ 1) (n : ℕ) :
    ∫ ω, (∑ k ∈ Finset.range n, h (Z k ω) (Z (k+1) ω))^2 ∂μ ≤ n := by
  have hZ := hlaw.1
  induction n with
  | zero => simp
  | succ n ih =>
    set Sn : Ω → ℝ := fun ω => ∑ k ∈ Finset.range n, h (Z k ω) (Z (k+1) ω) with hSn
    set xi : Ω → ℝ := fun ω => h (Z n ω) (Z (n+1) ω) with hxi
    have hSm : Measurable Sn := S_meas Z hZ h n
    have hxm : Measurable xi := xi_meas Z hZ h n
    have hxb : ∀ ω, |xi ω| ≤ 1 := fun ω => hb _ _
    have hSb : ∀ ω, |Sn ω| ≤ n := S_bound Z h hb n
    have i1 : Integrable (fun ω => (Sn ω)^2) μ :=
      Integrable.of_bound (C := (n:ℝ)^2) (hSm.pow_const 2).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun ω => by
          rw [Real.norm_eq_abs, abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hSb ω) 2))
    have i2 : Integrable (fun ω => Sn ω * xi ω) μ :=
      Integrable.of_bound (C := (n:ℝ) * 1) (hSm.mul hxm).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun ω => by
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul (hSb ω) (hxb ω) (abs_nonneg _) (Nat.cast_nonneg _)))
    have i3 : Integrable (fun ω => (xi ω)^2) μ :=
      Integrable.of_bound (C := 1) (hxm.pow_const 2).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun ω => by
          rw [Real.norm_eq_abs, abs_pow]; exact pow_le_one₀ (abs_nonneg _) (hxb ω)))
    have e0 : ∫ ω, Sn ω * xi ω ∂μ = 0 := by
      let g : (Fin (n+1) → X) → ℝ := fun xs => ∑ k : Fin n, h (xs k.castSucc) (xs k.succ)
      have : ∀ ω, Sn ω = g (pathV Z n ω) := by
        intro ω
        simp only [hSn, g, pathV]
        rw [← Fin.sum_univ_eq_sum_range (fun k => h (Z k ω) (Z (k+1) ω)) n]
        simp
      simp_rw [this]
      exact orth C S μ Z hS hlaw n g h hh
    have e1 : ∫ ω, (xi ω)^2 ∂μ ≤ 1 := by
      calc ∫ ω, (xi ω)^2 ∂μ ≤ ∫ _ω, (1:ℝ) ∂μ :=
            integral_mono i3 (integrable_const _) (fun ω => by
              show (xi ω)^2 ≤ 1
              exact pow_le_one₀ (abs_nonneg _) (hxb ω) |>.trans' (by rw [sq_abs]))
        _ = 1 := by simp
    have : (fun ω => (∑ k ∈ Finset.range (n+1), h (Z k ω) (Z (k+1) ω))^2) =
        fun ω => (Sn ω)^2 + 2 * (Sn ω * xi ω) + (xi ω)^2 := by
      funext ω
      rw [Finset.sum_range_succ]; simp only [hSn, hxi]; ring
    have iA : Integrable (fun ω => (Sn ω)^2 + 2 * (Sn ω * xi ω)) μ := i1.add (i2.const_mul 2)
    have k1 : ∫ ω, ((Sn ω)^2 + 2 * (Sn ω * xi ω) + (xi ω)^2) ∂μ =
        ∫ ω, ((Sn ω)^2 + 2 * (Sn ω * xi ω)) ∂μ + ∫ ω, (xi ω)^2 ∂μ := integral_add iA i3
    have k2 : ∫ ω, ((Sn ω)^2 + 2 * (Sn ω * xi ω)) ∂μ =
        ∫ ω, (Sn ω)^2 ∂μ + ∫ ω, 2 * (Sn ω * xi ω) ∂μ := integral_add i1 (i2.const_mul 2)
    have k3 : ∫ ω, 2 * (Sn ω * xi ω) ∂μ = 2 * ∫ ω, Sn ω * xi ω ∂μ := integral_const_mul _ _
    rw [this, k1, k2, k3, e0]
    push_cast
    linarith


end MC


section DET
open Matrix

variable {X : Type*} [Fintype X] [DecidableEq X] {m : ℕ}

noncomputable def pcnt (z : ℕ → X) (n : ℕ) (x y : X) : ℕ :=
  ((Finset.range n).filter (fun k => z k = x ∧ z (k+1) = y)).card

lemma sum_pairs {M : Type*} [AddCommMonoid M] [Module ℝ M] (f : X → X → M) (z : ℕ → X) (n : ℕ) :
    ∑ k ∈ Finset.range n, f (z k) (z (k+1)) = ∑ x, ∑ y, (pcnt z n x y : ℝ) • f x y := by
  have h1 : ∀ k, f (z k) (z (k+1)) = ∑ x, ∑ y, if z k = x ∧ z (k+1) = y then f x y else 0 := by
    intro k
    rw [Finset.sum_eq_single (z k)]
    · rw [Finset.sum_eq_single (z (k+1))]
      · simp
      · intro y _ hy; simp [Ne.symm hy]
      · simp
    · intro x _ hx; simp [Ne.symm hx]
    · simp
  simp_rw [h1]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro y _
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const]
  unfold pcnt
  rw [Nat.cast_smul_eq_nsmul]

lemma limitMatrix_apply (C : Chain X) (φ : X → Fin m → ℝ) (γ : ℝ) (π : X → ℝ) (i j : Fin m) :
    limitMatrix C φ γ π i j =
      ∑ x, φ x i * π x * (φ x j - γ * ∑ y, C.P x y * φ y j) := by
  unfold limitMatrix
  simp only [Matrix.mul_assoc]
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl; intro x _
  rw [Matrix.diagonal_mul, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
  have : ∑ a, (1 - γ • C.P) x a * Matrix.of φ a j = φ x j - γ * ∑ y, C.P x y * φ y j := by
    simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply,
      sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, mul_assoc, Finset.mul_sum]
  rw [this]; ring

lemma limitMatrix_eq (C : Chain X) (φ : X → Fin m → ℝ) (γ : ℝ) (π : X → ℝ) :
    ∑ x, ∑ y, (π x * C.P x y) • Matrix.vecMulVec (φ x) (φ x - γ • φ y) = limitMatrix C φ γ π := by
  ext i j
  rw [limitMatrix_apply]
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl; intro x _
  have : ∀ y, π x * C.P x y * (φ x i * (φ x j - γ * φ y j)) =
      π x * φ x i * (C.P x y * φ x j) - π x * φ x i * γ * (C.P x y * φ y j) := by
    intro y; ring
  simp_rw [this, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul, C.row_sum x,
    one_mul]
  ring

lemma limitVector_eq (C : Chain X) (R : X → X → ℝ) (φ : X → Fin m → ℝ) (π : X → ℝ) :
    ∑ x, ∑ y, (π x * C.P x y) • (R x y • φ x) = limitVector C R φ π := by
  ext i
  unfold limitVector
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply,
    Matrix.diagonal_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Chain.rbar]
  apply Finset.sum_congr rfl; intro x _
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_ite, mul_zero]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro y _
  ring

lemma inv_smul_field (c : ℝ) (hc : c ≠ 0) (M : Matrix (Fin m) (Fin m) ℝ) (h : M.det ≠ 0) :
    (c • M)⁻¹ = c⁻¹ • M⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hc, one_smul]
  exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 h)

lemma theta_tendsto (C : Chain X) (R : X → X → ℝ) (φ : X → Fin m → ℝ) (γ : ℝ) (π : X → ℝ)
    (z : ℕ → X)
    (hpair : ∀ x y, Tendsto (fun n : ℕ => (pcnt z n x y : ℝ) / n) atTop (𝓝 (π x * C.P x y)))
    (hunit : IsUnit (limitMatrix C φ γ π)) :
    Tendsto (fun n => chainLstdTheta R φ γ z n) atTop
      (𝓝 (Matrix.mulVec (limitMatrix C φ γ π)⁻¹ (limitVector C R φ π))) := by
  set At : ℕ → Matrix (Fin m) (Fin m) ℝ := fun n => (n:ℝ)⁻¹ • chainLstdA φ γ z n with hAt
  set Bt : ℕ → Fin m → ℝ := fun n => (n:ℝ)⁻¹ • chainLstdB R φ z n with hBt
  have hA : Tendsto At atTop (𝓝 (limitMatrix C φ γ π)) := by
    rw [← limitMatrix_eq]
    have : At = fun n => ∑ x, ∑ y, ((pcnt z n x y : ℝ) / n) • Matrix.vecMulVec (φ x) (φ x - γ • φ y) := by
      funext n
      simp only [hAt, chainLstdA]
      rw [sum_pairs (fun x y => Matrix.vecMulVec (φ x) (φ x - γ • φ y)) z n, Finset.smul_sum]
      apply Finset.sum_congr rfl; intro x _
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl; intro y _
      rw [smul_smul, div_eq_inv_mul]
    rw [this]
    refine tendsto_finset_sum _ (fun x _ => tendsto_finset_sum _ (fun y _ => ?_))
    exact (hpair x y).smul tendsto_const_nhds
  have hB : Tendsto Bt atTop (𝓝 (limitVector C R φ π)) := by
    rw [← limitVector_eq]
    have : Bt = fun n => ∑ x, ∑ y, ((pcnt z n x y : ℝ) / n) • (R x y • φ x) := by
      funext n
      simp only [hBt, chainLstdB]
      rw [sum_pairs (fun x y => R x y • φ x) z n, Finset.smul_sum]
      apply Finset.sum_congr rfl; intro x _
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl; intro y _
      rw [smul_smul, div_eq_inv_mul]
    rw [this]
    refine tendsto_finset_sum _ (fun x _ => tendsto_finset_sum _ (fun y _ => ?_))
    exact (hpair x y).smul tendsto_const_nhds
  have hdet : Tendsto (fun n => (At n).det) atTop (𝓝 (limitMatrix C φ γ π).det) :=
    ((continuous_id.matrix_det).tendsto _).comp hA
  have hdet0 : (limitMatrix C φ γ π).det ≠ 0 :=
    (isUnit_iff_ne_zero).1 ((Matrix.isUnit_iff_isUnit_det _).1 hunit)
  have hev : ∀ᶠ n : ℕ in atTop, (At n).det ≠ 0 := hdet.eventually_ne hdet0
  have hinv : Tendsto (fun n => (At n)⁻¹) atTop (𝓝 (limitMatrix C φ γ π)⁻¹) := by
    have hc : ContinuousAt Inv.inv (limitMatrix C φ γ π) := by
      apply continuousAt_matrix_inv
      have : ContinuousAt (fun r : ℝ => r⁻¹) (limitMatrix C φ γ π).det := continuousAt_inv₀ hdet0
      rw [Ring.inverse_eq_inv']
      exact this
    exact hc.tendsto.comp hA
  have hfin : Tendsto (fun n => Matrix.mulVec (At n)⁻¹ (Bt n)) atTop
      (𝓝 (Matrix.mulVec (limitMatrix C φ γ π)⁻¹ (limitVector C R φ π))) := by
    have hcont : Continuous (fun p : Matrix (Fin m) (Fin m) ℝ × (Fin m → ℝ) => Matrix.mulVec p.1 p.2) :=
      continuous_fst.matrix_mulVec continuous_snd
    exact (hcont.tendsto _).comp (hinv.prodMk_nhds hB)
  refine hfin.congr' ?_
  filter_upwards [hev, eventually_gt_atTop 0] with n hn hn0
  have hn' : (n:ℝ) ≠ 0 := by positivity
  have hA' : chainLstdA φ γ z n = (n:ℝ) • At n := by
    simp only [hAt, smul_smul, mul_inv_cancel₀ hn', one_smul]
  have hB' : chainLstdB R φ z n = (n:ℝ) • Bt n := by
    simp only [hBt, smul_smul, mul_inv_cancel₀ hn', one_smul]
  unfold chainLstdTheta
  rw [hA', inv_smul_field _ hn' _ hn, Matrix.smul_mulVec]
  have hBn : Bt n = (n:ℝ)⁻¹ • chainLstdB R φ z n := rfl
  rw [hBn, Matrix.mulVec_smul]

end DET

section PairAE
open Matrix

variable {X Ω : Type*} [Fintype X] [DecidableEq X] [MeasurableSpace X] [MeasurableSingletonClass X]
  [MeasurableSpace Ω]

lemma P_le_one (C : Chain X) (x y : X) : C.P x y ≤ 1 := by
  have := Finset.single_le_sum (f := fun y => C.P x y) (fun y _ => C.nonneg x y) (Finset.mem_univ y)
  simpa [C.row_sum x] using this

lemma pair_ae (C : Chain X) (S : X → ℝ) (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : ℕ → Ω → X)
    (hS : ∀ x, 0 ≤ S x) (hlaw : HasChainLaw C S μ Z) (π : X → ℝ)
    (hfreq : ∀ᵐ ω ∂μ, ∀ x,
      Tendsto (fun n => chainOutFrequency (fun k => Z k ω) x n) atTop (𝓝 (π x))) :
    ∀ᵐ ω ∂μ, ∀ x y, Tendsto (fun n : ℕ => (pcnt (fun k => Z k ω) n x y : ℝ) / n) atTop
      (𝓝 (π x * C.P x y)) := by
  have hZ := hlaw.1
  have key : ∀ x y : X, ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ =>
      (pcnt (fun k => Z k ω) n x y : ℝ) / n) atTop
      (𝓝 (C.P x y * (π x))) ∨ ¬ Tendsto (fun n => chainOutFrequency (fun k => Z k ω) x n) atTop (𝓝 (π x)) := by
    intro x y
    set h : X → X → ℝ := fun a b => if a = x then ((if b = y then 1 else 0) - C.P x y) else 0 with hh
    have hb : ∀ a b, |h a b| ≤ 1 := by
      intro a b
      simp only [hh]
      split_ifs
      · rw [abs_le]; have := C.nonneg x y; have := P_le_one C x y; constructor <;> linarith
      · rw [abs_le]; have := C.nonneg x y; have := P_le_one C x y; constructor <;> linarith
      · simp
    have hh0 : ∀ a, ∑ b, C.P a b * h a b = 0 := by
      intro a
      simp only [hh]
      split_ifs with ha
      · subst ha
        simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq' Finset.univ y (fun b => C.P a b)]
        rw [← Finset.sum_mul, C.row_sum a]
        simp
      · simp
    have hlln := LLNAux.lln_abstract μ (fun k ω => h (Z k ω) (Z (k+1) ω))
      (fun k ω => hb _ _) (S_meas Z hZ h) (second_moment C S μ Z hS hlaw h hh0 hb)
    filter_upwards [hlln] with ω hω
    by_cases hf : Tendsto (fun n => chainOutFrequency (fun k => Z k ω) x n) atTop (𝓝 (π x))
    · left
      have e : ∀ n : ℕ, (pcnt (fun k => Z k ω) n x y : ℝ) / n =
          (∑ k ∈ Finset.range n, h (Z k ω) (Z (k+1) ω)) / n +
            C.P x y * chainOutFrequency (fun k => Z k ω) x n := by
        intro n
        have : ∑ k ∈ Finset.range n, h (Z k ω) (Z (k+1) ω) =
            (pcnt (fun k => Z k ω) n x y : ℝ) - C.P x y *
              (((Finset.range n).filter (fun k => Z k ω = x)).card : ℝ) := by
          have : ∀ k, h (Z k ω) (Z (k+1) ω) =
              (if Z k ω = x ∧ Z (k+1) ω = y then (1:ℝ) else 0) -
                C.P x y * (if Z k ω = x then (1:ℝ) else 0) := by
            intro k
            simp only [hh]
            by_cases h1 : Z k ω = x <;> by_cases h2 : Z (k+1) ω = y <;> simp [h1, h2]
          simp_rw [this]
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole, Finset.sum_boole]
          rfl
        rw [this]
        unfold chainOutFrequency
        ring
      have : Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, h (Z k ω) (Z (k+1) ω)) / n +
            C.P x y * chainOutFrequency (fun k => Z k ω) x n) atTop (𝓝 (0 + C.P x y * π x)) :=
        hω.add (hf.const_mul _)
      rw [zero_add] at this
      exact this.congr (fun n => (e n).symm)
    · right; exact hf
  have hall : ∀ᵐ ω ∂μ, ∀ x y, Tendsto (fun n : ℕ => (pcnt (fun k => Z k ω) n x y : ℝ) / n) atTop
      (𝓝 (C.P x y * (π x))) ∨ ¬ Tendsto (fun n => chainOutFrequency (fun k => Z k ω) x n) atTop (𝓝 (π x)) :=
    ae_all_iff.2 (fun x => ae_all_iff.2 (fun y => key x y))
  filter_upwards [hall, hfreq] with ω h1 h2 x y
  rcases h1 x y with h | h
  · rw [mul_comm]; exact h
  · exact absurd (h2 x) h

end PairAE

variable {m : ℕ}

theorem lemma5_core
    {X Ω : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    [MeasurableSpace X] [MeasurableSingletonClass X] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (C : Chain X) (S : X → ℝ) (R : X → X → ℝ)
    (φ : X → Fin m → ℝ) (γ : ℝ) (π : X → ℝ) (Z : ℕ → Ω → X)
    (hS_nonneg : ∀ x, 0 ≤ S x)
    (hlaw : HasChainLaw C S μ Z)
    (hfreq : ∀ᵐ ω ∂μ, ∀ x,
      Tendsto (fun n => chainOutFrequency (fun k => Z k ω) x n) atTop (𝓝 (π x)))
    (hunit : IsUnit (limitMatrix C φ γ π)) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n => chainLstdTheta R φ γ (fun k => Z k ω) n)
      atTop (𝓝 (Matrix.mulVec (limitMatrix C φ γ π)⁻¹
        (limitVector C R φ π))) := by
  filter_upwards [pair_ae C S μ Z hS_nonneg hlaw π hfreq] with ω hω
  exact theta_tendsto C R φ γ π _ hω hunit

end LeastSquaresTD.Absorbing

open LeastSquaresTD.Absorbing
variable {m : ℕ}

theorem solution
    {X Ω : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    [MeasurableSpace X] [MeasurableSingletonClass X] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (C : Chain X) (S : X → ℝ) (R : X → X → ℝ)
    (φ : X → Fin m → ℝ) (γ : ℝ) (π : X → ℝ) (Z : ℕ → Ω → X)
    (hS_nonneg : ∀ x, 0 ≤ S x) (hS_sum : ∑ x, S x = 1)
    (hlaw : HasChainLaw C S μ Z)
    (hvisits : ∀ᵐ ω ∂μ, ∀ (x : X) (N : ℕ), ∃ n ≥ N, Z n ω = x)
    (hfreq : ∀ᵐ ω ∂μ, ∀ x,
      Tendsto (fun n => chainOutFrequency (fun k => Z k ω) x n) atTop (𝓝 (π x)))
    (hunit : IsUnit (limitMatrix C φ γ π)) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n => chainLstdTheta R φ γ (fun k => Z k ω) n)
      atTop (𝓝 (Matrix.mulVec (limitMatrix C φ γ π)⁻¹
        (limitVector C R φ π))) := by
  exact lemma5_core μ C S R φ γ π Z hS_nonneg hlaw hfreq hunit
