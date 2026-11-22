-- Prove2me | solution 1 for KingRockAsymp.Distribution.theorem_A3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T20:14:40.106265+00:00
-- url     : https://prove2.me/submissions/db13bd5c-70d1-4cd1-89fa-b9429454e6ad

import Mathlib
import Definitions.Def_KingRockAsymp_Distribution_Basic
import Theorems.Thm_KingRockAsymp_Distribution_proposition_A1

open Set Filter Topology Metric MeasureTheory ProbabilityTheory
open KingRockAsymp.Distribution
open scoped ENNReal NNReal BoundedContinuousFunction

noncomputable section

/-! ### Part 1: Elementary exponential and Bernstein tail bounds -/

private lemma real_exp_le_one_add_add_sq {u : ℝ} (hu : |u| ≤ 1) :
    Real.exp u ≤ 1 + u + u ^ 2 := by
  have h1 : ‖(u : ℂ)‖ ≤ 1 := by simpa [Complex.norm_real] using hu
  have h2 := Complex.exp_bound_sq 0 (u : ℂ) h1
  simp only [zero_add, Complex.exp_zero, smul_eq_mul, mul_one, norm_one, one_mul] at h2
  have h3 : ‖Complex.exp (u : ℂ) - 1 - (u : ℂ)‖ = |Real.exp u - 1 - u| := by
    rw [← Complex.ofReal_exp, ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
  rw [h3, Complex.norm_real, Real.norm_eq_abs, sq_abs] at h2
  linarith [(abs_le.mp h2).2]

private lemma bernstein_mgf_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {ν : ℕ} (hν : 1 ≤ ν) {d σ2 c : ℝ} (hd : 0 < d) (hσ2 : 0 ≤ σ2)
    (hc : |c| = (2 * d)⁻¹)
    {X : Fin ν → Ω → ℝ}
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X P)
    (hX_mean : ∀ i, ∫ ω, X i ω ∂P = 0)
    (hX_bdd : ∀ i ω, |X i ω| ≤ 2 * d)
    (hX_var : ∀ i, ∫ ω, (X i ω) ^ 2 ∂P ≤ σ2 * d ^ 2 / (ν : ℝ)) :
    ∫ ω, Real.exp (c * ∑ i : Fin ν, X i ω) ∂P ≤ Real.exp (σ2 / 4) := by
  have hprod_eq : (fun ω => Real.exp (c * ∑ i : Fin ν, X i ω)) =
      fun ω => ∏ i : Fin ν, Real.exp (c * X i ω) := by
    ext ω
    rw [Finset.mul_sum, Real.exp_sum]
  rw [hprod_eq]
  have hindep_exp : iIndepFun (fun i ω => Real.exp (c * X i ω)) P :=
    hX_indep.comp (fun _ x => Real.exp (c * x)) (fun _ => by fun_prop)
  have hmeas_exp : ∀ i, AEStronglyMeasurable (fun ω => Real.exp (c * X i ω)) P :=
    fun i => ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.comp
      (hX_meas i)).aestronglyMeasurable
  rw [hindep_exp.integral_fun_prod_eq_prod_integral hmeas_exp]
  have hfactor : ∀ i : Fin ν,
      ∫ ω, Real.exp (c * X i ω) ∂P ≤ Real.exp (σ2 / (4 * (ν : ℝ))) := by
    intro i
    have hpt : ∀ ω, Real.exp (c * X i ω) ≤ 1 + c * X i ω + (c * X i ω) ^ 2 := by
      intro ω
      apply real_exp_le_one_add_add_sq
      rw [abs_mul, hc]
      calc (2 * d)⁻¹ * |X i ω| ≤ (2 * d)⁻¹ * (2 * d) := by
            gcongr; exact hX_bdd i ω
        _ = 1 := inv_mul_cancel₀ (by positivity)
    have hint_exp : Integrable (fun ω => Real.exp (c * X i ω)) P := by
      refine Integrable.of_bound (hmeas_exp i) (Real.exp 1) (ae_of_all _ fun ω => ?_)
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      apply Real.exp_le_exp.mpr
      calc c * X i ω ≤ |c * X i ω| := le_abs_self _
        _ = (2 * d)⁻¹ * |X i ω| := by rw [abs_mul, hc]
        _ ≤ (2 * d)⁻¹ * (2 * d) := by gcongr; exact hX_bdd i ω
        _ = 1 := inv_mul_cancel₀ (by positivity)
    have hint_X : Integrable (X i) P :=
      Integrable.of_bound (hX_meas i).aestronglyMeasurable (2 * d)
        (ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using hX_bdd i ω)
    have hint_X2 : Integrable (fun ω => (X i ω) ^ 2) P :=
      Integrable.of_bound ((hX_meas i).pow_const 2).aestronglyMeasurable ((2 * d) ^ 2)
        (ae_of_all _ fun ω => by
          rw [Real.norm_of_nonneg (sq_nonneg _), ← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hX_bdd i ω) 2)
    have h1 : Integrable (fun _ : Ω => (1 : ℝ)) P := integrable_const 1
    have h2 : Integrable (fun ω => c * X i ω) P := hint_X.const_mul c
    have h3 : Integrable (fun ω => (c * X i ω) ^ 2) P := by
      have h3' : Integrable (fun ω => c ^ 2 * (X i ω) ^ 2) P := hint_X2.const_mul (c ^ 2)
      exact h3'.congr (ae_of_all _ fun ω => (mul_pow c (X i ω) 2).symm)
    have h12 : Integrable (fun ω => 1 + c * X i ω) P := h1.add h2
    have hint_rhs : Integrable (fun ω => 1 + c * X i ω + (c * X i ω) ^ 2) P := h12.add h3
    calc ∫ ω, Real.exp (c * X i ω) ∂P
        ≤ ∫ ω, (1 + c * X i ω + (c * X i ω) ^ 2) ∂P :=
          integral_mono hint_exp hint_rhs hpt
      _ = (∫ _ : Ω, (1 : ℝ) ∂P) + c * (∫ ω, X i ω ∂P) + c ^ 2 * (∫ ω, (X i ω) ^ 2 ∂P) := by
          rw [integral_add h12 h3, integral_add h1 h2, integral_const_mul]
          have h3_eq : ∫ ω, (c * X i ω) ^ 2 ∂P = c ^ 2 * ∫ ω, (X i ω) ^ 2 ∂P := by
            simp_rw [mul_pow]; exact integral_const_mul _ _
          rw [h3_eq]
      _ = 1 + c ^ 2 * (∫ ω, (X i ω) ^ 2 ∂P) := by
          simp [hX_mean i]
      _ ≤ 1 + c ^ 2 * (σ2 * d ^ 2 / (ν : ℝ)) := by
          gcongr; exact hX_var i
      _ = 1 + σ2 / (4 * (ν : ℝ)) := by
          have hc2 : c ^ 2 = (4 * d ^ 2)⁻¹ := by
            rw [← sq_abs, hc, inv_pow]; ring
          rw [hc2]
          field_simp
      _ ≤ Real.exp (σ2 / (4 * (ν : ℝ))) := by
          linarith [Real.add_one_le_exp (σ2 / (4 * (ν : ℝ)))]
  calc ∏ i : Fin ν, ∫ ω, Real.exp (c * X i ω) ∂P
      ≤ ∏ _i : Fin ν, Real.exp (σ2 / (4 * (ν : ℝ))) := by
        apply Finset.prod_le_prod
        · intro i _
          exact integral_nonneg fun ω => (Real.exp_pos _).le
        · intro i _; exact hfactor i
    _ = Real.exp (σ2 / (4 * (ν : ℝ))) ^ ν := by simp
    _ = Real.exp ((ν : ℝ) * (σ2 / (4 * (ν : ℝ)))) := by rw [← Real.exp_nat_mul]
    _ = Real.exp (σ2 / 4) := by
        have hν0 : (ν : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        congr 1; field_simp

private lemma bernstein_exp_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {ν : ℕ} (hν : 1 ≤ ν) {d σ2 : ℝ} (hd : 0 < d) (hσ2 : 0 ≤ σ2)
    {X : Fin ν → Ω → ℝ}
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X P)
    (hX_mean : ∀ i, ∫ ω, X i ω ∂P = 0)
    (hX_bdd : ∀ i ω, |X i ω| ≤ 2 * d)
    (hX_var : ∀ i, ∫ ω, (X i ω) ^ 2 ∂P ≤ σ2 * d ^ 2 / (ν : ℝ))
    (t : ℝ) :
    P {ω | t ≤ |∑ i : Fin ν, X i ω|} ≤
      ENNReal.ofReal (2 * Real.exp (σ2 / 4) * Real.exp (-t / (2 * d))) := by
  let S : Ω → ℝ := fun ω => ∑ i : Fin ν, X i ω
  have hS_meas : Measurable S := Finset.measurable_sum _ fun i _ => hX_meas i
  have hS_bdd : ∀ ω, |S ω| ≤ (ν : ℝ) * (2 * d) := fun ω =>
    (Finset.abs_sum_le_sum_abs _ _).trans <| by
      simpa using Finset.sum_le_sum (s := Finset.univ) fun i _ => hX_bdd i ω
  have honeside : ∀ (s : ℝ), |s| = 1 →
      P {ω | t ≤ s * S ω} ≤ ENNReal.ofReal (Real.exp (σ2 / 4) * Real.exp (-t / (2 * d))) := by
    intro s hs
    let c : ℝ := s * (2 * d)⁻¹
    have hc : |c| = (2 * d)⁻¹ := by
      rw [abs_mul, hs, one_mul, abs_of_pos (by positivity)]
    have hmgf : ∫ ω, Real.exp (c * S ω) ∂P ≤ Real.exp (σ2 / 4) :=
      bernstein_mgf_bound P hν hd hσ2 hc hX_meas hX_indep hX_mean hX_bdd hX_var
    have hint : Integrable (fun ω => Real.exp (c * S ω)) P := by
      refine Integrable.of_bound
        ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.comp
          hS_meas).aestronglyMeasurable
        (Real.exp (|c| * ((ν : ℝ) * (2 * d)))) (ae_of_all _ fun ω => ?_)
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      apply Real.exp_le_exp.mpr
      calc c * S ω ≤ |c * S ω| := le_abs_self _
        _ = |c| * |S ω| := abs_mul c (S ω)
        _ ≤ |c| * ((ν : ℝ) * (2 * d)) := by gcongr; exact hS_bdd ω
    have hsub : {ω | t ≤ s * S ω} ⊆ {ω | Real.exp (t / (2 * d)) ≤ Real.exp (c * S ω)} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω ⊢
      apply Real.exp_le_exp.mpr
      have : t / (2 * d) = t * (2 * d)⁻¹ := div_eq_mul_inv t (2 * d)
      rw [this]
      calc t * (2 * d)⁻¹ ≤ (s * S ω) * (2 * d)⁻¹ := by gcongr
        _ = c * S ω := by simp only [c]; ring
    have hmarkov := mul_meas_ge_le_integral_of_nonneg
      (ae_of_all _ fun ω => (Real.exp_pos (c * S ω)).le) hint (Real.exp (t / (2 * d)))
    have hmarkov2 : P.real {ω | Real.exp (t / (2 * d)) ≤ Real.exp (c * S ω)} ≤
        Real.exp (σ2 / 4) * Real.exp (-t / (2 * d)) := by
      have hpos : 0 < Real.exp (t / (2 * d)) := Real.exp_pos _
      rw [neg_div, Real.exp_neg]
      rw [← mul_le_mul_iff_right₀ hpos]
      calc Real.exp (t / (2 * d)) * P.real {ω | Real.exp (t / (2 * d)) ≤ Real.exp (c * S ω)}
          ≤ ∫ ω, Real.exp (c * S ω) ∂P := hmarkov
        _ ≤ Real.exp (σ2 / 4) := hmgf
        _ = Real.exp (t / (2 * d)) * (Real.exp (σ2 / 4) * (Real.exp (t / (2 * d)))⁻¹) := by
            rw [mul_left_comm, mul_inv_cancel₀ hpos.ne', mul_one]
    calc P {ω | t ≤ s * S ω}
        ≤ P {ω | Real.exp (t / (2 * d)) ≤ Real.exp (c * S ω)} := measure_mono hsub
      _ = ENNReal.ofReal (P.real {ω | Real.exp (t / (2 * d)) ≤ Real.exp (c * S ω)}) :=
          (ofReal_measureReal).symm
      _ ≤ ENNReal.ofReal (Real.exp (σ2 / 4) * Real.exp (-t / (2 * d))) :=
          ENNReal.ofReal_le_ofReal hmarkov2
  have hunion : {ω | t ≤ |S ω|} ⊆ {ω | t ≤ 1 * S ω} ∪ {ω | t ≤ (-1) * S ω} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, Set.mem_union, one_mul, neg_one_mul] at hω ⊢
    rcases le_or_gt 0 (S ω) with h | h
    · left; rwa [abs_of_nonneg h] at hω
    · right; rwa [abs_of_neg h] at hω
  calc P {ω | t ≤ |S ω|}
      ≤ P ({ω | t ≤ 1 * S ω} ∪ {ω | t ≤ (-1) * S ω}) := measure_mono hunion
    _ ≤ P {ω | t ≤ 1 * S ω} + P {ω | t ≤ (-1) * S ω} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (σ2 / 4) * Real.exp (-t / (2 * d))) +
        ENNReal.ofReal (Real.exp (σ2 / 4) * Real.exp (-t / (2 * d))) :=
        add_le_add (honeside 1 (by norm_num)) (honeside (-1) (by norm_num))
    _ = ENNReal.ofReal (2 * Real.exp (σ2 / 4) * Real.exp (-t / (2 * d))) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

/-! ### Part 2: Super-exponential series decay and dyadic chaining on compact `U ⊆ Rn n` -/

private lemma superexp_bound_eventually {r A B : ℝ} (hr : 1 < r) (hA : 0 < A) :
    ∀ᶠ k : ℕ in atTop, B * (k : ℝ) ≤ A * r ^ k := by
  have h1 : Tendsto (fun k : ℕ => (k : ℝ) / r ^ k) atTop (𝓝 0) := by
    simpa [pow_one] using tendsto_pow_const_div_const_pow_of_one_lt 1 hr
  have h2 : Tendsto (fun k : ℕ => B * ((k : ℝ) / r ^ k)) atTop (𝓝 (B * 0)) :=
    h1.const_mul B
  rw [mul_zero] at h2
  filter_upwards [h2.eventually (gt_mem_nhds hA)] with k hk
  have hrk : 0 < r ^ k := pow_pos (by linarith) k
  rw [← div_le_iff₀ hrk]
  calc B * (k : ℝ) / r ^ k = B * ((k : ℝ) / r ^ k) := mul_div_assoc _ _ _
    _ ≤ A := hk.le

private lemma superexp_tendsto_zero {n : ℕ} {C A : ℝ} (hC : 0 ≤ C) (hA : 0 < A) :
    Tendsto (fun k : ℕ => C * (2 : ℝ) ^ (2 * k * n) * Real.exp (-A * (2 : ℝ) ^ k))
      atTop (𝓝 0) := by
  let B : ℝ := (2 * (n : ℝ)) * Real.log 2 + 1
  have hev := superexp_bound_eventually (r := 2) (A := A) (B := B) (by norm_num) hA
  refine squeeze_zero_norm' ?_ (by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos (-1)).le
      (Real.exp_lt_one_iff.mpr (by norm_num))).const_mul C)
  filter_upwards [hev] with k hk
  rw [Real.norm_of_nonneg (by positivity)]
  have hpow : (2 : ℝ) ^ (2 * k * n) = Real.exp ((2 * (n : ℝ) * Real.log 2) * (k : ℝ)) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1; push_cast; ring
  rw [hpow, mul_assoc, ← Real.exp_add]
  have hexp_le : (2 * (n : ℝ) * Real.log 2) * (k : ℝ) + -A * (2 : ℝ) ^ k ≤ -(k : ℝ) := by
    have : B * (k : ℝ) = (2 * (n : ℝ) * Real.log 2) * (k : ℝ) + (k : ℝ) := by
      simp only [B]; ring
    linarith
  calc C * Real.exp ((2 * (n : ℝ) * Real.log 2) * (k : ℝ) + -A * (2 : ℝ) ^ k)
      ≤ C * Real.exp (-(k : ℝ)) := by gcongr
    _ = C * (Real.exp (-1)) ^ k := by
        rw [← Real.exp_nat_mul]; congr 2; ring

private lemma superexp_summable {n : ℕ} {C A : ℝ} (hC : 0 ≤ C) (hA : 0 < A) :
    Summable (fun k : ℕ => C * (2 : ℝ) ^ ((2 * k + 1) * n) * Real.exp (-A * (3 / 2 : ℝ) ^ k)) := by
  let B : ℝ := (2 * (n : ℝ)) * Real.log 2 + 1
  have hev := superexp_bound_eventually (r := 3 / 2) (A := A) (B := B) (by norm_num) hA
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  have hgeom : Summable (fun k : ℕ => (C * (2 : ℝ) ^ n) * (Real.exp (-1)) ^ k) :=
    (summable_geometric_of_lt_one (Real.exp_pos (-1)).le
      (Real.exp_lt_one_iff.mpr (by norm_num))).mul_left _
  rw [← summable_nat_add_iff N]
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    ((summable_nat_add_iff N).mpr hgeom)
  have hk := hN (k + N) (Nat.le_add_left N k)
  set m := k + N
  have hpow : (2 : ℝ) ^ ((2 * m + 1) * n) =
      (2 : ℝ) ^ n * Real.exp ((2 * (n : ℝ) * Real.log 2) * (m : ℝ)) := by
    have hsplit : (2 * m + 1) * n = n + 2 * m * n := by ring
    rw [hsplit, pow_add]
    congr 1
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1; push_cast; ring
  rw [hpow]
  have hexp_le : (2 * (n : ℝ) * Real.log 2) * (m : ℝ) + -A * (3 / 2 : ℝ) ^ m ≤ -(m : ℝ) := by
    have : B * (m : ℝ) = (2 * (n : ℝ) * Real.log 2) * (m : ℝ) + (m : ℝ) := by
      simp only [B]; ring
    linarith
  calc C * ((2 : ℝ) ^ n * Real.exp ((2 * (n : ℝ) * Real.log 2) * (m : ℝ))) *
          Real.exp (-A * (3 / 2 : ℝ) ^ m)
      = (C * (2 : ℝ) ^ n) *
          Real.exp ((2 * (n : ℝ) * Real.log 2) * (m : ℝ) + -A * (3 / 2 : ℝ) ^ m) := by
        rw [Real.exp_add]; ring
    _ ≤ (C * (2 : ℝ) ^ n) * Real.exp (-(m : ℝ)) := by gcongr
    _ = (C * (2 : ℝ) ^ n) * (Real.exp (-1)) ^ m := by
        rw [← Real.exp_nat_mul]; congr 2; ring

private lemma dyadic_chaining_osc_bound {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set (Rn n)) [CompactSpace ↥U] (x₀ : ↥U)
    {C ε η : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) (hη : 0 < η) :
    ∃ δ > 0, ∀ (W : Ω → C(↥U, ℝ)),
      (∀ x y : ↥U, x ≠ y → ∀ t ≥ 0,
        P {ω | t ≤ |W ω x - W ω y|} ≤
          ENNReal.ofReal (C * Real.exp (-t / (2 * ‖(x : Rn n) - y‖)))) →
      P {ω | ∃ x y : ↥U, ‖(x : Rn n) - y‖ < δ ∧ η < |W ω x - W ω y|} ≤
        ENNReal.ofReal ε := by
  have hU_bdd : Bornology.IsBounded U := (isCompact_iff_compactSpace.mpr ‹_›).isBounded
  obtain ⟨R₀, hR₀⟩ := hU_bdd.subset_ball (0 : Rn n)
  let M : ℝ := max 1 (R₀ + 1)
  have hM_pos : 0 < M := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hU_coord : ∀ (x : ↥U) (i : Fin n), |(x : Rn n) i| < M := by
    intro x i
    have hnorm : ‖(x : Rn n)‖ < R₀ := by
      have hx := hR₀ x.2
      simpa [Metric.mem_ball, dist_zero_right] using hx
    have hci : |(x : Rn n) i| ≤ ‖(x : Rn n)‖ := by
      simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (x : Rn n) i
    linarith [le_max_right (1 : ℝ) (R₀ + 1)]
  let D₀ : ℝ := 2 * M * (Real.sqrt n + 1)
  have hD₀_pos : 0 < D₀ := by positivity
  let cell (k : ℕ) (x : ↥U) : Fin n → Fin (2 ^ k) := fun i =>
    ⟨Nat.floor (((x : Rn n) i + M) / (2 * M) * (2 : ℝ) ^ k), by
      have hcoord := hU_coord x i
      have hlt1 : ((x : Rn n) i + M) / (2 * M) < 1 := by
        rw [div_lt_one (by positivity)]
        linarith [(abs_lt.mp hcoord).2]
      have hlt2 : ((x : Rn n) i + M) / (2 * M) * (2 : ℝ) ^ k < ((2 ^ k : ℕ) : ℝ) := by
        push_cast
        calc ((x : Rn n) i + M) / (2 * M) * (2 : ℝ) ^ k
            < 1 * (2 : ℝ) ^ k := by gcongr
          _ = (2 : ℝ) ^ k := one_mul _
      exact (Nat.floor_lt (by
        have hpos : 0 < (x : Rn n) i + M := by linarith [(abs_lt.mp hcoord).1]
        positivity)).mpr hlt2⟩
  have hcell_dist : ∀ (k : ℕ) (x y : ↥U), cell k x = cell k y →
      ‖(x : Rn n) - y‖ ≤ D₀ / (2 : ℝ) ^ k := by
    intro k x y hxy
    have hci : ∀ i : Fin n, |((x : Rn n) - y) i| ≤ 2 * M / (2 : ℝ) ^ k := by
      intro i
      have hfi : (cell k x i).val = (cell k y i).val := congrArg (fun g => (g i).val) hxy
      set ax : ℝ := ((x : Rn n) i + M) / (2 * M) * (2 : ℝ) ^ k
      set ay : ℝ := ((y : Rn n) i + M) / (2 * M) * (2 : ℝ) ^ k
      have hax_nn : 0 ≤ ax := by
        have hpos : 0 < (x : Rn n) i + M := by linarith [(abs_lt.mp (hU_coord x i)).1]
        positivity
      have hay_nn : 0 ≤ ay := by
        have hpos : 0 < (y : Rn n) i + M := by linarith [(abs_lt.mp (hU_coord y i)).1]
        positivity
      have hfx1 : (Nat.floor ax : ℝ) ≤ ax := Nat.floor_le hax_nn
      have hfx2 : ax < (Nat.floor ax : ℝ) + 1 := Nat.lt_floor_add_one ax
      have hfy1 : (Nat.floor ay : ℝ) ≤ ay := Nat.floor_le hay_nn
      have hfy2 : ay < (Nat.floor ay : ℝ) + 1 := Nat.lt_floor_add_one ay
      have hfeq : (Nat.floor ax : ℝ) = (Nat.floor ay : ℝ) := by exact_mod_cast hfi
      have hdiff : |ax - ay| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith
      have hsub : ax - ay = ((x : Rn n) i - (y : Rn n) i) * ((2 : ℝ) ^ k / (2 * M)) := by
        simp only [ax, ay]; field_simp; ring
      have hpos_fac : 0 < (2 : ℝ) ^ k / (2 * M) := by positivity
      rw [hsub, abs_mul, abs_of_pos hpos_fac] at hdiff
      have hle : |(x : Rn n) i - (y : Rn n) i| ≤ 2 * M / (2 : ℝ) ^ k := by
        rw [le_div_iff₀ (by positivity)]
        have h1 : |(x : Rn n) i - (y : Rn n) i| * (2 : ℝ) ^ k / (2 * M) ≤ 1 := by
          simpa [mul_div_assoc] using hdiff
        exact (div_le_one (by positivity)).mp h1
      simpa using hle
    have hsq : ‖(x : Rn n) - y‖ ^ 2 ≤ (D₀ / (2 : ℝ) ^ k) ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
      calc ∑ i : Fin n, ‖((x : Rn n) - y) i‖ ^ 2
          ≤ ∑ _i : Fin n, (2 * M / (2 : ℝ) ^ k) ^ 2 := by
            apply Finset.sum_le_sum; intro i _
            rw [Real.norm_eq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hci i) 2
        _ = (n : ℝ) * (2 * M / (2 : ℝ) ^ k) ^ 2 := by simp
        _ ≤ (Real.sqrt n + 1) ^ 2 * (2 * M / (2 : ℝ) ^ k) ^ 2 := by
            gcongr
            calc (n : ℝ) = (Real.sqrt n) ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg n)).symm
              _ ≤ (Real.sqrt n + 1) ^ 2 := by nlinarith [Real.sqrt_nonneg n]
        _ = (D₀ / (2 : ℝ) ^ k) ^ 2 := by simp only [D₀]; ring
    nlinarith [norm_nonneg ((x : Rn n) - y),
      div_nonneg hD₀_pos.le (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) k)]
  classical
  let rep (k : ℕ) (c : Fin n → Fin (2 ^ k)) : ↥U :=
    if h : ∃ x : ↥U, cell k x = c then Classical.choose h else x₀
  let proj (k : ℕ) (x : ↥U) : ↥U := rep k (cell k x)
  have hproj_dist : ∀ (k : ℕ) (x : ↥U), ‖(proj k x : Rn n) - x‖ ≤ D₀ / (2 : ℝ) ^ k := by
    intro k x
    apply hcell_dist k
    have hex : ∃ y : ↥U, cell k y = cell k x := ⟨x, rfl⟩
    dsimp only [proj, rep]
    rw [dif_pos hex]
    exact Classical.choose_spec hex
  have hsum := superexp_summable (n := n) (C := C) (A := η / (48 * D₀)) hC (by positivity)
  have hbad1_tendsto := superexp_tendsto_zero (n := n) (C := C) (A := η / (18 * D₀)) hC
    (by positivity)
  have htsum_tail : Tendsto (fun k₀ : ℕ =>
      ∑' j : ℕ, C * (2 : ℝ) ^ ((2 * (j + k₀) + 1) * n) *
        Real.exp (-(η / (48 * D₀)) * (3 / 2 : ℝ) ^ (j + k₀))) atTop (𝓝 0) := by
    have h0 := hsum.hasSum.tendsto_sum_nat
    have heq : ∀ k₀ : ℕ,
        (∑' j : ℕ, C * (2 : ℝ) ^ ((2 * (j + k₀) + 1) * n) *
          Real.exp (-(η / (48 * D₀)) * (3 / 2 : ℝ) ^ (j + k₀))) =
        (∑' k : ℕ, C * (2 : ℝ) ^ ((2 * k + 1) * n) *
          Real.exp (-(η / (48 * D₀)) * (3 / 2 : ℝ) ^ k)) -
        ∑ k ∈ Finset.range k₀, C * (2 : ℝ) ^ ((2 * k + 1) * n) *
          Real.exp (-(η / (48 * D₀)) * (3 / 2 : ℝ) ^ k) := by
      intro k₀
      have hsplit := hsum.sum_add_tsum_nat_add k₀
      linarith
    simp_rw [heq]
    have hsub_t := (tendsto_const_nhds (x := ∑' k : ℕ, C * (2 : ℝ) ^ ((2 * k + 1) * n) *
      Real.exp (-(η / (48 * D₀)) * (3 / 2 : ℝ) ^ k))).sub h0
    rwa [sub_self] at hsub_t
  obtain ⟨k₀, hk₀1, hk₀2⟩ : ∃ k₀ : ℕ,
      C * (2 : ℝ) ^ (2 * k₀ * n) * Real.exp (-(η / (18 * D₀)) * (2 : ℝ) ^ k₀) ≤ ε / 2 ∧
      (∑' j : ℕ, C * (2 : ℝ) ^ ((2 * (j + k₀) + 1) * n) *
        Real.exp (-(η / (48 * D₀)) * (3 / 2 : ℝ) ^ (j + k₀))) ≤ ε / 2 := by
    have h1 := hbad1_tendsto.eventually (ge_mem_nhds (half_pos hε))
    have h2 := htsum_tail.eventually (ge_mem_nhds (half_pos hε))
    exact (h1.and h2).exists
  refine ⟨D₀ / (2 : ℝ) ^ k₀, by positivity, fun W hW => ?_⟩
  let α : ℕ → ℝ := fun j => (η / 12) * (3 / 4 : ℝ) ^ j
  let Bad1 : Set Ω :=
    ⋃ p : (Fin n → Fin (2 ^ k₀)) × (Fin n → Fin (2 ^ k₀)),
      if ‖(rep k₀ p.1 : Rn n) - rep k₀ p.2‖ ≤ 3 * D₀ / (2 : ℝ) ^ k₀ then
        {ω | η / 3 ≤ |W ω (rep k₀ p.1) - W ω (rep k₀ p.2)|}
      else ∅
  let Bad2 (j : ℕ) : Set Ω :=
    ⋃ p : (Fin n → Fin (2 ^ (j + k₀ + 1))) × (Fin n → Fin (2 ^ (j + k₀))),
      if ‖(rep (j + k₀ + 1) p.1 : Rn n) - rep (j + k₀) p.2‖ ≤ 2 * D₀ / (2 : ℝ) ^ (j + k₀) then
        {ω | α j ≤ |W ω (rep (j + k₀ + 1) p.1) - W ω (rep (j + k₀) p.2)|}
      else ∅
  have hsub : {ω | ∃ x y : ↥U, ‖(x : Rn n) - y‖ < D₀ / (2 : ℝ) ^ k₀ ∧ η < |W ω x - W ω y|} ⊆
      Bad1 ∪ ⋃ j : ℕ, Bad2 j := by
    intro ω hω
    by_contra hnot
    simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hnot
    obtain ⟨hnot1, hnot2⟩ := hnot
    obtain ⟨x, y, hxy_dist, hxy_osc⟩ := hω
    have hchain : ∀ z : ↥U, |W ω z - W ω (proj k₀ z)| ≤ η / 3 := by
      intro z
      have hstep : ∀ j : ℕ, |W ω (proj (j + k₀ + 1) z) - W ω (proj (j + k₀) z)| < α j := by
        intro j
        have hstep_dist : ‖(proj (j + k₀ + 1) z : Rn n) - proj (j + k₀) z‖ ≤
            2 * D₀ / (2 : ℝ) ^ (j + k₀) := by
          have h1 := hproj_dist (j + k₀ + 1) z
          have h2 := hproj_dist (j + k₀) z
          have htri : ‖(proj (j + k₀ + 1) z : Rn n) - proj (j + k₀) z‖ ≤
              ‖(proj (j + k₀ + 1) z : Rn n) - z‖ + ‖(proj (j + k₀) z : Rn n) - z‖ := by
            calc ‖(proj (j + k₀ + 1) z : Rn n) - proj (j + k₀) z‖
                = ‖((proj (j + k₀ + 1) z : Rn n) - z) - ((proj (j + k₀) z : Rn n) - z)‖ := by
                  abel_nf
              _ ≤ ‖(proj (j + k₀ + 1) z : Rn n) - z‖ + ‖(proj (j + k₀) z : Rn n) - z‖ :=
                  norm_sub_le _ _
          have hpow : (2 : ℝ) ^ (j + k₀ + 1) = 2 * (2 : ℝ) ^ (j + k₀) := by
            rw [pow_succ]; ring
          have hdiv_le : D₀ / (2 : ℝ) ^ (j + k₀ + 1) ≤ D₀ / (2 : ℝ) ^ (j + k₀) := by
            rw [hpow]
            apply div_le_div_of_nonneg_left hD₀_pos.le (by positivity)
            linarith [pow_pos (by norm_num : (0 : ℝ) < 2) (j + k₀)]
          have h2eq : D₀ / (2 : ℝ) ^ (j + k₀) + D₀ / (2 : ℝ) ^ (j + k₀) =
              2 * D₀ / (2 : ℝ) ^ (j + k₀) := by ring
          linarith
        have hmem_not := hnot2 j
        simp only [Bad2, Set.mem_iUnion, not_exists] at hmem_not
        specialize hmem_not (cell (j + k₀ + 1) z, cell (j + k₀) z)
        rw [if_pos hstep_dist] at hmem_not
        exact not_le.mp hmem_not
      have hpartial : ∀ N : ℕ, |W ω (proj (N + k₀) z) - W ω (proj k₀ z)| ≤ η / 3 := by
        intro N
        have htelesc : W ω (proj (N + k₀) z) - W ω (proj k₀ z) =
            ∑ j ∈ Finset.range N, (W ω (proj (j + k₀ + 1) z) - W ω (proj (j + k₀) z)) := by
          induction N with
          | zero => simp
          | succ N ih =>
            rw [Finset.sum_range_succ, ← ih]
            have : (N + 1) + k₀ = N + k₀ + 1 := by omega
            rw [this]; ring
        rw [htelesc]
        calc |∑ j ∈ Finset.range N, (W ω (proj (j + k₀ + 1) z) - W ω (proj (j + k₀) z))|
            ≤ ∑ j ∈ Finset.range N, |W ω (proj (j + k₀ + 1) z) - W ω (proj (j + k₀) z)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ j ∈ Finset.range N, α j :=
              Finset.sum_le_sum fun j _ => (hstep j).le
          _ = (η / 12) * ∑ j ∈ Finset.range N, (3 / 4 : ℝ) ^ j := by
              simp only [α, ← Finset.mul_sum]
          _ ≤ (η / 12) * 4 := by
              gcongr
              rw [geom_sum_eq (by norm_num)]
              have hnn : (0 : ℝ) ≤ (3 / 4 : ℝ) ^ N := by positivity
              have hge : ((3 / 4 : ℝ) ^ N - 1) / (3 / 4 - 1) = 4 * (1 - (3 / 4 : ℝ) ^ N) := by ring
              linarith
          _ = η / 3 := by ring
      have htend_proj : Tendsto (fun N : ℕ => proj (N + k₀) z) atTop (𝓝 z) := by
        rw [tendsto_iff_dist_tendsto_zero]
        refine squeeze_zero (g := fun N => D₀ / (2 : ℝ) ^ (N + k₀))
          (fun _ => dist_nonneg) (fun N => ?_) ?_
        · simpa [Subtype.dist_eq, dist_eq_norm] using hproj_dist (N + k₀) z
        · have h1 : Tendsto (fun N : ℕ => D₀ * ((2 : ℝ)⁻¹) ^ (N + k₀)) atTop (𝓝 (D₀ * 0)) :=
            ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
              (tendsto_add_atTop_nat k₀)).const_mul D₀
          simpa [div_eq_mul_inv, inv_pow] using h1
      have htend_val : Tendsto (fun N : ℕ => |W ω (proj (N + k₀) z) - W ω (proj k₀ z)|)
          atTop (𝓝 |W ω z - W ω (proj k₀ z)|) :=
        (((W ω).continuous.tendsto z).comp htend_proj).sub_const _ |>.abs
      exact le_of_tendsto htend_val (Eventually.of_forall hpartial)
    have hcoarse_dist : ‖(proj k₀ x : Rn n) - proj k₀ y‖ ≤ 3 * D₀ / (2 : ℝ) ^ k₀ := by
      have h1 := hproj_dist k₀ x
      have h2 := hproj_dist k₀ y
      have htri : ‖(proj k₀ x : Rn n) - proj k₀ y‖ ≤
          ‖(proj k₀ x : Rn n) - x‖ + ‖(x : Rn n) - y‖ + ‖(proj k₀ y : Rn n) - y‖ := by
        calc ‖(proj k₀ x : Rn n) - proj k₀ y‖
            = ‖((proj k₀ x : Rn n) - x) + ((x : Rn n) - y) - ((proj k₀ y : Rn n) - y)‖ := by
              abel_nf
          _ ≤ ‖((proj k₀ x : Rn n) - x) + ((x : Rn n) - y)‖ + ‖(proj k₀ y : Rn n) - y‖ :=
              norm_sub_le _ _
          _ ≤ ‖(proj k₀ x : Rn n) - x‖ + ‖(x : Rn n) - y‖ + ‖(proj k₀ y : Rn n) - y‖ := by
              gcongr; exact norm_add_le _ _
      have h3eq : D₀ / (2 : ℝ) ^ k₀ + D₀ / (2 : ℝ) ^ k₀ + D₀ / (2 : ℝ) ^ k₀ =
          3 * D₀ / (2 : ℝ) ^ k₀ := by ring
      linarith
    have hcoarse_osc : |W ω (proj k₀ x) - W ω (proj k₀ y)| < η / 3 := by
      simp only [Bad1, Set.mem_iUnion, not_exists] at hnot1
      specialize hnot1 (cell k₀ x, cell k₀ y)
      rw [if_pos hcoarse_dist] at hnot1
      exact not_le.mp hnot1
    have htot : |W ω x - W ω y| ≤
        |W ω x - W ω (proj k₀ x)| + |W ω (proj k₀ x) - W ω (proj k₀ y)| +
          |W ω y - W ω (proj k₀ y)| := by
      have h1 : W ω x - W ω y =
          (W ω x - W ω (proj k₀ x)) + (W ω (proj k₀ x) - W ω (proj k₀ y)) -
            (W ω y - W ω (proj k₀ y)) := by ring
      rw [h1]
      calc |(W ω x - W ω (proj k₀ x)) + (W ω (proj k₀ x) - W ω (proj k₀ y)) -
              (W ω y - W ω (proj k₀ y))|
          ≤ |(W ω x - W ω (proj k₀ x)) + (W ω (proj k₀ x) - W ω (proj k₀ y))| +
              |W ω y - W ω (proj k₀ y)| := abs_sub _ _
        _ ≤ |W ω x - W ω (proj k₀ x)| + |W ω (proj k₀ x) - W ω (proj k₀ y)| +
              |W ω y - W ω (proj k₀ y)| := by gcongr; exact abs_add_le _ _
    linarith [hchain x, hchain y]
  have hpair : ∀ (u v : ↥U) (R t : ℝ), 0 < R → 0 < t → ‖(u : Rn n) - v‖ ≤ R →
      P {ω | t ≤ |W ω u - W ω v|} ≤ ENNReal.ofReal (C * Real.exp (-t / (2 * R))) := by
    intro u v R t hR ht huv
    by_cases heq : u = v
    · subst heq
      have hempty : {ω | t ≤ |W ω u - W ω u|} = ∅ := by
        ext ω; simp [ht]
      rw [hempty, measure_empty]
      exact bot_le
    · have hpos : 0 < ‖(u : Rn n) - v‖ :=
        norm_pos_iff.mpr (sub_ne_zero.mpr (fun h => heq (Subtype.ext h)))
      refine (hW u v heq t ht.le).trans (ENNReal.ofReal_le_ofReal ?_)
      have hexp : -t / (2 * ‖(u : Rn n) - v‖) ≤ -t / (2 * R) := by
        rw [neg_div, neg_div, neg_le_neg_iff]
        exact div_le_div_of_nonneg_left ht.le (by positivity) (by linarith)
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hC
  have hBad1 : P Bad1 ≤ ENNReal.ofReal (ε / 2) := by
    have hcard : (Fintype.card ((Fin n → Fin (2 ^ k₀)) × (Fin n → Fin (2 ^ k₀))) : ℝ) =
        (2 : ℝ) ^ (2 * k₀ * n) := by
      simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Nat.cast_mul, Nat.cast_pow,
        Nat.cast_ofNat]
      rw [← pow_mul, ← pow_add]
      congr 1; ring
    calc P Bad1
        ≤ ∑ p : (Fin n → Fin (2 ^ k₀)) × (Fin n → Fin (2 ^ k₀)),
            P (if ‖(rep k₀ p.1 : Rn n) - rep k₀ p.2‖ ≤ 3 * D₀ / (2 : ℝ) ^ k₀ then
              {ω | η / 3 ≤ |W ω (rep k₀ p.1) - W ω (rep k₀ p.2)|} else ∅) :=
          measure_iUnion_fintype_le P _
      _ ≤ ∑ _p : (Fin n → Fin (2 ^ k₀)) × (Fin n → Fin (2 ^ k₀)),
            ENNReal.ofReal (C * Real.exp (-(η / 3) / (2 * (3 * D₀ / (2 : ℝ) ^ k₀)))) := by
          apply Finset.sum_le_sum; intro p _
          split_ifs with h
          · exact hpair _ _ _ _ (by positivity) (by positivity) h
          · simp
      _ = ENNReal.ofReal ((2 : ℝ) ^ (2 * k₀ * n) *
            (C * Real.exp (-(η / 3) / (2 * (3 * D₀ / (2 : ℝ) ^ k₀))))) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (Nat.cast_nonneg _), hcard]
      _ = ENNReal.ofReal (C * (2 : ℝ) ^ (2 * k₀ * n) *
            Real.exp (-(η / (18 * D₀)) * (2 : ℝ) ^ k₀)) := by
          congr 1
          have hexp_eq : -(η / 3) / (2 * (3 * D₀ / (2 : ℝ) ^ k₀)) =
              -(η / (18 * D₀)) * (2 : ℝ) ^ k₀ := by
            field_simp; ring
          rw [hexp_eq]; ring
      _ ≤ ENNReal.ofReal (ε / 2) := ENNReal.ofReal_le_ofReal hk₀1
  have hBad2 : ∀ j : ℕ, P (Bad2 j) ≤
      ENNReal.ofReal (C * (2 : ℝ) ^ ((2 * (j + k₀) + 1) * n) *
        Real.exp (-(η / (48 * D₀)) * (3 / 2 : ℝ) ^ (j + k₀))) := by
    intro j
    have hcard : (Fintype.card ((Fin n → Fin (2 ^ (j + k₀ + 1))) ×
        (Fin n → Fin (2 ^ (j + k₀)))) : ℝ) = (2 : ℝ) ^ ((2 * (j + k₀) + 1) * n) := by
      simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Nat.cast_mul, Nat.cast_pow,
        Nat.cast_ofNat]
      rw [← pow_mul, ← pow_mul, ← pow_add]
      congr 1; ring
    have hexp_bound : -(α j) / (2 * (2 * D₀ / (2 : ℝ) ^ (j + k₀))) ≤
        -(η / (48 * D₀)) * (3 / 2 : ℝ) ^ (j + k₀) := by
      have h1 : -(α j) / (2 * (2 * D₀ / (2 : ℝ) ^ (j + k₀))) =
          -(η / (48 * D₀)) * ((2 : ℝ) ^ k₀ * (3 / 2 : ℝ) ^ j) := by
        simp only [α]
        have hpow : (3 / 4 : ℝ) ^ j * (2 : ℝ) ^ (j + k₀) = (2 : ℝ) ^ k₀ * (3 / 2 : ℝ) ^ j := by
          rw [pow_add]
          have : (3 / 4 : ℝ) ^ j * (2 : ℝ) ^ j = (3 / 2 : ℝ) ^ j := by
            rw [← mul_pow]; norm_num
          rw [← mul_assoc, this, mul_comm]
        field_simp
        nlinarith [hpow]
      rw [h1]
      have hpow_le : (3 / 2 : ℝ) ^ (j + k₀) ≤ (2 : ℝ) ^ k₀ * (3 / 2 : ℝ) ^ j := by
        rw [pow_add, mul_comm]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by norm_num) (by norm_num) k₀) (by positivity)
      have hcoef : 0 ≤ η / (48 * D₀) := by positivity
      nlinarith
    calc P (Bad2 j)
        ≤ ∑ p : (Fin n → Fin (2 ^ (j + k₀ + 1))) × (Fin n → Fin (2 ^ (j + k₀))),
            P (if ‖(rep (j + k₀ + 1) p.1 : Rn n) - rep (j + k₀) p.2‖ ≤
                2 * D₀ / (2 : ℝ) ^ (j + k₀) then
              {ω | α j ≤ |W ω (rep (j + k₀ + 1) p.1) - W ω (rep (j + k₀) p.2)|} else ∅) :=
          measure_iUnion_fintype_le P _
      _ ≤ ∑ _p : (Fin n → Fin (2 ^ (j + k₀ + 1))) × (Fin n → Fin (2 ^ (j + k₀))),
            ENNReal.ofReal (C * Real.exp (-(α j) / (2 * (2 * D₀ / (2 : ℝ) ^ (j + k₀))))) := by
          apply Finset.sum_le_sum; intro p _
          split_ifs with h
          · exact hpair _ _ _ _ (by positivity) (by simp only [α]; positivity) h
          · simp
      _ = ENNReal.ofReal ((2 : ℝ) ^ ((2 * (j + k₀) + 1) * n) *
            (C * Real.exp (-(α j) / (2 * (2 * D₀ / (2 : ℝ) ^ (j + k₀)))))) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (Nat.cast_nonneg _), hcard]
      _ ≤ ENNReal.ofReal (C * (2 : ℝ) ^ ((2 * (j + k₀) + 1) * n) *
            Real.exp (-(η / (48 * D₀)) * (3 / 2 : ℝ) ^ (j + k₀))) := by
          apply ENNReal.ofReal_le_ofReal
          have hmul : (2 : ℝ) ^ ((2 * (j + k₀) + 1) * n) *
              (C * Real.exp (-(α j) / (2 * (2 * D₀ / (2 : ℝ) ^ (j + k₀))))) =
              C * (2 : ℝ) ^ ((2 * (j + k₀) + 1) * n) *
                Real.exp (-(α j) / (2 * (2 * D₀ / (2 : ℝ) ^ (j + k₀)))) := by ring
          rw [hmul]
          gcongr
  have hBad2_sum : P (⋃ j : ℕ, Bad2 j) ≤ ENNReal.ofReal (ε / 2) := by
    have hsum_shift : Summable (fun j : ℕ =>
        C * (2 : ℝ) ^ ((2 * (j + k₀) + 1) * n) *
          Real.exp (-(η / (48 * D₀)) * (3 / 2 : ℝ) ^ (j + k₀))) :=
      (summable_nat_add_iff k₀).mpr hsum
    calc P (⋃ j : ℕ, Bad2 j)
        ≤ ∑' j : ℕ, P (Bad2 j) := measure_iUnion_le _
      _ ≤ ∑' j : ℕ, ENNReal.ofReal (C * (2 : ℝ) ^ ((2 * (j + k₀) + 1) * n) *
            Real.exp (-(η / (48 * D₀)) * (3 / 2 : ℝ) ^ (j + k₀))) :=
          ENNReal.tsum_le_tsum hBad2
      _ = ENNReal.ofReal (∑' j : ℕ, C * (2 : ℝ) ^ ((2 * (j + k₀) + 1) * n) *
            Real.exp (-(η / (48 * D₀)) * (3 / 2 : ℝ) ^ (j + k₀))) := by
          rw [ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hsum_shift]
      _ ≤ ENNReal.ofReal (ε / 2) := ENNReal.ofReal_le_ofReal hk₀2
  calc P {ω | ∃ x y : ↥U, ‖(x : Rn n) - y‖ < D₀ / (2 : ℝ) ^ k₀ ∧ η < |W ω x - W ω y|}
      ≤ P (Bad1 ∪ ⋃ j : ℕ, Bad2 j) := measure_mono hsub
    _ ≤ P Bad1 + P (⋃ j : ℕ, Bad2 j) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add hBad1 hBad2_sum
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves]

/-! ### Part 3: Measurable Lipschitz seminorm and Arzelà-Ascoli compactness -/

private lemma dense_lip_extend {n m : ℕ} (U : Set (Rn n)) (g : C(↥U, Rn m))
    (d : ℕ → ↥U) (hd : DenseRange d) (c : ℝ)
    (hc : ∀ p q : ℕ, ‖g (d p) - g (d q)‖ ≤ c * ‖(d p : Rn n) - d q‖) :
    ∀ x₁ x₂ : ↥U, ‖g x₁ - g x₂‖ ≤ c * ‖(x₁ : Rn n) - x₂‖ := by
  intro x₁ x₂
  have hseq : ∀ x : ↥U, ∃ u : ℕ → ℕ, Tendsto (fun k => d (u k)) atTop (𝓝 x) := by
    intro x
    have hex : ∀ k : ℕ, ∃ i : ℕ, dist (d i) x < 1 / ((k : ℝ) + 1) := by
      intro k
      obtain ⟨i, hi⟩ := Metric.denseRange_iff.mp hd x (1 / ((k : ℝ) + 1)) (by positivity)
      exact ⟨i, by rwa [dist_comm]⟩
    choose u hu using hex
    refine ⟨u, tendsto_iff_dist_tendsto_zero.mpr ?_⟩
    exact squeeze_zero (g := fun k : ℕ => 1 / ((k : ℝ) + 1))
      (fun _ => dist_nonneg) (fun k => (hu k).le) tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨u, hu⟩ := hseq x₁
  obtain ⟨v, hv⟩ := hseq x₂
  have hlhs : Tendsto (fun k => ‖g (d (u k)) - g (d (v k))‖) atTop (𝓝 ‖g x₁ - g x₂‖) :=
    (((g.continuous.tendsto x₁).comp hu).sub ((g.continuous.tendsto x₂).comp hv)).norm
  have hrhs : Tendsto (fun k => c * ‖(d (u k) : Rn n) - d (v k)‖) atTop
      (𝓝 (c * ‖(x₁ : Rn n) - x₂‖)) :=
    ((((continuous_subtype_val.tendsto x₁).comp hu).sub
      ((continuous_subtype_val.tendsto x₂).comp hv)).norm).const_mul c
  exact le_of_tendsto_of_tendsto hlhs hrhs (Eventually.of_forall fun k => hc (u k) (v k))

private lemma exists_measurable_lip_seminorm {n m : ℕ} {S Ω : Type*}
    [MeasurableSpace S] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set (Rn n)) [CompactSpace ↥U] (x₀ : ↥U)
    (f : S → C(↥U, Rn m)) (hmeas : ∀ x : ↥U, Measurable (fun σ => f σ x))
    (s0 : Ω → S) (hs0 : Measurable s0)
    (hP4 : ∃ a : S → ℝ, MemLp (fun ω => a (s0 ω)) 2 P ∧
      ∀ σ : S, ∀ x₁ x₂ : ↥U, ‖f σ x₁ - f σ x₂‖ ≤ a σ * ‖(x₁ : Rn n) - x₂‖) :
    ∃ L : S → ℝ, Measurable L ∧ (∀ σ, 0 ≤ L σ) ∧ MemLp (fun ω => L (s0 ω)) 2 P ∧
      ∀ σ : S, ∀ x₁ x₂ : ↥U, ‖f σ x₁ - f σ x₂‖ ≤ L σ * ‖(x₁ : Rn n) - x₂‖ := by
  have : Nonempty ↥U := ⟨x₀⟩
  obtain ⟨a, ha_lp, ha_lip⟩ := hP4
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq ↥U
  let L_inf : S → ℝ≥0∞ := fun σ =>
    ⨆ p : ℕ, ⨆ q : ℕ, edist (f σ (d p)) (f σ (d q)) / edist (d p) (d q)
  have hL_le : ∀ σ, L_inf σ ≤ ENNReal.ofReal |a σ| := by
    intro σ
    refine iSup_le fun p => iSup_le fun q => ?_
    by_cases hpq : d p = d q
    · simp [hpq]
    · have hpos : edist (d p) (d q) ≠ 0 := mt edist_eq_zero.mp hpq
      have hne_top : edist (d p) (d q) ≠ ⊤ := edist_ne_top _ _
      rw [ENNReal.div_le_iff_le_mul (Or.inl hpos) (Or.inl hne_top)]
      rw [edist_dist, edist_dist, dist_eq_norm, Subtype.dist_eq, dist_eq_norm,
        ← ENNReal.ofReal_mul (abs_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      calc ‖f σ (d p) - f σ (d q)‖ ≤ a σ * ‖(d p : Rn n) - d q‖ := ha_lip σ (d p) (d q)
        _ ≤ |a σ| * ‖(d p : Rn n) - d q‖ := by gcongr; exact le_abs_self _
  have hL_meas : Measurable L_inf := by
    refine Measurable.iSup fun p => Measurable.iSup fun q => ?_
    exact (Measurable.edist (hmeas (d p)) (hmeas (d q))).div_const _
  let L : S → ℝ := fun σ => (L_inf σ).toReal
  refine ⟨L, hL_meas.ennreal_toReal, fun _ => ENNReal.toReal_nonneg, ?_, ?_⟩
  · refine ha_lp.norm.mono' ((hL_meas.ennreal_toReal.comp hs0).aestronglyMeasurable)
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_of_nonneg ENNReal.toReal_nonneg, Real.norm_eq_abs]
    calc (L_inf (s0 ω)).toReal ≤ (ENNReal.ofReal |a (s0 ω)|).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top (hL_le (s0 ω))
      _ = |a (s0 ω)| := ENNReal.toReal_ofReal (abs_nonneg _)
  · intro σ x₁ x₂
    have hdense : ∀ p q : ℕ, ‖f σ (d p) - f σ (d q)‖ ≤ L σ * ‖(d p : Rn n) - d q‖ := by
      intro p q
      by_cases hpq : d p = d q
      · simp [hpq]
      · have hpos : edist (d p) (d q) ≠ 0 := mt edist_eq_zero.mp hpq
        have hne_top : edist (d p) (d q) ≠ ⊤ := edist_ne_top _ _
        have h1 : edist (f σ (d p)) (f σ (d q)) / edist (d p) (d q) ≤ L_inf σ :=
          le_iSup_of_le p (le_iSup_of_le q le_rfl)
        have h2 : edist (f σ (d p)) (f σ (d q)) ≤ L_inf σ * edist (d p) (d q) :=
          (ENNReal.div_le_iff_le_mul (Or.inl hpos) (Or.inl hne_top)).mp h1
        have hfin : L_inf σ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hL_le σ)
        have h3 := ENNReal.toReal_mono (ENNReal.mul_ne_top hfin hne_top) h2
        rw [ENNReal.toReal_mul, ← dist_edist, ← dist_edist, dist_eq_norm, Subtype.dist_eq,
          dist_eq_norm] at h3
        exact h3
    exact dense_lip_extend U (f σ) d hd (L σ) hdense x₁ x₂

private lemma isCompact_equicont_set {n m : ℕ} (U : Set (Rn n)) [CompactSpace ↥U]
    (F : Finset ↥U) (R : ℝ) (δ : ℕ → ℝ) (hδ : ∀ k, 0 < δ k)
    (hcover : ∀ x : ↥U, ∃ y ∈ F, dist x y < δ 0) :
    IsCompact {g : C(↥U, Rn m) | (∀ y ∈ F, ‖g y‖ ≤ R) ∧
      ∀ k : ℕ, ∀ x y : ↥U, dist x y < δ k → dist (g x) (g y) ≤ 1 / ((k : ℝ) + 1)} := by
  let e := ContinuousMap.equivBoundedOfCompact ↥U (Rn m)
  let A : Set C(↥U, Rn m) := {g | (∀ y ∈ F, ‖g y‖ ≤ R) ∧
    ∀ k : ℕ, ∀ x y : ↥U, dist x y < δ k → dist (g x) (g y) ≤ 1 / ((k : ℝ) + 1)}
  have hclosed_A : IsClosed A := by
    have h1 : IsClosed {g : C(↥U, Rn m) | ∀ y ∈ F, ‖g y‖ ≤ R} := by
      simp_rw [Set.ofPred_forall]
      exact isClosed_iInter fun y => isClosed_iInter fun _ =>
        isClosed_le ((continuous_eval_const y).norm) continuous_const
    have h2 : IsClosed {g : C(↥U, Rn m) |
        ∀ k : ℕ, ∀ x y : ↥U, dist x y < δ k → dist (g x) (g y) ≤ 1 / ((k : ℝ) + 1)} := by
      simp_rw [Set.ofPred_forall]
      exact isClosed_iInter fun k => isClosed_iInter fun x => isClosed_iInter fun y =>
        isClosed_iInter fun _ =>
          isClosed_le ((continuous_eval_const x).dist (continuous_eval_const y)) continuous_const
    exact h1.inter h2
  let hu := ContinuousMap.isUniformEmbedding_equivBoundedOfCompact ↥U (Rn m)
  let hhomeo : C(↥U, Rn m) ≃ₜ (↥U →ᵇ Rn m) :=
    { toEquiv := e
      continuous_toFun := hu.uniformContinuous.continuous
      continuous_invFun := hu.isUniformInducing.isInducing.continuous_iff.mpr (by
        have hcomp : (⇑(ContinuousMap.equivBoundedOfCompact ↥U (Rn m)) ∘ e.invFun) = id := by
          ext b x; simp [e]
        rw [hcomp]; exact continuous_id) }
  let B : Set (↥U →ᵇ Rn m) := hhomeo '' A
  have hcomp_B : IsCompact B := by
    refine BoundedContinuousFunction.arzela_ascoli₂ (closedBall (0 : Rn m) (R + 1))
      (isCompact_closedBall _ _) B ?_ ?_ ?_
    · exact hhomeo.isClosed_image.mpr hclosed_A
    · rintro _ x ⟨g, hg, rfl⟩
      obtain ⟨y, hyF, hxy⟩ := hcover x
      rw [Metric.mem_closedBall, dist_zero_right]
      have hgy : ‖g y‖ ≤ R := hg.1 y hyF
      have hdiff : dist (g x) (g y) ≤ 1 := by
        simpa using hg.2 0 x y hxy
      calc ‖(hhomeo g) x‖ = ‖g x‖ := rfl
        _ ≤ ‖g x - g y‖ + ‖g y‖ := norm_le_norm_sub_add (g x) (g y)
        _ = dist (g x) (g y) + ‖g y‖ := by rw [dist_eq_norm]
        _ ≤ 1 + R := add_le_add hdiff hgy
        _ = R + 1 := add_comm _ _
    · intro x
      rw [Metric.equicontinuousAt_iff]
      intro ε hε
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
      refine ⟨δ k, hδ k, fun y hy ⟨b, hb⟩ => ?_⟩
      obtain ⟨g, hg, rfl⟩ := hb
      rw [dist_comm]
      exact (hg.2 k y x hy).trans_lt hk
  have hA_eq : A = hhomeo.symm '' B := by
    ext g; simp [B]
  change IsCompact A
  rw [hA_eq]
  exact hcomp_B.image hhomeo.symm.continuous

private lemma continuous_charFunDual {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] (φ : StrongDual ℝ E) :
    Continuous (fun μ : ProbabilityMeasure E => charFunDual (μ : Measure E) φ) := by
  rw [continuous_iff_continuousAt]
  intro μ
  rw [ContinuousAt]
  have h := (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp
    (tendsto_id : Tendsto (id : ProbabilityMeasure E → ProbabilityMeasure E) (𝓝 μ) (𝓝 μ))
    (BoundedContinuousFunction.probCharDual φ)
  simpa [charFunDual] using h

/-! ### Part 4: Uniform stochastic equicontinuity and pointwise tightness -/

private lemma uniform_equicont_Z {n m : ℕ} {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set (Rn n)) [CompactSpace ↥U] (x₀ : ↥U)
    (f : S → C(↥U, Rn m)) (hf_meas : Measurable f)
    (s : ℕ → Ω → S) (hs : ∀ i, Measurable (s i))
    (hindep : iIndepFun s P) (hident : ∀ i, IdentDistrib (s i) (s 0) P P)
    (hfs0_int : Integrable (fun ω => f (s 0 ω)) P)
    (L : S → ℝ) (hL_meas : Measurable L) (hL_nn : ∀ σ, 0 ≤ L σ)
    (hL_lp : MemLp (fun ω => L (s 0 ω)) 2 P)
    (hL_lip : ∀ σ : S, ∀ x₁ x₂ : ↥U, ‖f σ x₁ - f σ x₂‖ ≤ L σ * ‖(x₁ : Rn n) - x₂‖)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ δ > (0 : ℝ), ∀ ν : ℕ,
      P {ω | ∃ x y : ↥U, dist x y < δ ∧
        η < dist ((Real.sqrt ν • ((ν : ℝ)⁻¹ • ∑ i ∈ Finset.range ν, f (s i ω) -
            ∫ ω', f (s 0 ω') ∂P)) x)
          ((Real.sqrt ν • ((ν : ℝ)⁻¹ • ∑ i ∈ Finset.range ν, f (s i ω) -
            ∫ ω', f (s 0 ω') ∂P)) y)} ≤ ENNReal.ofReal ε := by
  let E := C(↥U, Rn m)
  let Z : ℕ → Ω → E := fun ν ω =>
    Real.sqrt ν • ((ν : ℝ)⁻¹ • ∑ i ∈ Finset.range ν, f (s i ω) - ∫ ω', f (s 0 ω') ∂P)
  have hfs_meas : ∀ i, Measurable (fun ω => f (s i ω)) := fun i => hf_meas.comp (hs i)
  have hLs_meas : ∀ i, Measurable (fun ω => L (s i ω)) := fun i => hL_meas.comp (hs i)
  have hZ_meas : ∀ ν, Measurable (Z ν) := fun ν =>
    (continuous_const_smul (Real.sqrt ν)).measurable.comp
      (((continuous_const_smul ((ν : ℝ)⁻¹)).measurable.comp
        (Finset.measurable_sum _ fun i _ => hfs_meas i)).sub measurable_const)
  have hU_bdd : Bornology.IsBounded (Set.univ : Set ↥U) := isCompact_univ.isBounded
  let diamU : ℝ := Metric.diam (Set.univ : Set ↥U)
  have hdiam_nn : 0 ≤ diamU := Metric.diam_nonneg
  have hdist_le_diam : ∀ x y : ↥U, ‖(x : Rn n) - y‖ ≤ diamU := fun x y => by
    simpa [Subtype.dist_eq, dist_eq_norm] using
      Metric.dist_le_diam_of_mem hU_bdd (Set.mem_univ x) (Set.mem_univ y)
  let σ2 : ℝ := ∫ ω, (L (s 0 ω)) ^ 2 ∂P
  have hLsq_int : Integrable (fun ω => (L (s 0 ω)) ^ 2) P := hL_lp.integrable_sq
  have hσ2_nn : 0 ≤ σ2 := integral_nonneg fun ω => sq_nonneg _
  by_cases hm0 : m = 0
  · refine ⟨1, one_pos, fun ν => ?_⟩
    have hempty : {ω | ∃ x y : ↥U, dist x y < 1 ∧ η < dist (Z ν ω x) (Z ν ω y)} = ∅ := by
      ext ω; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
      intro x y _
      have hsub : Z ν ω x = Z ν ω y := by ext i; exact Fin.elim0 (hm0 ▸ i)
      rw [hsub, dist_self]; linarith
    rw [hempty, measure_empty]; exact bot_le
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm0
  let C_bern : ℝ := 2 * Real.exp (σ2 / 4)
  obtain ⟨δ₁, hδ₁_pos, hchain⟩ := dyadic_chaining_osc_bound P U x₀
    (C := C_bern) (ε := ε / (2 * (m : ℝ))) (η := η / (2 * (m : ℝ)))
    (by positivity) (by positivity) (by positivity)
  let tailInt : ℕ → ℝ := fun ν =>
    ∫ ω, (if L (s 0 ω) ≤ Real.sqrt ν then (0 : ℝ) else (L (s 0 ω)) ^ 2) ∂P
  have htail_tendsto : Tendsto tailInt atTop (𝓝 0) := by
    have h0 : (0 : ℝ) = ∫ _ : Ω, (0 : ℝ) ∂P := by simp
    rw [h0]
    refine tendsto_integral_of_dominated_convergence (fun ω => (L (s 0 ω)) ^ 2) ?_ hLsq_int ?_ ?_
    · intro ν
      exact (Measurable.ite (measurableSet_le (hLs_meas 0) measurable_const)
        measurable_const ((hLs_meas 0).pow_const 2)).aestronglyMeasurable
    · intro ν
      refine ae_of_all _ fun ω => ?_
      split_ifs <;> simp [sq_nonneg]
    · refine ae_of_all _ fun ω => ?_
      have hev : ∀ᶠ ν : ℕ in atTop, L (s 0 ω) ≤ Real.sqrt ν :=
        (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).eventually
          (eventually_ge_atTop (L (s 0 ω)))
      exact tendsto_const_nhds.congr' (hev.mono fun ν hν => (if_pos hν).symm)
  obtain ⟨N₀, hN₀_ge, hN₀_tail1, hN₀_tail2⟩ : ∃ N₀ : ℕ, 1 ≤ N₀ ∧
      (∀ ν ≥ N₀, tailInt ν * diamU ≤ η / 2) ∧ (∀ ν ≥ N₀, tailInt ν ≤ ε / 2) := by
    have h1 : Tendsto (fun ν => tailInt ν * diamU) atTop (𝓝 0) := by
      simpa using htail_tendsto.mul_const diamU
    have hev1 := h1.eventually (ge_mem_nhds (half_pos hη))
    have hev2 := htail_tendsto.eventually (ge_mem_nhds (half_pos hε))
    rw [Filter.eventually_atTop] at hev1 hev2
    obtain ⟨N₁, hN₁⟩ := hev1
    obtain ⟨N₂, hN₂⟩ := hev2
    exact ⟨max 1 (max N₁ N₂), le_max_left _ _,
      fun ν hν => hN₁ ν ((le_max_left _ _).trans ((le_max_right _ _).trans hν)),
      fun ν hν => hN₂ ν ((le_max_right _ _).trans ((le_max_right _ _).trans hν))⟩
  have hlarge : ∀ ν ≥ N₀,
      P {ω | ∃ x y : ↥U, dist x y < δ₁ ∧ η < dist (Z ν ω x) (Z ν ω y)} ≤ ENNReal.ofReal ε := by
    intro ν hνN₀
    have hν1 : 1 ≤ ν := hN₀_ge.trans hνN₀
    have hνpos : (0 : ℝ) < (ν : ℝ) := Nat.cast_pos.mpr (by omega)
    have hsq_pos : 0 < Real.sqrt ν := Real.sqrt_pos.mpr hνpos
    let f₁ : S → E := fun σ => if L σ ≤ Real.sqrt ν then f σ else 0
    let f₂ : S → E := fun σ => if L σ ≤ Real.sqrt ν then 0 else f σ
    have hf₁_meas : Measurable f₁ :=
      Measurable.ite (measurableSet_le hL_meas measurable_const) hf_meas measurable_const
    have hf₂_meas : Measurable f₂ :=
      Measurable.ite (measurableSet_le hL_meas measurable_const) measurable_const hf_meas
    have hf₁_int : Integrable (fun ω => f₁ (s 0 ω)) P :=
      hfs0_int.norm.mono' (hf₁_meas.comp (hs 0)).aestronglyMeasurable (ae_of_all _ fun ω => by
        simp only [f₁]; split_ifs <;> simp)
    have hf₂_int : Integrable (fun ω => f₂ (s 0 ω)) P :=
      hfs0_int.norm.mono' (hf₂_meas.comp (hs 0)).aestronglyMeasurable (ae_of_all _ fun ω => by
        simp only [f₂]; split_ifs <;> simp)
    let Z₁ : Ω → E := fun ω =>
      Real.sqrt ν • ((ν : ℝ)⁻¹ • ∑ i ∈ Finset.range ν, f₁ (s i ω) - ∫ ω', f₁ (s 0 ω') ∂P)
    let Z₂ : Ω → E := fun ω =>
      Real.sqrt ν • ((ν : ℝ)⁻¹ • ∑ i ∈ Finset.range ν, f₂ (s i ω) - ∫ ω', f₂ (s 0 ω') ∂P)
    have hZ_split : ∀ ω, Z ν ω = Z₁ ω + Z₂ ω := by
      intro ω
      have hadd : ∀ σ, f σ = f₁ σ + f₂ σ := fun σ => by
        simp only [f₁, f₂]; split_ifs <;> simp
      have hsum_eq : ∑ i ∈ Finset.range ν, f (s i ω) =
          (∑ i ∈ Finset.range ν, f₁ (s i ω)) + ∑ i ∈ Finset.range ν, f₂ (s i ω) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => hadd (s i ω)
      have hint_eq : ∫ ω', f (s 0 ω') ∂P =
          (∫ ω', f₁ (s 0 ω') ∂P) + ∫ ω', f₂ (s 0 ω') ∂P := by
        rw [← integral_add hf₁_int hf₂_int]
        congr 1; funext ω'; exact hadd (s 0 ω')
      ext x i
      change ((EuclideanSpace.proj i).comp (ContinuousMap.evalCLM (R := ℝ) x)) (Z ν ω) =
        ((EuclideanSpace.proj i).comp (ContinuousMap.evalCLM (R := ℝ) x)) (Z₁ ω + Z₂ ω)
      simp only [Z, Z₁, Z₂, hsum_eq, hint_eq, map_add, map_sub, map_smul, smul_eq_mul]
      ring
    have hZ₁_bound : P {ω | ∃ x y : ↥U, dist x y < δ₁ ∧ η / 2 < dist (Z₁ ω x) (Z₁ ω y)} ≤
        ENNReal.ofReal (ε / 2) := by
      let W (r : Fin m) : Ω → C(↥U, ℝ) := fun ω =>
        ⟨fun x => (Z₁ ω x) r, (EuclideanSpace.proj r).continuous.comp (Z₁ ω).continuous⟩
      have hsub_coord : {ω | ∃ x y : ↥U, dist x y < δ₁ ∧ η / 2 < dist (Z₁ ω x) (Z₁ ω y)} ⊆
          ⋃ r : Fin m, {ω | ∃ x y : ↥U, ‖(x : Rn n) - y‖ < δ₁ ∧
            η / (2 * (m : ℝ)) < |W r ω x - W r ω y|} := by
        intro ω ⟨x, y, hxy_d, hxy_osc⟩
        simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
        by_contra hnot
        push Not at hnot
        have hnorm_le : ‖Z₁ ω x - Z₁ ω y‖ ≤ ∑ r : Fin m, |(Z₁ ω x) r - (Z₁ ω y) r| := by
          rw [EuclideanSpace.norm_eq]
          have hsum_sq_le : ∀ (s' : Finset (Fin m)) (u : Fin m → ℝ),
              (∀ r ∈ s', 0 ≤ u r) → ∑ r ∈ s', (u r) ^ 2 ≤ (∑ r ∈ s', u r) ^ 2 := by
            intro s' u hu
            induction s' using Finset.cons_induction with
            | empty => simp
            | cons a s'' ha ih =>
              rw [Finset.sum_cons, Finset.sum_cons]
              have ha0 : 0 ≤ u a := hu a (Finset.mem_cons_self a s'')
              have hs0 : 0 ≤ ∑ r ∈ s'', u r :=
                Finset.sum_nonneg fun r hr => hu r (Finset.mem_cons_of_mem hr)
              have hih := ih fun r hr => hu r (Finset.mem_cons_of_mem hr)
              nlinarith
          have h1 : ∑ r : Fin m, ‖(Z₁ ω x - Z₁ ω y) r‖ ^ 2 ≤
              (∑ r : Fin m, |(Z₁ ω x) r - (Z₁ ω y) r|) ^ 2 := by
            simpa [Real.norm_eq_abs] using
              hsum_sq_le Finset.univ (fun r => |(Z₁ ω x) r - (Z₁ ω y) r|) fun _ _ => abs_nonneg _
          exact (Real.sqrt_le_sqrt h1).trans (by
            rw [Real.sqrt_sq (Finset.sum_nonneg fun _ _ => abs_nonneg _)])
        have hxy_n : ‖(x : Rn n) - y‖ < δ₁ := by
          simpa [Subtype.dist_eq, dist_eq_norm] using hxy_d
        have hle_sum : ∑ r : Fin m, |(Z₁ ω x) r - (Z₁ ω y) r| ≤ η / 2 := by
          calc ∑ r : Fin m, |(Z₁ ω x) r - (Z₁ ω y) r|
              ≤ ∑ _r : Fin m, η / (2 * (m : ℝ)) :=
                Finset.sum_le_sum fun r _ => hnot r x y hxy_n
            _ = (m : ℝ) * (η / (2 * (m : ℝ))) := by simp
            _ = η / 2 := by
                have hmne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm0
                field_simp
        rw [dist_eq_norm] at hxy_osc
        linarith
      have hW_tail : ∀ (r : Fin m) (x y : ↥U), x ≠ y → ∀ t ≥ 0,
          P {ω | t ≤ |W r ω x - W r ω y|} ≤
            ENNReal.ofReal (C_bern * Real.exp (-t / (2 * ‖(x : Rn n) - y‖))) := by
        intro r x y hxy t ht
        have hd_pos : 0 < ‖(x : Rn n) - y‖ :=
          norm_pos_iff.mpr (sub_ne_zero.mpr (fun h => hxy (Subtype.ext h)))
        let ψ : S → ℝ := fun σ => (f₁ σ x) r - (f₁ σ y) r
        have hψ_meas : Measurable ψ := by
          have h1 : Measurable (fun σ => (f₁ σ x) r) :=
            ((EuclideanSpace.proj r).continuous.comp
              (continuous_eval_const x)).measurable.comp hf₁_meas
          have h2 : Measurable (fun σ => (f₁ σ y) r) :=
            ((EuclideanSpace.proj r).continuous.comp
              (continuous_eval_const y)).measurable.comp hf₁_meas
          exact h1.sub h2
        have hψ_bdd : ∀ σ, |ψ σ| ≤ Real.sqrt ν * ‖(x : Rn n) - y‖ := by
          intro σ
          simp only [ψ, f₁]
          split_ifs with hLle
          · calc |(f σ x) r - (f σ y) r| = ‖(f σ x - f σ y) r‖ := by simp [Real.norm_eq_abs]
              _ ≤ ‖f σ x - f σ y‖ := PiLp.norm_apply_le _ r
              _ ≤ L σ * ‖(x : Rn n) - y‖ := hL_lip σ x y
              _ ≤ Real.sqrt ν * ‖(x : Rn n) - y‖ := by gcongr
          · simp only [E, ContinuousMap.zero_apply, PiLp.zero_apply, sub_self, abs_zero]
            positivity
        have hψ_lip : ∀ σ, |ψ σ| ≤ L σ * ‖(x : Rn n) - y‖ := by
          intro σ
          simp only [ψ, f₁]
          split_ifs with hLle
          · calc |(f σ x) r - (f σ y) r| = ‖(f σ x - f σ y) r‖ := by simp [Real.norm_eq_abs]
              _ ≤ ‖f σ x - f σ y‖ := PiLp.norm_apply_le _ r
              _ ≤ L σ * ‖(x : Rn n) - y‖ := hL_lip σ x y
          · simp only [E, ContinuousMap.zero_apply, PiLp.zero_apply, sub_self, abs_zero]
            exact mul_nonneg (hL_nn σ) (norm_nonneg _)
        let μψ : ℝ := ∫ ω', ψ (s 0 ω') ∂P
        let X : Fin ν → Ω → ℝ := fun i ω => (Real.sqrt ν)⁻¹ * (ψ (s i.val ω) - μψ)
        have hX_sum : ∀ ω, W r ω x - W r ω y = ∑ i : Fin ν, X i ω := by
          intro ω
          let evx : E →L[ℝ] ℝ := (EuclideanSpace.proj r).comp (ContinuousMap.evalCLM (R := ℝ) x)
          let evy : E →L[ℝ] ℝ := (EuclideanSpace.proj r).comp (ContinuousMap.evalCLM (R := ℝ) y)
          have hevx := evx.integral_comp_comm hf₁_int
          have hevy := evy.integral_comp_comm hf₁_int
          have hμψ : μψ = ((∫ ω', f₁ (s 0 ω') ∂P) x) r - ((∫ ω', f₁ (s 0 ω') ∂P) y) r := by
            simp only [μψ, ψ]
            have hint1 : Integrable (fun ω' => (f₁ (s 0 ω') x) r) P := evx.integrable_comp hf₁_int
            have hint2 : Integrable (fun ω' => (f₁ (s 0 ω') y) r) P := evy.integrable_comp hf₁_int
            rw [integral_sub hint1 hint2]
            exact congrArg₂ (· - ·) hevx hevy
          have hx_eval : (Z₁ ω x) r = Real.sqrt ν *
              ((ν : ℝ)⁻¹ * (∑ i ∈ Finset.range ν, (f₁ (s i ω) x) r) -
                ((∫ ω', f₁ (s 0 ω') ∂P) x) r) := by
            change evx (Z₁ ω) = _
            simp only [Z₁, map_smul, map_sub, map_sum, smul_eq_mul]; rfl
          have hy_eval : (Z₁ ω y) r = Real.sqrt ν *
              ((ν : ℝ)⁻¹ * (∑ i ∈ Finset.range ν, (f₁ (s i ω) y) r) -
                ((∫ ω', f₁ (s 0 ω') ∂P) y) r) := by
            change evy (Z₁ ω) = _
            simp only [Z₁, map_smul, map_sub, map_sum, smul_eq_mul]; rfl
          change (Z₁ ω x) r - (Z₁ ω y) r = ∑ i : Fin ν, (Real.sqrt ν)⁻¹ * (ψ (s i.val ω) - μψ)
          rw [hx_eval, hy_eval, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            Fin.sum_univ_eq_sum_range (fun i => ψ (s i ω)), hμψ]
          simp only [ψ, Finset.sum_sub_distrib]
          have hsq_ne : Real.sqrt ν ≠ 0 := hsq_pos.ne'
          field_simp
          rw [Real.sq_sqrt hνpos.le]
          ring
        have hX_meas : ∀ i : Fin ν, Measurable (X i) := fun i =>
          ((hψ_meas.comp (hs i.val)).sub measurable_const).const_mul _
        have hX_indep : iIndepFun X P := by
          have hind_sub : iIndepFun (fun i : Fin ν => s i.val) P :=
            hindep.precomp Fin.val_injective
          exact hind_sub.comp (fun _ σ => (Real.sqrt ν)⁻¹ * (ψ σ - μψ))
            (fun _ => (hψ_meas.sub measurable_const).const_mul _)
        have hψ_int : ∀ i : ℕ, Integrable (fun ω => ψ (s i ω)) P := fun i =>
          Integrable.of_bound (hψ_meas.comp (hs i)).aestronglyMeasurable
            (Real.sqrt ν * ‖(x : Rn n) - y‖)
            (ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using hψ_bdd (s i ω))
        have hX_mean : ∀ i : Fin ν, ∫ ω, X i ω ∂P = 0 := by
          intro i
          simp only [X]
          rw [integral_const_mul, integral_sub (hψ_int i.val) (integrable_const μψ),
            integral_const, probReal_univ, one_smul]
          have heq_int : ∫ ω, ψ (s i.val ω) ∂P = μψ :=
            ((hident i.val).comp hψ_meas).integral_eq
          rw [heq_int, sub_self, mul_zero]
        have hμψ_bdd : |μψ| ≤ Real.sqrt ν * ‖(x : Rn n) - y‖ := by
          calc |μψ| ≤ ∫ ω', |ψ (s 0 ω')| ∂P := by
                simpa [μψ, Real.norm_eq_abs] using
                  norm_integral_le_integral_norm (fun ω' => ψ (s 0 ω'))
            _ ≤ ∫ _ : Ω, (Real.sqrt ν * ‖(x : Rn n) - y‖) ∂P :=
                integral_mono (hψ_int 0).abs (integrable_const _) fun ω' => hψ_bdd (s 0 ω')
            _ = Real.sqrt ν * ‖(x : Rn n) - y‖ := by simp
        have hX_bdd : ∀ (i : Fin ν) ω, |X i ω| ≤ 2 * ‖(x : Rn n) - y‖ := by
          intro i ω
          simp only [X]
          rw [abs_mul, abs_of_pos (inv_pos.mpr hsq_pos)]
          calc (Real.sqrt ν)⁻¹ * |ψ (s i.val ω) - μψ|
              ≤ (Real.sqrt ν)⁻¹ * (|ψ (s i.val ω)| + |μψ|) := by gcongr; exact abs_sub _ _
            _ ≤ (Real.sqrt ν)⁻¹ * (Real.sqrt ν * ‖(x : Rn n) - y‖ +
                  Real.sqrt ν * ‖(x : Rn n) - y‖) := by
                gcongr; exact hψ_bdd _
            _ = 2 * ‖(x : Rn n) - y‖ := by field_simp; ring
        have hX_var : ∀ i : Fin ν, ∫ ω, (X i ω) ^ 2 ∂P ≤ σ2 * ‖(x : Rn n) - y‖ ^ 2 / (ν : ℝ) := by
          intro i
          have hψi_lp : MemLp (fun ω => ψ (s i.val ω)) 2 P :=
            MemLp.of_bound (hψ_meas.comp (hs i.val)).aestronglyMeasurable
              (Real.sqrt ν * ‖(x : Rn n) - y‖)
              (ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using hψ_bdd (s i.val ω))
          have heq_int : ∫ ω, ψ (s i.val ω) ∂P = μψ :=
            ((hident i.val).comp hψ_meas).integral_eq
          have hmeas_i : AEMeasurable (fun ω => ψ (s i.val ω)) P :=
            (hψ_meas.comp (hs i.val)).aemeasurable
          have hvar_eq : ∫ ω, (ψ (s i.val ω) - μψ) ^ 2 ∂P = Var[fun ω => ψ (s i.val ω); P] := by
            rw [variance_eq_integral hmeas_i, heq_int]
          have hvar_le : Var[fun ω => ψ (s i.val ω); P] ≤ ∫ ω, (ψ (s i.val ω)) ^ 2 ∂P :=
            variance_le_expectation_sq hψi_lp.aestronglyMeasurable
          have hsq_le : ∫ ω, (ψ (s i.val ω)) ^ 2 ∂P ≤ σ2 * ‖(x : Rn n) - y‖ ^ 2 := by
            have hident_L : ∫ ω, (L (s i.val ω)) ^ 2 ∂P = σ2 :=
              ((hident i.val).comp (hL_meas.pow_const 2)).integral_eq
            have hLsi_int : Integrable (fun ω => (L (s i.val ω)) ^ 2) P :=
              ((hident i.val).comp (hL_meas.pow_const 2)).integrable_iff.mpr hLsq_int
            calc ∫ ω, (ψ (s i.val ω)) ^ 2 ∂P
                ≤ ∫ ω, ((L (s i.val ω)) ^ 2 * ‖(x : Rn n) - y‖ ^ 2) ∂P := by
                  refine integral_mono hψi_lp.integrable_sq (hLsi_int.mul_const _) fun ω => ?_
                  rw [← mul_pow, ← sq_abs]
                  exact pow_le_pow_left₀ (abs_nonneg _) (hψ_lip (s i.val ω)) 2
              _ = (∫ ω, (L (s i.val ω)) ^ 2 ∂P) * ‖(x : Rn n) - y‖ ^ 2 :=
                  integral_mul_const _ _
              _ = σ2 * ‖(x : Rn n) - y‖ ^ 2 := by rw [hident_L]
          simp only [X, mul_pow, inv_pow, Real.sq_sqrt hνpos.le]
          rw [integral_const_mul, hvar_eq, inv_mul_eq_div]
          exact div_le_div_of_nonneg_right (hvar_le.trans hsq_le) hνpos.le
        have hbern := bernstein_exp_tail P hν1 hd_pos hσ2_nn hX_meas hX_indep hX_mean hX_bdd
          hX_var t
        simpa only [hX_sum] using hbern
      calc P {ω | ∃ x y : ↥U, dist x y < δ₁ ∧ η / 2 < dist (Z₁ ω x) (Z₁ ω y)}
          ≤ P (⋃ r : Fin m, {ω | ∃ x y : ↥U, ‖(x : Rn n) - y‖ < δ₁ ∧
              η / (2 * (m : ℝ)) < |W r ω x - W r ω y|}) := measure_mono hsub_coord
        _ ≤ ∑ r : Fin m, P {ω | ∃ x y : ↥U, ‖(x : Rn n) - y‖ < δ₁ ∧
              η / (2 * (m : ℝ)) < |W r ω x - W r ω y|} := measure_iUnion_fintype_le P _
        _ ≤ ∑ _r : Fin m, ENNReal.ofReal (ε / (2 * (m : ℝ))) :=
            Finset.sum_le_sum fun r _ => hchain (W r) (hW_tail r)
        _ = ENNReal.ofReal ((m : ℝ) * (ε / (2 * (m : ℝ)))) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
              ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        _ = ENNReal.ofReal (ε / 2) := by
            congr 1
            have hmne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm0
            field_simp
    have hZ₂_bound : P {ω | ∃ x y : ↥U, dist x y < δ₁ ∧ η / 2 < dist (Z₂ ω x) (Z₂ ω y)} ≤
        ENNReal.ofReal (ε / 2) := by
      let BadE : Set Ω := ⋃ i : Fin ν, {ω | Real.sqrt ν < L (s i.val ω)}
      have hsubE : {ω | ∃ x y : ↥U, dist x y < δ₁ ∧ η / 2 < dist (Z₂ ω x) (Z₂ ω y)} ⊆ BadE := by
        intro ω ⟨x, y, _, hosc⟩
        by_contra hnot
        simp only [BadE, Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_lt] at hnot
        have hsum0 : ∑ i ∈ Finset.range ν, f₂ (s i ω) = 0 := by
          refine Finset.sum_eq_zero fun i hi => ?_
          have hle : L (s i ω) ≤ Real.sqrt ν := hnot ⟨i, Finset.mem_range.mp hi⟩
          simp [f₂, hle]
        have hZ₂_eq : Z₂ ω = (-Real.sqrt ν) • ∫ ω', f₂ (s 0 ω') ∂P := by
          ext x i
          change ((EuclideanSpace.proj i).comp (ContinuousMap.evalCLM (R := ℝ) x)) (Z₂ ω) =
            ((EuclideanSpace.proj i).comp (ContinuousMap.evalCLM (R := ℝ) x))
              ((-Real.sqrt ν) • ∫ ω', f₂ (s 0 ω') ∂P)
          simp only [Z₂, hsum0, map_smul, map_sub, map_zero, smul_eq_mul]
          ring
        have hdiff_le : dist (Z₂ ω x) (Z₂ ω y) ≤ tailInt ν * diamU := by
          rw [dist_eq_norm]
          let ev_diff : E →L[ℝ] Rn m :=
            ContinuousMap.evalCLM (R := ℝ) x - ContinuousMap.evalCLM (R := ℝ) y
          have hev := ev_diff.integral_comp_comm hf₂_int
          have hpt : (Z₂ ω x) - (Z₂ ω y) = (-Real.sqrt ν) •
              (∫ ω', (f₂ (s 0 ω') x - f₂ (s 0 ω') y) ∂P) := by
            change ev_diff (Z₂ ω) = _
            rw [hZ₂_eq, map_smul, ← hev]
            rfl
          rw [hpt, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hsq_pos]
          have hdom_int : Integrable (fun ω' =>
              (if L (s 0 ω') ≤ Real.sqrt ν then (0 : ℝ) else (L (s 0 ω')) ^ 2) * diamU) P := by
            refine (Integrable.mono' hLsq_int ?_ (ae_of_all _ fun ω' => ?_)).mul_const diamU
            · exact (Measurable.ite (measurableSet_le (hLs_meas 0) measurable_const)
                measurable_const ((hLs_meas 0).pow_const 2)).aestronglyMeasurable
            · split_ifs <;> simp [sq_nonneg]
          calc Real.sqrt ν * ‖∫ ω', (f₂ (s 0 ω') x - f₂ (s 0 ω') y) ∂P‖
              ≤ Real.sqrt ν * ∫ ω', ‖f₂ (s 0 ω') x - f₂ (s 0 ω') y‖ ∂P := by
                gcongr; exact norm_integral_le_integral_norm _
            _ = ∫ ω', Real.sqrt ν * ‖f₂ (s 0 ω') x - f₂ (s 0 ω') y‖ ∂P :=
                (integral_const_mul _ _).symm
            _ ≤ ∫ ω', ((if L (s 0 ω') ≤ Real.sqrt ν then (0 : ℝ) else (L (s 0 ω')) ^ 2) *
                  diamU) ∂P := by
                refine integral_mono ((ev_diff.integrable_comp hf₂_int).norm.const_mul _)
                  hdom_int fun ω' => ?_
                simp only [f₂]
                split_ifs with hle
                · simp only [E, ContinuousMap.zero_apply, sub_self, norm_zero, mul_zero, zero_mul, le_refl]
                · push Not at hle
                  calc Real.sqrt ν * ‖f (s 0 ω') x - f (s 0 ω') y‖
                      ≤ Real.sqrt ν * (L (s 0 ω') * ‖(x : Rn n) - y‖) := by
                        gcongr; exact hL_lip _ _ _
                    _ ≤ Real.sqrt ν * (L (s 0 ω') * diamU) := by
                        gcongr; exact hL_nn _; exact hdist_le_diam x y
                    _ ≤ L (s 0 ω') * (L (s 0 ω') * diamU) :=
                        mul_le_mul_of_nonneg_right hle.le (mul_nonneg (hL_nn _) hdiam_nn)
                    _ = (L (s 0 ω')) ^ 2 * diamU := by ring
            _ = tailInt ν * diamU := integral_mul_const _ _
        linarith [hN₀_tail1 ν hνN₀]
      have hBadE_le : P BadE ≤ ENNReal.ofReal (tailInt ν) := by
        have heach : ∀ i : Fin ν, P {ω | Real.sqrt ν < L (s i.val ω)} =
            P {ω | Real.sqrt ν < L (s 0 ω)} := fun i =>
          ((hident i.val).comp hL_meas).measure_mem_eq measurableSet_Ioi
        have hmarkov : (ν : ℝ) * P.real {ω | Real.sqrt ν < L (s 0 ω)} ≤ tailInt ν := by
          have hset_meas : MeasurableSet {ω | Real.sqrt ν < L (s 0 ω)} :=
            measurableSet_lt measurable_const (hLs_meas 0)
          have htail_int_integrable : Integrable
              (fun ω => if L (s 0 ω) ≤ Real.sqrt ν then (0 : ℝ) else (L (s 0 ω)) ^ 2) P :=
            hLsq_int.mono'
              (Measurable.ite (measurableSet_le (hLs_meas 0) measurable_const)
                measurable_const ((hLs_meas 0).pow_const 2)).aestronglyMeasurable
              (ae_of_all _ fun ω => by split_ifs <;> simp [sq_nonneg])
          calc (ν : ℝ) * P.real {ω | Real.sqrt ν < L (s 0 ω)}
              = ∫ ω, Set.indicator {ω | Real.sqrt ν < L (s 0 ω)} (fun _ => (ν : ℝ)) ω ∂P := by
                rw [integral_indicator_const _ hset_meas, smul_eq_mul, mul_comm]
            _ ≤ ∫ ω, (if L (s 0 ω) ≤ Real.sqrt ν then (0 : ℝ) else (L (s 0 ω)) ^ 2) ∂P := by
                refine integral_mono ((integrable_const _).indicator hset_meas)
                  htail_int_integrable fun ω => ?_
                by_cases hle : L (s 0 ω) ≤ Real.sqrt ν
                · have hnot : ω ∉ {ω | Real.sqrt ν < L (s 0 ω)} := by
                    simp [not_lt.mpr hle]
                  rw [Set.indicator_of_notMem hnot, if_pos hle]
                · push Not at hle
                  have hmem : ω ∈ {ω | Real.sqrt ν < L (s 0 ω)} := hle
                  rw [Set.indicator_of_mem hmem, if_neg (not_le.mpr hle)]
                  have hsq : (Real.sqrt ν) ^ 2 = (ν : ℝ) := Real.sq_sqrt hνpos.le
                  nlinarith
        calc P BadE
            ≤ ∑ i : Fin ν, P {ω | Real.sqrt ν < L (s i.val ω)} := measure_iUnion_fintype_le P _
          _ = (ν : ℝ≥0∞) * P {ω | Real.sqrt ν < L (s 0 ω)} := by
              simp_rw [heach]; simp
          _ = ENNReal.ofReal ((ν : ℝ) * P.real {ω | Real.sqrt ν < L (s 0 ω)}) := by
              rw [ENNReal.ofReal_mul hνpos.le, ENNReal.ofReal_natCast, ofReal_measureReal]
          _ ≤ ENNReal.ofReal (tailInt ν) := ENNReal.ofReal_le_ofReal hmarkov
      exact (measure_mono hsubE).trans (hBadE_le.trans (ENNReal.ofReal_le_ofReal (hN₀_tail2 ν hνN₀)))
    have hsplit_set : {ω | ∃ x y : ↥U, dist x y < δ₁ ∧ η < dist (Z ν ω x) (Z ν ω y)} ⊆
        {ω | ∃ x y : ↥U, dist x y < δ₁ ∧ η / 2 < dist (Z₁ ω x) (Z₁ ω y)} ∪
        {ω | ∃ x y : ↥U, dist x y < δ₁ ∧ η / 2 < dist (Z₂ ω x) (Z₂ ω y)} := by
      intro ω ⟨x, y, hxy_d, hxy_osc⟩
      by_contra hnot
      simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_exists, not_and, not_lt] at hnot
      have h1 := hnot.1 x y hxy_d
      have h2 := hnot.2 x y hxy_d
      have htri : dist (Z ν ω x) (Z ν ω y) ≤
          dist (Z₁ ω x) (Z₁ ω y) + dist (Z₂ ω x) (Z₂ ω y) := by
        simp only [hZ_split ω, dist_eq_norm]
        calc ‖(Z₁ ω + Z₂ ω) x - (Z₁ ω + Z₂ ω) y‖
            = ‖(Z₁ ω x - Z₁ ω y) + (Z₂ ω x - Z₂ ω y)‖ := by
              change ‖(Z₁ ω x + Z₂ ω x) - (Z₁ ω y + Z₂ ω y)‖ = _; abel_nf
          _ ≤ ‖Z₁ ω x - Z₁ ω y‖ + ‖Z₂ ω x - Z₂ ω y‖ := norm_add_le _ _
      linarith
    calc P {ω | ∃ x y : ↥U, dist x y < δ₁ ∧ η < dist (Z ν ω x) (Z ν ω y)}
        ≤ P ({ω | ∃ x y : ↥U, dist x y < δ₁ ∧ η / 2 < dist (Z₁ ω x) (Z₁ ω y)} ∪
            {ω | ∃ x y : ↥U, dist x y < δ₁ ∧ η / 2 < dist (Z₂ ω x) (Z₂ ω y)}) :=
          measure_mono hsplit_set
      _ ≤ P {ω | ∃ x y : ↥U, dist x y < δ₁ ∧ η / 2 < dist (Z₁ ω x) (Z₁ ω y)} +
          P {ω | ∃ x y : ↥U, dist x y < δ₁ ∧ η / 2 < dist (Z₂ ω x) (Z₂ ω y)} :=
          measure_union_le _ _
      _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add hZ₁_bound hZ₂_bound
      _ = ENNReal.ofReal ε := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves]
  have hsmall : ∀ ν : ℕ, ∃ δ' > (0 : ℝ),
      P {ω | ∃ x y : ↥U, dist x y < δ' ∧ η < dist (Z ν ω x) (Z ν ω y)} ≤ ENNReal.ofReal ε := by
    intro ν
    let O (k : ℕ) : Set E :=
      {g : E | ∃ x y : ↥U, dist x y < 1 / ((k : ℝ) + 1) ∧ η < dist (g x) (g y)}
    have hO_open : ∀ k, IsOpen (O k) := by
      intro k
      have heq : O k = ⋃ (x : ↥U) (y : ↥U) (_ : dist x y < 1 / ((k : ℝ) + 1)),
          {g : E | η < dist (g x) (g y)} := by
        ext g; simp [O]
      rw [heq]
      exact isOpen_iUnion fun x => isOpen_iUnion fun y => isOpen_iUnion fun _ =>
        isOpen_lt continuous_const ((continuous_eval_const x).dist (continuous_eval_const y))
    have hO_anti : Antitone (fun k => Z ν ⁻¹' O k) := by
      intro a b hab ω ⟨x, y, hxy, hosc⟩
      refine ⟨x, y, hxy.trans_le ?_, hosc⟩
      exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hab 1)
    have hO_iInter : (⋂ k : ℕ, Z ν ⁻¹' O k) = ∅ := by
      ext ω
      simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_empty_iff_false, iff_false, not_forall, O,
        Set.mem_ofPred_eq]
      have huc := CompactSpace.uniformContinuous_of_continuous (Z ν ω).continuous
      rw [Metric.uniformContinuous_iff] at huc
      obtain ⟨δ', hδ'_pos, hδ'⟩ := huc η hη
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ'_pos
      refine ⟨k, fun ⟨x, y, hxy, hosc⟩ => ?_⟩
      have := hδ' (hxy.trans hk)
      linarith
    have htend : Tendsto (fun k => P (Z ν ⁻¹' O k)) atTop (𝓝 (P (⋂ k, Z ν ⁻¹' O k))) :=
      tendsto_measure_iInter_atTop
        (fun k => ((hO_open k).measurableSet.preimage (hZ_meas ν)).nullMeasurableSet)
        hO_anti ⟨0, measure_ne_top P _⟩
    rw [hO_iInter, measure_empty] at htend
    obtain ⟨k, hk⟩ := (htend.eventually (ge_mem_nhds (ENNReal.ofReal_pos.mpr hε))).exists
    exact ⟨1 / ((k : ℝ) + 1), by positivity, hk⟩
  choose δs hδs_pos hδs_le using hsmall
  have hrange_ne : (Finset.range N₀).Nonempty := ⟨0, Finset.mem_range.mpr (by omega)⟩
  let δ_fin : ℝ := (Finset.range N₀).inf' hrange_ne δs
  let δ_all : ℝ := min δ₁ δ_fin
  have hδ_fin_pos : 0 < δ_fin :=
    (Finset.lt_inf'_iff hrange_ne).mpr fun ν _ => hδs_pos ν
  refine ⟨δ_all, lt_min hδ₁_pos hδ_fin_pos, fun ν => ?_⟩
  by_cases hν : N₀ ≤ ν
  · refine (measure_mono ?_).trans (hlarge ν hν)
    intro ω ⟨x, y, hxy, hosc⟩
    exact ⟨x, y, hxy.trans_le (min_le_left _ _), hosc⟩
  · push Not at hν
    refine (measure_mono ?_).trans (hδs_le ν)
    intro ω ⟨x, y, hxy, hosc⟩
    have hle : δ_all ≤ δs ν :=
      (min_le_right _ _).trans (Finset.inf'_le δs (Finset.mem_range.mpr hν))
    exact ⟨x, y, hxy.trans_le hle, hosc⟩

private lemma pointwise_tight_Z {n m : ℕ} {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set (Rn n)) [CompactSpace ↥U]
    (f : S → C(↥U, Rn m)) (hmeas : ∀ x : ↥U, Measurable (fun σ => f σ x))
    (hf_meas : Measurable f)
    (s : ℕ → Ω → S) (hs : ∀ i, Measurable (s i))
    (hindep : iIndepFun s P) (hident : ∀ i, IdentDistrib (s i) (s 0) P P)
    (hfs0_lp : MemLp (fun ω => f (s 0 ω)) 2 P)
    (hfs0_int : Integrable (fun ω => f (s 0 ω)) P)
    (x : ↥U) {ε : ℝ} (hε : 0 < ε) :
    ∃ R > (0 : ℝ), ∀ ν : ℕ,
      P {ω | R < ‖(Real.sqrt ν • ((ν : ℝ)⁻¹ • ∑ i ∈ Finset.range ν, f (s i ω) -
        ∫ ω', f (s 0 ω') ∂P)) x‖} ≤ ENNReal.ofReal ε := by
  let E := C(↥U, Rn m)
  let Z : ℕ → Ω → E := fun ν ω =>
    Real.sqrt ν • ((ν : ℝ)⁻¹ • ∑ i ∈ Finset.range ν, f (s i ω) - ∫ ω', f (s 0 ω') ∂P)
  have hfs_meas : ∀ i, Measurable (fun ω => f (s i ω)) := fun i => hf_meas.comp (hs i)
  have hZ_meas : ∀ ν, Measurable (Z ν) := fun ν =>
    (continuous_const_smul (Real.sqrt ν)).measurable.comp
      (((continuous_const_smul ((ν : ℝ)⁻¹)).measurable.comp
        (Finset.measurable_sum _ fun i _ => hfs_meas i)).sub measurable_const)
  have hfx_lp : MemLp (fun ω => f (s 0 ω) x) 2 P :=
    hfs0_lp.norm.mono' ((hmeas x).comp (hs 0)).aestronglyMeasurable (ae_of_all _ fun ω =>
      ContinuousMap.norm_coe_le_norm (f (s 0 ω)) x)
  let C_x : ℝ := ∑ r : Fin m, Var[fun ω => (f (s 0 ω) x) r; P]
  have hCx_nn : 0 ≤ C_x := Finset.sum_nonneg fun r _ => variance_nonneg _ _
  let R : ℝ := Real.sqrt (C_x / ε) + 1
  have hR_pos : 0 < R := by positivity
  refine ⟨R, hR_pos, fun ν => ?_⟩
  by_cases hν0 : ν = 0
  · subst hν0
    have hempty : {ω | R < ‖Z 0 ω x‖} = ∅ := by
      ext ω
      have hZ0 : Z 0 ω x = 0 := by
        change ContinuousMap.evalCLM (R := ℝ) x (Z 0 ω) = 0
        simp only [Z, map_smul, Nat.cast_zero, Real.sqrt_zero, zero_smul]
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt, hZ0, norm_zero]
      exact hR_pos.le
    rw [hempty, measure_empty]; exact bot_le
  have hνpos : (0 : ℝ) < (ν : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hν0)
  have hsq_pos : 0 < Real.sqrt ν := Real.sqrt_pos.mpr hνpos
  have hcoord_sq : ∀ r : Fin m,
      ∫ ω, ((Z ν ω x) r) ^ 2 ∂P = Var[fun ω => (f (s 0 ω) x) r; P] := by
    intro r
    let Xr : ℕ → Ω → ℝ := fun i ω => (f (s i ω) x) r
    have hXr_meas : ∀ i, Measurable (Xr i) := fun i =>
      (EuclideanSpace.proj r).continuous.measurable.comp ((hmeas x).comp (hs i))
    have hXr_ident : ∀ i, IdentDistrib (Xr i) (Xr 0) P P := fun i =>
      (hident i).comp ((EuclideanSpace.proj r).continuous.measurable.comp (hmeas x))
    have hXr_lp : ∀ i, MemLp (Xr i) 2 P := fun i =>
      (hXr_ident i).memLp_iff.mpr <|
        hfx_lp.norm.mono' (hXr_meas 0).aestronglyMeasurable (ae_of_all _ fun ω =>
          PiLp.norm_apply_le _ r)
    have hXr_indep : iIndepFun Xr P :=
      hindep.comp (fun _ σ => (f σ x) r)
        (fun _ => (EuclideanSpace.proj r).continuous.measurable.comp (hmeas x))
    let ev : E →L[ℝ] ℝ := (EuclideanSpace.proj r).comp (ContinuousMap.evalCLM (R := ℝ) x)
    have hev := ev.integral_comp_comm hfs0_int
    have hZr_eq : ∀ ω, (Z ν ω x) r =
        (Real.sqrt ν)⁻¹ * ((∑ i ∈ Finset.range ν, Xr i ω) - (ν : ℝ) * P[Xr 0]) := by
      intro ω
      have hz_eval : (Z ν ω x) r =
          Real.sqrt ν * ((ν : ℝ)⁻¹ * (∑ i ∈ Finset.range ν, Xr i ω) - P[Xr 0]) := by
        change ev (Z ν ω) = _
        simp only [Z, map_smul, map_sub, map_sum, smul_eq_mul]
        rw [← hev]; rfl
      rw [hz_eval]
      have hsq_ne : Real.sqrt ν ≠ 0 := hsq_pos.ne'
      field_simp
      rw [Real.sq_sqrt hνpos.le]
    have hmean_sum : P[∑ i ∈ Finset.range ν, Xr i] = (ν : ℝ) * P[Xr 0] := by
      simp_rw [Finset.sum_apply]
      rw [integral_finsetSum _ fun i _ =>
        memLp_one_iff_integrable.mp ((hXr_lp i).mono_exponent (by norm_num))]
      have : ∀ i ∈ Finset.range ν, P[Xr i] = P[Xr 0] := fun i _ => (hXr_ident i).integral_eq
      rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hsum_meas : AEMeasurable (∑ i ∈ Finset.range ν, Xr i) P := by
      have hfun : (∑ i ∈ Finset.range ν, Xr i) = fun ω => ∑ i ∈ Finset.range ν, Xr i ω := by
        ext ω; simp [Finset.sum_apply]
      rw [hfun]
      exact (Finset.measurable_sum _ fun i _ => hXr_meas i).aemeasurable
    have hvar_sum : Var[∑ i ∈ Finset.range ν, Xr i; P] = (ν : ℝ) * Var[Xr 0; P] := by
      rw [IndepFun.variance_sum (fun i _ => hXr_lp i)
        (fun i _ j _ hij => hXr_indep.indepFun hij)]
      have : ∀ i ∈ Finset.range ν, Var[Xr i; P] = Var[Xr 0; P] :=
        fun i _ => (hXr_ident i).variance_eq
      rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hsum_sq : ∫ ω, ((∑ i ∈ Finset.range ν, Xr i ω) - (ν : ℝ) * P[Xr 0]) ^ 2 ∂P =
        (ν : ℝ) * Var[Xr 0; P] := by
      rw [← hvar_sum, variance_eq_integral hsum_meas, hmean_sum]
      congr 1; ext ω; simp [Finset.sum_apply]
    calc ∫ ω, ((Z ν ω x) r) ^ 2 ∂P
        = ∫ ω, ((Real.sqrt ν)⁻¹ ^ 2 *
            ((∑ i ∈ Finset.range ν, Xr i ω) - (ν : ℝ) * P[Xr 0]) ^ 2) ∂P := by
          congr 1; ext ω; rw [hZr_eq ω, mul_pow]
      _ = (Real.sqrt ν)⁻¹ ^ 2 *
            ∫ ω, ((∑ i ∈ Finset.range ν, Xr i ω) - (ν : ℝ) * P[Xr 0]) ^ 2 ∂P :=
          integral_const_mul _ _
      _ = (ν : ℝ)⁻¹ * ((ν : ℝ) * Var[Xr 0; P]) := by
          rw [inv_pow, Real.sq_sqrt hνpos.le, hsum_sq]
      _ = Var[Xr 0; P] := by field_simp
  have hnorm_sq_int : Integrable (fun ω => ‖Z ν ω x‖ ^ 2) P := by
    have hdom : ∀ r : Fin m, Integrable (fun ω => ((Z ν ω x) r) ^ 2) P := by
      intro r
      have hZr_lp : MemLp (fun ω => (Z ν ω x) r) 2 P := by
        have h1 : ∀ i, MemLp (fun ω => (f (s i ω) x) r) 2 P := fun i =>
          ((hident i).comp ((EuclideanSpace.proj r).continuous.measurable.comp (hmeas x))).memLp_iff.mpr <|
            hfx_lp.norm.mono'
              ((EuclideanSpace.proj r).continuous.measurable.comp ((hmeas x).comp (hs 0))).aestronglyMeasurable
              (ae_of_all _ fun ω => PiLp.norm_apply_le _ r)
        have h2 : MemLp (fun ω => Real.sqrt ν * ((ν : ℝ)⁻¹ *
            (∑ i ∈ Finset.range ν, (f (s i ω) x) r) - ((∫ ω', f (s 0 ω') ∂P) x) r)) 2 P :=
          (((memLp_finsetSum _ fun i _ => h1 i).const_mul _).sub (memLp_const _)).const_mul _
        have heq_r : (fun ω => (Z ν ω x) r) = fun ω => Real.sqrt ν * ((ν : ℝ)⁻¹ *
            (∑ i ∈ Finset.range ν, (f (s i ω) x) r) - ((∫ ω', f (s 0 ω') ∂P) x) r) := by
          ext ω
          let ev : E →L[ℝ] ℝ := (EuclideanSpace.proj r).comp (ContinuousMap.evalCLM (R := ℝ) x)
          change ev (Z ν ω) = _
          simp only [Z, map_smul, map_sub, map_sum, smul_eq_mul]
          rfl
        rwa [heq_r]
      exact hZr_lp.integrable_sq
    have heq : (fun ω => ‖Z ν ω x‖ ^ 2) = fun ω => ∑ r : Fin m, ((Z ν ω x) r) ^ 2 := by
      ext ω
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
      simp [Real.norm_eq_abs]
    rw [heq]
    exact integrable_finsetSum _ fun r _ => hdom r
  have hE_sq : ∫ ω, ‖Z ν ω x‖ ^ 2 ∂P = C_x := by
    have heq : (fun ω => ‖Z ν ω x‖ ^ 2) = fun ω => ∑ r : Fin m, ((Z ν ω x) r) ^ 2 := by
      ext ω
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
      simp [Real.norm_eq_abs]
    rw [heq, integral_finsetSum]
    · exact Finset.sum_congr rfl fun r _ => hcoord_sq r
    · intro r _
      have hZr_eq : ∀ ω, ((Z ν ω x) r) ^ 2 ≤ ‖Z ν ω x‖ ^ 2 := fun ω => by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (by
          simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (Z ν ω x) r) 2
      exact hnorm_sq_int.mono'
        ((((EuclideanSpace.proj r).continuous.comp
          (continuous_eval_const x)).measurable.comp (hZ_meas ν)).pow_const 2).aestronglyMeasurable
        (ae_of_all _ fun ω => by
          rw [Real.norm_of_nonneg (sq_nonneg _)]
          exact hZr_eq ω)
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all _ fun ω => sq_nonneg ‖Z ν ω x‖) hnorm_sq_int (R ^ 2)
  rw [hE_sq] at hmarkov
  have hsub : {ω | R < ‖Z ν ω x‖} ⊆ {ω | R ^ 2 ≤ ‖Z ν ω x‖ ^ 2} := fun ω hω =>
    pow_le_pow_left₀ hR_pos.le (le_of_lt hω) 2
  have hR2_gt : C_x / ε ≤ R ^ 2 := by
    have hsq_nn : 0 ≤ Real.sqrt (C_x / ε) := Real.sqrt_nonneg _
    have hsq : Real.sqrt (C_x / ε) ^ 2 = C_x / ε := Real.sq_sqrt (by positivity)
    simp only [R]; nlinarith
  have hprob_le : P.real {ω | R ^ 2 ≤ ‖Z ν ω x‖ ^ 2} ≤ ε := by
    rw [← mul_le_mul_iff_right₀ (by positivity : 0 < R ^ 2)]
    calc R ^ 2 * P.real {ω | R ^ 2 ≤ ‖Z ν ω x‖ ^ 2}
        ≤ C_x := hmarkov
      _ = R ^ 2 * (C_x / R ^ 2) := by field_simp
      _ ≤ R ^ 2 * ε := by
          gcongr
          rw [div_le_iff₀ (by positivity)]
          calc C_x = ε * (C_x / ε) := by field_simp
            _ ≤ ε * R ^ 2 := by gcongr
  calc P {ω | R < ‖Z ν ω x‖}
      ≤ P {ω | R ^ 2 ≤ ‖Z ν ω x‖ ^ 2} := measure_mono hsub
    _ = ENNReal.ofReal (P.real {ω | R ^ 2 ≤ ‖Z ν ω x‖ ^ 2}) := (ofReal_measureReal).symm
    _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hprob_le

/-! ### Part 5: Main theorem `solution` -/

theorem solution {n m : ℕ} {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set (Rn n)) [CompactSpace ↥U] (f : S → C(↥U, Rn m))
    (hmeas : ∀ x : ↥U, Measurable (fun σ => f σ x))
    (s : ℕ → Ω → S) (hs : ∀ i, Measurable (s i))
    (hindep : iIndepFun s P) (hident : ∀ i, IdentDistrib (s i) (s 0) P P)
    (hP3 : ∃ x : ↥U, MemLp (fun ω => f (s 0 ω) x) 2 P)
    (hP4 : ∃ a : S → ℝ, MemLp (fun ω => a (s 0 ω)) 2 P ∧
      ∀ σ : S, ∀ x₁ x₂ : ↥U, ‖f σ x₁ - f σ x₂‖ ≤ a σ * ‖(x₁ : Rn n) - x₂‖) :
    ∃ μG : ProbabilityMeasure C(↥U, Rn m), IsGaussian (μG : Measure C(↥U, Rn m)) ∧
      TendstoInDistribution
        (fun (ν : ℕ) ω => Real.sqrt ν •
          ((ν : ℝ)⁻¹ • ∑ i ∈ Finset.range ν, f (s i ω) - ∫ ω', f (s 0 ω') ∂P))
        atTop id (fun _ => P) (μG : Measure C(↥U, Rn m)) := by
  let E := C(↥U, Rn m)
  obtain ⟨x₀, hx₀_lp⟩ := hP3
  have : Nonempty ↥U := ⟨x₀⟩
  have hf_meas : Measurable f :=
    KingRockAsymp.Distribution.proposition_A1 P U f hmeas s hs hindep hident ⟨x₀, hx₀_lp⟩ hP4
  have hfs_meas : ∀ i, Measurable (fun ω => f (s i ω)) := fun i => hf_meas.comp (hs i)
  obtain ⟨L, hL_meas, hL_nn, hL_lp, hL_lip⟩ :=
    exists_measurable_lip_seminorm P U x₀ f hmeas (s 0) (hs 0) hP4
  have hU_bdd : Bornology.IsBounded (Set.univ : Set ↥U) := isCompact_univ.isBounded
  let diamU : ℝ := Metric.diam (Set.univ : Set ↥U)
  have hdiam_nn : 0 ≤ diamU := Metric.diam_nonneg
  have hdist_le_diam : ∀ x y : ↥U, ‖(x : Rn n) - y‖ ≤ diamU := fun x y => by
    simpa [Subtype.dist_eq, dist_eq_norm] using
      Metric.dist_le_diam_of_mem hU_bdd (Set.mem_univ x) (Set.mem_univ y)
  have hfs0_lp : MemLp (fun ω => f (s 0 ω)) 2 P := by
    have hdom : MemLp (fun ω => ‖f (s 0 ω) x₀‖ + diamU * L (s 0 ω)) 2 P :=
      hx₀_lp.norm.add (hL_lp.const_mul diamU)
    refine hdom.mono' (hfs_meas 0).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    have hrhs_nn : 0 ≤ ‖f (s 0 ω) x₀‖ + diamU * L (s 0 ω) := by
      have := hL_nn (s 0 ω); positivity
    rw [ContinuousMap.norm_le _ hrhs_nn]
    intro x
    calc ‖f (s 0 ω) x‖ ≤ ‖f (s 0 ω) x - f (s 0 ω) x₀‖ + ‖f (s 0 ω) x₀‖ :=
          norm_le_norm_sub_add _ _
      _ ≤ L (s 0 ω) * ‖(x : Rn n) - x₀‖ + ‖f (s 0 ω) x₀‖ := by
          gcongr; exact hL_lip (s 0 ω) x x₀
      _ ≤ L (s 0 ω) * diamU + ‖f (s 0 ω) x₀‖ := by
          gcongr; exact hL_nn _; exact hdist_le_diam x x₀
      _ = ‖f (s 0 ω) x₀‖ + diamU * L (s 0 ω) := by ring
  have hfs0_int : Integrable (fun ω => f (s 0 ω)) P :=
    memLp_one_iff_integrable.mp (hfs0_lp.mono_exponent (by norm_num))
  let Z : ℕ → Ω → E := fun ν ω =>
    Real.sqrt ν • ((ν : ℝ)⁻¹ • ∑ i ∈ Finset.range ν, f (s i ω) - ∫ ω', f (s 0 ω') ∂P)
  have hZ_meas : ∀ ν, Measurable (Z ν) := fun ν =>
    (continuous_const_smul (Real.sqrt ν)).measurable.comp
      (((continuous_const_smul ((ν : ℝ)⁻¹)).measurable.comp
        (Finset.measurable_sum _ fun i _ => hfs_meas i)).sub measurable_const)
  -- Step 1: Convergence of charFunDual via 1D CLT
  have hchar_tendsto : ∀ φ : StrongDual ℝ E,
      Tendsto (fun ν => charFunDual (P.map (Z ν)) φ) atTop
        (𝓝 (Complex.exp (-((Var[fun ω => φ (f (s 0 ω)); P] : ℝ) : ℂ) / 2))) := by
    intro φ
    let X : ℕ → Ω → ℝ := fun i ω => φ (f (s i ω))
    have hX_meas : ∀ i, Measurable (X i) := fun i => φ.continuous.measurable.comp (hfs_meas i)
    have hX_indep : iIndepFun X P :=
      hindep.comp (fun _ σ => φ (f σ)) (fun _ => φ.continuous.measurable.comp hf_meas)
    have hX_ident : ∀ i, IdentDistrib (X i) (X 0) P P := fun i =>
      (hident i).comp (φ.continuous.measurable.comp hf_meas)
    have hX0_lp : MemLp (X 0) 2 P :=
      (hfs0_lp.norm.const_mul ‖φ‖).mono' (hX_meas 0).aestronglyMeasurable
        (ae_of_all _ fun ω => φ.le_opNorm _)
    have hclt := ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub
      (P := P) (P' := gaussianReal 0 Var[X 0; P].toNNReal) (X := X) (Y := id)
      ⟨measurable_id.aemeasurable, Measure.map_id⟩ hX0_lp hX_indep hX_ident
    have hφZ_eq : ∀ ν ω, φ (Z ν ω) =
        (Real.sqrt ν)⁻¹ * (∑ i ∈ Finset.range ν, X i ω - (ν : ℝ) * P[X 0]) := by
      intro ν ω
      simp only [Z, X, map_smul, map_sub, map_sum, smul_eq_mul]
      rw [φ.integral_comp_comm hfs0_int]
      by_cases hν : ν = 0
      · simp [hν]
      · have hνpos : (0 : ℝ) < (ν : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hν)
        have hsq_ne : Real.sqrt ν ≠ 0 := (Real.sqrt_pos.mpr hνpos).ne'
        field_simp
        rw [Real.sq_sqrt hνpos.le]
    let μ_lim : ProbabilityMeasure ℝ := ⟨gaussianReal 0 Var[X 0; P].toNNReal, inferInstance⟩
    have hclt_map : Tendsto (β := ProbabilityMeasure ℝ) (fun ν : ℕ =>
        ⟨P.map (fun ω => φ (Z ν ω)),
          Measure.isProbabilityMeasure_map (φ.continuous.measurable.comp (hZ_meas ν)).aemeasurable⟩)
        atTop (𝓝 μ_lim) := by
      have ht := hclt.tendsto
      have hlim_eq : (⟨(gaussianReal 0 Var[X 0; P].toNNReal).map id,
          Measure.isProbabilityMeasure_map measurable_id.aemeasurable⟩ :
          ProbabilityMeasure ℝ) = μ_lim := by
        apply ProbabilityMeasure.toMeasure_injective
        simp [μ_lim]
      rw [hlim_eq] at ht
      refine ht.congr fun ν => ?_
      apply ProbabilityMeasure.toMeasure_injective
      simp only [ProbabilityMeasure.coe_mk]
      congr 1; ext ω; exact (hφZ_eq ν ω).symm
    have hcf := (ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp hclt_map) 1
    simp only [μ_lim, ProbabilityMeasure.coe_mk, charFun_gaussianReal, Complex.ofReal_one, one_mul,
      Complex.ofReal_zero, zero_mul, zero_sub, one_pow, mul_one,
      Real.coe_toNNReal _ (variance_nonneg _ _), ← neg_div] at hcf
    refine hcf.congr fun ν => ?_
    rw [charFunDual_eq_charFun_map_one, Measure.map_map φ.continuous.measurable (hZ_meas ν)]
    rfl
  -- Step 2: Tightness of {P.map (Z ν) | ν : ℕ}
  let μ : ℕ → ProbabilityMeasure E := fun ν =>
    ⟨P.map (Z ν), Measure.isProbabilityMeasure_map (hZ_meas ν).aemeasurable⟩
  have hTight : IsTightMeasureSet {((m' : ProbabilityMeasure E) : Measure E) |
      m' ∈ Set.range μ} := by
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro ε hε
    rcases eq_or_ne ε ⊤ with rfl | hε_top
    · exact ⟨∅, isCompact_empty, fun _ _ => le_top⟩
    let εr : ℝ := ε.toReal
    have hεr_pos : 0 < εr := ENNReal.toReal_pos hε.ne' hε_top
    have hε_eq : ENNReal.ofReal εr = ε := ENNReal.ofReal_toReal hε_top
    have hchoose : ∀ k : ℕ, ∃ δk > (0 : ℝ), ∀ ν : ℕ,
        P {ω | ∃ x y : ↥U, dist x y < δk ∧ 1 / ((k : ℝ) + 1) < dist (Z ν ω x) (Z ν ω y)} ≤
          ENNReal.ofReal (εr / (2 : ℝ) ^ (k + 2)) :=
      fun k => uniform_equicont_Z P U x₀ f hf_meas s hs hindep hident hfs0_int L hL_meas hL_nn
        hL_lp hL_lip (by positivity) (by positivity)
    choose δ hδ_pos hδ_bound using hchoose
    obtain ⟨F_set, _, hF_fin, hF_cov⟩ :=
      finite_cover_balls_of_compact (isCompact_univ (X := ↥U)) (hδ_pos 0)
    let F : Finset ↥U := hF_fin.toFinset
    have hF_nonempty : F.Nonempty := by
      have ⟨y, hy, _⟩ := Set.mem_iUnion₂.mp (hF_cov (Set.mem_univ x₀))
      exact ⟨y, hF_fin.mem_toFinset.mpr hy⟩
    have hcover : ∀ x : ↥U, ∃ y ∈ F, dist x y < δ 0 := by
      intro x
      obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hF_cov (Set.mem_univ x))
      exact ⟨y, hF_fin.mem_toFinset.mpr hy, hxy⟩
    have hR_each : ∀ y : ↥U, ∃ Ry > (0 : ℝ), ∀ ν : ℕ,
        P {ω | Ry < ‖Z ν ω y‖} ≤ ENNReal.ofReal (εr / (2 * (F.card : ℝ))) := fun y =>
      pointwise_tight_Z P U f hmeas hf_meas s hs hindep hident hfs0_lp hfs0_int y
        (by have : 0 < (F.card : ℝ) := Nat.cast_pos.mpr hF_nonempty.card_pos; positivity)
    choose Rmap hRmap_pos hRmap_le using hR_each
    let R : ℝ := F.sup' hF_nonempty Rmap
    let K : Set E := {g : E | (∀ y ∈ F, ‖g y‖ ≤ R) ∧
      ∀ k : ℕ, ∀ x y : ↥U, dist x y < δ k → dist (g x) (g y) ≤ 1 / ((k : ℝ) + 1)}
    have hK_comp : IsCompact K := isCompact_equicont_set U F R δ hδ_pos hcover
    refine ⟨K, hK_comp, ?_⟩
    rintro _ ⟨_, ⟨ν, rfl⟩, rfl⟩
    simp only [μ, ProbabilityMeasure.coe_mk]
    rw [Measure.map_apply (hZ_meas ν) hK_comp.isClosed.measurableSet.compl]
    have hcompl_sub : Z ν ⁻¹' Kᶜ ⊆
        (⋃ y ∈ F, {ω | Rmap y < ‖Z ν ω y‖}) ∪
        (⋃ k : ℕ, {ω | ∃ x y : ↥U, dist x y < δ k ∧
          1 / ((k : ℝ) + 1) < dist (Z ν ω x) (Z ν ω y)}) := by
      intro ω hω
      simp only [Set.mem_preimage, Set.mem_compl_iff, K, Set.mem_ofPred_eq, not_and_or,
        not_forall, not_le] at hω
      rcases hω with ⟨y, hyF, hyR⟩ | ⟨k, x, y, hxy, hosc⟩
      · left
        refine Set.mem_biUnion hyF ?_
        have hle : Rmap y ≤ R := Finset.le_sup' Rmap hyF
        exact lt_of_le_of_lt hle hyR
      · right
        exact Set.mem_iUnion.mpr ⟨k, x, y, hxy, hosc⟩
    have hpart1 : P (⋃ y ∈ F, {ω | Rmap y < ‖Z ν ω y‖}) ≤ ENNReal.ofReal (εr / 2) := by
      calc P (⋃ y ∈ F, {ω | Rmap y < ‖Z ν ω y‖})
          ≤ ∑ y ∈ F, P {ω | Rmap y < ‖Z ν ω y‖} := measure_biUnion_finset_le F _
        _ ≤ ∑ _y ∈ F, ENNReal.ofReal (εr / (2 * (F.card : ℝ))) :=
            Finset.sum_le_sum fun y _ => hRmap_le y ν
        _ = ENNReal.ofReal ((F.card : ℝ) * (εr / (2 * (F.card : ℝ)))) := by
            rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
              ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        _ = ENNReal.ofReal (εr / 2) := by
            congr 1
            have hFne : (F.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hF_nonempty.card_pos.ne'
            field_simp
    have hpart2 : P (⋃ k : ℕ, {ω | ∃ x y : ↥U, dist x y < δ k ∧
        1 / ((k : ℝ) + 1) < dist (Z ν ω x) (Z ν ω y)}) ≤ ENNReal.ofReal (εr / 2) := by
      have hgeom : Summable (fun k : ℕ => εr / (2 : ℝ) ^ (k + 2)) := by
        have h1 : Summable (fun k : ℕ => (εr / 4) * ((2 : ℝ)⁻¹) ^ k) :=
          (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
        refine h1.congr fun k => ?_
        rw [pow_add, inv_pow]; ring
      have htsum_eq : ∑' k : ℕ, εr / (2 : ℝ) ^ (k + 2) = εr / 2 := by
        have h1 : (fun k : ℕ => εr / (2 : ℝ) ^ (k + 2)) =
            fun k : ℕ => (εr / 4) * ((2 : ℝ)⁻¹) ^ k := by
          ext k; rw [pow_add, inv_pow]; ring
        rw [h1, tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
        ring
      calc P (⋃ k : ℕ, {ω | ∃ x y : ↥U, dist x y < δ k ∧
              1 / ((k : ℝ) + 1) < dist (Z ν ω x) (Z ν ω y)})
          ≤ ∑' k : ℕ, P {ω | ∃ x y : ↥U, dist x y < δ k ∧
              1 / ((k : ℝ) + 1) < dist (Z ν ω x) (Z ν ω y)} := measure_iUnion_le _
        _ ≤ ∑' k : ℕ, ENNReal.ofReal (εr / (2 : ℝ) ^ (k + 2)) :=
            ENNReal.tsum_le_tsum fun k => hδ_bound k ν
        _ = ENNReal.ofReal (∑' k : ℕ, εr / (2 : ℝ) ^ (k + 2)) := by
            rw [ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hgeom]
        _ = ENNReal.ofReal (εr / 2) := by rw [htsum_eq]
    calc P (Z ν ⁻¹' Kᶜ)
        ≤ P ((⋃ y ∈ F, {ω | Rmap y < ‖Z ν ω y‖}) ∪
            (⋃ k : ℕ, {ω | ∃ x y : ↥U, dist x y < δ k ∧
              1 / ((k : ℝ) + 1) < dist (Z ν ω x) (Z ν ω y)})) := measure_mono hcompl_sub
      _ ≤ P (⋃ y ∈ F, {ω | Rmap y < ‖Z ν ω y‖}) +
          P (⋃ k : ℕ, {ω | ∃ x y : ↥U, dist x y < δ k ∧
            1 / ((k : ℝ) + 1) < dist (Z ν ω x) (Z ν ω y)}) := measure_union_le _ _
      _ ≤ ENNReal.ofReal (εr / 2) + ENNReal.ofReal (εr / 2) := add_le_add hpart1 hpart2
      _ = ε := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves, hε_eq]
  -- Step 3: Prokhorov compactness + uniqueness of cluster point via charFunDual
  have hComp : IsCompact (closure (Set.range μ)) :=
    isCompact_closure_of_isTightMeasureSet hTight
  have hmem_cl : ∀ ν : ℕ, μ ν ∈ closure (Set.range μ) :=
    fun ν => subset_closure ⟨ν, rfl⟩
  obtain ⟨μG, _, hμG_cluster⟩ := hComp.exists_mapClusterPt (f := atTop) (u := μ)
    (Filter.tendsto_principal.mpr (Eventually.of_forall hmem_cl))
  have hcluster_char : ∀ (ν₀ : ProbabilityMeasure E), MapClusterPt ν₀ atTop μ →
      ∀ φ : StrongDual ℝ E,
        charFunDual (ν₀ : Measure E) φ =
          Complex.exp (-((Var[fun ω => φ (f (s 0 ω)); P] : ℝ) : ℂ) / 2) := by
    intro ν₀ hν₀ φ
    have hcont : Continuous (fun m' : ProbabilityMeasure E => charFunDual (m' : Measure E) φ) :=
      continuous_charFunDual φ
    have hcl_cf : ClusterPt (charFunDual (ν₀ : Measure E) φ)
        (Filter.map (fun ν => charFunDual (μ ν : Measure E) φ) atTop) :=
      hν₀.map hcont.continuousAt tendsto_map
    exact eq_of_nhds_neBot (hcl_cf.mono (hchar_tendsto φ))
  have hμG_char : ∀ φ : StrongDual ℝ E,
      charFunDual (μG : Measure E) φ =
        Complex.exp (-((Var[fun ω => φ (f (s 0 ω)); P] : ℝ) : ℂ) / 2) :=
    hcluster_char μG hμG_cluster
  have htend_μ : Tendsto μ atTop (𝓝 μG) := by
    refine hComp.tendsto_nhds_of_unique_mapClusterPt (Eventually.of_forall hmem_cl) ?_
    intro ν₀ _ hν₀
    apply ProbabilityMeasure.toMeasure_injective
    apply Measure.ext_of_charFunDual
    ext φ
    rw [hcluster_char ν₀ hν₀ φ, hμG_char φ]
  -- Step 4: μG is Gaussian and Z →_D μG
  have hGauss : IsGaussian (μG : Measure E) := by
    refine isGaussian_of_map_eq_gaussianReal fun φ =>
      ⟨0, Var[fun ω => φ (f (s 0 ω)); P].toNNReal, ?_⟩
    have : IsProbabilityMeasure ((μG : Measure E).map φ) :=
      Measure.isProbabilityMeasure_map φ.continuous.measurable.aemeasurable
    apply Measure.ext_of_charFun
    ext t
    rw [charFun_map_eq_charFunDual_smul, hμG_char (t • φ), charFun_gaussianReal]
    have hvar_smul : Var[fun ω => (t • φ) (f (s 0 ω)); P] =
        t ^ 2 * Var[fun ω => φ (f (s 0 ω)); P] := by
      change Var[fun ω => t * φ (f (s 0 ω)); P] = t ^ 2 * Var[fun ω => φ (f (s 0 ω)); P]
      rw [variance_const_mul]
    rw [hvar_smul, Real.coe_toNNReal _ (variance_nonneg _ _)]
    push_cast
    congr 1; ring
  refine ⟨μG, hGauss, ?_⟩
  exact {
    forall_aemeasurable := fun ν => (hZ_meas ν).aemeasurable
    aemeasurable_limit := measurable_id.aemeasurable
    tendsto := by
      have h_eq : (⟨(μG : Measure E).map id,
          Measure.isProbabilityMeasure_map measurable_id.aemeasurable⟩ :
          ProbabilityMeasure E) = μG := by
        apply ProbabilityMeasure.toMeasure_injective; simp
      rw [h_eq]
      exact htend_μ
  }

end
