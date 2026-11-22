-- Prove2me | solution 1 for MarkushevichBasis.fourierLp_one_isMarkushevichBasis
-- status  : ACCEPTED   (prove)
-- author  : @RSoulat
-- created : 2026-11-22T18:58:45.762053+00:00
-- url     : https://prove2.me/submissions/fa3c688c-4e54-404d-ac99-99b39b821a91

import Mathlib
import Definitions.Def_MarkushevichBasis_Basic

open MeasureTheory AddCircle MarkushevichBasis Filter Topology Set

set_option autoImplicit false
set_option maxHeartbeats 800000

private theorem eq_zero_of_fourierCoeff_eq_zero (T : ℝ) [Fact (0 < T)]
    (g : Lp ℂ 1 (haarAddCircle (T := T)))
    (hg : ∀ n : ℤ, fourierCoeff (⇑g) n = 0) : g = 0 := by
  let μ := haarAddCircle (T := T)
  have hInt (f : C(AddCircle T, ℂ)) : Integrable (fun x => f x * g x) μ :=
    (L1.integrable_coeFn g).bdd_mul f.continuous.aestronglyMeasurable
      (Eventually.of_forall f.norm_coe_le_norm)
  let l : C(AddCircle T, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∫ x, f x * g x ∂μ
      map_add' := fun f h => by
        simp only [ContinuousMap.add_apply, add_mul]
        exact integral_add (hInt f) (hInt h)
      map_smul' := fun c f => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul,
          RingHom.id_apply] }
  let L := l.mkContinuous ‖g‖ fun f => by
    calc
      ‖l f‖ ≤ ∫ x, ‖f x * g x‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ x, ‖f‖ * ‖g x‖ ∂μ := by
        apply integral_mono (hInt f).norm ((L1.integrable_coeFn g).norm.const_mul ‖f‖)
        intro x
        change ‖f x * g x‖ ≤ ‖f‖ * ‖g x‖
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (f.norm_coe_le_norm x) (norm_nonneg _)
      _ = ‖g‖ * ‖f‖ := by rw [integral_const_mul, ← L1.norm_eq_integral_norm, mul_comm]
  have hPolynomials : Submodule.span ℂ (range (fun n : ℤ => fourier (T := T) n)) ≤ L.ker := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨n, rfl⟩
    change (∫ x : AddCircle T, fourier n x * g x ∂μ) = 0
    simpa only [fourierCoeff, neg_neg, smul_eq_mul] using hg (-n)
  have hZero (f : C(AddCircle T, ℂ)) : (∫ x, f x * g x ∂μ) = 0 :=
    closure_minimal hPolynomials L.isClosed_ker
      ((Submodule.dense_iff_topologicalClosure_eq_top.mpr span_fourier_closure_eq_top) f)
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  refine ae_eq_zero_of_forall_setIntegral_isClosed_eq_zero (L1.integrable_coeFn g) ?_
  intro S hS
  rcases S.eq_empty_or_nonempty with rfl | hSnon
  · simp
  let a (x : AddCircle T) : ℝ := (1 + Metric.infDist x S)⁻¹
  have ha0 (x : AddCircle T) : 0 ≤ a x := by
    have hd : 0 ≤ Metric.infDist x S := Metric.infDist_nonneg
    dsimp [a]
    exact inv_nonneg.mpr (by linarith)
  have ha1 (x : AddCircle T) : a x ≤ 1 := by
    have hd : 0 ≤ Metric.infDist x S := Metric.infDist_nonneg
    dsimp [a]
    exact inv_le_one_of_one_le₀ (by linarith)
  have haCont : Continuous a :=
    (continuous_const.add (Metric.continuous_infDist_pt S)).inv₀ (fun x => by
      have hd : 0 ≤ Metric.infDist x S := Metric.infDist_nonneg
      change 1 + Metric.infDist x S ≠ 0
      exact ne_of_gt (by linarith))
  let f (n : ℕ) : C(AddCircle T, ℂ) := ⟨fun x => ((a x ^ n : ℝ) : ℂ),
    Complex.continuous_ofReal.comp (haCont.pow n)⟩
  have hDom := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun n x => f n x * g x) (f := S.indicator (⇑g)) (fun x => ‖g x‖)
    (fun n => (hInt (f n)).aestronglyMeasurable) (L1.integrable_coeFn g).norm
    (fun n => Eventually.of_forall fun x => by
      change ‖((a x ^ n : ℝ) : ℂ) * g x‖ ≤ ‖g x‖
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg (ha0 x) n)]
      exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (ha0 x) (ha1 x)))
    (Eventually.of_forall fun x => by
      by_cases hx : x ∈ S
      · simp [f, a, Metric.infDist_zero_of_mem hx, hx]
      · have hd := (hS.notMem_iff_infDist_pos hSnon).mp hx
        have hlt : a x < 1 := inv_lt_one_of_one_lt₀ (by linarith)
        have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (ha0 x) hlt
        simpa [f, hx] using ((Complex.continuous_ofReal.tendsto 0).comp hp).mul
          (tendsto_const_nhds (x := g x)))
  have hConst : Tendsto (fun n => ∫ x, f n x * g x ∂μ) atTop (𝓝 (0 : ℂ)) := by
    simpa only [hZero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
  rw [← integral_indicator hS.measurableSet]
  exact tendsto_nhds_unique hDom hConst

theorem solution (T : ℝ) [Fact (0 < T)] :
    ∃ c : ℤ → StrongDual ℂ (Lp ℂ 1 (haarAddCircle (T := T))),
      (∀ (n : ℤ) (g : Lp ℂ 1 (haarAddCircle (T := T))), c n g = fourierCoeff (⇑g) n) ∧
      IsMarkushevichBasis (fun n : ℤ => fourierLp (T := T) 1 n) c := by
  let μ := haarAddCircle (T := T)
  let l (n : ℤ) : Lp ℂ 1 μ →ₗ[ℂ] ℂ :=
    { toFun := fun g => fourierCoeff (⇑g) n
      map_add' := fun g h => by
        rw [fourierCoeff_congr_ae (Lp.coeFn_add g h),
          fourierCoeff.add (L1.integrable_coeFn g) (L1.integrable_coeFn h)]
        rfl
      map_smul' := fun a g => by
        rw [fourierCoeff_congr_ae (Lp.coeFn_smul a g), fourierCoeff.const_smul]
        rfl }
  let c (n : ℤ) : StrongDual ℂ (Lp ℂ 1 μ) := (l n).mkContinuous 1 fun g => by
    change ‖∫ x : AddCircle T, fourier (-n) x • g x ∂μ‖ ≤ _
    refine (norm_integral_le_integral_norm _).trans ?_
    simp only [norm_smul, fourier_apply, Circle.norm_coe, one_mul, L1.norm_eq_integral_norm]
    rfl
  refine ⟨c, fun _ _ => rfl, ?_⟩
  have hCoeff (n m : ℤ) : c n (fourierLp (T := T) 1 m) = (Pi.single m (1 : ℂ) : ℤ → ℂ) n := by
    change fourierCoeff (fourierLp (T := T) 1 m) n = _
    rw [fourierCoeff_congr_ae (coeFn_fourierLp 1 m), fourierCoeff_fourier]
  refine ⟨fun i => ?_, fun i j hij => ?_, ?_, fun g hg => eq_zero_of_fourierCoeff_eq_zero T g hg⟩
  · simp [hCoeff]
  · simp [hCoeff, hij]
  · exact Submodule.dense_iff_topologicalClosure_eq_top.mpr
      (span_fourierLp_closure_eq_top (by norm_num))
