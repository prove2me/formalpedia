-- Prove2me | solution 1 for GlobalTheory.exists_average_fixed_approx_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:38:09.116318+00:00
-- url     : https://prove2.me/submissions/b5c8b26f-9644-4424-929a-fc6b4dd0d546

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocallyIntegrableRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFixedAverageApproxOfSubgroupFixed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ContDiff
open GlobalTheory
open MeasureTheory
open scoped ContDiff
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K], ∀ (ρ : G →* (K →L[ℂ] K)), (∀ g v, ‖ρ g v‖ = ‖v‖) → (∀ v, Continuous fun g => ρ g v) → ∀ (H U : Subgroup G), IsOpen (U : Set G) → (∀ y ∈ U, ∀ k ∈ H, y⁻¹ * k * y ∈ H) → ∀ v : K, (∀ k ∈ H, ρ k v = v) → ∀ ε : ℝ, 0 < ε → ∃ η : G → ℂ, Continuous η ∧ HasCompactSupport η ∧ (∀ k ∈ H, ρ k (∫ y, η y • ρ y v ∂μ) = ∫ y, η y • ρ y v ∂μ) ∧ ‖v - ∫ y, η y • ρ y v ∂μ‖ < ε := by
  intro G _ _ _ _ _ _ _ _ μ _ K _ _ _ ρ _ hcont H U hU hconj v hv ε hε
  set W : Set G := (U : Set G) ∩ {y | ‖ρ y v - v‖ < ε / 2} with hW
  have hWo : IsOpen W :=
    hU.inter (isOpen_lt ((hcont v).sub continuous_const).norm continuous_const)
  have h1W : (1 : G) ∈ W := ⟨U.one_mem, by simp [half_pos hε]⟩
  obtain ⟨f, hf1, hf0, hfc, hfI⟩ := exists_continuous_one_zero_of_isCompact
    (isCompact_singleton (x := (1 : G))) hWo.isClosed_compl
    (Set.disjoint_singleton_left.2 fun h => h h1W)
  have hf1' : f 1 = 1 := by simpa using hf1 (Set.mem_singleton (1 : G))
  have hfpos : 0 < ∫ y, f y ∂μ :=
    f.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hfc (fun x => (hfI x).1)
      (x := 1) (by rw [hf1']; norm_num)
  set c := ∫ y, f y ∂μ with hc
  set η : G → ℂ := fun y => ((c⁻¹ * f y : ℝ) : ℂ) with hηdef
  have hηc : Continuous η :=
    Complex.continuous_ofReal.comp (continuous_const.mul f.continuous)
  have hηs : HasCompactSupport η :=
    hfc.comp_left (g := fun r : ℝ => ((c⁻¹ * r : ℝ) : ℂ)) (by simp)
  have hηW : ∀ y, η y ≠ 0 → y ∈ W := by
    intro y hy
    by_contra hyW
    exact hy (by simp [hηdef, hf0 hyW])
  have hηI : Integrable η μ := hηc.integrable_of_hasCompactSupport hηs
  have hint : Integrable (fun y => η y • ρ y v) μ :=
    (hηc.smul (hcont v)).integrable_of_hasCompactSupport hηs.smul_right
  have hnormη : (fun y => ‖η y‖) = fun y => c⁻¹ * f y := by
    funext y
    simp only [hηdef, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (mul_nonneg (inv_nonneg.2 hfpos.le) (hfI y).1)
  have hη1 : ∫ y, η y ∂μ = 1 := by
    simp only [hηdef]
    rw [integral_complex_ofReal, integral_const_mul, inv_mul_cancel₀ hfpos.ne', Complex.ofReal_one]
  refine ⟨η, hηc, hηs, ?_, ?_⟩
  · intro k hk
    rw [← ContinuousLinearMap.integral_comp_comm _ hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [map_smul]
    by_cases hy : η y = 0
    · simp [hy]
    have hyU : y ∈ U := (hηW y hy).1
    congr 1
    have hky : k * y = y * (y⁻¹ * k * y) := by group
    calc ρ k (ρ y v) = ρ (k * y) v := by rw [map_mul]; rfl
      _ = ρ (y * (y⁻¹ * k * y)) v := by rw [hky]
      _ = ρ y (ρ (y⁻¹ * k * y) v) := by rw [map_mul]; rfl
      _ = ρ y v := by rw [hv _ (hconj y hyU k hk)]
  · have hsplit : v - ∫ y, η y • ρ y v ∂μ = ∫ y, η y • (v - ρ y v) ∂μ := by
      simp_rw [smul_sub]
      rw [integral_sub (hηI.smul_const v) hint, integral_smul_const, hη1, one_smul]
    rw [hsplit]
    calc ‖∫ y, η y • (v - ρ y v) ∂μ‖ ≤ ∫ y, ‖η y‖ * (ε / 2) ∂μ := by
          refine norm_integral_le_of_norm_le (hηI.norm.mul_const _)
            (Filter.Eventually.of_forall fun y => ?_)
          rw [norm_smul]
          by_cases hy : η y = 0
          · simp [hy]
          exact mul_le_mul_of_nonneg_left
            (by rw [norm_sub_rev]; exact (hηW y hy).2.le) (norm_nonneg _)
      _ = ε / 2 := by
          rw [integral_mul_const, hnormη, integral_const_mul, inv_mul_cancel₀ hfpos.ne', one_mul]
      _ < ε := half_lt_self hε
end _root_.GlobalTheory
end GlobalTheory
