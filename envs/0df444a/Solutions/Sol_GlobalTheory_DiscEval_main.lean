-- Prove2me | solution 1 for GlobalTheory.DiscEval.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:47:56.730058+00:00
-- url     : https://prove2.me/submissions/82c22a25-96e8-40b3-bdfd-20f8349a450f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FinCorePf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_BasisChangePf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsUnitEvalOfMapResidueNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ResidueNormValuationSubringEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SummableNormBoundedSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_BoundedOnFramesIffIntegralOnFrames
import Theorems.Thm_GlobalTheory_DiscEval_coeff_laurent
import Theorems.Thm_GlobalTheory_DiscEval_discEvalAway_eq
import Theorems.Thm_GlobalTheory_DiscEval_hasSum_laurent
import Theorems.Thm_GlobalTheory_DiscEval_tendsto_norm_laurent_term
import Theorems.Thm_GlobalTheory_DiscEval_residueFieldInfiniteOn_algField
import Theorems.Thm_GlobalTheory_DiscEval_algDisc_dense
import Theorems.Thm_GlobalTheory_DiscEval_mul_mem_algDisc
import Theorems.Thm_GlobalTheory_DiscEval_isAdicComplete_integralClosure
import Theorems.Thm_GlobalTheory_DiscEval_finite_residueField_integralClosure
import Theorems.Thm_GlobalTheory_DiscEval_mem_genField_of_mem
import Theorems.Thm_GlobalTheory_DiscEval_isLocalHom_of_intEmb_eq_discEval
import Theorems.Thm_GlobalTheory_DiscEval_IsDiscPoint_comp_algebraMap
import Theorems.Thm_GlobalTheory_DiscEval_exists_isDiscPoint
import Theorems.Thm_GlobalTheory_DiscEval_boundedOnFrames_iff_integralOnFrames
import Theorems.Thm_GlobalTheory_DiscEval_BoundedOnFrames_norm_coeff_linear_le
import Theorems.Thm_GlobalTheory_BoundedPowerSeriesDisc_evalBounded_C
import Theorems.Thm_GlobalTheory_BoundedPowerSeriesDisc_evalBounded_X
import Theorems.Thm_GlobalTheory_IsPolynomialFunction_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.BoundedPowerSeriesDisc.evalBounded_C
attribute [local simp] GlobalTheory.BoundedPowerSeriesDisc.evalBounded_X



set_option autoImplicit false
open GlobalTheory GlobalTheory.DiscEval
open Filter Topology IsLocalRing
open scoped PowerSeries LaurentSeries
open MvPolynomial
namespace GlobalTheory.DiscEval
theorem _root_.solution (p : ℕ) [Fact p.Prime] :
    (ReciprocityTheory.MultiplicativeHeights.ResidueFieldInfiniteOn (algField p : Set ℂ_[p]) ∧
      (∀ t ∈ algDisc p, 0 < ‖t‖ ∧ ‖t‖ < 1) ∧
      (∀ r : ℝ, 0 < r → r < 1 → ∀ ε > (0 : ℝ), ∃ t ∈ algDisc p, |‖t‖ - r| < ε) ∧
      ∀ t ∈ algDisc p, ∀ τ ∈ algField p, ‖τ‖ = 1 → t * τ ∈ algDisc p) ∧
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[p] O] [Module.Finite ℤ_[p] O] (i : O →+* ℂ_[p])
      (hi : ∀ x, ‖i x‖ ≤ 1) (_ : Function.Injective i) (π : O) (hπ : i π ≠ 0)
      (A : Type) [CommRing A] [Algebra O⟦X⟧ A]
      [IsLocalization.Away (PowerSeries.C π * PowerSeries.X : O⟦X⟧) A],
      (∀ (t : ℂ_[p]) (ht0 : t ≠ 0) (ht : ‖t‖ < 1),
        (∀ f : O⟦X⟧,
          HasSum (fun n : ℕ => i (PowerSeries.coeff n f) * t ^ n) (discEval i hi ht f) ∧
          discEvalAway π A i hi hπ ht0 ht (algebraMap O⟦X⟧ A f) = discEval i hi ht f) ∧
        (∀ T : Set ℂ_[p], T.Finite → T ⊆ algField p → t ∈ T →
          (fieldEmb (genField i T)).fieldRange = Subfield.closure (Set.range i ∪ T) ∧
          ∃ (_ : FiniteDimensional ℚ_[p] (genField i T))
            (_ : IsDiscreteValuationRing (integralClosure ℤ_[p] (genField i T))),
            IsAdicComplete (maximalIdeal (integralClosure ℤ_[p] (genField i T)))
              (integralClosure ℤ_[p] (genField i T)) ∧
            Finite (ResidueField (integralClosure ℤ_[p] (genField i T))) ∧
            IsFractionRing (integralClosure ℤ_[p] (genField i T)) (genField i T) ∧
            ∃ (ev : O⟦X⟧ →+* integralClosure ℤ_[p] (genField i T)) (evA : A →+* genField i T),
              (∀ f, intEmb _ (ev f) = discEval i hi ht f) ∧
              (∀ f, fieldEmb _ (evA f) = discEvalAway π A i hi hπ ht0 ht f) ∧
              evA.comp (algebraMap O⟦X⟧ A) = (algebraMap _ (genField i T)).comp ev ∧
              IsLocalHom ev ∧ (ev.comp PowerSeries.C).Finite ∧
              IsLocalHom (ev.comp PowerSeries.C)) ∧
        (∀ f : A,
          Tendsto (fun n : ℤ => ‖(laurent π A i hπ f).coeff n * t ^ n‖) cofinite (𝓝 0) ∧
          HasSum (fun n : ℤ => (laurent π A i hπ f).coeff n * t ^ n)
            (discEvalAway π A i hi hπ ht0 ht f)) ∧
        ∀ (f : A) (a b : ℕ) (f₀ : O⟦X⟧),
          f * algebraMap O⟦X⟧ A (PowerSeries.C π ^ a * PowerSeries.X ^ b) = algebraMap O⟦X⟧ A f₀ →
          discEvalAway π A i hi hπ ht0 ht f = (i π)⁻¹ ^ a * t⁻¹ ^ b * discEval i hi ht f₀ ∧
          ∀ n : ℤ, (laurent π A i hπ f).coeff n =
            if n + b < 0 then 0 else (i π)⁻¹ ^ a * i (PowerSeries.coeff (n + b).natAbs f₀)) ∧
      ∀ (ι : Type) [Fintype ι] (n : ι → Type) [∀ s, Fintype (n s)] [∀ s, DecidableEq (n s)]
        (F : MvPolynomial (EntryIndex n n) A),
        (BoundedOnFrames i hi hπ F ↔ IntegralOnFrames i hi hπ F) ∧
        ∀ d : ℕ, F.IsHomogeneous d → BoundedOnFrames i hi hπ F →
          ∀ (B : EntryIndex n n → EntryIndex n n → ℂ_[p]) (c : ℝ), 1 ≤ c → (∀ k l, ‖B k l‖ ≤ c) →
            ∀ (μ : EntryIndex n n →₀ ℕ) (m : ℤ),
              ‖(coeff μ (bind₁ (fun k => ∑ l, C (HahnSeries.C (B k l)) * X l)
                (map (laurent π A i hπ) F))).coeff m‖ ≤ c ^ d ∧
              (m < 0 → (coeff μ (bind₁ (fun k => ∑ l, C (HahnSeries.C (B k l)) * X l)
                (map (laurent π A i hπ) F))).coeff m = 0) := by
  refine ⟨⟨residueFieldInfiniteOn_algField p, fun _ ht => ht.2, algDisc_dense p, mul_mem_algDisc p⟩,
    fun O _ _ _ i hi hinj π hπ A _ _ _ => ⟨fun t ht0 ht => ⟨fun f =>
      ⟨hasSum_discEval i hi ht f, discEvalAway_algebraMap π A i hi hπ ht0 ht f⟩,
      fun T hT hTK htT => ⟨fieldRange_genField i hi hTK, ?_⟩,
      fun f => ⟨tendsto_norm_laurent_term i hi hπ ht0 ht f, hasSum_laurent i hi hπ ht0 ht f⟩,
      fun f a b f₀ h => ⟨discEvalAway_eq i hi hπ ht0 ht h, coeff_laurent i hπ h⟩⟩,
    fun ι _ n _ _ F => ⟨boundedOnFrames_iff_integralOnFrames i hi hπ F,
      fun d hd hF B c hc hB μ m => hF.norm_coeff_linear_le hd hc hB μ m⟩⟩⟩
  have := finiteDimensional_genField i hi hT
  obtain ⟨ev, evA, h⟩ := exists_isDiscPoint i hi hπ A (genField i T) (map_mem_genField i hi hTK)
    (mem_genField_of_mem i hi hTK htT) ht0 ht
  have hj : ∀ a, intEmb _ (ev.comp PowerSeries.C a) = i a := fun a => by simp [h.1]
  exact ⟨this, inferInstance, isAdicComplete_integralClosure _,
    finite_residueField_integralClosure _, inferInstance, ev, evA, h.1, h.2, h.comp_algebraMap,
    isLocalHom_of_intEmb_eq_discEval i hi _ hinj ht h.1, finite_of_intEmb_eq i hi _ hj,
    isLocalHom_of_intEmb_eq i hi _ hinj hj⟩
end GlobalTheory.DiscEval
