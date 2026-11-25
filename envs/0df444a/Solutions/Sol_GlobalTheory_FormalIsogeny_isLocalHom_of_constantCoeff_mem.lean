-- Prove2me | solution 1 for GlobalTheory.FormalIsogeny.isLocalHom_of_constantCoeff_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:09:09.857561+00:00
-- url     : https://prove2.me/submissions/9596edef-952c-45b3-86d3-d8cda62ceb63

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasSubstEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueFixedPointOfAdicContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
import Theorems.Thm_GlobalTheory_FormalIsogeny_mem_maximalIdeal_iff_constantCoeff
import Theorems.Thm_GlobalTheory_algHom_sub_constantCoeff_mem
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_C
import Theorems.Thm_GlobalTheory_mvEvalAdic_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_coe
import Theorems.Thm_GlobalTheory_pderivEval_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.mvEvalAdic_C
attribute [local simp] GlobalTheory.mvEvalAdic_X
attribute [local simp] GlobalTheory.mvEvalAdic_coe
attribute [local simp] GlobalTheory.pderivEval_X



set_option autoImplicit false
noncomputable section
open IsLocalRing MvPowerSeries
open GlobalTheory GlobalTheory.FormalIsogeny
variable {R : Type*} [CommRing R] {σ τ : Type*}
variable [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Finite σ]
variable [Finite τ]
omit [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Finite σ]
namespace GlobalTheory.FormalIsogeny
theorem _root_.solution (φ : MvPowerSeries τ R →ₐ[R] MvPowerSeries σ R)
    (h0 : ∀ j, constantCoeff (φ (X j)) ∈ maximalIdeal R) : IsLocalHom φ.toRingHom := by
  refine ((IsLocalRing.local_hom_TFAE _).out 0 3).2 fun g hg => ?_
  have h1 := algHom_sub_constantCoeff_mem φ (K := maximalIdeal _)
    (fun j => mem_maximalIdeal_iff_constantCoeff.2 (h0 j)) g
  have h2 : algebraMap R (MvPowerSeries σ R) (constantCoeff g) ∈ maximalIdeal _ := by
    exact mem_maximalIdeal_iff_constantCoeff.2
      ((mem_maximalIdeal_iff_constantCoeff (g := g)).1 hg)
  simpa using add_mem h1 h2
end GlobalTheory.FormalIsogeny
