-- Prove2me | solution 1 for GlobalTheory.FormalIsogeny.flat_injective_basis_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:58:30.341947+00:00
-- url     : https://prove2.me/submissions/a6e198bc-c0a0-4c5d-892b-8fcb56aa74cb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasSubstEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueFixedPointOfAdicContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
import Theorems.Thm_GlobalTheory_flat_of_isCM_of_quasiFinite


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsLocalRing MvPowerSeries
open GlobalTheory GlobalTheory.FormalIsogeny
variable {R : Type*} [CommRing R] [IsRegularLocalRing R] [IsAdicComplete (maximalIdeal R) R]
  {σ τ : Type*} [Finite σ] [Finite τ]
namespace GlobalTheory.FormalIsogeny
theorem _root_.solution {A B : Type*} [CommRing A] [CommRing B]
    [IsRegularLocalRing A] [IsRegularLocalRing B] (ψ : A →+* B) [IsLocalHom ψ] (hψ : ψ.Finite)
    (hd : ringKrullDim A ≤ ringKrullDim B) :
    ψ.Flat ∧ Function.Injective ψ ∧ @Module.Free A B _ _ ψ.toAlgebra.toModule ∧
      ∃ (n : ℕ) (e : Fin n → B), ∀ g : B, ∃! c : Fin n → A, g = ∑ i, ψ (c i) * e i := by
  letI := ψ.toAlgebra
  have : Module.Finite A B := hψ
  have : IsLocalHom (algebraMap A B) := ‹_›
  have hf : Module.Flat A B := flat_of_isCM_of_quasiFinite (isCM_of_isRegularLocalRing B) hd
  have hfr : Module.Free A B := Module.free_of_flat_of_isLocalRing
  refine ⟨hf, FaithfulSMul.algebraMap_injective A B, hfr, _, Module.finBasis A B, fun g => ?_⟩
  refine ⟨(Module.finBasis A B).equivFun g, ?_, fun c hc => ?_⟩
  · exact ((Module.finBasis A B).sum_equivFun g).symm
  · rw [eq_comm, ← LinearEquiv.eq_symm_apply, Module.Basis.equivFun_symm_apply, hc]
    rfl
end GlobalTheory.FormalIsogeny
