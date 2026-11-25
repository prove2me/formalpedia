-- Prove2me | solution 1 for GlobalTheory.QCoh.isSMulRegular_sections_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:20:45.330888+00:00
-- url     : https://prove2.me/submissions/3dc427c9-a3b2-483a-9023-f12e034330bb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsLocalizedModuleGermLinearPointOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_TopologicalKrullDimLeOfIrreducibleCloseds
import Theorems.Thm_GlobalTheory_QCoh_pointOfPrime_mem_assPoints_iff
import Theorems.Thm_GlobalTheory_QCoh_mem_primeCompl_primeIdealOf_iff
import Theorems.Thm_GlobalTheory_QCoh_primeIdealOf_pointOfPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.QCoh.primeIdealOf_pointOfPrime



set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite TensorProduct IsLocalRing
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} {F G H : X.Modules} {U V : X.Opens}
variable [IsLocallyNoetherian X]
namespace GlobalTheory.QCoh
theorem _root_.solution [F.IsQuasicoherent] (hU : IsAffineOpen U) (f : Γ(X, U)) :
    IsSMulRegular Γ(F, U) f ↔ assPoints F ∩ U ⊆ X.basicOpen f := by
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have h : f ∈ (⋃ p ∈ associatedPrimes Γ(X, U) Γ(F, U), (p : Set Γ(X, U))) ↔
      ¬ IsSMulRegular Γ(F, U) f := by
    rw [biUnion_associatedPrimes_eq_compl_regular]; rfl
  rw [← not_iff_not, ← h, Set.mem_iUnion₂, Set.not_subset]
  constructor
  · rintro ⟨P, hP, hf⟩
    let y := pointOfPrime hU ⟨P, hP.isPrime⟩
    refine ⟨y, ⟨(pointOfPrime_mem_assPoints_iff hU _).2 hP, y.2⟩, fun hy ↦ ?_⟩
    have := (mem_primeCompl_primeIdealOf_iff hU y f).2 hy
    rw [Ideal.mem_primeCompl_iff, primeIdealOf_pointOfPrime] at this
    exact this hf
  · rintro ⟨x, ⟨hx, hxU⟩, hf⟩
    refine ⟨_, (mem_assPoints_iff_primeIdealOf hU ⟨x, hxU⟩).1 hx, ?_⟩
    by_contra hf'
    exact hf ((mem_primeCompl_primeIdealOf_iff hU ⟨x, hxU⟩ f).1 hf')
end GlobalTheory.QCoh
