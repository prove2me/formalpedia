-- Prove2me | solution 1 for GlobalTheory.SemilinearModule.invariantsFunctor_full
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:43:02.14126+00:00
-- url     : https://prove2.me/submissions/25bad0bb-2108-4d9f-83c1-b7d4fd113b10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
import Theorems.Thm_GlobalTheory_FreeQuotient_isBaseChange_invariants
import Theorems.Thm_GlobalTheory_FreeQuotient_existsUnique_equivariant_extension
import Theorems.Thm_GlobalTheory_FreeQuotient_coe_toInvariantsTensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FreeQuotient.coe_toInvariantsTensor

set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
universe w v u
open CategoryTheory
open GlobalTheory.SemilinearModule
attribute [instance] addCommGroup module action semilinear
variable (G : Type v) [Group G] (A : Type u) [CommRing A] [MulSemiringAction G A]
variable {G A}
namespace GlobalTheory.SemilinearModule
theorem _root_.solution [Finite G] (h : IsFreeRingAction G A) :
    (invariantsFunctor.{w} G A).Full where
  map_surjective {M N} φ := by
    obtain ⟨f, ⟨hf, hf'⟩, -⟩ := FreeQuotient.existsUnique_equivariant_extension
      (FreeQuotient.isBaseChange_invariants (FixedPoints.subring A G) M.carrier h) φ.hom
    exact ⟨⟨f, hf⟩, ModuleCat.hom_ext (LinearMap.ext fun x ↦ Subtype.ext (hf' x))⟩
end GlobalTheory.SemilinearModule
