-- Prove2me | solution 1 for GlobalTheory.LocalFiniteOddFixed.precomplete_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:49:11.388298+00:00
-- url     : https://prove2.me/submissions/eebc73fb-8e76-475a-87bb-557ecd7db70c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.LocalFiniteOddFixed
namespace GlobalTheory.LocalFiniteOddFixed
theorem _root_.solution (O : Type) [CommRing O] (I : Ideal O) [IsPrecomplete I O]
    (M : Type) [AddCommGroup M] [Module O M] [Module.Finite O M] : IsPrecomplete I M := by
  rw [← AdicCompletion.of_surjective_iff]
  intro z
  obtain ⟨t, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite I M z
  induction t with
  | zero => exact ⟨0, by simp⟩
  | tmul r x =>
    obtain ⟨a, rfl⟩ := AdicCompletion.of_surjective I O r
    refine ⟨a • x, ?_⟩
    rw [AdicCompletion.ofTensorProduct_tmul, map_smul]
    ext n
    rfl
  | add a b ha hb =>
    obtain ⟨x, hx⟩ := ha
    obtain ⟨y, hy⟩ := hb
    exact ⟨x + y, by rw [map_add, map_add, hx, hy]⟩
end GlobalTheory.LocalFiniteOddFixed
