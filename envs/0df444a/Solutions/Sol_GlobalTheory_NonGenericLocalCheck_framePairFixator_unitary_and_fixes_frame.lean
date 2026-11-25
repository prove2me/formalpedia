-- Prove2me | solution 1 for GlobalTheory.NonGenericLocalCheck.framePairFixator_unitary_and_fixes_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:49:02.545476+00:00
-- url     : https://prove2.me/submissions/6bc6bbae-54af-4c42-b313-b57d9d488441

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_TransversalityLocal_FramePairFixatorUnitaryAndFixesFrame

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG
open GlobalTheory GlobalTheory.NonGenericLocalCheck
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E}
variable {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}
namespace GlobalTheory.NonGenericLocalCheck
theorem _root_.solution (P : FPair H r) {g : V ≃ₗ[E] V} (hg : g ∈ P.UW0) :
    IsUnitary H g ∧ ∀ b, g (P.A.f b) = P.A.f b ∧ g (P.B.f b) = P.B.f b := by
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one => exact ⟨fun x y => rfl, fun b => ⟨rfl, rfl⟩⟩
  | mul x y _ _ hx hy =>
    have hxu : ∀ u w, H.h (x u) (x w) = H.h u w := hx.1
    have hyu : ∀ u w, H.h (y u) (y w) = H.h u w := hy.1
    refine ⟨fun u w => ?_, fun b => ⟨?_, ?_⟩⟩
    · change H.h (x (y u)) (x (y w)) = H.h u w
      rw [hxu, hyu]
    · change x (y _) = _
      rw [(hy.2 b).1, (hx.2 b).1]
    · change x (y _) = _
      rw [(hy.2 b).2, (hx.2 b).2]
  | inv x _ hx =>
    have hxu : ∀ u w, H.h (x u) (x w) = H.h u w := hx.1
    refine ⟨fun u w => ?_, fun b => ⟨?_, ?_⟩⟩
    · change H.h (x.symm u) (x.symm w) = H.h u w
      have key := hxu (x.symm u) (x.symm w)
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at key
      exact key.symm
    · change x.symm _ = _
      rw [LinearEquiv.symm_apply_eq]
      exact ((hx.2 b).1).symm
    · change x.symm _ = _
      rw [LinearEquiv.symm_apply_eq]
      exact ((hx.2 b).2).symm
end GlobalTheory.NonGenericLocalCheck
