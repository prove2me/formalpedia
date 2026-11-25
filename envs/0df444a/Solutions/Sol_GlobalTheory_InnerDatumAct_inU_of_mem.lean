-- Prove2me | solution 1 for GlobalTheory.InnerDatumAct.inU_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:45:17.327204+00:00
-- url     : https://prove2.me/submissions/f1eeb19f-e31a-4de4-8419-83777fe9ecfb

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsComplementUnitaryMulActionLocalInnerDatum
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical
noncomputable section
open GlobalTheory GlobalTheory.InnerDatumAct
open Formalism.MainNotions.S.LocNG
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}
namespace GlobalTheory.InnerDatumAct
theorem _root_.solution {P : FPair H r} {g : V ≃ₗ[E] V} (hg : g ∈ P.UW0) : InU P g := by
  unfold FPair.UW0 at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact ⟨⟨hx.1, fun b => (hx.2 b).1⟩, ⟨hx.1, fun b => (hx.2 b).2⟩⟩
  | one => exact ⟨⟨fun _ _ => rfl, fun _ => rfl⟩, ⟨fun _ _ => rfl, fun _ => rfl⟩⟩
  | mul x y _ _ hx hy =>
    refine ⟨⟨fun a b => ?_, fun b => ?_⟩, ⟨fun a b => ?_, fun b => ?_⟩⟩ <;>
      simp only [LinearEquiv.mul_apply]
    · rw [hx.1.1, hy.1.1]
    · rw [hy.1.2, hx.1.2]
    · rw [hx.1.1, hy.1.1]
    · rw [hy.2.2, hx.2.2]
  | inv x _ hx => exact ⟨hx.1.symm, hx.2.symm⟩
end GlobalTheory.InnerDatumAct
