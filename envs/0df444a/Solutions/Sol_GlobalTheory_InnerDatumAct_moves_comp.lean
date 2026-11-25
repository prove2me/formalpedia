-- Prove2me | solution 1 for GlobalTheory.InnerDatumAct.moves_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:45:20.532803+00:00
-- url     : https://prove2.me/submissions/38bb2d00-2bc0-4bb2-8724-4cc1d437b3c4

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsComplementUnitaryMulActionLocalInnerDatum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution {P : FPair H r} {g g' : V ≃ₗ[E] V} (hg : InU P g) {d₁ d₂ d₃ : Datum P}
    (h₁₂ : Datum.Moves g d₁ d₂) (h₂₃ : Datum.Moves g' d₂ d₃) : Datum.Moves (g' * g) d₁ d₃ := by
  refine ⟨fun x y hxy => ?_, fun x y hxy => ?_, fun x' y' x y hx' hx => ?_⟩
  · exact (h₁₂.1 x ⟨g x, hg.1.mem_perp x.2⟩ rfl).trans
      (h₂₃.1 _ y (by rw [hxy, LinearEquiv.mul_apply]))
  · exact (h₁₂.2.1 x ⟨g x, hg.2.mem_perp x.2⟩ rfl).trans
      (h₂₃.2.1 _ y (by rw [hxy, LinearEquiv.mul_apply]))
  · exact (h₁₂.2.2 x' ⟨g x', hg.2.mem_perp x'.2⟩ x ⟨g x, hg.1.mem_perp x.2⟩ rfl rfl).trans
      (h₂₃.2.2 _ y' _ y (by rw [hx', LinearEquiv.mul_apply]) (by rw [hx, LinearEquiv.mul_apply]))
end GlobalTheory.InnerDatumAct
