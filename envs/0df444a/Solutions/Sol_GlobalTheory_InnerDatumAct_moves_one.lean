-- Prove2me | solution 1 for GlobalTheory.InnerDatumAct.moves_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:45:23.743621+00:00
-- url     : https://prove2.me/submissions/d7762c1b-5b72-4e68-831c-ec62401dee3c

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
theorem _root_.solution {P : FPair H r} (d : Datum P) : Datum.Moves (1 : V ≃ₗ[E] V) d d := by
  refine ⟨fun x y hxy => ?_, fun x y hxy => ?_, fun x' y' x y hx' hx => ?_⟩
  · rw [Subtype.ext hxy]
  · rw [Subtype.ext hxy]
  · rw [Subtype.ext hx, Subtype.ext hx']
end GlobalTheory.InnerDatumAct
