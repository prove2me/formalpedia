-- Prove2me | solution 1 for GlobalTheory.T.exists_complementUnitary_mulAction_localInnerDatum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:34:58.100298+00:00
-- url     : https://prove2.me/submissions/3be9b02c-76c8-4ac9-bd97-9645d88ad900

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsComplementUnitaryMulActionLocalInnerDatum
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsComplementUnitaryMulActionLocalInnerDatumStatement
import Theorems.Thm_GlobalTheory_InnerDatumAct_exists_mulAction


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∃ act : MulAction P.UW0 (LocNG.Datum P), (∀ (g : P.UW0) d d', LocNG.Datum.Moves g.1 d d' ↔ act.smul g d = d') ∧ ∀ d (g : P.UW0), g.1 ∈ LocNG.Datum.Stab d ↔ act.smul g d = d := by
  first | exact @GlobalTheory.InnerDatumAct.exists_mulAction | exact GlobalTheory.InnerDatumAct.exists_mulAction | (intros; apply GlobalTheory.InnerDatumAct.exists_mulAction <;> assumption)
end _root_.GlobalTheory.T
