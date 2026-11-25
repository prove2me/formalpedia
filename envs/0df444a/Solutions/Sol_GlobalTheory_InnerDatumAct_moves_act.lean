-- Prove2me | solution 1 for GlobalTheory.InnerDatumAct.moves_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:45:18.891104+00:00
-- url     : https://prove2.me/submissions/183bd094-367f-43c6-847b-2c5a18066f10

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
theorem _root_.solution {P : FPair H r} {g : V ≃ₗ[E] V} (hg : InU P g) (d : Datum P) :
    Datum.Moves g d (act hg d) := by
  refine ⟨fun x y hxy => ?_, fun x y hxy => ?_, fun x' y' x y hx' hx => ?_⟩
  · show _ ↔ _ ∈ d.L.map _
    rw [mem_map_wMap, wMap_symm_of_eq hg.1 hxy]
  · show _ ↔ _ ∈ d.L'.map _
    rw [mem_map_wMap, wMap_symm_of_eq hg.2 hxy]
  · show _ ↔ (wMap hg.2.symm _, wMap hg.1.symm _) ∈ d.io
    rw [wMap_symm_of_eq hg.2 hx', wMap_symm_of_eq hg.1 hx]
end GlobalTheory.InnerDatumAct
