-- Prove2me | solution 1 for GlobalTheory.InnerDatumAct.datum_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:43:41.279786+00:00
-- url     : https://prove2.me/submissions/43373421-8091-43e7-9eb5-cb1430863b49

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
theorem _root_.solution {P : FPair H r} {d₁ d₂ : Datum P} (hL : d₁.L = d₂.L) (hL' : d₁.L' = d₂.L')
    (hio : d₁.io = d₂.io) : d₁ = d₂ := by
  cases d₁; cases d₂
  simp only at hL hL' hio
  subst hL hL' hio
  rfl
end GlobalTheory.InnerDatumAct
