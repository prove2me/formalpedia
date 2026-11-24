-- Prove2me | solution 1 for GlobalTheory.RootEx.Supp.bd_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:03:14.122993+00:00
-- url     : https://prove2.me/submissions/45681feb-8d5d-4b73-a2a1-eb282330fc2a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CharEqOneOfOpENeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Supp
variable {k : Type} [Field k] [ValuativeRel k]
namespace GlobalTheory.RootEx.Supp
theorem _root_.solution {ι : Type} [DecidableEq ι] : Bd 1 (1 : Matrix ι ι k) := by
  intro r s
  rw [Matrix.one_apply]
  split_ifs <;> simp
end GlobalTheory.RootEx.Supp
