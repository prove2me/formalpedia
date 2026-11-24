-- Prove2me | solution 1 for GlobalTheory.RankFibreKer.tw_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:51:47.146866+00:00
-- url     : https://prove2.me/submissions/497683e0-5006-4075-82da-2357a785ad7f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FullRankSB
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OmAOneApply
import Theorems.Thm_GlobalTheory_SplitFlip_apow_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil
open GlobalTheory GlobalTheory.RankFibreKer
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.RankFibreKer
theorem _root_.solution (ν : kˣ →* ℂˣ) (d : ℕ) {a : ℕ} (g : GL (Fin a) k) : tw ν d g ≠ 0 :=
  mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _)
end GlobalTheory.RankFibreKer
