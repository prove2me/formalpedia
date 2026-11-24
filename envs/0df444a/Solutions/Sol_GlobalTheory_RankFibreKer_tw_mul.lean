-- Prove2me | solution 1 for GlobalTheory.RankFibreKer.tw_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:51:46.262622+00:00
-- url     : https://prove2.me/submissions/f25ea1d7-122f-4d17-97ab-aece63475022

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FullRankSB
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OmAOneApply
import Theorems.Thm_GlobalTheory_SplitFlip_gdet_mul


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
theorem _root_.solution (ν : kˣ →* ℂˣ) (d : ℕ) {a : ℕ} (g x : GL (Fin a) k) : tw ν d (g * x) = tw ν d g * tw ν d x := by
  simp only [tw, gdet_mul, map_mul, Units.val_mul, apow_mul]; ring
end GlobalTheory.RankFibreKer
