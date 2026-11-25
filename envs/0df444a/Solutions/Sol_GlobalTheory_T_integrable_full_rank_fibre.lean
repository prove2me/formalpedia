-- Prove2me | solution 1 for GlobalTheory.T.integrable_full_rank_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:24:22.475775+00:00
-- url     : https://prove2.me/submissions/1a3cd384-6aa6-40d5-9d91-048329c78ebd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegrableFullRankFibre
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FullRankSB
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegrableFullRankFibreStatement
import Theorems.Thm_GlobalTheory_RankFibre_integrable_fibre_integrand


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a b : ℕ) (ν : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν → ∀ Φ ∈ GlobalTheory.RankFibre.fullRankSB k a (a + b), MeasureTheory.Integrable (fun g : GL (Fin a) k => Φ (g.val * GlobalTheory.SplitFlip.X0 k finSumFinEquiv) * (ν (GlobalTheory.SplitFlip.gdet g) : ℂ) * GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) (((a + b : ℕ) : ℂ) / 2)) (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a))) := by
  first | exact @GlobalTheory.RankFibre.integrable_fibre_integrand | exact GlobalTheory.RankFibre.integrable_fibre_integrand | (intros; apply GlobalTheory.RankFibre.integrable_fibre_integrand <;> assumption)
end _root_.GlobalTheory.T
