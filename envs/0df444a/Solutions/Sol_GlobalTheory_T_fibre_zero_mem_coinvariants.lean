-- Prove2me | solution 1 for GlobalTheory.T.fibre_zero_mem_coinvariants
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:18:09.367828+00:00
-- url     : https://prove2.me/submissions/96c66b6e-16b6-4fe5-aa3b-8d7e74da525a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FibreZeroMemCoinvariants
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FullRankSB
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FibreZeroMemCoinvariantsStatement
import Theorems.Thm_GlobalTheory_RankFibreKer_fibre_ker


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
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a b : ℕ) (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsSmoothChar β → ∀ Φ ∈ GlobalTheory.RankFibre.fullRankSB k a (a + b), GlobalTheory.RankFibre.fibre ν β a b Φ = 0 → Φ ∈ GlobalTheory.RankFibre.coinv ν β a (a + b) := by
  first | exact @GlobalTheory.RankFibreKer.fibre_ker | exact GlobalTheory.RankFibreKer.fibre_ker | (intros; apply GlobalTheory.RankFibreKer.fibre_ker <;> assumption)
end _root_.GlobalTheory.T
