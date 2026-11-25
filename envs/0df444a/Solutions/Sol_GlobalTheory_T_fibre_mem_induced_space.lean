-- Prove2me | solution 1 for GlobalTheory.T.fibre_mem_induced_space
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:18:06.490118+00:00
-- url     : https://prove2.me/submissions/2fd65385-bb99-4e57-9db1-ff7c00cbc35e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FibreMemInducedSpace
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FullRankSB
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FibreMemInducedSpaceStatement
import Theorems.Thm_GlobalTheory_RankFibre_fibre_mem_indSpace


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
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a b : ℕ) (ν β : kˣ →* ℂˣ) (Φ : Matrix (Fin a) (Fin (a + b)) k → ℂ), GlobalTheory.RankFibre.fibre ν β a b Φ ∈ GlobalTheory.PRep.indSpace (GlobalTheory.SmGL.parab k (GlobalTheory.RankFibre.blocks a b)) (GlobalTheory.SmGL.ofChar (GlobalTheory.RankFibre.parChar ν β a b)) := by
  first | exact @GlobalTheory.RankFibre.fibre_mem_indSpace | exact GlobalTheory.RankFibre.fibre_mem_indSpace | (intros; apply GlobalTheory.RankFibre.fibre_mem_indSpace <;> assumption)
end _root_.GlobalTheory.T
