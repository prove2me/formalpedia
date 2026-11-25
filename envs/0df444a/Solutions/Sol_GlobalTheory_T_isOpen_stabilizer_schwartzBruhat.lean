-- Prove2me | solution 1 for GlobalTheory.T.isOpen_stabilizer_schwartzBruhat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:20:31.51829+00:00
-- url     : https://prove2.me/submissions/661f4df0-2103-4afb-b921-dbb49cf76c2e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenStabilizerSchwartzBruhat
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FullRankSB
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenStabilizerSchwartzBruhatStatement
import Theorems.Thm_GlobalTheory_OmAStab_isOpen_omA_stab


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
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar β → ∀ Φ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k), IsOpen {h : GL (Fin d) k | GlobalTheory.SplitFlip.omA ν β 1 h Φ = Φ} := by
  first | exact @GlobalTheory.OmAStab.isOpen_omA_stab | exact GlobalTheory.OmAStab.isOpen_omA_stab | (intros; apply GlobalTheory.OmAStab.isOpen_omA_stab <;> assumption)
end _root_.GlobalTheory.T
