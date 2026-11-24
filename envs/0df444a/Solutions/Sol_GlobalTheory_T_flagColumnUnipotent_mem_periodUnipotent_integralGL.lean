-- Prove2me | solution 1 for GlobalTheory.T.flagColumnUnipotent_mem_periodUnipotent_integralGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:09:43.490909+00:00
-- url     : https://prove2.me/submissions/6b05bb40-ff75-44ee-83cc-6e9c34340ebf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FlagColumnUnipotentMemPeriodUnipotentIntegralGL
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OrdL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FlagColumnUnipotentMemPeriodUnipotentIntegralGLStatement
import Theorems.Thm_GlobalTheory_DiagVol_colE_mem_symN_KO


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.DiagVol ValuativeRel Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (t : n ⊕ Fin c) (y : n ⊕ Fin c → k), (∀ r, y r ∈ 𝒪[k]) → (∀ r, ¬ ordL c r < ordL c t → y r = 0) → ∃ x ∈ symN k n c ⊓ KO k (n ⊕ Fin c), x.val = 1 + Matrix.of (fun r s => if s = t then y r else 0) := by
  first | exact @GlobalTheory.DiagVol.colE_mem_symN_KO | exact GlobalTheory.DiagVol.colE_mem_symN_KO | (intros; apply GlobalTheory.DiagVol.colE_mem_symN_KO <;> assumption)
end _root_.GlobalTheory.T
