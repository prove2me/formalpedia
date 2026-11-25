-- Prove2me | solution 1 for GlobalTheory.MinorGerm.Lead.pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:21:45.415213+00:00
-- url     : https://prove2.me/submissions/cd801c02-12ad-4c1f-8205-532f102db514

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreAndCapelli
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ProdFactorialDiag
import Theorems.Thm_GlobalTheory_MinorGerm_Low_mul
import Theorems.Thm_GlobalTheory_MinorGerm_lead_one
import Theorems.Thm_GlobalTheory_MinorGerm_Lead_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds
noncomputable section
open GlobalTheory GlobalTheory.MinorGerm
variable {C : Type} [Field C] {σ : Type}
variable {p : σ → Prop} [DecidablePred p]
namespace GlobalTheory.MinorGerm
namespace Lead
theorem _root_.solution {α : σ →₀ ℕ} {P : MvPolynomial σ C} (hP : Lead p α P) (n : ℕ) :
    Lead p (n • α) (P ^ n) := by
  classical
  induction n with
  | zero => simpa using (lead_one (p := p) : Lead p (0 : σ →₀ ℕ) (1 : MvPolynomial σ C))
  | succ n ih =>
    rw [succ_nsmul, pow_succ]
    exact ih.mul hP
end Lead
end GlobalTheory.MinorGerm
