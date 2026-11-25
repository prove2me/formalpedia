-- Prove2me | solution 1 for GlobalTheory.MinorGerm.lead_monP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:29:36.035168+00:00
-- url     : https://prove2.me/submissions/f253fdca-cf59-4530-a9b1-3081e4aaf99c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreAndCapelli
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ProdFactorialDiag
import Theorems.Thm_GlobalTheory_MinorGerm_Low_pow
import Theorems.Thm_GlobalTheory_MinorGerm_lead_prod
import Theorems.Thm_GlobalTheory_MinorGerm_Lead_pow
import Theorems.Thm_GlobalTheory_MinorGerm_dg_monAl
import Theorems.Thm_GlobalTheory_MinorGerm_lead_minor

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
variable {C : Type} [Field C] {σ : Type} {N N' : ℕ}
variable {p : σ → Prop} [DecidablePred p]
namespace GlobalTheory.MinorGerm
theorem _root_.solution (j : Fin N × Fin N' → σ) (hj : ∀ b c, p (j (b, c)) ↔ b.val = c.val)
    (e : ℕ → ℕ) :
    Lead p (dg j (monAl N N' e)) (MvPolynomial.rename j (monP C N N' e)) := by
  classical
  unfold monP
  rw [map_prod]
  simp_rw [map_pow]
  rw [dg_monAl]
  apply lead_prod
  intro k hk
  exact (lead_minor j hj (Finset.mem_Icc.1 hk).2).pow (e k)
end GlobalTheory.MinorGerm
