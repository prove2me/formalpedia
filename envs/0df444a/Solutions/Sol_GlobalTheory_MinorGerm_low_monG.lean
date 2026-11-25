-- Prove2me | solution 1 for GlobalTheory.MinorGerm.low_monG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:32:58.414802+00:00
-- url     : https://prove2.me/submissions/977684a6-f796-4a79-84c9-d46a418b7be4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreAndCapelli
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ProdFactorialDiag
import Theorems.Thm_GlobalTheory_MinorGerm_low_one
import Theorems.Thm_GlobalTheory_MinorGerm_low_prod
import Theorems.Thm_GlobalTheory_MinorGerm_low_tangent

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
theorem _root_.solution (j : Fin N × Fin N' → σ) {t : σ → MvPowerSeries σ C} (ht : TangentId t)
    (e : ℕ → ℕ) : Low (dg j (monAl N N' e)) (monG N N' e fun x => t (j x)) := by
  classical
  unfold monG dg
  rw [← Fin.sum_univ_eq_sum_range (fun ρ => dgOne j ρ (monAl N N' e ρ)) N]
  apply low_prod
  intro ρ _
  unfold dgOne
  by_cases h : ρ.val < N'
  · rw [dif_pos h, dif_pos ⟨ρ.isLt, h⟩]
    exact low_tangent ht (j (ρ, ⟨ρ, h⟩)) _
  · rw [dif_neg h, dif_neg (fun hh => h hh.2)]
    exact low_one
end GlobalTheory.MinorGerm
