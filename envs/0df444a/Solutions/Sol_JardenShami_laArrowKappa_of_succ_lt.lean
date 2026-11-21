-- Prove2me | solution 1 for JardenShami.laArrowKappa_of_succ_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:48:28.934177+00:00
-- url     : https://prove2.me/submissions/f62069bc-d701-44ed-b42a-7eca5931e25f

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section7
import Theorems.Thm_JardenShami_not_isAronszajn_of_card_lev_lt
import Theorems.Thm_JardenShami_Tree_isCofinalBranch_iff
import Theorems.Thm_JardenShami_laArrowKappa_of_forall_branch


set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
open Tree
namespace JardenShami
theorem _root_.solution (κ μ : Cardinal.{w})
    (hκ : κ.IsRegular) (h : Order.succ μ < κ) : LaArrowKappa κ μ := by
  have hlt : μ < Order.succ μ := Order.lt_succ_of_not_isMax (not_isMax μ)
  have hμ : μ < κ := hlt.trans h
  refine laArrowKappa_of_forall_branch κ μ hκ hμ fun T _ _ hT hlev => ?_
  have hTk : IsKappaTree κ T := ⟨hT, fun α _ => (hlev α).trans_lt hμ⟩
  have hna := not_isAronszajn_of_card_lev_lt κ (Order.succ μ) hκ h T hTk
    (fun α => (hlev α).trans_lt hlt)
  by_contra hc
  refine hna ⟨hTk, ?_⟩
  rintro ⟨b, hb⟩
  exact hc ⟨b, (isCofinalBranch_iff hT).1 hb⟩
end JardenShami
