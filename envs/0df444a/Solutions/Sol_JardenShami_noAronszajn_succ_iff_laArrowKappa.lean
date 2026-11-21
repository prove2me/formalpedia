-- Prove2me | solution 1 for JardenShami.noAronszajn_succ_iff_laArrowKappa
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:48:56.437723+00:00
-- url     : https://prove2.me/submissions/2df1115e-ce5c-4dce-8338-d89d8004429a

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5
import Theorems.Thm_JardenShami_Tree_isCofinalBranch_iff
import Theorems.Thm_JardenShami_branch_iff_laArrowKappa
import Theorems.Thm_JardenShami_Kappa_coe_mk
import Theorems.Thm_JardenShami_Kappa_mk_coe
import Theorems.Thm_JardenShami_Tree_ht_lt_height
attribute [local simp] JardenShami.Kappa.coe_mk
attribute [local simp] JardenShami.Kappa.mk_coe



set_option autoImplicit true
open Cardinal
universe w
noncomputable section
open JardenShami
open Tree
namespace JardenShami
theorem _root_.solution (μ : Cardinal.{w}) (hμ : ℵ₀ ≤ μ) :
    NoAronszajn (Order.succ μ) ↔ LaArrowKappa (Order.succ μ) μ := by
  have hreg := Cardinal.isRegular_succ hμ
  have hlt : μ < Order.succ μ := Order.lt_succ μ
  rw [← branch_iff_laArrowKappa _ μ hreg (hμ.trans_lt hlt) hlt]
  constructor
  · intro h T _ _ hT hlev
    by_contra hc
    refine h T ⟨⟨hT, fun α _ => (hlev α).trans_lt hlt⟩, ?_⟩
    rintro ⟨b, hb⟩
    exact hc ⟨b, (isCofinalBranch_iff hT).1 hb⟩
  · intro h T _ _ ⟨hTk, hno⟩
    have hlev : ∀ α : Ordinal.{w}, #(Lev T α) ≤ μ := by
      intro α
      by_cases hα : α < (Order.succ μ).ord
      · exact Order.lt_succ_iff.1 (hTk.2 α hα)
      · have : Lev T α = ∅ := by
          refine Set.eq_empty_of_forall_notMem fun t ht' => hα ?_
          rw [← hTk.1, ← show ht t = α from ht']
          exact ht_lt_height t
        rw [this]
        simp
    obtain ⟨b, hb⟩ := h T hTk.1 hlev
    exact hno ⟨b, (isCofinalBranch_iff hTk.1).2 hb⟩
end JardenShami
