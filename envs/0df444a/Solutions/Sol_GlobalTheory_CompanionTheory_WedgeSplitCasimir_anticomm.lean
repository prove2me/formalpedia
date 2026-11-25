-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WedgeSplitCasimir.anticomm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:51:30.522548+00:00
-- url     : https://prove2.me/submissions/2c9fa7f6-c2e5-47a0-8282-0082bdb902a9

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExteriorDifferentialSignRuleQuadratic
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WedgeSplitCasimir
namespace GlobalTheory.CompanionTheory.WedgeSplitCasimir
theorem _root_.solution {n : ℕ} (J J' : Finset (Fin n)) (s s' : Fin n) :
    (if s ∈ J' ∧ s' ∉ J'.erase s ∧ J = insert s' (J'.erase s) then
        (-1 : ℂ) ^ ((J'.erase s).filter fun c => c < s').card * (-1) ^ ((J'.erase s).filter fun c => c < s).card
      else 0) =
    (if J = J' ∧ s = s' then 1 else 0) -
      if s ∉ J ∧ s' ∉ J' ∧ insert s J = insert s' J' then
        (-1) ^ (J.filter fun a => a < s).card * (-1) ^ (J'.filter fun a => a < s').card else 0 := by
  have sq : ∀ a : ℕ, (-1 : ℂ) ^ a * (-1) ^ a = 1 := fun a => by
    rw [← mul_pow]; simp
  by_cases hss : s = s'
  · subst hss
    by_cases hs : s ∈ J'
    · rw [Finset.insert_erase hs, sq]
      simp [hs]
    · by_cases hJ : J = J'
      · subst hJ
        simp [hs, sq]
      · rw [if_neg (fun h => hs h.1), if_neg (fun h => hJ h.1), if_neg, sub_zero]
        rintro ⟨h1, h2, h3⟩
        apply hJ
        rw [← Finset.erase_insert h1, h3, Finset.erase_insert h2]
  · rw [if_neg (fun h : J = J' ∧ s = s' => hss h.2), zero_sub]
    by_cases h : s ∈ J' ∧ s' ∉ J'.erase s ∧ J = insert s' (J'.erase s)
    · rw [if_pos h]
      obtain ⟨h1, h2, h3⟩ := h
      obtain ⟨K, hK, rfl⟩ : ∃ K : Finset (Fin n), s ∉ K ∧ J' = insert s K :=
        ⟨J'.erase s, Finset.notMem_erase _ _, (Finset.insert_erase h1).symm⟩
      rw [Finset.erase_insert hK] at h2 h3 ⊢
      subst h3
      rw [if_pos ⟨by simp [hss, hK], by simp [Ne.symm hss, h2], Finset.insert_comm _ _ _⟩]
      rw [Finset.filter_insert, Finset.filter_insert]
      rcases lt_or_gt_of_ne hss with hlt | hlt
      · rw [if_neg (not_lt.2 hlt.le), if_pos hlt,
          Finset.card_insert_of_notMem (fun h => hK (Finset.mem_filter.1 h).1)]
        ring
      · rw [if_pos hlt, if_neg (not_lt.2 hlt.le),
          Finset.card_insert_of_notMem (fun h => h2 (Finset.mem_filter.1 h).1)]
        ring
    · rw [if_neg h, if_neg, neg_zero]
      rintro ⟨h1, h2, h3⟩
      apply h
      have hs : s ∈ J' := by
        have : s ∈ insert s' J' := h3 ▸ Finset.mem_insert_self s J
        exact (Finset.mem_insert.1 this).resolve_left hss
      refine ⟨hs, fun h => h2 (Finset.mem_of_mem_erase h), ?_⟩
      rw [← Finset.erase_insert h1, h3, Finset.erase_insert_of_ne (Ne.symm hss)]
end GlobalTheory.CompanionTheory.WedgeSplitCasimir
