-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WedgeDeriv.sum_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:01:30.95037+00:00
-- url     : https://prove2.me/submissions/587646db-3a1b-4b6b-80bf-3e590a2e0054

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSecondOrder_HasDerivAtDOf
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExteriorDifferentialMatrixUnitFormula
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeDeriv_det_one_submatrix
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeDeriv_card_filter_lt
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeDeriv_image_succAbove
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WedgeDeriv
namespace GlobalTheory.CompanionTheory.WedgeDeriv
theorem _root_.solution {m n : ℕ} (f g : Fin m → Fin n) (hf : StrictMono f) (hg : StrictMono g) (a b : Fin n) :
    ∑ j, ∑ i, adjugate ((1 : Matrix (Fin n) (Fin n) ℂ).submatrix f g) j i *
      (Matrix.single a b (1 : ℂ)) (f i) (g j) =
    if b ∈ univ.image g ∧ a ∉ (univ.image g).erase b ∧ univ.image f = insert a ((univ.image g).erase b) then
      (-1) ^ (((univ.image g).erase b).filter fun c => c < a).card *
        (-1) ^ (((univ.image g).erase b).filter fun c => c < b).card else 0 := by
  by_cases hb : b ∈ univ.image g
  swap
  · rw [if_neg (fun h => hb h.1)]
    refine sum_eq_zero fun j _ => sum_eq_zero fun i _ => ?_
    rw [single_apply_of_ne, mul_zero]
    rintro ⟨_, rfl⟩
    exact hb (mem_image_of_mem _ (mem_univ _))
  by_cases ha : a ∈ univ.image f
  swap
  · rw [if_neg (by rintro ⟨_, _, h⟩; exact ha (h ▸ mem_insert_self _ _))]
    refine sum_eq_zero fun j _ => sum_eq_zero fun i _ => ?_
    rw [single_apply_of_ne, mul_zero]
    rintro ⟨rfl, _⟩
    exact ha (mem_image_of_mem _ (mem_univ _))
  obtain ⟨j, _, rfl⟩ := mem_image.1 hb
  obtain ⟨i, _, rfl⟩ := mem_image.1 ha
  rw [sum_eq_single j, sum_eq_single i, single_apply_same, mul_one]
  · obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by have := i.pos; omega⟩
    rw [adjugate_fin_succ_eq_det_submatrix, submatrix_submatrix,
      det_one_submatrix _ _ (hf.comp (Fin.strictMono_succAbove i)) (hg.comp (Fin.strictMono_succAbove j)),
      image_succAbove f hf, image_succAbove g hg]
    by_cases h : (univ.image f).erase (f i) = (univ.image g).erase (g j)
    · rw [if_pos h, if_pos, card_filter_lt g hg, ← h, card_filter_lt f hf, mul_one, pow_add]
      refine ⟨hb, ?_, ?_⟩
      · rw [← h]; exact notMem_erase _ _
      · rw [← h, insert_erase ha]
    · rw [if_neg h, if_neg, mul_zero]
      rintro ⟨_, h1, h2⟩
      apply h
      rw [h2, erase_insert h1]
  · intro i' _ hi
    rw [single_apply_of_ne, mul_zero]
    exact fun h => hi (hf.injective h.1).symm
  · simp
  · intro j' _ hj
    refine sum_eq_zero fun i _ => ?_
    rw [single_apply_of_ne, mul_zero]
    exact fun h => hj (hg.injective h.2).symm
  · simp
end GlobalTheory.CompanionTheory.WedgeDeriv
