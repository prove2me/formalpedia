-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZuckCount.count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:29:28.093977+00:00
-- url     : https://prove2.me/submissions/42fa0a29-cd86-405d-9e9f-3dd24457e4e4

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CountingBound
import Theorems.Thm_GlobalTheory_CompanionTheory_ZuckCount_addSet_insert
import Theorems.Thm_GlobalTheory_CompanionTheory_ZuckCount_addSet_eq_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_ZuckCount_casG_polar_complex

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ZuckCount
namespace GlobalTheory.CompanionTheory.ZuckCount
theorem _root_.solution : Count := by
  intro n m μ _ par w
  have hw : ∀ p, w p (par p) = if p.2 ∈ p.1.1 then 0 else 2 := fun p => casG_polar_complex μ p.1.1 p.2
  refine ⟨fun I => ?_, fun ν hν => ?_⟩
  · have h1 : ∀ p ∈ univ.filter (fun p => par p = addSet μ I.1), w p (addSet μ I.1) = 2 := by
      intro p hp
      have hp' := (Finset.mem_filter.1 hp).2
      rw [← hp', hw, if_neg ((addSet_eq_iff μ p.1.1 I.1 p.2).1 hp').1]
    rw [Finset.sum_congr rfl h1, Finset.sum_const]
    have hc : (univ.filter (fun p => par p = addSet μ I.1)).card = I.1.card := by
      refine Finset.card_bij (fun p _ => p.2) ?_ ?_ ?_
      · intro p hp
        have := (addSet_eq_iff μ p.1.1 I.1 p.2).1 (Finset.mem_filter.1 hp).2
        rw [this.2]; exact Finset.mem_insert_self _ _
      · intro p hp q hq hpq
        have h1 := (addSet_eq_iff μ p.1.1 I.1 p.2).1 (Finset.mem_filter.1 hp).2
        have h2 := (addSet_eq_iff μ q.1.1 I.1 q.2).1 (Finset.mem_filter.1 hq).2
        have hpq' : p.2 = q.2 := hpq
        refine Prod.ext (Subtype.ext ?_) hpq'
        rw [← Finset.erase_insert h1.1, ← Finset.erase_insert h2.1, ← h1.2, ← h2.2, hpq']
      · intro s hs
        refine ⟨(⟨I.1.erase s, ?_⟩, s), Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, rfl⟩
        · rw [Finset.card_erase_of_mem hs, I.2]; rfl
        · exact (addSet_eq_iff μ _ I.1 s).2 ⟨Finset.notMem_erase _ _, (Finset.insert_erase hs).symm⟩
    rw [hc, I.2, nsmul_eq_mul]
    push_cast
    ring
  · refine Finset.sum_eq_zero fun p hp => ?_
    have hp' := (Finset.mem_filter.1 hp).2
    rw [← hp', hw, if_pos]
    by_contra hs
    refine hν ⟨insert p.2 p.1.1, ?_⟩ ?_
    · rw [Finset.card_insert_of_notMem hs, p.1.2]
    · rw [← hp']; exact (addSet_insert μ _ _ hs).symm
end GlobalTheory.CompanionTheory.ZuckCount
