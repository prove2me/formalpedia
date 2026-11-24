-- Prove2me | solution 1 for GlobalTheory.DoubleCosetEuler.eval_eq_ite_prod_of_finprod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:25:05.588181+00:00
-- url     : https://prove2.me/submissions/a88dab70-ec55-4a9c-be29-6dc3993a7d1b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinsumDoubleCosetEqFinprodLocalSums

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter
open scoped Classical
open GlobalTheory GlobalTheory.DoubleCosetEuler
namespace GlobalTheory.DoubleCosetEuler
theorem _root_.solution (ι G : Type) [Group G] (H : ι → Type) [∀ i, Group (H i)] (p : ∀ i, G →* H i)
    (TH KH : ∀ i, Subgroup (H i)) (s : G → ℂ) (s' : ∀ i, H i → ℂ) (S0 : Finset ι)
    (hcof : ∀ x : G, ∀ᶠ i in cofinite, p i x ∈ KH i)
    (hS0 : ∀ i ∉ S0, ∀ x, s' i x = if ∃ t ∈ TH i, ∃ k ∈ KH i, x = t * k then 1 else 0)
    (hprod : ∀ g, s g = ∏ᶠ i, s' i (p i g)) (g : G) :
    s g = if ∀ i ∉ S0, ∃ t ∈ TH i, ∃ k ∈ KH i, p i g = t * k then ∏ i ∈ S0, s' i (p i g) else 0 := by
  rw [hprod]
  have hfin : {i | p i g ∉ KH i}.Finite := Filter.eventually_cofinite.mp (hcof g)
  set B : Finset ι := S0 ∪ hfin.toFinset with hB
  have hone : ∀ i ∉ B, s' i (p i g) = 1 := by
    intro i hi
    simp only [B, Finset.mem_union, not_or, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hi
    rw [hS0 i hi.1, if_pos ⟨1, (TH i).one_mem, p i g, hi.2, (one_mul _).symm⟩]
  rw [finprod_eq_prod_of_mulSupport_subset (f := fun i => s' i (p i g)) (s := B) (fun i hi => by by_contra h; exact hi (hone i h))]
  split_ifs with hgood
  · symm
    apply Finset.prod_subset Finset.subset_union_left
    intro i _ hi
    rw [hS0 i hi, if_pos (hgood i hi)]
  · push_neg at hgood
    obtain ⟨i, hi, hbad⟩ := hgood
    apply Finset.prod_eq_zero (i := i)
    · refine Finset.mem_union_right _ ?_
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      intro hk
      exact hbad 1 (TH i).one_mem (p i g) hk (one_mul _).symm
    · rw [hS0 i hi, if_neg (by push_neg; exact hbad)]
end GlobalTheory.DoubleCosetEuler
