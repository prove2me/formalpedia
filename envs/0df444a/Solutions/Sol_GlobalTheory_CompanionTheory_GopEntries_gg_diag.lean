-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GopEntries.gg_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:49:54.56159+00:00
-- url     : https://prove2.me/submissions/0d3d9be4-46a1-48ff-b23b-1f8ebebfb01a

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CreAnnApply
import Theorems.Thm_GlobalTheory_CompanionTheory_GopEntries_sgR_mul_self
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
open Finset
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GopEntries
open CompanionTheory.D.DSIC
variable {n : ℕ} {ε : Fin n → Bool}
namespace GlobalTheory.CompanionTheory.GopEntries
theorem _root_.solution (c : Fin n) (A B : Finset (NC ε)) : gg c c A B = if A = B then wtA A c else 0 := by
  have h1 : ∀ i : NC ε, ∑ j : NC ε, coef c c i j * hh i j A B = coef c c i i * hh i i A B := by
    intro i
    refine Finset.sum_eq_single i (fun j _ hj => ?_) (fun h => absurd (mem_univ _) h)
    have e1 : ¬ (i.1.1 = c ∧ j.1.1 = c ∧ i.1.2 = j.1.2) := by
      rintro ⟨a, b, e⟩
      exact hj (Subtype.ext (Prod.ext (b.trans a.symm) e.symm))
    have e2 : ¬ (i.1.2 = c ∧ j.1.2 = c ∧ i.1.1 = j.1.1) := by
      rintro ⟨a, b, e⟩
      exact hj (Subtype.ext (Prod.ext e.symm (b.trans a.symm)))
    rw [coef, if_neg e1, if_neg e2, sub_zero, zero_mul]
  unfold gg
  simp only [h1]
  split_ifs with h
  · subst h
    have h2 : ∀ i : NC ε, hh i i A A = if i ∈ A then 1 else 0 := by
      intro i
      unfold hh
      by_cases hi : i ∈ A
      · simp [hi, sgR_mul_self]
      · simp [hi]
    simp only [h2, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
    simp [coef, wtA, Finset.sum_sub_distrib]
  · refine Finset.sum_eq_zero fun i _ => ?_
    have : ¬ (i ∈ A ∧ i ∈ B ∧ A.erase i = B.erase i) := by
      rintro ⟨a, b, e⟩
      apply h
      rw [← Finset.insert_erase a, e, Finset.insert_erase b]
    rw [hh, if_neg this, mul_zero]
end GlobalTheory.CompanionTheory.GopEntries
