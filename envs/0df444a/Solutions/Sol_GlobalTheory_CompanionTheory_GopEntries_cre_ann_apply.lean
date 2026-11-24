-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GopEntries.cre_ann_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:52:42.711827+00:00
-- url     : https://prove2.me/submissions/437003c2-1a46-40b6-889a-f083909ca92f

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CreAnnApply
import Theorems.Thm_GlobalTheory_CompanionTheory_GopEntries_sg_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_GopEntries_sgR_erase
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
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] (i j : NC ε) (x : Ch ε V)
    (A : Finset (NC ε)) :
    (cre i * ann j : Module.End ℂ (Ch ε V)) x A = ∑ B, (hh i j A B : ℂ) • x B := by
  change (if i ∈ A then sg i A • (if j ∈ A.erase i then 0 else
    sg j (A.erase i) • x (insert j (A.erase i))) else 0) = _
  by_cases hi : i ∈ A
  · rw [if_pos hi]
    by_cases hj : j ∈ A.erase i
    · rw [if_pos hj, smul_zero]
      symm
      refine Finset.sum_eq_zero fun B _ => ?_
      have : ¬ (i ∈ A ∧ j ∈ B ∧ A.erase i = B.erase j) := by
        rintro ⟨_, _, h⟩
        rw [h] at hj
        exact Finset.notMem_erase _ _ hj
      simp only [hh, if_neg this, Complex.ofReal_zero, zero_smul]
    · rw [if_neg hj, Finset.sum_eq_single (insert j (A.erase i))]
      · have : i ∈ A ∧ j ∈ insert j (A.erase i) ∧ A.erase i = (insert j (A.erase i)).erase j :=
          ⟨hi, mem_insert_self _ _, (Finset.erase_insert hj).symm⟩
        rw [hh, if_pos this, Finset.erase_insert hj, sgR_erase, smul_smul, sg_eq, sg_eq,
          Complex.ofReal_mul]
      · intro B _ hB
        have : ¬ (i ∈ A ∧ j ∈ B ∧ A.erase i = B.erase j) := by
          rintro ⟨_, h1, h⟩
          apply hB
          rw [h, Finset.insert_erase h1]
        simp only [hh, if_neg this, Complex.ofReal_zero, zero_smul]
      · intro h; exact absurd (mem_univ _) h
  · rw [if_neg hi]
    symm
    refine Finset.sum_eq_zero fun B _ => ?_
    have : ¬ (i ∈ A ∧ j ∈ B ∧ A.erase i = B.erase j) := fun h => hi h.1
    simp only [hh, if_neg this, Complex.ofReal_zero, zero_smul]
end GlobalTheory.CompanionTheory.GopEntries
