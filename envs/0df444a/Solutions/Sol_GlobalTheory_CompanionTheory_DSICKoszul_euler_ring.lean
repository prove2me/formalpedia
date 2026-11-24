-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSICKoszul.euler_ring
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:28:48.349383+00:00
-- url     : https://prove2.me/submissions/5cb97ef9-e68a-45e6-814f-b24b49072cf0

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_MemFiltOfWords
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSICKoszul
open CompanionTheory.D.DSIC
variable {R : Type*} [Ring R] {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.DSICKoszul
theorem _root_.solution (A D : ι → R) (h2 : ∀ i j, Commute (D i) (D j))
    (h3 : ∀ i j, D i * A j - A j * D i = if i = j then 1 else 0) (i : ι) :
    D i * (∑ j, A j * D j) = (∑ j, A j * D j) * D i + D i := by
  have key : ∀ j, D i * (A j * D j) = A j * D j * D i + if i = j then D i else 0 := by
    intro j
    have e3 : D i * A j = A j * D i + if i = j then 1 else 0 := by
      rw [← h3 i j]; abel
    rw [← mul_assoc, e3, add_mul, mul_assoc, (h2 i j).eq, ← mul_assoc]
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  rw [Finset.mul_sum, Finset.sum_mul]
  simp only [key, Finset.sum_add_distrib]
  simp
end GlobalTheory.CompanionTheory.DSICKoszul
