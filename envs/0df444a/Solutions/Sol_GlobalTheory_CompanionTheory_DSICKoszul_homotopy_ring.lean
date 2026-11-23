-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSICKoszul.homotopy_ring
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:06:43.891148+00:00
-- url     : https://prove2.me/submissions/2c77d72e-788c-444a-9acc-a53db90b05f5

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
theorem _root_.solution (A D an cr : ι → R)
    (h1 : ∀ i j, Commute (an i) (D j)) (h2 : ∀ i j, Commute (cr i) (A j))
    (h3 : ∀ i j, D i * A j - A j * D i = if i = j then 1 else 0)
    (h4 : ∀ i j, an i * cr j + cr j * an i = if i = j then 1 else 0) :
    (∑ i, A i * an i) * (∑ j, D j * cr j) + (∑ j, D j * cr j) * (∑ i, A i * an i) =
      ∑ i, A i * D i + ∑ i, cr i * an i := by
  have key : ∀ i j, A i * an i * (D j * cr j) + D j * cr j * (A i * an i) =
      (if i = j then A i * D i else 0) + (if i = j then cr i * an i else 0) := by
    intro i j
    have e1 : A i * an i * (D j * cr j) = A i * D j * (an i * cr j) := by
      rw [mul_assoc, ← mul_assoc (an i), (h1 i j).eq, mul_assoc, mul_assoc]
    have e2 : D j * cr j * (A i * an i) = D j * A i * (cr j * an i) := by
      rw [mul_assoc, ← mul_assoc (cr j), (h2 j i).eq, mul_assoc, mul_assoc]
    have e3 : D j * A i = A i * D j + if j = i then 1 else 0 := by
      rw [← h3 j i]; abel
    rw [e1, e2, e3, add_mul, ← add_assoc, ← mul_add, h4]
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm (s := univ) (t := univ)
    (f := fun j i => D j * cr j * (A i * an i)), ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  simp only [key, Finset.sum_add_distrib]
  simp
end GlobalTheory.CompanionTheory.DSICKoszul
