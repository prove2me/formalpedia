-- Prove2me | solution 1 for GlobalTheory.DegreeGrowth.exists_aeval_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:12:53.902533+00:00
-- url     : https://prove2.me/submissions/1a135824-b5d4-4d82-a0d9-f28c8c9c1417

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FinrankTotalDegreeImageGrowth
import Theorems.Thm_GlobalTheory_DegreeGrowth_monomial_mul_mem
import Theorems.Thm_GlobalTheory_DegreeGrowth_boxSpan_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.DegreeGrowth
variable {K B : Type} [Field K] [CommRing B] [Algebra K B]
namespace GlobalTheory.DegreeGrowth
theorem _root_.solution {s n : ℕ} (y : Fin s → B) (b : Fin n → B)
    (p : MvPolynomial (Fin s) K) {x : B} (hx : ∃ D, x ∈ boxSpan K y b D) :
    ∃ D, MvPolynomial.aeval y p * x ∈ boxSpan K y b D := by
  induction p using MvPolynomial.induction_on'' with
  | C a =>
    obtain ⟨D, hD⟩ := hx
    refine ⟨D, ?_⟩
    rw [MvPolynomial.aeval_C, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ hD
  | monomial_add a c f _ _ h1' h2 =>
    obtain ⟨D1, h1⟩ := h2
    obtain ⟨D2, h2⟩ := h1'
    refine ⟨max D1 D2, ?_⟩
    rw [map_add, add_mul]
    exact add_mem (boxSpan_mono y b (le_max_left _ _) h1) (boxSpan_mono y b (le_max_right _ _) h2)
  | mul_X p i h =>
    obtain ⟨D, hD⟩ := h
    refine ⟨D + 1, ?_⟩
    have := monomial_mul_mem y b D 1 (Pi.single i 1)
      (fun j => by by_cases hj : j = i <;> simp [hj]) hD
    have e : ∏ j, y j ^ (Pi.single i 1 : Fin s → ℕ) j = y i := by
      rw [Finset.prod_eq_single i] <;> simp +contextual
    rw [e] at this
    rw [map_mul, MvPolynomial.aeval_X]
    convert this using 1
    ring
end GlobalTheory.DegreeGrowth
