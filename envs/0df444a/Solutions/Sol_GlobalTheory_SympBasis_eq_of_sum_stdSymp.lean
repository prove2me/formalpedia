-- Prove2me | solution 1 for GlobalTheory.SympBasis.eq_of_sum_stdSymp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:00:04.510927+00:00
-- url     : https://prove2.me/submissions/8e2381cd-f46a-4823-9b47-0a06fc2136c3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SymplecticTorsionSystemIsGeometricBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
namespace GlobalTheory.SympBasis
private theorem sum_inv_mulVec_smul_col_of_det_ne_zero {R : Type} [CommRing R] {g : ℕ} (c : Fin (2 * g) → R) (i j : Fin (2 * g))
    (hij : (i : ℕ) < g ∧ (j : ℕ) = i + g) : ∑ l, c l * (Out.stdSymp g l j : R) = c i := by
  rw [Finset.sum_eq_single i]
  · unfold Out.stdSymp
    rw [if_pos hij]
    simp
  · intro l _ hl
    have h1 : ¬ ((l : ℕ) < g ∧ (j : ℕ) = l + g) := fun h => hl (Fin.ext (by omega))
    have h2 : ¬ ((j : ℕ) < g ∧ (l : ℕ) = j + g) := by omega
    unfold Out.stdSymp
    rw [if_neg h1, if_neg h2]
    simp
  · simp
private theorem sum_mul_stdSymp_eq_neg_of_eq_add {R : Type} [CommRing R] {g : ℕ} (c : Fin (2 * g) → R) (i j : Fin (2 * g))
    (hij : (j : ℕ) < g ∧ (i : ℕ) = j + g) : ∑ l, c l * (Out.stdSymp g l j : R) = - c i := by
  rw [Finset.sum_eq_single i]
  · have h1 : ¬ ((i : ℕ) < g ∧ (j : ℕ) = i + g) := by omega
    unfold Out.stdSymp
    rw [if_neg h1, if_pos hij]
    simp
  · intro l _ hl
    have h1 : ¬ ((l : ℕ) < g ∧ (j : ℕ) = l + g) := by omega
    have h2 : ¬ ((j : ℕ) < g ∧ (l : ℕ) = j + g) := fun h => hl (Fin.ext (by omega))
    unfold Out.stdSymp
    rw [if_neg h1, if_neg h2]
    simp
  · simp
end GlobalTheory.SympBasis
namespace GlobalTheory
end GlobalTheory
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.SympBasis
namespace GlobalTheory.SympBasis
theorem _root_.solution {R : Type} [CommRing R] {g : ℕ} (a b : Fin (2 * g) → R)
    (h : ∀ j, ∑ i, a i * (Out.stdSymp g i j : R) = ∑ i, b i * (Out.stdSymp g i j : R)) : a = b := by
  funext i
  have hi2 := i.isLt
  by_cases hi : (i : ℕ) < g
  ·
    have h1 := h ⟨i + g, by omega⟩
    rwa [sum_inv_mulVec_smul_col_of_det_ne_zero a i _ ⟨hi, rfl⟩, sum_inv_mulVec_smul_col_of_det_ne_zero b i _ ⟨hi, rfl⟩] at h1
  ·
    have h1 := h ⟨i - g, by omega⟩
    rw [sum_mul_stdSymp_eq_neg_of_eq_add a i _ ⟨by simp; omega, by simp; omega⟩,
      sum_mul_stdSymp_eq_neg_of_eq_add b i _ ⟨by simp; omega, by simp; omega⟩] at h1
    exact neg_inj.mp h1
end GlobalTheory.SympBasis
