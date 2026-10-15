-- Prove2me | solution 1 for OAI.SquareRootDegree.fourier_inversion
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:02:14.463805+00:00
-- url     : https://prove2.me/submissions/dff59223-d187-4d49-97b5-c28df6c99933

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BooleanFunctions/Walsh.lean:L221-L236
-- (upload_full_project.md Phase 4): solution for node OAI.SquareRootDegree.fourier_inversion. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_SquareRootDegree
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Walsh

-- ---- from OAI.Combinatorics.BooleanFunctions.Walsh ----
namespace OAI

/-!
Bool encodes a sign: false is +1 and true is -1. The average is uniform,
and degree is ordinary real Fourier degree, not F₂ degree or threshold degree.
-/

open scoped BigOperators

noncomputable section

namespace SquareRootDegree

/-! ## Finite Walsh calculus -/

theorem character_kernel {ι : Type*} [Fintype ι] [DecidableEq ι] (x y : Cube ι) :
    (∑ s : Finset ι, character s x * character s y) =
      if x = y then (Fintype.card (Cube ι) : ℝ) else 0 := by
  classical
  calc
    _ = ∏ i : ι, (1 + sign (x i) * sign (y i)) := by
      rw [Finset.prod_one_add, Finset.powerset_univ]
      simp [character, Finset.prod_mul_distrib]
    _ = _ := by
      by_cases h : x = y
      · subst y
        simp only [↓reduceIte]
        have hsign (i : ι) : (1 : ℝ) + sign (x i) * sign (x i) = 2 := by
          nlinarith [sign_sq (x i)]
        simp [hsign, Fintype.card_bool]
      · simp only [h, ↓reduceIte]
        obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
          simpa only [funext_iff, not_forall] using h
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        cases hx : x i <;> cases hy : y i <;> simp_all [sign]

theorem fourier_inversion {ι : Type*} [Fintype ι] (f : Cube ι → ℝ) (x : Cube ι) :
    f x = ∑ s : Finset ι, fourierCoeff f s * character s x := by
  classical
  have hn : (Fintype.card (Cube ι) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  symm
  calc
    _ = (Fintype.card (Cube ι) : ℝ)⁻¹ *
        ∑ y : Cube ι, f y * ∑ s : Finset ι, character s y * character s x := by
      simp only [fourierCoeff, average, mul_assoc, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
    _ = (Fintype.card (Cube ι) : ℝ)⁻¹ *
        ∑ y : Cube ι, f y * (if y = x then (Fintype.card (Cube ι) : ℝ) else 0) := by
      simp only [character_kernel]
    _ = f x := by
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      field_simp

/-! ### Degree calculus for finite observations -/

end SquareRootDegree

end

end OAI

-- ---- platform node ----
open OAI OAI.SquareRootDegree
open scoped BigOperators

theorem solution {ι : Type*} [Fintype ι] (f : Cube ι → ℝ) (x : Cube ι) :
    f x = ∑ s : Finset ι, fourierCoeff f s * character s x := by
  first
    | exact OAI.SquareRootDegree.fourier_inversion f x
    | exact OAI.SquareRootDegree.fourier_inversion
    | (apply OAI.SquareRootDegree.fourier_inversion <;> assumption)
    | (intros; apply OAI.SquareRootDegree.fourier_inversion <;> assumption)
