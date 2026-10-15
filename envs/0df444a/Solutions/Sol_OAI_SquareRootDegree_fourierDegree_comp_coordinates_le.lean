-- Prove2me | solution 1 for OAI.SquareRootDegree.fourierDegree_comp_coordinates_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:05:11.262288+00:00
-- url     : https://prove2.me/submissions/773b3a65-d1c4-4f32-ab25-4babe51db0a3

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BooleanFunctions/Blocks.lean:L34-L53
-- (upload_full_project.md Phase 4): solution for node OAI.SquareRootDegree.fourierDegree_comp_coordinates_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_SquareRootDegree
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Walsh
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Conditioning
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Blocks
import Theorems.Thm_OAI_SquareRootDegree_fourier_inversion

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

theorem average_sum {α κ : Type*} [Fintype α] (s : Finset κ) (f : κ → α → ℝ) :
    average (fun x => ∑ j ∈ s, f j x) = ∑ j ∈ s, average (f j) := by
  simp only [average, Finset.mul_sum]
  rw [Finset.sum_comm]

/-! ### Degree calculus for finite observations -/

theorem fourierCoeff_const_mul {ι : Type*} [Fintype ι]
    (c : ℝ) (f : Cube ι → ℝ) (s : Finset ι) :
    fourierCoeff (fun x => c * f x) s = c * fourierCoeff f s := by
  simp only [fourierCoeff, mul_assoc, average_const_mul]

theorem fourierCoeff_sum {ι κ : Type*} [Fintype ι]
    (t : Finset κ) (f : κ → Cube ι → ℝ) (s : Finset ι) :
    fourierCoeff (fun x => ∑ j ∈ t, f j x) s = ∑ j ∈ t, fourierCoeff (f j) s := by
  simp only [fourierCoeff, Finset.sum_mul, average_sum]

theorem fourierDegree_sum_le {ι κ : Type*} [Fintype ι]
    (t : Finset κ) (f : κ → Cube ι → ℝ) (d : ℕ)
    (h : ∀ j ∈ t, fourierDegree (f j) ≤ d) :
    fourierDegree (fun x => ∑ j ∈ t, f j x) ≤ d := by
  rw [fourierDegree_le_iff]
  intro s hs
  rw [fourierCoeff_sum]
  exact Finset.sum_eq_zero fun j hj =>
    fourierCoeff_eq_zero_of_degree_lt _ (lt_of_le_of_lt (h j hj) hs)

theorem fourierDegree_const_mul_le {ι : Type*} [Fintype ι]
    (c : ℝ) (f : Cube ι → ℝ) : fourierDegree (fun x => c * f x) ≤ fourierDegree f := by
  rw [fourierDegree_le_iff]
  intro s hs
  rw [fourierCoeff_const_mul, fourierCoeff_eq_zero_of_degree_lt _ hs, mul_zero]

theorem fourierDegree_const {ι : Type*} [Fintype ι] (c : ℝ) :
    fourierDegree (fun _ : Cube ι => c) = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact fourierDegree_le_card_of_dependsOn (t := ∅) (by intro x y _; rfl)

end SquareRootDegree

end

end OAI

-- ---- from OAI.Combinatorics.BooleanFunctions.Blocks ----
namespace OAI

open scoped BigOperators

noncomputable section

namespace SquareRootDegree

/-! ## Disjoint blocks and finite observation degree calculus -/

attribute [local instance] Classical.propDecidable

theorem fourierDegree_comp_coordinates_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : Cube ι → ℝ) (e : ι → κ) :
    fourierDegree (fun x : Cube κ => f (fun i => x (e i))) ≤ fourierDegree f := by
  have he : (fun x : Cube κ => f (fun i => x (e i))) = fun x =>
      ∑ s : Finset ι, fourierCoeff f s * character s (fun i => x (e i)) := by
    funext x
    exact fourier_inversion f _
  rw [he]
  apply fourierDegree_sum_le
  intro s _
  by_cases hs : fourierCoeff f s = 0
  · simp [hs, fourierDegree_const]
  apply (fourierDegree_const_mul_le _ _).trans
  apply (fourierDegree_le_card_of_dependsOn (t := s.image e) ?_).trans
  · exact (Finset.card_image_le).trans
      (Finset.le_sup (f := Finset.card) (by simp [hs]))
  · intro x y hxy
    apply Finset.prod_congr rfl
    intro i hi
    exact congrArg sign (hxy (e i) (Finset.mem_image.mpr ⟨i,hi,rfl⟩))

end SquareRootDegree

end

end OAI

-- ---- platform node ----
open OAI OAI.SquareRootDegree
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem solution {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : Cube ι → ℝ) (e : ι → κ) :
    fourierDegree (fun x : Cube κ => f (fun i => x (e i))) ≤ fourierDegree f := by
  first
    | exact OAI.SquareRootDegree.fourierDegree_comp_coordinates_le f e
    | exact OAI.SquareRootDegree.fourierDegree_comp_coordinates_le
    | (apply OAI.SquareRootDegree.fourierDegree_comp_coordinates_le <;> assumption)
    | (intros; apply OAI.SquareRootDegree.fourierDegree_comp_coordinates_le <;> assumption)
