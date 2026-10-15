-- Prove2me | solution 1 for OAI.SquareRootDegree.fourierDegree_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:03:34.868451+00:00
-- url     : https://prove2.me/submissions/12a2de56-8561-4d0f-8863-177798f9a01e

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BooleanFunctions/Walsh.lean:L377-L413
-- (upload_full_project.md Phase 4): solution for node OAI.SquareRootDegree.fourierDegree_mul_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_SquareRootDegree
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Walsh
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

theorem character_dependsOn {ι : Type*} (s : Finset ι) : DependsOn s (character s) := by
  intro x y h
  exact Finset.prod_congr rfl fun i hi => congrArg sign (h i hi)

theorem dependsOn_mul {ι : Type*} [DecidableEq ι] {s t : Finset ι}
    {f g : Cube ι → ℝ} (hf : DependsOn s f) (hg : DependsOn t g) :
    DependsOn (s ∪ t) (fun x => f x * g x) := by
  intro x y h
  change f x * g x = f y * g y
  rw [hf x y (fun i hi => h i (Finset.mem_union_left _ hi)),
    hg x y (fun i hi => h i (Finset.mem_union_right _ hi))]

theorem fourierDegree_mul_le {ι : Type*} [Fintype ι] (f g : Cube ι → ℝ) :
    fourierDegree (fun x => f x * g x) ≤ fourierDegree f + fourierDegree g := by
  classical
  let sf : Finset (Finset ι) := Finset.univ.filter (fun s => fourierCoeff f s ≠ 0)
  let sg : Finset (Finset ι) := Finset.univ.filter (fun s => fourierCoeff g s ≠ 0)
  have hexp (h : Cube ι → ℝ) (x : Cube ι) :
      h x = ∑ s ∈ Finset.univ.filter (fun s => fourierCoeff h s ≠ 0),
        fourierCoeff h s * character s x := by
    rw [fourier_inversion h x]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro s hs hnot
    have hz : fourierCoeff h s = 0 := by simpa [Finset.mem_filter, hs] using hnot
    simp [hz]
  have heq : (fun x => f x * g x) = fun x =>
      ∑ s ∈ sf, ∑ t ∈ sg,
        (fourierCoeff f s * fourierCoeff g t) * (character s x * character t x) := by
    funext x
    rw [hexp f x, hexp g x]
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum, sf, sg]
    apply Finset.sum_congr rfl
    intro s hs
    apply Finset.sum_congr rfl
    intro t ht
    ring
  rw [heq]
  apply fourierDegree_sum_le
  intro s hs
  apply fourierDegree_sum_le
  intro t ht
  apply (fourierDegree_const_mul_le _ _).trans
  apply (fourierDegree_le_card_of_dependsOn
    (dependsOn_mul (character_dependsOn s) (character_dependsOn t))).trans
  apply (Finset.card_union_le _ _).trans
  exact Nat.add_le_add (Finset.le_sup (f := Finset.card) hs)
    (Finset.le_sup (f := Finset.card) ht)

end SquareRootDegree

end

end OAI

-- ---- platform node ----
open OAI OAI.SquareRootDegree
open scoped BigOperators

theorem solution {ι : Type*} [Fintype ι] (f g : Cube ι → ℝ) :
    fourierDegree (fun x => f x * g x) ≤ fourierDegree f + fourierDegree g := by
  first
    | exact OAI.SquareRootDegree.fourierDegree_mul_le f g
    | exact OAI.SquareRootDegree.fourierDegree_mul_le
    | (apply OAI.SquareRootDegree.fourierDegree_mul_le <;> assumption)
    | (intros; apply OAI.SquareRootDegree.fourierDegree_mul_le <;> assumption)
