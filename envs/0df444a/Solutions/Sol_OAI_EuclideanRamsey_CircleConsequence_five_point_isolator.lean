-- Prove2me | solution 1 for OAI.EuclideanRamsey.CircleConsequence.five_point_isolator
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T12:40:08.411712+00:00
-- url     : https://prove2.me/submissions/513a1fb8-6015-4240-aa88-4745a144e65c

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/CircleInterpolation.lean:L72-L94
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.CircleConsequence.five_point_isolator. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Model__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CircleInterpolation
import Theorems.Thm_OAI_EuclideanRamsey_CircleConsequence_secantValue_ne_zero

-- ---- from OAI.Combinatorics.EuclideanRamsey.CircleInterpolation ----
namespace OAI

/- The secant equations and quadratic isolators have coefficients in the coordinate field. -/
noncomputable section
namespace EuclideanRamsey.CircleConsequence

theorem secantRow_eval {s : ℕ} (a : Fin s → Space 2) (i j k : Fin s) :
    (∑ α : Option (Fin 2), secantRow a i j α * augmented a k α) =
      secantValue a i j k := by
  simp [secantRow, secantValue, augmented, Fin.sum_univ_two]
  ring

theorem pairedSecantMatrix_eval {s : ℕ} (a : Fin s → Space 2)
    (i j k l m : Fin s) :
    (∑ α : Option (Fin 2), ∑ β : Option (Fin 2),
      pairedSecantMatrix a i j k l α β * augmented a m α * augmented a m β) =
      secantValue a i j m * secantValue a k l m := by
  rw [← secantRow_eval a i j m, ← secantRow_eval a k l m]
  rw [Finset.sum_mul]
  simp only [pairedSecantMatrix, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α hα
  apply Finset.sum_congr rfl
  intro β hβ
  ring

theorem pairedSecantMatrix_vanishes {s : ℕ} (a : Fin s → Space 2)
    (i j k l m : Fin s) (hm : m = i ∨ m = j ∨ m = k ∨ m = l) :
    (∑ α : Option (Fin 2), ∑ β : Option (Fin 2),
      pairedSecantMatrix a i j k l α β * augmented a m α * augmented a m β) = 0 := by
  rw [pairedSecantMatrix_eval]
  rcases hm with rfl | rfl | rfl | rfl <;> dsimp only [secantValue] <;> ring

/-- The five-point isolator is a concrete coordinate-field matrix.
The permutation is just a labeling, with e 0 the point being isolated. -/
theorem five_point_isolator (a : Fin 5 → Space 2)
    (ha : Function.Injective a) (c : Space 2) (R : ℝ)
    (hc : ∀ m, (a m 0-c 0)^2 + (a m 1-c 1)^2 = R)
    (e : Equiv.Perm (Fin 5)) :
    ∃ M : Matrix (Option (Fin 2)) (Option (Fin 2)) (Coeff a),
      (∀ m, m ≠ e 0 →
        (∑ α : Option (Fin 2), ∑ β : Option (Fin 2),
          M α β * augmented a m α * augmented a m β) = 0) ∧
      (∑ α : Option (Fin 2), ∑ β : Option (Fin 2),
          M α β * augmented a (e 0) α * augmented a (e 0) β) ≠ 0 := by
  refine ⟨pairedSecantMatrix a (e 1) (e 2) (e 3) (e 4), ?_, ?_⟩
  · intro m hm
    apply pairedSecantMatrix_vanishes
    have hem : e (e.symm m) = m := e.apply_symm_apply m
    have hn : e.symm m ≠ 0 := by intro h; apply hm; simpa [h] using hem.symm
    generalize h : e.symm m = k at hem hn
    fin_cases k <;> simp_all
  · rw [pairedSecantMatrix_eval]
    apply mul_ne_zero
    · apply secantValue_ne_zero a ha c R hc <;> exact e.injective.ne (by decide)
    · apply secantValue_ne_zero a ha c R hc <;> exact e.injective.ne (by decide)

end EuclideanRamsey.CircleConsequence

end

end OAI

-- ---- platform node ----
open OAI OAI.EuclideanRamsey OAI.EuclideanRamsey.CircleConsequence


theorem solution : type_of% @_root_.OAI.EuclideanRamsey.CircleConsequence.five_point_isolator := @_root_.OAI.EuclideanRamsey.CircleConsequence.five_point_isolator
