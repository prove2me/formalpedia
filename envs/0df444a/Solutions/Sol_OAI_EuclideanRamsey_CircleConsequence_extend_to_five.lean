-- Prove2me | solution 1 for OAI.EuclideanRamsey.CircleConsequence.extend_to_five
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T12:46:48.792248+00:00
-- url     : https://prove2.me/submissions/35657094-48e5-4636-b465-242dddc8f79f

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/CircleExtension.lean:L62-L95
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.CircleConsequence.extend_to_five. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Model__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CircleInterpolation
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CircleRows
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CircleExtension

-- ---- from OAI.Combinatorics.EuclideanRamsey.CircleExtension ----
namespace OAI
noncomputable section
namespace EuclideanRamsey.CircleConsequence

theorem stereographic_recover (t : ℝ) :
    ((2*t)/(1+t^2)) / (1 + (1-t^2)/(1+t^2)) = t := by
  have hd : 1+t^2 ≠ 0 := by positivity
  have he : 1 + (1-t^2)/(1+t^2) = 2/(1+t^2) := by field_simp; ring
  rw [he, div_div]
  field_simp

theorem stereographic_injective (c : Space 2) (r : ℝ) (hr : 0 < r) :
    Function.Injective (stereographic c r) := by
  intro t u h
  have h₀ := congrArg (fun p : Space 2 => p 0) h
  have h₁ := congrArg (fun p : Space 2 => p 1) h
  have hx : (1-t^2)/(1+t^2) = (1-u^2)/(1+u^2) := by
    apply mul_left_cancel₀ (ne_of_gt hr)
    apply add_left_cancel (a := c 0)
    simpa only [stereographic, PiLp.add_apply, PiLp.smul_apply, PiLp.toLp_apply,
      Matrix.cons_val_zero, smul_eq_mul] using h₀
  have hy : (2*t)/(1+t^2) = (2*u)/(1+u^2) := by
    apply mul_left_cancel₀ (ne_of_gt hr)
    apply add_left_cancel (a := c 1)
    simpa only [stereographic, PiLp.add_apply, PiLp.smul_apply, PiLp.toLp_apply,
      Matrix.cons_val_one, Matrix.cons_val_zero, smul_eq_mul] using h₁
  calc
    t = ((2*t)/(1+t^2)) / (1 + (1-t^2)/(1+t^2)) := (stereographic_recover t).symm
    _ = ((2*u)/(1+u^2)) / (1 + (1-u^2)/(1+u^2)) := by rw [hx, hy]
    _ = u := stereographic_recover u

theorem stereographic_on_circle (c : Space 2) (r t : ℝ) (hr : 0 < r) :
    dist (stereographic c r t) c = r := by
  have hd : 1+t^2 ≠ 0 := by positivity
  have hs : ((1-t^2)/(1+t^2))^2 + ((2*t)/(1+t^2))^2 = 1 := by
    field_simp
    ring
  have he : dist (stereographic c r t) c ^ 2 = r^2 := by
    simp only [dist_eq_norm, stereographic, add_sub_cancel_left]
    rw [norm_smul, mul_pow]
    simp only [Real.norm_eq_abs, sq_abs, EuclideanSpace.norm_sq_eq,
      Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Real.norm_eq_abs, sq_abs]
    rw [hs, mul_one]
  have hn : 0 ≤ dist (stereographic c r t) c := dist_nonneg
  nlinarith

theorem circle_infinite (c : Space 2) (r : ℝ) (hr : 0 < r) :
    {p : Space 2 | dist p c = r}.Infinite := by
  apply (Set.infinite_range_of_injective (stereographic_injective c r hr)).mono
  rintro p ⟨t, rfl⟩
  exact stereographic_on_circle c r t hr

/-- Extension adds actual distinct points on the same metric circle. -/
theorem extend_to_five {s : ℕ} (a : Fin s → Space 2)
    (hs : s ≤ 5) (ha : Function.Injective a)
    (c : Space 2) (r : ℝ) (hr : 0 < r)
    (hc : ∀ i, dist (a i) c = r) :
    ∃ b : Fin 5 → Space 2, Function.Injective b ∧
      (∀ j, dist (b j) c = r) ∧ ∃ f : Fin s → Fin 5, ∀ i, b (f i) = a i := by
  classical
  let S : Finset (Space 2) := Finset.univ.image a
  have hS : S.card = s := by simp [S, Finset.card_image_of_injective _ ha]
  have hSc : ∀ p ∈ S, dist p c = r := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    exact hc i
  obtain ⟨T, hTc, hT⟩ := (circle_infinite c r hr).exists_subset_card_eq 5
  have hST : 5 ≤ (S ∪ T).card := by
    rw [← hT]
    exact Finset.card_le_card Finset.subset_union_right
  obtain ⟨U, hSU, hUst, hU⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_union_left : S ⊆ S ∪ T) (by omega : S.card ≤ 5) hST
  let e : U ≃ Fin 5 := Finset.equivFinOfCardEq hU
  let b : Fin 5 → Space 2 := fun j => (e.symm j).val
  refine ⟨b, ?_, ?_, ?_⟩
  · intro i j hij
    exact e.symm.injective (Subtype.ext hij)
  · intro j
    have hj : b j ∈ S ∪ T := hUst (e.symm j).property
    rcases Finset.mem_union.mp hj with hj | hj
    · exact hSc _ hj
    · exact hTc hj
  · let f : Fin s → Fin 5 := fun i => e ⟨a i, hSU (by simp [S])⟩
    refine ⟨f, ?_⟩
    intro i
    simp [b, f]
end EuclideanRamsey.CircleConsequence

end

end OAI

-- ---- platform node ----
open OAI OAI.EuclideanRamsey OAI.EuclideanRamsey.CircleConsequence


theorem solution : type_of% @_root_.OAI.EuclideanRamsey.CircleConsequence.extend_to_five := @_root_.OAI.EuclideanRamsey.CircleConsequence.extend_to_five
