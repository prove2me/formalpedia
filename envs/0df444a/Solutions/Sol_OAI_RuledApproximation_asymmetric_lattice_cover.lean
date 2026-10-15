-- Prove2me | solution 1 for OAI.RuledApproximation.asymmetric_lattice_cover
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T07:37:59.558708+00:00
-- url     : https://prove2.me/submissions/cbb394f2-176d-442c-ab43-2cabf28de9e3

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/Lattice.lean:L50-L108
-- (upload_full_project.md Phase 4): solution for node OAI.RuledApproximation.asymmetric_lattice_cover. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection
import Definitions.Def_OAI_Geometry_RuledCovering_Frames
import Definitions.Def_OAI_Geometry_RuledCovering_OuterApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_Lattice
import Theorems.Thm_OAI_RuledApproximation_integer_fixed_point_of_bounded_drift

-- ---- from OAI.Geometry.RuledCovering.Lattice ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma nearestInteger_mono : Monotone nearestInteger := by
  intro a b hab
  exact Int.floor_mono (by linarith)

lemma nearestInteger_error (t : ℝ) : |(nearestInteger t : ℝ) - t| ≤ 1 / 2 := by
  have h₁ := Int.floor_le (t + 1 / 2)
  have h₂ := Int.lt_floor_add_one (t + 1 / 2)
  unfold nearestInteger
  rw [abs_le]
  constructor <;> linarith

/-- A useful strengthening of the lattice estimates: only the product
conditions are needed; either off-diagonal entry may be arbitrarily large. -/
theorem asymmetric_lattice_cover (alpha beta : ℝ)
    (hprod : 0 ≤ alpha * beta) (hprod' : alpha * beta < 1) (u₁ u₂ : ℝ) :
    ∃ i j : ℤ, |u₁ - ((i : ℝ) + alpha * j)| ≤ 1 / 2 ∧
      |u₂ - (beta * i + (j : ℝ))| ≤ 1 / 2 := by
  let F : ℤ → ℤ := fun i => nearestInteger
    (u₁ - alpha * (nearestInteger (u₂ - beta * (i : ℝ)) : ℝ))
  have hmono : Monotone F := by
    intro i j hij
    have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
    rcases mul_nonneg_iff.mp hprod with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · have hinner : nearestInteger (u₂ - beta * (j : ℝ)) ≤
          nearestInteger (u₂ - beta * (i : ℝ)) :=
        nearestInteger_mono (by nlinarith)
      have hinner' : (nearestInteger (u₂ - beta * (j : ℝ)) : ℝ) ≤
          (nearestInteger (u₂ - beta * (i : ℝ)) : ℝ) := by exact_mod_cast hinner
      exact nearestInteger_mono (by nlinarith)
    · have hinner : nearestInteger (u₂ - beta * (i : ℝ)) ≤
          nearestInteger (u₂ - beta * (j : ℝ)) :=
        nearestInteger_mono (by nlinarith)
      have hinner' : (nearestInteger (u₂ - beta * (i : ℝ)) : ℝ) ≤
          (nearestInteger (u₂ - beta * (j : ℝ)) : ℝ) := by exact_mod_cast hinner
      exact nearestInteger_mono (by nlinarith)
  have hdrift : ∀ i : ℤ,
      |(F i : ℝ) - (alpha * beta) * i| ≤
        1 / 2 + |alpha| * (1 / 2) + |u₁ - alpha * u₂| := by
    intro i
    let j := nearestInteger (u₂ - beta * (i : ℝ))
    have h₁ := nearestInteger_error (u₁ - alpha * (j : ℝ))
    have h₂ := nearestInteger_error (u₂ - beta * (i : ℝ))
    have hdecomp : (F i : ℝ) - (alpha * beta) * i =
        ((F i : ℝ) - (u₁ - alpha * j)) -
        alpha * ((j : ℝ) - (u₂ - beta * i)) + (u₁ - alpha * u₂) := by ring
    rw [hdecomp]
    calc
      _ ≤ |(F i : ℝ) - (u₁ - alpha * j)| +
          |alpha * ((j : ℝ) - (u₂ - beta * i))| + |u₁ - alpha * u₂| :=
        (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ 1 / 2 + |alpha| * (1 / 2) + |u₁ - alpha * u₂| := by
        rw [abs_mul]
        exact add_le_add (add_le_add h₁ (mul_le_mul_of_nonneg_left h₂ (abs_nonneg _))) le_rfl
  obtain ⟨i, hi⟩ := integer_fixed_point_of_bounded_drift F hmono
    (alpha * beta) _ hprod' hdrift
  let j := nearestInteger (u₂ - beta * (i : ℝ))
  refine ⟨i, j, ?_, ?_⟩
  · have h := nearestInteger_error (u₁ - alpha * (j : ℝ))
    change |(F i : ℝ) - (u₁ - alpha * (j : ℝ))| ≤ 1 / 2 at h
    rw [hi] at h
    convert h using 1
    rw [← abs_neg]
    congr 1
    ring
  · have h := nearestInteger_error (u₂ - beta * (i : ℝ))
    change |(j : ℝ) - (u₂ - beta * (i : ℝ))| ≤ 1 / 2 at h
    convert h using 1
    rw [← abs_neg]
    congr 1
    ring

end RuledApproximation

end

end OAI

-- ---- platform node ----
open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff


theorem solution : type_of% @_root_.OAI.RuledApproximation.asymmetric_lattice_cover := @_root_.OAI.RuledApproximation.asymmetric_lattice_cover
