-- Prove2me | solution 1 for OAI.EuclideanRamsey.CircleConsequence.normalized_isolators
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T12:41:43.148648+00:00
-- url     : https://prove2.me/submissions/569e2d38-7921-474f-b3ee-36b5ac24ccef

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/CircleRows.lean:L12-L34
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.CircleConsequence.normalized_isolators. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Model__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CircleInterpolation
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CircleRows
import Theorems.Thm_OAI_EuclideanRamsey_CircleConsequence_five_point_isolator

-- ---- from OAI.Combinatorics.EuclideanRamsey.CircleGeometry ----
namespace OAI

noncomputable section
namespace EuclideanRamsey.CircleConsequence

/-- The metric circle equation implies the scalar coordinate equation. -/
theorem circle_coordinates {s : ℕ} (a : Fin s → Space 2)
    (c : Space 2) (r : ℝ) (hc : ∀ i, dist (a i) c = r) :
    ∀ i, (a i 0-c 0)^2 + (a i 1-c 1)^2 = r^2 := by
  intro i
  have h := congrArg (fun x : ℝ => x^2) (hc i)
  simpa [dist_eq_norm, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two,
    Real.norm_eq_abs, sq_abs] using h

end EuclideanRamsey.CircleConsequence

end

end OAI

-- ---- from OAI.Combinatorics.EuclideanRamsey.CircleRows ----
namespace OAI
noncomputable section
namespace EuclideanRamsey.CircleConsequence

/-- Normalized coefficients for quadratic interpolation at five circle points. -/
theorem normalized_isolators (a : Fin 5 → Space 2) (ha : Function.Injective a)
    (c : Space 2) (r : ℝ) (hc : ∀ i, dist (a i) c = r) :
    ∃ L : Fin 5 → QIndex → Coeff a,
      ∀ i j, ∑ q, L i q * quadraticRow a j q = if j = i then 1 else 0 := by
  classical
  have hcoord := circle_coordinates a c r hc
  have hiso (i : Fin 5) : ∃ M : QIndex → Coeff a,
      (∀ j, j ≠ i → ∑ q, M q * quadraticRow a j q = 0) ∧
      (∑ q, M q * quadraticRow a i q) ≠ 0 := by
    obtain ⟨M, hM, hMi⟩ := five_point_isolator a ha c (r^2) hcoord (Equiv.swap 0 i)
    refine ⟨fun q => M q.1 q.2, ?_, ?_⟩
    · intro j hj
      simpa [quadraticRow, Fintype.sum_prod_type, mul_assoc] using hM j (by simpa using hj)
    · simpa [quadraticRow, Fintype.sum_prod_type, mul_assoc] using hMi
  choose M hM hMi using hiso
  refine ⟨fun i q => (∑ t, M i t * quadraticRow a i t)⁻¹ * M i q, ?_⟩
  intro i j
  simp_rw [mul_assoc, ← Finset.mul_sum]
  by_cases hji : j = i
  · subst j
    simp [hMi]
  · simp [hji, hM i j hji]

end EuclideanRamsey.CircleConsequence

end

end OAI

-- ---- platform node ----
open OAI OAI.EuclideanRamsey OAI.EuclideanRamsey.CircleConsequence


theorem solution : type_of% @_root_.OAI.EuclideanRamsey.CircleConsequence.normalized_isolators := @_root_.OAI.EuclideanRamsey.CircleConsequence.normalized_isolators
