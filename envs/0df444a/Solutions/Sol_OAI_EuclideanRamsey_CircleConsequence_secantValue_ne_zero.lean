-- Prove2me | solution 1 for OAI.EuclideanRamsey.CircleConsequence.secantValue_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T12:38:35.22701+00:00
-- url     : https://prove2.me/submissions/42952142-b856-4c99-9e16-934efa096141

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/CircleInterpolation.lean:L50-L70
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.CircleConsequence.secantValue_ne_zero. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Model__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CircleInterpolation
import Theorems.Thm_OAI_EuclideanRamsey_CircleConsequence_secant_nonzero

-- ---- from OAI.Combinatorics.EuclideanRamsey.CircleInterpolation ----
namespace OAI

/- The secant equations and quadratic isolators have coefficients in the coordinate field. -/
noncomputable section
namespace EuclideanRamsey.CircleConsequence

/-- Nonzero evaluation follows from actual planar circle equations. -/
theorem secantValue_ne_zero {s : ℕ} (a : Fin s → Space 2)
    (ha : Function.Injective a) (c : Space 2) (R : ℝ)
    (hc : ∀ m, (a m 0-c 0)^2 + (a m 1-c 1)^2 = R)
    (i j k : Fin s) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    secantValue a i j k ≠ 0 := by
  have different (u v : Fin s) (huv : u ≠ v) :
      a u 0 ≠ a v 0 ∨ a u 1 ≠ a v 1 := by
    by_contra h
    push Not at h
    apply huv
    apply ha
    ext q
    fin_cases q <;> simp_all
  have h := secant_nonzero (a i 0) (a i 1) (a j 0) (a j 1)
    (a k 0) (a k 1) (c 0) (c 1) R (hc i) (hc j) (hc k)
    (different i j hij) (different i k hik) (different j k hjk)
  intro hz
  apply h
  have he := congrArg (fun z : Coeff a => (z : ℝ)) hz
  simpa [secantValue, coordinate] using he

end EuclideanRamsey.CircleConsequence

end

end OAI

-- ---- platform node ----
open OAI OAI.EuclideanRamsey OAI.EuclideanRamsey.CircleConsequence


theorem solution : type_of% @_root_.OAI.EuclideanRamsey.CircleConsequence.secantValue_ne_zero := @_root_.OAI.EuclideanRamsey.CircleConsequence.secantValue_ne_zero
