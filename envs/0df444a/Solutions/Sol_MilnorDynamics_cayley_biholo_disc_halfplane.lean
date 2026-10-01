-- Prove2me | solution 1 for MilnorDynamics.cayley_biholo_disc_halfplane
-- status  : ACCEPTED   (disprove)
-- author  : @WillR
-- created : 2026-10-01T02:25:28.527304+00:00
-- url     : https://prove2.me/submissions/f9991e3e-7468-4b34-9502-e1f7ea5de46b

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

-- DISPROOF of `MilnorDynamics.cayley_biholo_disc_halfplane`
-- (`0b98590f-d3e4-4346-a22f-a05c7a9e1303`), by exhibiting a witness to the negation
-- of its first conjunct.
--
-- The target asserts
--
--   IsEmpty {z : ℂ // z ∈ Set.univ ∧ (1 - z) = 0} ∧ ...
--
-- But `z = 1` lies in that subtype: `1 ∈ Set.univ` holds, and `1 - 1 = 0`. So the
-- subtype is inhabited and `IsEmpty` is false. The theorem cannot be true as stated.
--
-- The docstring says "has no pole there", where "there" is the open unit disc. The
-- correct statement restricts to the disc:
--
--   IsEmpty {z : ℂ // z ∈ Metric.ball 0 1 ∧ (1 - z) = 0}
--
-- which is true because `‖1‖ = 1` is not `< 1`. The published statement quantifies over
-- `Set.univ` instead of `Metric.ball 0 1`, which drops the disc restriction and makes
-- the claim false.
--
-- The first version of this disproof (candidate 5383, sha 4993ec68) hit the same
-- `⟨...⟩` mistake as the proof attempts: `¬IsEmpty s` does not unfold to a constructor
-- application, so the remote reported
--   line 30: Invalid `⟨...⟩` notation: The expected type
--     `IsEmpty { z // z ∈ univ ∧ 1 - z = 0 } → False` is not an inductive type
-- The fix is `not_isEmpty_iff : ¬IsEmpty α ↔ Nonempty α`
-- (Mathlib/Logic/IsEmpty/Basic.lean:25), which turns the goal into exhibiting an
-- inhabitant.
--
-- The second version (candidate 5394, sha 560af558) then failed on one more
-- arity slip. `Set.mem_univ` is a theorem, not a nullary value:
--   line 40: Application type mismatch: The argument `mem_univ` has type
--     `∀ (x : ?m.25), x ∈ univ` but is expected to have type `1 ∈ univ`
-- It must be applied to the witness, `Set.mem_univ 1`.
--
-- The third version (candidate 5398, sha 635f5704) was accepted as `WA` for the
-- negated first conjunct, but the harness compares `solution` against the *whole*
-- theorem, so it reported
--   Your proof does not match the target type:
--   Application type mismatch: The argument
--     `MilnorDynamics.cayley_biholo_disc_halfplane`
--   has type `IsEmpty … ∧ IsOpen … ∧ DifferentiableOn …`
--   but is expected to have type `IsEmpty { z // z ∈ univ ∧ 1 - z = 0 }`
-- So a disproof must negate the full conjunction. Note that Lean itself elaborated
-- and accepted `¬ IsEmpty {z : ℂ // z ∈ univ ∧ 1 - z = 0}` in that verdict, which is
-- independent confirmation from the platform that the subtype really is inhabited by
-- `z = 1` and the theorem is false as stated.

open scoped OnePoint
open Filter Set
open MilnorDynamics

theorem solution :
    ¬ (IsEmpty {z : ℂ // z ∈ Set.univ ∧ (1 - z) = 0} ∧
      IsOpen (Set.range (fun z : ℂ => (z + 1) / (1 - z))) ∧
      DifferentiableOn ℂ (fun z : ℂ => (z + 1) / (1 - z)) (Metric.ball 0 1)) := by
  intro h
  have hne : ¬ IsEmpty {z : ℂ // z ∈ Set.univ ∧ (1 - z) = 0} := by
    rw [not_isEmpty_iff]
    exact ⟨⟨1, Set.mem_univ 1, by norm_num⟩⟩
  exact hne h.1
