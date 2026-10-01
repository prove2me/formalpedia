-- Prove2me | solution 1 for MilnorDynamics.exp_cayley_maps_to_punctured
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-01T07:52:54.774961+00:00
-- url     : https://prove2.me/submissions/f18148ba-18d1-423d-a284-d5ba8cb4b955

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

-- Proof of `MilnorDynamics.exp_cayley_maps_to_punctured`
-- (`db1444b1-5d50-4112-984a-b3e3ccdbf1f1`), variant 2: SELF-CONTAINED.
--
-- Variant 1 (candidate 5453, sha dc934b8a) cited the `Proved` sibling
-- `exp_cayley_avoid_punctures` (`9081076b`) by bare name and the remote reported
--   line 30: Unknown identifier `exp_cayley_avoid_punctures`
-- So a `Proved` platform theorem is NOT importable from
-- `Definitions.Def_MilnorDynamics_NormalFamilies`. The `p2m show` record for a
-- `Proved` target carries an empty `preamble` and no module path, and the `identifiers`
-- lint stage is `advisory`, so neither the record nor lint can reveal this. The whole
-- argument is therefore inlined here.
--
-- `MapsTo f s t` is `forall x in s, f x in t` (Mathlib/Data/Set/Operations.lean:295).
-- For each `z` in the disc, write `w = (z + 1) / (1 - z)`:
--   * `exp w != 0` is `Complex.exp_ne_zero` (Complex/Exponential.lean:162);
--   * `exp w != 1` because `exp_eq_exp_iff_exists_int`
--     (SpecialFunctions/Complex/Log.lean:171) would give `w = n * (2 * pi * I)`, whose
--     real part is `0`, whereas `Re(w) = (1 - norm z ^ 2) / norm (1 - z) ^ 2 > 0`.
--
-- The positivity is the same identity proved for `cayley_disk_lt_halfplane`, inlined
-- rather than cited, for the reason recorded above.

open scoped OnePoint
open Filter Set
open MilnorDynamics

theorem solution :
    MapsTo (fun z : ℂ => Complex.exp ((z + 1) / (1 - z)))
      (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ) := by
  intro z hz

  have hnorm : ‖z‖ < 1 := by simpa using hz
  have hre : 0 < ((z + 1) / (1 - z)).re := by
    -- `sub_ne_zero.mpr` is stated as `1 - z ≠ 0 → 1 ≠ z`, so the hypothesis must be
    -- `1 ≠ z`. The first version supplied `z ≠ 1` and the remote reported
    --   term `hne` has type `z ≠ 1` but is expected to have type `1 ≠ z`
    -- This is the same `sub_ne_zero` orientation lesson already recorded for
    -- `cayley_disk_lt_halfplane`.
    have hne : (1 : ℂ) ≠ z := by
      intro h
      -- `h : 1 = z` rewrites occurrences of `z`, not occurrences of `1`. The previous
      -- version wrote `rw [h, norm_one] at hnorm` and the remote reported
      --   Did not find an occurrence of the pattern `1` in the target `‖z‖ < 1`
      -- Symmetricating gives `z = 1`, which does occur, and `norm_one` then rewrites
      -- `‖1‖` to `1`.
      have hz1 : z = (1 : ℂ) := h.symm
      rw [hz1, norm_one] at hnorm
      exact (by norm_num : ¬ ((1 : ℝ) < 1)) hnorm
    have hden : ((1 : ℂ) - z) ≠ 0 := sub_ne_zero.mpr hne
    have hnormne : ‖((1 : ℂ) - z)‖ ≠ 0 := norm_ne_zero_iff.mpr hden
    have hdenR : 0 < ‖((1 : ℂ) - z)‖ ^ 2 := sq_pos_of_ne_zero hnormne
    have hnn : 0 ≤ ‖z‖ := norm_nonneg z
    have hnum : 0 < (1 : ℝ) - ‖z‖ ^ 2 := by nlinarith
    rw [Complex.div_re]
    rw [show ((1 : ℂ) - z).re = 1 - z.re by simp]
    rw [show ((1 : ℂ) - z).im = -z.im by simp]
    rw [show (z + 1).re = z.re + 1 by simp]
    rw [show (z + 1).im = z.im by simp]
    rw [Complex.normSq_eq_norm_sq]
    have hA : (z.re + 1) * (1 - z.re) + z.im * -z.im = (1 : ℝ) - ‖z‖ ^ 2 := by
      linarith [Complex.sq_norm_sub_sq_re z]
    have hD : (0 : ℝ) < ‖((1 : ℂ) - z)‖ ^ 2 := hdenR
    have hsum : (0 : ℝ) < ((z.re + 1) * (1 - z.re) + z.im * -z.im) / ‖((1 : ℂ) - z)‖ ^ 2 :=
      div_pos (by linarith [hA, hnum]) hD
    have heq : ((z.re + 1) * (1 - z.re)) / ‖((1 : ℂ) - z)‖ ^ 2 +
        (z.im * -z.im) / ‖((1 : ℂ) - z)‖ ^ 2 =
        ((z.re + 1) * (1 - z.re) + z.im * -z.im) / ‖((1 : ℂ) - z)‖ ^ 2 := by
      ring
    rw [heq]
    exact hsum
  -- The goal is MEMBERSHIP in the complement, `exp w ∈ {0, 1}ᶜ`, not the conjunction
  -- `exp w != 0 /\ exp w != 1`. Variant 2 (candidate 5455) spliced a conjunction proof in
  -- mechanically and the remote reported
  --   line 74: Tactic `constructor` failed: target is not an inductive datatype
  -- `{0, 1}ᶜ` is a `Set ℂ`, so `exp w ∈ {0, 1}ᶜ` is `exp w ∉ {0, 1}` -- a `Not`,
  -- not a conjunction. Variant 3 (candidate 5465) assumed a conjunction and the remote
  -- reported
  --   line 82: Invalid `⟨...⟩` notation: The expected type
  --     `Complex.exp ((z + 1) / (1 - z)) ∈ {0, 1} → False`
  --     is not an inductive type
  -- The correct shape is an implication with the two-element `Set` as its hypothesis,
  -- so the argument proceeds by contradiction from membership in `{0, 1}`.
  -- `{0, 1}ᶜ` is a `Set ℂ`, so the goal `exp w ∈ {0, 1}ᶜ` is `exp w ∉ {0, 1}`, a `Not`.
  -- Rather than destruct the membership by hand -- which previous attempts did wrongly
  -- three times: as a conjunction (5465, `Invalid ⟨...⟩ notation`), then by
  -- `Set.mem_insert.mp` (5470, `Dependent elimination failed: Failed to solve equation
  -- { re := 0, im := 0 } = Complex.exp …`) -- the membership is normalised by `simp`
  -- into the conjunction of two inequalities, which is a goal shape already proved
  -- for `exp_cayley_avoid_punctures`.
  -- `Set.mem_compl_iff : x ∈ sᶜ ↔ x ∉ s` (Mathlib/Data/Set/Operations.lean:118) and
  -- `Set.mem_insert_iff` (Mathlib/Data/Set/Insert.lean:70) normalise the goal to the
  -- conjunction of two inequalities, with no dependent elimination involved.
  -- After the first pass the goal is
  --   `exp w = 0 ∨ exp w ∈ {1} → False`
  -- (candidate 5474 stopped here, reporting `Invalid ⟨...⟩ notation` on exactly that
  -- type), so a second `simp` pass splits the singleton `{1}` into `exp w = 1`. Then the
  -- goal is the plain conjunction `exp w ≠ 0 ∧ exp w ≠ 1`, which is the shape already
  -- proved for `exp_cayley_avoid_punctures`.
  -- The two passes leave `exp w = 0 ∨ exp w = 1 → False`, i.e. a `Not` over a
  -- `Disj`. Candidate 5480 stopped here. `not_or` and `not_eq` push the negation
  -- through to the two disjuncts, giving the plain conjunction.
  -- Candidate 5480 supplied `not_eq`, which does not exist at this revision
  -- (`Unknown identifier 'not_eq'`). Rather than hunt for the right `Neg` lemma name,
  -- plain `simp` is used: it closes the complement, the two inserts and the singleton
  -- by the standard simp set, and pushes the negation through the resulting `Disj`.
  simp only [Set.mem_compl_iff, Set.mem_insert_iff]
  simp only [Set.mem_singleton_iff]
  simp only [not_or, not_false_eq_true]
  refine ⟨?_, ?_⟩
  · exact Complex.exp_ne_zero _
  · intro h1
    have h1' : Complex.exp ((z + 1) / (1 - z)) = Complex.exp 0 := by
      rw [Complex.exp_zero]
      exact h1
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h1'
    have hre0 : ((z + 1) / (1 - z)).re = 0 := by
      rw [hn]
      simp
    linarith
