-- Prove2me | solution 1 for MilnorDynamics.schottky_two_point
-- status  : ACCEPTED   (disprove)
-- author  : @WillR
-- created : 2026-10-01T23:48:01.923145+00:00
-- url     : https://prove2.me/submissions/342fa9be-c060-4e14-b3cc-53c430093ce1

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set
open MilnorDynamics

/-- `schottky_two_point` is false as published.

The hypotheses constrain `g` only on the **open** ball `Metric.ball 0 (1/2)`, while the
conclusion bounds the value of `g` at `1/2`.  Since `‖1/2‖ = 1/2` is exactly the radius,
`1/2` lies in none of the hypotheses, so that value is a free parameter and no uniform
bound on it follows.  Fixing `M := 1` refutes the statement.

Repairs, each tied to the exact reported evidence of CEs 6016/6018:

* **E01 (6016)** `Metric.mem_ball_iff_norm` is an unknown identifier.  The `to_additive`
  of `mem_ball_iff_norm''` (Analysis/Normed/Group/Basic.lean:869) is emitted in the
  **root** namespace, not under `Metric`, so it is used unqualified here.
* **E02/E04 (6016), E03 (6018)** `RCLike.norm_ofReal` reports no occurrence of
  `‖↑(1 / 2)‖` in `‖1 / 2‖ < 1 / 2`.  That is because the rational has already been
  reduced, so there is no cast redex; the two norms are instead discharged by `norm_num`
  on the fully concrete goal, which needs no rewrite at all.
* **E03 (6016), E02 (6018)** `Invalid field 'congr': the environment does not contain
  `Function.congr`.  `differentiable_const` returns `Differentiable`, which has no
  `congr` field; `DifferentiableOn.congr` (Analysis/Calculus/FDeriv/Congr.lean:201) is a
  *theorem* applied to an explicit proof, so it is invoked as a function.
* **E01 (6025)** With the five earlier causes repaired, exactly one error group remains and
  it is the escape recollapse.  The report gives pattern `↑D + ↑1` against target
  `D < ‖↑D + 1‖`.  `Complex.ofReal_add` (Data/Complex/Basic.lean:178) is
  `((r + s : ℝ) : ℂ) = r + s`, so its right-hand side is a *coerced* `↑1`, while the goal
  carries an `OfNat` `1` produced by `Complex.instHAdd`.  The two are not syntactically equal,
  which is exactly the "implicit casts blocking matching" rung of the
  `rewrite-pattern-not-found` repair ladder.
* **E01 (6045)** `v27` tried to bridge that gap with `← Complex.ofReal_one` and still failed,
  because `rw` applies its rules left to right and aborts at the first rule that does not
  match: the recollapse ran before the bridge had introduced the `↑1` it needed.
  **This variant avoids the ordering question altogether** by removing the recollapse from
  the proof.  The witness value is written `((D + 1 : ℝ) : ℂ)` rather than the distributed
  `(D + 1 : ℂ)`, so after `rw [hval]` the goal is already `D < ‖↑(D + 1)‖` and
  `RCLike.norm_ofReal (D + 1)` would match directly, with no `ofReal_add` and no `ofReal_one`.
* **E01 (6046)** `v28` already produced the goal `D < ‖↑(D + 1)‖` and still failed, which
  shows the obstacle was never the cast shape: `RCLike.norm_ofReal`
  (`Analysis/RCLike/Basic.lean:246`) is proved through the generic `K` norm instance, so it
  does not match `Complex`'s own `Coe ℝ ℂ` coercion (`Data/Complex/Basic.lean:85`).
  The fix is `Complex.norm_of_nonneg {r : ℝ} (h : 0 ≤ r) : ‖(r : ℂ)‖ = r`
  (`Analysis/Complex/Norm.lean:108`), stated directly for the complex norm and already the
  identity needed - no `abs` step, no `RCLike`, no recollapse. -/
theorem solution :
    ¬ (∀ (M : ℝ), 0 ≤ M → ∃ D : ℝ, 0 ≤ D ∧ ∀ (g : ℂ → ℂ),
      DifferentiableOn ℂ g (Metric.ball 0 (1/2)) →
      MapsTo g (Metric.ball 0 (1/2)) ({0, 1}ᶜ : Set ℂ) →
      ‖g 0‖ ≤ M → ‖g (1/2 : ℂ)‖ ≤ D) := by
  intro hall
  obtain ⟨D, hD0, hD⟩ := hall (1 : ℝ) (by norm_num)
  have hhalf : ((1/2 : ℂ) ∉ Metric.ball 0 (1/2)) := by
    intro hb
    have hlt : ‖(1 / 2 : ℂ) - 0‖ < (1 / 2 : ℝ) := mem_ball_iff_norm.mp hb
    rw [sub_zero] at hlt
    norm_num at hlt
  have hcompl : ((1 / 2 : ℂ) ∈ ({0, 1}ᶜ : Set ℂ)) := by
    show (1 / 2 : ℂ) ∉ ({0, 1} : Set ℂ)
    rw [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (hz | hz)
    · exact (by norm_num : (1 / 2 : ℂ) ≠ 0) hz
    · exact (by norm_num : (1 / 2 : ℂ) ≠ 1) hz
  set g : ℂ → ℂ := fun z => if z = (1/2 : ℂ) then ((D + 1 : ℝ) : ℂ) else (1/2 : ℂ) with hg
  have hval : g (1/2 : ℂ) = ((D + 1 : ℝ) : ℂ) := by simp only [hg, if_pos rfl]
  have hconst : ∀ z ∈ Metric.ball 0 (1/2), g z = (1/2 : ℂ) := by
    intro z hz
    have hz2 : z ≠ (1/2 : ℂ) := fun hze => hhalf (hze ▸ hz)
    simp only [hg, if_neg hz2]
  have hdiff : DifferentiableOn ℂ g (Metric.ball 0 (1/2)) :=
    DifferentiableOn.congr (differentiableOn_const (𝕜 := ℂ) (1/2 : ℂ)) hconst
  have hmap : MapsTo g (Metric.ball 0 (1/2)) ({0, 1}ᶜ : Set ℂ) := by
    intro z hz
    rw [hconst z hz]
    exact hcompl
  have hz0 : ‖g 0‖ ≤ (1 : ℝ) := by
    have h0mem : ((0 : ℂ) ∈ Metric.ball 0 (1/2)) := Metric.mem_ball_self (by norm_num)
    have h0 : g 0 = (1 / 2 : ℂ) := hconst 0 h0mem
    rw [h0]
    norm_num
  have hbig : D < ‖g (1/2 : ℂ)‖ := by
    rw [hval, Complex.norm_of_nonneg (by linarith [hD0])]
    linarith
  have hle : ‖g (1/2 : ℂ)‖ ≤ D := hD g hdiff hmap hz0
  exact absurd hle (not_le_of_gt hbig)
