-- Prove2me | solution 3 for MilnorDynamics.montel_three_omitted_values
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-02T09:08:44.56758+00:00
-- url     : https://prove2.me/submissions/40c1b183-48c2-4dd1-b44a-86c9075c4bff
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies
import Theorems.Thm_MilnorDynamics_montel_reduce_to_normalized_open
import Theorems.Thm_MilnorDynamics_montel_normalized_omitting_zero_one_infty

open scoped OnePoint
open Filter Set
open MilnorDynamics

/--
Montel's theorem for maps omitting three values, by reduction to the normalised core.

This is the milestone target `MilnorDynamics.montel_three_omitted_values`. It is the
composition of the two published children of its accepted decomposition:

* `MilnorDynamics.montel_reduce_to_normalized_open` (`17b51714`, **Proved**) — postcompose
  the family by the invertible matrix carrying `a, b, c` to `0, 1, ∞`. The normalised
  family omits `{0, 1, ∞}`, and normality transfers back because the matrix action and its
  inverse are continuous and uniformly continuous in the chordal metric.
* `MilnorDynamics.montel_normalized_omitting_zero_one_infty` (`2ed4dd6c`) — the core
  Montel argument for the normalised family.

Note on `montel_reduce_to_normalized` (`909f78ec`): that live sibling omits `(hU : IsOpen U)`
from its binder list and is therefore not usable here. Its own decomposition cites the
**Disproved** child `isHolomorphicOn_smul_gl` (`c0cfcaeb`), so it cannot close in that form;
the `hU` hypothesis is genuinely required, because `IsHolomorphicOn` does not assume
`IsOpen U` and the accepted proof of `isHolomorphicOn_smul_gl_open` uses `hU` precisely to
promote `ContinuousOn` to `ContinuousAt` before rewriting the charts. This milestone
target carries `hU` itself, so `17b51714` applies directly.
-/
theorem solution (U : Set ℂ) (hU : IsOpen U) (hUc : IsConnected U)
    (a b c : OnePoint ℂ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (𝓕 : Set (ℂ → OnePoint ℂ))
    (h𝓕 : ∀ f ∈ 𝓕, IsHolomorphicOn U f ∧ ∀ z ∈ U, f z ≠ a ∧ f z ≠ b ∧ f z ≠ c) :
    IsNormalFamily U 𝓕 := by
  obtain ⟨𝓖, h𝓖, htransfer⟩ :=
    montel_reduce_to_normalized_open a b c hab hac hbc U hU 𝓕 h𝓕
  exact htransfer (montel_normalized_omitting_zero_one_infty U hU hUc 𝓖 h𝓖)
