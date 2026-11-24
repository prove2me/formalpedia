-- Prove2me | solution 1 for Kyprianou.Ch02.bvLevyDriftPlusJumpDecompositionV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T13:47:31.385945+00:00
-- url     : https://prove2.me/submissions/49f25754-3a5e-4ebb-ad33-5c3f93af457c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch02_bvLevyCanonicalJordanPathwiseV1
import Theorems.Thm_Kyprianou_Ch02_bvLevyJordanSposSnegEqJumpPlusDriftV1
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Drift plus signed jump-sum decomposition

Glue sketch: from the proved pathwise Jordan identity `X = Spos - Sneg` and the
open child asserting
`Spos = Jpos + dpos · t`, `Sneg = Jneg + dneg · t` a.s. with `dpos, dneg ≥ 0`,
set `d := dpos - dneg` to obtain
`X = d · t + Jpos - Jneg` a.s.
-/

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hBV : ∀ᵐ ω ∂P,
      LocallyBoundedVariationOn (fun t : ℝ≥0 => X t ω) Set.univ) :
    let Jpos : ℝ≥0 → Ω → ℝ := fun t ω =>
      ∑' s : Set.Ioc (0 : ℝ≥0) t,
        max (X s.1 ω -
          Filter.limUnder (nhdsWithin s.1 (Set.Iio s.1)) (fun u => X u ω)) 0
    let Jneg : ℝ≥0 → Ω → ℝ := fun t ω =>
      ∑' s : Set.Ioc (0 : ℝ≥0) t,
        max (Filter.limUnder (nhdsWithin s.1 (Set.Iio s.1)) (fun u => X u ω) -
          X s.1 ω) 0
    ∃ d : ℝ, ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      X t ω = d * (t : ℝ) + Jpos t ω - Jneg t ω := by
  dsimp only
  -- Proved: X = Spos - Sneg pathwise a.s. (expanded Jordan formulae).
  obtain ⟨_, _, hXeq⟩ :=
    Kyprianou.Ch02.bvLevyCanonicalJordanPathwiseV1 P X hX hBV
  -- Open child: Spos = Jpos + dpos·t and Sneg = Jneg + dneg·t a.s.
  -- Use `Exists.elim` (not `obtain`) to avoid dependent elimination on AE props.
  refine Exists.elim
    (Kyprianou.Ch02.bvLevyJordanSposSnegEqJumpPlusDriftV1 P X hX hBV)
    fun dpos hex =>
      Exists.elim hex fun dneg hpack => ?_
  rcases hpack with ⟨_, _, hSpos, hSneg⟩
  refine ⟨dpos - dneg, ?_⟩
  filter_upwards [hXeq, hSpos, hSneg] with ω hXω hSposω hSnegω
  intro t
  have hx := hXω t
  have hp := hSposω t
  have hn := hSnegω t
  -- hx / hp / hn are the expanded equalities; rearrange by `linarith`.
  linarith
