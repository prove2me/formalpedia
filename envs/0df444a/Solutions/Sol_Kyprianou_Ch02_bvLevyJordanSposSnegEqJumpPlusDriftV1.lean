-- Prove2me | solution 1 for Kyprianou.Ch02.bvLevyJordanSposSnegEqJumpPlusDriftV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T17:23:56.107889+00:00
-- url     : https://prove2.me/submissions/12bf8bdc-ce3e-45a6-9da8-b346c25af5e3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch02_bvLevyCanonicalJordanMarginalProcessesV1
import Theorems.Thm_Kyprianou_Ch02_bvLevyCanonicalJordanPathwiseV1
import Theorems.Thm_Kyprianou_Ch02_bvLevySubordinatorEqJumpSumPlusDriftV1
import Theorems.Thm_Kyprianou_Ch02_bvLevyJordanJumpsEqSignedProcessJumpsV1
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Jordan subordinators = jump sums + linear drifts

Glue sketch:
* proved marginals ⇒ `S±` are Lévy;
* proved pathwise ⇒ `S±` are a.s. monotone;
* open child `bvLevySubordinatorEqJumpSumPlusDriftV1` ⇒
  `S± = d±·t + jumpSum(S±)` with `d± ≥ 0`;
* open child `bvLevyJordanJumpsEqSignedProcessJumpsV1` ⇒
  `jumpSum(S±) = J±` (signed jumps of `X`);
* rewrite to the target identities.
-/

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hBV : ∀ᵐ ω ∂P,
      LocallyBoundedVariationOn (fun t : ℝ≥0 => X t ω) Set.univ) :
    let V : ℝ≥0 → Ω → ℝ := fun t ω =>
      variationOnFromTo (fun s : ℝ≥0 => X s ω) Set.univ 0 t
    let Spos : ℝ≥0 → Ω → ℝ := fun t ω => (V t ω + X t ω) / 2
    let Sneg : ℝ≥0 → Ω → ℝ := fun t ω => (V t ω - X t ω) / 2
    let Jpos : ℝ≥0 → Ω → ℝ := fun t ω =>
      ∑' s : Set.Ioc (0 : ℝ≥0) t,
        max (X s.1 ω -
          Filter.limUnder (nhdsWithin s.1 (Set.Iio s.1)) (fun u => X u ω)) 0
    let Jneg : ℝ≥0 → Ω → ℝ := fun t ω =>
      ∑' s : Set.Ioc (0 : ℝ≥0) t,
        max (Filter.limUnder (nhdsWithin s.1 (Set.Iio s.1)) (fun u => X u ω) -
          X s.1 ω) 0
    ∃ dpos dneg : ℝ, 0 ≤ dpos ∧ 0 ≤ dneg ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, Spos t ω = Jpos t ω + dpos * (t : ℝ)) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, Sneg t ω = Jneg t ω + dneg * (t : ℝ)) := by
  dsimp only
  let V : ℝ≥0 → Ω → ℝ := fun t ω =>
    variationOnFromTo (fun s : ℝ≥0 => X s ω) Set.univ 0 t
  let Spos : ℝ≥0 → Ω → ℝ := fun t ω => (V t ω + X t ω) / 2
  let Sneg : ℝ≥0 → Ω → ℝ := fun t ω => (V t ω - X t ω) / 2
  let Jpos : ℝ≥0 → Ω → ℝ := fun t ω =>
    ∑' s : Set.Ioc (0 : ℝ≥0) t,
      max (X s.1 ω -
        Filter.limUnder (nhdsWithin s.1 (Set.Iio s.1)) (fun u => X u ω)) 0
  let Jneg : ℝ≥0 → Ω → ℝ := fun t ω =>
    ∑' s : Set.Ioc (0 : ℝ≥0) t,
      max (Filter.limUnder (nhdsWithin s.1 (Set.Iio s.1)) (fun u => X u ω) -
        X s.1 ω) 0
  obtain ⟨hSposLevy, hSnegLevy⟩ :=
    Kyprianou.Ch02.bvLevyCanonicalJordanMarginalProcessesV1 P X hX hBV
  obtain ⟨hSposMono, hSnegMono, _⟩ :=
    Kyprianou.Ch02.bvLevyCanonicalJordanPathwiseV1 P X hX hBV
  -- Subordinator jump+drift for each Jordan margin.
  refine Exists.elim
    (Kyprianou.Ch02.bvLevySubordinatorEqJumpSumPlusDriftV1 P Spos hSposLevy hSposMono)
    fun dpos hpos => ?_
  rcases hpos with ⟨hdpos, hSposEq⟩
  refine Exists.elim
    (Kyprianou.Ch02.bvLevySubordinatorEqJumpSumPlusDriftV1 P Sneg hSnegLevy hSnegMono)
    fun dneg hneg => ?_
  rcases hneg with ⟨hdneg, hSnegEq⟩
  -- Identify Jordan jump sums with signed jumps of `X`.
  have hJumps :=
    Kyprianou.Ch02.bvLevyJordanJumpsEqSignedProcessJumpsV1 P X hX hBV
  rcases hJumps with ⟨hJpos, hJneg⟩
  refine ⟨dpos, dneg, hdpos, hdneg, ?_, ?_⟩
  · filter_upwards [hSposEq, hJpos] with ω hYω hJω
    intro t
    change Spos t ω = Jpos t ω + dpos * (t : ℝ)
    rw [hYω t, hJω t, add_comm]
  · filter_upwards [hSnegEq, hJneg] with ω hYω hJω
    intro t
    change Sneg t ω = Jneg t ω + dneg * (t : ℝ)
    rw [hYω t, hJω t, add_comm]
