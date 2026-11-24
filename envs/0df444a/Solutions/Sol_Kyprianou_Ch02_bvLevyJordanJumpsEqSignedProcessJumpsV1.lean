-- Prove2me | solution 1 for Kyprianou.Ch02.bvLevyJordanJumpsEqSignedProcessJumpsV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T22:37:53.2666+00:00
-- url     : https://prove2.me/submissions/b2fcbf15-26e4-4777-aaa5-0e54c032006b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch02_bvLevyJordanJumpIdentityPointwiseV1
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false
set_option linter.unusedVariables false

/-!
Jordan jump sums equal signed jump sums of `X`.

On the BV ∩ càdlàg event, the pointwise child gives
`max(ΔS±,0) = max(±ΔX,0)` (with the usual sign), so the `∑'` of equal
nonnegative summands agree.
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
    let JSpos : ℝ≥0 → Ω → ℝ := fun t ω =>
      ∑' s : Set.Ioc (0 : ℝ≥0) t,
        max (Spos s.1 ω -
          Filter.limUnder (nhdsWithin s.1 (Set.Iio s.1)) (fun u => Spos u ω)) 0
    let JSneg : ℝ≥0 → Ω → ℝ := fun t ω =>
      ∑' s : Set.Ioc (0 : ℝ≥0) t,
        max (Sneg s.1 ω -
          Filter.limUnder (nhdsWithin s.1 (Set.Iio s.1)) (fun u => Sneg u ω)) 0
    (∀ᵐ ω ∂P, ∀ t : ℝ≥0, JSpos t ω = Jpos t ω) ∧
    (∀ᵐ ω ∂P, ∀ t : ℝ≥0, JSneg t ω = Jneg t ω) := by
  dsimp only
  let V : ℝ≥0 → Ω → ℝ := fun t ω =>
    variationOnFromTo (fun s : ℝ≥0 => X s ω) Set.univ 0 t
  let Spos : ℝ≥0 → Ω → ℝ := fun t ω => (V t ω + X t ω) / 2
  let Sneg : ℝ≥0 → Ω → ℝ := fun t ω => (V t ω - X t ω) / 2
  refine ⟨?_, ?_⟩
  · filter_upwards [hBV, hX.cadlag_ae] with ω hBVω hcad
    intro t
    refine tsum_congr fun s => ?_
    have hid :=
      Kyprianou.Ch02.bvLevyJordanJumpIdentityPointwiseV1
        (fun u => X u ω) s.1 hBVω hcad
    -- hid.1 : max(ΔSpos,0) = max(ΔX,0)
    simpa [Spos, V] using hid.1
  · filter_upwards [hBV, hX.cadlag_ae] with ω hBVω hcad
    intro t
    refine tsum_congr fun s => ?_
    have hid :=
      Kyprianou.Ch02.bvLevyJordanJumpIdentityPointwiseV1
        (fun u => X u ω) s.1 hBVω hcad
    -- hid.2 : max(ΔSneg,0) = max(-ΔX,0) = max(X_- - X, 0)
    -- align with Jneg encoding max(limUnder - X, 0)
    have h2 := hid.2
    -- max(-ΔX,0) = max(limUnder X - X, 0)
    simpa [Sneg, V, neg_sub] using h2
