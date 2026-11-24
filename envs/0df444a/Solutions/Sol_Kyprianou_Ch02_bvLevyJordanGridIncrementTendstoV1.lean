-- Prove2me | solution 1 for Kyprianou.Ch02.bvLevyJordanGridIncrementTendstoV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:54:30.245114+00:00
-- url     : https://prove2.me/submissions/7ab843a2-a741-46c2-b24e-b5980b8c9213

import Theorems.Thm_Kyprianou_Ch02_bvPathEqualGridJordanSumsTendstoV1
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hBV : ∀ᵐ ω ∂P,
      LocallyBoundedVariationOn (fun t : ℝ≥0 => X t ω) Set.univ) :
    let G : ℕ → ℝ≥0 → ℝ≥0 → Ω → ℝ × ℝ := fun n a b ω =>
      let g (k : ℕ) := a + (b-a)*(k : ℝ≥0)/((n+1 : ℕ) : ℝ≥0)
      let d (k : ℕ) := X (g (k+1)) ω - X (g k) ω
      (∑ k : Fin (n+1), max (d k) 0, ∑ k : Fin (n+1), max (-d k) 0)
    let V : ℝ≥0 → Ω → ℝ := fun t ω =>
      variationOnFromTo (fun s : ℝ≥0 => X s ω) Set.univ 0 t
    let Y : ℝ≥0 → Ω → ℝ × ℝ := fun t ω =>
      ((V t ω + X t ω)/2, (V t ω - X t ω)/2)
    ∀ a b : ℝ≥0, a ≤ b → ∀ᵐ ω ∂P,
      Tendsto (fun n => G n a b ω) atTop
        (nhds (increment Y a b ω)) := by
  dsimp only
  intro a b hab
  filter_upwards [hBV, hX.cadlag_ae] with ω hbv hc
  let f : ℝ≥0 → ℝ := fun t => X t ω
  let g (n k : ℕ) : ℝ≥0 := a+(b-a)*(k : ℝ≥0)/((n+1 : ℕ) : ℝ≥0)
  let d (n k : ℕ) : ℝ := f (g n (k+1)) - f (g n k)
  let v := variationOnFromTo f univ
  have hpair := Kyprianou.Ch02.bvPathEqualGridJordanSumsTendstoV1 f a b hab hbv
    (fun t => (hc t).1)
  have hv : v 0 b - v 0 a = v a b :=
    variationOnFromTo.sub_right hbv (mem_univ _) (mem_univ _) (mem_univ _)
  convert hpair using 1
  apply congrArg nhds
  change ((v 0 b + f b)/2 - (v 0 a+f a)/2,
    (v 0 b-f b)/2-(v 0 a-f a)/2) = _
  change (_, _) = ((v a b + (f b-f a))/2, (v a b-(f b-f a))/2)
  rw [← hv]
  congr 1 <;> ring
