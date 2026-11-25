-- Prove2me | solution 1 for Kyprianou.Ch04.bvTruncatedJumpSumLimitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T07:46:54.529184+00:00
-- url     : https://prove2.me/submissions/7d0b3048-d6d2-4475-a8ae-946defe4b113

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_bvTruncatedPathCompactBoundV1
import Theorems.Thm_Kyprianou_Ch04_bvTruncatedPathsUniformV1
import Theorems.Thm_Kyprianou_Ch04_bvCompactSpatialLipschitzV1
import Theorems.Thm_Kyprianou_Ch04_bvFiniteTruncationJumpDifferenceV1
import Theorems.Thm_Kyprianou_Ch04_bvContDiffSpatialEvalTendstoV1
import Theorems.Thm_Kyprianou_Ch04_bvFiniteSetDominatedSumLimitV1
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false
open Kyprianou.Ch04

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (X Xleft : NNReal → Omega → Real) (omega : Omega) (c : Real)
    (hRep : forall t : NNReal,
      Summable (fun s : Set.Ioc (0 : NNReal) t => |X s omega - Xleft s omega|) ∧
      X t omega = X 0 omega + c * (t : Real) +
        ∑' s : Set.Ioc (0 : NNReal) t, (X s omega - Xleft s omega))
    (hLeft : ∀ u : NNReal, 0 < u →
      Tendsto (fun v : NNReal => X v omega) (nhdsWithin u (Set.Iio u))
        (nhds (Xleft u omega)))
    (f : ℝ × ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Set.prod (Set.Ici (0 : ℝ)) Set.univ))
    (t : NNReal) :
    let j : Set.Ioc (0 : NNReal) t → ℝ := fun s => X s omega - Xleft s omega
    let P : Finset (Set.Ioc (0 : NNReal) t) → NNReal → ℝ :=
      fun S u => X 0 omega + c * (u : ℝ) + ∑ s ∈ S, if (s : NNReal) ≤ u then j s else 0
    let Q : Finset (Set.Ioc (0 : NNReal) t) → NNReal → ℝ :=
      fun S u => X 0 omega + c * (u : ℝ) + ∑ s ∈ S, if (s : NNReal) < u then j s else 0
    Tendsto (fun S : Finset (Set.Ioc (0 : NNReal) t) => ∑ s ∈ S,
      (f (((s : NNReal) : ℝ),P S s) - f (((s : NNReal) : ℝ),Q S s))) atTop
      (nhds (∑' s : Set.Ioc (0 : NNReal) t,
        (f (((s : NNReal) : ℝ),X s omega) - f (((s : NNReal) : ℝ),Xleft s omega)))) := by
  classical
  intro j P Q
  let I := Set.Ioc (0 : NNReal) t
  let τ : I → ℝ := fun s => ((s : NNReal) : ℝ)
  have hτ : Function.Injective τ := fun i j h => Subtype.ext (NNReal.coe_injective h)
  let M := |X 0 omega| + |c| * (t : ℝ) + ∑' s, |j s|
  let G (S : Finset I) (s : I) := f (τ s,P S s) - f (τ s,Q S s)
  let g (s : I) := f (τ s,X s omega) - f (τ s,Xleft s omega)
  have hB := Kyprianou.Ch04.bvTruncatedPathCompactBoundV1 X Xleft omega c hRep hLeft t
  have hU := Kyprianou.Ch04.bvTruncatedPathsUniformV1 X Xleft omega c hRep hLeft t
  obtain ⟨C,hC,hLip⟩ := Kyprianou.Ch04.bvCompactSpatialLipschitzV1 f hf (t : ℝ) M
  have hb : Summable (fun s : I => C * |j s|) := (hRep t).1.mul_left C
  change Tendsto (fun S : Finset I => ∑ s ∈ S, G S s) atTop (nhds (∑' s, g s))
  apply Kyprianou.Ch04.bvFiniteSetDominatedSumLimitV1 G g (fun s => C * |j s|) hb
  · intro s
    exact mul_nonneg hC (abs_nonneg _)
  · intro S s
    have hSP := hB.2.1 S s s.property.2
    have hj : P S s - Q S s = if s ∈ S then j s else 0 := by
      simpa only [P,Q,τ,NNReal.coe_le_coe,NNReal.coe_lt_coe] using
        Kyprianou.Ch04.bvFiniteTruncationJumpDifferenceV1
          τ hτ j (X 0 omega) c S s
    have hjb : |P S s - Q S s| ≤ |j s| := by
      rw [hj]
      by_cases hs : s ∈ S <;> simp [hs]
    have htime : τ s ∈ Set.Icc (0 : ℝ) (t : ℝ) := ⟨(s : NNReal).coe_nonneg,s.property.2⟩
    exact (hLip (τ s) (P S s) (Q S s) htime
      (abs_le.mp hSP.1) (abs_le.mp hSP.2)).trans (mul_le_mul_of_nonneg_left hjb hC)
  · intro s
    have hp := hU.1.tendsto_at (show (s : NNReal) ∈ Set.Icc 0 t from ⟨zero_le,s.property.2⟩)
    have hq := hU.2.tendsto_at s.property
    exact (Kyprianou.Ch04.bvContDiffSpatialEvalTendstoV1 atTop f hf (τ s)
      (s : NNReal).coe_nonneg _ _ hp).sub
      (Kyprianou.Ch04.bvContDiffSpatialEvalTendstoV1 atTop f hf (τ s)
        (s : NNReal).coe_nonneg _ _ hq)
