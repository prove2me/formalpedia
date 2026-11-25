-- Prove2me | solution 1 for Kyprianou.Ch04.exercise42LipschitzTruncatedJumpSumLimitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:30:08.308429+00:00
-- url     : https://prove2.me/submissions/7253bb77-57ee-430b-a0c3-332085151c39

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_bvTruncatedPathCompactBoundV1
import Theorems.Thm_Kyprianou_Ch04_bvTruncatedPathsUniformV1
import Theorems.Thm_Kyprianou_Ch04_bvCompactSpatialLipschitzV1
import Theorems.Thm_Kyprianou_Ch04_bvFiniteTruncationJumpDifferenceV1
import Theorems.Thm_Kyprianou_Ch04_bvContDiffSpatialEvalTendstoV1
import Theorems.Thm_Kyprianou_Ch04_bvFiniteSetDominatedSumLimitV1
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- Dominated convergence of jump increments with the fixed first coordinate. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (X Xleft : NNReal → Omega → ℝ) (omega : Omega) (c : ℝ)
    (hRep : ∀ t : NNReal,
      Summable (fun s : Ioc (0 : NNReal) t => |X s omega - Xleft s omega|) ∧
      X t omega = X 0 omega + c * (t : ℝ) +
        ∑' s : Ioc (0 : NNReal) t, (X s omega - Xleft s omega))
    (hLeft : ∀ u : NNReal, 0 < u →
      Tendsto (fun v : NNReal => X v omega) (nhdsWithin u (Iio u))
        (nhds (Xleft u omega)))
    (U : NNReal → ℝ) (K : NNReal) (hULip : LipschitzWith K U)
    (hU0 : 0 ≤ U 0) (hUp : ∀ s : NNReal, 0 < s → 0 < U s)
    (f : ℝ × ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Set.prod (Set.Ici (0 : ℝ)) Set.univ))
    (t : NNReal) :
    let j : Ioc (0 : NNReal) t → ℝ := fun s => X s omega - Xleft s omega
    let P : Finset (Ioc (0 : NNReal) t) → NNReal → ℝ :=
      fun S u => X 0 omega + c * (u : ℝ) +
        ∑ s ∈ S, if (s : NNReal) ≤ u then j s else 0
    let Q : Finset (Ioc (0 : NNReal) t) → NNReal → ℝ :=
      fun S u => X 0 omega + c * (u : ℝ) +
        ∑ s ∈ S, if (s : NNReal) < u then j s else 0
    Tendsto (fun S : Finset (Ioc (0 : NNReal) t) => ∑ s ∈ S,
      (f (U s,P S s) - f (U s,Q S s))) atTop
      (nhds (∑' s : Ioc (0 : NNReal) t,
        (f (U s,X s omega) - f (U s,Xleft s omega)))) := by
  classical
  intro j P Q
  let I := Ioc (0 : NNReal) t
  let τ : I → ℝ := fun s => ((s : NNReal) : ℝ)
  have hτ : Function.Injective τ := fun i j h => Subtype.ext (NNReal.coe_injective h)
  let M := |X 0 omega| + |c| * (t : ℝ) + ∑' s, |j s|
  let G (S : Finset I) (s : I) := f (U s,P S s) - f (U s,Q S s)
  let g (s : I) := f (U s,X s omega) - f (U s,Xleft s omega)
  have hB := Kyprianou.Ch04.bvTruncatedPathCompactBoundV1 X Xleft omega c hRep hLeft t
  have hU := Kyprianou.Ch04.bvTruncatedPathsUniformV1 X Xleft omega c hRep hLeft t
  let T := U 0 + (K : ℝ) * (t : ℝ)
  have htime (s : I) : U s ∈ Icc (0 : ℝ) T := by
    refine ⟨(hUp s s.property.1).le, ?_⟩
    have h := hULip.dist_le_mul (s : NNReal) 0
    rw [Real.dist_eq, NNReal.dist_eq, NNReal.coe_zero, sub_zero, abs_of_nonneg
      (s : NNReal).coe_nonneg] at h
    have hh := (abs_le.mp h).2
    have hm := mul_le_mul_of_nonneg_left
      (show ((s : NNReal) : ℝ) ≤ (t : ℝ) from s.property.2) K.coe_nonneg
    dsimp [T]
    linarith
  obtain ⟨C,hC,hLip⟩ := Kyprianou.Ch04.bvCompactSpatialLipschitzV1 f hf T M
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
    exact (hLip (U s) (P S s) (Q S s) (htime s)
      (abs_le.mp hSP.1) (abs_le.mp hSP.2)).trans (mul_le_mul_of_nonneg_left hjb hC)
  · intro s
    have hp := hU.1.tendsto_at (show (s : NNReal) ∈ Icc 0 t from ⟨zero_le,s.property.2⟩)
    have hq := hU.2.tendsto_at s.property
    exact (Kyprianou.Ch04.bvContDiffSpatialEvalTendstoV1 atTop f hf (U s)
      (htime s).1 _ _ hp).sub
      (Kyprianou.Ch04.bvContDiffSpatialEvalTendstoV1 atTop f hf (U s)
        (htime s).1 _ _ hq)
