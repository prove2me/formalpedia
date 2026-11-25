-- Prove2me | solution 1 for Kyprianou.Ch04.exercise42LipschitzTruncatedDerivativeUniformV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T19:58:33.45426+00:00
-- url     : https://prove2.me/submissions/260157e3-e8a8-4933-9bbe-a42df9be8a37

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_bvTruncatedPathsUniformV1
import Theorems.Thm_Kyprianou_Ch04_bvTruncatedPathCompactBoundV1
import Theorems.Thm_Kyprianou_Ch04_bvFullFderivEqWithinPositiveV1
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04

/-- The first coordinate may be any fixed positive Lipschitz path: uniform
continuity of fderiv on its compact range preserves uniform convergence. -/
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
    (t : NNReal) (v : ℝ × ℝ) :
    let j : Ioc (0 : NNReal) t → ℝ := fun s => X s omega - Xleft s omega
    let P : Finset (Ioc (0 : NNReal) t) → NNReal → ℝ :=
      fun S u => X 0 omega + c * (u : ℝ) +
        ∑ s ∈ S, if (s : NNReal) ≤ u then j s else 0
    TendstoUniformlyOn
      (fun S (u : ℝ) => fderiv ℝ f (U (Real.toNNReal u), P S (Real.toNNReal u)) v)
      (fun u : ℝ => fderiv ℝ f (U (Real.toNNReal u), X (Real.toNNReal u) omega) v)
      atTop (Ioc (0 : ℝ) (t : ℝ)) := by
  classical
  intro j P
  let M := |X 0 omega| + |c| * (t : ℝ) + ∑' s, |j s|
  let H : Set (ℝ × ℝ) := Set.prod (Ici (0 : ℝ)) Set.univ
  let C : Set (ℝ × ℝ) :=
    Set.prod (U '' Icc (0 : NNReal) t) (Icc (-M) M)
  let D : ℝ × ℝ → ℝ := fun z => fderivWithin ℝ f H z v
  have hR : TendstoUniformlyOn P (fun u => X u omega) atTop
      (Icc (0 : NNReal) t) :=
    (Kyprianou.Ch04.bvTruncatedPathsUniformV1 X Xleft omega c hRep hLeft t).1
  have hB := Kyprianou.Ch04.bvTruncatedPathCompactBoundV1
    X Xleft omega c hRep hLeft t
  have hUpos (s : NNReal) (hs : s ∈ Icc (0 : NNReal) t) : 0 ≤ U s := by
    rcases eq_or_lt_of_le hs.1 with heq | hpos
    · rw [← heq]; exact hU0
    · exact (hUp s hpos).le
  have hsub : C ⊆ H := by
    rintro z ⟨⟨s, hs, heq⟩, _⟩
    exact ⟨heq ▸ hUpos s hs, mem_univ _⟩
  have hUnique : UniqueDiffOn ℝ H := (uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ
  have hD : ContinuousOn D C :=
    ((hf.continuousOn_fderivWithin hUnique le_rfl).clm_apply continuousOn_const).mono hsub
  have hC : IsCompact C := (isCompact_Icc.image hULip.continuous).prod isCompact_Icc
  have hUC := Metric.uniformContinuousOn_iff.mp (hC.uniformContinuousOn_of_continuous hD)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨δ,hδ,hδb⟩ := hUC ε hε
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hR) δ hδ] with S hS u hu
  have hut : Real.toNNReal u ≤ t := by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal u hu.1.le]
    exact hu.2
  have huPos : 0 < Real.toNNReal u := by
    rw [← NNReal.coe_pos, Real.coe_toNNReal u hu.1.le]
    exact hu.1
  have hx : (U (Real.toNNReal u), X (Real.toNNReal u) omega) ∈ C :=
    ⟨⟨_, ⟨zero_le,hut⟩, rfl⟩, abs_le.mp (hB.2.2.1 _ hut)⟩
  have hy : (U (Real.toNNReal u), P S (Real.toNNReal u)) ∈ C :=
    ⟨⟨_, ⟨zero_le,hut⟩, rfl⟩, abs_le.mp ((hB.2.1 S _ hut).1)⟩
  have hd : dist (U (Real.toNNReal u), X (Real.toNNReal u) omega)
      (U (Real.toNNReal u), P S (Real.toNNReal u)) < δ := by
    rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
    exact hS _ ⟨zero_le,hut⟩
  have hh := hδb _ hx _ hy hd
  simpa only [D,H,
    Kyprianou.Ch04.bvFullFderivEqWithinPositiveV1
      f hf (U (Real.toNNReal u)) (X (Real.toNNReal u) omega)
      (hUp _ huPos),
    Kyprianou.Ch04.bvFullFderivEqWithinPositiveV1
      f hf (U (Real.toNNReal u)) (P S (Real.toNNReal u))
      (hUp _ huPos)] using hh
