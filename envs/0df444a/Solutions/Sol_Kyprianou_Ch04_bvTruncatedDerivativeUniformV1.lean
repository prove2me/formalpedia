-- Prove2me | solution 1 for Kyprianou.Ch04.bvTruncatedDerivativeUniformV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T00:42:33.082242+00:00
-- url     : https://prove2.me/submissions/a0b1bd7d-a15e-4ad8-ad2a-66ce14b97e94
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_bvTruncatedPathsUniformV1
import Theorems.Thm_Kyprianou_Ch04_bvTruncatedPathCompactBoundV1
import Theorems.Thm_Kyprianou_Ch04_bvFullFderivEqWithinPositiveV1
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Filter
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
    (t : NNReal) (v : ℝ × ℝ) :
    let j : Set.Ioc (0 : NNReal) t → ℝ := fun s => X s omega - Xleft s omega
    let P : Finset (Set.Ioc (0 : NNReal) t) → NNReal → ℝ :=
      fun S u => X 0 omega + c * (u : ℝ) + ∑ s ∈ S, if (s : NNReal) ≤ u then j s else 0
    TendstoUniformlyOn
      (fun S (u : ℝ) => fderiv ℝ f (u,P S (Real.toNNReal u)) v)
      (fun u : ℝ => fderiv ℝ f (u,X (Real.toNNReal u) omega) v)
      atTop (Set.Ioc (0 : ℝ) (t : ℝ)) := by
  classical
  intro j P
  let M := |X 0 omega| + |c| * (t : ℝ) + ∑' s, |j s|
  let H : Set (ℝ × ℝ) := Set.prod (Set.Ici (0 : ℝ)) Set.univ
  let K : Set (ℝ × ℝ) := Set.prod (Set.Icc 0 (t : ℝ)) (Set.Icc (-M) M)
  let D : ℝ × ℝ → ℝ := fun z => fderivWithin ℝ f H z v
  have hU := Kyprianou.Ch04.bvTruncatedPathsUniformV1 X Xleft omega c hRep hLeft t
  have hR : TendstoUniformlyOn P (fun u => X u omega) atTop (Set.Icc 0 t) := hU.1
  have hB := Kyprianou.Ch04.bvTruncatedPathCompactBoundV1 X Xleft omega c hRep hLeft t
  have hsub : K ⊆ H := fun z hz => ⟨hz.1.1, Set.mem_univ _⟩
  have hUnique : UniqueDiffOn ℝ H := (uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ
  have hD : ContinuousOn D K :=
    ((hf.continuousOn_fderivWithin hUnique le_rfl).clm_apply continuousOn_const).mono hsub
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hUC := Metric.uniformContinuousOn_iff.mp (hK.uniformContinuousOn_of_continuous hD)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨δ,hδ,hδb⟩ := hUC ε hε
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hR) δ hδ] with S hS u hu
  have hut : Real.toNNReal u ≤ t := by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal u hu.1.le]
    exact hu.2
  have hx : (u,X (Real.toNNReal u) omega) ∈ K :=
    ⟨⟨hu.1.le,hu.2⟩,abs_le.mp (hB.2.2.1 _ hut)⟩
  have hy : (u,P S (Real.toNNReal u)) ∈ K :=
    ⟨⟨hu.1.le,hu.2⟩,abs_le.mp ((hB.2.1 S _ hut).1)⟩
  have hd : dist (u,X (Real.toNNReal u) omega) (u,P S (Real.toNNReal u)) < δ := by
    rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
    exact hS _ ⟨zero_le,hut⟩
  have hh := hδb _ hx _ hy hd
  simpa only [D,H,
    Kyprianou.Ch04.bvFullFderivEqWithinPositiveV1 f hf u (X (Real.toNNReal u) omega) hu.1,
    Kyprianou.Ch04.bvFullFderivEqWithinPositiveV1 f hf u (P S (Real.toNNReal u)) hu.1] using hh
