-- Prove2me | solution 1 for Kyprianou.Ch04.bvFiniteJumpTruncationLimitV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T00:38:11.404698+00:00
-- url     : https://prove2.me/submissions/98f0dd5a-c5da-40c5-802c-82f86f749f1a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_bvTruncationDerivativeIntegralLimitV1
import Theorems.Thm_Kyprianou_Ch04_bvTruncationJumpLedgerLimitV1
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (X Xleft : NNReal → Omega → Real) (omega : Omega) (c : Real)
    (hCadlag : IsCadlag (fun t : NNReal => X t omega))
    (hLeft : forall t : NNReal, 0 < t →
      Tendsto (fun s : NNReal => X s omega)
        (nhdsWithin t (Set.Iio t)) (nhds (Xleft t omega)))
    (hRep : forall t : NNReal,
      Summable (fun s : Set.Ioc (0 : NNReal) t => |X s omega - Xleft s omega|) ∧
      X t omega = X 0 omega + c * (t : Real) +
        ∑' s : Set.Ioc (0 : NNReal) t, (X s omega - Xleft s omega))
    (f : Real × Real → Real)
    (hf : ContDiffOn Real 1 f (Set.prod (Set.Ici (0 : Real)) Set.univ))
    (t : NNReal) :
    let jump : Set.Ioc (0 : NNReal) t → Real :=
      fun s => X s omega - Xleft s omega
    let approx : Finset (Set.Ioc (0 : NNReal) t) → NNReal → Real :=
      fun S u => X 0 omega + c * (u : Real) +
        ∑ s ∈ S, if (s : NNReal) ≤ u then jump s else 0
    let before : Finset (Set.Ioc (0 : NNReal) t) → NNReal → Real :=
      fun S u => X 0 omega + c * (u : Real) +
        ∑ s ∈ S, if (s : NNReal) < u then jump s else 0
    let A : Finset (Set.Ioc (0 : NNReal) t) → Real :=
      fun S => f (0, X 0 omega) +
        (∫ u in Set.Icc (0 : Real) (t : Real),
          fderiv Real f (u, approx S (Real.toNNReal u)) (1, 0) ∂volume) +
        c * (∫ u in Set.Icc (0 : Real) (t : Real),
          fderiv Real f (u, approx S (Real.toNNReal u)) (0, 1) ∂volume) +
        ∑ s ∈ S, (f (((s : NNReal) : Real), approx S s) -
          f (((s : NNReal) : Real), before S s))
    Tendsto (fun S => f ((t : Real), approx S t)) atTop (nhds (f ((t : Real), X t omega))) ∧
    Tendsto A atTop (nhds (
                f (0, X 0 omega) +
        (∫ s in Set.Icc (0 : Real) (t : Real),
          fderiv Real f (s, X (Real.toNNReal s) omega)
            (1, 0) ∂volume) +
        c *
          (∫ s in Set.Icc (0 : Real) (t : Real),
            fderiv Real f (s, X (Real.toNNReal s) omega)
              (0, 1) ∂volume) +
        (∑' s : Set.Ioc (0 : NNReal) t,
          (f (((s : NNReal) : Real), X s omega) -
            f (((s : NNReal) : Real), Xleft s omega))))) := by
  classical
  dsimp only
  constructor
  · have hj : Summable (fun s : Set.Ioc (0 : NNReal) t =>
        X s omega - Xleft s omega) :=
      Summable.of_norm (by simpa only [Real.norm_eq_abs] using (hRep t).1)
    have hs : Tendsto (fun S : Finset (Set.Ioc (0 : NNReal) t) =>
        ∑ s ∈ S, (X s omega - Xleft s omega)) atTop
        (nhds (∑' s : Set.Ioc (0 : NNReal) t, (X s omega - Xleft s omega))) :=
      hj.hasSum
    have ht : Tendsto (fun S : Finset (Set.Ioc (0 : NNReal) t) =>
        X 0 omega + c * (t : Real) + ∑ s ∈ S, (X s omega - Xleft s omega))
        atTop (nhds (X t omega)) := by
      have h := (tendsto_const_nhds (x := X 0 omega + c * (t : Real))).add hs
      simpa only [← (hRep t).2] using h
    have hc : Continuous (fun x : Real => f ((t : Real), x)) :=
      hf.continuousOn.comp_continuous (Continuous.prodMk_right (t : Real))
        (fun x => ⟨NNReal.coe_nonneg t, Set.mem_univ x⟩)
    have hcut (s : Set.Ioc (0 : NNReal) t) : (s : NNReal) ≤ t := s.property.2
    simpa only [hcut, if_true, Function.comp_def] using hc.continuousAt.tendsto.comp ht
  · have h1 := Kyprianou.Ch04.bvTruncationDerivativeIntegralLimitV1
      X Xleft omega c hCadlag hLeft hRep f hf t (1, 0)
    have h2 := Kyprianou.Ch04.bvTruncationDerivativeIntegralLimitV1
      X Xleft omega c hCadlag hLeft hRep f hf t (0, 1)
    have hJ := Kyprianou.Ch04.bvTruncationJumpLedgerLimitV1
      X Xleft omega c hCadlag hLeft hRep f hf t
    exact ((tendsto_const_nhds.add h1).add (tendsto_const_nhds.mul h2)).add hJ
