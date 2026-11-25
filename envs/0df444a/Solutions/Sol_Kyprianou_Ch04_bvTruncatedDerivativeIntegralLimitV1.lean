-- Prove2me | solution 1 for Kyprianou.Ch04.bvTruncatedDerivativeIntegralLimitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T00:36:11.517801+00:00
-- url     : https://prove2.me/submissions/4ea86105-2f0c-4cbc-bd00-886f56f49f0d

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_bvNNRealFiniteAffineRightCoercionV1
import Theorems.Thm_Kyprianou_Ch04_bvFiniteJumpDerivativeIntervalIntegrableV1
import Theorems.Thm_Kyprianou_Ch04_bvTruncatedDerivativeUniformV1
import Theorems.Thm_Kyprianou_Ch04_bvUniformSetIntegralLimitV1
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
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
    (t : NNReal) (v : ℝ × ℝ) :
    let j : Set.Ioc (0 : NNReal) t → ℝ := fun s => X s omega - Xleft s omega
    let P : Finset (Set.Ioc (0 : NNReal) t) → NNReal → ℝ :=
      fun S u => X 0 omega + c * (u : ℝ) + ∑ s ∈ S, if (s : NNReal) ≤ u then j s else 0
    Tendsto (fun S => ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
      fderiv ℝ f (u,P S (Real.toNNReal u)) v ∂volume) atTop
      (nhds (∫ u in Set.Icc (0 : ℝ) (t : ℝ),
        fderiv ℝ f (u,X (Real.toNNReal u) omega) v ∂volume)) := by
  classical
  intro j P
  let I := Set.Ioc (0 : NNReal) t
  let τ : I → ℝ := fun s => ((s : NNReal) : ℝ)
  have hτ : StrictMono τ := fun i j hij => hij
  let R (S : Finset I) (u : ℝ) :=
    X 0 omega + c * u + ∑ s ∈ S, if τ s ≤ u then j s else 0
  let F (S : Finset I) (u : ℝ) := fderiv ℝ f (u,P S (Real.toNNReal u)) v
  let g (u : ℝ) := fderiv ℝ f (u,X (Real.toNNReal u) omega) v
  have hF (S : Finset I) : IntegrableOn (F S) (Set.Ioc (0 : ℝ) (t : ℝ)) volume := by
    have hi := Kyprianou.Ch04.bvFiniteJumpDerivativeIntervalIntegrableV1
      τ hτ j (X 0 omega) c f hf v S (t : ℝ) t.coe_nonneg
      (fun s _ => s.property.1) (fun s _ => s.property.2)
    change IntervalIntegrable (fun u => fderiv ℝ f (u,R S u) v) volume 0 (t : ℝ) at hi
    apply hi.1.congr_fun _ measurableSet_Ioc
    intro u hu
    have hR : R S u = P S (Real.toNNReal u) :=
      Kyprianou.Ch04.bvNNRealFiniteAffineRightCoercionV1
        (fun s : I => (s : NNReal)) j (X 0 omega) c S u hu.1.le
    change fderiv ℝ f (u,R S u) v = fderiv ℝ f (u,P S (Real.toNNReal u)) v
    rw [hR]
  have hU : TendstoUniformlyOn F g atTop (Set.Ioc (0 : ℝ) (t : ℝ)) :=
    Kyprianou.Ch04.bvTruncatedDerivativeUniformV1 X Xleft omega c hRep hLeft f hf t v
  have hm : volume (Set.Ioc (0 : ℝ) (t : ℝ)) < ⊤ :=
    (measure_mono Set.Ioc_subset_Icc_self).trans_lt (isCompact_Icc.measure_lt_top)
  simp only [integral_Icc_eq_integral_Ioc]
  exact Kyprianou.Ch04.bvUniformSetIntegralLimitV1 atTop volume _ measurableSet_Ioc hm F g hF hU
