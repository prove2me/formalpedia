-- Prove2me | solution 1 for Kyprianou.Ch04.exercise42LipschitzTruncatedFderivIntegralLimitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:25:22.960796+00:00
-- url     : https://prove2.me/submissions/9a43b580-12c2-40c8-90a3-1187bb1edf0d

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_bvNNRealFiniteAffineRightCoercionV1
import Theorems.Thm_Kyprianou_Ch04_exercise42LipschitzFiniteJumpFderivIntegrableV1
import Theorems.Thm_Kyprianou_Ch04_exercise42LipschitzTruncatedDerivativeUniformV1
import Theorems.Thm_Kyprianou_Ch04_bvUniformSetIntegralLimitV1
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false
open Kyprianou.Ch04

/-- The directional fderiv integral along a finite truncation converges to
the corresponding integral along the original bounded-variation path. -/
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
    Tendsto (fun S => ∫ u in Icc (0 : ℝ) (t : ℝ),
      fderiv ℝ f (U (Real.toNNReal u), P S (Real.toNNReal u)) v ∂volume) atTop
      (nhds (∫ u in Icc (0 : ℝ) (t : ℝ),
        fderiv ℝ f (U (Real.toNNReal u), X (Real.toNNReal u) omega) v ∂volume)) := by
  classical
  intro j P
  let I := Ioc (0 : NNReal) t
  let τ : I → ℝ := fun s => ((s : NNReal) : ℝ)
  have hτ : StrictMono τ := fun i j hij => hij
  let R (S : Finset I) (u : ℝ) :=
    X 0 omega + c * u + ∑ s ∈ S, if τ s ≤ u then j s else 0
  let Ureal : ℝ → ℝ := fun u => U u.toNNReal
  have hUrLip : LipschitzWith K Ureal := by
    simpa only [Ureal, Function.comp_def, mul_one] using
      hULip.comp Real.lipschitzWith_toNNReal
  have hUnonneg (u : ℝ) (hu : u ∈ Icc (0 : ℝ) (t : ℝ)) : 0 ≤ Ureal u := by
    by_cases hz : u = 0
    · simpa [hz, Ureal] using hU0
    · have hpos : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hz)
      exact (hUp u.toNNReal (by
        rw [← NNReal.coe_pos, Real.coe_toNNReal u hpos.le]; exact hpos)).le
  have hUpos (u : ℝ) (hu : u ∈ Ioc (0 : ℝ) (t : ℝ)) : 0 < Ureal u := by
    exact hUp u.toNNReal (by
      rw [← NNReal.coe_pos, Real.coe_toNNReal u hu.1.le]; exact hu.1)
  let F (S : Finset I) (u : ℝ) :=
    fderiv ℝ f (Ureal u,P S (Real.toNNReal u)) v
  let g (u : ℝ) := fderiv ℝ f (Ureal u,X (Real.toNNReal u) omega) v
  have hF (S : Finset I) : IntegrableOn (F S) (Ioc (0 : ℝ) (t : ℝ)) volume := by
    have hi := Kyprianou.Ch04.exercise42LipschitzFiniteJumpFderivIntegrableV1
      τ hτ j (X 0 omega) c Ureal K hUrLip f hf v
      S (t : ℝ) t.coe_nonneg
      (fun s _ => s.property.1) (fun s _ => s.property.2)
      (fun u hu => hUnonneg u hu) (fun u hu => hUpos u hu)
    change IntervalIntegrable (fun u => fderiv ℝ f (Ureal u,R S u) v)
      volume 0 (t : ℝ) at hi
    apply hi.1.congr_fun _ measurableSet_Ioc
    intro u hu
    have hR : R S u = P S (Real.toNNReal u) :=
      Kyprianou.Ch04.bvNNRealFiniteAffineRightCoercionV1
        (fun s : I => (s : NNReal)) j (X 0 omega) c S u hu.1.le
    change fderiv ℝ f (Ureal u,R S u) v =
      fderiv ℝ f (Ureal u,P S (Real.toNNReal u)) v
    rw [hR]
  have hUni : TendstoUniformlyOn F g atTop (Ioc (0 : ℝ) (t : ℝ)) :=
    Kyprianou.Ch04.exercise42LipschitzTruncatedDerivativeUniformV1
      X Xleft omega c hRep hLeft U K hULip hU0 hUp f hf t v
  have hm : volume (Ioc (0 : ℝ) (t : ℝ)) < ⊤ :=
    (measure_mono Ioc_subset_Icc_self).trans_lt (isCompact_Icc.measure_lt_top)
  simp only [integral_Icc_eq_integral_Ioc]
  exact Kyprianou.Ch04.bvUniformSetIntegralLimitV1 atTop volume _
    measurableSet_Ioc hm F g hF hUni
