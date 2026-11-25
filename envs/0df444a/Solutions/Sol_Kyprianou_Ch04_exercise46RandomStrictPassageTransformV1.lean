-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46RandomStrictPassageTransformV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:31:22.368002+00:00
-- url     : https://prove2.me/submissions/0dae32e5-be9f-4237-bb63-50a2c6329f6e

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise46StrictPassagePathKernelV1
import Theorems.Thm_Kyprianou_Ch04_exercise46IndependentPathKernelIntegralV1
import Theorems.Thm_Kyprianou_Ch04_exercise46KilledDiscountPropertiesV1
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Strict first passage at an independent positive random height. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G)
    (J : Omega → Real) (hJ : AEMeasurable J P)
    (hJPositive : ∀ᵐ w ∂P, 0 < J w)
    (hInd : IndepFun J (fun w : Omega => fun t : NNReal => L.X t w) P)
    (beta phi : Real) (hb : 0 ≤ beta)
    (hStrict : ∀ x : Real, 0 < x →
      (∫ w, if Kyprianou.Ch03.firstHittingTime L.X (Ioi x) w = ⊤
        then (0 : Real) else Real.exp (-beta *
          (((Kyprianou.Ch03.firstHittingTime L.X (Ioi x) w).untopD 0 : NNReal) : Real)) ∂P)
        = Real.exp (-phi * x)) :
    let S : Omega → WithTop NNReal := fun w =>
      Kyprianou.Ch03.firstHittingTime L.X (Ioi (J w)) w
    AEMeasurable S P ∧
      (∫ w, if S w = ⊤ then (0 : Real)
        else Real.exp (-beta * (((S w).untopD 0 : NNReal) : Real)) ∂P) =
      ∫ w, Real.exp (-phi * J w) ∂P := by
  dsimp only
  obtain ⟨K, hK, hKx⟩ := Kyprianou.Ch04.exercise46StrictPassagePathKernelV1 P G L
  let Z : Omega → (NNReal → Real) := fun w t => L.X t w
  let d : WithTop NNReal → Real := fun z =>
    if z = ⊤ then 0 else Real.exp (-beta * (((z.untopD 0 : NNReal) : Real)))
  let S : Omega → WithTop NNReal := fun w =>
    Kyprianou.Ch03.firstHittingTime L.X (Ioi (J w)) w
  obtain ⟨hd, hbnd, _⟩ := Kyprianou.Ch04.exercise46KilledDiscountPropertiesV1 beta hb
  have hZ : Measurable Z := measurable_pi_lambda _ fun t =>
    (chat04_levy_joint_time_state_measurable L).comp (measurable_const.prodMk measurable_id)
  have hEq : S =ᵐ[P] fun w => K (J w, Z w) :=
    hJPositive.mono fun w hw => (hKx (J w) hw w).symm
  refine ⟨(hK.comp_aemeasurable (hJ.prodMk hZ.aemeasurable)).congr hEq.symm, ?_⟩
  change (∫ w, d (S w) ∂P) = _
  have hBound (z : Real × (NNReal → Real)) : ‖d (K z)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ d (K z) from (hbnd (K z)).1)]
    exact (hbnd (K z)).2
  calc
    _ = ∫ w, d (K (J w, Z w)) ∂P := integral_congr_ae (hEq.fun_comp d)
    _ = ∫ y, (∫ w, d (K (y, Z w)) ∂P) ∂(P.map J) :=
      Kyprianou.Ch04.exercise46IndependentPathKernelIntegralV1
        P J hJ Z hZ.aemeasurable hInd (d ∘ K) (hd.comp hK) hBound
    _ = ∫ y, Real.exp (-phi * y) ∂(P.map J) := by
      apply integral_congr_ae
      filter_upwards [(ae_map_iff hJ measurableSet_Ioi).mpr hJPositive] with y hy
      simpa [d, Z, hKx y hy] using hStrict y hy
    _ = _ := integral_map hJ (by fun_prop)
