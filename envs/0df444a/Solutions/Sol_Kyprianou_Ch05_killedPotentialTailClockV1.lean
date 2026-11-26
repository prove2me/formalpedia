-- Prove2me | solution 1 for Kyprianou.Ch05.killedPotentialTailClockV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T21:52:11.676082+00:00
-- url     : https://prove2.me/submissions/df28e649-2dd8-4fd7-81fe-12df702443db

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_ito43_levy_joint_version
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
import Theorems.Thm_Kyprianou_Ch05_killedPotential_lintegral_formula
import Theorems.Thm_Kyprianou_Ch05_killedPotentialSurvivalFactorGeneralV1
import Theorems.Thm_Kyprianou_Ch05_monotoneStrictPassageDiscountedTailV1
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_TailRatioClassL
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

open Set Topology Kyprianou.Ch05
open scoped Classical Topology
theorem solution
    {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → ℝ) (death : Omega → WithTop NNReal)
    (eta : ℝ) (hKilled : IsKilledSubordinator P Y death eta)
    (d : ℝ) (Pi : Measure ℝ) (Phi : ℝ → ℝ)
    (hTriplet : IsKilledLaplaceTriplet eta d Pi Phi)
    (hLaplaceLaw : ∀ t : NNReal, ∀ theta : ℝ, 0 ≤ theta →
      (∫ w, Real.exp (-theta*Y t w) ∂P) = Real.exp (-(t : ℝ)*(Phi theta-eta)))
    (U : ℝ → Measure ℝ) (hPotential : IsKilledPotentialFamily P Y death U)
    (heta : 0 < eta)
    (x : ℝ) (T : (NNReal → ℝ) → ENNReal) (hTm : Measurable T)
    (hT : ∀ f : NNReal → ℝ, Monotone f → f 0 = 0 →
      T f = sInf ((fun t : NNReal => (t : ENNReal)) '' {t : NNReal | 0 < t ∧ x < f t}))
    (hx : 0 ≤ x) :
    U 0 (Ioi x) = ∫⁻ w, if T (fun t => Y t w) ≠ ⊤ then
      ENNReal.ofReal (Real.exp (-eta*(T (fun t => Y t w)).toReal)/eta) else 0 ∂P := by
  classical
  obtain ⟨Y',hYm,hYe,_⟩ := Kyprianou.Ch04.ito43_levy_joint_version P Y hKilled.1.1
  let f : ℝ → ENNReal := (Ioi x).indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator measurableSet_Ioi
  let G (t : ℝ) (w : Omega) := ENNReal.ofReal (Real.exp (-eta*t)) * f (Y' t.toNNReal w)
  have hG : Measurable (Function.uncurry G) := by
    have hv : Measurable (fun p : ℝ × Omega => Y' p.1.toNNReal p.2) :=
      hYm.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
    exact (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_fst.const_mul (-eta)))).mul (hf.comp hv)
  calc
    U 0 (Ioi x) = ∫⁻ v, f v ∂(U 0) := (lintegral_indicator_fun_one measurableSet_Ioi).symm
    _ = ∫⁻ t in Ici (0 : ℝ), ENNReal.ofReal (Real.exp (-eta*t)) *
        (∫⁻ v, f v ∂(P.map (Y t.toNNReal))) ∂volume := by
      rw [killedPotential_lintegral_formula P Y death eta d Pi Phi hKilled hTriplet
        hLaplaceLaw U hPotential 0 le_rfl f hf]
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
      rw [killedPotentialSurvivalFactorGeneralV1 P Y death eta hKilled f hf t ht]
      simp
    _ = ∫⁻ t in Ici (0 : ℝ), ∫⁻ w, G t w ∂P ∂volume := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
      rw [lintegral_map' hf.aemeasurable
        (Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P Y hKilled.1.1 t.toNNReal)]
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr_ae
      filter_upwards [hYe] with w hw
      simp [G,hw]
    _ = ∫⁻ w, ∫⁻ t in Ici (0 : ℝ), G t w ∂volume ∂P :=
      lintegral_lintegral_swap hG.aemeasurable
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [hYe,hKilled.1.2] with w hw hm
      have he (t : ℝ) : G t w = if x < Y t.toNNReal w then
          ENNReal.ofReal (Real.exp (-eta*t)) else 0 := by
        simp [G,f,hw,Set.indicator_apply]
      simp_rw [he]
      exact monotoneStrictPassageDiscountedTailV1 (fun t => Y t w) hm x hx
        (congrFun hKilled.1.1.start_zero w) (T (fun t => Y t w))
        (hT _ hm (congrFun hKilled.1.1.start_zero w)) eta heta
