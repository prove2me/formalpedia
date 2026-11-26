-- Prove2me | solution 1 for Kyprianou.Ch05.canonicalPositivePoissonStationaryIncrementsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:42:18.550324+00:00
-- url     : https://prove2.me/submissions/114e6348-69c8-4996-a619-b8d231afbbb7

import Mathlib
import Theorems.Thm_Kyprianou_Ch05_positivePoissonStripMeasurableAmbientV1
import Theorems.Thm_Kyprianou_Ch05_positivePoissonStripCharacteristicV1
import Theorems.Thm_Kyprianou_Ch05_positivePoissonPathIncrementStripV1
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Filter Set Complex Topology Kyprianou.Ch05
open scoped NNReal ENNReal Topology Classical
set_option autoImplicit false
theorem solution
    {Lambda : Type} [MeasurableSpace Lambda]
    (Q : Measure Lambda) [IsProbabilityMeasure Q]
    (Pi : Measure ℝ) [SigmaFinite Pi]
    (K : ℕ → Lambda → ℕ) (Z : ℕ → ℕ → Lambda → ℝ × ℝ)
    (hd : IsPoissonPointFamily K Z ((volume : Measure ℝ).prod Pi) Q)
    (hint : Integrable (fun z : ℝ => min (1 : ℝ) |z|) Pi)
    (d : ℝ) :
    HasStationaryIncrements (fun (t : NNReal) (w : Lambda) =>
      d * (t : ℝ) + (∫⁻ z in Ioc (0 : ℝ) (t : ℝ) ×ˢ Ioi (0 : ℝ),
        ENNReal.ofReal z.2 ∂(poissonRandomMeasure K Z w)).toReal) Q := by
  intro s h
  let G (a b : ℝ) (w : Lambda) := (∫⁻ z in Ioc a b ×ˢ Ioi (0 : ℝ),
    ENNReal.ofReal z.2 ∂(poissonRandomMeasure K Z w)).toReal
  have hm (a b : ℝ) : Measurable (G a b) :=
    positivePoissonStripMeasurableAmbientV1 Q Pi K Z hd hint a b
  have hi : IdentDistrib (G s (s+h : NNReal)) (G 0 h) Q Q := by
    refine ⟨(hm _ _).aemeasurable,(hm _ _).aemeasurable,?_⟩
    letI : IsProbabilityMeasure (Q.map (G s (s+h : NNReal))) :=
      Measure.isProbabilityMeasure_map (hm (s : ℝ) ((s+h : NNReal) : ℝ)).aemeasurable
    letI : IsProbabilityMeasure (Q.map (G 0 h)) :=
      Measure.isProbabilityMeasure_map (hm 0 (h : ℝ)).aemeasurable
    apply Measure.ext_of_charFun
    funext u
    change charFun (Q.map (G s (s+h : NNReal))) u = charFun (Q.map (G 0 h)) u
    dsimp only [G]
    rw [positivePoissonStripCharacteristicV1 Q Pi K Z hd hint _ _ u
      (by exact_mod_cast (le_add_of_nonneg_right (zero_le : 0 ≤ h) : s ≤ s+h)),
      positivePoissonStripCharacteristicV1 Q Pi K Z hd hint 0 _ u h.coe_nonneg]
    simp [NNReal.coe_add]
  have hj := hi.comp (u := fun y : ℝ => d*(h : ℝ)+y) (by fun_prop)
  have hAE := positivePoissonPathIncrementStripV1 Q Pi K Z hd hint d
  have ha : (fun w => d*(h : ℝ)+G s (s+h : NNReal) w) =ᵐ[Q]
      increment (fun (t : NNReal) (w : Lambda) =>
        d*(t : ℝ)+ (G 0 t w)) s (s+h) := by
    filter_upwards [hAE] with w hw
    have he := hw s (s+h) (le_add_of_nonneg_right (zero_le : 0 ≤ h))
    simpa [G,increment,NNReal.coe_add] using he.symm
  have hb : (fun w => d*(h : ℝ)+G 0 h w) =ᵐ[Q]
      increment (fun (t : NNReal) (w : Lambda) =>
        d*(t : ℝ)+ (G 0 t w)) 0 h := by
    filter_upwards [hAE] with w hw
    simpa [G,increment] using (hw 0 h zero_le).symm
  exact (IdentDistrib.of_ae_eq hj.aemeasurable_fst ha).symm.trans
    (hj.trans (IdentDistrib.of_ae_eq hj.aemeasurable_snd hb))
