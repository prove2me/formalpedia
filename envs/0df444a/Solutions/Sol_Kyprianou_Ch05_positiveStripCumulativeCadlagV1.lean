-- Prove2me | solution 1 for Kyprianou.Ch05.positiveStripCumulativeCadlagV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:42:18.436935+00:00
-- url     : https://prove2.me/submissions/410fd04f-950e-4da3-9b2c-55bda7d0c711

import Mathlib
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
    (mu : Measure (ℝ × ℝ))
    (hfin : ∀ t : NNReal, (∫⁻ z in Ioc (0 : ℝ) (t : ℝ) ×ˢ Ioi (0 : ℝ),
      ENNReal.ofReal z.2 ∂mu) < ⊤) :
    let J := fun t : NNReal => (∫⁻ z in Ioc (0 : ℝ) (t : ℝ) ×ˢ Ioi (0 : ℝ),
      ENNReal.ofReal z.2 ∂mu).toReal
    Monotone J ∧ IsCadlag J := by
  dsimp only
  let nu := mu.withDensity (fun z => ENNReal.ofReal z.2)
  let R (t : NNReal) := Ioc (0 : ℝ) (t : ℝ) ×ˢ Ioi (0 : ℝ)
  have hm (t : NNReal) : MeasurableSet (R t) := measurableSet_Ioc.prod measurableSet_Ioi
  have he (t : NNReal) : nu (R t) = ∫⁻ z in R t, ENNReal.ofReal z.2 ∂mu :=
    withDensity_apply _ (hm t)
  have hf (t : NNReal) : nu (R t) ≠ ⊤ := by rw [he]; exact (hfin t).ne
  have hmono : Monotone R := fun a b hab z hz =>
    ⟨⟨hz.1.1,hz.1.2.trans (by exact_mod_cast hab)⟩,hz.2⟩
  let J : NNReal → ℝ := fun t => (nu (R t)).toReal
  have hJ : Monotone J := fun a b hab => ENNReal.toReal_mono (hf b) (measure_mono (hmono hab))
  have hright (t : NNReal) : ContinuousWithinAt J (Ici t) t := by
    rw [← continuousWithinAt_Ioi_iff_Ici]
    have hR : (⋂ r > t, R r) = R t := by
      ext z
      constructor
      · intro hz
        have hh := mem_iInter.mp hz (t+1)
        have hj := mem_iInter.mp hh (by simp : t < t+1)
        refine ⟨⟨hj.1.1,?_⟩,hj.2⟩
        by_contra! hlt
        let r := Real.toNNReal (((t : ℝ)+z.1)/2)
        have hr : (r : ℝ) = ((t : ℝ)+z.1)/2 := Real.coe_toNNReal _ (by linarith [t.coe_nonneg])
        have htr : t < r := by exact_mod_cast (show (t : ℝ) < (r : ℝ) by rw [hr]; linarith)
        have hk := mem_iInter.mp (mem_iInter.mp hz r) htr
        linarith [hk.1.2]
      · intro hz
        exact mem_iInter.mpr (fun r => mem_iInter.mpr (fun hr => hmono hr.le hz))
    have ht := tendsto_measure_biInter_gt (μ := nu) (a := t) (s := R)
      (fun r _ => (hm r).nullMeasurableSet)
      (fun i j _ hij => hmono hij) ⟨t+1,by simp,hf (t+1)⟩
    rw [hR] at ht
    exact (ENNReal.tendsto_toReal (hf t)).comp ht
  have hc : IsCadlag J := fun t => ⟨hright t,Function.leftLim J t,hJ.tendsto_leftLim t⟩
  simpa only [J,he] using And.intro hJ hc
