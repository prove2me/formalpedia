-- Prove2me | solution 1 for Kyprianou.Ch05.positivePoissonPathIncrementStripV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:26:40.925648+00:00
-- url     : https://prove2.me/submissions/71f00d14-3627-47a9-b703-847491c24946

import Mathlib
import Theorems.Thm_Kyprianou_Ch05_positivePoissonAllTimeMassFiniteV1
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
    let X := fun (t : NNReal) (w : Lambda) =>
      d * (t : ℝ) + (∫⁻ z in Ioc (0 : ℝ) (t : ℝ) ×ˢ Ioi (0 : ℝ),
        ENNReal.ofReal z.2 ∂(poissonRandomMeasure K Z w)).toReal
    ∀ᵐ w ∂Q, ∀ s t : NNReal, s ≤ t →
      X t w - X s w = d * ((t : ℝ)-(s : ℝ)) +
        (∫⁻ z in Ioc (s : ℝ) (t : ℝ) ×ˢ Ioi (0 : ℝ),
          ENNReal.ofReal z.2 ∂(poissonRandomMeasure K Z w)).toReal := by
  dsimp only
  filter_upwards [positivePoissonAllTimeMassFiniteV1 Q Pi K Z hd hint] with w hw
  intro s t hst
  have hsr : (s : ℝ) ≤ (t : ℝ) := by exact_mod_cast hst
  let R (a b : ℝ) := Ioc a b ×ˢ Ioi (0 : ℝ)
  let M (a b : ℝ) := ∫⁻ z in R a b, ENNReal.ofReal z.2 ∂(poissonRandomMeasure K Z w)
  change d*(t : ℝ)+(M 0 t).toReal - (d*(s : ℝ)+(M 0 s).toReal) =
    d*((t : ℝ)-(s : ℝ))+(M s t).toReal
  have hdis : Disjoint (R 0 s) (R s t) := by
    apply Set.disjoint_left.2
    intro z ha hb
    exact (not_lt_of_ge ha.1.2) hb.1.1
  have hun : R 0 s ∪ R s t = R 0 t := by
    simp only [R,← union_prod,Ioc_union_Ioc_eq_Ioc s.coe_nonneg hsr]
  have hM : M 0 t = M 0 s + M s t := by
    dsimp [M]
    rw [← hun,lintegral_union (measurableSet_Ioc.prod measurableSet_Ioi) hdis]
  have hfin : M s t < ⊤ := (lintegral_mono_set
    (show R s t ⊆ R 0 t from fun z hz => ⟨⟨s.coe_nonneg.trans_lt hz.1.1,hz.1.2⟩,hz.2⟩)).trans_lt (hw t)
  rw [hM,ENNReal.toReal_add (hw s).ne hfin.ne]
  ring
