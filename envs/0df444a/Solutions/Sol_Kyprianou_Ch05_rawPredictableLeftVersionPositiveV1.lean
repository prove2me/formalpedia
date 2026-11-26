-- Prove2me | solution 1 for Kyprianou.Ch05.rawPredictableLeftVersionPositiveV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T19:58:56.844523+00:00
-- url     : https://prove2.me/submissions/cee30d7d-9f27-475f-9a8e-64a616e0ecfc

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_predictableENNGridSampling
import Theorems.Thm_Kyprianou_Ch04_predictableLeftGridClock
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
    {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega)
    (F : Filtration NNReal inferInstance) (X : NNReal → Omega → ℝ)
    (hX : Adapted F X)
    (hreg : ∀ᵐ w ∂P, Monotone (fun t => X t w) ∧ X 0 w = 0) :
    ∃ V : NNReal → Omega → ℝ, Measurable[F.predictable] (Function.uncurry V) ∧
      ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t → V t w = Function.leftLim (fun s => X s w) t := by
  classical
  obtain ⟨q,a,b,h0,hcell,hcover,hleft⟩ := Kyprianou.Ch04.predictableLeftGridClock
  let phi : ℝ → ℝ → Omega → ℝ := fun s _ w => X s.toNNReal w
  have hp (t : NNReal) : Measurable[(F t).prod inferInstance]
      (fun z : Omega × ℝ => phi (t : ℝ) z.2 z.1) := by
    simp only [phi,Real.toNNReal_coe]
    change @Measurable (Omega × ℝ) ℝ ((F t).prod inferInstance) inferInstance
      (fun z => X t z.1)
    exact (hX t).comp (@measurable_fst Omega ℝ (F t) inferInstance)
  let G (n : ℕ) (z : NNReal × Omega) := ENNReal.ofReal (X (q n z.1) z.2)
  have hG (n : ℕ) : Measurable[F.predictable] (G n) := by
    have hh := Kyprianou.Ch04.predictableENNGridSampling F phi hp (q n) (a n) (b n)
      (h0 n) (hcell n) (hcover n)
    have hm : @Measurable (NNReal × Omega) ((NNReal × Omega) × ℝ)
        F.predictable (F.predictable.prod inferInstance) (fun z => (z,(0 : ℝ))) :=
      @measurable_prodMk_right (NNReal × Omega) ℝ F.predictable inferInstance 0
    change @Measurable (NNReal × Omega) ENNReal F.predictable inferInstance
      (fun z => ENNReal.ofReal (X (q n z.1) z.2))
    have he := hh.comp hm
    simpa only [Function.comp_def,phi,Real.toNNReal_coe] using he
  let L (z : NNReal × Omega) := Filter.liminf (fun n => G n z) atTop
  have hL : Measurable[F.predictable] L := by
    change Measurable[F.predictable] (fun z => Filter.liminf (fun n => G n z) atTop)
    simp_rw [Filter.liminf_eq_iSup_iInf_of_nat]
    exact Measurable.iSup fun n => Measurable.iInf fun i => Measurable.iInf fun _ => hG i
  refine ⟨fun t w => (L (t,w)).toReal,ENNReal.measurable_toReal.comp hL,?_⟩
  filter_upwards [hreg] with w hw
  intro t ht
  have hq : Tendsto (fun n => q n t) atTop (nhdsWithin t (Iio t)) := by
    obtain ⟨h₁,h₂⟩ := tendsto_nhdsWithin_iff.mp (hleft t ht)
    refine tendsto_nhdsWithin_iff.mpr ⟨NNReal.tendsto_coe.mp h₁,?_⟩
    filter_upwards [h₂] with n hn
    exact_mod_cast hn
  have hnon : 0 ≤ Function.leftLim (fun s => X s w) t := by
    have h := hw.1.le_leftLim ht
    rwa [hw.2] at h
  have hlim := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    ((hw.1.tendsto_leftLim t).comp hq)
  have he : Tendsto (fun n => G n (t,w)) atTop
      (nhds (ENNReal.ofReal (Function.leftLim (fun s => X s w) t))) := hlim
  change (L (t,w)).toReal = _
  rw [show L (t,w) = ENNReal.ofReal (Function.leftLim (fun s => X s w) t)
      from he.liminf_eq,ENNReal.toReal_ofReal hnon]
