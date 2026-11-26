-- Prove2me | solution 1 for Kyprianou.Ch05.positiveDiscountedKernelHorizonLimitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:27:47.595271+00:00
-- url     : https://prove2.me/submissions/2a072274-de53-482b-aecb-dd1b2dcaf049

import Mathlib
import Theorems.Thm_Kyprianou_Ch05_nonnegativeKernelHorizonExhaustionV1
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
    {Omega : Type} [MeasurableSpace Omega]
    (Q : Measure Omega) [IsProbabilityMeasure Q]
    (V X : NNReal → Omega → ℝ)
    (hV : Measurable (Function.uncurry V))
    (hX : ∀ t, Measurable (X t))
    (he : ∀ t : NNReal, 0 < t → V t =ᵐ[Q] X t)
    (f : ℝ → ENNReal) (hf : Measurable f) (eta : ℝ) :
    Tendsto (fun n : ℕ => ∫⁻ w, ∫⁻ t in Icc (0 : ℝ) (n : ℝ),
      if 0 < t then ENNReal.ofReal (Real.exp (-eta*t)) * f (V t.toNNReal w) else 0
        ∂volume ∂Q) atTop
      (nhds (∫⁻ t in Ici (0 : ℝ), ENNReal.ofReal (Real.exp (-eta*t)) *
        (∫⁻ v, f v ∂(Q.map (X t.toNNReal))) ∂volume)) := by
  classical
  let g (w : Omega) (t : ℝ) := if 0 < t then
    ENNReal.ofReal (Real.exp (-eta*t)) * f (V t.toNNReal w) else 0
  have hg : Measurable (Function.uncurry g) := by
    have hv : Measurable (fun p : Omega × ℝ => V p.2.toNNReal p.1) :=
      hV.comp ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst)
    exact Measurable.ite (measurableSet_lt measurable_const measurable_snd)
      ((ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
        (measurable_snd.const_mul (-eta)))).mul (hf.comp hv)) measurable_const
  have hS (n : ℕ) : MeasurableSet (Icc (0 : ℝ) (n : ℝ)) := measurableSet_Icc
  have hmono : Monotone (fun n : ℕ => Icc (0 : ℝ) (n : ℝ)) :=
    fun i j hij => Icc_subset_Icc_right (by exact_mod_cast hij)
  have hM (n : ℕ) : AEMeasurable (fun w => ∫⁻ t in Icc (0 : ℝ) (n : ℝ), g w t ∂volume) Q :=
    (hg.lintegral_prod_right (ν := volume.restrict (Icc (0 : ℝ) (n : ℝ)))).aemeasurable
  have h := nonnegativeKernelHorizonExhaustionV1 Q (fun _ => volume) g
    (fun w => hg.comp measurable_prodMk_left) _ hS hmono hM
  have hu : (⋃ n : ℕ, Icc (0 : ℝ) (n : ℝ)) = Ici 0 := by
    ext t
    constructor
    · intro ht
      obtain ⟨n,hn⟩ := mem_iUnion.mp ht
      exact hn.1
    · intro ht
      obtain ⟨n,hn⟩ := exists_nat_ge t
      exact mem_iUnion.mpr ⟨n,ht,hn⟩
  rw [hu,lintegral_lintegral_swap hg.aemeasurable] at h
  convert h using 2
  rw [Measure.restrict_congr_set (Ioi_ae_eq_Ici (μ := volume)).symm]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht' : 0 < t := ht
  have hp : 0 < t.toNNReal := Real.toNNReal_pos.mpr ht'
  change ENNReal.ofReal (Real.exp (-eta*t)) * (∫⁻ v, f v ∂Q.map (X t.toNNReal)) =
    ∫⁻ w, g w t ∂Q
  simp only [g,ht',if_true]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_map hf (hX _)]
  congr 1
  exact lintegral_congr_ae ((he _ hp).mono fun w hw => congrArg f hw.symm)
