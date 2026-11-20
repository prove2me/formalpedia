-- Prove2me | solution 1 for MathFin.memLp_adapted_mul_compensated
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T07:06:14.55889+00:00
-- url     : https://prove2.me/submissions/be7871dd-66f2-4004-a8df-94f07458494a

import Definitions.Def_MathFin_Foundations_PoissonCompensatedIsometryAdapted_F001
import Definitions.Def_SourceProof_09a1d2ad90db017031836da3

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

theorem _root_.solution (N : PoissonRandomMeasure P ν) {s t : ℝ}
    {A : Set E} (hA : MeasurableSet A) (hAfin : ν A ≠ ⊤)
    {φ : Ω → ℝ} (hφ : N.AdaptedAt s φ) (hφL2 : MemLp φ 2 P) :
    MemLp (fun ω => φ ω * N.compensated (Set.Ioc s t ×ˢ A) ω) 2 P := by
  have hbox : MeasurableSet (Set.Ioc s t ×ˢ A) := measurableSet_Ioc.prod hA
  have hfin : referenceIntensity ν (Set.Ioc s t ×ˢ A) ≠ ⊤ := by
    unfold referenceIntensity
    rw [Measure.prod_prod]
    refine ENNReal.mul_ne_top ?_ hAfin
    refine ne_top_of_le_ne_top ?_ (Measure.restrict_apply_le _ _)
    rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  have mÑ := Prove2MeSourceProof.h_09a1d2ad90db017031836da3 N hbox hfin
  have hI := adapted_indepFun_compensated (t := t) N hA hφ
  refine (memLp_two_iff_integrable_sq (hφL2.1.mul mÑ.1)).2 ?_
  have h2 := hI.comp (φ := fun x : ℝ => x ^ 2) (ψ := fun x : ℝ => x ^ 2)
    (measurable_id.pow_const 2) (measurable_id.pow_const 2)
  have := h2.integrable_mul hφL2.integrable_sq mÑ.integrable_sq
  refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp [Function.comp_def, mul_pow]

end MathFin
