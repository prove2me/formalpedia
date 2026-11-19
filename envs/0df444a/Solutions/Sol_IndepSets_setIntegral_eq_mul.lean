-- Prove2me | solution 1 for IndepSets.setIntegral_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T03:16:31.687905+00:00
-- url     : https://prove2.me/submissions/51dccf18-b186-4e6c-822a-81585a5ca295

import Definitions.Def_BrownianMotion_Auxiliary_MeasureTheory_F001


/-!
# Measure theory lemmas to be upstreamed to Mathlib
-/

@[expose] public section

open MeasureTheory WithLp

open scoped ENNReal NNReal ProbabilityTheory

                                     

namespace ProbabilityTheory

section iIndepFun

variable {ι : Type*} [Fintype ι] {Ω : ι → Type*} {mΩ : ∀ i, MeasurableSpace (Ω i)}
  {μ : (i : ι) → Measure (Ω i)}

variable [∀ i, IsProbabilityMeasure (μ i)]

end iIndepFun

section covariance

end covariance

end ProbabilityTheory

--generalizing `MeasureTheory.Measure.addHaar_ball_center`

open Metric

section covariance

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X Y Z : Ω → ℝ} (c : ℝ)

end ProbabilityTheory

open ProbabilityTheory MeasurableSpace


theorem _root_.solution {Ω 𝓧 : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧} [IsZeroOrProbabilityMeasure μ]
    {f : 𝓧 → ℝ} {A : Set Ω} (hA1 : IndepSets {A} {s | MeasurableSet[m𝓧.comap X] s} μ)
    (hX : Measurable X) (hA2 : MeasurableSet A)
    (hf : AEStronglyMeasurable f (μ.map X)) :
    ∫ ω in A, f (X ω) ∂μ = μ.real A * ∫ ω, f (X ω) ∂μ := by
  set g := hf.mk f with hgdef
  have hg : Measurable g := hf.stronglyMeasurable_mk.measurable
  have hfg : f =ᵐ[μ.map X] g := hf.ae_eq_mk
  have hcomp : (fun ω => f (X ω)) =ᵐ[μ] fun ω => g (X ω) := ae_of_ae_map hX.aemeasurable hfg
  rw [setIntegral_congr_ae₀ hA2.nullMeasurableSet (hcomp.mono fun ω h _ => h),
    integral_congr_ae hcomp]
  have hind : Indep (MeasurableSpace.generateFrom {A}) (m𝓧.comap X) μ :=
    IndepSets.indep (MeasurableSpace.generateFrom_le (by
        rintro s rfl; exact hA2))
      hX.comap_le (IsPiSystem.singleton A) (fun s hs t ht _ => @MeasurableSet.inter Ω (m𝓧.comap X) s t hs ht)
      rfl (@MeasurableSpace.generateFrom_measurableSet Ω (m𝓧.comap X)).symm hA1
  have hIF : IndepFun (A.indicator (1 : Ω → ℝ)) (fun ω => g (X ω)) μ := by
    rw [IndepFun_iff_Indep]
    refine indep_of_indep_of_le_right (indep_of_indep_of_le_left hind ?_) ?_
    · have hm : Measurable[MeasurableSpace.generateFrom {A}] (A.indicator (1 : Ω → ℝ)) := by
        refine Measurable.indicator ?_ (MeasurableSpace.measurableSet_generateFrom (Set.mem_singleton A))
        exact measurable_const
      exact hm.comap_le
    · exact (hg.comp (Measurable.of_comap_le le_rfl)).comap_le
  have h1 : ∫ ω in A, g (X ω) ∂μ = ∫ ω, A.indicator (1 : Ω → ℝ) ω * g (X ω) ∂μ := by
    rw [← integral_indicator hA2]
    congr 1
    funext ω
    by_cases h : ω ∈ A <;> simp [Set.indicator, h]
  rw [h1, hIF.integral_fun_mul_eq_mul_integral
    ((measurable_const.indicator hA2).aestronglyMeasurable)
    ((hg.comp hX).aestronglyMeasurable), integral_indicator_one hA2]

