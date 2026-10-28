-- Prove2me | solution 1 for NegativeDP.OptEq.lemma71
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T12:52:06.985926+00:00
-- url     : https://prove2.me/submissions/cd0cb931-8a72-4b8c-9bcd-41bef730bb4e

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Model
import Definitions.Def_DiscountedDP_Stationary_Return
import Definitions.Def_DiscountedDP_Stationary_Operators
import Definitions.Def_NegativeDP_OptEq_Model
import Definitions.Def_NegativeDP_OptEq_Futures
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open DiscountedDP.Stationary (Hist Plan MarkovPlan stationary IsGenerated IsGeneratedPlan)

open NegativeDP.OptEq in
theorem solution {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A] :
    (∀ u : S × Futures S A → ℝ, Measurable u → (∃ C : ℝ, ∀ x, |u x| ≤ C) →
      Measurable (fun p : S × {ν : Measure (Futures S A) // IsProbabilityMeasure ν} =>
        ∫ x, u (p.1, x) ∂(p.2 : Measure (Futures S A)))) ∧
    (∀ u : S × Futures S A → EReal, Measurable u → (∀ x, 0 ≤ u x) →
      Measurable (fun p : S × {ν : Measure (Futures S A) // IsProbabilityMeasure ν} =>
        ∫⁻ x, (u (p.1, x)).toENNReal ∂(p.2 : Measure (Futures S A)))) ∧
    (∀ u : S × Futures S A → EReal, Measurable u → (∀ x, u x ≤ 0) →
      Measurable (fun p : S × {ν : Measure (Futures S A) // IsProbabilityMeasure ν} =>
        -(((∫⁻ x, (-(u (p.1, x))).toENNReal ∂(p.2 : Measure (Futures S A))) : ℝ≥0∞) :
          EReal))) := by
  let κ : Kernel (S × {ν : Measure (Futures S A) // IsProbabilityMeasure ν}) (Futures S A) :=
    ⟨fun p => (p.2 : Measure (Futures S A)), measurable_subtype_coe.comp measurable_snd⟩
  haveI : IsMarkovKernel κ := ⟨fun p => p.2.2⟩
  have hκ : ∀ p, κ p = (p.2 : Measure (Futures S A)) := fun p => rfl
  refine ⟨?_, ?_, ?_⟩
  · intro u hu _
    have hf : StronglyMeasurable
        (fun q : (S × {ν : Measure (Futures S A) // IsProbabilityMeasure ν}) × Futures S A =>
          u (q.1.1, q.2)) :=
      (hu.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).stronglyMeasurable
    exact (hf.integral_kernel_prod_right' (κ := κ)).measurable
  · intro u hu _
    have hf : Measurable
        (fun q : (S × {ν : Measure (Futures S A) // IsProbabilityMeasure ν}) × Futures S A =>
          (u (q.1.1, q.2)).toENNReal) :=
      (hu.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).ereal_toENNReal
    exact hf.lintegral_kernel_prod_right' (κ := κ)
  · intro u hu _
    have hf : Measurable
        (fun q : (S × {ν : Measure (Futures S A) // IsProbabilityMeasure ν}) × Futures S A =>
          (-(u (q.1.1, q.2))).toENNReal) :=
      (continuous_neg.measurable.comp
        (hu.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))).ereal_toENNReal
    have h2 := hf.lintegral_kernel_prod_right' (κ := κ)
    exact continuous_neg.measurable.comp (measurable_coe_ennreal_ereal.comp h2)
