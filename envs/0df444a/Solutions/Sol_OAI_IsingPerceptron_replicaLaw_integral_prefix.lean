-- Prove2me | solution 1 for OAI.IsingPerceptron.replicaLaw_integral_prefix
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:12:35.1333+00:00
-- url     : https://prove2.me/submissions/ba366c40-974a-4082-8be1-99ad8e85ab03

import Mathlib
import Definitions.Def_OAIQ4Ip000

section
-- module Solutions.OAIQ258_II.IsingPerceptron_TiltedLabelLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tilted Label Law. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace IsingPerceptron

lemma replica_prefix_map {X : Type*} [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] (r : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => ν)).map (fun σ => fun i : Fin r => σ i) =
      Measure.pi (fun _ : Fin r => ν) := by
  have hi : iIndepFun (fun i : ℕ => fun σ : ℕ → X => σ i)
      (Measure.infinitePi (fun _ : ℕ => ν)) := iIndepFun_infinitePi (fun _ => measurable_id)
  have he := (hi.precomp (fun {i j : Fin r} h => Fin.val_injective h)).map_fun_eq_pi_map
    (fun _ => (by fun_prop : Measurable _).aemeasurable)
  simpa only [Measure.infinitePi_map_eval] using he

lemma replicaLaw_integral_bounded {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    {F : (ℕ → X) → ℝ} (hF : Measurable F) {C : ℝ} (hC : ∀ σ, |F σ| ≤ C) :
    (∫ σ, F σ ∂replicaLaw P ν hν) =
      ∫ ω, ∫ σ, F σ ∂Measure.infinitePi (fun _ : ℕ => ν ω) ∂P := by
  have hi : Integrable F (replicaLaw P ν hν) := (integrable_const C).mono'
    hF.aestronglyMeasurable (ae_of_all _ (fun σ => by simpa only [Real.norm_eq_abs] using hC σ))
  unfold replicaLaw at hi ⊢
  rw [Measure.comp_eq_comp_const_apply] at hi ⊢
  calc
    _ = ∫ ω, ∫ σ, F σ ∂(replicaKernel ν hν) ω ∂P := by
      simpa only [Kernel.const_apply] using Kernel.integral_comp hi
    _ = _ := rfl

lemma replicaLaw_integral_prefix_oai {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    {r : ℕ} (D : (Fin r → X) → ℝ) {C : ℝ} (hD : ∀ σ, |D σ| ≤ C) :
    (∫ σ, D (fun i : Fin r => σ i) ∂replicaLaw P ν hν) =
      ∫ ω, ∫ σ, D σ ∂Measure.pi (fun _ : Fin r => ν ω) ∂P := by
  rw [replicaLaw_integral_bounded P ν hν (F := fun σ => D (fun i : Fin r => σ i))
    ((measurable_of_countable D).comp (by fun_prop)) (fun _ => hD _)]
  apply integral_congr_ae
  exact ae_of_all _ (fun ω => ((HasLaw.mk
    ((Measurable.of_eval (fun i : Fin r => measurable_pi_apply (i : ℕ))).aemeasurable)
    (replica_prefix_map (ν ω) r)).integral_comp (measurable_of_countable D).aestronglyMeasurable))

end IsingPerceptron

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.IsingPerceptron.replicaLaw_integral_prefix_oai.{u_1, u_2} := @OAI.IsingPerceptron.replicaLaw_integral_prefix_oai.{u_1, u_2}
