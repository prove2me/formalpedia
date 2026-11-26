-- Prove2me | solution 1 for MathlibGap.absolutelyContinuous_pi
-- status  : ACCEPTED   (prove)
-- author  : @domodus
-- created : 2026-11-26T14:54:42.810395+00:00
-- url     : https://prove2.me/submissions/709b1254-8da1-47a1-8a50-2c117a0cc933

import Mathlib
import Theorems.Thm_MeasureTheory_pi_withDensity

open MeasureTheory

/-- Radon-Nikodym writes each `μ i` as `ν i` with density `dμᵢ/dνᵢ`; the product of these
measures is `Measure.pi ν` with the product density (`MeasureTheory.pi_withDensity`), and a
measure with a density is absolutely continuous with respect to its base. -/
theorem solution {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] {μ ν : (i : ι) → Measure (α i)}
    [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)] (h : ∀ i, μ i ≪ ν i) :
    Measure.pi μ ≪ Measure.pi ν := by
  have hrn : ∀ i, (ν i).withDensity ((μ i).rnDeriv (ν i)) = μ i := fun i =>
    Measure.withDensity_rnDeriv_eq _ _ (h i)
  have : ∀ i, SigmaFinite ((ν i).withDensity ((μ i).rnDeriv (ν i))) := fun i => by
    rw [hrn i]; infer_instance
  have hpi : Measure.pi μ = (Measure.pi ν).withDensity
      (fun x => ∏ i, (μ i).rnDeriv (ν i) (x i)) := by
    rw [← MeasureTheory.pi_withDensity ν _ fun i => Measure.measurable_rnDeriv _ _]
    exact congrArg Measure.pi (funext fun i => (hrn i).symm)
  rw [hpi]
  exact withDensity_absolutelyContinuous _ _
