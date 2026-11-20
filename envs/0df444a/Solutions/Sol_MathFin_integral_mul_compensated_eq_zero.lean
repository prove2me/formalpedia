-- Prove2me | solution 1 for MathFin.integral_mul_compensated_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T07:03:54.328676+00:00
-- url     : https://prove2.me/submissions/d5589407-202d-4364-8525-b4f166f431af

import Definitions.Def_MathFin_Foundations_PoissonCompensatedIsometryAdapted_F000

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

theorem _root_.solution (N : PoissonRandomMeasure P ν) {D : Set (ℝ × E)}
    (hD : MeasurableSet D) (hfin : referenceIntensity ν D ≠ ⊤)
    {X : Ω → ℝ} (hX : Measurable[N.regionSigma D] X) :
    ∫ ω, X ω * N.compensated D ω ∂P = 0 := by
  have hle : N.regionSigma D ≤ (inferInstance : MeasurableSpace Ω) :=
    iSup₂_le fun _ hC => measurable_iff_comap_le.mp (N.measurable_eval hC.2)
  have hfield : Indep (N.regionSigma D)
      (MeasurableSpace.comap (fun ω => N.N ω D) inferInstance) P :=
    N.indep_of_disjoint_region hD
  have hraw : IndepFun X (fun ω => N.N ω D) P :=
    (IndepFun_iff_Indep _ _ _).mpr
      (indep_of_indep_of_le_left hfield (measurable_iff_comap_le.mp hX))
  have hcomp : IndepFun X (N.compensated D) P := by
    have := hraw.comp (φ := (id : ℝ → ℝ))
      (ψ := fun x : ℝ≥0∞ => x.toReal - (referenceIntensity ν D).toReal)
      measurable_id (measurable_id.ennreal_toReal.sub measurable_const)
    exact this
  have hm := hcomp.integral_mul_eq_mul_integral (hX.mono hle le_rfl).aestronglyMeasurable
    (N.measurable_compensated hD).aestronglyMeasurable
  rw [compensated_integral_zero N hD hfin, mul_zero] at hm
  exact hm

end MathFin
