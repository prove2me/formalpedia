-- Prove2me | solution 1 for Matrix.UnitaryGroup.fsMeasure_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:58:42.234906+00:00
-- url     : https://prove2.me/submissions/c2ab1a57-91d3-49d6-8c84-f929b14dfc6f

module
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_FubiniStudy
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_UnitaryTransitive
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Topology.Instances.Matrix
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_FubiniStudyUnique
public import Theorems.Thm_Matrix_UnitaryGroup_haar_orbit_indicator_eq

set_option autoImplicit false
@[expose] public section
public section
open Matrix
open scoped LinearAlgebra.Projectivization
open Matrix Matrix.UnitaryGroup
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
namespace Matrix.UnitaryGroup
theorem _root_.solution
    (p₀ : ℙ ℂ (EuclideanSpace ℂ ι))
    (μ : MeasureTheory.Measure (ℙ ℂ (EuclideanSpace ℂ ι)))
    [MeasureTheory.IsProbabilityMeasure μ]
    (hμ_inv : ∀ U : Matrix.unitaryGroup ι ℂ,
       MeasureTheory.Measure.map (fun p => U • p) μ = μ) :
    μ = fsMeasure p₀ := by
  apply MeasureTheory.Measure.ext
  intro B hB
  -- Joint measurability of (U, p) ↦ U • p, from the joint continuity of the action.
  have h_smul_meas : Measurable
      (fun Up : Matrix.unitaryGroup ι ℂ
            × ℙ ℂ (EuclideanSpace ℂ ι) => Up.1 • Up.2) :=
    continuous_smul.measurable
  -- Measurability of the indicator function `B.indicator (fun _ => 1)`.
  have h_ind_meas :
      Measurable (B.indicator (fun _ : ℙ ℂ (EuclideanSpace ℂ ι) =>
                                  (1 : ENNReal))) :=
    measurable_const.indicator hB
  -- The integrand f(U, p) := B.indicator 1 (U • p) is measurable (joint).
  have h_indicator_meas : Measurable
      (fun Up : Matrix.unitaryGroup ι ℂ
            × ℙ ℂ (EuclideanSpace ℂ ι) =>
        B.indicator (fun _ => (1 : ENNReal)) (Up.1 • Up.2)) :=
    h_ind_meas.comp h_smul_meas
  -- Inner integral over μ, with U fixed: equals μ B by invariance.
  have h_inner_mu (U : Matrix.unitaryGroup ι ℂ) :
      ∫⁻ p, B.indicator (fun _ => (1 : ENNReal)) (U • p) ∂μ = μ B := by
    have hcont : Measurable (fun p : ℙ ℂ (EuclideanSpace ℂ ι) => U • p) :=
      (continuous_const_smul U).measurable
    rw [← MeasureTheory.lintegral_map h_ind_meas hcont, hμ_inv U,
        MeasureTheory.lintegral_indicator_const hB 1, one_mul]
  -- fsMeasure p₀ in terms of unitaryHaarProb (unfold the def).
  have h_fubini_def : fsMeasure p₀ B
      = unitaryHaarProb {U : Matrix.unitaryGroup ι ℂ | U • p₀ ∈ B} := by
    show (MeasureTheory.Measure.map (orbitMap p₀) unitaryHaarProb) B = _
    rw [MeasureTheory.Measure.map_apply (orbit_map_measurable p₀) hB]
    rfl
  -- Inner integral over λ, with p fixed: equals fsMeasure p₀ B by haar_orbit_indicator_eq.
  have h_inner_haar (p : ℙ ℂ (EuclideanSpace ℂ ι)) :
      ∫⁻ U : Matrix.unitaryGroup ι ℂ,
          B.indicator (fun _ => (1 : ENNReal)) (U • p) ∂unitaryHaarProb
        = fsMeasure p₀ B := by
    have hcont : Measurable (fun U : Matrix.unitaryGroup ι ℂ => U • p) :=
      (orbit_map_continuous p).measurable
    rw [← MeasureTheory.lintegral_map h_ind_meas hcont,
        MeasureTheory.lintegral_indicator_const hB 1, one_mul,
        MeasureTheory.Measure.map_apply hcont hB]
    show unitaryHaarProb {U | U • p ∈ B} = fsMeasure p₀ B
    rw [haar_orbit_indicator_eq hB p₀ p, h_fubini_def]
  -- λ univ = 1 (probability measure).
  have h_lam_univ : unitaryHaarProb
      (Set.univ : Set (Matrix.unitaryGroup ι ℂ)) = 1 :=
    MeasureTheory.measure_univ
  -- μ univ = 1 (probability measure).
  have h_mu_univ : μ (Set.univ : Set (ℙ ℂ (EuclideanSpace ℂ ι))) = 1 :=
    MeasureTheory.measure_univ
  -- Compose the chain via Fubini.
  calc μ B
      = ∫⁻ _ : Matrix.unitaryGroup ι ℂ, μ B ∂unitaryHaarProb := by
            rw [MeasureTheory.lintegral_const, h_lam_univ, mul_one]
    _ = ∫⁻ U, ∫⁻ p, B.indicator (fun _ => (1 : ENNReal)) (U • p) ∂μ
            ∂unitaryHaarProb := by
            congr 1 with U
            exact (h_inner_mu U).symm
    _ = ∫⁻ p, ∫⁻ U, B.indicator (fun _ => (1 : ENNReal)) (U • p) ∂unitaryHaarProb ∂μ :=
            MeasureTheory.lintegral_lintegral_swap h_indicator_meas.aemeasurable
    _ = ∫⁻ _ : ℙ ℂ (EuclideanSpace ℂ ι), fsMeasure p₀ B ∂μ := by
            congr 1 with p
            exact h_inner_haar p
    _ = fsMeasure p₀ B := by
            rw [MeasureTheory.lintegral_const, h_mu_univ, mul_one]
end Matrix.UnitaryGroup
