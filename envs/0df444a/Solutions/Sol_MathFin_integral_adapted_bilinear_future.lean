-- Prove2me | solution 1 for MathFin.integral_adapted_bilinear_future
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T07:07:44.664302+00:00
-- url     : https://prove2.me/submissions/5ccd875f-30fb-4116-8349-0c46dbbfef87

import Definitions.Def_MathFin_Foundations_PoissonCompensatedBilinear_F001
import Definitions.Def_MathFin_Foundations_PoissonCompensatedBilinear_F000

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

theorem AuxAbf.past_le (N : PoissonRandomMeasure P ν) {s : ℝ}
    {D : Set (ℝ × E)} (hD : D ⊆ Set.Ioi s ×ˢ Set.univ) :
    N.pastSigma s ≤ N.regionSigma D := by
  refine iSup₂_le fun C hC => le_iSup₂_of_le C ⟨?_, hC.2⟩ le_rfl
  refine Set.disjoint_of_subset hC.1 hD (Set.disjoint_left.mpr ?_)
  rintro ⟨x, e⟩ hx hxD
  exact absurd (Set.mem_Iic.mp (Set.mem_prod.mp hx).1)
    (not_le.mpr (Set.mem_Ioi.mp (Set.mem_prod.mp hxD).1))

theorem AuxAbf.comp_meas (N : PoissonRandomMeasure P ν) {X W : Set (ℝ × E)}
    (hX : MeasurableSet X) (hd : Disjoint X W) :
    Measurable[N.regionSigma W] (N.compensated X) := by
  show Measurable[N.regionSigma W] fun ω => (N.N ω X).toReal - (referenceIntensity ν X).toReal
  have hc : Measurable[N.regionSigma W] fun ω => N.N ω X :=
    (measurable_iff_comap_le.mpr le_rfl).mono (le_iSup₂_of_le X ⟨hd, hX⟩ le_rfl) le_rfl
  exact hc.ennreal_toReal.sub measurable_const

theorem AuxAbf.indep (N : PoissonRandomMeasure P ν) {W : Set (ℝ × E)} (hW : MeasurableSet W)
    {F : Ω → ℝ} (hF : Measurable[N.regionSigma W] F) : IndepFun F (N.compensated W) P := by
  have hfield : Indep (N.regionSigma W)
      (MeasurableSpace.comap (fun ω => N.N ω W) inferInstance) P :=
    N.indep_of_disjoint_region hW
  have hraw : IndepFun F (fun ω => N.N ω W) P :=
    (IndepFun_iff_Indep _ _ _).mpr
      (indep_of_indep_of_le_left hfield (measurable_iff_comap_le.mp hF))
  exact hraw.comp (φ := (id : ℝ → ℝ))
    (ψ := fun x : ℝ≥0∞ => x.toReal - (referenceIntensity ν W).toReal)
    measurable_id (measurable_id.ennreal_toReal.sub measurable_const)

theorem AuxAbf.le_amb (N : PoissonRandomMeasure P ν) (W : Set (ℝ × E)) :
    N.regionSigma W ≤ (inferInstance : MeasurableSpace Ω) :=
  iSup₂_le fun _ hC => measurable_iff_comap_le.mp (N.measurable_eval hC.2)

theorem AuxAbf.cross (N : PoissonRandomMeasure P ν) {W : Set (ℝ × E)} (hW : MeasurableSet W)
    (hWf : referenceIntensity ν W ≠ ⊤) {F : Ω → ℝ} (hF : Measurable[N.regionSigma W] F)
    (hFi : Integrable F P) :
    Integrable (fun ω => F ω * N.compensated W ω) P ∧
      ∫ ω, F ω * N.compensated W ω ∂P = 0 := by
  have hI := AuxAbf.indep N hW hF
  have mW := (Prove2MeSourceProof.h_09a1d2ad90db017031836da3 N hW hWf).integrable one_le_two
  refine ⟨hI.integrable_mul hFi mW, ?_⟩
  have hm := hI.integral_mul_eq_mul_integral hFi.aestronglyMeasurable mW.aestronglyMeasurable
  rw [compensated_integral_zero N hW hWf, mul_zero] at hm
  exact hm

theorem _root_.solution (N : PoissonRandomMeasure P ν) {s : ℝ}
    {C D : Set (ℝ × E)} (hCms : MeasurableSet C) (hDms : MeasurableSet D)
    (hCsub : C ⊆ Set.Ioi s ×ˢ Set.univ) (hDsub : D ⊆ Set.Ioi s ×ˢ Set.univ)
    (hCfin : referenceIntensity ν C ≠ ⊤) (hDfin : referenceIntensity ν D ≠ ⊤)
    {φ : Ω → ℝ} (hφ : N.AdaptedAt s φ) (hφint : Integrable φ P) :
    ∫ ω, φ ω * N.compensated C ω * N.compensated D ω ∂P
      = (∫ ω, φ ω ∂P) * (referenceIntensity ν (C ∩ D)).toReal := by
  set X := C \ D
  set Y := D \ C
  set Z := C ∩ D
  have hX : MeasurableSet X := hCms.diff hDms
  have hY : MeasurableSet Y := hDms.diff hCms
  have hZ : MeasurableSet Z := hCms.inter hDms
  have hXf : referenceIntensity ν X ≠ ⊤ := ne_top_of_le_ne_top hCfin (measure_mono Set.diff_subset)
  have hYf : referenceIntensity ν Y ≠ ⊤ := ne_top_of_le_ne_top hDfin (measure_mono Set.diff_subset)
  have hZf : referenceIntensity ν Z ≠ ⊤ :=
    ne_top_of_le_ne_top hCfin (measure_mono Set.inter_subset_left)
  have dXZ : Disjoint X Z := Set.disjoint_sdiff_left.mono_right Set.inter_subset_right
  have dYZ : Disjoint Y Z := Set.disjoint_sdiff_left.mono_right Set.inter_subset_left
  have dXY : Disjoint X Y := Set.disjoint_sdiff_left.mono_right Set.diff_subset
  have eC : C = X ∪ Z := (Set.diff_union_inter C D).symm
  have eD : D = Y ∪ Z := by
    show D = D \ C ∪ C ∩ D
    rw [Set.inter_comm]; exact (Set.diff_union_inter D C).symm
  have aC := compensated_add_of_disjoint N hX hZ dXZ hXf hZf
  have aD := compensated_add_of_disjoint N hY hZ dYZ hYf hZf
  rw [← eC] at aC
  rw [← eD] at aD
  have hYs : Y ⊆ Set.Ioi s ×ˢ Set.univ := Set.diff_subset.trans hDsub
  have hZs : Z ⊆ Set.Ioi s ×ˢ Set.univ := Set.inter_subset_right.trans hDsub
  have hφm : ∀ {W}, W ⊆ Set.Ioi s ×ˢ Set.univ → Measurable[N.regionSigma W] φ :=
    fun hW => (show Measurable[N.pastSigma s] φ from hφ).mono (AuxAbf.past_le N hW) le_rfl
  -- φ ÑX integrable, measurable for regionSigma Y and Z
  have iφX := (AuxAbf.cross N hX hXf (hφm (Set.diff_subset.trans hCsub)) hφint).1
  have iφZ := (AuxAbf.cross N hZ hZf (hφm hZs) hφint).1
  have t1 := AuxAbf.cross N hY hYf ((hφm hYs).mul (AuxAbf.comp_meas N hX dXY)) iφX
  have t2 := AuxAbf.cross N hZ hZf ((hφm hZs).mul (AuxAbf.comp_meas N hX dXZ)) iφX
  have t3 := AuxAbf.cross N hY hYf ((hφm hYs).mul (AuxAbf.comp_meas N hZ dYZ.symm)) iφZ
  -- square term
  have hI2 := (AuxAbf.indep N hZ (hφm hZs)).comp (φ := (id : ℝ → ℝ)) (ψ := fun x : ℝ => x ^ 2)
    measurable_id (measurable_id.pow_const 2)
  have mZ := (Prove2MeSourceProof.h_09a1d2ad90db017031836da3 N hZ hZf).integrable_sq
  have i4 := hI2.integrable_mul hφint mZ
  have v4 := hI2.integral_mul_eq_mul_integral hφint.aestronglyMeasurable mZ.aestronglyMeasurable
  simp only [Function.comp_def, id_eq] at i4 v4
  rw [compensated_integral_sq N hZ hZf] at v4
  have hcongr : ∫ ω, φ ω * N.compensated C ω * N.compensated D ω ∂P
      = ∫ ω, ((φ ω * N.compensated X ω * N.compensated Y ω
          + φ ω * N.compensated X ω * N.compensated Z ω)
          + (φ ω * N.compensated Z ω * N.compensated Y ω
          + φ ω * N.compensated Z ω ^ 2)) ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [aC, aD] with ω h1 h2
    rw [h1, h2]; ring
  have i4' : Integrable (fun ω => φ ω * N.compensated Z ω ^ 2) P := i4
  rw [hcongr, integral_add
      (f := fun ω => φ ω * N.compensated X ω * N.compensated Y ω
          + φ ω * N.compensated X ω * N.compensated Z ω)
      (g := fun ω => φ ω * N.compensated Z ω * N.compensated Y ω
          + φ ω * N.compensated Z ω ^ 2)
      (t1.1.add t2.1) (t3.1.add i4'),
    integral_add (f := fun ω => φ ω * N.compensated X ω * N.compensated Y ω)
      (g := fun ω => φ ω * N.compensated X ω * N.compensated Z ω) t1.1 t2.1,
    integral_add (f := fun ω => φ ω * N.compensated Z ω * N.compensated Y ω)
      (g := fun ω => φ ω * N.compensated Z ω ^ 2) t3.1 i4']
  have e1 : ∫ ω, φ ω * N.compensated X ω * N.compensated Y ω ∂P = 0 := t1.2
  have e2 : ∫ ω, φ ω * N.compensated X ω * N.compensated Z ω ∂P = 0 := t2.2
  have e3 : ∫ ω, φ ω * N.compensated Z ω * N.compensated Y ω ∂P = 0 := t3.2
  have e4 : ∫ ω, φ ω * N.compensated Z ω ^ 2 ∂P
      = (∫ ω, φ ω ∂P) * (referenceIntensity ν Z).toReal := v4
  rw [e1, e2, e3, e4]
  ring

end MathFin
