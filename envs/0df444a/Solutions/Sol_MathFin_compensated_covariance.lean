-- Prove2me | solution 1 for MathFin.compensated_covariance
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T07:05:32.352246+00:00
-- url     : https://prove2.me/submissions/0bca65ee-d5ee-422c-8459-c7d6ddbfb210

import Definitions.Def_MathFin_Foundations_PoissonCompensatedBilinear_F000
import Definitions.Def_SourceProof_09a1d2ad90db017031836da3

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

theorem _root_.solution (N : PoissonRandomMeasure P ν) {C D : Set (ℝ × E)}
    (hC : MeasurableSet C) (hD : MeasurableSet D)
    (hCfin : referenceIntensity ν C ≠ ⊤) (hDfin : referenceIntensity ν D ≠ ⊤) :
    ∫ ω, N.compensated C ω * N.compensated D ω ∂P = (referenceIntensity ν (C ∩ D)).toReal := by
  set X := C \ D
  set Y := D \ C
  set Z := C ∩ D
  have hX : MeasurableSet X := hC.diff hD
  have hY : MeasurableSet Y := hD.diff hC
  have hZ : MeasurableSet Z := hC.inter hD
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
  have mX := Prove2MeSourceProof.h_09a1d2ad90db017031836da3 N hX hXf
  have mY := Prove2MeSourceProof.h_09a1d2ad90db017031836da3 N hY hYf
  have mZ := Prove2MeSourceProof.h_09a1d2ad90db017031836da3 N hZ hZf
  have iXY : Integrable (fun ω => N.compensated X ω * N.compensated Y ω) P := mX.integrable_mul mY
  have iXZ : Integrable (fun ω => N.compensated X ω * N.compensated Z ω) P := mX.integrable_mul mZ
  have iZY : Integrable (fun ω => N.compensated Z ω * N.compensated Y ω) P := mZ.integrable_mul mY
  have iZZ : Integrable (fun ω => N.compensated Z ω * N.compensated Z ω) P := mZ.integrable_mul mZ
  have hcongr : ∫ ω, N.compensated C ω * N.compensated D ω ∂P
      = ∫ ω, (N.compensated X ω * N.compensated Y ω + N.compensated X ω * N.compensated Z ω)
          + (N.compensated Z ω * N.compensated Y ω + N.compensated Z ω * N.compensated Z ω) ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [aC, aD] with ω h1 h2
    rw [h1, h2]; ring
  rw [hcongr, integral_add
      (f := fun ω => N.compensated X ω * N.compensated Y ω + N.compensated X ω * N.compensated Z ω)
      (g := fun ω => N.compensated Z ω * N.compensated Y ω + N.compensated Z ω * N.compensated Z ω)
      (iXY.add iXZ) (iZY.add iZZ),
    integral_add (f := fun ω => N.compensated X ω * N.compensated Y ω)
      (g := fun ω => N.compensated X ω * N.compensated Z ω) iXY iXZ,
    integral_add (f := fun ω => N.compensated Z ω * N.compensated Y ω)
      (g := fun ω => N.compensated Z ω * N.compensated Z ω) iZY iZZ, compensated_mul_compensated_disjoint N hX hY dXY hYf,
    compensated_mul_compensated_disjoint N hX hZ dXZ hZf,
    compensated_mul_compensated_disjoint N hZ hY dYZ.symm hYf]
  have hsq := compensated_integral_sq N hZ hZf
  simp only [pow_two] at hsq
  rw [hsq]; ring

end MathFin
