-- Prove2me | solution 1 for Kyprianou.Ch04.boundedSupportedPhysicalPastMeasurableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T09:28:23.487984+00:00
-- url     : https://prove2.me/submissions/50cd1399-bfac-452d-a6f5-91d2e7b2d36d

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_predictableClampedPastKernelMeasurableV1
import Theorems.Thm_Kyprianou_Ch04_pointwiseFiniteKernelJointRealIntegralV1
import Theorems.Thm_Kyprianou_Ch04_finiteWindowRandomMeasureVersionV1
import Theorems.Thm_Kyprianou_Ch04_supportedPhysicalWindowClampV1
import Theorems.Thm_Kyprianou_Ch04_completedMeasAECongrV1
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Supported predictable physical integrals are measurable in the completed past. -/
theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (X : NNReal → Ω → ℝ) (F : Filtration NNReal mΩ)
    (hF : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F)
    (R : Ω → Measure (ℝ × ℝ)) (T : NNReal) (B : Set ℝ)
    (hB : MeasurableSet B)
    (hPast : ∀ S : Set (ℝ × ℝ), MeasurableSet S →
      S ⊆ Icc (0 : ℝ) (T : ℝ) ×ˢ B → Measurable[F T] (fun w => R w S))
    (hFin : ∀ᵐ w ∂P, R w (Icc (0 : ℝ) (T : ℝ) ×ˢ B) < ⊤)
    (g : (NNReal × Ω) × ℝ → ℝ)
    (hg : Measurable[F.predictable.prod inferInstance] g)
    (C : ℝ) (hC : ∀ p, ‖g p‖ ≤ C) (hs : ∀ p, p.2 ∉ B → g p = 0) :
    Measurable[F T] (fun w => ∫ z in Icc (0 : ℝ) (T : ℝ) ×ˢ univ,
      g ((z.1.toNNReal,w),z.2) ∂(R w)) := by
  let D := Icc (0 : ℝ) (T : ℝ) ×ˢ B
  have hD : MeasurableSet D := measurableSet_Icc.prod hB
  have hbad : MeasurableSet[F T] {w | ¬ R w D < ⊤} :=
    (measurableSet_lt (hPast D hD subset_rfl) measurable_const).compl
  have hFin' : ∀ᵐ w ∂P.trim (F.le T), R w D < ⊤ := by
    rw [ae_iff, trim_measurableSet_eq (F.le T) hbad]
    exact ae_iff.mp hFin
  letI : MeasurableSpace Ω := F T
  obtain ⟨S,hS,hSm,hEq⟩ :=
    Kyprianou.Ch04.finiteWindowRandomMeasureVersionV1 (P.trim (F.le T)) R D hD hPast hFin'
  let k := fun p : Ω × (ℝ × ℝ) => g ((min p.2.1.toNNReal T,p.1),p.2.2)
  have hk : Measurable k := @Kyprianou.Ch04.predictableClampedPastKernelMeasurableV1 Ω mΩ F T g hg
  have hV := Kyprianou.Ch04.pointwiseFiniteKernelJointRealIntegralV1 S hSm hS k hk C
    (fun p => hC _)
  apply @Kyprianou.Ch04.completedMeasAECongrV1 Ω ℝ mΩ inferInstance P X F hF T _ _ hV
  filter_upwards [ae_of_ae_trim (F.le T) hEq] with w hw
  rw [hw]
  exact Kyprianou.Ch04.supportedPhysicalWindowClampV1 (R w) T B hB g hs w
