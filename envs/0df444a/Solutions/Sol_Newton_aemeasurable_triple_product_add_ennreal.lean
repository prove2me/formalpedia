-- Prove2me | solution 1 for Newton.aemeasurable_triple_product_add_ennreal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:31:51.880406+00:00
-- url     : https://prove2.me/submissions/005ab71d-ca1b-49d9-81ff-21435c571f99

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Definitions.Def_Newton_MeasureTheory_Integral_Tonelli

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
open Newton
variable {G : Type*} [MeasurableSpace G]
variable {μ : Measure G}
namespace Newton
theorem _root_.solution
    {G : Type*} [MeasurableSpace G] [AddCommGroup G] [TopologicalSpace G]
    [MeasurableAdd₂ G] {μ : Measure G} [μ.IsAddHaarMeasure] [SFinite μ] {f g φ : G → ℂ}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hφ : AEStronglyMeasurable φ μ) :
    AEMeasurable
      (fun zy : G × G => (‖g zy.2‖₊ : ℝ≥0∞) * ‖φ (zy.1 + zy.2)‖₊ * ‖f zy.1‖₊)
      (μ.prod μ) := by
  -- AEMeasurability follows from composition with quasi-measure-preserving maps
  have hf_nnnorm : AEMeasurable (fun x : G => (‖f x‖₊ : ℝ≥0∞)) μ := by
    simpa [enorm_eq_nnnorm] using hf.enorm
  have hg_nnnorm : AEMeasurable (fun x : G => (‖g x‖₊ : ℝ≥0∞)) μ := by
    simpa [enorm_eq_nnnorm] using hg.enorm
  have hφ_nnnorm : AEMeasurable (fun x : G => (‖φ x‖₊ : ℝ≥0∞)) μ := by
    simpa [enorm_eq_nnnorm] using hφ.enorm
  -- Compose with projection and addition maps
  have h_add_qmp :
      Measure.QuasiMeasurePreserving (fun p : G × G => p.1 + p.2) (μ.prod μ) μ := by
    have h_add_prod :
        MeasurePreserving (fun q : G × G => (q.1 + q.2, q.2)) (μ.prod μ) (μ.prod μ) :=
      measurePreserving_add_prod (μ := μ) (ν := μ)
    have h_fst_qmp :
        Measure.QuasiMeasurePreserving (fun q : G × G => q.1) (μ.prod μ) μ :=
      MeasureTheory.Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)
    exact h_fst_qmp.comp h_add_prod.quasiMeasurePreserving
  have hf_comp : AEMeasurable (fun p : G × G => (‖f p.1‖₊ : ℝ≥0∞)) (μ.prod μ) :=
    hf_nnnorm.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ))
  have hg_comp : AEMeasurable (fun p : G × G => (‖g p.2‖₊ : ℝ≥0∞)) (μ.prod μ) :=
    hg_nnnorm.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ))
  have hφ_comp : AEMeasurable (fun p : G × G => (‖φ (p.1 + p.2)‖₊ : ℝ≥0∞)) (μ.prod μ) :=
    hφ_nnnorm.comp_quasiMeasurePreserving h_add_qmp
  exact (hg_comp.mul hφ_comp).mul hf_comp
end Newton
