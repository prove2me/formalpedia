-- Prove2me | solution 1 for GlobalTheory.JR.ResidueGauss.setIntegral_addChar_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:09:44.096824+00:00
-- url     : https://prove2.me/submissions/279e97a7-a7ca-4244-a6db-42cec4f21a7e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ResidueGaussIntegralNormForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.ResidueGauss
namespace GlobalTheory.JR.ResidueGauss
theorem _root_.solution {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure] (H : AddSubgroup G) (f : G → ℂ)
    (hf : ∀ x y, f (x + y) = f x * f y) (s₀ : G) (hs₀ : s₀ ∈ H) (hne : f s₀ ≠ 1) :
    ∫ x in (H : Set G), f x ∂μ = 0 := by
  have hmp : MeasurePreserving (fun x => s₀ + x) μ μ := measurePreserving_add_left μ s₀
  have hpre : (fun x => s₀ + x) ⁻¹' (H : Set G) = H := by
    ext x; simp [H.add_mem_cancel_left hs₀]
  have e := hmp.setIntegral_preimage_emb (measurableEmbedding_addLeft s₀) f H
  rw [hpre] at e
  simp_rw [hf s₀] at e
  rw [integral_const_mul] at e
  have h : (f s₀ - 1) * ∫ x in (H : Set G), f x ∂μ = 0 := by rw [sub_mul, e]; ring
  exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 hne)
end GlobalTheory.JR.ResidueGauss
