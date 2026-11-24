-- Prove2me | solution 1 for GlobalTheory.JR.ResidueGauss.setIntegral_comp_mul_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:09:44.721295+00:00
-- url     : https://prove2.me/submissions/8a49c463-de07-41e9-8a6c-cd49c219a169

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
theorem _root_.solution {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [T2Space R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R]
    (μ : Measure R) [μ.IsAddHaarMeasure] (S : Set R) (u v : R) (huv : u * v = 1) (h0 : μ S ≠ 0)
    (hT : μ S ≠ ⊤) (hu : ∀ y ∈ S, u * y ∈ S) (hv : ∀ y ∈ S, v * y ∈ S) (g : R → ℂ) :
    ∫ y in S, g (u * y) ∂μ = ∫ y in S, g y ∂μ := by
  have hU : IsUnit u := ⟨⟨u, v, huv, by rw [mul_comm]; exact huv⟩, rfl⟩
  set w : Rˣ := hU.unit with hw
  have hwv : (w : R) = u := IsUnit.unit_spec hU
  have hvu : v * u = 1 := by rw [mul_comm]; exact huv
  have hwS : w • S = S := by
    ext y
    simp only [Set.mem_smul_set, Units.smul_def, hwv, smul_eq_mul]
    constructor
    · rintro ⟨z, hz, rfl⟩; exact hu z hz
    · intro hy; exact ⟨v * y, hv y hy, by rw [← mul_assoc, huv, one_mul]⟩
  have hΔ : distribHaarChar R w = 1 := by
    apply distribHaarChar_eq_of_measure_smul_eq_mul h0 hT
    rw [hwS]; simp
  let e : R ≃ₜ R :=
    { toFun := fun y => u * y
      invFun := fun y => v * y
      left_inv := fun y => by simp only; rw [← mul_assoc, hvu, one_mul]
      right_inv := fun y => by simp only; rw [← mul_assoc, huv, one_mul]
      continuous_toFun := continuous_const.mul continuous_id
      continuous_invFun := continuous_const.mul continuous_id }
  have hemb : MeasurableEmbedding (fun y => u * y) := e.toMeasurableEquiv.measurableEmbedding
  have hmp : MeasurePreserving (fun y => u * y) μ μ := by
    refine ⟨hemb.measurable, ?_⟩
    ext T hT'
    rw [Measure.map_apply hemb.measurable hT']
    have : (fun y => u * y) ⁻¹' T = w⁻¹ • T := by
      ext y
      rw [Set.mem_inv_smul_set_iff, Units.smul_def, hwv]
      rfl
    rw [this, ← distribHaarChar_mul, map_inv, hΔ]
    simp
  have hpre : (fun y => u * y) ⁻¹' S = S := by
    ext y
    constructor
    · intro hy
      have := hv _ hy
      simp only at this
      rwa [← mul_assoc, hvu, one_mul] at this
    · intro hy; exact hu y hy
  have := hmp.setIntegral_preimage_emb hemb g S
  rwa [hpre] at this
end GlobalTheory.JR.ResidueGauss
