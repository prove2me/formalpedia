-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.DetScale.map_mulVec_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:52:05.104804+00:00
-- url     : https://prove2.me/submissions/6935ab5c-3c63-4dde-8e31-6ce1ceeb3b52

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HaarMapLinearScalingByDeterminant
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_DetScale_char_smul_map
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_DetScale_smul_map_pi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.DetScale
open Matrix
open scoped Pointwise
namespace GlobalTheory.CompanionTheory.SW.DetScale
theorem _root_.solution : ∀ (F : Type) [Field F] (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R]
    [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R] (ι : Type)
    [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F), A.det ≠ 0 → ∀ (lam : Measure R),
    lam.IsAddHaarMeasure → ∀ c : ℝ≥0, lam.map (fun x => algebraMap F R A.det * x) = c • lam →
    ∀ μ : Measure (ι → R), μ.IsAddHaarMeasure →
      μ.map (fun x => A.map (algebraMap F R) *ᵥ x) = c • μ := by
  intro F _ R _ _ _ _ _ _ _ _ _ ι _ _ A hA lam hlam c hc μ hμ
  have h1 := smul_map_pi lam A hA
  have h2 := char_smul_map lam (Units.map (algebraMap F R : F →* R) (Units.mk0 A.det hA))
  set d := distribHaarChar R (Units.map (algebraMap F R : F →* R) (Units.mk0 A.det hA))
  have h2' : d • lam.map (fun x => algebraMap F R A.det * x) = lam := h2
  rw [hc] at h2'
  obtain ⟨K, hKc, hK0⟩ : ∃ K : Set R, IsCompact K ∧ K ∈ 𝓝 (0 : R) := exists_compact_mem_nhds 0
  have hdc : d * c = 1 := by
    have h3 := congrArg (fun m : Measure R => m K) h2'
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h3
    rw [← mul_assoc, ← ENNReal.coe_mul] at h3
    have h4 : ((d * c : ℝ≥0) : ℝ≥0∞) = 1 :=
      (ENNReal.mul_left_inj (Measure.measure_pos_of_mem_nhds lam hK0).ne' hKc.measure_lt_top.ne).1
        (h3.trans (one_mul _).symm)
    exact_mod_cast h4
  have h4 : (Measure.pi fun _ : ι => lam).map (fun x => A.map (algebraMap F R) *ᵥ x) =
      c • Measure.pi fun _ : ι => lam := by
    conv_rhs => rw [← h1]
    rw [smul_smul, mul_comm c d, hdc, one_smul]
  obtain ⟨k, hk⟩ : ∃ k : ℝ≥0, μ = k • Measure.pi fun _ : ι => lam :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul_of_regular μ (Measure.pi fun _ : ι => lam)⟩
  rw [hk, Measure.map_smul, h4, smul_comm]
end GlobalTheory.CompanionTheory.SW.DetScale
