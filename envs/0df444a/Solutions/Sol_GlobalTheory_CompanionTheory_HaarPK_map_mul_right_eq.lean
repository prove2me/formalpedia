-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HaarPK.map_mul_right_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:34:38.154801+00:00
-- url     : https://prove2.me/submissions/22c7d143-bfad-4095-9663-2c1010de25d9

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_HaarProductClosedCompact
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HaarProductClosedCompactHolds
import Theorems.Thm_GlobalTheory_CompanionTheory_HaarPK_exists_eq_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology TopologicalSpace
open scoped ENNReal Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HaarPK
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
namespace GlobalTheory.CompanionTheory.HaarPK
theorem _root_.solution [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] (μ : Measure G)
    [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] (hμ : μ ≠ 0) (K : Subgroup G)
    (hK : IsCompact (K : Set G)) {k : G} (hk : k ∈ K) : μ.map (fun x => x * k) = μ := by
  obtain ⟨K₀⟩ : Nonempty (PositiveCompacts G) := inferInstance
  have h1 := Measure.haarMeasure_unique μ K₀
  have a0 : μ K₀ ≠ 0 := fun h => hμ (by rw [h1, h, zero_smul])
  haveI : IsFiniteMeasureOnCompacts (μ.map (fun x => x * k)) :=
    ⟨fun C hC => by
      rw [Measure.map_apply (measurable_mul_const k) hC.measurableSet]
      exact ((Homeomorph.mulRight k).isCompact_preimage.2 hC).measure_lt_top⟩
  have hne : μ.map (fun x => x * k) ≠ 0 := by
    rwa [Ne, Measure.map_eq_zero_iff (measurable_mul_const k).aemeasurable]
  obtain ⟨c, -, -, hc⟩ := exists_eq_smul (μ.map (fun x => x * k)) μ hne hμ
  have hC : IsCompact ((K₀ : Set G) * (K : Set G)) := K₀.isCompact.mul hK
  have hpre : (fun x => x * k) ⁻¹' ((K₀ : Set G) * (K : Set G)) = (K₀ : Set G) * (K : Set G) := by
    ext x
    constructor
    · rintro ⟨a, ha, b, hb, hab⟩
      exact ⟨a, ha, b * k⁻¹, K.mul_mem hb (K.inv_mem hk), by
        simp only at hab ⊢; rw [← mul_assoc, hab]; simp⟩
    · rintro ⟨a, ha, b, hb, hab⟩
      exact ⟨a, ha, b * k, K.mul_mem hb hk, by
        simp only at hab ⊢; rw [← mul_assoc, hab]⟩
  have h0 : μ ((K₀ : Set G) * (K : Set G)) ≠ 0 := fun h =>
    a0 (measure_mono_null (fun x hx => Set.mem_mul.2 ⟨x, hx, 1, K.one_mem, mul_one x⟩) h)
  have h2 := congrArg (fun m : Measure G => m ((K₀ : Set G) * (K : Set G))) hc
  simp only [Measure.smul_apply, smul_eq_mul] at h2
  rw [Measure.map_apply (measurable_mul_const k) hC.measurableSet, hpre] at h2
  have hc1 : c = 1 := by
    have := (ENNReal.mul_left_inj h0 hC.measure_lt_top.ne).1 ((one_mul _).trans h2)
    exact this.symm
  rw [hc, hc1, one_smul]
end GlobalTheory.CompanionTheory.HaarPK
