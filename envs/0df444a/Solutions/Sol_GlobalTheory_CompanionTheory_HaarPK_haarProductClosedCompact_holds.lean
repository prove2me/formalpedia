-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HaarPK.haarProductClosedCompact_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:09:37.986288+00:00
-- url     : https://prove2.me/submissions/6a79e21d-02b3-40fa-8565-f9e88a517bbb

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_HaarProductClosedCompact
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HaarProductClosedCompactHolds
import Theorems.Thm_GlobalTheory_CompanionTheory_HaarPK_map_mul_right_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_HaarPK_exists_lift
import Theorems.Thm_GlobalTheory_CompanionTheory_HaarPK_exists_eq_smul_subgroup

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
theorem _root_.solution : Formalism.D.haarProductClosedCompact := by
  intro G _ _ _ _ _ _ _ _ μ _ _ hμ P K hP hK hPK μP μK p1 p2 p3 p4 k1 k2 k3
  haveI : IsProbabilityMeasure μK := ⟨k1⟩
  obtain ⟨l, l1, l2, l3, l4⟩ := exists_lift μ P K hP hK hPK
  have l0 : l ≠ 0 := by
    intro h
    have := l4 (fun _ => 1) measurable_const (fun _ _ _ => rfl)
    rw [h] at this
    simp only [lintegral_zero_measure, lintegral_const, one_mul] at this
    exact hμ (Measure.measure_univ_eq_zero.1 this.symm)
  obtain ⟨c, c0, ct, hc⟩ := exists_eq_smul_subgroup P hP l μP l1 l2 l3 l0 p1 p2 p3 p4
  refine ⟨c, c0, ct, fun Φ hΦ => ?_⟩
  have hΦ2 : Measurable (fun z : G × G => Φ (z.1 * z.2)) := hΦ.comp measurable_mul
  have hφ : Measurable (fun x => ∫⁻ k, Φ (x * k) ∂μK) := hΦ2.lintegral_prod_right'
  have hinv : ∀ x, ∀ k ∈ K, ∫⁻ y, Φ (x * k * y) ∂μK = ∫⁻ y, Φ (x * y) ∂μK := by
    intro x k hk
    conv_rhs => rw [← k3 k hk]
    rw [lintegral_map (f := fun y => Φ (x * y)) (hΦ.comp (measurable_const_mul x)) (measurable_const_mul k)]
    simp [mul_assoc]
  have h1 := l4 _ hφ hinv
  rw [hc, lintegral_smul_measure, smul_eq_mul] at h1
  rw [h1, lintegral_lintegral_swap hΦ2.aemeasurable]
  have : ∀ᵐ k ∂μK, ∫⁻ x, Φ (x * k) ∂μ = ∫⁻ x, Φ x ∂μ := by
    filter_upwards [(mem_ae_iff.2 k2 : (K : Set G) ∈ ae μK)] with k hk
    conv_rhs => rw [← map_mul_right_eq μ hμ K hK hk]
    rw [lintegral_map hΦ (measurable_mul_const k)]
  rw [lintegral_congr_ae this]
  simp
end GlobalTheory.CompanionTheory.HaarPK
