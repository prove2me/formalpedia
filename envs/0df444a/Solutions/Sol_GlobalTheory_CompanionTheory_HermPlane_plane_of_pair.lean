-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HermPlane.plane_of_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:55:11.006802+00:00
-- url     : https://prove2.me/submissions/3e81d83e-07fb-4a7d-bcde-171ac7f56e0f

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_PlaneOfHenselAndPairing
import Theorems.Thm_GlobalTheory_CompanionTheory_HermPlane_lat_smul
import Theorems.Thm_GlobalTheory_CompanionTheory_HermPlane_hyperbolic_partner

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HermPlane
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] [ProperSpace L] [CharZero L]
  {V : Type} [AddCommGroup V] [Module L V] [FiniteDimensional L V]
namespace GlobalTheory.CompanionTheory.HermPlane
theorem _root_.solution {s : L →+* L} (hs : IsInv s) {δ : L} (hδ : IsDelta s δ) {h : V → V → L}
    (hh : IsHerm s h) {Λ M : AddSubgroup V} (hΛ : IsMax h Λ) (hM : IsMax h M) {p : L} (hp0 : p ≠ 0)
    (hp1 : ‖p‖ < 1) {r : ℕ} (hrM : ∀ y ∈ Λ, p ^ r • y ∈ M) {e y : V} (heΛ : e ∈ Λ) (hyΛ : y ∈ Λ)
    (he : h e e = 0) (hey : ‖h e y‖ = ‖δ‖) (heM : (p ^ r)⁻¹ • e ∈ M) :
    ∃ (e f : V) (u : L), u ≠ 0 ∧ h e e = 0 ∧ h f f = 0 ∧ h e f = δ ∧
      e ∈ Λ ∧ f ∈ Λ ∧ u • e ∈ M ∧ (s u)⁻¹ • f ∈ M := by
  obtain ⟨b, t, hb, ht, hf, hef⟩ := hyperbolic_partner hs hδ hh he (hΛ.2.1 y hyΛ) hey
  have hP0 : p ^ r ≠ 0 := pow_ne_zero _ hp0
  have hP1 : ‖p ^ r‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) hp1.le
  have hPpos : 0 < ‖p ^ r‖ := norm_pos_iff.2 hP0
  have hyM := hrM y hyΛ
  generalize p ^ r = P at *
  refine ⟨e, b • y + t • e, P⁻¹, inv_ne_zero hP0, he, hf, hef, heΛ,
    add_mem (lat_smul hΛ.1 hb.le hyΛ) (lat_smul hΛ.1 ht heΛ), heM, ?_⟩
  rw [map_inv₀, inv_inv, smul_add]
  have hsP : ‖s P‖ = ‖P‖ := hs.2.1 P
  have h1 : s P • b • y = (s P * b * P⁻¹) • P • y := by
    rw [smul_smul, smul_smul, mul_assoc (s P * b), inv_mul_cancel₀ hP0, mul_one]
  have h2 : s P • t • e = (s P * t * P) • P⁻¹ • e := by
    rw [smul_smul, smul_smul, mul_assoc (s P * t), mul_inv_cancel₀ hP0, mul_one]
  rw [h1, h2]
  refine add_mem (lat_smul hM.1 ?_ hyM) (lat_smul hM.1 ?_ heM)
  · rw [norm_mul, norm_mul, norm_inv, hsP, hb, mul_one, mul_inv_cancel₀ hPpos.ne']
  · rw [norm_mul, norm_mul, hsP]
    exact mul_le_one₀ (mul_le_one₀ hP1 (norm_nonneg _) ht) (norm_nonneg _) hP1
end GlobalTheory.CompanionTheory.HermPlane
