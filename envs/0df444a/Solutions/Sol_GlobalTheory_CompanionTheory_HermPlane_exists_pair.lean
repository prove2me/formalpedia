-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HermPlane.exists_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:55:09.983538+00:00
-- url     : https://prove2.me/submissions/e329243f-438f-44d8-a608-ece7f8d5462e

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_PlaneOfHenselAndPairing
import Theorems.Thm_GlobalTheory_CompanionTheory_HermPlane_lat_smul
import Theorems.Thm_GlobalTheory_CompanionTheory_HermPlane_lat_primitive
import Theorems.Thm_GlobalTheory_CompanionTheory_HermPlane_herm_add_left
import Theorems.Thm_GlobalTheory_CompanionTheory_HermPlane_herm_smul_left
import Theorems.Thm_GlobalTheory_CompanionTheory_HermPlane_one_le_norm_delta
import Theorems.Thm_GlobalTheory_CompanionTheory_HermPlane_isotropic_lift

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
theorem _root_.solution (hH : StHensel) (hP : StPairing) {s : L →+* L} (hs : IsInv s) {δ : L}
    (hδ : IsDelta s δ) {h : V → V → L} (hh : IsHerm s h) (hiso : ∃ x, x ≠ 0 ∧ h x x = 0)
    {Λ M : AddSubgroup V} (hΛ : IsMax h Λ) (hM : IsMax h M) {p : L} (hp0 : p ≠ 0) (hp1 : ‖p‖ < 1)
    (hpm : ∀ a : L, ‖a‖ < 1 → ‖a‖ ≤ ‖p‖) {r : ℕ} (hr : ∀ x ∈ M, p ^ r • x ∈ Λ)
    (hmin : ∀ k < r, ∃ z ∈ M, p ^ k • z ∉ Λ) (hrM : ∀ y ∈ Λ, p ^ r • y ∈ M) :
    ∃ e y : V, e ∈ Λ ∧ y ∈ Λ ∧ h e e = 0 ∧ ‖h e y‖ = ‖δ‖ ∧ (p ^ r)⁻¹ • e ∈ M := by
  obtain ⟨-, hpair⟩ := hP L s hs δ hδ V h hh Λ hΛ
  obtain ⟨hinv, hnorm, -⟩ := id hs
  rcases r with _ | n
  · obtain ⟨v, hv, hq⟩ := hiso
    obtain ⟨a, ha0, haΛ, hprim⟩ := lat_primitive hΛ.1 hp0 hp1 hv
    have hqa : h (a • v) (a • v) = 0 := by rw [herm_smul_left hh, hh.2.1, hq]; simp
    obtain ⟨y, hy, hxy⟩ := hpair p hp1 hpm (a • v) haΛ hprim (by rw [hqa, norm_zero]; positivity)
    refine ⟨a • v, y, haΛ, hy, hqa, by rw [hxy], ?_⟩
    simpa using hrM _ haΛ
  · obtain ⟨z, hz, hzΛ⟩ := hmin n (Nat.lt_succ_self n)
    have hP0 : p ^ (n + 1) ≠ 0 := pow_ne_zero _ hp0
    have hPle : ‖p ^ (n + 1)‖ ≤ ‖p‖ := by
      rw [norm_pow, pow_succ]
      exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hp1.le)
    have hP1 : ‖p ^ (n + 1)‖ < 1 := hPle.trans_lt hp1
    generalize hPdef : p ^ (n + 1) = P at *
    have hPpos : 0 < ‖P‖ := norm_pos_iff.2 hP0
    have hxΛ : P • z ∈ Λ := hr z hz
    have hprim : p⁻¹ • P • z ∉ Λ := by
      intro hcon
      apply hzΛ
      have hpn : p⁻¹ * P = p ^ n := by
        rw [← hPdef, pow_succ']
        field_simp
      rwa [smul_smul, hpn] at hcon
    have hqz := hM.2.1 z hz
    have hnx : ‖h (P • z) (P • z)‖ ≤ ‖P‖ * ‖P‖ := by
      rw [herm_smul_left hh, hh.2.1, norm_mul, norm_mul, hnorm]
      calc ‖P‖ * (‖P‖ * ‖h z z‖) ≤ ‖P‖ * (‖P‖ * 1) := by gcongr
        _ = ‖P‖ * ‖P‖ := by ring
    obtain ⟨y, hy, hxy⟩ := hpair p hp1 hpm (P • z) hxΛ hprim (by
      refine hnx.trans ?_
      rw [pow_two]
      exact mul_le_mul hPle hPle (norm_nonneg _) (norm_nonneg _))
    have hN : ‖P * s P‖ = ‖P‖ * ‖P‖ := by rw [norm_mul, hnorm]
    have hN1 : ‖P * s P‖ < 1 := by
      rw [hN]
      exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hP1 hP1.le
    have hqy := hΛ.2.1 y hy
    obtain ⟨a, ha, haq⟩ := isotropic_lift hH hs hδ hh
      (mul_ne_zero hP0 ((map_ne_zero s).2 hP0)) hN1
      (by rw [map_mul, hinv, mul_comm]) (by rw [hN]; exact hnx) hqy hxy
    have ha1 : ‖a‖ ≤ 1 := ha.trans hN1.le
    have haN : ‖a‖ < 1 := ha.trans_lt hN1
    refine ⟨P • z + a • y, y, add_mem hxΛ (lat_smul hΛ.1 ha1 hy), hy, haq, ?_, ?_⟩
    · rw [herm_add_left hh, hxy, herm_smul_left hh]
      have h1 := one_le_norm_delta hs hδ
      have h2 : ‖s a * h y y‖ < ‖δ‖ := by
        rw [norm_mul, hnorm]
        calc ‖a‖ * ‖h y y‖ ≤ ‖a‖ * 1 := by gcongr
          _ < 1 := by simpa using haN
          _ ≤ ‖δ‖ := h1
      rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h2.ne']
      exact max_eq_left h2.le
    · have heq : P⁻¹ • (P • z + a • y) = z + (P⁻¹ * a * P⁻¹) • (P • y) := by
        rw [smul_add, smul_smul, smul_smul, smul_smul (P⁻¹ * a * P⁻¹), inv_mul_cancel₀ hP0, one_smul,
          mul_assoc (P⁻¹ * a), inv_mul_cancel₀ hP0, mul_one]
      rw [heq]
      refine add_mem hz (lat_smul hM.1 ?_ (hrM y hy))
      rw [norm_mul, norm_mul, norm_inv]
      have : ‖a‖ ≤ ‖P‖ * ‖P‖ := hN ▸ ha
      field_simp
      rw [pow_two]
      exact this
end GlobalTheory.CompanionTheory.HermPlane
