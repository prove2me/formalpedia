-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HermPlane.isotropic_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:38:07.145685+00:00
-- url     : https://prove2.me/submissions/bc9ddeed-95cc-4843-9c46-eea8a4f5e567

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_PlaneOfHenselAndPairing
import Theorems.Thm_GlobalTheory_CompanionTheory_HermPlane_herm_expand

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
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {V : Type} [AddCommGroup V] [Module L V]
namespace GlobalTheory.CompanionTheory.HermPlane
theorem _root_.solution [CompleteSpace L] (hH : StHensel) {s : L →+* L} (hs : IsInv s) {δ : L}
    (hδ : IsDelta s δ) {h : V → V → L} (hh : IsHerm s h) {x y : V} {N : L} (hN0 : N ≠ 0)
    (hN1 : ‖N‖ < 1) (hNs : s N = N) (hqx : ‖h x x‖ ≤ ‖N‖) (hqy : ‖h y y‖ ≤ 1) (hxy : h x y = δ) :
    ∃ a : L, ‖a‖ ≤ ‖N‖ ∧ h (x + a • y) (x + a • y) = 0 := by
  obtain ⟨hinv, hnorm, -⟩ := id hs
  obtain ⟨-, -, c0, hc0, hc⟩ := hδ
  have hfx : s (h x x) = h x x := (hh.2.2.1 x x).symm
  have hfy : s (h y y) = h y y := (hh.2.2.1 y y).symm
  have hc' : c0 * δ + s c0 * s δ = 1 := by simpa [map_mul] using hc
  have hNpos : 0 < ‖N‖ := norm_pos_iff.2 hN0
  obtain ⟨u, hu, hu1, huq⟩ := hH L s hs (N * (c0 * s c0 * h y y)) (h x x / N)
    (by simp only [map_mul, hNs, hinv, hfy]; ring)
    (by rw [map_div₀, hfx, hNs])
    (by
      rw [norm_mul, norm_mul, norm_mul, hnorm]
      have : ‖c0‖ * ‖c0‖ * ‖h y y‖ ≤ 1 :=
        mul_le_one₀ (mul_le_one₀ hc0 (norm_nonneg _) hc0) (norm_nonneg _) hqy
      calc ‖N‖ * (‖c0‖ * ‖c0‖ * ‖h y y‖) ≤ ‖N‖ * 1 := by gcongr
        _ < 1 := by simpa using hN1)
    (by rw [norm_div]; exact div_le_one_of_le₀ hqx hNpos.le)
  have hd : h x x = N * (h x x / N) := by field_simp
  refine ⟨N * c0 * u, ?_, ?_⟩
  · rw [norm_mul, norm_mul]
    calc ‖N‖ * ‖c0‖ * ‖u‖ ≤ ‖N‖ * 1 * 1 := by gcongr
      _ = ‖N‖ := by ring
  · have hexp := herm_expand hh (N * c0 * u) 1 x y
    rw [one_smul] at hexp
    rw [hexp, hxy, hh.2.2.1 x y, hxy]
    simp only [map_one, map_mul, hNs, hu, one_mul]
    linear_combination hd + N * huq + N * u * hc'
end GlobalTheory.CompanionTheory.HermPlane
