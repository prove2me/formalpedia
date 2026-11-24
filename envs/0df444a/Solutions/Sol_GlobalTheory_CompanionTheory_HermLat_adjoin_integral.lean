-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HermLat.adjoin_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:16:30.619812+00:00
-- url     : https://prove2.me/submissions/23d20437-9b8a-4bb4-8f30-f815d8ab7976

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_PairingOfSandwichStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_HermLat_herm_smul_left
import Theorems.Thm_GlobalTheory_CompanionTheory_HermLat_herm_add_add

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HermLat
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {V : Type} [AddCommGroup V]
  [Module L V] {s : L →+* L} {δ : L} {h : V → V → L}
namespace GlobalTheory.CompanionTheory.HermLat
theorem _root_.solution (hs : IsInv s) (hδ : IsDelta s δ) (hh : IsHerm s h) {Λ : AddSubgroup V}
    (hint : ∀ x ∈ Λ, ‖h x x‖ ≤ 1) {p : L} (hp0 : p ≠ 0) {x : V}
    (hq : ‖h x x‖ ≤ ‖p‖ ^ 2) (hsmall : ∀ y ∈ Λ, ‖h x y‖ ≤ ‖p‖ * ‖δ‖) :
    ∀ z ∈ adjoin L Λ (p⁻¹ • x), ‖h z z‖ ≤ 1 := by
  rintro _ ⟨l, hl, a, ha, rfl⟩
  have hpn : 0 < ‖p‖ := norm_pos_iff.mpr hp0
  rw [herm_add_add hh]
  have hb : ‖h l (a • p⁻¹ • x)‖ ≤ ‖δ‖ := by
    rw [hh.2.1, hh.2.1, hh.2.2.1 x l, norm_mul, norm_mul, norm_inv, hs.2.1]
    have h1 := hsmall l hl
    calc ‖a‖ * (‖p‖⁻¹ * ‖h x l‖) ≤ 1 * (‖p‖⁻¹ * (‖p‖ * ‖δ‖)) := by gcongr
      _ = ‖δ‖ := by field_simp
  have htr : ‖h l (a • p⁻¹ • x) + s (h l (a • p⁻¹ • x))‖ ≤ 1 := by
    have := (hδ.2.1 _).2 hb 1 (by simp)
    simpa using this
  have hlast : ‖h (a • p⁻¹ • x) (a • p⁻¹ • x)‖ ≤ 1 := by
    rw [herm_smul_left hh, herm_smul_left hh, hh.2.1, hh.2.1, norm_mul, norm_mul, norm_mul,
      norm_mul, hs.2.1, hs.2.1, norm_inv]
    have hpp : ‖p‖⁻¹ * (‖p‖⁻¹ * ‖p‖ ^ 2) = 1 := by field_simp
    calc ‖a‖ * (‖p‖⁻¹ * (‖a‖ * (‖p‖⁻¹ * ‖h x x‖)))
        ≤ 1 * (‖p‖⁻¹ * (1 * (‖p‖⁻¹ * ‖p‖ ^ 2))) := by gcongr
      _ = 1 := by rw [one_mul, one_mul, hpp]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le
    ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hint l hl) htr)) hlast)
end GlobalTheory.CompanionTheory.HermLat
