-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HermAniso.pair_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:09:20.535237+00:00
-- url     : https://prove2.me/submissions/5c162aab-b006-4d7d-a276-f75322be27c3

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_AnisotropicOfHenselAndSandwich
import Theorems.Thm_GlobalTheory_CompanionTheory_HermAniso_smul_left
import Theorems.Thm_GlobalTheory_CompanionTheory_HermAniso_q_add

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HermAniso
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
  {s : L →+* L} {h : V → V → L}
namespace GlobalTheory.CompanionTheory.HermAniso
theorem _root_.solution [IsUltrametricDist L] [CompleteSpace L] (hH : StHensel) (hs : IsInv s) (hh : IsHerm s h)
    (hani : ∀ x, h x x = 0 → x = 0) {x y : V} (hx : ‖h x x‖ ≤ 1) (hy : ‖h y y‖ ≤ 1) :
    ‖h x y + h y x‖ ≤ 1 := by
  have h1 := hh.2.2.1
  by_contra hb
  push_neg at hb
  obtain ⟨b, hbd⟩ : ∃ b, b = h x y + h y x := ⟨_, rfl⟩
  rw [← hbd] at hb
  have hbpos : 0 < ‖b‖ := by linarith
  have hb0 : b ≠ 0 := norm_pos_iff.mp hbpos
  have hsb : s b = b := by
    rw [hbd, map_add, ← h1 x y, ← h1 y x, add_comm]
  have hsx : s (h x x) = h x x := (h1 x x).symm
  have hsy : s (h y y) = h y y := (h1 y y).symm
  have hc1 : s (h y y / b ^ 2) = h y y / b ^ 2 := by
    rw [map_div₀, map_pow, hsb, hsy]
  have hc2 : ‖h y y / b ^ 2‖ < 1 := by
    rw [norm_div, norm_pow, div_lt_one (by positivity)]
    nlinarith
  obtain ⟨u, hsu, hu, he⟩ := hH L s hs (h y y / b ^ 2) (h x x) hc1 hsx hc2 hx
  obtain ⟨t, htd⟩ : ∃ t, t = u / b := ⟨_, rfl⟩
  have hst : s t = t := by rw [htd, map_div₀, hsu, hsb]
  have hq : h (x + t • y) (x + t • y) = 0 := by
    rw [q_add hh, smul_left hh, hh.2.1, hh.2.1, smul_left hh, hst]
    have e1 : t * (t * h y y) + t * h x y + t * h y x = t * b + t ^ 2 * h y y := by
      rw [hbd]; ring
    have e2 : t * b = u := by rw [htd]; field_simp
    have e3 : t ^ 2 * h y y = h y y / b ^ 2 * u ^ 2 := by rw [htd]; field_simp
    linear_combination he + e1 + e2 + e3
  have hz := hani _ hq
  have hxe : x = (-t) • y := by
    rw [neg_smul]; exact eq_neg_of_add_eq_zero_left hz
  have hxy : h x y = -t * h y y := by
    have : h x y = h ((-t) • y) y := congrArg (fun z => h z y) hxe
    rw [this, smul_left hh, map_neg, hst]
  have hyx : h y x = -t * h y y := by
    have : h y x = h y ((-t) • y) := congrArg (fun z => h y z) hxe
    rw [this, hh.2.1]
  have ht : ‖t‖ < 1 := by
    rw [htd, norm_div, div_lt_one hbpos]; linarith
  have hle : ‖-t * h y y‖ < 1 := by
    rw [norm_mul, norm_neg]
    nlinarith [norm_nonneg t, norm_nonneg (h y y)]
  have : ‖b‖ < 1 := by
    rw [hbd, hxy, hyx]
    exact lt_of_le_of_lt ((IsUltrametricDist.norm_add_le_max _ _).trans (by simp)) hle
  linarith
end GlobalTheory.CompanionTheory.HermAniso
