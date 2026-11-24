-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HermPlane.hyperbolic_partner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:38:22.396996+00:00
-- url     : https://prove2.me/submissions/bdfaca77-fa21-4de2-94aa-57c2f64435eb

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_PlaneOfHenselAndPairing
import Theorems.Thm_GlobalTheory_CompanionTheory_HermPlane_herm_smul_left
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
theorem _root_.solution {s : L →+* L} (hs : IsInv s) {δ : L} (hδ : IsDelta s δ) {h : V → V → L}
    (hh : IsHerm s h) {e y : V} (he : h e e = 0) (hqy : ‖h y y‖ ≤ 1) (hey : ‖h e y‖ = ‖δ‖) :
    ∃ b t : L, ‖b‖ = 1 ∧ ‖t‖ ≤ 1 ∧ h (b • y + t • e) (b • y + t • e) = 0 ∧
      h e (b • y + t • e) = δ := by
  obtain ⟨hinv, hnorm, -⟩ := id hs
  obtain ⟨hδ0, -, c0, hc0, hc⟩ := hδ
  have hc' : c0 * δ + s c0 * s δ = 1 := by simpa [map_mul] using hc
  have hw0 : h e y ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hey
    exact hδ0 (norm_eq_zero.1 hey.symm)
  have hb : ‖δ / h e y‖ = 1 := by
    rw [norm_div, hey]
    exact div_self (norm_ne_zero_iff.2 hδ0)
  set b : L := δ / h e y with hbdef
  set y' : V := b • y with hy'
  have hfix : s (h y' y') = h y' y' := (hh.2.2.1 y' y').symm
  have hq' : ‖h y' y'‖ ≤ 1 := by
    rw [hy', herm_smul_left hh, hh.2.1, norm_mul, norm_mul, hnorm, hb]
    simpa using hqy
  have hey' : h e y' = δ := by
    rw [hy', hh.2.1, hbdef]
    field_simp
  have hy'e : h y' e = s δ := by rw [hh.2.2.1 e y', hey']
  refine ⟨b, -(h y' y' * s c0), hb, ?_, ?_, ?_⟩
  · rw [norm_neg, norm_mul, hnorm]
    exact mul_le_one₀ hq' (norm_nonneg _) hc0
  · have hexp := herm_expand hh (-(h y' y' * s c0)) 1 y' e
    rw [one_smul] at hexp
    rw [← hy', hexp, hey', hy'e, he]
    simp only [map_one, map_mul, map_neg, hfix, hinv, one_mul]
    linear_combination (-(h y' y')) * hc'
  · rw [← hy', hh.1, hey', hh.2.1, he]
    simp
end GlobalTheory.CompanionTheory.HermPlane
