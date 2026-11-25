-- Prove2me | solution 1 for GlobalTheory.DI.exists_isH_of_isFrob
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:41:38.323931+00:00
-- url     : https://prove2.me/submissions/64e610dd-fc94-4a12-9735-074994f344c4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FrobeniusDerivationFactorsThroughKaehlerStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIsHOfIsFrob
import Theorems.Thm_GlobalTheory_T_frobeniusDerivation_factors_through_kaehler


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
open GlobalTheory GlobalTheory.DI
namespace GlobalTheory.DI
theorem _root_.solution : ∀ {K Kt : Type} [CommRing K] [CommRing Kt] (p : ℕ) [Fact p.Prime] [CharP K p]
    (π : Kt →+* K) (F F' : Kt →+* Kt), IsFlatLift p π → IsFrob p π F → IsFrob p π F' →
    ∃ h, IsH p π F F' h := by
  intro K Kt _ _ p _ _ π F F' hL hF hF'
  have hex : ∀ z, ∃ w, F' z = F z + p * w := by
    intro z
    obtain ⟨w, hw⟩ := (hL.ker (F' z - F z)).1 (by rw [map_sub, hF, hF', sub_self])
    exact ⟨w, by rw [← hw]; ring⟩
  have huniq : ∀ z w w', F' z = F z + p * w → F' z = F z + p * w' → π w = π w' := by
    intro z w w' h1 h2
    have h3 : (p : Kt) * (w - w') = 0 := by rw [mul_sub]; linear_combination h2 - h1
    have h4 := (hL.ann (w - w')).1 h3
    rw [map_sub] at h4
    exact sub_eq_zero.1 h4
  let g : Kt → K := fun z => π (Classical.choose (hex z))
  have hg : ∀ z w, F' z = F z + p * w → g z = π w := fun z w hw =>
    huniq z _ w (Classical.choose_spec (hex z)) hw
  have hgadd : ∀ z z', g (z + z') = g z + g z' := by
    intro z z'
    obtain ⟨w, h1⟩ := hex z
    obtain ⟨w', h2⟩ := hex z'
    rw [hg z w h1, hg z' w' h2, hg (z + z') (w + w') (by rw [map_add, map_add, h1, h2]; ring), map_add]
  have hgp : ∀ y, g (p * y) = 0 := by
    intro y
    obtain ⟨w, h1⟩ := hex y
    rw [hg (p * y) (p * w) (by rw [map_mul, map_mul, map_natCast, map_natCast, h1]; ring), map_mul,
      map_natCast, CharP.cast_eq_zero, zero_mul]
  have hgmul : ∀ z z', g (z * z') = π z' ^ p * g z + π z ^ p * g z' := by
    intro z z'
    obtain ⟨w, h1⟩ := hex z
    obtain ⟨w', h2⟩ := hex z'
    rw [hg z w h1, hg z' w' h2, hg (z * z') (w * F z' + F z * w' + p * w * w')
      (by rw [map_mul, map_mul, h1, h2]; ring)]
    simp only [map_add, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul, add_zero]
    rw [hF z, hF z']
    ring
  have hwd : ∀ z z', π z = π z' → g z = g z' := by
    intro z z' hzz
    obtain ⟨y, hy⟩ := (hL.ker (z - z')).1 (by rw [map_sub, hzz, sub_self])
    have : z = z' + p * y := by rw [← hy]; ring
    rw [this, hgadd, hgp, add_zero]
  let φ : K →+ K := AddMonoidHom.mk' (fun x => g (Function.surjInv hL.surj x)) (by
    intro a b
    show g _ = g _ + g _
    rw [← hgadd]
    apply hwd
    rw [map_add, Function.surjInv_eq hL.surj, Function.surjInv_eq hL.surj, Function.surjInv_eq hL.surj])
  have hφ : ∀ z, φ (π z) = g z := by
    intro z
    show g _ = g _
    exact hwd _ _ (Function.surjInv_eq hL.surj _)
  obtain ⟨f, hfs, hfD⟩ := GlobalTheory.T.frobeniusDerivation_factors_through_kaehler (M := K) p φ (by
    intro a b
    obtain ⟨z, rfl⟩ := hL.surj a
    obtain ⟨z', rfl⟩ := hL.surj b
    rw [← map_mul, hφ, hφ, hφ, hgmul, smul_eq_mul, smul_eq_mul]; ring)
  refine ⟨f, fun c v => by rw [hfs, smul_eq_mul], fun z w hzw => ?_⟩
  rw [hfD, hφ, hg z w hzw]
end GlobalTheory.DI
