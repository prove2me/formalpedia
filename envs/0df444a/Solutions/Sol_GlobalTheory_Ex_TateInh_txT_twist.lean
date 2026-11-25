-- Prove2me | solution 1 for GlobalTheory.Ex.TateInh.txT_twist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:43:54.32571+00:00
-- url     : https://prove2.me/submissions/d0275849-3d67-412d-af0f-fa951c9fc90b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Ex
variable {O : Type} [CommRing O]
open GlobalTheory.Ex.TateInh
namespace GlobalTheory.Ex.TateInh
theorem _root_.solution (N : NumD O) {k : ℕ} (β : N.Form k) (u : Oˣ) (m : ℕ) (hm : m ^ 2 ∣ k) (ho : Odd m)
    (p : N.QT (m ^ 2)) (χ : N.X) :
    (N.twist β u).txT m (N.twQ β u hm p) χ =
      (u ^ (β.be (p.1.1.toAdd + m • χ) (p.1.1.toAdd + m • χ) / (2 * m ^ 2)) : Oˣ) * N.txT m p χ := by
  set y := p.1.1.toAdd with hy
  have h' := N.twG_pow β u p.1.2 (fun z => β.be y z / ((m ^ 2 : ℕ) : ℤ)) (β.div_add hm _) m
  have hd : ∀ a b, (2 * m ^ 2 : ℤ) ∣ β.be a b := fun a b =>
    (mul_dvd_mul_left 2 (by exact_mod_cast hm)).trans (β.dvd a b)
  obtain ⟨a, ha⟩ := hd y y
  obtain ⟨b, hb⟩ := hd y χ
  obtain ⟨c, hc⟩ := hd χ χ
  obtain ⟨r, hr⟩ : Odd (m ^ 2) := ho.pow
  have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast ho.pos.ne'
  have hr' : (m : ℤ) ^ 2 = 2 * r + 1 := by exact_mod_cast hr
  have e0 : β.be (y + m • χ) (y + m • χ) / (2 * m ^ 2) = a + 2 * b * m + c * m ^ 2 := by
    simp only [map_add, LinearMap.add_apply, map_nsmul, LinearMap.smul_apply, β.symm χ y, ha, hb, hc, nsmul_eq_mul]
    exact Int.ediv_eq_of_eq_mul_right (by positivity) (by ring)
  have e1 : β.be y y / 2 = a * (2 * r + 1) := Int.ediv_eq_of_eq_mul_right two_ne_zero (by rw [ha, hr']; ring)
  have e2 : β.be χ χ / 2 = c * m ^ 2 := Int.ediv_eq_of_eq_mul_right two_ne_zero (by rw [hc]; ring)
  have e3 : β.be y y / ((m ^ 2 : ℕ) : ℤ) = 2 * a := Int.ediv_eq_of_eq_mul_right (by push_cast; positivity) (by rw [ha]; push_cast; ring)
  have e4 : β.be y χ / ((m ^ 2 : ℕ) : ℤ) = 2 * b := Int.ediv_eq_of_eq_mul_right (by push_cast; positivity) (by rw [hb]; push_cast; ring)
  have e5 : (m ^ 2 - 1) / 2 = r := by omega
  change ((N.ψ y * u ^ (β.be y y / 2) * mulq N.θ N.σ (m ^ 2) p.1.2.b /
      (p.1.2.s y * u ^ (β.be y y / ((m ^ 2 : ℕ) : ℤ)) * cubN N.θ (m ^ 2) 1 p.1.2.b p.1.2.b / dbl N.θ N.σ p.1.2.b ^ (m ^ 2)) ^ ((m ^ 2 - 1) / 2)
      / mulq N.θ N.σ m p.1.2.b : Oˣ) : O) *
      ((N.ψ χ * u ^ (β.be χ χ / 2) * (N.twG β u p.1.2 (fun z => β.be y z / ((m ^ 2 : ℕ) : ℤ)) (β.div_add hm _) ^ m).s χ : Oˣ) *
        N.th (N.c χ * (show N.A from (N.twG β u p.1.2 (fun z => β.be y z / ((m ^ 2 : ℕ) : ℤ)) (β.div_add hm _) ^ m).b))) = _
  erw [h'.1, h'.2]
  rw [ e0, e1, e2, e3, e4]
  simp only [NumD.txT, NumD.vt, NumD.wQ, NumB.wS, ← hy, e5, ← mul_assoc, ← Units.val_mul]
  congr 2
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, ofMul_pow, ofMul_zpow]
  module
end GlobalTheory.Ex.TateInh
