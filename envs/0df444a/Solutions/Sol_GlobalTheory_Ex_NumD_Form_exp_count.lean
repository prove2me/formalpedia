-- Prove2me | solution 1 for GlobalTheory.Ex.NumD.Form.exp_count
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:51:27.409665+00:00
-- url     : https://prove2.me/submissions/21a02491-cfde-468c-bbf9-a131bbc9f172

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TwistTerms

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.Ex.NumD
variable {O : Type} [CommRing O] (N : NumD O)
namespace GlobalTheory.Ex.NumD
namespace Form
theorem _root_.solution {N : NumD O} {k : ℕ} (β : N.Form k) {m : ℕ} (hm : m ^ 2 ∣ k) (ho : Odd m) (y χ : N.X) :
    β.be (y + m • χ) (y + m • χ) / (2 * m ^ 2) =
      β.be y y / 2 - β.be y y / (m ^ 2 : ℕ) * ((m ^ 2 - 1) / 2 : ℕ) + β.be χ χ / 2 + β.be y χ / (m ^ 2 : ℕ) * m := by
  have hd : ∀ x z, (2 * (m : ℤ) ^ 2) ∣ β.be x z := fun x z =>
    (mul_dvd_mul_left 2 (by exact_mod_cast hm)).trans (β.dvd x z)
  obtain ⟨a, ha⟩ := hd y y
  obtain ⟨b, hb⟩ := hd y χ
  obtain ⟨c, hc⟩ := hd χ χ
  obtain ⟨t, ht⟩ := ho.pow (n := 2)
  have hm0 : (m : ℤ) ^ 2 ≠ 0 := pow_ne_zero _ (Int.natCast_ne_zero.2 ho.pos.ne')
  have h1 : (m ^ 2 - 1) / 2 = t := by omega
  have h2 : (m : ℤ) ^ 2 = 2 * t + 1 := by exact_mod_cast ht
  have e : β.be (y + m • χ) (y + m • χ) = 2 * m ^ 2 * (a + 2 * m * b + m ^ 2 * c) := by
    simp only [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul, β.symm χ y, ha, hb, hc]
    ring
  have d1 : ∀ x : ℤ, 2 * (m : ℤ) ^ 2 * x / 2 = m ^ 2 * x := fun x => by
    rw [mul_assoc, Int.mul_ediv_cancel_left _ two_ne_zero]
  have d2 : ∀ x : ℤ, 2 * (m : ℤ) ^ 2 * x / (m ^ 2 : ℕ) = 2 * x := fun x => by
    rw [Nat.cast_pow, mul_right_comm, Int.mul_ediv_cancel _ hm0]
  rw [e, h1, ha, hb, hc, d1, d1, d2, d2, Int.mul_ediv_cancel_left _ (mul_ne_zero two_ne_zero hm0)]
  linear_combination (-a) * h2
end Form
end GlobalTheory.Ex.NumD
