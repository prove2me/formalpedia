-- Prove2me | solution 1 for GlobalTheory.SplitLevel.exists_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:21:39.843426+00:00
-- url     : https://prove2.me/submissions/9332de21-54c7-4f76-bc78-72467f148bba

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLevelMulSplit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.SplitLevel
namespace GlobalTheory.SplitLevel
theorem _root_.solution {p d m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : 4 * m = d + 1)
    (hj : jacobiSym (-(d : ℤ)) p = 1) :
    ∃ c : ℤ, (p : ℤ) ∣ c ^ 2 - c + m ∧ IsCoprime (1 - 2 * c) (p : ℤ) := by
  have := Fact.mk hp
  obtain ⟨r, hr⟩ := ZMod.isSquare_of_jacobiSym_eq_one hj
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h')
  set h := (2 : ZMod p)⁻¹
  have hh : 2 * h = 1 := mul_inv_cancel₀ h2
  have e4 : (4 : ZMod p) * (m : ZMod p) = (d : ZMod p) + 1 := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ZMod p) hm
  push_cast at hr
  obtain ⟨c, hc⟩ := ZMod.intCast_surjective ((1 + r) * h)
  have hdv : (p : ℤ) ∣ c ^ 2 - c + m := by
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 ?_
    push_cast [hc]
    linear_combination (-h ^ 2) * hr + h ^ 2 * e4 + ((1 + r) * h - (m : ZMod p) * (2 * h + 1)) * hh
  refine ⟨c, hdv, ?_⟩
  apply IsCoprime.symm
  rw [Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp)]
  intro hdiv
  have e : (4 : ℤ) * (m : ℤ) = (d : ℤ) + 1 := by exact_mod_cast hm
  have hd : -(d : ℤ) = (1 - 2 * c) ^ 2 - 4 * (c ^ 2 - c + m) := by
    linear_combination e
  have hpd : (p : ℤ) ∣ -(d : ℤ) := by
    rw [hd]; exact dvd_sub (dvd_pow hdiv two_ne_zero) (Dvd.dvd.mul_left hdv 4)
  have h0 : jacobiSym (-(d : ℤ)) p = 0 := by
    rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_zero_iff]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 hpd
  rw [h0] at hj
  exact absurd hj (by decide)
end GlobalTheory.SplitLevel
