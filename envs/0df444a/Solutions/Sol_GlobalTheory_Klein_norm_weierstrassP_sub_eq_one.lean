-- Prove2me | solution 1 for GlobalTheory.Klein.norm_weierstrassP_sub_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:58:25.381973+00:00
-- url     : https://prove2.me/submissions/78a9f567-4b66-4cee-8671-f397252dec12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_NotRedOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassCurvePointOfLatticeAddOfGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_NormWeierstrassPSubEqOne
import Theorems.Thm_GlobalTheory_latticePointEquiv_mk
import Theorems.Thm_GlobalTheory_weierstrassP_add
import Theorems.Thm_GlobalTheory_weierstrassP_add_add_sub
import Theorems.Thm_GlobalTheory_weierstrassP_eq_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.latticePointEquiv_mk


section
open Formalism.L2.Th1.F GlobalTheory.Klein
open scoped ComplexConjugate BigOperators
namespace GlobalTheory.Klein.DiffUnit
variable {p : ℕ} [Fact p.Prime]
end GlobalTheory.Klein.DiffUnit
namespace GlobalTheory.Klein
open DiffUnit
open scoped ComplexConjugate BigOperators in
variable {p : ℕ} [Fact p.Prime] in
private lemma padicComplex_norm_add_le_of_norm_le {x y : ℂ_[p]} {a : ℝ} (hx : ‖x‖ ≤ a) (hy : ‖y‖ ≤ a) :
    ‖x + y‖ ≤ a :=
  (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)
open scoped ComplexConjugate BigOperators in
variable {p : ℕ} [Fact p.Prime] in
private lemma padicComplex_norm_sub_le_of_norm_le {x y : ℂ_[p]} {a : ℝ} (hx : ‖x‖ ≤ a) (hy : ‖y‖ ≤ a) :
    ‖x - y‖ ≤ a := by
  rw [sub_eq_add_neg]
  exact padicComplex_norm_add_le_of_norm_le hx (by rwa [norm_neg])
open scoped ComplexConjugate BigOperators in
variable {p : ℕ} [Fact p.Prime] in
private lemma padicComplex_norm_mul_le_of_norm_le_one {x y : ℂ_[p]} {a : ℝ} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ a) :
    ‖x * y‖ ≤ a := by
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hx).trans hy
open scoped ComplexConjugate BigOperators in
variable {p : ℕ} [Fact p.Prime] in
private lemma padicComplex_norm_ofNat_le_one (n : ℕ) [n.AtLeastTwo] : ‖(OfNat.ofNat n : ℂ_[p])‖ ≤ 1 := by
  have := IsUltrametricDist.norm_natCast_le_one ℂ_[p] (OfNat.ofNat n)
  rwa [Nat.cast_ofNat] at this
open scoped ComplexConjugate BigOperators in
variable {p : ℕ} [Fact p.Prime] in
private lemma norm_sub_eq_one_of_discriminant_relations (hp2 : ‖(2 : ℂ_[p])‖ = 1)
    {X₁ X₂ S T Y₁ Y₂ b c D : ℂ_[p]} (hX₁ : ‖X₁‖ ≤ 1) (hX₂ : ‖X₂‖ ≤ 1) (hS : ‖S‖ ≤ 1)
    (hT : ‖T‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) (hD : ‖D‖ = 1) (hne : X₁ - X₂ ≠ 0)
    (hA : (Y₁ - Y₂) ^ 2 = (X₁ - X₂) ^ 2 * (4 * (S + X₁ + X₂) + b))
    (hB : (Y₁ + Y₂) ^ 2 = (X₁ - X₂) ^ 2 * (4 * (T + X₁ + X₂) + b))
    (hsym : (X₁ - X₂) ^ 2 * (S + T - 2 * X₂) =
      (6 * X₂ ^ 2 + b * X₂ + c / 2) * (X₁ - X₂) + Y₂ ^ 2)
    (hdisc : 4 * D = Y₂ ^ 2 * (36 * (12 * X₂ + b) * (6 * X₂ ^ 2 + b * X₂ + c / 2)
        - 108 * Y₂ ^ 2 - (12 * X₂ + b) ^ 3) +
      (6 * X₂ ^ 2 + b * X₂ + c / 2) ^ 2 * ((12 * X₂ + b) ^ 2 - 32 * (6 * X₂ ^ 2 + b * X₂ + c / 2))) :
    ‖X₁ - X₂‖ = 1 := by
  have hc2 : ‖c / 2‖ ≤ 1 := by rw [norm_div, hp2, div_one]; exact hc
  set d := X₁ - X₂ with hd
  set H := 6 * X₂ ^ 2 + b * X₂ + c / 2 with hH
  set K := 12 * X₂ + b with hK
  have h1 : ‖d‖ ≤ 1 := padicComplex_norm_sub_le_of_norm_le hX₁ hX₂
  refine le_antisymm h1 (not_lt.1 fun hlt => ?_)
  have hdpos : 0 < ‖d‖ := norm_pos_iff.2 hne
  have hfour : ∀ {W : ℂ_[p]}, ‖W‖ ≤ 1 → ‖4 * (W + X₁ + X₂) + b‖ ≤ 1 := fun hW =>
    padicComplex_norm_add_le_of_norm_le (padicComplex_norm_mul_le_of_norm_le_one (padicComplex_norm_ofNat_le_one 4)
      (padicComplex_norm_add_le_of_norm_le (padicComplex_norm_add_le_of_norm_le hW hX₁) hX₂)) hb
  have hsq : ∀ {Y W : ℂ_[p]}, Y ^ 2 = d ^ 2 * W → ‖W‖ ≤ 1 → ‖Y‖ ≤ ‖d‖ := fun {Y W} hY hW => by
    have : ‖Y‖ ^ 2 ≤ ‖d‖ ^ 2 := by
      rw [← norm_pow, hY, norm_mul, norm_pow]
      exact mul_le_of_le_one_right (by positivity) hW
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this
  have hm := hsq hA (hfour hS)
  have hp := hsq hB (hfour hT)
  have hY₂ : ‖Y₂‖ ≤ ‖d‖ := by
    have h2 : 2 * Y₂ = (Y₁ + Y₂) - (Y₁ - Y₂) := by ring
    have := padicComplex_norm_sub_le_of_norm_le hp hm
    rwa [← h2, norm_mul, hp2, one_mul] at this
  have hX₂' : ‖2 * X₂‖ ≤ 1 := padicComplex_norm_mul_le_of_norm_le_one (padicComplex_norm_ofNat_le_one 2) hX₂
  have hHd : ‖H‖ ≤ ‖d‖ := by
    have heq : H * d = d ^ 2 * (S + T - 2 * X₂) - Y₂ ^ 2 := by linear_combination -hsym
    have hST : ‖S + T - 2 * X₂‖ ≤ 1 := padicComplex_norm_sub_le_of_norm_le (padicComplex_norm_add_le_of_norm_le hS hT) hX₂'
    have : ‖H‖ * ‖d‖ ≤ ‖d‖ * ‖d‖ := by
      rw [← norm_mul, heq]
      refine padicComplex_norm_sub_le_of_norm_le ?_ ?_
      · rw [norm_mul, norm_pow]
        nlinarith [norm_nonneg (S + T - 2 * X₂), sq_nonneg ‖d‖]
      · rw [norm_pow]
        nlinarith [norm_nonneg Y₂]
    exact le_of_mul_le_mul_right this hdpos
  have hK1 : ‖K‖ ≤ 1 :=
    padicComplex_norm_add_le_of_norm_le (padicComplex_norm_mul_le_of_norm_le_one (padicComplex_norm_ofNat_le_one 12) hX₂) hb
  have hH1 : ‖H‖ ≤ 1 := hHd.trans h1
  have hα : ‖Y₂ ^ 2‖ < 1 := by
    rw [norm_pow]; nlinarith [norm_nonneg Y₂]
  have hH2 : ‖H ^ 2‖ < 1 := by
    rw [norm_pow]; nlinarith [norm_nonneg H]
  have hP : ‖36 * K * H - 108 * Y₂ ^ 2 - K ^ 3‖ ≤ 1 :=
    padicComplex_norm_sub_le_of_norm_le (padicComplex_norm_sub_le_of_norm_le
      (padicComplex_norm_mul_le_of_norm_le_one (padicComplex_norm_mul_le_of_norm_le_one (padicComplex_norm_ofNat_le_one 36) hK1) hH1)
      (padicComplex_norm_mul_le_of_norm_le_one (padicComplex_norm_ofNat_le_one 108) hα.le))
      (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hK1)
  have hQ : ‖K ^ 2 - 32 * H‖ ≤ 1 :=
    padicComplex_norm_sub_le_of_norm_le (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hK1)
      (padicComplex_norm_mul_le_of_norm_le_one (padicComplex_norm_ofNat_le_one 32) hH1)
  have hlt4 : ‖4 * D‖ < 1 := by
    rw [hdisc]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) hP).trans_lt hα
    · rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) hQ).trans_lt hH2
  have h4 : ‖4 * D‖ = 1 := by
    rw [norm_mul, hD, show (4 : ℂ_[p]) = 2 * 2 by norm_num, norm_mul, hp2]
    norm_num
  linarith
open scoped ComplexConjugate BigOperators in
variable {p : ℕ} [Fact p.Prime] in
private lemma padicComplex_norm_two_eq_one_of_ne_two (h : p ≠ 2) : ‖(2 : ℂ_[p])‖ = 1 := by
  have h1 : ‖algebraMap ℚ_[p] ℂ_[p] 2‖ = ‖(2 : ℚ_[p])‖ := norm_algebraMap' _ _
  rw [map_ofNat] at h1
  rw [h1]
  have h2 : ‖(2 : ℚ_[p])‖ = ‖((2 : ℤ) : ℤ_[p])‖ := by
    rw [PadicInt.norm_def, PadicInt.coe_intCast]; norm_num
  rw [h2]
  refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun hlt => h ?_)
  rw [PadicInt.norm_int_lt_one_iff_dvd] at hlt
  have : p ∣ 2 := by exact_mod_cast hlt
  exact (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 this
end GlobalTheory.Klein
end

set_option autoImplicit false
open Formalism.L2.Th1.F GlobalTheory.Klein
open scoped ComplexConjugate BigOperators
open GlobalTheory GlobalTheory.Klein
open DiffUnit
open scoped ComplexConjugate BigOperators
variable {p : ℕ} [Fact p.Prime]
namespace GlobalTheory.Klein
namespace _root_.GlobalTheory.Klein
theorem _root_.solution (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p])
    (L : PeriodPair) (r : ℂ)
    (hG : _root_.GlobalTheory.Klein.Good ι L r) (u v : ℂ) (hu : _root_.GlobalTheory.Klein.Red ι L r u)
    (hv : _root_.GlobalTheory.Klein.Red ι L r v)
    (h₁ : _root_.GlobalTheory.Klein.Red ι L r (u + v))
    (h₂ : _root_.GlobalTheory.Klein.Red ι L r (u - v)) :
    ‖ι (L.weierstrassP u - L.weierstrassP v)‖ = 1 := by
  obtain ⟨hp, h12r, hc, -, hΔ⟩ := hG
  obtain ⟨hu, hXu⟩ := hu
  obtain ⟨hv, hXv⟩ := hv
  obtain ⟨hs, hS⟩ := h₁
  obtain ⟨ht, hT⟩ := h₂
  have hne : L.weierstrassP u ≠ L.weierstrassP v := by
    rw [Ne, _root_.GlobalTheory.weierstrassP_eq_iff L hu hv]
    rintro (h | h)
    exacts [ht h, hs h]
  have hd : L.weierstrassP u - L.weierstrassP v ≠ 0 := sub_ne_zero.2 hne
  have hA := (_root_.GlobalTheory.weierstrassP_add L hu hv hne).1
  have hnv : -v ∉ L.lattice := fun h => hv (by simpa using neg_mem h)
  have hne' : L.weierstrassP u ≠ L.weierstrassP (-v) := by rwa [PeriodPair.weierstrassP_neg]
  have hB := (_root_.GlobalTheory.weierstrassP_add L hu hnv hne').1
  rw [PeriodPair.weierstrassP_neg, PeriodPair.derivWeierstrassP_neg, ← sub_eq_add_neg,
    sub_neg_eq_add] at hB
  have hsym := _root_.GlobalTheory.weierstrassP_add_add_sub L hu hv hne
  have hY := L.derivWeierstrassP_sq v hv
  set x₁ := L.weierstrassP u
  set x₂ := L.weierstrassP v
  set s := L.weierstrassP (u + v)
  set t := L.weierstrassP (u - v)
  set y₁ := L.derivWeierstrassP u
  set y₂ := L.derivWeierstrassP v
  have cA : (y₁ - y₂) ^ 2 = ((x₁ - r) - (x₂ - r)) ^ 2 *
      (4 * ((s - r) + (x₁ - r) + (x₂ - r)) + 12 * r) := by
    rw [hA]; field_simp; ring
  have cB : (y₁ + y₂) ^ 2 = ((x₁ - r) - (x₂ - r)) ^ 2 *
      (4 * ((t - r) + (x₁ - r) + (x₂ - r)) + 12 * r) := by
    rw [hB]; field_simp; ring
  have cS : ((x₁ - r) - (x₂ - r)) ^ 2 * ((s - r) + (t - r) - 2 * (x₂ - r)) =
      (6 * (x₂ - r) ^ 2 + 12 * r * (x₂ - r) + (12 * r ^ 2 - L.g₂) / 2) * ((x₁ - r) - (x₂ - r)) +
        y₂ ^ 2 := by
    have e : s = (6 * x₂ ^ 2 - L.g₂ / 2) / (x₁ - x₂) + y₂ ^ 2 / (x₁ - x₂) ^ 2 - t + 2 * x₂ := by
      linear_combination hsym
    rw [e]; field_simp; ring
  have cD : 4 * (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) =
      y₂ ^ 2 * (36 * (12 * (x₂ - r) + 12 * r) *
          (6 * (x₂ - r) ^ 2 + 12 * r * (x₂ - r) + (12 * r ^ 2 - L.g₂) / 2)
        - 108 * y₂ ^ 2 - (12 * (x₂ - r) + 12 * r) ^ 3) +
      (6 * (x₂ - r) ^ 2 + 12 * r * (x₂ - r) + (12 * r ^ 2 - L.g₂) / 2) ^ 2 *
        ((12 * (x₂ - r) + 12 * r) ^ 2 -
          32 * (6 * (x₂ - r) ^ 2 + 12 * r * (x₂ - r) + (12 * r ^ 2 - L.g₂) / 2)) := by
    rw [hY]; ring
  have key := norm_sub_eq_one_of_discriminant_relations (padicComplex_norm_two_eq_one_of_ne_two hp) hXu hXv hS hT h12r hc
    hΔ (Y₁ := ι y₁) (Y₂ := ι y₂)
    (by rw [← map_sub]; exact (map_ne_zero ι).2 (by rwa [sub_sub_sub_cancel_right]))
    (by simpa only [map_sub, map_mul, map_add, map_pow, map_ofNat, map_div₀] using congrArg ι cA)
    (by simpa only [map_sub, map_mul, map_add, map_pow, map_ofNat, map_div₀] using congrArg ι cB)
    (by simpa only [map_sub, map_mul, map_add, map_pow, map_ofNat, map_div₀] using congrArg ι cS)
    (by simpa only [map_sub, map_mul, map_add, map_pow, map_ofNat, map_div₀] using congrArg ι cD)
  rwa [← map_sub, sub_sub_sub_cancel_right] at key
end _root_.GlobalTheory.Klein
end GlobalTheory.Klein
