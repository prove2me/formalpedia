-- Prove2me | solution 1 for ModularCurve.FifteenA1.selmerBound
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/5fb54a86-54e0-547f-87b4-b83f4a49b6d3

import Definitions.Def_EllipticCurve_FifteenA1
import Theorems.Thm_ModularCurve_FifteenA1_deltaPairHom
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Algebra.Rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FifteenA1_selmerBound

set_option autoImplicit false

namespace M4cP2
namespace Selmer

p2m_open "WeierstrassCurve Affine WeierstrassCurve.Affine ModularCurve.FifteenA1"

theorem equation_shortW_iff (X Y : ℚ) :
    shortW.Equation X Y ↔ Y ^ 2 = (X - 12) * (X + 4) * (X + 13) := by
  rw [equation_iff]
  simp only [shortW_a₁, shortW_a₂, shortW_a₃, shortW_a₄, shortW_a₆]
  constructor <;> intro h <;> linear_combination h

theorem negY_shortW (X Y : ℚ) : shortW.negY X Y = -Y := by
  simp [WeierstrassCurve.Affine.negY]

theorem factors_ne_zero {X Y : ℚ} (h : shortW.Nonsingular X Y) (hY : Y ≠ 0) :
    X - 12 ≠ 0 ∧ X + 4 ≠ 0 ∧ X + 13 ≠ 0 := by
  have heq : Y ^ 2 = (X - 12) * (X + 4) * (X + 13) := (equation_shortW_iff X Y).mp h.1
  exact ⟨fun h0 => pow_ne_zero 2 hY (by rw [heq, h0]; ring),
    fun h0 => pow_ne_zero 2 hY (by rw [heq, h0]; ring),
    fun h0 => pow_ne_zero 2 hY (by rw [heq, h0]; ring)⟩

theorem two_torsion_abscissa {X : ℚ} (h : shortW.Nonsingular X 0) :
    X = 12 ∨ X = -4 ∨ X = -13 := by
  have heq : (0 : ℚ) ^ 2 = (X - 12) * (X + 4) * (X + 13) := (equation_shortW_iff X 0).mp h.1
  have hzero : (X - 12) * (X + 4) * (X + 13) = 0 := by linear_combination -heq
  rcases mul_eq_zero.mp hzero with h0 | h0
  · rcases mul_eq_zero.mp h0 with h1 | h1
    · exact Or.inl (by linarith)
    · exact Or.inr (Or.inl (by linarith))
  · exact Or.inr (Or.inr (by linarith))

theorem isSqClass_self (a : ℚ) : IsSqClass a a := ⟨1, one_ne_zero, by ring⟩

theorem ne_zero_of_isSqClass {d a : ℚ} (hd : d ≠ 0) (h : IsSqClass d a) : a ≠ 0 := by
  obtain ⟨c, hc, rfl⟩ := h
  exact mul_ne_zero hd (pow_ne_zero 2 hc)

theorem isSqClass_symm {d a : ℚ} (_hd : d ≠ 0) (h : IsSqClass d a) : IsSqClass a d := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
  rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hc, one_pow, mul_one]

theorem isSqClass_trans {d a b : ℚ} (hab : IsSqClass d a) (hbc : IsSqClass a b) :
    IsSqClass d b := by
  obtain ⟨c₁, hc₁, rfl⟩ := hab
  obtain ⟨c₂, hc₂, rfl⟩ := hbc
  exact ⟨c₁ * c₂, mul_ne_zero hc₁ hc₂, by ring⟩

theorem not_isSqClass_of_pos_of_neg {d a : ℚ} (hd : 0 < d) (ha : a < 0) : ¬ IsSqClass d a := by
  rintro ⟨c, hc, rfl⟩
  have h2 : (0 : ℚ) < c ^ 2 := by positivity
  nlinarith

theorem isSqClass_third_coordinate {X Y : ℚ} (h : shortW.Nonsingular X Y) (hY : Y ≠ 0) :
    IsSqClass ((X - 12) * (X + 4)) (X + 13) := by
  have heq : Y ^ 2 = (X - 12) * (X + 4) * (X + 13) := (equation_shortW_iff X Y).mp h.1
  obtain ⟨h12, h4, -⟩ := factors_ne_zero h hY
  have hne : (X - 12) * (X + 4) ≠ 0 := mul_ne_zero h12 h4
  refine ⟨Y / ((X - 12) * (X + 4)), div_ne_zero hY hne, ?_⟩
  rw [div_pow, eq_comm, ← mul_div_assoc, div_eq_iff (pow_ne_zero 2 hne)]
  linear_combination (X - 12) * (X + 4) * heq

theorem deltaPair_some_of_ne {X Y : ℚ} (h : shortW.Nonsingular X Y) (hY : Y ≠ 0) :
    deltaPair (.some X Y h) = (X - 12, X + 4) := by
  obtain ⟨h12, h4, _⟩ := factors_ne_zero h hY
  rw [deltaPair_some]
  have hX12 : X ≠ 12 := fun h0 => h12 (by rw [h0]; ring)
  have hX4 : X ≠ -4 := fun h0 => h4 (by rw [h0]; ring)
  rw [if_neg hX12, if_neg hX4]

theorem padicValRat_emod_two_of_isSqClass (p : ℕ) [Fact p.Prime] {d a : ℚ} (hd : d ≠ 0)
    (h : IsSqClass d a) : padicValRat p a % 2 = padicValRat p d % 2 := by
  obtain ⟨c, hc, rfl⟩ := h
  rw [padicValRat.mul hd (pow_ne_zero 2 hc), padicValRat.pow _]
  push_cast
  omega

theorem padicValRat_two_two : padicValRat 2 (2 : ℚ) = 1 := by
  rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num]
  exact padicValRat.self (by norm_num)

theorem padicValRat_three_three : padicValRat 3 (3 : ℚ) = 1 := by
  rw [show (3 : ℚ) = ((3 : ℕ) : ℚ) by norm_num]
  exact padicValRat.self (by norm_num)

scoped instance fact_prime_three : Fact (Nat.Prime 3) := ⟨by norm_num⟩

theorem not_isSqClass_one_two : ¬ IsSqClass 1 2 := by
  intro h
  have h2 := padicValRat_emod_two_of_isSqClass 2 one_ne_zero h
  rw [padicValRat_two_two, padicValRat.one] at h2
  omega

theorem not_isSqClass_one_three : ¬ IsSqClass 1 3 := by
  intro h
  have h2 := padicValRat_emod_two_of_isSqClass 3 one_ne_zero h
  rw [padicValRat_three_three, padicValRat.one] at h2
  omega

theorem not_isSqClass_two_of_isSqClass_one {a : ℚ} (ha : IsSqClass 1 a) : ¬ IsSqClass 2 a :=
  fun h => not_isSqClass_one_two (isSqClass_trans ha (isSqClass_symm (by norm_num) h))

theorem not_isSqClass_three_of_isSqClass_one {a : ℚ} (ha : IsSqClass 1 a) : ¬ IsSqClass 3 a :=
  fun h => not_isSqClass_one_three (isSqClass_trans ha (isSqClass_symm (by norm_num) h))

theorem zmod_nine_key :
    ∀ x y z : ZMod 9, x ^ 2 - 3 * y ^ 2 + 16 * z ^ 2 = 0 →
      3 * x = 0 ∧ 3 * y = 0 ∧ 3 * z = 0 := by
  decide

theorem zmod_five_key₁ :
    ∀ x z w : ZMod 5, 2 * x ^ 2 - 4 * z ^ 2 + 25 * w ^ 2 = 0 → x = 0 ∧ z = 0 := by
  decide

theorem zmod_five_key₂ :
    ∀ x y w : ZMod 5, 50 * x ^ 2 - 2 * y ^ 2 + 16 * w ^ 2 = 0 → y = 0 ∧ w = 0 := by
  decide

theorem zmod_four_key :
    ∀ x y w : ZMod 4, 4 * x ^ 2 - 2 * y ^ 2 - 3 * w ^ 2 = 0 → 2 * y = 0 ∧ 2 * w = 0 := by
  decide

theorem zmod_eight_key :
    ∀ x y w : ZMod 8, x ^ 2 - 2 * y ^ 2 - 3 * w ^ 2 = 0 → 4 * x = 0 := by
  decide

theorem three_dvd_of_zmod_nine {a : ℤ} (h : 3 * (a : ZMod 9) = 0) : (3 : ℤ) ∣ a := by
  have h1 : ((3 * a : ℤ) : ZMod 9) = 0 := by push_cast; linear_combination h
  have h2 : ((9 : ℕ) : ℤ) ∣ 3 * a := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 9).mp h1
  have h3 : (3 : ℤ) * 3 ∣ 3 * a := by exact_mod_cast h2
  exact (mul_dvd_mul_iff_left (show (3 : ℤ) ≠ 0 by norm_num)).mp h3

theorem five_dvd_of_zmod_five {a : ℤ} (h : (a : ZMod 5) = 0) : (5 : ℤ) ∣ a := by
  have h2 : ((5 : ℕ) : ℤ) ∣ a := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp h
  exact_mod_cast h2

theorem two_dvd_of_zmod_four {a : ℤ} (h : 2 * (a : ZMod 4) = 0) : (2 : ℤ) ∣ a := by
  have h1 : ((2 * a : ℤ) : ZMod 4) = 0 := by push_cast; linear_combination h
  have h2 : ((4 : ℕ) : ℤ) ∣ 2 * a := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp h1
  have h3 : (2 : ℤ) * 2 ∣ 2 * a := by exact_mod_cast h2
  exact (mul_dvd_mul_iff_left (show (2 : ℤ) ≠ 0 by norm_num)).mp h3

theorem two_dvd_of_zmod_eight {a : ℤ} (h : 4 * (a : ZMod 8) = 0) : (2 : ℤ) ∣ a := by
  have h1 : ((4 * a : ℤ) : ZMod 8) = 0 := by push_cast; linear_combination h
  have h2 : ((8 : ℕ) : ℤ) ∣ 4 * a := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp h1
  have h3 : (4 : ℤ) * 2 ∣ 4 * a := by exact_mod_cast h2
  exact (mul_dvd_mul_iff_left (show (4 : ℤ) ≠ 0 by norm_num)).mp h3

theorem hspaceOneThree_int :
    ∀ n : ℕ, ∀ a b c : ℤ, c.natAbs = n → c ≠ 0 → a ^ 2 - 3 * b ^ 2 + 16 * c ^ 2 ≠ 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rintro a b c rfl hc h
    have h9 : (a : ZMod 9) ^ 2 - 3 * (b : ZMod 9) ^ 2 + 16 * (c : ZMod 9) ^ 2 = 0 := by
      have h0 : ((a ^ 2 - 3 * b ^ 2 + 16 * c ^ 2 : ℤ) : ZMod 9) = 0 := by
        rw [h]; norm_num
      push_cast at h0
      linear_combination h0
    obtain ⟨hx, hy, hz⟩ := zmod_nine_key _ _ _ h9
    obtain ⟨a₁, rfl⟩ := three_dvd_of_zmod_nine hx
    obtain ⟨b₁, rfl⟩ := three_dvd_of_zmod_nine hy
    obtain ⟨c₁, rfl⟩ := three_dvd_of_zmod_nine hz
    have h9' : (9 : ℤ) * (a₁ ^ 2 - 3 * b₁ ^ 2 + 16 * c₁ ^ 2) = 0 := by linear_combination h
    have h' : a₁ ^ 2 - 3 * b₁ ^ 2 + 16 * c₁ ^ 2 = 0 :=
      (mul_eq_zero.mp h9').resolve_left (by norm_num)
    have hc₁ : c₁ ≠ 0 := fun h0 => hc (by rw [h0, mul_zero])
    exact ih c₁.natAbs (by omega) a₁ b₁ c₁ rfl hc₁ h'

theorem hspace_one_three_insoluble : ¬ ∃ z₁ z₂ : ℚ, z₁ ^ 2 - 3 * z₂ ^ 2 = -16 := by
  rintro ⟨z₁, z₂, h⟩
  have hd₁ : ((z₁.den : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr z₁.den_nz
  have hd₂ : ((z₂.den : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr z₂.den_nz
  have hn₁ : (z₁.num : ℚ) = z₁ * (z₁.den : ℚ) := (div_eq_iff hd₁).mp (Rat.num_div_den z₁)
  have hn₂ : (z₂.num : ℚ) = z₂ * (z₂.den : ℚ) := (div_eq_iff hd₂).mp (Rat.num_div_den z₂)
  refine hspaceOneThree_int ((z₁.den : ℤ) * (z₂.den : ℤ)).natAbs
    (z₁.num * (z₂.den : ℤ)) (z₂.num * (z₁.den : ℤ)) ((z₁.den : ℤ) * (z₂.den : ℤ)) rfl
    (mul_ne_zero (by exact_mod_cast z₁.den_nz) (by exact_mod_cast z₂.den_nz)) ?_
  have key : (((z₁.num * (z₂.den : ℤ)) ^ 2 - 3 * (z₂.num * (z₁.den : ℤ)) ^ 2
      + 16 * ((z₁.den : ℤ) * (z₂.den : ℤ)) ^ 2 : ℤ) : ℚ) = 0 := by
    push_cast
    rw [hn₁, hn₂]
    linear_combination ((z₁.den : ℚ) * (z₂.den : ℚ)) ^ 2 * h
  exact_mod_cast key

theorem hspaceTwoTwo_int :
    ∀ n : ℕ, ∀ a₁ a₂ a₃ c : ℤ, c.natAbs = n → c ≠ 0 →
      ¬ (2 * a₁ ^ 2 - 2 * a₂ ^ 2 + 16 * c ^ 2 = 0 ∧ 2 * a₁ ^ 2 - 4 * a₃ ^ 2 + 25 * c ^ 2 = 0) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rintro a₁ a₂ a₃ c rfl hc ⟨h₁, h₂⟩
    have h5A : 2 * (a₁ : ZMod 5) ^ 2 - 4 * (a₃ : ZMod 5) ^ 2 + 25 * (c : ZMod 5) ^ 2 = 0 := by
      have h0 : ((2 * a₁ ^ 2 - 4 * a₃ ^ 2 + 25 * c ^ 2 : ℤ) : ZMod 5) = 0 := by
        rw [h₂]; norm_num
      push_cast at h0
      linear_combination h0
    obtain ⟨hx, hz⟩ := zmod_five_key₁ _ _ _ h5A
    obtain ⟨b₁, rfl⟩ := five_dvd_of_zmod_five hx
    obtain ⟨b₃, rfl⟩ := five_dvd_of_zmod_five hz
    have h5B : 50 * (b₁ : ZMod 5) ^ 2 - 2 * (a₂ : ZMod 5) ^ 2 + 16 * (c : ZMod 5) ^ 2 = 0 := by
      have h0 : ((50 * b₁ ^ 2 - 2 * a₂ ^ 2 + 16 * c ^ 2 : ℤ) : ZMod 5) = 0 := by
        rw [show (50 * b₁ ^ 2 - 2 * a₂ ^ 2 + 16 * c ^ 2 : ℤ)
            = 2 * (5 * b₁) ^ 2 - 2 * a₂ ^ 2 + 16 * c ^ 2 by ring, h₁]
        norm_num
      push_cast at h0
      linear_combination h0
    obtain ⟨hy, hw⟩ := zmod_five_key₂ _ _ _ h5B
    obtain ⟨b₂, rfl⟩ := five_dvd_of_zmod_five hy
    obtain ⟨c₁, rfl⟩ := five_dvd_of_zmod_five hw
    have h₁' : 2 * b₁ ^ 2 - 2 * b₂ ^ 2 + 16 * c₁ ^ 2 = 0 := by
      have h25 : (25 : ℤ) * (2 * b₁ ^ 2 - 2 * b₂ ^ 2 + 16 * c₁ ^ 2) = 0 := by
        linear_combination h₁
      exact (mul_eq_zero.mp h25).resolve_left (by norm_num)
    have h₂' : 2 * b₁ ^ 2 - 4 * b₃ ^ 2 + 25 * c₁ ^ 2 = 0 := by
      have h25 : (25 : ℤ) * (2 * b₁ ^ 2 - 4 * b₃ ^ 2 + 25 * c₁ ^ 2) = 0 := by
        linear_combination h₂
      exact (mul_eq_zero.mp h25).resolve_left (by norm_num)
    have hc₁ : c₁ ≠ 0 := fun h0 => hc (by rw [h0, mul_zero])
    exact ih c₁.natAbs (by omega) b₁ b₂ b₃ c₁ rfl hc₁ ⟨h₁', h₂'⟩

theorem hspace_two_two_insoluble :
    ¬ ∃ z₁ z₂ z₃ : ℚ, 2 * z₁ ^ 2 - 2 * z₂ ^ 2 = -16 ∧ 2 * z₁ ^ 2 - 4 * z₃ ^ 2 = -25 := by
  rintro ⟨z₁, z₂, z₃, h₁, h₂⟩
  have hd₁ : ((z₁.den : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr z₁.den_nz
  have hd₂ : ((z₂.den : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr z₂.den_nz
  have hd₃ : ((z₃.den : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr z₃.den_nz
  have hn₁ : (z₁.num : ℚ) = z₁ * (z₁.den : ℚ) := (div_eq_iff hd₁).mp (Rat.num_div_den z₁)
  have hn₂ : (z₂.num : ℚ) = z₂ * (z₂.den : ℚ) := (div_eq_iff hd₂).mp (Rat.num_div_den z₂)
  have hn₃ : (z₃.num : ℚ) = z₃ * (z₃.den : ℚ) := (div_eq_iff hd₃).mp (Rat.num_div_den z₃)
  set D : ℤ := (z₁.den : ℤ) * (z₂.den : ℤ) * (z₃.den : ℤ) with hD
  have hDne : D ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_ <;> exact_mod_cast Rat.den_nz _
  refine hspaceTwoTwo_int D.natAbs
    (z₁.num * ((z₂.den : ℤ) * (z₃.den : ℤ)))
    (z₂.num * ((z₁.den : ℤ) * (z₃.den : ℤ)))
    (z₃.num * ((z₁.den : ℤ) * (z₂.den : ℤ))) D rfl hDne ⟨?_, ?_⟩
  · have key : ((2 * (z₁.num * ((z₂.den : ℤ) * (z₃.den : ℤ))) ^ 2
        - 2 * (z₂.num * ((z₁.den : ℤ) * (z₃.den : ℤ))) ^ 2 + 16 * D ^ 2 : ℤ) : ℚ) = 0 := by
      rw [hD]
      push_cast
      rw [hn₁, hn₂]
      linear_combination ((z₁.den : ℚ) * (z₂.den : ℚ) * (z₃.den : ℚ)) ^ 2 * h₁
    exact_mod_cast key
  · have key : ((2 * (z₁.num * ((z₂.den : ℤ) * (z₃.den : ℤ))) ^ 2
        - 4 * (z₃.num * ((z₁.den : ℤ) * (z₂.den : ℤ))) ^ 2 + 25 * D ^ 2 : ℤ) : ℚ) = 0 := by
      rw [hD]
      push_cast
      rw [hn₁, hn₃]
      linear_combination ((z₁.den : ℚ) * (z₂.den : ℚ) * (z₃.den : ℚ)) ^ 2 * h₂
    exact_mod_cast key

theorem hspaceTwoSix_int :
    ∀ n : ℕ, ∀ a₂ a₃ c : ℤ, c.natAbs = n → c ≠ 0 →
      4 * a₃ ^ 2 - 2 * a₂ ^ 2 - 3 * c ^ 2 ≠ 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rintro a₂ a₃ c rfl hc h
    have h4 : 4 * (a₃ : ZMod 4) ^ 2 - 2 * (a₂ : ZMod 4) ^ 2 - 3 * (c : ZMod 4) ^ 2 = 0 := by
      have h0 : ((4 * a₃ ^ 2 - 2 * a₂ ^ 2 - 3 * c ^ 2 : ℤ) : ZMod 4) = 0 := by
        rw [h]; norm_num
      push_cast at h0
      linear_combination h0
    obtain ⟨hy, hw⟩ := zmod_four_key _ _ _ h4
    obtain ⟨b₂, rfl⟩ := two_dvd_of_zmod_four hy
    obtain ⟨c₁, rfl⟩ := two_dvd_of_zmod_four hw
    have hq : a₃ ^ 2 - 2 * b₂ ^ 2 - 3 * c₁ ^ 2 = 0 := by
      have h4' : (4 : ℤ) * (a₃ ^ 2 - 2 * b₂ ^ 2 - 3 * c₁ ^ 2) = 0 := by linear_combination h
      exact (mul_eq_zero.mp h4').resolve_left (by norm_num)
    have h8 : (a₃ : ZMod 8) ^ 2 - 2 * (b₂ : ZMod 8) ^ 2 - 3 * (c₁ : ZMod 8) ^ 2 = 0 := by
      have h0 : ((a₃ ^ 2 - 2 * b₂ ^ 2 - 3 * c₁ ^ 2 : ℤ) : ZMod 8) = 0 := by
        rw [hq]; norm_num
      push_cast at h0
      linear_combination h0
    obtain ⟨b₃, rfl⟩ := two_dvd_of_zmod_eight (zmod_eight_key _ _ _ h8)
    have h' : 4 * b₃ ^ 2 - 2 * b₂ ^ 2 - 3 * c₁ ^ 2 = 0 := by
      have h4'' : (4 : ℤ) * (4 * b₃ ^ 2 - 2 * b₂ ^ 2 - 3 * c₁ ^ 2) = 0 := by
        linear_combination h
      exact (mul_eq_zero.mp h4'').resolve_left (by norm_num)
    have hc₁ : c₁ ≠ 0 := fun h0 => hc (by rw [h0, mul_zero])
    exact ih c₁.natAbs (by omega) b₂ b₃ c₁ rfl hc₁ h'

theorem hspace_two_six_insoluble : ¬ ∃ z₂ z₃ : ℚ, 12 * z₃ ^ 2 - 6 * z₂ ^ 2 = 9 := by
  rintro ⟨z₂, z₃, h⟩
  have h3 : 4 * z₃ ^ 2 - 2 * z₂ ^ 2 = 3 := by linarith
  have hd₂ : ((z₂.den : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr z₂.den_nz
  have hd₃ : ((z₃.den : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr z₃.den_nz
  have hn₂ : (z₂.num : ℚ) = z₂ * (z₂.den : ℚ) := (div_eq_iff hd₂).mp (Rat.num_div_den z₂)
  have hn₃ : (z₃.num : ℚ) = z₃ * (z₃.den : ℚ) := (div_eq_iff hd₃).mp (Rat.num_div_den z₃)
  refine hspaceTwoSix_int ((z₂.den : ℤ) * (z₃.den : ℤ)).natAbs
    (z₂.num * (z₃.den : ℤ)) (z₃.num * (z₂.den : ℤ)) ((z₂.den : ℤ) * (z₃.den : ℤ)) rfl
    (mul_ne_zero (by exact_mod_cast z₂.den_nz) (by exact_mod_cast z₃.den_nz)) ?_
  have key : ((4 * (z₃.num * (z₂.den : ℤ)) ^ 2 - 2 * (z₂.num * (z₃.den : ℤ)) ^ 2
      - 3 * ((z₂.den : ℤ) * (z₃.den : ℤ)) ^ 2 : ℤ) : ℚ) = 0 := by
    push_cast
    rw [hn₂, hn₃]
    linear_combination ((z₂.den : ℚ) * (z₃.den : ℚ)) ^ 2 * h3
  exact_mod_cast key

theorem isSqClass_one_fourHundred : IsSqClass 1 (400 : ℚ) := ⟨20, by norm_num, by norm_num⟩

theorem isSqClass_one_sixteen : IsSqClass 1 (16 : ℚ) := ⟨4, by norm_num, by norm_num⟩

theorem exists_witnesses {d₁ d₂ : ℚ} {X Y : ℚ} (h : shortW.Nonsingular X Y) (hY : Y ≠ 0)
    (h₁ : IsSqClass d₁ (X - 12)) (h₂ : IsSqClass d₂ (X + 4)) :
    ∃ z₁ z₂ z₃ : ℚ, X - 12 = d₁ * z₁ ^ 2 ∧ X + 4 = d₂ * z₂ ^ 2 ∧ X + 13 = d₁ * d₂ * z₃ ^ 2 := by
  obtain ⟨z₁, hz₁, e₁⟩ := h₁
  obtain ⟨z₂, hz₂, e₂⟩ := h₂
  have h3 : IsSqClass ((X - 12) * (X + 4)) (X + 13) := isSqClass_third_coordinate h hY
  have h3' : IsSqClass (d₁ * d₂) (X + 13) := by
    refine isSqClass_trans ⟨z₁ * z₂, mul_ne_zero hz₁ hz₂, ?_⟩ h3
    rw [e₁, e₂]; ring
  obtain ⟨z₃, _, e₃⟩ := h3'
  exact ⟨z₁, z₂, z₃, e₁, e₂, e₃⟩

theorem deltaPair_not_isSqClass_one_three (P : shortW.Point) :
    ¬ (IsSqClass 1 (deltaPair P).1 ∧ IsSqClass 3 (deltaPair P).2) := by
  rintro ⟨hP₁, hP₂⟩
  rcases P with _ | ⟨X, Y, h⟩
  · exact not_isSqClass_three_of_isSqClass_one (isSqClass_self 1) hP₂
  · by_cases hY : Y = 0
    · subst hY
      rw [deltaPair_some] at hP₂
      rcases two_torsion_abscissa h with rfl | rfl | rfl
      · norm_num at hP₂
        exact not_isSqClass_three_of_isSqClass_one isSqClass_one_sixteen hP₂
      · norm_num at hP₂
        exact not_isSqClass_of_pos_of_neg (by norm_num) (by norm_num) hP₂
      · norm_num at hP₂
        exact not_isSqClass_of_pos_of_neg (by norm_num) (by norm_num) hP₂
    · rw [deltaPair_some_of_ne h hY] at hP₁ hP₂
      obtain ⟨z₁, z₂, _, e₁, e₂, _⟩ := exists_witnesses h hY hP₁ hP₂
      exact hspace_one_three_insoluble ⟨z₁, z₂, by rw [one_mul] at e₁; nlinarith [e₁, e₂]⟩

theorem deltaPair_not_isSqClass_two_two (P : shortW.Point) :
    ¬ (IsSqClass 2 (deltaPair P).1 ∧ IsSqClass 2 (deltaPair P).2) := by
  rintro ⟨hP₁, hP₂⟩
  rcases P with _ | ⟨X, Y, h⟩
  · exact not_isSqClass_two_of_isSqClass_one (isSqClass_self 1) hP₁
  · by_cases hY : Y = 0
    · subst hY
      rw [deltaPair_some] at hP₁
      rcases two_torsion_abscissa h with rfl | rfl | rfl
      · norm_num at hP₁
        exact not_isSqClass_two_of_isSqClass_one isSqClass_one_fourHundred hP₁
      · norm_num at hP₁
        exact not_isSqClass_of_pos_of_neg (by norm_num) (by norm_num) hP₁
      · norm_num at hP₁
        exact not_isSqClass_of_pos_of_neg (by norm_num) (by norm_num) hP₁
    · rw [deltaPair_some_of_ne h hY] at hP₁ hP₂
      obtain ⟨z₁, z₂, z₃, e₁, e₂, e₃⟩ := exists_witnesses h hY hP₁ hP₂
      exact hspace_two_two_insoluble ⟨z₁, z₂, z₃, by nlinarith [e₁, e₂],
        by rw [show (2 : ℚ) * 2 = 4 by norm_num] at e₃; nlinarith [e₁, e₃]⟩

theorem deltaPair_not_isSqClass_two_six (P : shortW.Point) :
    ¬ (IsSqClass 2 (deltaPair P).1 ∧ IsSqClass 6 (deltaPair P).2) := by
  rintro ⟨hP₁, hP₂⟩
  rcases P with _ | ⟨X, Y, h⟩
  · exact not_isSqClass_two_of_isSqClass_one (isSqClass_self 1) hP₁
  · by_cases hY : Y = 0
    · subst hY
      rw [deltaPair_some] at hP₁
      rcases two_torsion_abscissa h with rfl | rfl | rfl
      · norm_num at hP₁
        exact not_isSqClass_two_of_isSqClass_one isSqClass_one_fourHundred hP₁
      · norm_num at hP₁
        exact not_isSqClass_of_pos_of_neg (by norm_num) (by norm_num) hP₁
      · norm_num at hP₁
        exact not_isSqClass_of_pos_of_neg (by norm_num) (by norm_num) hP₁
    · rw [deltaPair_some_of_ne h hY] at hP₁ hP₂
      obtain ⟨z₁, z₂, z₃, e₁, e₂, e₃⟩ := exists_witnesses h hY hP₁ hP₂
      exact hspace_two_six_insoluble ⟨z₂, z₃,
        by rw [show (2 : ℚ) * 6 = 12 by norm_num] at e₃; nlinarith [e₂, e₃]⟩

def selmerCandidates : Finset (ℤ × ℤ) :=
  {(1, 1), (-1, -1), (5, 1), (-5, -1),
   (1, 3), (-1, -3), (5, 3), (-5, -3),
   (2, 2), (-2, -2), (10, 2), (-10, -2),
   (2, 6), (-2, -6), (10, 6), (-10, -6)}

def torsionClasses : Finset (ℤ × ℤ) := {(1, 1), (-5, -1), (-1, -1), (5, 1)}

def killedReps : Finset (ℤ × ℤ) := {(1, 3), (2, 2), (2, 6)}

theorem selmerCandidates_coset_decomp :
    ∀ v ∈ selmerCandidates, v ∉ torsionClasses →
      ∃ r ∈ killedReps, ∃ w ∈ torsionClasses, v.1 = r.1 * w.1 ∧ v.2 = r.2 * w.2 := by
  decide

theorem deltaPair_not_isSqClass_killed (P : shortW.Point) :
    ∀ r ∈ killedReps, ¬ (IsSqClass ((r.1 : ℤ) : ℚ) (deltaPair P).1 ∧
      IsSqClass ((r.2 : ℤ) : ℚ) (deltaPair P).2) := by
  intro r hr
  simp only [killedReps, Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with rfl | rfl | rfl
  · exact_mod_cast deltaPair_not_isSqClass_one_three P
  · exact_mod_cast deltaPair_not_isSqClass_two_two P
  · exact_mod_cast deltaPair_not_isSqClass_two_six P

section PadicHelpers

variable {q : ℕ} [hq : Fact q.Prime]

omit hq in
theorem val_natCast_nonneg' (n : ℕ) : 0 ≤ padicValRat q (n : ℚ) :=
  zero_le_padicValRat_of_nat n

omit hq in
theorem val_intCast_nonneg' (n : ℤ) : 0 ≤ padicValRat q (n : ℚ) := by
  rw [padicValRat.of_int]
  exact Int.natCast_nonneg _

omit hq in
theorem val_natCast_eq_zero' {n : ℕ} (hn : ¬ q ∣ n) : padicValRat q (n : ℚ) = 0 := by
  rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hn, Nat.cast_zero]

theorem val_add_nonneg' {a b : ℚ} (ha : 0 ≤ padicValRat q a) (hb : 0 ≤ padicValRat q b) :
    0 ≤ padicValRat q (a + b) := by
  rcases eq_or_ne (a + b) 0 with h | h
  · rw [h, padicValRat.zero]
  · exact le_trans (le_min ha hb) (padicValRat.min_le_padicValRat_add h)

theorem val_add_eq_left' {a b : ℚ} (ha : a ≠ 0)
    (h : padicValRat q a < padicValRat q b) : padicValRat q (a + b) = padicValRat q a := by
  rcases eq_or_ne b 0 with rfl | hb
  · rw [add_zero]
  · have hab : a + b ≠ 0 := by
      intro h0
      have hba : b = -a := by linarith
      rw [hba, padicValRat.neg] at h
      exact lt_irrefl _ h
    exact padicValRat.add_eq_of_lt hab ha hb h

end PadicHelpers

theorem nat_sq_of_even_padicValNat :
    ∀ n : ℕ, n ≠ 0 → (∀ p : ℕ, p.Prime → Even (padicValNat p n)) → ∃ m : ℕ, n = m ^ 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn h
    rcases eq_or_ne n 1 with rfl | hn1
    · exact ⟨1, by norm_num⟩
    obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd hn1
    haveI : Fact p.Prime := ⟨hp⟩
    have hval1 : 1 ≤ padicValNat p n := one_le_padicValNat_of_dvd hn hpn
    have hval2 : 2 ≤ padicValNat p n := by
      obtain ⟨r, hr⟩ := h p hp
      omega
    obtain ⟨k, hk⟩ := (padicValNat_dvd_iff_le hn).mpr hval2
    have hk0 : k ≠ 0 := by rintro rfl; exact hn (by rw [hk, mul_zero])
    have hp0 : p ^ 2 ≠ 0 := pow_ne_zero 2 hp.ne_zero
    have hklt : k < n := by
      have h4 : 4 * k ≤ p ^ 2 * k :=
        Nat.mul_le_mul (by nlinarith [hp.two_le]) (le_refl k)
      omega
    have hkval : ∀ r : ℕ, r.Prime → Even (padicValNat r k) := by
      intro r hr
      haveI : Fact r.Prime := ⟨hr⟩
      have hsum : padicValNat r n = padicValNat r (p ^ 2) + padicValNat r k := by
        rw [hk]; exact padicValNat.mul hp0 hk0
      rcases eq_or_ne r p with rfl | hrp
      · rw [padicValNat.prime_pow] at hsum
        obtain ⟨s, hs⟩ := h r hr
        exact ⟨s - 1, by omega⟩
      · rw [padicValNat.pow _ 2, padicValNat_primes hrp, mul_zero, zero_add] at hsum
        rw [← hsum]; exact h r hr
    obtain ⟨m, hm⟩ := ih k hklt hk0 hkval
    exact ⟨p * m, by rw [hk, hm]; ring⟩

theorem exists_sq_of_even_padicValRat_of_pos {a : ℚ} (ha : 0 < a)
    (h : ∀ p : ℕ, p.Prime → Even (padicValRat p a)) : ∃ c : ℚ, c ≠ 0 ∧ a = c ^ 2 := by
  have hnum : (0 : ℤ) < a.num := Rat.num_pos.mpr ha
  have hden : a.den ≠ 0 := a.den_nz
  have hnumabs : a.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hnum.ne'
  have hkey : ∀ p : ℕ, p.Prime →
      Even (padicValNat p a.num.natAbs) ∧ Even (padicValNat p a.den) := by
    intro p hp
    haveI : Fact p.Prime := ⟨hp⟩
    have hval : padicValRat p a =
        (padicValNat p a.num.natAbs : ℤ) - (padicValNat p a.den : ℤ) := rfl
    have heven := h p hp
    rw [hval] at heven
    have hcop : ¬ (p ∣ a.num.natAbs ∧ p ∣ a.den) := by
      rintro ⟨h1, h2⟩
      have hgcd : Nat.gcd a.num.natAbs a.den = 1 := a.reduced
      exact hp.ne_one (Nat.dvd_one.mp (hgcd ▸ Nat.dvd_gcd h1 h2))
    rw [Int.even_sub] at heven
    rcases not_and_or.mp hcop with h1 | h1
    · have hz : padicValNat p a.num.natAbs = 0 := padicValNat.eq_zero_of_not_dvd h1
      refine ⟨by rw [hz]; exact Even.zero, ?_⟩
      have : Even ((padicValNat p a.den : ℤ)) := heven.mp (by rw [hz]; exact Even.zero)
      exact_mod_cast this
    · have hz : padicValNat p a.den = 0 := padicValNat.eq_zero_of_not_dvd h1
      refine ⟨?_, by rw [hz]; exact Even.zero⟩
      have : Even ((padicValNat p a.num.natAbs : ℤ)) := heven.mpr (by rw [hz]; exact Even.zero)
      exact_mod_cast this
  obtain ⟨s, hs⟩ := nat_sq_of_even_padicValNat a.num.natAbs hnumabs fun p hp => (hkey p hp).1
  obtain ⟨t, ht⟩ := nat_sq_of_even_padicValNat a.den hden fun p hp => (hkey p hp).2
  have hs0 : (s : ℚ) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    rintro rfl
    exact hnumabs (by rw [hs]; norm_num)
  have ht0 : (t : ℚ) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    rintro rfl
    exact hden (by rw [ht]; norm_num)
  refine ⟨(s : ℚ) / (t : ℚ), div_ne_zero hs0 ht0, ?_⟩
  have hnum' : (a.num : ℚ) = (s : ℚ) ^ 2 := by
    have hcast : (a.num.natAbs : ℤ) = a.num := Int.natAbs_of_nonneg hnum.le
    rw [← hcast, hs]; push_cast; ring
  have hden' : (a.den : ℚ) = (t : ℚ) ^ 2 := by rw [ht]; push_cast; ring
  rw [div_pow, ← hnum', ← hden', Rat.num_div_den]

def sgn (a : ℚ) : ℤ := if 0 < a then 1 else -1

def vparity (q : ℕ) (a : ℚ) : ℕ := (padicValRat q a % 2).toNat

def canonRep (p : ℕ) (a : ℚ) : ℤ := sgn a * 2 ^ vparity 2 a * (p : ℤ) ^ vparity p a

theorem sgn_eq_one_or_neg_one (a : ℚ) : sgn a = 1 ∨ sgn a = -1 := by
  unfold sgn; split <;> simp

theorem vparity_le_one (q : ℕ) (a : ℚ) : vparity q a ≤ 1 := by
  unfold vparity
  omega

theorem sgn_congr {a b : ℚ} (h : 0 < a ↔ 0 < b) : sgn a = sgn b := by
  unfold sgn
  by_cases ha : 0 < a
  · rw [if_pos ha, if_pos (h.mp ha)]
  · rw [if_neg ha, if_neg (fun hb => ha (h.mpr hb))]

theorem vparity_congr {q : ℕ} {a b : ℚ}
    (h : padicValRat q a % 2 = padicValRat q b % 2) : vparity q a = vparity q b := by
  unfold vparity
  rw [h]

theorem canonRep_pos_iff {p : ℕ} (hp : p.Prime) (a : ℚ) :
    canonRep p a ≠ 0 ∧ (0 < canonRep p a ↔ 0 < a) := by
  have hppos : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp.pos
  have hpow : (0 : ℤ) < 2 ^ vparity 2 a * (p : ℤ) ^ vparity p a := by positivity
  unfold canonRep sgn
  split
  · exact ⟨by nlinarith, ⟨fun _ => ‹0 < a›, fun _ => by nlinarith⟩⟩
  · exact ⟨by nlinarith, ⟨fun h' => by nlinarith, fun h' => absurd h' ‹¬ 0 < a›⟩⟩

theorem padicValRat_canonRep {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (a : ℚ)
    (q : ℕ) (hqq : q.Prime) :
    padicValRat q ((canonRep p a : ℤ) : ℚ) =
      (if q = 2 then (vparity 2 a : ℤ) else 0) + (if q = p then (vparity p a : ℤ) else 0) := by
  haveI : Fact q.Prime := ⟨hqq⟩
  have h2 : ((2 : ℕ) : ℚ) ≠ 0 := by norm_num
  have hpQ : ((p : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hcast : ((canonRep p a : ℤ) : ℚ) =
      ((sgn a : ℤ) : ℚ) * ((2 : ℕ) : ℚ) ^ vparity 2 a * ((p : ℕ) : ℚ) ^ vparity p a := by
    unfold canonRep; push_cast; ring
  have hsgn : ((sgn a : ℤ) : ℚ) ≠ 0 := by
    rcases sgn_eq_one_or_neg_one a with h | h <;> rw [h] <;> norm_num
  have hvalsgn : padicValRat q ((sgn a : ℤ) : ℚ) = 0 := by
    rcases sgn_eq_one_or_neg_one a with h | h <;> rw [h]
    · norm_num
    · rw [show (((-1 : ℤ) : ℚ)) = -(1 : ℚ) by norm_num, padicValRat.neg, padicValRat.one]
  have hval2 : padicValRat q (((2 : ℕ) : ℚ) ^ vparity 2 a) =
      (if q = 2 then (vparity 2 a : ℤ) else 0) := by
    rw [padicValRat.pow _]
    by_cases hq2 : q = 2
    · subst hq2
      rw [if_pos rfl, padicValRat.self (by norm_num)]
      ring
    · rw [if_neg hq2, val_natCast_eq_zero'
        (fun hdvd => hq2 ((Nat.prime_dvd_prime_iff_eq hqq (by norm_num)).mp hdvd))]
      ring
  have hvalp : padicValRat q (((p : ℕ) : ℚ) ^ vparity p a) =
      (if q = p then (vparity p a : ℤ) else 0) := by
    rw [padicValRat.pow _]
    by_cases hqp : q = p
    · subst hqp
      rw [if_pos rfl, padicValRat.self hqq.one_lt]
      ring
    · rw [if_neg hqp, val_natCast_eq_zero'
        (fun hdvd => hqp ((Nat.prime_dvd_prime_iff_eq hqq hp).mp hdvd))]
      ring
  rw [hcast, padicValRat.mul (mul_ne_zero hsgn (pow_ne_zero _ h2)) (pow_ne_zero _ hpQ),
    padicValRat.mul hsgn (pow_ne_zero _ h2), hvalsgn, hval2, hvalp, zero_add]

theorem isSqClass_canonRep {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {a : ℚ} (ha : a ≠ 0)
    (h : ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ p → Even (padicValRat q a)) :
    IsSqClass ((canonRep p a : ℤ) : ℚ) a := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hd0', hdsign⟩ := canonRep_pos_iff hp a
  have hd0 : ((canonRep p a : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hd0'
  have hquot_pos : 0 < a / ((canonRep p a : ℤ) : ℚ) := by
    rcases lt_or_gt_of_ne ha with hneg | hpos
    · refine div_pos_of_neg_of_neg hneg ?_
      have : ¬ (0 < canonRep p a) := fun hcontra => absurd (hdsign.mp hcontra) (by linarith)
      have h1 : canonRep p a < 0 := lt_of_le_of_ne (not_lt.mp this) hd0'
      exact_mod_cast h1
    · refine div_pos hpos ?_
      exact_mod_cast hdsign.mpr hpos
  have hquot_even : ∀ r : ℕ, r.Prime → Even (padicValRat r (a / ((canonRep p a : ℤ) : ℚ))) := by
    intro r hrr
    haveI : Fact r.Prime := ⟨hrr⟩
    rw [padicValRat.div ha hd0, padicValRat_canonRep hp hp2 a r hrr]
    by_cases hr2 : r = 2
    · subst hr2
      rw [if_pos rfl, if_neg (Ne.symm hp2)]
      unfold vparity
      have h01 := Int.emod_two_eq_zero_or_one (padicValRat 2 a)
      rw [Int.even_iff]
      omega
    · by_cases hrp : r = p
      · subst hrp
        rw [if_neg hr2, if_pos rfl]
        unfold vparity
        have h01 := Int.emod_two_eq_zero_or_one (padicValRat r a)
        rw [Int.even_iff]
        omega
      · rw [if_neg hr2, if_neg hrp]
        simpa using h r hrr hr2 hrp
  obtain ⟨c, hc, hc2⟩ := exists_sq_of_even_padicValRat_of_pos hquot_pos hquot_even
  exact ⟨c, hc, by linear_combination (div_eq_iff hd0).mp hc2⟩

theorem support_sixteen {q : ℕ} (hq : q.Prime) (h2 : q ≠ 2) : ¬ q ∣ 16 := fun h =>
  h2 ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp
    (hq.dvd_of_dvd_pow (n := 4) ((by norm_num : (16 : ℕ) = 2 ^ 4) ▸ h)))

theorem support_twentyfive {q : ℕ} (hq : q.Prime) (h5 : q ≠ 5) : ¬ q ∣ 25 := fun h =>
  h5 ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp
    (hq.dvd_of_dvd_pow (n := 2) ((by norm_num : (25 : ℕ) = 5 ^ 2) ▸ h)))

theorem support_nine {q : ℕ} (hq : q.Prime) (h3 : q ≠ 3) : ¬ q ∣ 9 := fun h =>
  h3 ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp
    (hq.dvd_of_dvd_pow (n := 2) ((by norm_num : (9 : ℕ) = 3 ^ 2) ▸ h)))

section EvenValuation

variable {q : ℕ} [hq : Fact q.Prime]

theorem val_sum_eq {X Y : ℚ} (h : shortW.Nonsingular X Y) (hY : Y ≠ 0) :
    padicValRat q (X - 12) + padicValRat q (X + 4) + padicValRat q (X + 13) =
      2 * padicValRat q Y := by
  obtain ⟨h12, h4, h13⟩ := factors_ne_zero h hY
  have heq : Y ^ 2 = (X - 12) * (X + 4) * (X + 13) := (equation_shortW_iff X Y).mp h.1
  have hcong := congrArg (padicValRat q) heq
  rw [padicValRat.pow _, padicValRat.mul (mul_ne_zero h12 h4) h13,
    padicValRat.mul h12 h4] at hcong
  push_cast at hcong
  omega

theorem even_val_of_neg {X Y : ℚ} (h : shortW.Nonsingular X Y) (hY : Y ≠ 0)
    (hX : padicValRat q X < 0) :
    Even (padicValRat q (X - 12)) ∧ Even (padicValRat q (X + 4)) ∧
      Even (padicValRat q (X + 13)) := by
  have hX0 : X ≠ 0 := by
    rintro rfl
    rw [padicValRat.zero] at hX
    exact lt_irrefl _ hX
  have hfac : ∀ c : ℚ, c ≠ 0 → 0 ≤ padicValRat q c →
      padicValRat q (X + c) = padicValRat q X := fun c hc hcv =>
    val_add_eq_left' hX0 (lt_of_lt_of_le hX hcv)
  have h12 : padicValRat q (X - 12) = padicValRat q X := by
    rw [show X - (12 : ℚ) = X + (-12 : ℚ) by ring]
    exact hfac (-12) (by norm_num)
      (by rw [show (-12 : ℚ) = -((12 : ℕ) : ℚ) by norm_num, padicValRat.neg]
          exact val_natCast_nonneg' 12)
  have h4 : padicValRat q (X + 4) = padicValRat q X := by
    rw [show (4 : ℚ) = ((4 : ℕ) : ℚ) by norm_num]
    exact hfac _ (by norm_num) (val_natCast_nonneg' 4)
  have h13 : padicValRat q (X + 13) = padicValRat q X := by
    rw [show (13 : ℚ) = ((13 : ℕ) : ℚ) by norm_num]
    exact hfac _ (by norm_num) (val_natCast_nonneg' 13)
  have hsum := val_sum_eq (q := q) h hY
  rw [h12, h4, h13] at hsum
  have heven : Even (padicValRat q X) := by
    rw [Int.even_iff]
    omega
  exact ⟨h12 ▸ heven, h4 ▸ heven, h13 ▸ heven⟩

theorem even_val_of_nonneg {α c₁ c₂ Y : ℚ}
    (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0)
    (hvc₁ : padicValRat q c₁ = 0) (hvc₂ : padicValRat q c₂ = 0)
    (hsum : padicValRat q α + padicValRat q (α + c₁) + padicValRat q (α + c₂) =
      2 * padicValRat q Y)
    (hint : 0 ≤ padicValRat q α) :
    Even (padicValRat q α) := by
  rcases eq_or_lt_of_le hint with hz | hpos
  · rw [← hz]; exact Even.zero
  have h1 : padicValRat q (α + c₁) = 0 := by
    rw [add_comm, val_add_eq_left' hc₁ (by rw [hvc₁]; exact hpos)]
    exact hvc₁
  have h2 : padicValRat q (α + c₂) = 0 := by
    rw [add_comm, val_add_eq_left' hc₂ (by rw [hvc₂]; exact hpos)]
    exact hvc₂
  rw [h1, h2] at hsum
  rw [Int.even_iff]
  omega

theorem even_padicValRat_sub_twelve {X Y : ℚ} (h : shortW.Nonsingular X Y) (hY : Y ≠ 0)
    (hq2 : q ≠ 2) (hq5 : q ≠ 5) : Even (padicValRat q (X - 12)) := by
  rcases lt_or_ge (padicValRat q X) 0 with hX | hX
  · exact (even_val_of_neg h hY hX).1
  · have hint : 0 ≤ padicValRat q (X - 12) := by
      rw [show X - (12 : ℚ) = X + ((-12 : ℤ) : ℚ) by push_cast; ring]
      exact val_add_nonneg' hX (val_intCast_nonneg' (-12))
    have hsum := val_sum_eq (q := q) h hY
    refine even_val_of_nonneg (α := X - 12) (c₁ := 16) (c₂ := 25) (Y := Y)
      (by norm_num) (by norm_num) ?_ ?_ ?_ hint
    · rw [show (16 : ℚ) = ((16 : ℕ) : ℚ) by norm_num]
      exact val_natCast_eq_zero' (support_sixteen hq.out hq2)
    · rw [show (25 : ℚ) = ((25 : ℕ) : ℚ) by norm_num]
      exact val_natCast_eq_zero' (support_twentyfive hq.out hq5)
    · rw [show X - 12 + 16 = X + 4 by ring, show X - 12 + 25 = X + 13 by ring]
      exact hsum

theorem even_padicValRat_add_four {X Y : ℚ} (h : shortW.Nonsingular X Y) (hY : Y ≠ 0)
    (hq2 : q ≠ 2) (hq3 : q ≠ 3) : Even (padicValRat q (X + 4)) := by
  rcases lt_or_ge (padicValRat q X) 0 with hX | hX
  · exact (even_val_of_neg h hY hX).2.1
  · have hint : 0 ≤ padicValRat q (X + 4) := by
      rw [show (4 : ℚ) = ((4 : ℤ) : ℚ) by push_cast; ring]
      exact val_add_nonneg' hX (val_intCast_nonneg' 4)
    have hsum := val_sum_eq (q := q) h hY
    refine even_val_of_nonneg (α := X + 4) (c₁ := -16) (c₂ := 9) (Y := Y)
      (by norm_num) (by norm_num) ?_ ?_ ?_ hint
    · rw [show (-16 : ℚ) = -((16 : ℕ) : ℚ) by norm_num, padicValRat.neg]
      exact val_natCast_eq_zero' (support_sixteen hq.out hq2)
    · rw [show (9 : ℚ) = ((9 : ℕ) : ℚ) by norm_num]
      exact val_natCast_eq_zero' (support_nine hq.out hq3)
    · rw [show X + 4 + -16 = X - 12 by ring, show X + 4 + 9 = X + 13 by ring]
      omega

theorem even_padicValRat_add_thirteen {X Y : ℚ} (h : shortW.Nonsingular X Y) (hY : Y ≠ 0)
    (hq3 : q ≠ 3) (hq5 : q ≠ 5) : Even (padicValRat q (X + 13)) := by
  rcases lt_or_ge (padicValRat q X) 0 with hX | hX
  · exact (even_val_of_neg h hY hX).2.2
  · have hint : 0 ≤ padicValRat q (X + 13) := by
      rw [show (13 : ℚ) = ((13 : ℤ) : ℚ) by push_cast; ring]
      exact val_add_nonneg' hX (val_intCast_nonneg' 13)
    have hsum := val_sum_eq (q := q) h hY
    refine even_val_of_nonneg (α := X + 13) (c₁ := -25) (c₂ := -9) (Y := Y)
      (by norm_num) (by norm_num) ?_ ?_ ?_ hint
    · rw [show (-25 : ℚ) = -((25 : ℕ) : ℚ) by norm_num, padicValRat.neg]
      exact val_natCast_eq_zero' (support_twentyfive hq.out hq5)
    · rw [show (-9 : ℚ) = -((9 : ℕ) : ℚ) by norm_num, padicValRat.neg]
      exact val_natCast_eq_zero' (support_nine hq.out hq3)
    · rw [show X + 13 + -25 = X - 12 by ring, show X + 13 + -9 = X + 4 by ring]
      omega

end EvenValuation

theorem sign_constraint {X Y : ℚ} (h : shortW.Nonsingular X Y) (hY : Y ≠ 0) :
    0 < (X - 12) * (X + 4) := by
  obtain ⟨h12, h4, h13⟩ := factors_ne_zero h hY
  have heq : Y ^ 2 = (X - 12) * (X + 4) * (X + 13) := (equation_shortW_iff X Y).mp h.1
  have hY2 : 0 < Y ^ 2 := by positivity
  have h13pos : 0 < X + 13 := by
    rcases lt_or_gt_of_ne h13 with hneg | hpos
    · exfalso
      have ha : (0 : ℚ) < -(X - 12) := by linarith
      have hb : (0 : ℚ) < -(X + 4) := by linarith
      have hc : (0 : ℚ) < -(X + 13) := by linarith
      nlinarith [mul_pos (mul_pos ha hb) hc]
    · exact hpos
  nlinarith [mul_pos hY2 h13pos]

theorem sign_constraint' {X Y : ℚ} (h : shortW.Nonsingular X Y) (hY : Y ≠ 0) :
    (0 < X - 12 ↔ 0 < X + 4) := by
  obtain ⟨h12, h4, _⟩ := factors_ne_zero h hY
  have hprod := sign_constraint h hY
  constructor
  · intro h1
    rcases lt_or_gt_of_ne h4 with h2 | h2
    · nlinarith [mul_pos h1 (show (0 : ℚ) < -(X + 4) by linarith)]
    · exact h2
  · intro h1
    rcases lt_or_gt_of_ne h12 with h2 | h2
    · nlinarith [mul_pos (show (0 : ℚ) < -(X - 12) by linarith) h1]
    · exact h2

theorem parity_constraint {X Y : ℚ} (h : shortW.Nonsingular X Y) (hY : Y ≠ 0) :
    padicValRat 2 (X - 12) % 2 = padicValRat 2 (X + 4) % 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hsum := val_sum_eq (q := 2) h hY
  have h13 : Even (padicValRat 2 (X + 13)) :=
    even_padicValRat_add_thirteen h hY (by norm_num) (by norm_num)
  rw [Int.even_iff] at h13
  omega

theorem canonical_pair_mem (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (j k₁ k₂ : ℕ) (hj : j ≤ 1) (hk₁ : k₁ ≤ 1) (hk₂ : k₂ ≤ 1) :
    (ε * 2 ^ j * (5 : ℤ) ^ k₁, ε * 2 ^ j * (3 : ℤ) ^ k₂) ∈ selmerCandidates := by
  interval_cases j <;> interval_cases k₁ <;> interval_cases k₂ <;>
    rcases hε with rfl | rfl <;> decide

theorem canonRep_mem_selmerCandidates {X Y : ℚ} (h : shortW.Nonsingular X Y) (hY : Y ≠ 0) :
    (canonRep 5 (X - 12), canonRep 3 (X + 4)) ∈ selmerCandidates := by
  unfold canonRep
  rw [sgn_congr (sign_constraint' h hY), vparity_congr (parity_constraint h hY)]
  exact canonical_pair_mem (sgn (X + 4)) (sgn_eq_one_or_neg_one _) (vparity 2 (X + 4))
    (vparity 5 (X - 12)) (vparity 3 (X + 4)) (vparity_le_one _ _) (vparity_le_one _ _)
    (vparity_le_one _ _)

theorem deltaPairImageRefined (P : shortW.Point) :
    ∃ v ∈ selmerCandidates,
      IsSqClass (v.1 : ℚ) (deltaPair P).1 ∧ IsSqClass (v.2 : ℚ) (deltaPair P).2 := by
  rcases P with _ | ⟨X, Y, h⟩
  · refine ⟨(1, 1), by decide, ⟨1, one_ne_zero, ?_⟩, ⟨1, one_ne_zero, ?_⟩⟩ <;>
      norm_num [deltaPair]
  · by_cases hY : Y = 0
    · subst hY
      rcases two_torsion_abscissa h with rfl | rfl | rfl
      · refine ⟨(1, 1), by decide, ?_⟩
        rw [deltaPair_some]
        refine ⟨?_, ?_⟩ <;> norm_num
        · exact ⟨20, by norm_num, by norm_num⟩
        · exact ⟨4, by norm_num, by norm_num⟩
      · refine ⟨(-1, -1), by decide, ?_⟩
        rw [deltaPair_some]
        refine ⟨?_, ?_⟩ <;> norm_num
        · exact ⟨4, by norm_num, by norm_num⟩
        · exact ⟨12, by norm_num, by norm_num⟩
      · refine ⟨(-1, -1), by decide, ?_⟩
        rw [deltaPair_some]
        refine ⟨?_, ?_⟩ <;> norm_num
        · exact ⟨5, by norm_num, by norm_num⟩
        · exact ⟨3, by norm_num, by norm_num⟩
    · obtain ⟨h12, h4, h13⟩ := factors_ne_zero h hY
      refine ⟨(canonRep 5 (X - 12), canonRep 3 (X + 4)),
        canonRep_mem_selmerCandidates h hY, ?_⟩
      rw [deltaPair_some_of_ne h hY]
      exact ⟨isSqClass_canonRep (by norm_num) (by norm_num) h12
          (fun r hr hr2 hr5 => by
            haveI : Fact r.Prime := ⟨hr⟩
            exact even_padicValRat_sub_twelve h hY hr2 hr5),
        isSqClass_canonRep (by norm_num) (by norm_num) h4
          (fun r hr hr2 hr3 => by
            haveI : Fact r.Prime := ⟨hr⟩
            exact even_padicValRat_add_four h hY hr2 hr3)⟩

theorem nonsingular_genS : shortW.Nonsingular (-8) 20 := by
  rw [nonsingular_iff, equation_iff]
  simp only [shortW_a₁, shortW_a₂, shortW_a₃, shortW_a₄, shortW_a₆]
  norm_num

theorem nonsingular_tS : shortW.Nonsingular (-4) 0 := by
  rw [nonsingular_iff, equation_iff]
  simp only [shortW_a₁, shortW_a₂, shortW_a₃, shortW_a₄, shortW_a₆]
  norm_num

theorem nonsingular_genAddTS : shortW.Nonsingular 32 180 := by
  rw [nonsingular_iff, equation_iff]
  simp only [shortW_a₁, shortW_a₂, shortW_a₃, shortW_a₄, shortW_a₆]
  norm_num

def genS : shortW.Point := .some (-8) 20 nonsingular_genS

def tS : shortW.Point := .some (-4) 0 nonsingular_tS

def gtS : shortW.Point := .some 32 180 nonsingular_genAddTS

theorem isSqClass_deltaPair_genS :
    IsSqClass (-5) (deltaPair genS).1 ∧ IsSqClass (-1) (deltaPair genS).2 := by
  rw [genS, deltaPair_some]
  norm_num
  exact ⟨⟨2, by norm_num, by norm_num⟩, ⟨2, by norm_num, by norm_num⟩⟩

theorem isSqClass_deltaPair_tS :
    IsSqClass (-1) (deltaPair tS).1 ∧ IsSqClass (-1) (deltaPair tS).2 := by
  rw [tS, deltaPair_some]
  norm_num
  exact ⟨⟨4, by norm_num, by norm_num⟩, ⟨12, by norm_num, by norm_num⟩⟩

theorem isSqClass_deltaPair_gtS :
    IsSqClass 5 (deltaPair gtS).1 ∧ IsSqClass 1 (deltaPair gtS).2 := by
  rw [gtS, deltaPair_some]
  norm_num
  exact ⟨⟨2, by norm_num, by norm_num⟩, ⟨6, by norm_num, by norm_num⟩⟩

theorem isSqClass_mul_of_eq_mul {d r w a b : ℚ} (hd : d = r * w) (hw : w ≠ 0)
    (ha : IsSqClass d a) (hb : IsSqClass w b) : IsSqClass r (a * b) := by
  subst hd
  obtain ⟨c₁, hc₁, rfl⟩ := ha
  obtain ⟨c₂, hc₂, rfl⟩ := hb
  exact ⟨w * (c₁ * c₂), mul_ne_zero hw (mul_ne_zero hc₁ hc₂), by ring⟩

theorem isSqClass_deltaPair_add_of_isSqClass {d₁ d₂ r₁ r₂ w₁ w₂ : ℚ} (P t : shortW.Point)
    (hd₁ : d₁ = r₁ * w₁) (hd₂ : d₂ = r₂ * w₂) (hw₁ : w₁ ≠ 0) (hw₂ : w₂ ≠ 0)
    (ht₁ : IsSqClass w₁ (deltaPair t).1) (ht₂ : IsSqClass w₂ (deltaPair t).2)
    (hP₁ : IsSqClass d₁ (deltaPair P).1) (hP₂ : IsSqClass d₂ (deltaPair P).2) :
    IsSqClass r₁ (deltaPair (P + t)).1 ∧ IsSqClass r₂ (deltaPair (P + t)).2 :=
  ⟨isSqClass_trans (isSqClass_mul_of_eq_mul hd₁ hw₁ hP₁ ht₁)
      (ModularCurve.FifteenA1.deltaPairHom P t).1,
    isSqClass_trans (isSqClass_mul_of_eq_mul hd₂ hw₂ hP₂ ht₂)
      (ModularCurve.FifteenA1.deltaPairHom P t).2⟩

theorem deltaPairCosetTransport (P : shortW.Point) (r w : ℤ × ℤ) (hw : w ∈ torsionClasses)
    (hP : IsSqClass ((r.1 * w.1 : ℤ) : ℚ) (deltaPair P).1 ∧
      IsSqClass ((r.2 * w.2 : ℤ) : ℚ) (deltaPair P).2) :
    ∃ Q : shortW.Point,
      IsSqClass ((r.1 : ℤ) : ℚ) (deltaPair Q).1 ∧ IsSqClass ((r.2 : ℤ) : ℚ) (deltaPair Q).2 := by
  simp only [torsionClasses, Finset.mem_insert, Finset.mem_singleton] at hw
  obtain rfl | rfl | rfl | rfl := hw
  · exact ⟨P, by simpa using hP.1, by simpa using hP.2⟩
  · exact ⟨P + genS, isSqClass_deltaPair_add_of_isSqClass P genS
      (by push_cast; ring) (by push_cast; ring) (by norm_num) (by norm_num)
      isSqClass_deltaPair_genS.1 isSqClass_deltaPair_genS.2 hP.1 hP.2⟩
  · exact ⟨P + tS, isSqClass_deltaPair_add_of_isSqClass P tS
      (by push_cast; ring) (by push_cast; ring) (by norm_num) (by norm_num)
      isSqClass_deltaPair_tS.1 isSqClass_deltaPair_tS.2 hP.1 hP.2⟩
  · exact ⟨P + gtS, isSqClass_deltaPair_add_of_isSqClass P gtS
      (by push_cast; ring) (by push_cast; ring) (by norm_num) (by norm_num)
      isSqClass_deltaPair_gtS.1 isSqClass_deltaPair_gtS.2 hP.1 hP.2⟩

theorem deltaPair_mem_torsionClasses (P : shortW.Point) :
    ∃ v ∈ torsionClasses,
      IsSqClass (v.1 : ℚ) (deltaPair P).1 ∧ IsSqClass (v.2 : ℚ) (deltaPair P).2 := by
  obtain ⟨v, hv, hP⟩ := deltaPairImageRefined P
  by_cases hvt : v ∈ torsionClasses
  · exact ⟨v, hvt, hP⟩
  · exfalso
    obtain ⟨r, hr, w, hw, h1, h2⟩ := selmerCandidates_coset_decomp v hv hvt
    obtain ⟨Q, hQ⟩ := deltaPairCosetTransport P r w hw (by rw [← h1, ← h2]; exact hP)
    exact deltaPair_not_isSqClass_killed Q r hr hQ

theorem selmerBound (P : shortW.Point) :
    ∃ v ∈ V₀, IsSqClass v.1 (deltaPair P).1 ∧ IsSqClass v.2 (deltaPair P).2 := by
  obtain ⟨v, hv, h1, h2⟩ := deltaPair_mem_torsionClasses P
  refine ⟨((v.1 : ℚ), (v.2 : ℚ)), ?_, h1, h2⟩
  simp only [torsionClasses, Finset.mem_insert, Finset.mem_singleton] at hv
  obtain rfl | rfl | rfl | rfl := hv <;> simp [V₀]

end M4cP2.Selmer
p2m_reactivate "P2MW.S_ModularCurve_FifteenA1_selmerBound.M4cP2 P2MW.S_ModularCurve_FifteenA1_selmerBound.M4cP2.Selmer"
p2m_reactivate "P2MW.S_ModularCurve_FifteenA1_selmerBound.M4cP2"

open ModularCurve.FifteenA1

theorem solution (P : shortW.Point) : ∃ v ∈ V₀, IsSqClass v.1 (deltaPair P).1 ∧ IsSqClass v.2 (deltaPair P).2 :=
  M4cP2.Selmer.selmerBound P

end S_ModularCurve_FifteenA1_selmerBound
end P2MW
export P2MW.S_ModularCurve_FifteenA1_selmerBound (solution)
