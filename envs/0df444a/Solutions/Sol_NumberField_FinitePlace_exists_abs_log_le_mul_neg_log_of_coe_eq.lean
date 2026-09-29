-- Prove2me | solution 1 for NumberField.FinitePlace.exists_abs_log_le_mul_neg_log_of_coe_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/d57b303a-1677-52eb-9716-051e90e4dbcd

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_FinitePlace_exists_abs_log_le_mul_neg_log_of_coe_eq

set_option autoImplicit false

open NumberField

namespace AbsLogBound

variable {L : IntermediateField ℚ (AlgebraicClosure ℚ)} [NumberField ↥L] (ν : FinitePlace ↥L)

private theorem apply_le_one_of_isIntegral {x : ↥L} (hx : IsIntegral ℤ x) : ν x ≤ 1 := by
  rw [← ν.mk_maximalIdeal, FinitePlace.mk_apply]
  exact FinitePlace.norm_le_one (↥L) ν.maximalIdeal (⟨x, hx⟩ : 𝓞 ↥L)

private theorem apply_intCast_le_one (u : ℤ) : ν (u : ↥L) ≤ 1 :=
  apply_le_one_of_isIntegral ν (by simpa using isIntegral_algebraMap (R := ℤ) (A := ↥L) (x := u))

private theorem apply_natCast_le_one (n : ℕ) : ν (n : ↥L) ≤ 1 := by
  simpa using apply_intCast_le_one ν (n : ℤ)

private theorem apply_natCast_eq_one_of_not_dvd {p : ℕ} (hp : p.Prime) (hν : ν (p : ↥L) < 1) {n : ℕ}
    (hn : ¬ p ∣ n) : ν (n : ↥L) = 1 := by
  refine le_antisymm (apply_natCast_le_one ν n) ?_
  have hcop : Nat.Coprime p n := (Nat.Prime.coprime_iff_not_dvd hp).mpr hn
  have hbez : ((p : ℤ) * Nat.gcdA p n + (n : ℤ) * Nat.gcdB p n) = 1 := by
    have h := Nat.gcd_eq_gcd_ab p n
    rw [hcop.gcd_eq_one] at h
    exact_mod_cast h.symm
  have h1 : (1 : ↥L) = (p : ↥L) * (Nat.gcdA p n : ↥L) + (n : ↥L) * (Nat.gcdB p n : ↥L) := by
    have := congrArg (fun t : ℤ => (t : ↥L)) hbez
    push_cast at this
    exact this.symm
  have hsum := ν.add_le ((p : ↥L) * (Nat.gcdA p n : ↥L)) ((n : ↥L) * (Nat.gcdB p n : ↥L))
  rw [← h1, map_one, map_mul, map_mul] at hsum
  have hpu : ν (p : ↥L) * ν (Nat.gcdA p n : ↥L) < 1 := by
    calc ν (p : ↥L) * ν (Nat.gcdA p n : ↥L) ≤ ν (p : ↥L) * 1 :=
          mul_le_mul_of_nonneg_left (apply_intCast_le_one ν _) (apply_nonneg ν _)
      _ < 1 := by simpa using hν
  have hnv : ν (n : ↥L) * ν (Nat.gcdB p n : ↥L) ≤ ν (n : ↥L) := by
    simpa using mul_le_mul_of_nonneg_left (apply_intCast_le_one ν (Nat.gcdB p n)) (apply_nonneg ν (n : ↥L))
  rcases le_max_iff.mp hsum with h | h
  · exact absurd (lt_of_le_of_lt h hpu) (lt_irrefl _)
  · exact h.trans hnv

private theorem exists_apply_natCast_eq_pow {p : ℕ} (hp : p.Prime) (hν : ν (p : ↥L) < 1) {n : ℕ} (hn : n ≠ 0) :
    ∃ e : ℕ, e ≤ n ∧ ν (n : ↥L) = ν (p : ↥L) ^ e := by
  obtain ⟨e, n₀, hn₀, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one
  refine ⟨e, ?_, ?_⟩
  · have h1 : p ^ e ≤ p ^ e * n₀ := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (by rintro rfl; simp at hn))
    exact ((Nat.lt_pow_self hp.one_lt).le.trans h1)
  · rw [Nat.cast_mul, Nat.cast_pow, map_mul, map_pow, apply_natCast_eq_one_of_not_dvd ν hp hν hn₀, mul_one]

private theorem log_apply_le_of_isIntegral_mul {p : ℕ} (hp : p.Prime) (hν : ν (p : ↥L) < 1) {n : ℕ} (hn : n ≠ 0)
    {b : ↥L} (hint : IsIntegral ℤ ((n : ↥L) * b)) :
    Real.log (ν b) ≤ (n : ℝ) * (-Real.log (ν (p : ↥L))) := by
  have hp0 : (0 : ℝ) < ν (p : ↥L) := FinitePlace.pos_iff.mpr (by exact_mod_cast hp.ne_zero)
  have hX : 0 ≤ -Real.log (ν (p : ↥L)) := by
    have := Real.log_nonpos (le_of_lt hp0) hν.le
    linarith
  by_cases hb : b = 0
  · subst hb
    simp only [map_zero, Real.log_zero]
    exact mul_nonneg (Nat.cast_nonneg n) hX
  obtain ⟨e, he, hne⟩ := exists_apply_natCast_eq_pow ν hp hν hn
  have hb0 : 0 < ν b := FinitePlace.pos_iff.mpr hb
  have hnb : ν (n : ↥L) * ν b ≤ 1 := by
    have := apply_le_one_of_isIntegral ν hint
    rwa [map_mul] at this
  have hpe : 0 < ν (p : ↥L) ^ e := pow_pos hp0 e
  have hle : ν b ≤ 1 / ν (p : ↥L) ^ e := by
    rw [hne] at hnb
    exact (le_div_iff₀ hpe).mpr (by rw [mul_comm]; exact hnb)
  calc Real.log (ν b) ≤ Real.log (1 / ν (p : ↥L) ^ e) := Real.log_le_log hb0 hle
    _ = (e : ℝ) * (-Real.log (ν (p : ↥L))) := by rw [one_div, Real.log_inv, Real.log_pow]; ring
    _ ≤ (n : ℝ) * (-Real.log (ν (p : ↥L))) := mul_le_mul_of_nonneg_right (by exact_mod_cast he) hX

omit [NumberField ↥L] in

private theorem isIntegral_mul_of_coe_eq {z : AlgebraicClosure ℚ} {n : ℕ}
    (hz : IsIntegral ℤ ((n : AlgebraicClosure ℚ) * z)) {a : ↥L} (ha : (a : AlgebraicClosure ℚ) = z) :
    IsIntegral ℤ ((n : ↥L) * a) := by
  obtain ⟨P, hP, hroot⟩ := hz
  refine ⟨P, hP, ?_⟩
  apply (algebraMap (↥L) (AlgebraicClosure ℚ)).injective
  rw [map_zero, Polynomial.hom_eval₂, map_mul, map_natCast]
  have hA : algebraMap (↥L) (AlgebraicClosure ℚ) a = z := ha
  rw [hA]
  convert hroot using 2
  rfl
  rfl

private theorem exists_natCast_mul_isIntegral (z : AlgebraicClosure ℚ) :
    ∃ n : ℕ, n ≠ 0 ∧ IsIntegral ℤ ((n : AlgebraicClosure ℚ) * z) := by
  haveI : IsScalarTower ℤ ℚ (AlgebraicClosure ℚ) := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have h₁ : IsAlgebraic ℚ z := by
    have h := (@AlgebraicClosure.isAlgebraic ℚ _).isAlgebraic z
    convert h
    rfl
    rfl
  have hz : IsAlgebraic ℤ z := (IsFractionRing.isAlgebraic_iff ℤ ℚ (AlgebraicClosure ℚ)).mpr h₁
  obtain ⟨y, hy, hint⟩ := hz.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_ne_zero.mpr hy, ?_⟩
  rcases Int.natAbs_eq y with h | h
  · have hc : ((y.natAbs : ℕ) : AlgebraicClosure ℚ) = (y : AlgebraicClosure ℚ) := by
      conv_rhs => rw [h]
      simp
    rw [hc, ← zsmul_eq_mul]
    exact hint
  · have hc : ((y.natAbs : ℕ) : AlgebraicClosure ℚ) = -(y : AlgebraicClosure ℚ) := by
      conv_rhs => rw [h]
      simp
    rw [hc, neg_mul, ← zsmul_eq_mul]
    exact hint.neg

end AbsLogBound

theorem solution (z : AlgebraicClosure ℚ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L]
      (ν : NumberField.FinitePlace ↥L) (p : ℕ), p.Prime → ν (p : ↥L) < 1 →
      ∀ a : ↥L, (a : AlgebraicClosure ℚ) = z → |Real.log (ν a)| ≤ C * (-Real.log (ν (p : ↥L))) := by
  obtain ⟨n, hn, hnz⟩ := AbsLogBound.exists_natCast_mul_isIntegral z
  obtain ⟨n', hn', hnz'⟩ := AbsLogBound.exists_natCast_mul_isIntegral z⁻¹
  refine ⟨max (n : ℝ) (n' : ℝ), le_max_of_le_left (Nat.cast_nonneg n), ?_⟩
  intro L _ ν p hp hν a ha
  have hp0 : (0 : ℝ) < ν (p : ↥L) := NumberField.FinitePlace.pos_iff.mpr (by exact_mod_cast hp.ne_zero)
  have hX : 0 ≤ -Real.log (ν (p : ↥L)) := by
    have := Real.log_nonpos (le_of_lt hp0) hν.le
    linarith
  have h₁ : Real.log (ν a) ≤ (n : ℝ) * (-Real.log (ν (p : ↥L))) :=
    AbsLogBound.log_apply_le_of_isIntegral_mul ν hp hν hn (AbsLogBound.isIntegral_mul_of_coe_eq hnz ha)
  have ha' : ((a⁻¹ : ↥L) : AlgebraicClosure ℚ) = z⁻¹ := by rw [← ha]; simp
  have h₂ : Real.log (ν a⁻¹) ≤ (n' : ℝ) * (-Real.log (ν (p : ↥L))) :=
    AbsLogBound.log_apply_le_of_isIntegral_mul ν hp hν hn' (AbsLogBound.isIntegral_mul_of_coe_eq hnz' ha')
  rw [map_inv₀, Real.log_inv] at h₂
  have hC₁ : (n : ℝ) * (-Real.log (ν (p : ↥L))) ≤ max (n : ℝ) (n' : ℝ) * (-Real.log (ν (p : ↥L))) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hX
  have hC₂ : (n' : ℝ) * (-Real.log (ν (p : ↥L))) ≤ max (n : ℝ) (n' : ℝ) * (-Real.log (ν (p : ↥L))) :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hX
  exact abs_le.mpr ⟨by linarith, h₁.trans hC₁⟩

end S_NumberField_FinitePlace_exists_abs_log_le_mul_neg_log_of_coe_eq
end P2MW
export P2MW.S_NumberField_FinitePlace_exists_abs_log_le_mul_neg_log_of_coe_eq (solution)
