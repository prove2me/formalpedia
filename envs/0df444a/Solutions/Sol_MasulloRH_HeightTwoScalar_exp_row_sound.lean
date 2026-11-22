-- Prove2me | solution 1 for MasulloRH.HeightTwoScalar.exp_row_sound
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T20:11:03.0844+00:00
-- url     : https://prove2.me/submissions/e954a94e-24fd-483e-9c6c-cb1d6cb6e23c

import Mathlib
import Definitions.Def_MasulloRH_ThetaCertificate

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

open scoped BigOperators
open _root_.MasulloRH.CertifiedExp _root_.MasulloRH.Certificates
open _root_.MasulloRH.HeightTwoScalar

namespace N5ExpCertificateProof

/- Embedded checked source: Solutions/ThetaExpCertificateCore.lean -/
set_option autoImplicit false

open scoped BigOperators

namespace MasulloRH.CertifiedExp

/-- A finite rational certificate for an exponential on the unit interval. -/
theorem enclosure_of_taylor {x a b : ℝ} {n : ℕ}
    (hx : |x| ≤ 1) (hn : 0 < n)
    (hlo : a ≤ (∑ m ∈ Finset.range n, x ^ m / m.factorial) -
      |x| ^ n * ((n + 1 : ℕ) : ℝ) / (n.factorial * n))
    (hhi : (∑ m ∈ Finset.range n, x ^ m / m.factorial) +
      |x| ^ n * ((n + 1 : ℕ) : ℝ) / (n.factorial * n) ≤ b) :
    a ≤ Real.exp x ∧ Real.exp x ≤ b := by
  have h := Real.exp_bound hx hn
  have h' : |Real.exp x - ∑ m ∈ Finset.range n, x ^ m / m.factorial| ≤
      |x| ^ n * ((n + 1 : ℕ) : ℝ) / (n.factorial * n) := by
    simpa only [Nat.succ_eq_add_one, mul_div_assoc] using h
  constructor <;> linarith [(abs_le.mp h').1, (abs_le.mp h').2]

/-- Scaling, powering and reciprocation preserve certified rational endpoints.
The powers in the two final hypotheses are rational arithmetic only. -/
theorem neg_enclosure_of_scaled {t x a b l u : ℝ} {n : ℕ}
    (ht : t = n * x) (ha : 0 < a)
    (hsmall : a ≤ Real.exp x ∧ Real.exp x ≤ b)
    (hl : l ≤ 1 / b ^ n) (hu : 1 / a ^ n ≤ u) :
    l ≤ Real.exp (-t) ∧ Real.exp (-t) ≤ u := by
  have hlow := pow_le_pow_left₀ ha.le hsmall.1 n
  have hupp := pow_le_pow_left₀ (Real.exp_pos x).le hsmall.2 n
  rw [Real.exp_neg, ht, Real.exp_nat_mul, ← one_div]
  exact ⟨hl.trans (one_div_le_one_div_of_le (pow_pos (Real.exp_pos x) n) hupp),
    (one_div_le_one_div_of_le (pow_pos ha n) hlow).trans hu⟩

theorem enclosure_of_scaled {t x a b l u : ℝ} {n : ℕ}
    (ht : t = n * x) (ha : 0 ≤ a)
    (hsmall : a ≤ Real.exp x ∧ Real.exp x ≤ b)
    (hl : l ≤ a ^ n) (hu : b ^ n ≤ u) :
    l ≤ Real.exp t ∧ Real.exp t ≤ u := by
  rw [ht, Real.exp_nat_mul]
  exact ⟨hl.trans (pow_le_pow_left₀ ha hsmall.1 n),
    (pow_le_pow_left₀ (Real.exp_pos x).le hsmall.2 n).trans hu⟩

/-- A cheap enclosure for every sufficiently negative Gaussian exponent. -/
theorem neg_enclosure_of_twenty_le {t : ℝ} (ht : 20 ≤ t) :
    0 ≤ Real.exp (-t) ∧ Real.exp (-t) ≤ 1 / 1048576 := by
  have hbase : (2 : ℝ) ≤ Real.exp 1 := by
    linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hbase 20
  have hexp : Real.exp 1 ^ (20 : ℕ) = Real.exp 20 := by
    simpa only [Nat.cast_ofNat, mul_one] using (Real.exp_nat_mul (1 : ℝ) 20).symm
  rw [hexp] at hpow
  norm_num at hpow
  have ht' := hpow.trans (Real.exp_le_exp.mpr ht)
  refine ⟨(Real.exp_pos _).le, ?_⟩
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (by norm_num) ht'

theorem enclosure_of_argument_interval {x a b l u : ℝ}
    (hx : a ≤ x ∧ x ≤ b) (hl : l ≤ Real.exp a) (hu : Real.exp b ≤ u) :
    l ≤ Real.exp x ∧ Real.exp x ≤ u :=
  ⟨hl.trans (Real.exp_le_exp.mpr hx.1), (Real.exp_le_exp.mpr hx.2).trans hu⟩


end MasulloRH.CertifiedExp

/- Embedded checked source: Solutions/ThetaHeightTwoExpCheck.lean -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

open scoped BigOperators

namespace MasulloRH.HeightTwoScalar

/-- The arithmetic checked by the kernel is rational, not floating point. -/
theorem cast_taylorRat (x : ℚ) (n : ℕ) :
    (taylorRat x n : ℝ) =
      ∑ m ∈ Finset.range n, (x : ℝ) ^ m / (m.factorial : ℝ) := by
  unfold taylorRat
  push_cast <;> rfl

theorem cast_remainderRat (x : ℚ) (n : ℕ) :
    (remainderRat x n : ℝ) =
      (x : ℝ) ^ n * (n + 1 : ℕ) / ((n.factorial : ℝ) * n) := by
  unfold remainderRat
  push_cast <;> rfl

private theorem small_enclosure (x a b : ℚ) (order : ℕ)
    (hx0 : 0 ≤ x) (hx : x ≤ 1) (hn : 0 < order)
    (hlo : a ≤ taylorRat x order - remainderRat x order)
    (hhi : taylorRat x order + remainderRat x order ≤ b) :
    (a : ℝ) ≤ Real.exp (x : ℝ) ∧ Real.exp (x : ℝ) ≤ (b : ℝ) := by
  have hx0' : (0 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx0
  apply MasulloRH.CertifiedExp.enclosure_of_taylor (n := order)
  · rw [abs_of_nonneg hx0']
    exact_mod_cast hx
  · exact hn
  · have h : (a : ℝ) ≤ ((taylorRat x order - remainderRat x order : ℚ) : ℝ) :=
      Rat.cast_le.mpr hlo
    simpa only [Rat.cast_sub, cast_taylorRat, cast_remainderRat, abs_of_nonneg hx0'] using h
  · have h : ((taylorRat x order + remainderRat x order : ℚ) : ℝ) ≤ (b : ℝ) :=
      Rat.cast_le.mpr hhi
    simpa only [Rat.cast_add, cast_taylorRat, cast_remainderRat, abs_of_nonneg hx0'] using h

theorem positive_exp_of_check (t x a b l u : ℚ) (power order : ℕ)
    (h : PositiveExpCheck t x a b l u power order) :
    (l : ℝ) ≤ Real.exp (t : ℝ) ∧ Real.exp (t : ℝ) ≤ (u : ℝ) := by
  rcases h with ⟨hx0, hx, hn, ht, ha, hlo, hhi, hl, hu⟩
  apply MasulloRH.CertifiedExp.enclosure_of_scaled (n := power)
    (x := (x : ℝ)) (a := (a : ℝ)) (b := (b : ℝ))
  · exact_mod_cast ht
  · exact_mod_cast ha.le
  · exact small_enclosure x a b order hx0 hx hn hlo hhi
  · exact_mod_cast hl
  · exact_mod_cast hu

theorem negative_exp_of_check (t x a b l u : ℚ) (power order : ℕ)
    (h : NegativeExpCheck t x a b l u power order) :
    (l : ℝ) ≤ Real.exp (-(t : ℝ)) ∧ Real.exp (-(t : ℝ)) ≤ (u : ℝ) := by
  rcases h with ⟨hx0, hx, hn, ht, ha, hlo, hhi, hl, hu⟩
  apply MasulloRH.CertifiedExp.neg_enclosure_of_scaled (n := power)
    (x := (x : ℝ)) (a := (a : ℝ)) (b := (b : ℝ))
  · exact_mod_cast ht
  · exact_mod_cast ha
  · exact small_enclosure x a b order hx0 hx hn hlo hhi
  · exact_mod_cast hl
  · exact_mod_cast hu

/-- The integer cutoff can be chosen per argument, so far-tail derivative
factors do not magnify a fixed coarse exponential error. -/
theorem exp_neg_le_two_pow (t : ℝ) (n : ℕ) (ht : (n : ℝ) ≤ t) :
    0 ≤ Real.exp (-t) ∧ Real.exp (-t) ≤ 1 / (2 : ℝ) ^ n := by
  have he : (2 : ℝ) ≤ Real.exp 1 := by
    linarith [Real.add_one_le_exp (1 : ℝ)]
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) he n
  have hn : Real.exp 1 ^ n = Real.exp (n : ℝ) := by
    simpa only [mul_one] using (Real.exp_nat_mul (1 : ℝ) n).symm
  rw [hn] at hp
  have hpow : (2 : ℝ) ^ n ≤ Real.exp t := hp.trans (Real.exp_le_exp.mpr ht)
  refine ⟨(Real.exp_pos _).le, ?_⟩
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (by positivity) hpow

end MasulloRH.HeightTwoScalar

end N5ExpCertificateProof

/-- Every valid rational exponential row encloses the actual real exponential. -/
theorem solution (q : ExpRow) (hq : q.Valid) :
    (q.lower : ℝ) ≤ Real.exp (q.argument : ℝ) ∧
      Real.exp (q.argument : ℝ) ≤ (q.upper : ℝ) := by
  by_cases h0 : q.mode = 0
  · rw [ExpRow.Valid, if_pos h0] at hq
    rcases hq with ⟨harg, hl, hu⟩
    rw [harg]
    simp only [Rat.cast_zero, Real.exp_zero]
    constructor
    · exact_mod_cast hl
    · exact_mod_cast hu
  · by_cases h1 : q.mode = 1
    · rw [ExpRow.Valid, if_neg h0, if_pos h1] at hq
      exact N5ExpCertificateProof.MasulloRH.HeightTwoScalar.positive_exp_of_check
        q.argument q.smallArg q.baseL q.baseU q.lower q.upper q.power q.order hq
    · by_cases h2 : q.mode = 2
      · rw [ExpRow.Valid, if_neg h0, if_neg h1, if_pos h2] at hq
        simpa only [Rat.cast_neg, neg_neg] using
          N5ExpCertificateProof.MasulloRH.HeightTwoScalar.negative_exp_of_check
            (-q.argument) q.smallArg q.baseL q.baseU q.lower q.upper q.power q.order hq
      · by_cases h3 : q.mode = 3
        · rw [ExpRow.Valid, if_neg h0, if_neg h1, if_neg h2, if_pos h3] at hq
          rcases hq with ⟨hn, hl, hu⟩
          have hnR : (q.natBound : ℝ) ≤ -(q.argument : ℝ) := by exact_mod_cast hn
          have he : 0 ≤ Real.exp (q.argument : ℝ) ∧
              Real.exp (q.argument : ℝ) ≤ 1/(2 : ℝ)^q.natBound := by
            simpa only [neg_neg] using
              N5ExpCertificateProof.MasulloRH.HeightTwoScalar.exp_neg_le_two_pow
                (-(q.argument : ℝ)) q.natBound hnR
          refine ⟨le_trans ?_ he.1, le_trans he.2 ?_⟩
          · exact_mod_cast hl
          · have huR := (Rat.cast_le (K := ℝ)).2 hu
            simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat] using huR
        · simp only [ExpRow.Valid, if_neg h0, if_neg h1, if_neg h2, if_neg h3] at hq

#print axioms solution
