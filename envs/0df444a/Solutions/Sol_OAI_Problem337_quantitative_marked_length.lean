-- Prove2me | solution 1 for OAI.Problem337.quantitative_marked_length
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T10:05:40.611808+00:00
-- url     : https://prove2.me/submissions/a2b7b830-507c-4920-b2d7-ac4bf1547c5f

import Mathlib
import Definitions.Def_EgyptianFractions
import Definitions.Def_OAIQ8EF000

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_BilinearFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

lemma residue_character_orthogonality {q : ℕ} [NeZero q] (y z : ZMod q) :
    (∑ x : ZMod q, ZMod.stdAddChar (x * y) *
      (starRingEnd ℂ) (ZMod.stdAddChar (x * z))) =
      if y = z then (q : ℂ) else 0 := by
  simp_rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul, ← mul_neg, ← mul_add]
  rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar q)]
  simp only [add_neg_eq_zero, ZMod.card]
  split_ifs <;> simp

/-- Parseval's identity for the positive-sign transform on all residue classes. -/
theorem residueFourier_parseval {q : ℕ} [NeZero q] (β : ZMod q → ℂ) :
    (∑ x : ZMod q, ‖residueFourier β x‖ ^ 2) =
      (q : ℝ) * ∑ y : ZMod q, ‖β y‖ ^ 2 := by
  have hc : (∑ x : ZMod q, residueFourier β x *
      (starRingEnd ℂ) (residueFourier β x)) =
      (q : ℂ) * ∑ y : ZMod q, β y * (starRingEnd ℂ) (β y) := by
    simp only [residueFourier, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.sum_comm]
    calc
      _ = ∑ z : ZMod q, (β z * (starRingEnd ℂ) (β y)) *
          ∑ x : ZMod q, ZMod.stdAddChar (x * z) *
            (starRingEnd ℂ) (ZMod.stdAddChar (x * y)) := by
        apply Finset.sum_congr rfl
        intro z _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = (q : ℂ) * (β y * (starRingEnd ℂ) (β y)) := by
        simp_rw [residue_character_orthogonality]
        simp [mul_comm]
  simpa only [Complex.mul_conj, ← Complex.ofReal_sum, ← Complex.ofReal_mul,
    ← Complex.ofReal_natCast, Complex.ofReal_inj, Complex.normSq_eq_norm_sq] using hc

/-- A unit frequency preserves the Parseval identity, also for composite moduli. -/
theorem residueFourier_parseval_unit {q : ℕ} [NeZero q]
    (β : ZMod q → ℂ) (c : (ZMod q)ˣ) :
    (∑ x : ZMod q, ‖residueFourier β ((c : ZMod q) * x)‖ ^ 2) =
      (q : ℝ) * ∑ y : ZMod q, ‖β y‖ ^ 2 := by
  rw [show (∑ x : ZMod q, ‖residueFourier β ((c : ZMod q) * x)‖ ^ 2) =
      ∑ x : ZMod q, ‖residueFourier β x‖ ^ 2 from
    Equiv.sum_comp c.mulLeft (fun x => ‖residueFourier β x‖ ^ 2)]
  exact residueFourier_parseval β

/-- The bilinear additive-character bound used for random prime products.
No primality hypothesis on the modulus is needed; the frequency is a unit. -/
theorem residue_bilinear_bound {q : ℕ} [NeZero q]
    (α β : ZMod q → ℂ) (c : (ZMod q)ˣ) :
    ‖∑ x : ZMod q, ∑ y : ZMod q,
      α x * β y * ZMod.stdAddChar ((c : ZMod q) * x * y)‖ ≤
      Real.sqrt (q : ℝ) * Real.sqrt (∑ x : ZMod q, ‖α x‖ ^ 2) *
        Real.sqrt (∑ y : ZMod q, ‖β y‖ ^ 2) := by
  have hsum : (∑ x : ZMod q, ∑ y : ZMod q,
      α x * β y * ZMod.stdAddChar ((c : ZMod q) * x * y)) =
      ∑ x : ZMod q, α x * residueFourier β ((c : ZMod q) * x) := by
    simp only [residueFourier, Finset.mul_sum, mul_assoc]
  rw [hsum]
  calc
    _ ≤ ∑ x : ZMod q, ‖α x * residueFourier β ((c : ZMod q) * x)‖ :=
      norm_sum_le _ _
    _ = ∑ x : ZMod q, ‖α x‖ * ‖residueFourier β ((c : ZMod q) * x)‖ := by
      simp only [norm_mul]
    _ ≤ Real.sqrt (∑ x : ZMod q, ‖α x‖ ^ 2) *
        Real.sqrt (∑ x : ZMod q, ‖residueFourier β ((c : ZMod q) * x)‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = _ := by
      rw [residueFourier_parseval_unit, Real.sqrt_mul (by positivity)]
      ring

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_CollisionCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped BigOperators

namespace Problem337

lemma collision_card_eq_strict_add {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (f : α → β) :
    (collisionPairs A f).card = (strictCollisionPairs A f).card + A.card := by
  have hdiag : (collisionPairs A f).filter (fun p => ¬p.1 ≠ p.2) = A.diag := by
    ext p
    simp only [collisionPairs, Finset.mem_filter, Finset.mem_product, not_not,
      Finset.mem_diag]
    aesop
  have h := Finset.card_filter_add_card_filter_not (s := collisionPairs A f)
    (fun p => p.1 ≠ p.2)
  rw [hdiag, Finset.diag_card] at h
  exact h.symm

end Problem337

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_PrimeProductBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
open Filter Real

namespace Problem337

lemma primePrefixProduct_pos (n : ℕ) : 0 < primePrefixProduct n := by
  apply Finset.prod_pos
  intro i hi
  exact (Nat.prime_nth_prime i).pos

lemma primePrefixProduct_dvd_mono {m n : ℕ} (h : m ≤ n) :
    primePrefixProduct m ∣ primePrefixProduct n := by
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.range_mono h)

lemma two_pow_le_primePrefixProduct (n : ℕ) : 2 ^ n ≤ primePrefixProduct n := by
  calc
    2 ^ n = ∏ _i ∈ Finset.range n, 2 := by simp
    _ ≤ primePrefixProduct n := by
      apply Finset.prod_le_prod'
      intro i hi
      exact (Nat.prime_nth_prime i).two_le

lemma card_divisors_primePrefixProduct (n : ℕ) :
    (primePrefixProduct n).divisors.card = 2 ^ n := by
  induction n with
  | zero => simp [primePrefixProduct]
  | succ n ih =>
    have hc : (primePrefixProduct n).Coprime (Nat.nth Nat.Prime n) := by
      apply Nat.Coprime.prod_left
      intro i hi
      apply (Nat.coprime_primes (Nat.prime_nth_prime i) (Nat.prime_nth_prime n)).2
      exact ne_of_lt (Nat.nth_strictMono Nat.infinite_setOfPred_prime (Finset.mem_range.mp hi))
    have hstep : primePrefixProduct (n + 1) = primePrefixProduct n * Nat.nth Nat.Prime n := by
      simp [primePrefixProduct, Finset.prod_range_succ]
    rw [hstep, hc.card_divisors_mul, ih, (Nat.prime_nth_prime n).divisors]
    simp [(Nat.prime_nth_prime n).ne_one.symm, pow_succ]

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_PrimeTripleAsymptotics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open Filter
open scoped Topology

namespace Problem337

/-- Any fixed logarithmic power is eventually smaller than an arbitrary
positive multiple of a positive real power. -/
lemma eventually_log_pow_lt_mul_rpow (n : ℕ) (r c : ℝ) (hr : 0 < r) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, (Real.log x) ^ n < c * x ^ r := by
  have hsmall : (fun x : ℝ => (Real.log x) ^ n) =o[atTop] (fun x : ℝ => x ^ r) := by
    simpa only [Real.rpow_natCast] using
      isLittleO_log_rpow_rpow_atTop (n : ℝ) hr
  have hlim := hsmall.tendsto_div_nhds_zero
  filter_upwards [hlim.eventually (gt_mem_nhds hc), eventually_gt_atTop (0 : ℝ)] with x hx hx0
  exact (div_lt_iff₀ (Real.rpow_pos_of_pos hx0 r)).1 hx

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_PrimeProductGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open Filter
open scoped Topology BigOperators

namespace Problem337

/-- Chebyshev's elementary bounds give the lower prime-density estimate needed
for the size of the first-prime product. No prime number theorem is used. -/
lemma eventually_primeCounting_ge_linear_div_log :
    ∀ᶠ x : ℝ in atTop,
      (Real.log 2 / 2) * x / Real.log x ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsmall := eventually_log_pow_lt_mul_rpow 1 1 (Real.log 2 / 4)
    (by norm_num) (by positivity)
  filter_upwards [hsmall, eventually_ge_atTop (8 : ℝ)] with x hlog hx
  simp only [pow_one, Real.rpow_one] at hlog
  have hx0 : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  have hlogadd : Real.log (x + 2) ≤ Real.log 2 + Real.log x := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hx0.ne']
    exact Real.log_le_log (by positivity) (by linarith)
  apply le_trans ?_ (Chebyshev.pi_ge' hx1)
  apply div_le_div_of_nonneg_right _ (Real.log_pos hx1).le
  nlinarith

lemma eventually_nth_prime_le_rpow (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      (Nat.nth Nat.Prime n : ℝ) ≤ (n : ℝ) ^ (1 + δ) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have he : 0 < 1 + δ := by linarith
  have hsmall := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ))
    atTop atTop).eventually (eventually_log_pow_lt_mul_rpow 1 δ
      (Real.log 2 / (2 * (1 + δ))) hδ (by positivity))
  have hpcount := ((tendsto_rpow_atTop he).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)).eventually
      eventually_primeCounting_ge_linear_div_log
  filter_upwards [hsmall, hpcount, eventually_ge_atTop 2] with n hn hp hn2
  simp only [Function.comp_apply] at hp
  have hnR : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hn0 : (0 : ℝ) < n := lt_trans zero_lt_one hnR
  have hx1 : (1 : ℝ) < (n : ℝ) ^ (1 + δ) := Real.one_lt_rpow hnR he
  have hlogpow : Real.log ((n : ℝ) ^ (1 + δ)) = (1 + δ) * Real.log (n : ℝ) :=
    Real.log_rpow hn0 _
  have hpow : (n : ℝ) ^ (1 + δ) = (n : ℝ) * (n : ℝ) ^ δ := by
    rw [Real.rpow_add hn0, Real.rpow_one]
  have hcount : (n : ℝ) < (Nat.primeCounting ⌊(n : ℝ) ^ (1 + δ)⌋₊ : ℝ) := by
    apply lt_of_lt_of_le _ hp
    apply (lt_div_iff₀ (Real.log_pos hx1)).2
    rw [hlogpow, hpow]
    simp only [pow_one] at hn
    have ht := (lt_div_iff₀ (show 0 < 2 * (1 + δ) by positivity)).1
      (show Real.log (n : ℝ) <
        (Real.log 2 * (n : ℝ) ^ δ) / (2 * (1 + δ)) by convert hn using 1; ring)
    nlinarith [mul_lt_mul_of_pos_left ht hn0]
  have hcountN : n < Nat.primeCounting ⌊(n : ℝ) ^ (1 + δ)⌋₊ := by exact_mod_cast hcount
  have hnth : Nat.nth Nat.Prime n < ⌊(n : ℝ) ^ (1 + δ)⌋₊ + 1 :=
    Nat.nth_lt_of_lt_count hcountN
  have hnth' : Nat.nth Nat.Prime n ≤ ⌊(n : ℝ) ^ (1 + δ)⌋₊ := by omega
  exact (by exact_mod_cast hnth' : (Nat.nth Nat.Prime n : ℝ) ≤
    (⌊(n : ℝ) ^ (1 + δ)⌋₊ : ℝ)).trans (Nat.floor_le (by positivity))

/-- The sharp leading coefficient in the logarithm of a prime-prefix product
needs only Chebyshev's lower prime-counting estimate. -/
lemma eventually_log_primePrefixProduct_le_growth (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      Real.log (primePrefixProduct n : ℝ) ≤ (1 + δ) * (n : ℝ) * Real.log (n : ℝ) := by
  filter_upwards [eventually_nth_prime_le_rpow δ hδ, eventually_ge_atTop 2] with n hn hn2
  have hn0 : (0 : ℝ) < n := by positivity
  have hprime0 (i : ℕ) : (0 : ℝ) < Nat.nth Nat.Prime i := by
    exact_mod_cast (Nat.prime_nth_prime i).pos
  have hlog : Real.log (Nat.nth Nat.Prime n : ℝ) ≤ (1 + δ) * Real.log (n : ℝ) := by
    simpa [Real.log_rpow hn0] using Real.log_le_log (hprime0 n) hn
  calc
    Real.log (primePrefixProduct n : ℝ) =
        ∑ i ∈ Finset.range n, Real.log (Nat.nth Nat.Prime i : ℝ) := by
      simp only [primePrefixProduct, Nat.cast_prod]
      exact Real.log_prod (fun i _ => (hprime0 i).ne')
    _ ≤ ∑ _i ∈ Finset.range n, Real.log (Nat.nth Nat.Prime n : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Real.log_le_log (hprime0 i)
      exact_mod_cast (Nat.nth_monotone Nat.infinite_setOfPred_prime)
        (Finset.mem_range.1 hi).le
    _ = (n : ℝ) * Real.log (Nat.nth Nat.Prime n : ℝ) := by simp
    _ ≤ (n : ℝ) * ((1 + δ) * Real.log (n : ℝ)) := mul_le_mul_of_nonneg_left hlog hn0.le
    _ = (1 + δ) * (n : ℝ) * Real.log (n : ℝ) := by ring

lemma tendsto_log_natCeil_mul_div_log (A : ℝ) (hA : 0 < A) :
    Tendsto (fun x : ℝ => Real.log (⌈A * x⌉₊ : ℝ) / Real.log x)
      atTop (𝓝 1) := by
  have hceil : Tendsto (fun x : ℝ => (⌈A * x⌉₊ : ℝ) / x) atTop (𝓝 A) :=
    tendsto_nat_ceil_mul_div_atTop hA.le
  have hz := (hceil.log hA.ne').div_atTop Real.tendsto_log_atTop
  have hlim : Tendsto (fun x : ℝ => 1 + Real.log ((⌈A * x⌉₊ : ℝ) / x) / Real.log x)
      atTop (𝓝 1) := by simpa using tendsto_const_nhds.add hz
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hc0 : (0 : ℝ) < ⌈A * x⌉₊ := (mul_pos hA hx0).trans_le (Nat.le_ceil _)
  rw [Real.log_div hc0.ne' hx0.ne']
  field_simp [(Real.log_pos hx).ne']; ring

/-- A directly usable prime-product bound at the logarithmic number of primes
required by rational-divisor supply. -/
lemma eventually_log_primePrefixProduct_ceil_le (A ε : ℝ) (hA : 0 < A) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      Real.log (primePrefixProduct ⌈A * x⌉₊ : ℝ) ≤ (A + ε) * x * Real.log x := by
  let δ : ℝ := ε / (2 * A)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hceil : Tendsto (fun x : ℝ => (⌈A * x⌉₊ : ℝ) / x) atTop (𝓝 A) :=
    tendsto_nat_ceil_mul_div_atTop hA.le
  have hratio : Tendsto (fun x : ℝ =>
      ((1 + δ) * (⌈A * x⌉₊ : ℝ) * Real.log (⌈A * x⌉₊ : ℝ)) /
        (x * Real.log x)) atTop (𝓝 ((1 + δ) * A)) := by
    have h := (hceil.const_mul (1 + δ)).mul (tendsto_log_natCeil_mul_div_log A hA)
    convert h using 1
    · ext x
      ring
    · simp
  have hcoef : (1 + δ) * A < A + ε := by
    dsimp [δ]
    field_simp
    nlinarith
  have hell : Tendsto (fun x : ℝ => ⌈A * x⌉₊) atTop atTop :=
    tendsto_nat_ceil_atTop.comp (tendsto_id.const_mul_atTop hA)
  have hprod := hell.eventually (eventually_log_primePrefixProduct_le_growth δ hδ)
  filter_upwards [hratio.eventually (gt_mem_nhds hcoef), hprod,
    eventually_gt_atTop (1 : ℝ)] with x hr hp hx
  have hden : 0 < x * Real.log x := mul_pos (lt_trans zero_lt_one hx) (Real.log_pos hx)
  exact hp.trans (by simpa only [mul_assoc] using ((div_lt_iff₀ hden).1 hr).le)

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_CompositeSupplySize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-!
# Size of the fourth-power supply for cube-free moduli

The fourth-power auxiliary integer has a controlled logarithmic size.
-/
noncomputable section
open Filter
open scoped BigOperators

namespace Problem337.CompositeSupply

lemma base_pos (u : ℕ) : 0 < base u := primePrefixProduct_pos _

lemma multiplier_pos (m : ℕ) : 0 < multiplier m := pow_pos (base_pos _) _

lemma primeCount_eq_supplyPrimeCount (u : ℕ) :
    primeCount u = supplyPrimeCount (2 / Real.log 2) u := by
  unfold primeCount supplyPrimeCount
  congr 1
  ring

lemma base_fourth_power (m : ℕ) :
    base (m ^ 4) = primePrefixProduct (supplyPrimeCount (8 / Real.log 2) m) := by
  unfold base primeCount supplyPrimeCount
  rw [Nat.cast_pow, Real.log_pow]
  congr 2
  ring

lemma base_dvd_mono {u v : ℕ} (hu : 0 < u) (huv : u ≤ v) : base u ∣ base v := by
  apply primePrefixProduct_dvd_mono
  apply Nat.ceil_mono
  apply div_le_div_of_nonneg_right _ (by positivity : 0 ≤ Real.log 2)
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  exact Real.log_le_log (by exact_mod_cast hu) (by exact_mod_cast huv)

/-- A prime not dividing the initial prime product is beyond its index cutoff. -/
lemma primeCount_le_of_not_dvd (u p : ℕ) (hp : p.Prime) (hnot : ¬ p ∣ base u) :
    primeCount u ≤ p := by
  by_contra h
  have hplt : p < primeCount u := by omega
  have hi : Nat.count Nat.Prime p < primeCount u :=
    (Nat.count_le Nat.Prime).trans_lt hplt
  have hd := Finset.dvd_prod_of_mem (fun i => Nat.nth Nat.Prime i)
    (Finset.mem_range.mpr hi)
  apply hnot
  simpa only [base, primePrefixProduct, Nat.nth_count hp] using hd

lemma log_le_primeCount (u : ℕ) : Real.log (u : ℝ) ≤ primeCount u := by
  have hl2 : 0 < Real.log 2 := by positivity
  have hl2upper : Real.log 2 ≤ 2 :=
    (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)).trans (by norm_num)
  have hlog0 := Real.log_natCast_nonneg u
  have hfirst : Real.log (u : ℝ) ≤ 2 * Real.log (u : ℝ) / Real.log 2 := by
    apply (le_div_iff₀ hl2).mpr
    nlinarith
  exact hfirst.trans (Nat.le_ceil _)

/-- Every residual prime after removing the global pool is genuinely rough. -/
lemma log_le_prime_of_not_dvd (u p : ℕ) (hp : p.Prime) (hnot : ¬ p ∣ base u) :
    Real.log (u : ℝ) ≤ (p : ℝ) :=
  (log_le_primeCount u).trans (by exact_mod_cast primeCount_le_of_not_dvd u p hp hnot)

/-- The full cutoff coefficient is available when a dyadic shell requires
roughness at `log (2*u)` rather than just `log u`. -/
lemma scaled_log_le_prime_of_not_dvd (u p : ℕ) (hp : p.Prime)
    (hnot : ¬ p ∣ base u) :
    2 * Real.log (u : ℝ) / Real.log 2 ≤ (p : ℝ) :=
  (Nat.le_ceil _).trans (by exact_mod_cast primeCount_le_of_not_dvd u p hp hnot)

lemma log_double_le_prime_of_not_dvd (u p : ℕ) (hu : 2 ≤ u) (hp : p.Prime)
    (hnot : ¬ p ∣ base u) : Real.log (2 * (u : ℝ)) ≤ (p : ℝ) := by
  have huR : (0 : ℝ) < u := by exact_mod_cast (show 0 < u by omega)
  have hl2 : 0 < Real.log 2 := by positivity
  have hl2one : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlu : Real.log 2 ≤ Real.log (u : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hu)
  have hlu0 : 0 ≤ Real.log (u : ℝ) := Real.log_natCast_nonneg u
  have hscale := scaled_log_le_prime_of_not_dvd u p hp hnot
  have htwo : 2 * Real.log (u : ℝ) ≤ 2 * Real.log (u : ℝ) / Real.log 2 := by
    apply (le_div_iff₀ hl2).mpr
    nlinarith
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) huR.ne']
  linarith

lemma base_squarefree (u : ℕ) : Squarefree (base u) := by
  unfold base primePrefixProduct
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro i hi j hj hij
    simp only [← Nat.coprime_iff_isRelPrime]
    apply (Nat.coprime_primes (Nat.prime_nth_prime i) (Nat.prime_nth_prime j)).mpr
    exact (Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective.ne hij
  · intro i hi
    exact (Nat.prime_nth_prime i).squarefree

/-- The divisor pool has the required quadratic cardinality. -/
lemma square_le_divisors_card (u : ℕ) : u ^ 2 ≤ (base u).divisors.card := by
  unfold base
  rw [card_divisors_primePrefixProduct]
  by_cases hu : u = 0
  · simp [hu]
  have huR : (0 : ℝ) < u := by exact_mod_cast Nat.pos_of_ne_zero hu
  have hlog2 : 0 < Real.log 2 := by positivity
  have hc : 2 * Real.log (u : ℝ) ≤ (primeCount u : ℝ) * Real.log 2 :=
    (div_le_iff₀ hlog2).mp (Nat.le_ceil _)
  have hlogs : Real.log ((u : ℝ) ^ 2) ≤
      Real.log ((2 : ℝ) ^ primeCount u) := by
    rw [Real.log_pow, Real.log_pow]
    norm_num
    exact hc
  have hreal : (u : ℝ) ^ 2 ≤ (2 : ℝ) ^ primeCount u :=
    (Real.log_le_log_iff (by positivity) (by positivity)).mp hlogs
  exact_mod_cast hreal

lemma square_le_base (u : ℕ) : u ^ 2 ≤ base u := by
  have h := square_le_divisors_card u
  rw [base, card_divisors_primePrefixProduct] at h
  exact h.trans (two_pow_le_primePrefixProduct _)

lemma marker_lt_multiplier (m : ℕ) (hm : 2 ≤ m) : m < multiplier m := by
  have hm1 : 1 ≤ m := by omega
  have hm_sq : m < m ^ 2 := by nlinarith
  have hm4 : m ^ 2 ≤ m ^ 4 := Nat.pow_le_pow_right hm1 (by norm_num)
  have hu : 1 ≤ m ^ 4 := one_le_pow₀ hm1
  have hbase : m ^ 4 ≤ base (m ^ 4) :=
    (Nat.le_self_pow (by norm_num : 2 ≠ 0) (m ^ 4)).trans (square_le_base _)
  have hp : base (m ^ 4) ≤ base (m ^ 4) ^ 4 := Nat.le_self_pow (by norm_num) _
  exact hm_sq.trans_le (hm4.trans (hbase.trans hp))

/-- The sharp leading logarithmic size coefficient is the same as in the
original marked construction. No prime-distribution theorem is assumed. -/
theorem eventually_log_multiplier_le (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop,
      Real.log (multiplier m : ℝ) ≤
        (32 / Real.log 2 + ε) * Real.log (m : ℝ) *
          Real.log (Real.log (m : ℝ)) := by
  have hx : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hprime := hx.eventually (eventually_log_primePrefixProduct_ceil_le
    (8 / Real.log 2) (ε / 4) (by positivity) (by positivity))
  filter_upwards [hprime] with m hm
  rw [multiplier, base_fourth_power, Nat.cast_pow, Real.log_pow]
  change (4 : ℝ) *
      Real.log (primePrefixProduct ⌈(8 / Real.log 2) * Real.log (m : ℝ)⌉₊ : ℝ) ≤ _
  calc
    _ ≤ 4 * ((8 / Real.log 2 + ε / 4) * Real.log (m : ℝ) *
        Real.log (Real.log (m : ℝ))) := mul_le_mul_of_nonneg_left hm (by norm_num)
    _ = _ := by ring

end Problem337.CompositeSupply

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_CompositeUnitMixing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- The sum of unit translates has squared energy at most the number of
translates squared times the original energy. This needs no primality and
no positivity hypothesis on the original real-valued function. -/
theorem sum_sq_unit_mixing {q : ℕ} [NeZero q]
    {J : Type*} [Fintype J] (c : J → (ZMod q)ˣ) (w : ZMod q → ℝ) :
    (∑ x : ZMod q, (∑ j : J, w ((c j : ZMod q) * x)) ^ 2) ≤
      (Fintype.card J : ℝ) ^ 2 * ∑ x : ZMod q, w x ^ 2 := by
  classical
  have hpoint (x : ZMod q) :
      (∑ j : J, w ((c j : ZMod q) * x)) ^ 2 ≤
        (Fintype.card J : ℝ) * ∑ j : J, w ((c j : ZMod q) * x) ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset J) (fun _ => (1 : ℝ))
        (fun j => w ((c j : ZMod q) * x))
  calc
    _ ≤ ∑ x : ZMod q, (Fintype.card J : ℝ) *
        ∑ j : J, w ((c j : ZMod q) * x) ^ 2 :=
      Finset.sum_le_sum (fun x _ => hpoint x)
    _ = (Fintype.card J : ℝ) * ∑ j : J,
        ∑ x : ZMod q, w ((c j : ZMod q) * x) ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ = (Fintype.card J : ℝ) ^ 2 * ∑ x : ZMod q, w x ^ 2 := by
      have hperm (j : J) :
          (∑ x : ZMod q, w ((c j : ZMod q) * x) ^ 2) =
            ∑ x : ZMod q, w x ^ 2 :=
        Equiv.sum_comp (c j).mulLeft (fun x => w x ^ 2)
      simp_rw [hperm]
      simp [pow_two, mul_assoc]

/-- Averaging arbitrary unit permutations cannot increase squared energy.
In particular, adjoining independent prime choices coprime to a modulus
preserves any known upper bound for the projected divisor distribution. -/
theorem average_sq_unit_mixing {q : ℕ} [NeZero q]
    {J : Type*} [Fintype J] (c : J → (ZMod q)ˣ) (w : ZMod q → ℝ) :
    (∑ x : ZMod q,
      ((∑ j : J, w ((c j : ZMod q) * x)) / (Fintype.card J : ℝ)) ^ 2) ≤
        ∑ x : ZMod q, w x ^ 2 := by
  classical
  by_cases hJ : Fintype.card J = 0
  · simp [hJ, Finset.sum_nonneg (fun x _ => sq_nonneg (w x))]
  · have hJpos : (0 : ℝ) < Fintype.card J := by exact_mod_cast Nat.pos_of_ne_zero hJ
    simp_rw [div_pow]
    rw [← Finset.sum_div]
    apply (div_le_iff₀ (pow_pos hJpos 2)).mpr
    simpa only [mul_comm] using sum_sq_unit_mixing c w

/-- Multiplying an indexed sample by independent units transforms its fibers
by averaging inverse unit translations. Multiplicities are retained. -/
theorem unit_mixed_fiber_count {q : ℕ} [NeZero q]
    {I J : Type*} [Fintype I] [Fintype J]
    (f : I → ZMod q) (c : J → (ZMod q)ˣ) (x : ZMod q) :
    (Finset.univ.filter (fun z : I × J => (c z.2 : ZMod q) * f z.1 = x)).card =
      ∑ j : J, (Finset.univ.filter
        (fun i : I => f i = ((c j)⁻¹ : (ZMod q)ˣ) * x)).card := by
  classical
  simp only [Finset.card_filter, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  simp only [← (c j).eq_inv_mul_iff_mul_eq]

/-- The exact normalized finite-sample mass identity used in unit mixing.
The formula is valid even for an empty index type, using totalized division. -/
theorem unit_mixed_fiber_mass {q : ℕ} [NeZero q]
    {I J : Type*} [Fintype I] [Fintype J]
    (f : I → ZMod q) (c : J → (ZMod q)ˣ) (x : ZMod q) :
    ((Finset.univ.filter (fun z : I × J => (c z.2 : ZMod q) * f z.1 = x)).card : ℝ) /
        (Fintype.card (I × J) : ℝ) =
      (∑ j : J,
        ((Finset.univ.filter (fun i : I => f i = ((c j)⁻¹ : (ZMod q)ˣ) * x)).card : ℝ) /
          (Fintype.card I : ℝ)) / (Fintype.card J : ℝ) := by
  classical
  rw [unit_mixed_fiber_count, Nat.cast_sum, Fintype.card_prod, Nat.cast_mul,
    ← Finset.sum_div, div_div]

/-- Adjoining an independent list of units cannot increase the normalized
collision energy of a finite indexed residue sample. This is the precise
nesting principle for divisor lists at moduli coprime to the added primes. -/
theorem indexed_energy_unit_mixing {q : ℕ} [NeZero q]
    {I J : Type*} [Fintype I] [Fintype J]
    (f : I → ZMod q) (c : J → (ZMod q)ˣ) :
    (∑ x : ZMod q,
      (((Finset.univ.filter
        (fun z : I × J => (c z.2 : ZMod q) * f z.1 = x)).card : ℝ) /
          (Fintype.card (I × J) : ℝ)) ^ 2) ≤
      ∑ x : ZMod q,
        (((Finset.univ.filter (fun i : I => f i = x)).card : ℝ) /
          (Fintype.card I : ℝ)) ^ 2 := by
  classical
  simp_rw [unit_mixed_fiber_mass]
  exact average_sq_unit_mixing (fun j => (c j)⁻¹)
    (fun x => ((Finset.univ.filter (fun i : I => f i = x)).card : ℝ) /
      (Fintype.card I : ℝ))

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_DivisorEnergyNesting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators Pointwise

namespace Problem337

/-- Reindexing an indexed sample preserves each normalized fiber mass. -/
theorem fiber_mass_equiv {I J X : Type*} [Fintype I] [Fintype J]
    [DecidableEq X] (e : I ≃ J) (f : J → X) (x : X) :
    ((Finset.univ.filter (fun i : I => f (e i) = x)).card : ℝ) /
        (Fintype.card I : ℝ) =
      ((Finset.univ.filter (fun j : J => f j = x)).card : ℝ) /
        (Fintype.card J : ℝ) := by
  classical
  have hcard : (Finset.univ.filter (fun i : I => f (e i) = x)).card =
      (Finset.univ.filter (fun j : J => f j = x)).card := by
    simp only [Finset.card_filter]
    exact Equiv.sum_comp e (fun j => if f j = x then 1 else 0)
  rw [hcard, Fintype.card_congr e]

/-- Appending coprime factors which are units modulo `q` cannot increase the
normalized collision energy of the actual complete divisor list. -/
theorem divisorResidueEnergy_mul_le {P R q : ℕ} [NeZero q]
    (hPR : P.Coprime R) (hRq : R.Coprime q) :
    divisorResidueEnergy (P * R) q ≤ divisorResidueEnergy P q := by
  classical
  let c : ↥R.divisors → (ZMod q)ˣ := fun d =>
    ZMod.unitOfCoprime d.val (hRq.coprime_dvd_left (Nat.dvd_of_mem_divisors d.property))
  have hc (d : ↥R.divisors) : (c d : ZMod q) = (d.val : ZMod q) :=
    ZMod.coe_unitOfCoprime _ _
  have hmass (x : ZMod q) :
      ((Finset.univ.filter (fun z : ↥P.divisors × ↥R.divisors =>
        (c z.2 : ZMod q) * (z.1.val : ZMod q) = x)).card : ℝ) /
          (Fintype.card (↥P.divisors × ↥R.divisors) : ℝ) =
      ((Finset.univ.filter (fun d : ↥(P * R).divisors =>
        (d.val : ZMod q) = x)).card : ℝ) /
          (Fintype.card ↥(P * R).divisors : ℝ) := by
    simpa only [coprimeDivisorProductEquiv_val, Nat.cast_mul, hc, mul_comm] using
      fiber_mass_equiv (coprimeDivisorProductEquiv hPR)
        (fun d : ↥(P * R).divisors => (d.val : ZMod q)) x
  have h := indexed_energy_unit_mixing (fun d : ↥P.divisors => (d.val : ZMod q)) c
  simpa only [hmass, divisorResidueEnergy] using h

/-- The form used for nested prime-prefix products: at a modulus coprime to
 the larger squarefree supply, enlarging the supply decreases energy. -/
theorem divisorResidueEnergy_le_of_dvd_squarefree {P Q q : ℕ} [NeZero q]
    (hPQ : P ∣ Q) (hQ : Squarefree Q) (hQq : Q.Coprime q) :
    divisorResidueEnergy Q q ≤ divisorResidueEnergy P q := by
  have hmul : P * (Q / P) = Q := Nat.mul_div_cancel' hPQ
  have hcop : P.Coprime (Q / P) :=
    Nat.coprime_of_squarefree_mul (by simpa only [hmul] using hQ)
  have hdiv : Q / P ∣ Q := Nat.div_dvd_of_dvd hPQ
  simpa only [hmul] using divisorResidueEnergy_mul_le hcop (hQq.coprime_dvd_left hdiv)

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_RandomProductFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- Regroup a finite sum by the fibers of a map, with explicit fiber cardinalities. -/
lemma sum_fiber_card_mul {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (f : ι → κ) (g : κ → ℂ) :
    (∑ r : κ, ((Finset.univ.filter (fun a : ι => f a = r)).card : ℂ) * g r) =
      ∑ a : ι, g (f a) := by
  classical
  calc
    _ = ∑ r : κ, ∑ a ∈ Finset.univ.filter (fun a : ι => f a = r), g (f a) := by
      apply Finset.sum_congr rfl
      intro r _
      symm
      calc
        _ = ∑ a ∈ Finset.univ.filter (fun a : ι => f a = r), g r := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [(Finset.mem_filter.mp ha).2]
        _ = _ := by simp
    _ = _ := Finset.sum_fiberwise _ f (fun a => g (f a))

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_ReducedCharacter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

namespace Problem337

/-- The standard additive character evaluated at a natural integer. -/
lemma stdAddChar_natCast {q : ℕ} [NeZero q] (z : ℕ) :
    ZMod.stdAddChar (z : ZMod q) =
      Complex.exp (2 * Real.pi * Complex.I * (z : ℂ) / (q : ℂ)) := by
  simpa using ZMod.stdAddChar_coe (N := q) (z : ℤ)

lemma reduced_modulus_pos (a u : ℕ) (hu : 0 < u) :
    0 < u / a.gcd u :=
  Nat.div_pos (Nat.gcd_le_right a hu) (Nat.gcd_pos_of_pos_right a hu)

/-- Exact phase reduction to a primitive (unit-frequency) character. This also
covers `a = 0`, where the reduced modulus is `1`. -/
theorem stdAddChar_reduced (a u z : ℕ) (hu : 0 < u)
    [NeZero u] [NeZero (u / a.gcd u)] :
    ZMod.stdAddChar ((a * z : ℕ) : ZMod u) =
      ZMod.stdAddChar ((reducedFrequency a u hu : ZMod (u / a.gcd u)) *
        (z : ZMod (u / a.gcd u))) := by
  rw [reducedFrequency_coe, ← Nat.cast_mul]
  rw [stdAddChar_natCast, stdAddChar_natCast]
  congr 1
  have hgu : a.gcd u * (u / a.gcd u) = u :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_right a u)
  have hga : a.gcd u * (a / a.gcd u) = a :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_left a u)
  have hguC : (a.gcd u : ℂ) * ((u / a.gcd u : ℕ) : ℂ) = (u : ℂ) := by
    exact_mod_cast hgu
  have hgaC : (a.gcd u : ℂ) * ((a / a.gcd u : ℕ) : ℂ) = (a : ℂ) := by
    exact_mod_cast hga
  push_cast
  rw [← hguC, ← hgaC]
  have hg : (a.gcd u : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.gcd_pos_of_pos_right a hu).ne'
  have hq : ((u / a.gcd u : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (reduced_modulus_pos a u hu).ne'
  field_simp

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_ReducedCollisionFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- Squared fiber sizes exactly count pairs with equal images. -/
theorem sum_sq_residue_fiber_card {ι : Type*} [Fintype ι]
    {q : ℕ} [NeZero q] (f : ι → ZMod q) :
    (∑ x : ZMod q, ((Finset.univ.filter (fun i : ι => f i = x)).card : ℝ) ^ 2) =
      (indexedResidueCollisionCount f : ℝ) := by
  classical
  have hc : (∑ x : ZMod q,
      ((Finset.univ.filter (fun i : ι => f i = x)).card : ℂ) ^ 2) =
      (indexedResidueCollisionCount f : ℂ) := by
    calc
      _ = ∑ i : ι, ((Finset.univ.filter (fun j : ι => f j = f i)).card : ℂ) := by
        simpa only [pow_two] using sum_fiber_card_mul f
          (fun x => ((Finset.univ.filter (fun i : ι => f i = x)).card : ℂ))
      _ = _ := by
        simp only [indexedResidueCollisionCount, Finset.card_filter, Nat.cast_sum,
          Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        simp only [eq_comm]
  exact_mod_cast hc

/-- Exact regrouping of an indexed bilinear sum, with multiplicities. -/
theorem residue_fiber_double_sum {ι : Type*} [Fintype ι]
    {q : ℕ} [NeZero q] (f : ι → ZMod q) (g : ZMod q → ZMod q → ℂ) :
    (∑ x : ZMod q, ∑ y : ZMod q,
      ((Finset.univ.filter (fun i : ι => f i = x)).card : ℂ) *
      ((Finset.univ.filter (fun i : ι => f i = y)).card : ℂ) * g x y) =
      ∑ i : ι, ∑ j : ι, g (f i) (f j) := by
  classical
  calc
    _ = ∑ x : ZMod q,
        ((Finset.univ.filter (fun i : ι => f i = x)).card : ℂ) *
          (∑ y : ZMod q,
            ((Finset.univ.filter (fun i : ι => f i = y)).card : ℂ) * g x y) := by
      simp only [Finset.mul_sum, mul_assoc]
    _ = ∑ i : ι, ∑ y : ZMod q,
        ((Finset.univ.filter (fun j : ι => f j = y)).card : ℂ) * g (f i) y :=
      sum_fiber_card_mul f _
    _ = _ := by simp_rw [sum_fiber_card_mul]

/-- The two-sided collision estimate at a primitive frequency. It uses the
actual squared mass, not a maximum-atom estimate. -/
theorem indexed_residue_bilinear_bound {ι : Type*} [Fintype ι]
    {q : ℕ} [NeZero q] (f : ι → ZMod q) (c : (ZMod q)ˣ) :
    ‖∑ i : ι, ∑ j : ι,
      ZMod.stdAddChar ((c : ZMod q) * f i * f j)‖ ≤
      Real.sqrt (q : ℝ) * indexedResidueCollisionCount f := by
  classical
  let w : ZMod q → ℂ := fun x =>
    ((Finset.univ.filter (fun i : ι => f i = x)).card : ℂ)
  have hE : (∑ x : ZMod q, ‖w x‖ ^ 2) =
      (indexedResidueCollisionCount f : ℝ) := by
    simpa only [w, Complex.norm_natCast] using sum_sq_residue_fiber_card f
  have h := residue_bilinear_bound w w c
  have hs : (∑ x : ZMod q, ∑ y : ZMod q,
      w x * w y * ZMod.stdAddChar ((c : ZMod q) * x * y)) =
      ∑ i : ι, ∑ j : ι, ZMod.stdAddChar ((c : ZMod q) * f i * f j) :=
    residue_fiber_double_sum f _
  rw [hs, hE] at h
  simpa only [mul_assoc, Real.mul_self_sqrt (Nat.cast_nonneg _)] using h

/-- Nonprimitive frequencies reduce to their true conductor before applying
both collision factors. In particular there is no spurious ambient `sqrt(q)`
loss when the conductor is small. -/
theorem reduced_indexed_bilinear_bound {ι : Type*} [Fintype ι]
    (t : ι → ℕ) (a q : ℕ) (hq : 0 < q)
    [NeZero q] [NeZero (q / a.gcd q)] :
    ‖∑ i : ι, ∑ j : ι,
      ZMod.stdAddChar ((a * t i * t j : ℕ) : ZMod q)‖ ≤
      Real.sqrt ((q / a.gcd q : ℕ) : ℝ) *
        indexedResidueCollisionCount (fun i => (t i : ZMod (q / a.gcd q))) := by
  have h := indexed_residue_bilinear_bound
    (fun i => (t i : ZMod (q / a.gcd q))) (reducedFrequency a q hq)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [Nat.mul_assoc, stdAddChar_reduced a q _ hq, Nat.cast_mul, mul_assoc]

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_CompositeBadModuli
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- A finite natural list has the same collision count whether residues are
represented by remainders or by elements of `ZMod`. -/
theorem indexed_divisor_collision_eq (P q : ℕ) [NeZero q] :
    indexedResidueCollisionCount (fun d : ↥P.divisors => (d.val : ZMod q)) =
      (collisionPairs P.divisors (fun d => d % q)).card := by
  classical
  simp only [indexedResidueCollisionCount, collisionPairs, Finset.card_filter,
    Fintype.sum_prod_type, Finset.sum_product]
  simp_rw [ZMod.natCast_eq_natCast_iff']
  exact (Finset.sum_coe_sort P.divisors (fun a : ℕ =>
    ∑ b : ↥P.divisors, if a % q = b.val % q then 1 else 0)).trans
      (Finset.sum_congr rfl (fun a ha =>
        Finset.sum_coe_sort P.divisors (fun b : ℕ => if a % q = b % q then 1 else 0)))

/-- Exact normalized energy of the complete divisor list. -/
theorem divisorResidueEnergy_eq_collision_quotient (P q : ℕ) [NeZero q] :
    divisorResidueEnergy P q =
      ((collisionPairs P.divisors (fun d => d % q)).card : ℝ) /
        (P.divisors.card : ℝ)^2 := by
  unfold divisorResidueEnergy
  simp_rw [div_pow]
  rw [← Finset.sum_div, sum_sq_residue_fiber_card,
    indexed_divisor_collision_eq]
  simp only [Fintype.card_coe]

namespace CompositeSupply

lemma divisor_card_pos (u : ℕ) : 0 < ((base u).divisors.card : ℝ) := by
  exact_mod_cast Finset.card_pos.mpr
    (show (base u).divisors.Nonempty from
      ⟨1, Nat.one_mem_divisors.mpr (base_pos u).ne'⟩)

lemma badModulus_iff_energy {d : ℕ} [NeZero d] :
    BadModulus d ↔ 2 ≤ d ∧ (base d).Coprime d ∧
      1 / (d : ℝ)^(7 / 8 : ℝ) < divisorResidueEnergy (base d) d := by
  rw [divisorResidueEnergy_eq_collision_quotient]
  have hd : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hpow : 0 < (d : ℝ)^(7 / 8 : ℝ) := Real.rpow_pos_of_pos hd _
  have hc : 0 < ((base d).divisors.card : ℝ)^2 := pow_pos (divisor_card_pos d) 2
  unfold BadModulus
  rw [div_lt_div_iff₀ hpow hc]
  simp only [one_mul]
  ring_nf

/-- All bad moduli in a dyadic block have a large energy already in its
smaller, fixed divisor pool. This is the input for collision double counting. -/
lemma badModulus_fixed_base_energy {D d : ℕ} [NeZero d]
    (hD : 0 < D) (hDd : D ≤ d) (hd : BadModulus d) :
    1 / (d : ℝ)^(7 / 8 : ℝ) < divisorResidueEnergy (base D) d := by
  have he := (badModulus_iff_energy.mp hd).2.2
  exact he.trans_le (divisorResidueEnergy_le_of_dvd_squarefree
    (base_dvd_mono hD hDd) (base_squarefree d) hd.2.1)

/-- Collision-count version of the fixed-pool implication, ready for the
finite exceptional-modulus theorem. -/
lemma badModulus_fixed_base_collisions {D d : ℕ} [NeZero d]
    (hD : 0 < D) (hDd : D ≤ d) (hd : BadModulus d) :
    ((base D).divisors.card : ℝ)^2 ≤
      (d : ℝ)^(7 / 8 : ℝ) *
        ((collisionPairs (base D).divisors (fun a => a % d)).card : ℝ) := by
  have he := badModulus_fixed_base_energy hD hDd hd
  rw [divisorResidueEnergy_eq_collision_quotient] at he
  have hdp : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hpow : 0 < (d : ℝ)^(7 / 8 : ℝ) := Real.rpow_pos_of_pos hdp _
  have hc : 0 < ((base D).divisors.card : ℝ)^2 := pow_pos (divisor_card_pos D) 2
  have h := (div_lt_div_iff₀ hpow hc).mp he
  nlinarith

/-- The same global bad modulus satisfies the logarithmic roughness
condition needed in any smaller dyadic block. -/
lemma badModulus_prime_lower {D d p : ℕ} (hD : 2 ≤ D) (hDd : D ≤ d)
    (hd : BadModulus d) (hp : p.Prime) (hpd : p ∣ d) :
    Real.log (2 * (D : ℝ)) ≤ (p : ℝ) := by
  have hnot : ¬ p ∣ base d := by
    intro hpP
    have hh := Nat.dvd_gcd hpP hpd
    rw [hd.2.1] at hh
    exact hp.not_dvd_one hh
  apply (Real.log_le_log (by positivity : (0 : ℝ) < 2 * D)
    (show 2 * (D : ℝ) ≤ 2 * (d : ℝ) by exact_mod_cast Nat.mul_le_mul_left 2 hDd)).trans
  exact log_double_le_prime_of_not_dvd d p (hD.trans hDd) hp hnot

/-- Outside the global bad set, every conductor dividing a modulus coprime
to the ambient pool has the required ambient-pool energy bound. -/
lemma ambient_energy_le_of_not_bad {Y q d : ℕ} [NeZero d]
    (hq : 0 < q) (hqY : q ≤ Y) (hdq : d ∣ q)
    (hc : (base Y).Coprime q) (hnd : ¬ BadModulus d) (hd : 2 ≤ d) :
    divisorResidueEnergy (base Y) d ≤ 1 / (d : ℝ)^(7 / 8 : ℝ) := by
  have hdpos : 0 < d := by omega
  have hdY : d ≤ Y := (Nat.le_of_dvd hq hdq).trans hqY
  have hbase : base d ∣ base Y := base_dvd_mono hdpos hdY
  have hcY : (base Y).Coprime d := hc.coprime_dvd_right hdq
  have hcd : (base d).Coprime d := hcY.coprime_dvd_left hbase
  have hsmall : divisorResidueEnergy (base d) d ≤ 1 / (d : ℝ)^(7 / 8 : ℝ) := by
    by_contra h
    exact hnd (badModulus_iff_energy.mpr ⟨hd, hcd, lt_of_not_ge h⟩)
  exact (divisorResidueEnergy_le_of_dvd_squarefree hbase
    (base_squarefree Y) hcY).trans hsmall

/-- The same ambient estimate in the unnormalized form used by the
finite eight-product criterion. -/
lemma ambient_collisions_le_of_not_bad {Y q d : ℕ} [NeZero d]
    (hq : 0 < q) (hqY : q ≤ Y) (hdq : d ∣ q)
    (hc : (base Y).Coprime q) (hnd : ¬ BadModulus d) (hd : 2 ≤ d) :
    ((collisionPairs (base Y).divisors (fun a => a % d)).card : ℝ) ≤
      ((base Y).divisors.card : ℝ)^2 / (d : ℝ)^(7 / 8 : ℝ) := by
  have he := ambient_energy_le_of_not_bad hq hqY hdq hc hnd hd
  rw [divisorResidueEnergy_eq_collision_quotient] at he
  have hdp : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hpow : 0 < (d : ℝ)^(7 / 8 : ℝ) := Real.rpow_pos_of_pos hdp _
  have hcard : 0 < ((base Y).divisors.card : ℝ)^2 := pow_pos (divisor_card_pos Y) 2
  apply (le_div_iff₀ hpow).mpr
  have hh := (div_le_div_iff₀ hcard hpow).mp he
  nlinarith

/-- Every nontrivial conductor of a modulus coprime to the ambient pool
starts beyond the logarithmic cutoff. -/
lemma log_le_conductor {Y q d : ℕ} (hc : (base Y).Coprime q)
    (hdq : d ∣ q) (hd : 2 ≤ d) : Real.log (Y : ℝ) ≤ (d : ℝ) := by
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (by omega : d ≠ 1)
  have hnot : ¬ p ∣ base Y := by
    intro hpP
    have hcommon := Nat.dvd_gcd hpP (hpd.trans hdq)
    rw [hc] at hcommon
    exact hp.not_dvd_one hcommon
  exact (log_le_prime_of_not_dvd Y p hp hnot).trans
    (by exact_mod_cast Nat.le_of_dvd (by omega : 0 < d) hpd)

end CompositeSupply
end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_SparseBadDivisorTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.SparseBadDivisorTail

/-- Dyadic decomposition starting at an arbitrary dyadic threshold. -/
lemma sum_dyadic_from {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) (J K : ℕ) :
    (∑ n ∈ Finset.Ico (2 ^ J) (2 ^ (J + K)), f n) =
      ∑ k ∈ Finset.range K,
        ∑ n ∈ Finset.Ico (2 ^ (J + k)) (2 ^ (J + k + 1)), f n := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ← ih]
    exact (Finset.sum_Ico_consecutive f
      (Nat.pow_le_pow_right (by decide) (by omega : J ≤ J + K))
      (Nat.pow_le_pow_right (by decide) (by omega : J + K ≤ J + K + 1))).symm

/-- A dyadic shell has reciprocal mass at most its cardinality over its base. -/
lemma reciprocal_shell_le (A : Finset ℕ) (j : ℕ) :
    (∑ n ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)) ∩ A, (1 : ℝ) / n) ≤
      ((Finset.Ico (2 ^ j) (2 ^ (j + 1)) ∩ A).card : ℝ) / (2 : ℝ) ^ j := by
  calc
    _ ≤ ∑ _n ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)) ∩ A,
        (1 : ℝ) / (2 : ℝ) ^ j := by
      apply Finset.sum_le_sum
      intro n hn
      have hbase : (2 : ℝ) ^ j ≤ (n : ℝ) := by
        exact_mod_cast (Finset.mem_Ico.mp (Finset.mem_inter.mp hn).1).1
      exact one_div_le_one_div_of_le (by positivity) hbase
    _ = _ := by simp [div_eq_mul_inv]

/-- Finite reciprocal-tail estimate from dyadic cardinality bounds. The
geometric ratio `r` is the shell-growth ratio divided by two. Only shells
at or above `J` need satisfy the estimate. -/
theorem reciprocal_tail_le (A : Finset ℕ) (J : ℕ) {C r : ℝ}
    (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hA : ∀ n ∈ A, 2 ^ J ≤ n)
    (hcount : ∀ j : ℕ, J ≤ j →
      ((Finset.Ico (2 ^ j) (2 ^ (j + 1)) ∩ A).card : ℝ) ≤ C * (2 * r) ^ j) :
    (∑ n ∈ A, (1 : ℝ) / n) ≤ C * r ^ J / (1 - r) := by
  let K := Nat.log 2 (A.sup id) + 1
  let f : ℕ → ℝ := fun n => if n ∈ A then 1 / (n : ℝ) else 0
  have htop : A.sup id < 2 ^ (J + K) := by
    have ht : A.sup id < 2 ^ K := Nat.lt_pow_succ_log_self (by decide) _
    exact ht.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hsub : A ⊆ Finset.Ico (2 ^ J) (2 ^ (J + K)) := by
    intro n hn
    exact Finset.mem_Ico.mpr ⟨hA n hn, (Finset.le_sup (f := id) hn).trans_lt htop⟩
  have hsum : (∑ n ∈ A, (1 : ℝ) / n) =
      ∑ n ∈ Finset.Ico (2 ^ J) (2 ^ (J + K)), f n := by
    calc
      _ = ∑ n ∈ A, f n := Finset.sum_congr rfl (by intro n hn; simp [f, hn])
      _ = _ := Finset.sum_subset hsub (by intro n _ hn; simp [f, hn])
  have hblock (j : ℕ) (hj : J ≤ j) :
      (∑ n ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), f n) ≤ C * r ^ j := by
    have heq : (∑ n ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), f n) =
        ∑ n ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)) ∩ A, (1 : ℝ) / n := by
      simp only [f, ← Finset.sum_filter]
      congr 1
    rw [heq]
    calc
      _ ≤ ((Finset.Ico (2 ^ j) (2 ^ (j + 1)) ∩ A).card : ℝ) / (2 : ℝ) ^ j :=
        reciprocal_shell_le A j
      _ ≤ (C * (2 * r) ^ j) / (2 : ℝ) ^ j :=
        div_le_div_of_nonneg_right (hcount j hj) (by positivity)
      _ = C * r ^ j := by rw [mul_pow]; field_simp
  rw [hsum, sum_dyadic_from]
  calc
    _ ≤ ∑ k ∈ Finset.range K, C * r ^ (J + k) :=
      Finset.sum_le_sum (fun k _ => hblock (J + k) (by omega))
    _ = C * r ^ J * ∑ k ∈ Finset.range K, r ^ k := by
      simp_rw [pow_add]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intros
      ring
    _ ≤ C * r ^ J * ∑' k : ℕ, r ^ k :=
      mul_le_mul_of_nonneg_left
        ((summable_geometric_of_lt_one hr0 hr1).sum_le_tsum _ (by intros; positivity))
        (by positivity)
    _ = C * r ^ J / (1 - r) := by
      rw [tsum_geometric_of_lt_one hr0 hr1]
      rfl


lemma card_positive_multiples (Y d : ℕ) :
    ((Finset.Icc 1 Y).filter (fun n => d ∣ n)).card = Y / d := by
  have heq : (Finset.Icc 1 Y).filter (fun n => d ∣ n) =
      (Finset.range (Y + 1)).filter (fun n => n ≠ 0 ∧ d ∣ n) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
    omega
  rw [heq, Nat.card_multiples']

/-- The union bound for exceptional divisors has no additive endpoint error. -/
theorem divisorMultiples_card_le (A : Finset ℕ) (Y : ℕ) :
    ((divisorMultiples A Y).card : ℝ) ≤
      (Y : ℝ) * ∑ d ∈ A, (1 : ℝ) / d := by
  have heq : divisorMultiples A Y =
      A.biUnion (fun d => (Finset.Icc 1 Y).filter (fun n => d ∣ n)) := by
    ext n
    simp only [divisorMultiples, Finset.mem_filter, Finset.mem_biUnion]
    aesop
  rw [heq]
  calc
    _ ≤ ∑ d ∈ A, (((Finset.Icc 1 Y).filter (fun n => d ∣ n)).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ = ∑ d ∈ A, ((Y / d : ℕ) : ℝ) := by simp_rw [card_positive_multiples]
    _ ≤ ∑ d ∈ A, (Y : ℝ) / d :=
      Finset.sum_le_sum (fun d _ => Nat.cast_div_le)
    _ = (Y : ℝ) * ∑ d ∈ A, (1 : ℝ) / d := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intros
      simp [div_eq_mul_inv]

/-- Global dyadic counts control every finite truncation of the reciprocal tail. -/
theorem badTail_reciprocal_le (B : ℕ → Prop) [DecidablePred B]
    (J Y : ℕ) {C r : ℝ} (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hcount : ∀ j : ℕ, J ≤ j →
      (((Finset.Ico (2 ^ j) (2 ^ (j + 1))).filter B).card : ℝ) ≤ C * (2 * r) ^ j) :
    (∑ d ∈ badTail B J Y, (1 : ℝ) / d) ≤ C * r ^ J / (1 - r) := by
  apply reciprocal_tail_le (badTail B J Y) J hC hr0 hr1
  · intro n hn
    exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
  · intro j hj
    have hsub : Finset.Ico (2 ^ j) (2 ^ (j + 1)) ∩ badTail B J Y ⊆
        (Finset.Ico (2 ^ j) (2 ^ (j + 1))).filter B := by
      intro n hn
      obtain ⟨h1, h2⟩ := Finset.mem_inter.mp hn
      exact Finset.mem_filter.mpr ⟨h1, (Finset.mem_filter.mp h2).2⟩
    have hcard : ((Finset.Ico (2 ^ j) (2 ^ (j + 1)) ∩ badTail B J Y).card : ℝ) ≤
        (((Finset.Ico (2 ^ j) (2 ^ (j + 1))).filter B).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    exact hcard.trans (hcount j hj)

/-- Uniform exceptional-multiple density, with the explicit geometric tail. -/
theorem badTail_multiples_card_le (B : ℕ → Prop) [DecidablePred B]
    (J Y : ℕ) {C r : ℝ} (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hcount : ∀ j : ℕ, J ≤ j →
      (((Finset.Ico (2 ^ j) (2 ^ (j + 1))).filter B).card : ℝ) ≤ C * (2 * r) ^ j) :
    ((divisorMultiples (badTail B J Y) Y).card : ℝ) ≤
      (Y : ℝ) * (C * r ^ J / (1 - r)) := by
  exact (divisorMultiples_card_le _ _).trans
    (mul_le_mul_of_nonneg_left (badTail_reciprocal_le B J Y hC hr0 hr1 hcount)
      (Nat.cast_nonneg Y))

/-- Dyadic sublinear exceptional counts give a density tending uniformly to
zero as the excluded divisor threshold grows. The onset of the shell estimate
may be arbitrary but fixed. -/
theorem eventually_badTail_multiples_small (B : ℕ → Prop) [DecidablePred B]
    (J₀ : ℕ) {C r : ℝ} (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hcount : ∀ j : ℕ, J₀ ≤ j →
      (((Finset.Ico (2 ^ j) (2 ^ (j + 1))).filter B).card : ℝ) ≤ C * (2 * r) ^ j) :
    ∀ ε : ℝ, 0 < ε → ∃ J₁ : ℕ, J₀ ≤ J₁ ∧ ∀ J : ℕ, J₁ ≤ J → ∀ Y : ℕ,
      ((divisorMultiples (badTail B J Y) Y).card : ℝ) ≤ ε * Y := by
  intro ε hε
  have hlim : Filter.Tendsto (fun J : ℕ => C * r ^ J / (1 - r))
      Filter.atTop (nhds 0) := by
    have hc : Filter.Tendsto (fun _ : ℕ => C) Filter.atTop (nhds C) := tendsto_const_nhds
    have h := (hc.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1)).div_const (1 - r)
    simpa using h
  obtain ⟨J₂, hJ₂⟩ := Filter.eventually_atTop.mp (hlim.eventually_lt_const hε)
  refine ⟨max J₀ J₂, le_max_left _ _, ?_⟩
  intro J hJ Y
  have hJ0 : J₀ ≤ J := (le_max_left _ _).trans hJ
  have hJ2 : J₂ ≤ J := (le_max_right _ _).trans hJ
  have hbound := badTail_multiples_card_le B J Y hC hr0 hr1
    (fun j hj => hcount j (hJ0.trans hj))
  calc
    _ ≤ (Y : ℝ) * (C * r ^ J / (1 - r)) := hbound
    _ ≤ (Y : ℝ) * ε := mul_le_mul_of_nonneg_left (hJ₂ J hJ2).le (Nat.cast_nonneg Y)
    _ = ε * Y := mul_comm _ _


/-- The usual sublinear-power form of the uniform density statement. -/
theorem eventually_badTail_multiples_small_of_power (B : ℕ → Prop) [DecidablePred B]
    (J₀ : ℕ) {C β : ℝ} (hC : 0 ≤ C) (hβ : β < 1)
    (hcount : ∀ j : ℕ, J₀ ≤ j →
      (((Finset.Ico (2 ^ j) (2 ^ (j + 1))).filter B).card : ℝ) ≤
        C * ((2 : ℝ) ^ j) ^ β) :
    ∀ ε : ℝ, 0 < ε → ∃ J₁ : ℕ, J₀ ≤ J₁ ∧ ∀ J : ℕ, J₁ ≤ J → ∀ Y : ℕ,
      ((divisorMultiples (badTail B J Y) Y).card : ℝ) ≤ ε * Y := by
  let r : ℝ := (2 : ℝ) ^ β / 2
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by
    dsimp [r]
    apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    simpa using Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hβ
  apply eventually_badTail_multiples_small B J₀ hC hr0 hr1
  intro j hj
  have heq : (2 * r) ^ j = ((2 : ℝ) ^ j) ^ β := by
    have hr : 2 * r = (2 : ℝ) ^ β := by dsimp [r]; ring
    rw [hr]
    exact Real.rpow_pow_comm (by norm_num) β j
  rw [heq]
  exact hcount j hj


lemma divisorMultiples_mono {A A' : Finset ℕ} (Y : ℕ) (hA : A ⊆ A') :
    divisorMultiples A Y ⊆ divisorMultiples A' Y := by
  intro n hn
  obtain ⟨hn, d, hd, hdn⟩ := Finset.mem_filter.mp hn
  exact Finset.mem_filter.mpr ⟨hn, d, hA hd, hdn⟩

/-- The finite divisor cutoff is semantically redundant for positive multiples. -/
lemma mem_divisorMultiples_badAbove (B : ℕ → Prop) [DecidablePred B]
    (R Y n : ℕ) :
    n ∈ divisorMultiples ((Finset.Icc R Y).filter B) Y ↔
      1 ≤ n ∧ n ≤ Y ∧ ∃ d : ℕ, R ≤ d ∧ B d ∧ d ∣ n := by
  simp only [divisorMultiples, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hn1, hnY⟩, d, ⟨⟨hRd, _⟩, hBd⟩, hdn⟩
    exact ⟨hn1, hnY, d, hRd, hBd, hdn⟩
  · rintro ⟨hn1, hnY, d, hRd, hBd, hdn⟩
    have hdY : d ≤ Y := (Nat.le_of_dvd (by omega : 0 < n) hdn).trans hnY
    exact ⟨⟨hn1, hnY⟩, d, ⟨⟨hRd, hdY⟩, hBd⟩, hdn⟩

/-- An arbitrary growing lower cutoff can be used, not just a dyadic one.
The conclusion is uniform in the ambient integer interval. -/
theorem eventually_large_bad_divisor_multiples_small (B : ℕ → Prop) [DecidablePred B]
    (J₀ : ℕ) {C β : ℝ} (hC : 0 ≤ C) (hβ : β < 1)
    (hcount : ∀ j : ℕ, J₀ ≤ j →
      (((Finset.Ico (2 ^ j) (2 ^ (j + 1))).filter B).card : ℝ) ≤
        C * ((2 : ℝ) ^ j) ^ β) :
    ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℕ, 1 ≤ R₀ ∧ ∀ R : ℕ, R₀ ≤ R → ∀ Y : ℕ,
      ((divisorMultiples ((Finset.Icc R Y).filter B) Y).card : ℝ) ≤ ε * Y := by
  intro ε hε
  obtain ⟨J, _, hJ⟩ := eventually_badTail_multiples_small_of_power
    B J₀ hC hβ hcount ε hε
  refine ⟨2 ^ J, Nat.succ_le_iff.mpr (by positivity), ?_⟩
  intro R hR Y
  have hsub : (Finset.Icc R Y).filter B ⊆ badTail B J Y := by
    intro d hd
    obtain ⟨hdI, hBd⟩ := Finset.mem_filter.mp hd
    obtain ⟨hRd, hdY⟩ := Finset.mem_Icc.mp hdI
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hR.trans hRd, hdY⟩, hBd⟩
  have hcard : ((divisorMultiples ((Finset.Icc R Y).filter B) Y).card : ℝ) ≤
      ((divisorMultiples (badTail B J Y) Y).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (divisorMultiples_mono Y hsub)
  exact hcard.trans (hJ J le_rfl Y)

end Problem337.SparseBadDivisorTail

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_CompositeBadDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open Filter
open scoped BigOperators

namespace Problem337.CompositeSupply

attribute [local instance] OAI.Problem337.CompositeSupply.instDecidablePredNatBadModulus
lemma mem_badMultiples_iff (Y n : ℕ) :
    n ∈ badMultiples Y ↔ 1 ≤ n ∧ n ≤ Y ∧
      ∃ d : ℕ, ⌊Real.log (Y : ℝ)⌋₊ ≤ d ∧ BadModulus d ∧ d ∣ n := by
  classical
  exact SparseBadDivisorTail.mem_divisorMultiples_badAbove
    BadModulus ⌊Real.log (Y : ℝ)⌋₊ Y n

/-- Every conductor of a residual modulus avoids the global bad set if
its original positive multiple avoids `badMultiples`. -/
lemma not_bad_of_not_mem_badMultiples {Y n q d : ℕ}
    (hn : 1 ≤ n) (hnY : n ≤ Y) (hqn : q ∣ n)
    (hc : (base Y).Coprime q) (hne : n ∉ badMultiples Y)
    (hdq : d ∣ q) (hd : 2 ≤ d) : ¬ BadModulus d := by
  intro hb
  have hlog := log_le_conductor hc hdq hd
  have hfloor : ⌊Real.log (Y : ℝ)⌋₊ ≤ d := by
    have hh := (Nat.floor_le (Real.log_natCast_nonneg Y)).trans hlog
    exact_mod_cast hh
  exact hne ((mem_badMultiples_iff Y n).mpr
    ⟨hn, hnY, d, hfloor, hb, hdq.trans hqn⟩)

/-- A sublinear shell count gives a vanishing exceptional-multiple density
at the actual logarithmic conductor cutoff. The shell hypothesis is the
only input; the cutoff and the product-energy transport are unconditional. -/
theorem eventually_badMultiples_card_le_of_shell_bound
    {C β : ℝ} (hC : 0 ≤ C) (hβ : β < 1)
    (hcount : ∀ᶠ j : ℕ in atTop,
      (((Finset.Ico (2 ^ j) (2 ^ (j + 1))).filter BadModulus).card : ℝ) ≤
        C * ((2 : ℝ) ^ j) ^ β) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ Y : ℕ in atTop,
      ((badMultiples Y).card : ℝ) ≤ ε * Y := by
  classical
  intro ε hε
  obtain ⟨J, hJ⟩ := eventually_atTop.mp hcount
  obtain ⟨R, hR, hbound⟩ :=
    SparseBadDivisorTail.eventually_large_bad_divisor_multiples_small
      BadModulus J hC hβ hJ ε hε
  have hlog : Tendsto (fun Y : ℕ => Real.log (Y : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually_ge_atTop (R : ℝ)] with Y hY
  have hfloor : R ≤ ⌊Real.log (Y : ℝ)⌋₊ := Nat.le_floor hY
  exact hbound _ hfloor Y

end Problem337.CompositeSupply

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_WeightedBinomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- A weighted binomial bound, allowing a real cutoff on subset size. -/
theorem weighted_binomial_bound (L : ℕ) (t q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    (∑ j ∈ (Finset.range (L + 1)).filter (fun j : ℕ => (j : ℝ) ≤ t),
      (Nat.choose L j : ℝ)) ≤ q ^ (-t) * (1 + q) ^ L := by
  have hw : q ^ t *
      (∑ j ∈ (Finset.range (L + 1)).filter (fun j : ℕ => (j : ℝ) ≤ t),
        (Nat.choose L j : ℝ)) ≤ (1 + q) ^ L := by
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ j ∈ (Finset.range (L + 1)).filter (fun j : ℕ => (j : ℝ) ≤ t),
          q ^ j * (Nat.choose L j : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
        simpa only [Real.rpow_natCast] using
          Real.rpow_le_rpow_of_exponent_ge hq0 hq1 (Finset.mem_filter.mp hj).2
      _ ≤ ∑ j ∈ Finset.range (L + 1), q ^ j * (Nat.choose L j : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro j hj hnot
        positivity
      _ = (1 + q) ^ L := by
        rw [show 1 + q = q + 1 by ring, add_pow]
        simp
  have hqt : 0 < q ^ t := Real.rpow_pos_of_pos hq0 t
  have hdiv :
      (∑ j ∈ (Finset.range (L + 1)).filter (fun j : ℕ => (j : ℝ) ≤ t),
        (Nat.choose L j : ℝ)) ≤ (1 + q) ^ L / q ^ t :=
    (le_div_iff₀ hqt).2 (by simpa only [mul_comm] using hw)
  simpa only [Real.rpow_neg hq0.le, div_eq_mul_inv, mul_comm] using hdiv

/-- Exponential form of the weighted subset count used in divisor estimates. -/
theorem weighted_binomial_exp_bound (L : ℕ) (t q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    (∑ j ∈ (Finset.range (L + 1)).filter (fun j : ℕ => (j : ℝ) ≤ t),
      (Nat.choose L j : ℝ)) ≤ Real.exp (-t * Real.log q + (L : ℝ) * q) := by
  apply (weighted_binomial_bound L t q hq0 hq1).trans
  have hqadd : 0 < 1 + q := by positivity
  rw [← Real.rpow_natCast (1 + q) L,
    Real.rpow_def_of_pos hq0, Real.rpow_def_of_pos hqadd, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hlog : Real.log (1 + q) ≤ q := by
    simpa using Real.log_le_sub_one_of_pos hqadd
  nlinarith [mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg L : (0 : ℝ) ≤ L)]

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_LargePrimeDivisors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- Counting prime-factor sublists, with multiplicities labeled, overcounts divisors. -/
theorem truncatedDivisorCount_le_binomial_of_length (X t : ℝ) {n : ℕ} (hn : n ≠ 0)
    (hlen : ∀ a ∈ n.divisors, (a : ℝ) ≤ X → (a.primeFactorsList.length : ℝ) ≤ t) :
    truncatedDivisorCount X n ≤
      ∑ j ∈ (Finset.range (n.primeFactorsList.length + 1)).filter
          (fun j : ℕ => (j : ℝ) ≤ t), Nat.choose n.primeFactorsList.length j := by
  let S := (Finset.range (n.primeFactorsList.length + 1)).filter
    (fun j : ℕ => (j : ℝ) ≤ t)
  calc
    truncatedDivisorCount X n ≤
        (S.biUnion fun j => (n.primeFactorsList.sublistsLen j).toFinset).card := by
      apply Finset.card_le_card_of_injOn (fun a : ℕ => a.primeFactorsList)
      · intro a ha
        obtain ⟨had, haX⟩ := Finset.mem_filter.mp ha
        have hsub := Nat.primeFactorsList_sublist_of_dvd (Nat.mem_divisors.mp had).1 hn
        apply Finset.mem_biUnion.mpr
        refine ⟨a.primeFactorsList.length, ?_, ?_⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := hsub.length_le; omega),
            hlen a had haX⟩
        · exact List.mem_toFinset.mpr (List.mem_sublistsLen.mpr ⟨hsub, rfl⟩)
      · intro a ha b hb hab
        have ha0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors (Finset.mem_filter.mp ha).1)
        have hb0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors (Finset.mem_filter.mp hb).1)
        have hp := congrArg List.prod hab
        simpa only [Nat.prod_primeFactorsList ha0, Nat.prod_primeFactorsList hb0] using hp
    _ ≤ ∑ j ∈ S, (n.primeFactorsList.sublistsLen j).toFinset.card :=
      Finset.card_biUnion_le
    _ ≤ ∑ j ∈ S, Nat.choose n.primeFactorsList.length j := by
      apply Finset.sum_le_sum
      intro j hj
      simpa only [List.length_sublistsLen] using
        List.toFinset_card_le (n.primeFactorsList.sublistsLen j)

private theorem pow_length_le_nat_list_prod (z : ℝ) (hz : 0 ≤ z) (l : List ℕ)
    (hl : ∀ a ∈ l, z ≤ (a : ℝ)) : z ^ l.length ≤ (l.prod : ℝ) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha : z ≤ (a : ℝ) := hl a (by simp)
    have ht : z ^ l.length ≤ (l.prod : ℝ) := ih (by intro b hb; exact hl b (by simp [hb]))
    simpa only [List.length_cons, List.prod_cons, Nat.cast_mul, pow_succ, mul_comm z] using
      mul_le_mul ha ht (pow_nonneg hz _) (Nat.cast_nonneg a)

/-- If all prime factors are at least z, their number is bounded by log n / log z. -/
theorem primeFactorsList_length_le_log {n : ℕ} (hn : n ≠ 0) {z : ℝ} (hz : 1 < z)
    (hlarge : ∀ p ∈ n.primeFactorsList, z ≤ (p : ℝ)) :
    (n.primeFactorsList.length : ℝ) ≤ Real.log (n : ℝ) / Real.log z := by
  have hz0 : 0 < z := lt_trans zero_lt_one hz
  have hp := pow_length_le_nat_list_prod z hz0.le n.primeFactorsList hlarge
  rw [Nat.prod_primeFactorsList hn] at hp
  apply (le_div_iff₀ (Real.log_pos hz)).2
  simpa only [Real.log_pow] using Real.log_le_log (pow_pos hz0 _) hp

/-- Large prime factors give the standard weighted-binomial divisor bound. -/
theorem truncatedDivisorCount_large_primes_exp (X z q : ℝ) {n : ℕ} (hn : n ≠ 0)
    (hz : 1 < z) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hlarge : ∀ p ∈ n.primeFactorsList, z ≤ (p : ℝ)) :
    (truncatedDivisorCount X n : ℝ) ≤
      Real.exp (-(Real.log X / Real.log z) * Real.log q +
        (n.primeFactorsList.length : ℝ) * q) := by
  apply le_trans _ (weighted_binomial_exp_bound n.primeFactorsList.length
    (Real.log X / Real.log z) q hq0 hq1)
  have hcount := truncatedDivisorCount_le_binomial_of_length X
    (Real.log X / Real.log z) hn (by
      intro a ha haX
      have ha0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors ha)
      have hsub := Nat.primeFactorsList_subset_of_dvd (Nat.mem_divisors.mp ha).1 hn
      apply (primeFactorsList_length_le_log ha0 hz (by
        intro p hp; exact hlarge p (hsub hp))).trans
      apply div_le_div_of_nonneg_right _ (Real.log_pos hz).le
      exact Real.log_le_log (by exact_mod_cast Nat.pos_of_mem_divisors ha) haX)
  exact_mod_cast hcount

/-- The large-prime divisor estimate in the entropy form used by the manuscript. -/
theorem truncatedDivisorCount_large_primes_bound (X z W : ℝ) {n : ℕ} (hn : n ≠ 0)
    (hX : 1 < X) (hz : 1 < z) (hXW : Real.log X ≤ W)
    (hnW : Real.log (n : ℝ) ≤ W)
    (hlarge : ∀ p ∈ n.primeFactorsList, z ≤ (p : ℝ)) :
    (truncatedDivisorCount X n : ℝ) ≤
      Real.exp ((1 + Real.log (W / Real.log X)) * Real.log X / Real.log z) := by
  have hv : 0 < Real.log X := Real.log_pos hX
  have hW : 0 < W := lt_of_lt_of_le hv hXW
  have hlz : 0 < Real.log z := Real.log_pos hz
  have hq0 : 0 < Real.log X / W := div_pos hv hW
  have hq1 : Real.log X / W ≤ 1 := (div_le_one hW).2 hXW
  apply (truncatedDivisorCount_large_primes_exp X z (Real.log X / W)
    hn hz hq0 hq1 hlarge).trans
  apply Real.exp_le_exp.mpr
  have hlen : (n.primeFactorsList.length : ℝ) ≤ W / Real.log z :=
    (primeFactorsList_length_le_log hn hz hlarge).trans
      (div_le_div_of_nonneg_right hnW hlz.le)
  calc
    _ ≤ -(Real.log X / Real.log z) * Real.log (Real.log X / W) +
        (W / Real.log z) * (Real.log X / W) := by
      linarith [mul_le_mul_of_nonneg_right hlen hq0.le]
    _ = _ := by
      rw [Real.log_div (ne_of_gt hv) (ne_of_gt hW),
        Real.log_div (ne_of_gt hW) (ne_of_gt hv)]
      field_simp
      ring

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_RoughDivisorAsymptotic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

open Filter

namespace Problem337

/-- At the logarithmic roughness threshold, the elementary entropy exponent
for divisors of numbers of size `exp (A log X log log X)` is sublinear in
`log X`. All estimates are uniform in the integer being factored. -/
theorem eventually_rough_entropy_le_rpow (A ε : ℝ) (hA : 0 < A) (hε : 0 < ε) :
    ∀ᶠ X : ℝ in atTop,
      1 < X ∧ 1 < Real.log X ∧
      Real.log X ≤ A * Real.log X * Real.log (Real.log X) ∧
      Real.exp ((1 + Real.log
        ((A * Real.log X * Real.log (Real.log X)) / Real.log X)) *
          Real.log X / Real.log (Real.log X)) ≤ X ^ ε := by
  have hx : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
  have ht : Tendsto (fun X : ℝ => Real.log (Real.log X)) atTop atTop := hx.comp hx
  have hhalf : 0 < ε / 2 := by positivity
  filter_upwards [eventually_ge_atTop (2 : ℝ), hx.eventually_ge_atTop 2,
    ht.eventually_ge_atTop 1, ht.eventually_ge_atTop (1 / A),
    ht.eventually_ge_atTop (2 * (1 + |Real.log A|) / ε),
    ht.eventually (Real.isLittleO_log_id_atTop.bound hhalf)]
    with X hX hx2 ht1 htA htc hsmall
  have hxpos : 0 < Real.log X := by linarith
  have htpos : 0 < Real.log (Real.log X) := by linarith
  have hAt : 1 ≤ A * Real.log (Real.log X) := by
    have h := (div_le_iff₀ hA).mp htA
    nlinarith
  have hconst : 1 + Real.log A ≤ ε / 2 * Real.log (Real.log X) := by
    have h := (div_le_iff₀ hε).mp htc
    have hc := le_abs_self (Real.log A)
    nlinarith
  have hlogsmall : Real.log (Real.log (Real.log X)) ≤
      ε / 2 * Real.log (Real.log X) := by
    change ‖Real.log (Real.log (Real.log X))‖ ≤
      ε / 2 * ‖Real.log (Real.log X)‖ at hsmall
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos htpos] at hsmall
    exact (le_abs_self _).trans hsmall
  have hbracket : 1 + Real.log (A * Real.log (Real.log X)) ≤
      ε * Real.log (Real.log X) := by
    rw [Real.log_mul hA.ne' htpos.ne']
    linarith
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · nlinarith
  · rw [Real.rpow_def_of_pos (by linarith : 0 < X)]
    apply Real.exp_le_exp.mpr
    have hcancel : A * Real.log X * Real.log (Real.log X) / Real.log X =
        A * Real.log (Real.log X) := by
      field_simp
    rw [hcancel]
    apply (div_le_iff₀ htpos).mpr
    nlinarith [mul_le_mul_of_nonneg_right hbracket hxpos.le]

/-- Uniform subpower counting for logarithmically rough integers in the
prime-product size window. Repeated prime factors are allowed. -/
theorem eventually_truncatedDivisorCount_rough_subpower
    (A ε : ℝ) (hA : 0 < A) (hε : 0 < ε) :
    ∀ᶠ X : ℝ in atTop, ∀ n : ℕ, n ≠ 0 →
      Real.log (n : ℝ) ≤ A * Real.log X * Real.log (Real.log X) →
      (∀ p ∈ n.primeFactorsList, Real.log X ≤ (p : ℝ)) →
      (truncatedDivisorCount X n : ℝ) ≤ X ^ ε := by
  filter_upwards [eventually_rough_entropy_le_rpow A ε hA hε] with X hX
  intro n hn hnsize hrough
  exact (truncatedDivisorCount_large_primes_bound X (Real.log X)
    (A * Real.log X * Real.log (Real.log X)) hn hX.1 hX.2.1 hX.2.2.1
    hnsize hrough).trans hX.2.2.2

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_RoughPart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

theorem roughPart_pos (R : ℝ) (n : ℕ) : 0 < roughPart R n := by
  apply List.prod_pos
  intro p hp
  exact (Nat.prime_of_mem_primeFactorsList (List.mem_filter.mp hp).1).pos

theorem roughPart_dvd (R : ℝ) {n : ℕ} (hn : n ≠ 0) : roughPart R n ∣ n := by
  have h := (List.filter_sublist
    (p := fun p : ℕ => decide (R ≤ (p : ℝ))) (l := n.primeFactorsList)).prod_dvd_prod
  obtain ⟨k, hk⟩ := h
  exact ⟨k, by simpa only [roughPart, Nat.prod_primeFactorsList hn] using hk⟩

theorem roughPart_le (R : ℝ) {n : ℕ} (hn : n ≠ 0) : roughPart R n ≤ n :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (roughPart_dvd R hn)

theorem roughPart_log_le (R : ℝ) {n : ℕ} (hn : n ≠ 0) :
    Real.log (roughPart R n : ℝ) ≤ Real.log (n : ℝ) := by
  exact Real.log_le_log (by exact_mod_cast roughPart_pos R n)
    (by exact_mod_cast roughPart_le R hn)

theorem roughPart_primeFactorsList (R : ℝ) (n : ℕ) :
    (n.primeFactorsList.filter (fun p : ℕ => R ≤ (p : ℝ))).Perm
      (roughPart R n).primeFactorsList := by
  exact Nat.primeFactorsList_unique rfl (fun p hp =>
    Nat.prime_of_mem_primeFactorsList (List.mem_filter.mp hp).1)

theorem roughPart_large (R : ℝ) (n : ℕ) :
    ∀ p ∈ (roughPart R n).primeFactorsList, R ≤ (p : ℝ) := by
  intro p hp
  have h := (roughPart_primeFactorsList R n).mem_iff.mpr hp
  exact of_decide_eq_true (List.mem_filter.mp h).2

/-- Divisibility in the rough part is exactly divisibility in the original
integer together with the roughness of the divisor, not of the ambient integer. -/
theorem dvd_roughPart_iff (R : ℝ) {n d : ℕ} (hn : n ≠ 0) :
    d ∣ roughPart R n ↔ d ∣ n ∧ ∀ p ∈ d.primeFactorsList, R ≤ (p : ℝ) := by
  constructor
  · intro hd
    refine ⟨hd.trans (roughPart_dvd R hn), ?_⟩
    intro p hp
    exact roughPart_large R n p
      (Nat.primeFactorsList_subset_of_dvd hd (roughPart_pos R n).ne' hp)
  · rintro ⟨hd, hlarge⟩
    have hd0 : d ≠ 0 := (Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hn)).ne'
    have hsub := List.Sublist.filter (fun p : ℕ => decide (R ≤ (p : ℝ)))
      (Nat.primeFactorsList_sublist_of_dvd hd hn)
    have hfilter : d.primeFactorsList.filter (fun p : ℕ => R ≤ (p : ℝ)) =
        d.primeFactorsList := by
      apply List.filter_eq_self.mpr
      intro p hp
      exact decide_eq_true (hlarge p hp)
    have h := hsub.prod_dvd_prod
    rw [hfilter, Nat.prod_primeFactorsList hd0] at h
    exact h

/-- Any finite family of rough divisors is bounded by the existing truncated
count of the single rough part. This is the transport needed for differences
of samples, whose small prime factors must not be excluded. -/
theorem rough_divisor_card_le_truncated_roughPart (R X : ℝ) {n : ℕ}
    (hn : n ≠ 0) (s : Finset ℕ)
    (hdiv : ∀ d ∈ s, d ∣ n)
    (hsmall : ∀ d ∈ s, (d : ℝ) ≤ X)
    (hrough : ∀ d ∈ s, ∀ p ∈ d.primeFactorsList, R ≤ (p : ℝ)) :
    s.card ≤ truncatedDivisorCount X (roughPart R n) := by
  classical
  apply Finset.card_le_card
  intro d hd
  exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr
    ⟨(dvd_roughPart_iff R hn).mpr ⟨hdiv d hd, hrough d hd⟩,
      (roughPart_pos R n).ne'⟩, hsmall d hd⟩

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_RestrictedRoughAsymptotic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open Filter

namespace Problem337

/-- Uniform subpower bound for rough divisors of an arbitrary positive integer.
The ambient integer may have small prime factors. The threshold and the finite
family may both vary after the single eventual size threshold is chosen. -/
theorem eventually_rough_divisor_card_subpower
    (A ε : ℝ) (hA : 0 < A) (hε : 0 < ε) :
    ∀ᶠ X : ℝ in atTop, ∀ n : ℕ, n ≠ 0 →
      Real.log (n : ℝ) ≤ A * Real.log X * Real.log (Real.log X) →
      ∀ R : ℝ, Real.log X ≤ R → ∀ s : Finset ℕ,
      (∀ d ∈ s, d ∣ n) → (∀ d ∈ s, (d : ℝ) ≤ X) →
      (∀ d ∈ s, ∀ p ∈ d.primeFactorsList, R ≤ (p : ℝ)) →
      (s.card : ℝ) ≤ X ^ ε := by
  filter_upwards [eventually_truncatedDivisorCount_rough_subpower A ε hA hε]
    with X hX
  intro n hn hsize R hR s hdiv hsmall hrough
  have hcount := hX (roughPart R n) (roughPart_pos R n).ne'
    ((roughPart_log_le R hn).trans hsize)
    (fun p hp => hR.trans (roughPart_large R n p hp))
  exact (show (s.card : ℝ) ≤ truncatedDivisorCount X (roughPart R n) by
    exact_mod_cast rough_divisor_card_le_truncated_roughPart R X hn s
      hdiv hsmall hrough).trans hcount

/-- The literal filtered-divisor-set version of the preceding uniform bound. -/
theorem eventually_card_rough_divisors_subpower
    (A ε : ℝ) (hA : 0 < A) (hε : 0 < ε) :
    ∀ᶠ X : ℝ in atTop, ∀ n : ℕ, n ≠ 0 →
      Real.log (n : ℝ) ≤ A * Real.log X * Real.log (Real.log X) →
      ∀ R : ℝ, Real.log X ≤ R →
      ((n.divisors.filter (fun d : ℕ => (d : ℝ) ≤ X ∧
        ∀ p ∈ d.primeFactorsList, R ≤ (p : ℝ))).card : ℝ) ≤ X ^ ε := by
  classical
  filter_upwards [eventually_rough_divisor_card_subpower A ε hA hε] with X hX
  intro n hn hsize R hR
  apply hX n hn hsize R hR
  · intro d hd
    exact Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
  · intro d hd
    exact (Finset.mem_filter.mp hd).2.1
  · intro d hd
    exact (Finset.mem_filter.mp hd).2.2

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_RoughModulusCollision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- A collision-energy threshold, rather than a small-image hypothesis,
also permits the larger-sieve double count. The diagonal is removed before
using the bound on how many maps can identify two distinct inputs. -/
theorem large_collision_maps_card_le {ι α : Type*} {β : ι → Type*}
    [DecidableEq ι] [DecidableEq α] [∀ i, DecidableEq (β i)]
    (I : Finset ι) (A : Finset α) (f : ∀ i, α → β i)
    {H R : ℝ} (hH : 0 < H) (hR : 0 ≤ R)
    (hsize : 2 * H ≤ (A.card : ℝ))
    (henergy : ∀ i ∈ I,
      (A.card : ℝ) ^ 2 ≤ H * ((collisionPairs A (f i)).card : ℝ))
    (hpairs : ∀ p ∈ A.offDiag,
      ((I.filter (fun i => f i p.1 = f i p.2)).card : ℝ) ≤ R) :
    (I.card : ℝ) ≤ 2 * H * R := by
  classical
  have hlow : ∀ i ∈ I, (A.card : ℝ) ^ 2 / (2 * H) ≤
      ((A.offDiag.bipartiteAbove (fun i p => f i p.1 = f i p.2) i).card : ℝ) := by
    intro i hi
    have heq : A.offDiag.bipartiteAbove (fun i p => f i p.1 = f i p.2) i =
        strictCollisionPairs A (f i) := by
      ext p
      simp only [Finset.mem_bipartiteAbove, Finset.mem_offDiag,
        strictCollisionPairs, collisionPairs, Finset.mem_filter, Finset.mem_product]
      tauto
    rw [heq]
    have hdiag : ((collisionPairs A (f i)).card : ℝ) =
        ((strictCollisionPairs A (f i)).card : ℝ) + (A.card : ℝ) := by
      exact_mod_cast collision_card_eq_strict_add A (f i)
    have he := henergy i hi
    rw [hdiag] at he
    have hmul := mul_nonneg (Nat.cast_nonneg A.card : (0 : ℝ) ≤ A.card)
      (sub_nonneg.mpr hsize)
    apply (div_le_iff₀ (by positivity : 0 < 2 * H)).mpr
    nlinarith
  have hdouble := Finset.card_nsmul_le_card_nsmul
    (R := ℝ) (s := I) (t := A.offDiag)
    (m := (A.card : ℝ) ^ 2 / (2 * H)) (n := R)
    (fun (i : ι) (p : α × α) => f i p.1 = f i p.2) hlow hpairs
  simp only [nsmul_eq_mul] at hdouble
  have hoffnat : A.offDiag.card ≤ A.card ^ 2 := by
    calc
      A.offDiag.card ≤ (A ×ˢ A).card := Finset.card_le_card (by
        intro p hp
        exact Finset.mem_product.mpr ⟨(Finset.mem_offDiag.mp hp).1,
          (Finset.mem_offDiag.mp hp).2.1⟩)
      _ = A.card ^ 2 := by rw [Finset.card_product, pow_two]
  have hoff : (A.offDiag.card : ℝ) ≤ (A.card : ℝ) ^ 2 := by
    exact_mod_cast hoffnat
  have hbound := hdouble.trans (mul_le_mul_of_nonneg_right hoff hR)
  have hmain : (I.card : ℝ) * (A.card : ℝ) ^ 2 ≤
      (A.card : ℝ) ^ 2 * R * (2 * H) := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * H)).mp
    simpa only [mul_div_assoc] using hbound
  have hN : 0 < (A.card : ℝ) := by linarith
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hN)).mp
  calc
    (I.card : ℝ) * (A.card : ℝ) ^ 2 ≤ (A.card : ℝ) ^ 2 * R * (2 * H) := hmain
    _ = (2 * H * R) * (A.card : ℝ) ^ 2 := by ring

/-- For arbitrary moduli, each off-diagonal collision gives a divisor of
a positive difference. The predicate `Q` can restrict the divisors to rough
integers; the difference itself need not be rough. -/
theorem moduli_energy_card_le_of_divisor_count
    (I A : Finset ℕ) (P : ℕ) (X : ℝ) (Q : ℕ → Prop) [DecidablePred Q]
    {H R : ℝ} (hH : 0 < H) (hR : 0 ≤ R)
    (hA : ∀ a ∈ A, 1 ≤ a ∧ a ≤ P)
    (hI : ∀ q ∈ I, (q : ℝ) ≤ X ∧ Q q)
    (hsize : 2 * H ≤ (A.card : ℝ))
    (henergy : ∀ q ∈ I,
      (A.card : ℝ) ^ 2 ≤ H * ((collisionPairs A (fun a => a % q)).card : ℝ))
    (hdivisors : ∀ n : ℕ, 0 < n → n ≤ P →
      ((n.divisors.filter (fun d : ℕ => (d : ℝ) ≤ X ∧ Q d)).card : ℝ) ≤ R) :
    (I.card : ℝ) ≤ 2 * H * R := by
  apply large_collision_maps_card_le I A (fun q a => a % q) hH hR hsize henergy
  intro p hp
  obtain ⟨hpa, hpb, hne⟩ := Finset.mem_offDiag.mp hp
  have hd : 0 < Nat.dist p.1 p.2 := Nat.dist_pos_of_ne hne
  have hdP : Nat.dist p.1 p.2 ≤ P := by
    have ha := hA p.1 hpa
    have hb := hA p.2 hpb
    unfold Nat.dist
    omega
  have hsub : I.filter (fun q => p.1 % q = p.2 % q) ⊆
      (Nat.dist p.1 p.2).divisors.filter (fun d : ℕ => (d : ℝ) ≤ X ∧ Q d) := by
    intro q hq
    obtain ⟨hqI, hmod⟩ := Finset.mem_filter.mp hq
    refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨?_, hd.ne'⟩, hI q hqI⟩
    have hm : Nat.ModEq q p.1 p.2 := hmod
    rcases le_total p.1 p.2 with hab | hba
    · rw [Nat.dist_eq_sub_of_le hab]
      exact (Nat.modEq_iff_dvd' hab).mp hm
    · rw [Nat.dist_eq_sub_of_le_right hba]
      exact (Nat.modEq_iff_dvd' hba).mp hm.symm
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
    (hdivisors _ hd hdP)

/-- A common divisor list on a modulus block turns a power-size collision
exception into a sparse set of moduli. This is applicable to every modulus,
not only primes, and retains the genuine restricted-divisor-count input. -/
theorem moduli_rpow_energy_card_le
    (I A : Finset ℕ) (P : ℕ) (X θ : ℝ) (Q : ℕ → Prop) [DecidablePred Q]
    {R : ℝ} (hX : 0 < X) (hθ : 0 ≤ θ) (hR : 0 ≤ R)
    (hA : ∀ a ∈ A, 1 ≤ a ∧ a ≤ P)
    (hI : ∀ q ∈ I, (q : ℝ) ≤ X ∧ Q q)
    (hsize : 2 * X ^ θ ≤ (A.card : ℝ))
    (henergy : ∀ q ∈ I, (A.card : ℝ) ^ 2 ≤
      (q : ℝ) ^ θ * ((collisionPairs A (fun a => a % q)).card : ℝ))
    (hdivisors : ∀ n : ℕ, 0 < n → n ≤ P →
      ((n.divisors.filter (fun d : ℕ => (d : ℝ) ≤ X ∧ Q d)).card : ℝ) ≤ R) :
    (I.card : ℝ) ≤ 2 * X ^ θ * R := by
  apply moduli_energy_card_le_of_divisor_count I A P X Q
    (Real.rpow_pos_of_pos hX θ) hR hA hI hsize ?_ hdivisors
  intro q hq
  exact (henergy q hq).trans (mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow (Nat.cast_nonneg q) (hI q hq).1 hθ) (by positivity))

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_ThinSupplyBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open Filter

namespace Problem337

/-- The exact divisor cardinality already dominates the real power dictated by
its logarithmic prime-prefix coefficient. -/
lemma rpow_le_divisors_card_thinSupplyBase (a : ℝ) {u : ℕ} (hu : 0 < u) :
    (u : ℝ) ^ (a * Real.log 2) ≤ ((thinSupplyBase a u).divisors.card : ℝ) := by
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  rw [thinSupplyBase, card_divisors_primePrefixProduct, Nat.cast_pow, Nat.cast_ofNat]
  rw [Real.rpow_def_of_pos huR]
  have hceil : a * Real.log (u : ℝ) ≤ (supplyPrimeCount a u : ℝ) := Nat.le_ceil _
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hexp : Real.log (u : ℝ) * (a * Real.log 2) ≤
      (supplyPrimeCount a u : ℝ) * Real.log 2 := by nlinarith
  calc
    Real.exp (Real.log (u : ℝ) * (a * Real.log 2)) ≤
        Real.exp ((supplyPrimeCount a u : ℝ) * Real.log 2) := Real.exp_le_exp.mpr hexp
    _ = (2 : ℝ) ^ supplyPrimeCount a u := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]

/-- Sharp leading logarithmic size of the smaller prime-prefix base itself. -/
theorem eventually_log_thinSupplyBase_le (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∀ᶠ u : ℕ in atTop,
      Real.log (thinSupplyBase a u : ℝ) ≤
        (a + ε) * Real.log (u : ℝ) * Real.log (Real.log (u : ℝ)) := by
  exact (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_log_primePrefixProduct_ceil_le a ε ha hε)

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_RoughModulusBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open Filter

namespace Problem337

theorem roughModulusBadBlock_card_le (D : ℕ) (hD : 4 ≤ D)
    (R : ℝ) (hR : 0 ≤ R)
    (hdivisors : ∀ n : ℕ, 0 < n →
      n ≤ thinSupplyBase (2 / Real.log 2) D →
      ((n.divisors.filter (fun d : ℕ => (d : ℝ) ≤ 2 * (D : ℝ) ∧
        ∀ p ∈ d.primeFactorsList, Real.log (2 * (D : ℝ)) ≤ (p : ℝ))).card : ℝ) ≤ R) :
    ((roughModulusBadBlock D).card : ℝ) ≤
      2 * (2 * (D : ℝ)) ^ (7 / 8 : ℝ) * R := by
  classical
  let A := (thinSupplyBase (2 / Real.log 2) D).divisors
  have hDpos : 0 < D := by omega
  have hDR : (4 : ℝ) ≤ D := by exact_mod_cast hD
  have hcard := rpow_le_divisors_card_thinSupplyBase (2 / Real.log 2) hDpos
  have hcoef : (2 / Real.log 2) * Real.log 2 = (2 : ℝ) := by
    have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
    field_simp
  rw [hcoef, Real.rpow_two] at hcard
  have hpow : (2 * (D : ℝ)) ^ (7 / 8 : ℝ) ≤ 2 * (D : ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le
      (show (1 : ℝ) ≤ 2 * D by linarith) (show (7 / 8 : ℝ) ≤ 1 by norm_num)
  apply moduli_rpow_energy_card_le (roughModulusBadBlock D) A
    (thinSupplyBase (2 / Real.log 2) D) (2 * (D : ℝ)) (7 / 8)
    (fun q => ∀ p ∈ q.primeFactorsList, Real.log (2 * (D : ℝ)) ≤ (p : ℝ))
    (by positivity) (by norm_num) hR
  · intro a ha
    exact ⟨Nat.pos_of_mem_divisors ha, Nat.divisor_le ha⟩
  · intro q hq
    obtain ⟨hqrange, hrough, _⟩ := Finset.mem_filter.mp hq
    exact ⟨by exact_mod_cast (Finset.mem_Ico.mp hqrange).2.le, hrough⟩
  · change 2 * (2 * (D : ℝ)) ^ (7 / 8 : ℝ) ≤
      ((thinSupplyBase (2 / Real.log 2) D).divisors.card : ℝ)
    nlinarith
  · intro q hq
    exact (Finset.mem_filter.mp hq).2.2
  · exact hdivisors

/-- The small subpower divisor error still leaves a fixed power saving in
the bad-modulus count, including the dyadic-block factor of two. -/
lemma roughModulusBlock_power_budget {D : ℝ} (hD : 0 < D)
    (hlarge : 4 ≤ D ^ (1 / 32 : ℝ)) :
    2 * (2 * D) ^ (7 / 8 : ℝ) * (2 * D) ^ (1 / 32 : ℝ) ≤
      D ^ (15 / 16 : ℝ) := by
  have htwo : (2 : ℝ) ^ (29 / 32 : ℝ) ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (29 / 32 : ℝ) ≤ 1)
  calc
    2 * (2 * D) ^ (7 / 8 : ℝ) * (2 * D) ^ (1 / 32 : ℝ) =
        2 * (2 * D) ^ (29 / 32 : ℝ) := by
      rw [mul_assoc, ← Real.rpow_add (by positivity : 0 < 2 * D)]
      norm_num
    _ = 2 * ((2 : ℝ) ^ (29 / 32 : ℝ) * D ^ (29 / 32 : ℝ)) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hD.le]
    _ ≤ 4 * D ^ (29 / 32 : ℝ) := by
      nlinarith [Real.rpow_nonneg hD.le (29 / 32),
        mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hD.le (29 / 32))]
    _ ≤ D ^ (1 / 32 : ℝ) * D ^ (29 / 32 : ℝ) :=
      mul_le_mul_of_nonneg_right hlarge (Real.rpow_nonneg hD.le _)
    _ = D ^ (15 / 16 : ℝ) := by
      rw [← Real.rpow_add hD]
      norm_num

/-- The actual prime-prefix cardinality and size estimates discharge all
inputs to the block double count except the uniform restricted-divisor
estimate.  That estimate concerns arbitrary positive differences, not
rough ambient integers. -/
theorem eventually_roughModulusBadBlock_card_le_of_divisor_subpower
    (hrough : ∀ᶠ X : ℝ in atTop, ∀ n : ℕ, n ≠ 0 →
      Real.log (n : ℝ) ≤ (2 / Real.log 2 + 1) * Real.log X * Real.log (Real.log X) →
      ((n.divisors.filter (fun d : ℕ => (d : ℝ) ≤ X ∧
        ∀ p ∈ d.primeFactorsList, Real.log X ≤ (p : ℝ))).card : ℝ) ≤
        X ^ (1 / 32 : ℝ)) :
    ∀ᶠ D : ℕ in atTop,
      ((roughModulusBadBlock D).card : ℝ) ≤ (D : ℝ) ^ (15 / 16 : ℝ) := by
  have ha : 0 < (2 : ℝ) / Real.log 2 := by positivity
  have hA : 0 < (2 : ℝ) / Real.log 2 + 1 := by positivity
  have htX : Tendsto (fun D : ℕ => 2 * (D : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have htpow : Tendsto (fun D : ℕ => (D : ℝ) ^ (1 / 32 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 32)).comp tendsto_natCast_atTop_atTop
  have htlog : Tendsto (fun D : ℕ => Real.log (D : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [htX.eventually hrough,
    eventually_log_thinSupplyBase_le (2 / Real.log 2) 1 ha zero_lt_one,
    htpow.eventually_ge_atTop 4, htlog.eventually_ge_atTop 1,
    eventually_ge_atTop (4 : ℕ)] with D hroughD hbase hlarge hlogD hD
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hlogDX : Real.log (D : ℝ) ≤ Real.log (2 * (D : ℝ)) :=
    Real.log_le_log hDpos (by linarith)
  have hloglogDX : Real.log (Real.log (D : ℝ)) ≤
      Real.log (Real.log (2 * (D : ℝ))) :=
    Real.log_le_log (by linarith) hlogDX
  have hloglogD : 0 ≤ Real.log (Real.log (D : ℝ)) := Real.log_nonneg hlogD
  have hwindow : Real.log (thinSupplyBase (2 / Real.log 2) D : ℝ) ≤
      (2 / Real.log 2 + 1) * Real.log (2 * (D : ℝ)) *
        Real.log (Real.log (2 * (D : ℝ))) := by
    refine hbase.trans ?_
    gcongr
    exact mul_nonneg hA.le (by linarith)
  have hcount := roughModulusBadBlock_card_le D hD
    ((2 * (D : ℝ)) ^ (1 / 32 : ℝ)) (by positivity) (by
      intro n hn hnP
      apply hroughD n hn.ne'
      exact (Real.log_le_log (by exact_mod_cast hn) (by exact_mod_cast hnP)).trans hwindow)
  exact hcount.trans (roughModulusBlock_power_budget hDpos hlarge)

/-- An unconditional power-saving bound for the actual bad-modulus blocks.
The common divisor list is the explicit logarithmic prime prefix, and the
restricted-divisor estimate has been discharged for every positive difference. -/
theorem eventually_roughModulusBadBlock_card_le :
    ∀ᶠ D : ℕ in atTop,
      ((roughModulusBadBlock D).card : ℝ) ≤ (D : ℝ) ^ (15 / 16 : ℝ) := by
  apply eventually_roughModulusBadBlock_card_le_of_divisor_subpower
  filter_upwards [eventually_card_rough_divisors_subpower
    (2 / Real.log 2 + 1) (1 / 32) (by positivity) (by norm_num)] with X hX
  intro n hn hsize
  exact hX n hn hsize (Real.log X) le_rfl

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_CompositeBadDensityBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open Filter

namespace Problem337.CompositeSupply

lemma base_eq_thinSupplyBase (u : ℕ) :
    base u = thinSupplyBase (2 / Real.log 2) u := by
  unfold base thinSupplyBase
  rw [primeCount_eq_supplyPrimeCount]

attribute [local instance] OAI.Problem337.CompositeSupply.instDecidablePredNatBadModulus_1
/-- The variable-pool global exception set embeds into the actual fixed-pool
exception block. Both roughness and the energy threshold follow from its
definition and the proved unit-mixing contraction. -/
theorem badModuli_block_subset (D : ℕ) (hD : 2 ≤ D) :
    (Finset.Ico D (2 * D)).filter BadModulus ⊆ roughModulusBadBlock D := by
  classical
  intro d hd
  obtain ⟨hdI, hbad⟩ := Finset.mem_filter.mp hd
  have hdD : D ≤ d := (Finset.mem_Ico.mp hdI).1
  let : NeZero d := ⟨by omega⟩
  change d ∈ (Finset.Ico D (2 * D)).filter _
  refine Finset.mem_filter.mpr ⟨hdI, ?_, ?_⟩
  · intro p hp
    exact badModulus_prime_lower hD hdD hbad
      (Nat.prime_of_mem_primeFactorsList hp) (Nat.dvd_of_mem_primeFactorsList hp)
  · simpa only [← base_eq_thinSupplyBase] using
      badModulus_fixed_base_collisions (by omega : 0 < D) hdD hbad

/-- An unconditional sparse dyadic count for one global predicate. No
unproved rough-divisor, collision, or distribution hypothesis remains. -/
theorem eventually_badModulus_shell_card_le :
    ∀ᶠ j : ℕ in atTop,
      (((Finset.Ico (2 ^ j) (2 ^ (j + 1))).filter BadModulus).card : ℝ) ≤
        ((2 : ℝ) ^ j) ^ (15 / 16 : ℝ) := by
  classical
  obtain ⟨D₀, hD₀⟩ := eventually_atTop.mp eventually_roughModulusBadBlock_card_le
  filter_upwards [eventually_ge_atTop (max D₀ 2)] with j hj
  have hjpow : j ≤ 2 ^ j := Nat.le_of_lt (Nat.lt_two_pow_self (n := j))
  have hpowD : D₀ ≤ 2 ^ j := ((le_max_left D₀ 2).trans hj).trans hjpow
  have hpow2 : 2 ≤ 2 ^ j := ((le_max_right D₀ 2).trans hj).trans hjpow
  have hsub := badModuli_block_subset (2 ^ j) hpow2
  have hcard : (((Finset.Ico (2 ^ j) (2 ^ (j + 1))).filter BadModulus).card : ℝ) ≤
      ((roughModulusBadBlock (2 ^ j)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (by simpa [pow_succ, Nat.mul_comm] using hsub)
  exact hcard.trans (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hD₀ _ hpowD)

/-- The exceptional original integers have arbitrarily small density.
This is the unconditional arithmetic input for the cube-free supply assembly. -/
theorem eventually_badMultiples_card_le :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ Y : ℕ in atTop,
      ((badMultiples Y).card : ℝ) ≤ ε * Y := by
  apply eventually_badMultiples_card_le_of_shell_bound
    (C := 1) (β := 15 / 16) (by norm_num) (by norm_num)
  simpa only [one_mul] using eventually_badModulus_shell_card_le

end Problem337.CompositeSupply

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_FiveProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337.FiveProducts

theorem character_map_sum {p : ℕ} [NeZero p] {ι : Type*}
    (s : Finset ι) (g : ι → ZMod p) :
    ZMod.stdAddChar (∑ i ∈ s, g i) = ∏ i ∈ s, ZMod.stdAddChar (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, AddChar.map_add_eq_mul, ih]

/-- Orthogonality for the standard character on a finite cyclic group. -/
theorem character_sum {p : ℕ} [NeZero p] (t : ZMod p) :
    (∑ r : ZMod p, ZMod.stdAddChar (t * r)) =
      if t = 0 then (p : ℂ) else 0 := by
  split_ifs with ht
  · simp [ht]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar p ht)

end Problem337.FiveProducts

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_CompositeSpectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.CompositeSpectral

/-- Exact Fourier inversion for an arbitrary tuple length and target. The
modulus need not be prime, and the sample type can retain multiplicities. -/
theorem sumTuples_fourier {q : ℕ} [NeZero q] {X : Type*} [Fintype X]
    (f : X → ZMod q) (k : ℕ) (t : ZMod q) :
    (∑ r : ZMod q, ZMod.stdAddChar (-t * r) *
      (∑ x : X, ZMod.stdAddChar (f x * r)) ^ k) =
      (q : ℂ) * (sumTuples f k t).card := by
  classical
  simp_rw [Fintype.sum_pow, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hterm (v : Fin k → X) (r : ZMod q) :
      ZMod.stdAddChar (-t * r) *
        (∏ i : Fin k, ZMod.stdAddChar (f (v i) * r)) =
        ZMod.stdAddChar (((∑ i : Fin k, f (v i)) - t) * r) := by
    rw [← FiveProducts.character_map_sum, ← AddChar.map_add_eq_mul]
    congr 1
    rw [← Finset.sum_mul]
    ring
  simp_rw [hterm, FiveProducts.character_sum, sub_eq_zero]
  rw [← Finset.sum_filter]
  simp [sumTuples, mul_comm]

/-- The nontrivial Fourier frequencies control the discrepancy from the
uniform tuple count. Keeping the sum, rather than using a worst frequency,
allows different proper quotients of a composite modulus to be estimated
separately. -/
theorem sumTuples_discrepancy_le {q : ℕ} [NeZero q]
    {X : Type*} [Fintype X] (f : X → ZMod q) (k : ℕ) (t : ZMod q) :
    |(q : ℝ) * (sumTuples f k t).card - (Fintype.card X : ℝ) ^ k| ≤
      ∑ r ∈ (Finset.univ : Finset (ZMod q)).erase 0,
        ‖∑ x : X, ZMod.stdAddChar (f x * r)‖ ^ k := by
  classical
  let S : ZMod q → ℂ := fun r => ZMod.stdAddChar (-t * r) *
    (∑ x : X, ZMod.stdAddChar (f x * r)) ^ k
  have hzero : S 0 = (Fintype.card X : ℂ) ^ k := by simp [S]
  have hsplit := Finset.sum_erase_add (s := (Finset.univ : Finset (ZMod q)))
    S (Finset.mem_univ 0)
  have htotal : ∑ r, S r = (q : ℂ) * (sumTuples f k t).card :=
    sumTuples_fourier f k t
  rw [hzero, htotal] at hsplit
  have hdiff : (q : ℂ) * (sumTuples f k t).card - (Fintype.card X : ℂ) ^ k =
      ∑ r ∈ (Finset.univ : Finset (ZMod q)).erase 0, S r := by
    linear_combination -hsplit
  have hnorm := norm_sum_le ((Finset.univ : Finset (ZMod q)).erase 0) S
  rw [← hdiff] at hnorm
  have hterm (r : ZMod q) : ‖S r‖ =
      ‖∑ x : X, ZMod.stdAddChar (f x * r)‖ ^ k := by
    dsimp [S]
    have hc : ‖ZMod.stdAddChar (-t * r)‖ = 1 := Circle.norm_coe _
    rw [norm_mul, hc, one_mul, norm_pow]
  simp_rw [hterm] at hnorm
  exact_mod_cast hnorm

/-- A frequency-by-frequency bound gives a quantitative lower bound for
the number of tuples having any prescribed sum. -/
theorem sumTuples_lower_bound {q : ℕ} [NeZero q]
    {X : Type*} [Fintype X] (f : X → ZMod q) (k : ℕ) (t : ZMod q)
    (B : ZMod q → ℝ)
    (hB : ∀ r : ZMod q, r ≠ 0 →
      ‖∑ x : X, ZMod.stdAddChar (f x * r)‖ ≤ B r) :
    (Fintype.card X : ℝ) ^ k -
      (∑ r ∈ (Finset.univ : Finset (ZMod q)).erase 0, B r ^ k) ≤
        (q : ℝ) * (sumTuples f k t).card := by
  classical
  have hdisc := sumTuples_discrepancy_le f k t
  have hsum : (∑ r ∈ (Finset.univ : Finset (ZMod q)).erase 0,
      ‖∑ x : X, ZMod.stdAddChar (f x * r)‖ ^ k) ≤
      ∑ r ∈ (Finset.univ : Finset (ZMod q)).erase 0, B r ^ k := by
    apply Finset.sum_le_sum
    intro r hr
    exact pow_le_pow_left₀ (norm_nonneg _)
      (hB r (Finset.mem_erase.mp hr).1) k
  linarith [(abs_le.mp hdisc).1]

/-- Summed spectral losses below the zero frequency force a tuple of the
specified sum, without any prime-modulus hypothesis. -/
theorem exists_sum_of_character_bounds {q : ℕ} [NeZero q]
    {X : Type*} [Fintype X] (f : X → ZMod q) (k : ℕ) (t : ZMod q)
    (B : ZMod q → ℝ)
    (hB : ∀ r : ZMod q, r ≠ 0 →
      ‖∑ x : X, ZMod.stdAddChar (f x * r)‖ ≤ B r)
    (hbudget : (∑ r ∈ (Finset.univ : Finset (ZMod q)).erase 0, B r ^ k) <
      (Fintype.card X : ℝ) ^ k) :
    ∃ v : Fin k → X, ∑ i, f (v i) = t := by
  classical
  have hcount := sumTuples_lower_bound f k t B hB
  have hpos : 0 < (sumTuples f k t).card := by
    by_contra hn
    have hz : (sumTuples f k t).card = 0 := Nat.eq_zero_of_not_pos hn
    rw [hz, Nat.cast_zero, mul_zero] at hcount
    linarith
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
  exact ⟨v, (Finset.mem_filter.mp hv).2⟩

end Problem337.CompositeSpectral

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_CompositeConductorBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.CompositeSpectral

/-- A finite reciprocal-square tail with a uniform strict margin below one. -/
theorem reciprocal_square_Icc_bound (N : ℕ) (hN : 2 ≤ N) :
    (∑ d ∈ Finset.Icc 2 N, (1 : ℝ) / (d : ℝ) ^ 2) ≤
      3 / 4 - 1 / (N : ℝ) := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ N hN ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hid : (1 : ℝ) / ((N : ℝ) * (N + 1)) = 1 / N - 1 / (N + 1) := by
      field_simp
      ring
    have hterm : (1 : ℝ) / ((N : ℝ) + 1) ^ 2 ≤
        1 / (N : ℝ) - 1 / ((N : ℝ) + 1) := by
      rw [← hid]
      exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
    push_cast
    linarith

/-- At most `d` residues have additive order `d`, including orders which do
not divide the modulus. For divisors, the exact count is Euler's totient. -/
theorem order_fiber_card_le (q d : ℕ) [NeZero q] :
    ((Finset.univ : Finset (ZMod q)).filter (fun r => addOrderOf r = d)).card ≤ d := by
  classical
  by_cases hd : d ∣ q
  · have hcount := IsAddCyclic.card_addOrderOf_eq_totient (α := ZMod q)
      (show d ∣ Fintype.card (ZMod q) by simpa using hd)
    rw [hcount]
    exact Nat.totient_le d
  · have hempty : ((Finset.univ : Finset (ZMod q)).filter
        (fun r => addOrderOf r = d)) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro r hr
      have heq := (Finset.mem_filter.mp hr).2
      apply hd
      have horder := addOrderOf_dvd_card (x := r)
      simpa only [heq, ZMod.card] using horder
    simp [hempty]

/-- The total cubic reciprocal-conductor mass is uniformly at most `3/4`.
This controls the sixth moment when the normalized character bound at
conductor `d` is `1 / sqrt d`. -/
theorem conductor_cube_sum_le (q : ℕ) [NeZero q] :
    (∑ r ∈ (Finset.univ : Finset (ZMod q)).erase 0,
      (1 : ℝ) / (addOrderOf r : ℝ) ^ 3) ≤ 3 / 4 := by
  classical
  have hmap : ∀ r ∈ (Finset.univ : Finset (ZMod q)).erase 0,
      addOrderOf r ∈ Finset.Icc 2 q := by
    intro r hr
    have hr0 := (Finset.mem_erase.mp hr).1
    have hp := addOrderOf_pos r
    have hne : addOrderOf r ≠ 1 := by
      intro h
      exact hr0 (AddMonoid.addOrderOf_eq_one_iff.mp h)
    have hd : addOrderOf r ∣ q := by simpa using addOrderOf_dvd_card (x := r)
    exact Finset.mem_Icc.mpr ⟨by omega, Nat.le_of_dvd (NeZero.pos q) hd⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmap
    (fun r : ZMod q => (1 : ℝ) / (addOrderOf r : ℝ) ^ 3)]
  have hsum :
      (∑ d ∈ Finset.Icc 2 q,
        ∑ r ∈ (Finset.univ.erase 0).filter (fun r : ZMod q => addOrderOf r = d),
          (1 : ℝ) / (addOrderOf r : ℝ) ^ 3) ≤
      ∑ d ∈ Finset.Icc 2 q, (1 : ℝ) / (d : ℝ) ^ 2 := by
    apply Finset.sum_le_sum
    intro d hd
    have hdpos : (0 : ℝ) < d := by
      exact_mod_cast (show 0 < d by have := (Finset.mem_Icc.mp hd).1; omega)
    have hcard : ((Finset.univ.erase 0).filter
        (fun r : ZMod q => addOrderOf r = d)).card ≤ d :=
      (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.erase_subset _ _))).trans
        (order_fiber_card_le q d)
    calc
      _ = (((Finset.univ.erase 0).filter
          (fun r : ZMod q => addOrderOf r = d)).card : ℝ) * (1 / (d : ℝ) ^ 3) := by
        calc
          _ = ∑ r ∈ (Finset.univ.erase 0).filter
              (fun r : ZMod q => addOrderOf r = d), (1 : ℝ) / (d : ℝ) ^ 3 := by
            apply Finset.sum_congr rfl
            intro r hr
            rw [(Finset.mem_filter.mp hr).2]
          _ = _ := by simp
      _ ≤ (d : ℝ) * (1 / (d : ℝ) ^ 3) := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
      _ = 1 / (d : ℝ) ^ 2 := by field_simp
  apply hsum.trans
  by_cases hq : 2 ≤ q
  · exact (reciprocal_square_Icc_bound q hq).trans (sub_le_self _ (by positivity))
  · have he : Finset.Icc 2 q = ∅ := Finset.Icc_eq_empty_of_lt (by omega)
    norm_num [he]

/-- Additive order is exactly the conductor obtained by cancelling the
frequency against the modulus. -/
theorem order_eq_reduced_modulus {q : ℕ} [NeZero q] (r : ZMod q) :
    addOrderOf r = q / r.val.gcd q := by
  simpa only [ZMod.natCast_zmod_val, Nat.gcd_comm] using
    ZMod.addOrderOf_coe r.val (NeZero.ne q)

end Problem337.CompositeSpectral

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_MarkedGreedy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace Problem337

/-- The integer ceiling of `q/R`, presented without rational rounding. -/
theorem marked_ceiling_spec (R q : ℕ) (hR : 0 < R) (hRq : R < q) :
    ∃ a : ℕ, 2 ≤ a ∧ a ≤ q ∧ (a - 1) * R < q ∧ q ≤ a * R := by
  let a := (q - 1) / R + 1
  have hq : 0 < q := by omega
  have hlow : ((q - 1) / R) * R ≤ q - 1 := Nat.div_mul_le_self _ _
  have hhigh : q - 1 < ((q - 1) / R + 1) * R := by
    have hr := Nat.mod_lt (q - 1) hR
    have he := Nat.mod_add_div (q - 1) R
    nlinarith
  have ha2 : 2 ≤ a := by
    have hdiv : 1 ≤ (q - 1) / R := (Nat.one_le_div_iff hR).2 (by omega)
    dsimp [a]
    omega
  refine ⟨a, ha2, ?_, ?_, ?_⟩
  · have hmul : (a - 1) ≤ (a - 1) * R := by nlinarith
    have : (a - 1) * R ≤ q - 1 := by simpa [a] using hlow
    omega
  · simpa [a] using (lt_of_le_of_lt hlow (by omega : q - 1 < q))
  · dsimp [a]
    omega

/-- One marked greedy step avoids the prescribed denominator, with an unreduced numerator. -/
theorem marked_greedy_step_data (m R q : ℕ)
    (hm : 4 ≤ m) (hR : 0 < R) (hRq : R < q) :
    ∃ n c : ℕ, 2 ≤ n ∧ n ≠ m ∧ n ≤ q + 1 ∧
      q ≤ n * R ∧ n * R = q + c ∧ c < q ∧ c < 2 * R ∧
      (n ≠ m + 1 → c < R) ∧
      (R : ℚ) / q = 1 / (n : ℚ) + (c : ℚ) / (n * q : ℕ) ∧
      (c : ℚ) / (n * q : ℕ) < 1 / (n : ℚ) := by
  obtain ⟨a, ha2, haq, halow, hahigh⟩ := marked_ceiling_spec R q hR hRq
  let n := if a = m then m + 1 else a
  have hn2 : 2 ≤ n := by dsimp [n]; split <;> omega
  have hnm : n ≠ m := by dsimp [n]; split <;> omega
  have hnq : n ≤ q + 1 := by dsimp [n]; split <;> omega
  have han : a ≤ n := by dsimp [n]; split <;> omega
  have hhigh : q ≤ n * R := le_trans hahigh (Nat.mul_le_mul_right R han)
  let c := n * R - q
  have heq : n * R = q + c := by dsimp [c]; omega
  have hc2 : c < 2 * R := by
    by_cases ham : a = m
    · have hn : n = m + 1 := by simp [n, ham]
      have hlow : (m - 1) * R < q := by simpa [ham] using halow
      have hm1 : m - 1 + 1 = m := by omega
      rw [hn] at heq
      nlinarith
    · have hn : n = a := by simp [n, ham]
      rw [hn] at heq
      have ha1 : a - 1 + 1 = a := by omega
      nlinarith
  have hcord : n ≠ m + 1 → c < R := by
    intro hne
    have ham : a ≠ m := by intro he; simp [n, he] at hne
    have hn : n = a := by simp [n, ham]
    rw [hn] at heq
    have ha1 : a - 1 + 1 = a := by omega
    nlinarith
  have hcq : c < q := by
    by_cases ham : a = m
    · have hlow : (m - 1) * R < q := by simpa [ham] using halow
      have hm1 : 3 ≤ m - 1 := by omega
      nlinarith
    · have hn : n = a := by simp [n, ham]
      rw [hn] at heq
      have ha1 : a - 1 + 1 = a := by omega
      have : c < R := by nlinarith
      omega
  have hnQ : (0 : ℚ) < n := by exact_mod_cast (by omega : 0 < n)
  have hqQ : (0 : ℚ) < q := by exact_mod_cast (by omega : 0 < q)
  have heqQ : (n : ℚ) * R = q + c := by exact_mod_cast heq
  refine ⟨n, c, hn2, hnm, hnq, hhigh, heq, hcq, hc2, hcord, ?_, ?_⟩
  · push_cast
    field_simp
    nlinarith
  · push_cast
    apply (div_lt_div_iff₀ (mul_pos hnQ hqQ) hnQ).2
    have hcqQ : (c : ℚ) < q := by exact_mod_cast hcq
    nlinarith

/-- The ordinary steps square the size of the remainder. -/
theorem marked_greedy_square (R q n c : ℕ) (hR : 0 < R) (hq : 0 < q)
    (hn : 0 < n) (heq : n * R = q + c) (hc : c < R) :
    (c : ℚ) / (n * q : ℕ) < ((R : ℚ) / q) ^ 2 := by
  have hR' : (0 : ℚ) < R := by exact_mod_cast hR
  have hq' : (0 : ℚ) < q := by exact_mod_cast hq
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  have heq' : (n : ℚ) * R = q + c := by exact_mod_cast heq
  have hc' : (c : ℚ) < R := by exact_mod_cast hc
  have hc0 : (0 : ℚ) ≤ c := by positivity
  have hprod : (c : ℚ) * q < (n : ℚ) * R ^ 2 := by
    calc
      (c : ℚ) * q < R * q := mul_lt_mul_of_pos_right hc' hq'
      _ ≤ (n : ℚ) * R ^ 2 := by nlinarith
  push_cast
  apply (div_lt_iff₀ (mul_pos hn' hq')).2
  field_simp
  nlinarith


/-- Every chosen denominator is above the preceding threshold; the numerator remains small. -/
theorem MarkedGreedySteps.invariants {m R q Rf qf : ℕ} {L : List ℕ}
    (h : MarkedGreedySteps m R q L Rf qf) (t : ℕ)
    (ht : 1 ≤ t) (hq : 0 < q) (hgap : t * R < q)
    (hsmall : R < 2 * m) (hphase : R < m ∨ m < t) :
    qf > 0 ∧ t * Rf < qf ∧ Rf < 2 * m ∧
      (∀ n ∈ L, t < n ∧ n ≠ m) ∧ L.Pairwise (· < ·) ∧
      (∀ n ∈ L, n * Rf < qf) := by
  induction h generalizing t with
  | nil R q => exact ⟨hq, hgap, hsmall, by simp, by simp, by simp⟩
  | cons R q n c L Rf qf hn hnm hnq heq hcq hcR hord tail ih =>
    have htn : t < n := by
      by_contra h
      have hnt : n ≤ t := by omega
      have := Nat.mul_le_mul_right R hnt
      omega
    have hcsmall : c < 2 * m := by
      by_cases hne : n ≠ m + 1
      · exact lt_trans (hord hne) hsmall
      · have hnm1 : n = m + 1 := by omega
        have hRm : R < m := by rcases hphase with h | h <;> omega
        omega
    have hcphase : c < m ∨ m < n := by
      by_cases hmn : m < n
      · exact Or.inr hmn
      · have hne : n ≠ m + 1 := by omega
        have hRm : R < m := by rcases hphase with h | h <;> omega
        exact Or.inl (lt_trans (hord hne) hRm)
    have hnextq : 0 < n * q := by positivity
    have hnextgap : n * c < n * q := Nat.mul_lt_mul_of_pos_left hcq (by omega)
    obtain ⟨hqf, hgapf, hsmallf, hlist, hpair, hfinal⟩ :=
      ih n (by omega) hnextq hnextgap hcsmall hcphase
    refine ⟨hqf, ?_, hsmallf, ?_, ?_, ?_⟩
    · exact lt_of_le_of_lt (Nat.mul_le_mul_right Rf (by omega : t ≤ n)) hgapf
    · intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact ⟨htn, hnm⟩
      · exact ⟨lt_trans htn (hlist a ha).1, (hlist a ha).2⟩
    · exact List.pairwise_cons.mpr ⟨fun a ha => (hlist a ha).1, hpair⟩
    · intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hgapf
      · exact hfinal a ha

/-- The unreduced denominator is exactly the initial one times the chosen denominators. -/
theorem MarkedGreedySteps.denominator {m R q Rf qf : ℕ} {L : List ℕ}
    (h : MarkedGreedySteps m R q L Rf qf) : qf = q * L.prod := by
  induction h with
  | nil => simp
  | cons R q n c L Rf qf hn hnm hnq heq hcq hcR hord tail ih =>
    simpa [List.prod_cons, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using ih

/-- Telescoping the successive unreduced fraction identities. -/
theorem MarkedGreedySteps.sum {m R q Rf qf : ℕ} {L : List ℕ}
    (h : MarkedGreedySteps m R q L Rf qf) (hq : 0 < q) :
    (R : ℚ) / q = (L.map (fun n : ℕ => (1 : ℚ) / (n : ℚ))).sum + (Rf : ℚ) / qf := by
  induction h with
  | nil R q => simp
  | cons R q n c L Rf qf hn hnm hnq heq hcq hcR hord tail ih =>
    have hnQ : (0 : ℚ) < n := by exact_mod_cast (by omega : 0 < n)
    have hqQ : (0 : ℚ) < q := by exact_mod_cast hq
    have heqQ : (n : ℚ) * R = q + c := by exact_mod_cast heq
    have hstep : (R : ℚ) / q = 1 / (n : ℚ) + (c : ℚ) / (n * q : ℕ) := by
      push_cast
      field_simp
      nlinarith
    have htail := ih (by positivity : 0 < n * q)
    rw [hstep, htail]
    simp only [List.map_cons, List.sum_cons]
    ring

/-- Stopping also records that the denominator before the last step is below the threshold. -/
theorem exists_marked_greedy_steps_bounded (m T R q : ℕ) (hm : 4 ≤ m)
    (hq : 0 < q) (hRq : R < q) (hbound : q < T ^ 2) :
    ∃ L : List ℕ, ∃ Rf qf : ℕ, MarkedGreedySteps m R q L Rf qf ∧
      (Rf = 0 ∨ T ≤ qf) ∧ qf < T ^ 2 ∧
      (L ≠ [] → q * L.dropLast.prod < T) := by
  by_cases hstop : R = 0 ∨ T ≤ q
  · exact ⟨[], R, q, .nil R q, hstop, hbound, by simp⟩
  · have hR : 0 < R := by omega
    have hqT : q < T := by omega
    obtain ⟨n, c, hn, hnm, hnq, hhigh, heq, hcq, hcR, hord, hfrac, hrem⟩ :=
      marked_greedy_step_data m R q hm hR hRq
    have hqq : q < n * q := by nlinarith
    have hnext : n * q < T ^ 2 := by nlinarith
    obtain ⟨L, Rf, qf, htrace, hstop', hbound', hactive⟩ :=
      exists_marked_greedy_steps_bounded m T c (n * q) hm
        (Nat.mul_pos (by omega) hq) (by omega) hnext
    refine ⟨n :: L, Rf, qf, .cons R q n c L Rf qf hn hnm hnq heq hcq hcR hord htrace,
      hstop', hbound', ?_⟩
    intro _
    cases L with
    | nil => simpa using hqT
    | cons a L =>
      have ha := hactive (by simp)
      simpa [List.dropLast_cons_cons, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using ha
termination_by T - q


/-- Every nonempty marked trace starts by removing one half. -/
theorem MarkedGreedySteps.first {m n Rf qf : ℕ} {L : List ℕ}
    (h : MarkedGreedySteps m (m - 1) m (n :: L) Rf qf) (hm : 4 ≤ m) :
    n = 2 ∧ MarkedGreedySteps m (m - 2) (2 * m) L Rf qf := by
  cases h with
  | cons R q n c L Rf qf hn hnm hnq heq hcq hcR hord tail =>
    have hm1 : m - 1 + 1 = m := by omega
    have hne : n ≠ m + 1 := by
      intro he
      rw [he] at heq
      nlinarith
    have hc : c < m - 1 := hord hne
    have hn2 : n = 2 := by nlinarith
    have hm2 : m - 2 + 2 = m := by omega
    have hc2 : c = m - 2 := by nlinarith
    refine ⟨hn2, ?_⟩
    simpa [hn2, hc2] using tail


/-- A trace can be cut at any chosen prefix. -/
theorem MarkedGreedySteps.split {m R q Rf qf : ℕ} {A B : List ℕ}
    (h : MarkedGreedySteps m R q (A ++ B) Rf qf) :
    ∃ Ri qi : ℕ, MarkedGreedySteps m R q A Ri qi ∧
      MarkedGreedySteps m Ri qi B Rf qf := by
  induction A generalizing R q with
  | nil => exact ⟨R, q, .nil R q, h⟩
  | cons a A ih =>
    cases h with
    | cons R q n c L Rf qf hn hnm hnq heq hcq hcR hord tail =>
      obtain ⟨Ri, qi, hleft, hright⟩ := ih tail
      exact ⟨Ri, qi, .cons R q a c A Ri qi hn hnm hnq heq hcq hcR hord hleft, hright⟩

/-- The state before the final step has a positive numerator. -/
theorem MarkedGreedySteps.penultimate {m R q Rf qf : ℕ} {L : List ℕ}
    (h : MarkedGreedySteps m R q L Rf qf) (hL : L ≠ []) :
    ∃ Ri qi : ℕ, MarkedGreedySteps m R q L.dropLast Ri qi ∧
      0 < Ri ∧ 0 < qi ∧ qi = q * L.dropLast.prod := by
  have hsplit : MarkedGreedySteps m R q (L.dropLast ++ [L.getLast hL]) Rf qf := by
    simpa only [List.dropLast_append_getLast hL] using h
  obtain ⟨Ri, qi, hleft, hright⟩ := hsplit.split
  refine ⟨Ri, qi, hleft, ?_, ?_, hleft.denominator⟩
  · cases hright with
    | cons R q n c L Rf qf hn hnm hnq heq hcq hcR hord tail => omega
  · cases hright with
    | cons R q n c L Rf qf hn hnm hnq heq hcq hcR hord tail => omega

/-- The full arithmetic prefix contract also recording the final active state. -/
theorem exists_marked_greedy_prefix_bounded (m T : ℕ) (hm : 4 ≤ m) (hT : 2 * m ^ 2 ≤ T) :
    ∃ L : List ℕ, ∃ R q : ℕ,
      MarkedGreedySteps m (m - 1) m L R q ∧
      L.Pairwise (· < ·) ∧ (∀ n ∈ L, 2 ≤ n ∧ n ≠ m) ∧
      q = m * L.prod ∧ 0 < q ∧ R < 2 * m ∧
      (1 : ℚ) = 1 / (m : ℚ) + (L.map (fun n : ℕ => (1 : ℚ) / (n : ℚ))).sum + (R : ℚ) / q ∧
      q < T ^ 2 ∧ (R = 0 ∨ T ≤ q) ∧
      m * R < q ∧ (∀ n ∈ L, n * R < q) ∧
      (L ≠ [] → m * L.dropLast.prod < T) := by
  have hm0 : 0 < m := by omega
  have hmT0 : m < T := by nlinarith
  have hTT : T ≤ T ^ 2 := by nlinarith
  have hmT : m < T ^ 2 := lt_of_lt_of_le hmT0 hTT
  obtain ⟨L, R, q, htrace, hstop, hbound, hactive⟩ :=
    exists_marked_greedy_steps_bounded m T (m - 1) m hm hm0 (by omega) hmT
  obtain ⟨hq, hgap, hsmall, hlist, hpair, hfinal⟩ :=
    htrace.invariants 1 (by omega) hm0 (by omega) (by omega) (Or.inl (by omega))
  have hsum := htrace.sum hm0
  have hmarker : m * R < q := by
    rcases hstop with hzero | hlarge
    · simp [hzero, hq]
    · nlinarith
  refine ⟨L, R, q, htrace, hpair, ?_, htrace.denominator, hq, hsmall, ?_,
    hbound, hstop, hmarker, hfinal, hactive⟩
  · intro n hn
    exact ⟨by have := (hlist n hn).1; omega, (hlist n hn).2⟩
  · have hmQ : (0 : ℚ) < m := by exact_mod_cast hm0
    have hm1 : ((m - 1 : ℕ) : ℚ) = (m : ℚ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ m)]
      norm_num
    have htotal : (1 : ℚ) = 1 / (m : ℚ) + ((m - 1 : ℕ) : ℚ) / m := by
      rw [hm1]
      field_simp
      ring
    rw [hsum] at htotal
    linarith

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_DivisorDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

namespace Problem337

theorem divisorDense_base {m : ℕ} (hm : 2 ≤ m) : DivisorDense m m := by
  intro w hw hwm
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  refine ⟨1, by omega, one_dvd m, ?_, ?_⟩
  · simpa using (div_le_iff₀ hmpos).2 (by simpa using hwm)
  · simpa using hw

theorem DivisorDense.mul {m q n : ℕ} (hq : DivisorDense m q)
    (hm : 2 ≤ m) (hqpos : 1 ≤ q) (hnpos : 1 ≤ n) (hn : n ≤ q + 1) :
    DivisorDense m (n * q) := by
  intro w hw hwnq
  have hmposR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hnposR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hqposR : (1 : ℝ) ≤ q := by exact_mod_cast hqpos
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hnR : (n : ℝ) ≤ q + 1 := by exact_mod_cast hn
  simp only [Nat.cast_mul] at hwnq
  by_cases hwq : w ≤ (q : ℝ)
  · obtain ⟨d, hdpos, hdq, hdl, hdu⟩ := hq w hw hwq
    exact ⟨d, hdpos, dvd_mul_of_dvd_right hdq n, hdl, hdu⟩
  · by_cases hnw : (n : ℝ) ≤ w
    · have hwdiv : 1 ≤ w / (n : ℝ) := by
        exact (le_div_iff₀ hnposR).2 (by simpa using hnw)
      have hwdivq : w / (n : ℝ) ≤ q := by
        apply (div_le_iff₀ hnposR).2
        nlinarith [hwnq]
      obtain ⟨d, hdpos, hdq, hdl, hdu⟩ := hq (w / n) hwdiv hwdivq
      refine ⟨n * d, Nat.mul_pos (by omega) hdpos, Nat.mul_dvd_mul_left n hdq, ?_, ?_⟩
      · have hdl' : w / (n : ℝ) ≤ (d : ℝ) * m := (div_le_iff₀ hmposR).1 hdl
        have hdl'' : w ≤ (d : ℝ) * m * n := (div_le_iff₀ hnposR).1 hdl'
        apply (div_le_iff₀ hmposR).2
        simp only [Nat.cast_mul]
        nlinarith [hdl'']
      · have hdu' : (d : ℝ) * n ≤ w := (le_div_iff₀ hnposR).1 hdu
        simpa only [Nat.cast_mul, mul_comm] using hdu'
    · refine ⟨q, by omega, dvd_mul_left q n, ?_, by linarith⟩
      apply (div_le_iff₀ hmposR).2
      nlinarith

theorem GreedyDenominator.positive {m q : ℕ} (h : GreedyDenominator m q)
    (hm : 1 ≤ m) : 1 ≤ q := by
  induction h with
  | base => exact hm
  | @mul q n h hn hnq ih => exact Nat.mul_pos hn ih

theorem GreedyDenominator.divisorDense {m q : ℕ} (h : GreedyDenominator m q)
    (hm : 2 ≤ m) : DivisorDense m q := by
  induction h with
  | base => exact divisorDense_base hm
  | @mul q n h hn hnq ih =>
      exact ih.mul hm (h.positive (by omega)) hn hnq

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_MarkedGrouping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- One group strictly shrinks the remaining numerator by a factor `m²`. -/
theorem marked_grouping_step (m q X : ℕ) (hm : 2 ≤ m)
    (hX : m ^ 4 < X) (hXq : X ≤ q)
    (hdensity : HasMarkedDivisorDensity m q) :
    ∃ d s R : ℕ, 0 < d ∧ d ∣ q ∧ 1 ≤ s ∧ s ≤ m ^ 4 ∧
      X = d * s + R ∧ R * m ^ 2 < X := by
  have hm0 : 0 < m := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hm2R : (0 : ℝ) < (m : ℝ) ^ 2 := pow_pos hmR 2
  have hm2 : m ^ 2 ≤ m ^ 4 := by
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have hw1 : (1 : ℝ) ≤ (X : ℝ) / (m : ℝ) ^ 2 := by
    apply (le_div_iff₀ hm2R).2
    norm_num
    exact_mod_cast (hm2.trans hX.le)
  have hwq : (X : ℝ) / (m : ℝ) ^ 2 ≤ (q : ℝ) := by
    apply (div_le_iff₀ hm2R).2
    have hm21 : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by
      exact_mod_cast (show 1 ≤ m ^ 2 by have : 0 < m ^ 2 := pow_pos hm0 2; omega)
    have hq0 : (0 : ℝ) ≤ q := by positivity
    have hXqR : (X : ℝ) ≤ q := by exact_mod_cast hXq
    nlinarith
  obtain ⟨d, hd0, hdq, hdl, hdu⟩ := hdensity _ hw1 hwq
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  have hupper : d * m ^ 2 ≤ X := by
    have h := (le_div_iff₀ hm2R).1 hdu
    exact_mod_cast h
  have hlower : X ≤ d * m ^ 3 := by
    have h := (div_le_iff₀ hmR).1 hdl
    have h' := (div_le_iff₀ hm2R).1 h
    have heq : (d : ℝ) * (m : ℝ) * (m : ℝ) ^ 2 = (d : ℝ) * (m : ℝ) ^ 3 := by ring
    rw [heq] at h'
    exact_mod_cast h'
  refine ⟨d, X / d, X % d, hd0, hdq, ?_, ?_, ?_, ?_⟩
  · have hdm : d ≤ d * m ^ 2 := Nat.le_mul_of_pos_right d (by positivity)
    exact Nat.le_div_iff_mul_le hd0 |>.2 (by simpa using hdm.trans hupper)
  · have hdiv : X / d ≤ m ^ 3 := (Nat.div_le_iff_le_mul_add_pred hd0).2 (by omega)
    exact hdiv.trans (Nat.pow_le_pow_right (by omega) (by omega))
  · exact (Nat.div_add_mod X d).symm
  · have hmod : X % d < d := Nat.mod_lt X hd0
    exact lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hmod (by positivity)) hupper

/-- Discrete grouping bound: a numerator below `(m²)^t` needs at most `t` groups. -/
theorem marked_grouping_lt_pow (m q : ℕ) (hm : 2 ≤ m)
    (hdensity : HasMarkedDivisorDensity m q) (t X : ℕ)
    (hXq : X ≤ q) (hpow : X < (m ^ 2) ^ t) :
    ∃ groups : List (ℕ × ℕ), groups.length ≤ t ∧
      (∀ g ∈ groups, 0 < g.1 ∧ g.1 ∣ q ∧ 1 ≤ g.2 ∧ g.2 ≤ m ^ 4) ∧
      (groups.map (fun g => g.1 * g.2)).sum = X := by
  induction t generalizing X with
  | zero =>
      have hX : X = 0 := by simpa using hpow
      subst X
      exact ⟨[], by simp⟩
  | succ t ih =>
      by_cases hzero : X = 0
      · subst X
        exact ⟨[], by simp⟩
      by_cases hsmall : X ≤ m ^ 4
      · refine ⟨[(1, X)], by simp, ?_, by simp⟩
        intro g hg
        simp only [List.mem_singleton] at hg
        subst g
        exact ⟨by omega, one_dvd q, by omega, hsmall⟩
      obtain ⟨d, s, R, hd, hdq, hs, hsm, heq, hshrink⟩ :=
        marked_grouping_step m q X hm (by omega) hXq hdensity
      have hm2 : 0 < m ^ 2 := pow_pos (by omega) 2
      have hRpow : R < (m ^ 2) ^ t := by
        rw [pow_succ] at hpow
        exact Nat.lt_of_mul_lt_mul_right (hshrink.trans hpow)
      have hRX : R < X := by
        have hle : R ≤ R * m ^ 2 := Nat.le_mul_of_pos_right R hm2
        exact hle.trans_lt hshrink
      obtain ⟨groups, hlen, hgroups, hsum⟩ := ih R (by omega) hRpow
      refine ⟨(d, s) :: groups, by simpa using Nat.succ_le_succ hlen, ?_, ?_⟩
      · intro g hg
        rcases List.mem_cons.mp hg with rfl | hg
        · exact ⟨hd, hdq, hs, hsm⟩
        · exact hgroups g hg
      · simpa [hsum] using heq.symm

/-- The elementary grouping construction with its real logarithmic length bound. -/
theorem marked_grouping (m q X : ℕ) (hm : 2 ≤ m)
    (hdensity : HasMarkedDivisorDensity m q) (hXq : X ≤ q) :
    ∃ groups : List (ℕ × ℕ),
      (groups.length : ℝ) ≤ Real.log (X : ℝ) / (2 * Real.log (m : ℝ)) + 1 ∧
      (∀ g ∈ groups, 0 < g.1 ∧ g.1 ∣ q ∧ 1 ≤ g.2 ∧ g.2 ≤ m ^ 4) ∧
      (groups.map (fun g => g.1 * g.2)).sum = X := by
  have hm2 : 1 < m ^ 2 := by nlinarith
  obtain ⟨groups, hlen, hgroups, hsum⟩ := marked_grouping_lt_pow m q hm hdensity
    (Nat.log (m ^ 2) X + 1) X hXq (Nat.lt_pow_succ_log_self hm2 X)
  refine ⟨groups, ?_, hgroups, hsum⟩
  have hlenR : (groups.length : ℝ) ≤ (Nat.log (m ^ 2) X : ℝ) + 1 := by
    exact_mod_cast hlen
  have hlog := Real.natLog_le_logb X (m ^ 2)
  simp only [Real.logb, Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] at hlog
  linarith

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_MarkedGroupingUnits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- A rational with numerator dividing `K`, after scaling, is a unit fraction. -/
theorem rational_divisor_unit (q K d e t : ℕ) (hq : 0 < q) (hK : 0 < K)
    (hd : 0 < d) (hdq : d ∣ q) (he : 0 < e) (heK : e ∣ K) (ht : 0 < t) :
    0 < (q / d) * (K / e) * t ∧
    (1 : ℚ) / (((q / d) * (K / e) * t : ℕ) : ℚ) =
      ((d : ℚ) / ((q : ℚ) * (K : ℚ))) * ((e : ℚ) / (t : ℚ)) := by
  have hqd : 0 < q / d := Nat.div_pos (Nat.le_of_dvd hq hdq) hd
  have hKe : 0 < K / e := Nat.div_pos (Nat.le_of_dvd hK heK) he
  constructor
  · positivity
  have hqeq : (q : ℚ) = (d : ℚ) * (q / d : ℕ) := by
    exact_mod_cast (Nat.mul_div_cancel' hdq).symm
  have hKeq : (K : ℚ) = (e : ℚ) * (K / e : ℕ) := by
    exact_mod_cast (Nat.mul_div_cancel' heK).symm
  have hdR : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have heR : (e : ℚ) ≠ 0 := by exact_mod_cast he.ne'
  rw [hqeq, hKeq]
  push_cast
  field_simp

/-- Convert a single supplied group to positive unit fractions. -/
theorem supplied_group_units (m q K B d s : ℕ) (hq : 0 < q) (hK : 0 < K)
    (hd : 0 < d) (hdq : d ∣ q) (hs : 1 ≤ s) (hsm : s ≤ m ^ 4)
    (hsupply : HasRationalDivisorSupply m K B) :
    ∃ denoms : List ℕ, denoms.length ≤ B ∧ (∀ n ∈ denoms, 0 < n) ∧
      (denoms.map (fun n : ℕ => (1 : ℚ) / (n : ℚ))).sum =
        ((d : ℚ) * (s : ℚ)) / ((q : ℚ) * (K : ℚ)) := by
  obtain ⟨terms, hlen, hterms, hsum⟩ := hsupply s hs hsm
  let f : ℕ × ℕ → ℕ := fun et => (q / d) * (K / et.1) * et.2
  refine ⟨terms.map f, by simpa using hlen, ?_, ?_⟩
  · intro n hn
    obtain ⟨et, het, rfl⟩ := List.mem_map.mp hn
    obtain ⟨he, heK, ht⟩ := hterms et het
    exact (rational_divisor_unit q K d et.1 et.2 hq hK hd hdq he heK ht).1
  · rw [List.map_map]
    have hmap : terms.map ((fun n : ℕ => (1 : ℚ) / (n : ℚ)) ∘ f) =
        terms.map (fun et => ((d : ℚ) / ((q : ℚ) * (K : ℚ))) *
          ((et.1 : ℚ) / (et.2 : ℚ))) := by
      apply List.map_congr_left
      intro et het
      obtain ⟨he, heK, ht⟩ := hterms et het
      exact (rational_divisor_unit q K d et.1 et.2 hq hK hd hdq he heK ht).2
    rw [hmap, List.sum_map_mul_left, hsum]
    ring

/-- Concatenate supplied groups, retaining a linear length budget. -/
theorem supplied_groups_units (m q K B : ℕ) (hq : 0 < q) (hK : 0 < K)
    (hsupply : HasRationalDivisorSupply m K B) (groups : List (ℕ × ℕ))
    (hgroups : ∀ g ∈ groups, 0 < g.1 ∧ g.1 ∣ q ∧ 1 ≤ g.2 ∧ g.2 ≤ m ^ 4) :
    ∃ denoms : List ℕ, denoms.length ≤ B * groups.length ∧
      (∀ n ∈ denoms, 0 < n) ∧
      (denoms.map (fun n : ℕ => (1 : ℚ) / (n : ℚ))).sum =
        (((groups.map (fun g => g.1 * g.2)).sum : ℕ) : ℚ) / ((q : ℚ) * (K : ℚ)) := by
  induction groups with
  | nil => exact ⟨[], by simp⟩
  | cons g groups ih =>
      obtain ⟨hd, hdq, hs, hsm⟩ := hgroups g (by simp)
      obtain ⟨front, hflen, hfpos, hfsum⟩ :=
        supplied_group_units m q K B g.1 g.2 hq hK hd hdq hs hsm hsupply
      obtain ⟨tail, htlen, htpos, htsum⟩ := ih (by
        intro g hg
        exact hgroups g (by simp [hg]))
      refine ⟨front ++ tail, ?_, ?_, ?_⟩
      · simp only [List.length_append, List.length_cons]
        nlinarith
      · intro n hn
        rcases List.mem_append.mp hn with hn | hn
        · exact hfpos n hn
        · exact htpos n hn
      · simp only [List.map_append, List.sum_append, hfsum, htsum,
          List.map_cons, List.sum_cons, Nat.cast_add, Nat.cast_mul]
        ring

/-- Grouping a numerator using a rational-divisor supply yields a short unit-fraction list.
No distinctness is asserted here; later cleanup is applied only to the tail. -/
theorem marked_grouping_units_from_list_supply (m q K B X : ℕ) (hm : 2 ≤ m)
    (hq : 0 < q) (hK : 0 < K) (hXq : X ≤ q)
    (hdensity : HasMarkedDivisorDensity m q)
    (hsupply : HasRationalDivisorSupply m K B) :
    ∃ denoms : List ℕ,
      (denoms.length : ℝ) ≤ (B : ℝ) *
        (Real.log (X : ℝ) / (2 * Real.log (m : ℝ)) + 1) ∧
      (∀ n ∈ denoms, 0 < n) ∧
      (denoms.map (fun n : ℕ => (1 : ℚ) / (n : ℚ))).sum =
        (X : ℚ) / ((q : ℚ) * (K : ℚ)) := by
  obtain ⟨groups, hlen, hgroups, hsum⟩ := marked_grouping m q X hm hdensity hXq
  obtain ⟨denoms, hdlen, hdpos, hdsum⟩ :=
    supplied_groups_units m q K B hq hK hsupply groups hgroups
  refine ⟨denoms, ?_, hdpos, ?_⟩
  · have hdlenR : (denoms.length : ℝ) ≤ (B : ℝ) * (groups.length : ℝ) := by
      exact_mod_cast hdlen
    exact hdlenR.trans (mul_le_mul_of_nonneg_left hlen (by positivity))
  · simpa [hsum] using hdsum

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_MarkedGreedyDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- The concrete marked greedy trace obeys the unrestricted denominator chain. -/
theorem MarkedGreedySteps.denominator_chain {m R q Rf qf : ℕ} {L : List ℕ}
    (h : MarkedGreedySteps m R q L Rf qf) :
    GreedyDenominator m q → GreedyDenominator m qf := by
  induction h with
  | nil => exact id
  | cons R q n c L Rf qf hn hnm hnq heq hcq hcR hord tail ih =>
      intro hq
      exact ih (GreedyDenominator.mul hq (by omega) hnq)

/-- Every denominator arising from the marked prefix has divisors at every scale. -/
theorem MarkedGreedySteps.divisorDense {m R q : ℕ} {L : List ℕ}
    (h : MarkedGreedySteps m (m - 1) m L R q) (hm : 2 ≤ m) :
    DivisorDense m q :=
  (h.denominator_chain GreedyDenominator.base).divisorDense hm

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_RepeatedSquaring
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

namespace Problem337

/-- Convert a small positive rational remainder to a large unreduced denominator.
The premise `1 ≤ q*x` expresses that its numerator is a positive integer. -/
theorem denominator_bound_of_small_remainder {x q : ℝ} (e : ℕ)
    (hq : 0 ≤ q) (hnum : 1 ≤ q * x)
    (hx : x ≤ (1 / 2 : ℝ) ^ e) :
    (2 : ℝ) ^ e ≤ q := by
  have hmul : 1 ≤ q * ((1 / 2 : ℝ) ^ e) :=
    hnum.trans (mul_le_mul_of_nonneg_left hx hq)
  have hpow : (0 : ℝ) < (2 : ℝ) ^ e := by positivity
  rw [one_div_pow] at hmul
  have hdiv : 1 ≤ q / (2 : ℝ) ^ e := by simpa only [div_eq_mul_inv, one_div, one_mul] using hmul
  simpa using (le_div_iff₀ hpow).mp hdiv

/-- Inverting a double power, in the precise base-two convention used by the
marked greedy prefix bound. -/
theorem double_power_lt_loglog_bound (n : ℕ) (T : ℝ)
    (hbound : (2 : ℝ) ^ (2 ^ n) < T) :
    (n : ℝ) < Real.log (Real.log T / Real.log 2) / Real.log 2 := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hfirst := Real.log_lt_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ (2 ^ n)) hbound
  rw [Real.log_pow] at hfirst
  have hpow : (2 : ℝ) ^ n < Real.log T / Real.log 2 := by
    apply (lt_div_iff₀ hlog2).2
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hfirst
  have hsecond := Real.log_lt_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ n) hpow
  rw [Real.log_pow] at hsecond
  exact (lt_div_iff₀ hlog2).2 hsecond

/-- The stopping-time estimate for a prefix whose penultimate denominator is below T. -/
theorem marked_prefix_length_of_double_power (j : ℕ) (T : ℝ)
    (hj : 3 ≤ j) (hbound : (2 : ℝ) ^ (2 ^ (j - 3)) < T) :
    (j : ℝ) < 3 + Real.log (Real.log T / Real.log 2) / Real.log 2 := by
  have h := double_power_lt_loglog_bound (j - 3) T hbound
  have hcast : (j : ℝ) = (j - 3 : ℕ) + 3 := by
    exact_mod_cast (show j = j - 3 + 3 by omega)
  linarith

/-- Natural denominator version of the reciprocal remainder estimate. -/
theorem nat_denominator_bound_of_small_remainder (R q e : ℕ)
    (hR : 0 < R) (hq : 0 < q)
    (hsmall : (R : ℚ) / (q : ℚ) ≤ (1 / 2 : ℚ) ^ e) :
    2 ^ e ≤ q := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
  have hnum : (1 : ℝ) ≤ (q : ℝ) * ((R : ℝ) / (q : ℝ)) := by
    rw [mul_div_cancel₀ _ hqR]
    exact_mod_cast hR
  have h := denominator_bound_of_small_remainder e (by positivity) hnum
    (by
      have hh := (Rat.cast_le (K := ℝ)).mpr hsmall
      simpa only [Rat.cast_pow, Rat.cast_div, Rat.cast_natCast, Rat.cast_one,
        Rat.cast_ofNat] using hh)
  exact_mod_cast h

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_MarkedGreedyLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace Problem337

/-- Each ordinary step squares the remainder; we count only these steps. -/
theorem MarkedGreedySteps.remainder_le_pow_count {m R q Rf qf : ℕ} {L : List ℕ}
    (h : MarkedGreedySteps m R q L Rf qf) (hq : 0 < q)
    (a : ℚ) (ha : 0 ≤ a) (hstart : (R : ℚ) / q ≤ a) :
    (Rf : ℚ) / qf ≤ a ^ (2 ^ (L.filter (fun n => n ≠ m + 1)).length) := by
  induction h generalizing a with
  | nil R q => simpa using hstart
  | cons R q n c L Rf qf hn hnm hnq heq hcq hcR hord tail ih =>
    have hn0 : 0 < n := by omega
    have hqnext : 0 < n * q := Nat.mul_pos hn0 hq
    have hR : 0 < R := by nlinarith
    have hR_Q : (0 : ℚ) ≤ (R : ℚ) / q := by positivity
    have htail_nonneg : (0 : ℚ) ≤ (c : ℚ) / (n * q : ℕ) := by positivity
    by_cases hne : n ≠ m + 1
    · have hsq : (c : ℚ) / (n * q : ℕ) ≤ a ^ 2 :=
        (marked_greedy_square R q n c hR hq hn0 heq (hord hne)).le.trans
          (pow_le_pow_left₀ hR_Q hstart 2)
      have hres := ih hqnext (a ^ 2) (by positivity) hsq
      have hlen : ((n :: L).filter (fun b => b ≠ m + 1)).length =
          (L.filter (fun b => b ≠ m + 1)).length + 1 := by simp [hne]
      rw [hlen]
      calc
        (Rf : ℚ) / qf ≤ (a ^ 2) ^ (2 ^ (L.filter (fun b => b ≠ m + 1)).length) := hres
        _ = a ^ (2 ^ ((L.filter (fun b => b ≠ m + 1)).length + 1)) := by
          rw [← pow_mul, pow_succ]
          congr 1
          exact Nat.mul_comm _ _
    · have heqQ : (n : ℚ) * R = q + c := by exact_mod_cast heq
      have hnQ : (0 : ℚ) < n := by exact_mod_cast hn0
      have hqQ : (0 : ℚ) < q := by exact_mod_cast hq
      have hdec : (c : ℚ) / (n * q : ℕ) ≤ (R : ℚ) / q := by
        push_cast
        apply (div_le_div_iff₀ (mul_pos hnQ hqQ) hqQ).2
        nlinarith
      have hres := ih hqnext a ha (hdec.trans hstart)
      simpa [hne] using hres

/-- In a duplicate-free list, discarding one specified value loses at most one term. -/
theorem length_le_filter_ne_add_one (L : List ℕ) (c : ℕ) (hL : L.Nodup) :
    L.length ≤ (L.filter (fun n => n ≠ c)).length + 1 := by
  induction L with
  | nil => simp
  | cons n L ih =>
    obtain ⟨hn, htail⟩ := List.nodup_cons.mp hL
    by_cases hnc : n = c
    · subst n
      have hfilter : L.filter (fun n => n ≠ c) = L := by
        apply List.filter_eq_self.mpr
        intro a ha
        simp only [decide_eq_true_eq]
        intro hac
        subst a
        exact hn ha
      rw [List.filter_cons_of_neg (by simp), hfilter]
      simp
    · have hi := ih htail
      simpa [hnc] using Nat.succ_le_succ hi

/-- A duplicate-free marked trace has at most one non-squaring step. -/
theorem MarkedGreedySteps.remainder_le_half_pow_length {m R q Rf qf : ℕ} {L : List ℕ}
    (h : MarkedGreedySteps m R q L Rf qf) (hq : 0 < q)
    (hL : L.Nodup) (hstart : (R : ℚ) / q ≤ (1 / 2 : ℚ)) :
    (Rf : ℚ) / qf ≤ (1 / 2 : ℚ) ^ (2 ^ (L.length - 1)) := by
  have hcount := h.remainder_le_pow_count hq (1 / 2) (by norm_num) hstart
  have hlen := length_le_filter_ne_add_one L (m + 1) hL
  apply hcount.trans
  apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
  apply Nat.pow_le_pow_right (by omega : 1 ≤ 2)
  omega

/-- A marked greedy trace with a last active denominator below T has the
sharp double-logarithmic prefix length bound. -/
theorem MarkedGreedySteps.length_lt_loglog {m R q T : ℕ} {L : List ℕ}
    (h : MarkedGreedySteps m (m - 1) m L R q) (hm : 4 ≤ m)
    (hL : L.Nodup) (hT : 2 ≤ T)
    (hactive : L ≠ [] → m * L.dropLast.prod < T) :
    (L.length : ℝ) < 3 + Real.log (Real.log (T : ℝ) / Real.log 2) / Real.log 2 := by
  by_cases hlen : 3 ≤ L.length
  · have hne : L ≠ [] := by intro he; simp [he] at hlen
    obtain ⟨Ri, qi, hpre, hRi, hqi, hqeq⟩ := h.penultimate hne
    have hqiT : qi < T := by rw [hqeq]; exact hactive hne
    cases hP : L.dropLast with
    | nil =>
      have hlenP := congrArg List.length hP
      simp only [List.length_dropLast, List.length_nil] at hlenP
      omega
    | cons n S =>
      have hpre' : MarkedGreedySteps m (m - 1) m (n :: S) Ri qi := by
        simpa only [hP] using hpre
      obtain ⟨hn, htail⟩ := hpre'.first hm
      have hSnodup : S.Nodup := by
        have hPnodup := List.Nodup.sublist (List.dropLast_sublist L) hL
        rw [hP] at hPnodup
        exact (List.nodup_cons.mp hPnodup).2
      have hstart : ((m - 2 : ℕ) : ℚ) / (2 * m : ℕ) ≤ (1 / 2 : ℚ) := by
        have hden : (0 : ℚ) < (2 * m : ℕ) := by positivity
        apply (div_le_iff₀ hden).2
        have hsub : ((m - 2 : ℕ) : ℚ) ≤ (m : ℚ) := by
          exact_mod_cast Nat.sub_le m 2
        push_cast
        nlinarith
      have hrem := htail.remainder_le_half_pow_length (by omega) hSnodup hstart
      have hlenP := congrArg List.length hP
      simp only [List.length_dropLast, List.length_cons] at hlenP
      have hexp : S.length - 1 = L.length - 3 := by omega
      rw [hexp] at hrem
      have hden := nat_denominator_bound_of_small_remainder Ri qi
        (2 ^ (L.length - 3)) hRi hqi hrem
      apply marked_prefix_length_of_double_power L.length (T : ℝ) hlen
      exact_mod_cast hden.trans_lt hqiT
  · have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have hlogT : Real.log (2 : ℝ) ≤ Real.log (T : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hT)
    have hratio : 1 ≤ Real.log (T : ℝ) / Real.log 2 := by
      apply (le_div_iff₀ hlog2).2
      simpa using hlogT
    have hnonneg : 0 ≤ Real.log (Real.log (T : ℝ) / Real.log 2) / Real.log 2 :=
      div_nonneg (Real.log_nonneg hratio) hlog2.le
    have hlenR : (L.length : ℝ) < 3 := by exact_mod_cast (show L.length < 3 by omega)
    linarith

/-- The marked greedy prefix, now including its quantitative term budget. -/
theorem exists_marked_greedy_prefix_short (m T : ℕ)
    (hm : 4 ≤ m) (hT : 2 * m ^ 2 ≤ T) :
    ∃ L : List ℕ, ∃ R q : ℕ,
      MarkedGreedySteps m (m - 1) m L R q ∧
      L.Pairwise (· < ·) ∧ (∀ n ∈ L, 2 ≤ n ∧ n ≠ m) ∧
      q = m * L.prod ∧ 0 < q ∧ R < 2 * m ∧
      (1 : ℚ) = 1 / (m : ℚ) + (L.map (fun n : ℕ => (1 : ℚ) / (n : ℚ))).sum + (R : ℚ) / q ∧
      q < T ^ 2 ∧ (R = 0 ∨ T ≤ q) ∧
      m * R < q ∧ (∀ n ∈ L, n * R < q) ∧
      (L.length : ℝ) < 3 + Real.log (Real.log (T : ℝ) / Real.log 2) / Real.log 2 := by
  obtain ⟨L, R, q, htrace, hpair, hden, hqeq, hqpos, hRsmall, hsum,
    hqbound, hstop, hmarker, hfinal, hactive⟩ := exists_marked_greedy_prefix_bounded m T hm hT
  have hnodup : L.Nodup := hpair.imp (fun h => ne_of_lt h)
  have hT2 : 2 ≤ T := by nlinarith
  exact ⟨L, R, q, htrace, hpair, hden, hqeq, hqpos, hRsmall, hsum,
    hqbound, hstop, hmarker, hfinal, htrace.length_lt_loglog hm hnodup hT2 hactive⟩

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_FixedSumFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

lemma ordered_unit_sum_pos {k : ℕ} {x : ℚ} {n : Fin (k + 1) → ℕ}
    (hn : n ∈ OrderedUnitSums (k + 1) x) : 0 < x := by
  rw [← hn.2.2]
  apply Finset.sum_pos
  · intro i _
    exact div_pos (by norm_num) (by exact_mod_cast hn.1 i)
  · exact Finset.univ_nonempty

lemma ordered_unit_first_bound {k : ℕ} {x : ℚ} {n : Fin (k + 1) → ℕ}
    (hn : n ∈ OrderedUnitSums (k + 1) x) :
    n 0 ≤ ⌈((k + 1 : ℕ) : ℚ) / x⌉₊ := by
  have hx : 0 < x := ordered_unit_sum_pos hn
  have hn0 : (0 : ℚ) < n 0 := by exact_mod_cast hn.1 0
  have hsum : x ≤ ((k + 1 : ℕ) : ℚ) / (n 0 : ℚ) := by
    rw [← hn.2.2]
    calc
      (∑ i : Fin (k + 1), (1 : ℚ) / (n i : ℚ)) ≤
          ∑ _i : Fin (k + 1), (1 : ℚ) / (n 0 : ℚ) := by
        apply Finset.sum_le_sum
        intro i _
        apply one_div_le_one_div_of_le hn0
        exact_mod_cast hn.2.1 (Fin.zero_le i)
      _ = ((k + 1 : ℕ) : ℚ) / (n 0 : ℚ) := by simp [div_eq_mul_inv]
  have hmul : x * (n 0 : ℚ) ≤ ((k + 1 : ℕ) : ℚ) := (le_div_iff₀ hn0).mp hsum
  have hfirst : (n 0 : ℚ) ≤ ((k + 1 : ℕ) : ℚ) / x := by
    apply (le_div_iff₀ hx).2
    simpa [mul_comm] using hmul
  exact_mod_cast hfirst.trans (Nat.le_ceil _)

/-- For every fixed length and fixed rational total, there are only finitely
many nondecreasing tuples of positive unit-fraction denominators. -/
theorem ordered_unit_sums_finite (k : ℕ) (x : ℚ) :
    Set.Finite (OrderedUnitSums k x) := by
  induction k generalizing x with
  | zero => exact Set.toFinite _
  | succ k ih =>
    classical
    let B : ℕ := ⌈((k + 1 : ℕ) : ℚ) / x⌉₊
    have hfinite : (⋃ d ∈ Set.Icc 1 B,
        (fun t : Fin k → ℕ => Fin.cons (n := k) (α := fun _ => ℕ) d t) '' OrderedUnitSums k (x - (1 : ℚ) / (d : ℚ))).Finite := by
      apply (Set.finite_Icc 1 B).biUnion
      intro d _
      exact (ih _).image (fun t : Fin k → ℕ => Fin.cons (n := k) (α := fun _ => ℕ) d t)
    apply hfinite.subset
    intro n hn
    apply Set.mem_iUnion.2 ⟨n 0, ?_⟩
    apply Set.mem_iUnion.2 ⟨?_, ?_⟩
    · exact ⟨hn.1 0, ordered_unit_first_bound hn⟩
    · refine ⟨Fin.tail n, ?_, Fin.cons_self_tail n⟩
      refine ⟨fun i => hn.1 i.succ, ?_, ?_⟩
      · intro i j hij
        exact hn.2.1 (Fin.succ_le_succ_iff.mpr hij)
      · have hsum := hn.2.2
        rw [Fin.sum_univ_succ] at hsum
        change (∑ i : Fin k, (1 : ℚ) / (n i.succ : ℚ)) = _
        linarith

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_Distinctize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337
namespace Distinctize

/-- Takenouchi's two-term replacement increases the denominator sum. -/
theorem duplicate_split (d : ℕ) (hd : 3 ≤ d) :
    ∃ u v : ℕ, 2 ≤ u ∧ 2 ≤ v ∧
      (2 : ℚ) / d = 1 / (u : ℚ) + 1 / (v : ℚ) ∧ 2 * d < u + v := by
  let p := d / 2
  have hdiv := Nat.mod_add_div d 2
  by_cases heven : d % 2 = 0
  · have hdp : d = 2 * p := by omega
    have hp : 2 ≤ p := by omega
    refine ⟨p + 1, p * (p + 1), by omega, by nlinarith, ?_, ?_⟩
    · rw [hdp]
      push_cast
      have hp0 : (p : ℚ) ≠ 0 := by positivity
      have hp1 : (p : ℚ) + 1 ≠ 0 := by positivity
      field_simp
    · rw [hdp]
      nlinarith [sq_nonneg (p - 2 : ℤ)]
  · have hdp : d = 2 * p + 1 := by omega
    have hp : 1 ≤ p := by omega
    refine ⟨p + 1, (p + 1) * (2 * p + 1), by omega, by nlinarith, ?_, ?_⟩
    · rw [hdp]
      push_cast
      have hp1 : (p : ℚ) + 1 ≠ 0 := by positivity
      have hp2 : 2 * (p : ℚ) + 1 ≠ 0 := by positivity
      field_simp
      ring
    · rw [hdp]
      nlinarith

/-- Updating one coordinate changes a sum by the corresponding summand. -/
theorem sum_update_balance {k : ℕ} (n : Fin k → ℕ) (g : ℕ → ℚ)
    (i : Fin k) (u : ℕ) :
    (∑ j, g (Function.update n i u j)) + g (n i) =
      (∑ j, g (n j)) + g u := by
  have hfun : (fun j => g (Function.update n i u j)) =
      Function.update (fun j => g (n j)) i (g u) := by
    funext j
    exact Function.apply_update (fun _ => g) n i u j
  rw [hfun, Finset.sum_update_of_mem (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase]
  have hsum := Finset.sum_erase_add Finset.univ (fun j => g (n j)) (Finset.mem_univ i)
  linarith

/-- Replace equal coordinates by a two-term replacement. -/
theorem two_updates {k : ℕ} (n : Fin k → ℕ) (g : ℕ → ℚ)
    (i j : Fin k) (hij : i ≠ j) (u v : ℕ) :
    (∑ a, g (Function.update (Function.update n i u) j v a)) +
        g (n i) + g (n j) =
      (∑ a, g (n a)) + g u + g v := by
  have hi := sum_update_balance n g i u
  have hj := sum_update_balance (Function.update n i u) g j v
  rw [Function.update_of_ne hij.symm] at hj
  linarith

/-- Takenouchi's finite maximization argument removes all repetitions. -/
theorem distinctize_of_finite {k : ℕ} {x : ℚ} (_hx : 0 < x) (hxone : x < 1)
    (hfinite : Set.Finite {n : Fin k → ℕ | (∀ i, 0 < n i) ∧ Monotone n ∧
      (∑ i, (1 : ℚ) / (n i : ℚ)) = x})
    (n : Fin k → ℕ) (hn : ∀ i, 0 < n i)
    (hsum : (∑ i, (1 : ℚ) / (n i : ℚ)) = x) :
    ∃ d : Fin k → ℕ, (∀ i, 2 ≤ d i) ∧ StrictMono d ∧
      (∑ i, (1 : ℚ) / (d i : ℚ)) = x := by
  let S : Set (Fin k → ℕ) := {d | (∀ i, 0 < d i) ∧ Monotone d ∧
      (∑ i, (1 : ℚ) / (d i : ℚ)) = x}
  have hS : S.Nonempty := by
    refine ⟨n ∘ Tuple.sort n, (fun i => hn _), Tuple.monotone_sort n, ?_⟩
    calc
      _ = ∑ i, (1 : ℚ) / (n i : ℚ) :=
        Equiv.sum_comp (Tuple.sort n) (fun i => (1 : ℚ) / (n i : ℚ))
      _ = x := hsum
  obtain ⟨d, hd, hmax⟩ := Set.exists_max_image S
    (fun d => ∑ i, (d i : ℚ)) hfinite hS
  have hdpos : ∀ i, 0 < d i := hd.1
  have hdmono : Monotone d := hd.2.1
  have hdsum : (∑ i, (1 : ℚ) / (d i : ℚ)) = x := hd.2.2
  have hdtwo : ∀ i, 2 ≤ d i := by
    intro i
    have hsingle : (1 : ℚ) / (d i : ℚ) ≤ x := by
      rw [← hdsum]
      exact Finset.single_le_sum (f := fun j => (1 : ℚ) / (d j : ℚ))
        (by intro j hj; positivity) (Finset.mem_univ i)
    by_contra h
    have hdi : d i = 1 := by have := hdpos i; omega
    rw [hdi] at hsingle
    norm_num at hsingle
    linarith
  refine ⟨d, hdtwo, hdmono.strictMono_iff_injective.mpr ?_, hdsum⟩
  intro i j heq
  by_contra hij
  have hpair : (1 : ℚ) / (d i : ℚ) + 1 / (d j : ℚ) ≤ x := by
    have hle := Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun a => (1 : ℚ) / (d a : ℚ))
      (Finset.subset_univ {i, j}) (by intro a ha hnot; positivity)
    rw [Finset.sum_pair hij, hdsum] at hle
    exact hle
  have hdthree : 3 ≤ d i := by
    by_contra h
    have hdi : d i = 2 := by have := hdtwo i; omega
    rw [← heq, hdi] at hpair
    norm_num at hpair
    linarith
  obtain ⟨u, v, hu, hv, hsplit, hincrease⟩ := duplicate_split (d i) hdthree
  let e := Function.update (Function.update d i u) j v
  have hepos : ∀ a, 0 < e a := by
    intro a
    simp only [e, Function.update_apply]
    split_ifs <;> first | omega | exact hdpos a
  have hesum : (∑ a, (1 : ℚ) / (e a : ℚ)) = x := by
    have hbal := two_updates d (fun t => (1 : ℚ) / (t : ℚ)) i j hij u v
    change (∑ a, (1 : ℚ) / (e a : ℚ)) + 1 / (d i : ℚ) + 1 / (d j : ℚ) =
      (∑ a, (1 : ℚ) / (d a : ℚ)) + 1 / (u : ℚ) + 1 / (v : ℚ) at hbal
    rw [hdsum, ← heq] at hbal
    rw [show (2 : ℚ) / (d i : ℚ) = 1 / (d i : ℚ) + 1 / (d i : ℚ) by ring] at hsplit
    linarith [hsplit]
  have hegreater : (∑ a, (d a : ℚ)) < ∑ a, (e a : ℚ) := by
    have hbal := two_updates d (fun t => (t : ℚ)) i j hij u v
    change (∑ a, (e a : ℚ)) + (d i : ℚ) + (d j : ℚ) =
      (∑ a, (d a : ℚ)) + (u : ℚ) + (v : ℚ) at hbal
    rw [← heq] at hbal
    have hinc : 2 * (d i : ℚ) < (u : ℚ) + (v : ℚ) := by exact_mod_cast hincrease
    linarith
  have heS : e ∘ Tuple.sort e ∈ S := by
    refine ⟨(fun a => hepos _), Tuple.monotone_sort e, ?_⟩
    calc
      _ = ∑ a, (1 : ℚ) / (e a : ℚ) :=
        Equiv.sum_comp (Tuple.sort e) (fun a => (1 : ℚ) / (e a : ℚ))
      _ = x := hesum
  have hle := hmax (e ∘ Tuple.sort e) heS
  have heperm : (∑ a, ((e ∘ Tuple.sort e) a : ℚ)) = ∑ a, (e a : ℚ) :=
    Equiv.sum_comp (Tuple.sort e) (fun a => (e a : ℚ))
  rw [heperm] at hle
  linarith

/-- Every positive rational unit-fraction list of total less than one has a
strictly increasing representation with exactly the same number of terms. -/
theorem distinctize {k : ℕ} {x : ℚ} (hx : 0 < x) (hxone : x < 1)
    (n : Fin k → ℕ) (hn : ∀ i, 0 < n i)
    (hsum : (∑ i, (1 : ℚ) / (n i : ℚ)) = x) :
    ∃ d : Fin k → ℕ, (∀ i, 2 ≤ d i) ∧ StrictMono d ∧
      (∑ i, (1 : ℚ) / (d i : ℚ)) = x :=
  distinctize_of_finite hx hxone (ordered_unit_sums_finite k x) n hn hsum

end Distinctize
end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_MarkedEndgame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

open scoped BigOperators
open Filter

namespace Problem337

/-- A positive tail whose total is smaller than every reserved term cannot
reuse a reserved denominator. -/
theorem marked_tail_disjoint (p t : Finset ℕ)
    (hsmall : ∀ d ∈ p, (∑ e ∈ t, (1 : ℚ) / (e : ℚ)) < 1 / (d : ℚ)) :
    Disjoint p t := by
  apply Finset.disjoint_left.2
  intro d hdp hdt
  have hterm : (1 : ℚ) / (d : ℚ) ≤ ∑ e ∈ t, (1 : ℚ) / (e : ℚ) := by
    exact Finset.single_le_sum (f := fun e : ℕ => (1 : ℚ) / (e : ℚ))
      (fun e he => by positivity) hdt
  exact (not_lt_of_ge hterm) (hsmall d hdp)

/-- Adjoining a small distinct tail preserves every denominator in the prefix,
including the prescribed marker, and adds the lengths exactly. -/
theorem marked_expansion_of_small_tail (p t : Finset ℕ) (m : ℕ)
    (hp : ∀ d ∈ p, 1 ≤ d) (ht : ∀ d ∈ t, 1 ≤ d)
    (hm : m ∈ p)
    (hsum : (∑ d ∈ p, (1 : ℚ) / (d : ℚ)) +
      (∑ d ∈ t, (1 : ℚ) / (d : ℚ)) = 1)
    (hsmall : ∀ d ∈ p, (∑ e ∈ t, (1 : ℚ) / (e : ℚ)) < 1 / (d : ℚ)) :
    ∃ n : Fin (p.card + t.card) → ℕ,
      IsOneExpansion n ∧ ∃ i, n i = m := by
  classical
  have hdis : Disjoint p t := marked_tail_disjoint p t hsmall
  let s := p ∪ t
  have hcard : s.card = p.card + t.card := Finset.card_union_of_disjoint hdis
  let n : Fin (p.card + t.card) ↪o ℕ := s.orderEmbOfFin hcard
  refine ⟨n, ⟨?_, n.strictMono, ?_⟩, ?_⟩
  · intro i
    have hi : n i ∈ s := s.orderEmbOfFin_mem hcard i
    rcases Finset.mem_union.1 hi with hi | hi
    · exact hp _ hi
    · exact ht _ hi
  · have hn : Finset.univ.image n = s := s.image_orderEmbOfFin_univ hcard
    calc
      (∑ i, (1 : ℚ) / (n i : ℚ)) = ∑ d ∈ s, (1 : ℚ) / (d : ℚ) := by
        rw [← hn, Finset.sum_image]
        intro a ha b hb hab
        exact n.injective hab
      _ = 1 := by
        change (∑ d ∈ p ∪ t, (1 : ℚ) / (d : ℚ)) = 1
        rw [Finset.sum_union hdis]
        exact hsum
  · have hm' : m ∈ s := Finset.mem_union_left t hm
    have hrange : Set.range n = (s : Set ℕ) := s.range_orderEmbOfFin hcard
    change m ∈ Set.range n
    rw [hrange]
    exact hm'

/-- The small-tail assembly accepts the standard Egyptian expansion interface. -/
theorem marked_expansion_of_egyptian_tail {k : ℕ} {x : ℚ}
    (p : Finset ℕ) (m : ℕ) (n : Fin k → ℕ)
    (hp : ∀ d ∈ p, 1 ≤ d) (hm : m ∈ p)
    (hn : IsEgyptianExpansion x n)
    (hsum : (∑ d ∈ p, (1 : ℚ) / (d : ℚ)) + x = 1)
    (hsmall : ∀ d ∈ p, x < 1 / (d : ℚ)) :
    ∃ n' : Fin (p.card + k) → ℕ,
      IsOneExpansion n' ∧ ∃ i, n' i = m := by
  classical
  let t : Finset ℕ := Finset.univ.image n
  have htcard : t.card = k := by
    simp [t, Finset.card_image_of_injective _ hn.2.1.injective]
  have htsum : (∑ d ∈ t, (1 : ℚ) / (d : ℚ)) = x := by
    rw [Finset.sum_image]
    · exact hn.2.2
    · intro a ha b hb hab
      exact hn.2.1.injective hab
  have htpos : ∀ d ∈ t, 1 ≤ d := by
    intro d hd
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hd
    exact (hn.1 i).trans' (by omega)
  have h := marked_expansion_of_small_tail p t m hp htpos hm
    (by rw [htsum]; exact hsum) (by intro d hd; rw [htsum]; exact hsmall d hd)
  rw [← htcard]
  exact h

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_MarkedConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

open scoped BigOperators

namespace Problem337

/-- The list interface produced by grouping can be cleaned up at fixed length. -/
theorem marked_distinct_tail_of_list (l : List ℕ) {x : ℚ}
    (hx : 0 < x) (hxone : x < 1) (hl : ∀ d ∈ l, 0 < d)
    (hsum : (l.map (fun d : ℕ => (1 : ℚ) / (d : ℚ))).sum = x) :
    ∃ n : Fin l.length → ℕ, IsEgyptianExpansion x n := by
  apply Distinctize.distinctize hx hxone l.get
  · intro i
    exact hl _ (List.get_mem l i)
  · calc
      (∑ i, (1 : ℚ) / (l.get i : ℚ)) =
          (List.ofFn (fun i => (1 : ℚ) / (l.get i : ℚ))).sum := List.sum_ofFn.symm
      _ = (l.map (fun d : ℕ => (1 : ℚ) / (d : ℚ))).sum := by
        change (List.ofFn ((fun d : ℕ => (1 : ℚ) / (d : ℚ)) ∘ l.get)).sum = _
        rw [← List.map_ofFn, List.ofFn_get]
      _ = x := hsum

/-- The qualitative assembly step of the quantitative marked construction.
Only the prefix and the rational-divisor supply remain as inputs. -/
theorem marked_expansion_from_rational_supply
    (m q K R : ℕ) (p : Finset ℕ)
    (hm : 2 ≤ m) (hq : 0 < q) (hK : 0 < K)
    (hR : R < 2 * m) (hRKq : R * K ≤ q)
    (hdensity : HasMarkedDivisorDensity m q)
    (hsupply : HasRationalDivisorSupply m K 16)
    (hp : ∀ d ∈ p, 1 ≤ d) (hmarker : m ∈ p)
    (hsum : (∑ d ∈ p, (1 : ℚ) / (d : ℚ)) + (R : ℚ) / (q : ℚ) = 1)
    (hsmall : ∀ d ∈ p, (R : ℚ) / (q : ℚ) < 1 / (d : ℚ)) :
    ∃ t k : ℕ, ∃ n : Fin k → ℕ,
      k = p.card + t ∧ IsOneExpansion n ∧ (∃ i, n i = m) ∧
      (t : ℝ) ≤ 16 * ((Real.log (K : ℝ) + Real.log (2 * (m : ℝ))) /
        (2 * Real.log (m : ℝ)) + 2) := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos (by linarith)
  by_cases hRzero : R = 0
  · subst R
    obtain ⟨n, hn, hnm⟩ := marked_expansion_of_small_tail p ∅ m hp
      (by simp) hmarker (by simpa using hsum) (by simpa using hsmall)
    refine ⟨0, p.card + 0, n, rfl, hn, hnm, ?_⟩
    have hlogK : 0 ≤ Real.log (K : ℝ) := Real.log_nonneg (by exact_mod_cast hK)
    have hlog2m : 0 ≤ Real.log (2 * (m : ℝ)) := Real.log_nonneg (by linarith)
    norm_num only [Nat.cast_zero]
    positivity
  have hRpos : 0 < R := by omega
  obtain ⟨l, hlen, hlpos, hlsum⟩ :=
    marked_grouping_units_from_list_supply m q K 16 (R * K) hm hq hK hRKq hdensity hsupply
  have hcancel : ((R * K : ℕ) : ℚ) / ((q : ℚ) * (K : ℚ)) = (R : ℚ) / (q : ℚ) := by
    have hKQ : (K : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp
  rw [hcancel] at hlsum
  have hx : (0 : ℚ) < (R : ℚ) / (q : ℚ) := by positivity
  have hxone : (R : ℚ) / (q : ℚ) < 1 := by
    have hmQ : (1 : ℚ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
    have hfrac : (1 : ℚ) / (m : ℚ) ≤ 1 := by
      exact (div_le_one (by positivity : (0 : ℚ) < m)).2 hmQ
    exact (hsmall m hmarker).trans_le hfrac
  obtain ⟨tail, htail⟩ := marked_distinct_tail_of_list l hx hxone hlpos hlsum
  obtain ⟨n, hn, hnm⟩ := marked_expansion_of_egyptian_tail p m tail hp hmarker htail hsum hsmall
  refine ⟨l.length, p.card + l.length, n, rfl, hn, hnm, ?_⟩
  have hlogRK : Real.log ((R * K : ℕ) : ℝ) ≤
      Real.log (K : ℝ) + Real.log (2 * (m : ℝ)) := by
    rw [Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
    have hRR : (R : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast hR.le
    have hlogR := Real.log_le_log (by positivity : (0 : ℝ) < R) hRR
    linarith
  have hfrac := div_le_div_of_nonneg_right hlogRK (show 0 ≤ 2 * Real.log (m : ℝ) by positivity)
  norm_num at hlen
  simp only [Nat.cast_mul] at hfrac
  linarith

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_MarkedBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

open Filter

namespace Problem337

private theorem marked_loglog_tendsto :
    Tendsto (fun m : ℕ => Real.log (Real.log (m : ℝ))) atTop atTop :=
  Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

/-- Convert the supply's size budget into the short grouping budget. -/
theorem marked_group_budget (K G : ℕ → ℝ)
    (hK : ∀ δ : ℝ, 0 < δ → ∀ᶠ m : ℕ in atTop,
      Real.log (K m) ≤ (32 / Real.log 2 + δ) * Real.log (m : ℝ) *
        Real.log (Real.log (m : ℝ)))
    (hG : ∀ᶠ m : ℕ in atTop,
      G m ≤ (Real.log (K m) + Real.log (2 * (m : ℝ))) /
        (2 * Real.log (m : ℝ)) + 2) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop,
      G m ≤ (16 / Real.log 2 + ε) * Real.log (Real.log (m : ℝ)) := by
  intro ε hε
  have hlarge : ∀ᶠ m : ℕ in atTop, 6 / ε ≤ Real.log (Real.log (m : ℝ)) :=
    marked_loglog_tendsto.eventually (eventually_ge_atTop (6 / ε))
  filter_upwards [hK ε hε, hG, hlarge, eventually_ge_atTop (2 : ℕ)] with m hK hG hlarge hm
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos (by linarith)
  have hlog2m : Real.log (2 * (m : ℝ)) ≤ 2 * Real.log (m : ℝ) := by
    rw [Real.log_mul (by norm_num) (by positivity)]
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hmR
    linarith
  have hG' : (G m - 2) * (2 * Real.log (m : ℝ)) ≤
      Real.log (K m) + Real.log (2 * (m : ℝ)) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * Real.log (m : ℝ))).1
    linarith
  have hproduct : (2 * G m) * Real.log (m : ℝ) ≤
      ((32 / Real.log 2 + ε) * Real.log (Real.log (m : ℝ)) + 6) *
        Real.log (m : ℝ) := by nlinarith
  have hsimple := le_of_mul_le_mul_right hproduct hlogm
  have hlarge' : 6 ≤ Real.log (Real.log (m : ℝ)) * ε :=
    (div_le_iff₀ hε).1 hlarge
  have hcoef : (32 : ℝ) / Real.log 2 = 2 * (16 / Real.log 2) := by ring
  nlinarith

/-- Elementary error absorption used after taking a second logarithm. -/
theorem eventually_log_add_const_le_mul (C ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, Real.log x + C ≤ ε * x := by
  have htlog : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have htconst : Tendsto (fun x : ℝ => C / x) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have ht : Tendsto (fun x : ℝ => (Real.log x + C) / x) atTop (nhds 0) := by
    simpa [add_div] using htlog.add htconst
  filter_upwards [ht.eventually_le_const hε, eventually_gt_atTop (0 : ℝ)] with x hx hxpos
  exact (div_le_iff₀ hxpos).1 hx

/-- Convert the greedy stopping-time formula and supply size into the prefix
coefficient.  A fixed coarse supply bound suffices for this part. -/
theorem marked_prefix_budget (K J : ℕ → ℝ)
    (hKpositive : ∀ᶠ m : ℕ in atTop, 1 ≤ K m)
    (hK : ∀ᶠ m : ℕ in atTop,
      Real.log (K m) ≤ (32 / Real.log 2 + 1) * Real.log (m : ℝ) *
        Real.log (Real.log (m : ℝ)))
    (hJ : ∀ᶠ m : ℕ in atTop,
      J m ≤ 3 + (Real.log (Real.log (2 * (m : ℝ) * K m)) -
        Real.log (Real.log 2)) / Real.log 2) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop,
      J m ≤ (1 / Real.log 2 + ε) * Real.log (Real.log (m : ℝ)) := by
  intro ε hε
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let B : ℝ := 32 / Real.log 2 + 3
  let C : ℝ := Real.log B - Real.log (Real.log 2) + 3 * Real.log 2
  have hB : 0 < B := by dsimp [B]; positivity
  have herror : ∀ᶠ m : ℕ in atTop,
      Real.log (Real.log (Real.log (m : ℝ))) + C ≤
        (ε * Real.log 2) * Real.log (Real.log (m : ℝ)) :=
    marked_loglog_tendsto.eventually
      (eventually_log_add_const_le_mul C (ε * Real.log 2) (mul_pos hε hlog2))
  have hlarge : ∀ᶠ m : ℕ in atTop, 1 ≤ Real.log (Real.log (m : ℝ)) :=
    marked_loglog_tendsto.eventually (eventually_ge_atTop 1)
  filter_upwards [hKpositive, hK, hJ, herror, hlarge, eventually_ge_atTop (2 : ℕ)]
    with m hKpositive hK hJ herror hlarge hm
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos (by linarith)
  have hL : 0 < Real.log (Real.log (m : ℝ)) := by linarith
  have hT : 1 < 2 * (m : ℝ) * K m := by nlinarith
  have hlogT : Real.log (2 * (m : ℝ) * K m) ≤
      B * Real.log (m : ℝ) * Real.log (Real.log (m : ℝ)) := by
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity)]
    have hlog2le := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hmR
    dsimp [B]
    nlinarith
  have hloglogT : Real.log (Real.log (2 * (m : ℝ) * K m)) ≤
      Real.log (Real.log (m : ℝ)) + Real.log (Real.log (Real.log (m : ℝ))) +
        Real.log B := by
    calc
      Real.log (Real.log (2 * (m : ℝ) * K m)) ≤
          Real.log (B * Real.log (m : ℝ) * Real.log (Real.log (m : ℝ))) :=
        Real.log_le_log (Real.log_pos hT) hlogT
      _ = _ := by
        rw [Real.log_mul (by positivity) (ne_of_gt hL),
          Real.log_mul (ne_of_gt hB) (ne_of_gt hlogm)]
        ring
  have hJ' : (J m - 3) * Real.log 2 ≤
      Real.log (Real.log (2 * (m : ℝ) * K m)) - Real.log (Real.log 2) := by
    apply (le_div_iff₀ hlog2).1
    linarith
  apply le_of_mul_le_mul_right (a := Real.log 2) ?_ hlog2
  have hident : ((1 / Real.log 2 + ε) * Real.log (Real.log (m : ℝ))) * Real.log 2 =
      Real.log (Real.log (m : ℝ)) + (ε * Real.log 2) * Real.log (Real.log (m : ℝ)) := by
    field_simp
  rw [hident]
  dsimp [C] at herror
  linarith

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_MarkedQuantitative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

open Filter

namespace Problem337

/-- A final reduction of the quantitative marked target to the explicit
construction bounds, before asymptotic error absorption. -/
theorem quantitative_marked_length_of_explicit_budget (K : ℕ → ℝ)
    (hKpositive : ∀ᶠ m : ℕ in atTop, 1 ≤ K m)
    (hK : ∀ δ : ℝ, 0 < δ → ∀ᶠ m : ℕ in atTop,
      Real.log (K m) ≤ (32 / Real.log 2 + δ) * Real.log (m : ℝ) *
        Real.log (Real.log (m : ℝ)))
    (hconstruct : ∀ᶠ m : ℕ in atTop,
      ∃ j t k : ℕ, ∃ n : Fin k → ℕ,
        IsOneExpansion n ∧ (∃ i, n i = m) ∧ k ≤ 1 + j + t ∧
        (j : ℝ) ≤ 3 + (Real.log (Real.log (2 * (m : ℝ) * K m)) -
          Real.log (Real.log 2)) / Real.log 2 ∧
        (t : ℝ) ≤ 16 * ((Real.log (K m) + Real.log (2 * (m : ℝ))) /
          (2 * Real.log (m : ℝ)) + 2)) :
    ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, 2 ≤ M ∧
      ∀ m : ℕ, M ≤ m → ∃ k : ℕ, ∃ n : Fin k → ℕ,
        IsOneExpansion n ∧ (∃ i, n i = m) ∧
        (k : ℝ) ≤ (257 / Real.log 2 + ε) * Real.log (Real.log (m : ℝ)) := by
  intro ε hε
  let J : ℕ → ℝ := fun m => 3 + (Real.log (Real.log (2 * (m : ℝ) * K m)) -
    Real.log (Real.log 2)) / Real.log 2
  let G : ℕ → ℝ := fun m => (Real.log (K m) + Real.log (2 * (m : ℝ))) /
    (2 * Real.log (m : ℝ)) + 2
  have hJ := marked_prefix_budget K J hKpositive (hK 1 zero_lt_one)
    (Eventually.of_forall (fun m => le_rfl)) (ε / 34) (by positivity)
  have hG := marked_group_budget K G hK
    (Eventually.of_forall (fun m => le_rfl)) (ε / 34) (by positivity)
  have hloglog : Tendsto (fun m : ℕ => Real.log (Real.log (m : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hlarge : ∀ᶠ m : ℕ in atTop, 2 / ε ≤ Real.log (Real.log (m : ℝ)) :=
    hloglog.eventually (eventually_ge_atTop (2 / ε))
  have hevent : ∀ᶠ m : ℕ in atTop, ∃ k : ℕ, ∃ n : Fin k → ℕ,
      IsOneExpansion n ∧ (∃ i, n i = m) ∧
      (k : ℝ) ≤ (257 / Real.log 2 + ε) * Real.log (Real.log (m : ℝ)) := by
    filter_upwards [hconstruct, hJ, hG, hlarge] with m hm hJ hG hlarge
    obtain ⟨j, t, k, n, hn, hmarker, hk, hj, ht⟩ := hm
    refine ⟨k, n, hn, hmarker, ?_⟩
    have hj' : (j : ℝ) ≤ (1 / Real.log 2 + ε / 34) * Real.log (Real.log (m : ℝ)) :=
      hj.trans hJ
    have ht' : (t : ℝ) ≤ 16 * ((16 / Real.log 2 + ε / 34) * Real.log (Real.log (m : ℝ))) :=
      ht.trans (mul_le_mul_of_nonneg_left hG (by norm_num))
    have hkR : (k : ℝ) ≤ 1 + (j : ℝ) + (t : ℝ) := by exact_mod_cast hk
    have hlarge' : 2 ≤ Real.log (Real.log (m : ℝ)) * ε :=
      (div_le_iff₀ hε).1 hlarge
    have hcoef : (1 : ℝ) / Real.log 2 + 16 * (16 / Real.log 2) = 257 / Real.log 2 := by ring
    nlinarith
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  refine ⟨max 2 N, le_max_left _ _, ?_⟩
  intro m hm
  exact hN m ((le_max_right _ _).trans hm)

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_MarkedReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

open scoped BigOperators
open Filter

namespace Problem337

/-- Full quantitative endgame: a rational-divisor supply with a logarithmic
size estimate and the marked greedy prefix imply the `257 / log 2 + ε` bound.
Both remaining construction inputs are exposed explicitly. -/
theorem quantitative_marked_length_of_supply_and_prefix (K : ℕ → ℕ)
    (hKpositive : ∀ᶠ m : ℕ in atTop, 0 < K m)
    (hsize : ∀ δ : ℝ, 0 < δ → ∀ᶠ m : ℕ in atTop,
      Real.log (K m : ℝ) ≤ (32 / Real.log 2 + δ) * Real.log (m : ℝ) *
        Real.log (Real.log (m : ℝ)))
    (hsupply : ∀ᶠ m : ℕ in atTop, HasRationalDivisorSupply m (K m) 16)
    (hprefix : ∀ᶠ m : ℕ in atTop, HasQuantitativeMarkedPrefix m (K m)) :
    ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, 2 ≤ M ∧
      ∀ m : ℕ, M ≤ m → ∃ k : ℕ, ∃ n : Fin k → ℕ,
        IsOneExpansion n ∧ (∃ i, n i = m) ∧
        (k : ℝ) ≤ (257 / Real.log 2 + ε) * Real.log (Real.log (m : ℝ)) := by
  apply quantitative_marked_length_of_explicit_budget (fun m => (K m : ℝ))
  · filter_upwards [hKpositive] with m hm
    exact_mod_cast hm
  · exact hsize
  · filter_upwards [hKpositive, hsupply, hprefix, eventually_ge_atTop (2 : ℕ)]
      with m hKpositive hsupply hprefix hm
    obtain ⟨p, q, R, hq, hR, hRKq, hdensity, hp, hmarker, hsum, hsmall, hlength⟩ := hprefix
    have hp' : ∀ d ∈ insert m p, 1 ≤ d := by
      intro d hd
      rcases Finset.mem_insert.1 hd with rfl | hd
      · omega
      · exact hp d hd
    have hsum' : (∑ d ∈ insert m p, (1 : ℚ) / (d : ℚ)) + (R : ℚ) / (q : ℚ) = 1 := by
      rw [Finset.sum_insert hmarker]
      exact hsum
    obtain ⟨t, k, n, hk, hn, hnm, ht⟩ :=
      marked_expansion_from_rational_supply m q (K m) R (insert m p) hm hq hKpositive
        hR hRKq hdensity hsupply hp' (Finset.mem_insert_self m p) hsum' hsmall
    refine ⟨p.card, t, k, n, hn, hnm, ?_, hlength, ht⟩
    rw [Finset.card_insert_of_notMem hmarker] at hk
    omega

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_MarkedPrefixBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

open scoped BigOperators

namespace Problem337

/-- Translate the finite marked greedy list into the exact finite-set contract
consumed by the quantitative endgame. -/
theorem quantitative_marked_prefix_of_short_list
    (m K R q : ℕ) (L : List ℕ) (hm : 4 ≤ m) (hK : m ≤ K)
    (htrace : MarkedGreedySteps m (m - 1) m L R q)
    (hpair : L.Pairwise (· < ·)) (hlist : ∀ d ∈ L, 2 ≤ d ∧ d ≠ m)
    (hq : 0 < q) (hR : R < 2 * m)
    (hsum : (1 : ℚ) = 1 / (m : ℚ) +
      (L.map (fun d : ℕ => (1 : ℚ) / (d : ℚ))).sum + (R : ℚ) / (q : ℚ))
    (hstop : R = 0 ∨ 2 * m * K ≤ q)
    (hmarker : m * R < q) (hfinal : ∀ d ∈ L, d * R < q)
    (hlen : (L.length : ℝ) ≤ 3 +
      (Real.log (Real.log (2 * (m : ℝ) * (K : ℝ))) - Real.log (Real.log 2)) /
        Real.log 2) :
    HasQuantitativeMarkedPrefix m K := by
  classical
  have hnodup : L.Nodup := hpair.nodup
  have hRKq : R * K ≤ q := by
    rcases hstop with hzero | hlarge
    · simp [hzero]
    · nlinarith
  have hdense : HasMarkedDivisorDensity m q := htrace.divisorDense (by omega)
  refine ⟨L.toFinset, q, R, hq, hR, hRKq, hdense, ?_, ?_, ?_, ?_, ?_⟩
  · intro d hd
    have := (hlist d (List.mem_toFinset.1 hd)).1
    omega
  · intro hmL
    exact (hlist m (List.mem_toFinset.1 hmL)).2 rfl
  · rw [List.sum_toFinset _ hnodup]
    exact hsum.symm
  · intro d hd
    have hdpos : 0 < d := by
      rcases Finset.mem_insert.1 hd with rfl | hd
      · omega
      · have := (hlist d (List.mem_toFinset.1 hd)).1
        omega
    have hdR : d * R < q := by
      rcases Finset.mem_insert.1 hd with rfl | hd
      · exact hmarker
      · exact hfinal d (List.mem_toFinset.1 hd)
    apply (div_lt_div_iff₀ (show (0 : ℚ) < q by positivity)
      (show (0 : ℚ) < d by positivity)).2
    have hdR' : (d : ℚ) * (R : ℚ) < q := by exact_mod_cast hdR
    nlinarith
  · rw [List.toFinset_card_of_nodup hnodup]
    exact hlen

/-- The complete marked greedy construction discharges the prefix prerequisite
for every multiplier at least as large as the marker. -/
theorem hasQuantitativeMarkedPrefix_of_le (m K : ℕ) (hm : 4 ≤ m) (hK : m ≤ K) :
    HasQuantitativeMarkedPrefix m K := by
  have hT : 2 * m ^ 2 ≤ 2 * m * K := by nlinarith
  obtain ⟨L, R, q, htrace, hpair, hlist, hqeq, hq, hR, hsum,
    hqbound, hstop, hmarker, hfinal, hlen⟩ :=
      exists_marked_greedy_prefix_short m (2 * m * K) hm hT
  apply quantitative_marked_prefix_of_short_list m K R q L hm hK htrace hpair hlist
    hq hR hsum hstop hmarker hfinal
  have hTreal : (1 : ℝ) < ((2 * m * K : ℕ) : ℝ) := by
    exact_mod_cast (show 1 < 2 * m * K by nlinarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [Real.log_div (ne_of_gt (Real.log_pos hTreal)) (ne_of_gt hlog2)] at hlen
  push_cast at hlen
  exact hlen.le

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_CompositeMarkedReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open Filter

namespace Problem337.CompositeSupply

/-- The new fourth-power auxiliary integer can be passed directly to the
already proved marked construction.  Its positivity, size coefficient, and
marked greedy prefix are unconditional; precisely the arithmetic supply
remains as an explicit hypothesis here. -/
theorem quantitative_marked_length_of_supply
    (hsupply : ∀ᶠ m : ℕ in atTop, HasRationalDivisorSupply m (multiplier m) 16) :
    ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, 2 ≤ M ∧
      ∀ m : ℕ, M ≤ m → ∃ k : ℕ, ∃ n : Fin k → ℕ,
        IsOneExpansion n ∧ (∃ i, n i = m) ∧
        (k : ℝ) ≤ (257 / Real.log 2 + ε) * Real.log (Real.log (m : ℝ)) := by
  apply quantitative_marked_length_of_supply_and_prefix multiplier
    (Eventually.of_forall multiplier_pos) eventually_log_multiplier_le hsupply
  filter_upwards [eventually_ge_atTop (4 : ℕ)] with m hm
  exact hasQuantitativeMarkedPrefix_of_le m (multiplier m) hm
    (marker_lt_multiplier m (by omega)).le

end Problem337.CompositeSupply

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_RationalDivisorSupplyAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

open scoped BigOperators

namespace Problem337

theorem hasRationalDivisorSum_of_dvd {K s : ℕ} (hs : 0 < s) (hdiv : s ∣ K) :
    HasRationalDivisorSum K (s : ℚ) 1 := by
  refine ⟨1, le_rfl, (fun _ => s), (fun _ => 1), ?_, ?_⟩
  · intro i
    exact ⟨hs, hdiv, by norm_num⟩
  · simp

theorem hasRationalDivisorSum_of_common_denominator {K k t : ℕ} {x : ℚ}
    (e : Fin k → ℕ) (ht : 0 < t) (he : ∀ i, 0 < e i ∧ e i ∣ K)
    (hsum : (∑ i, (e i : ℚ) / (t : ℚ)) = x) :
    HasRationalDivisorSum K x k := by
  exact ⟨k, le_rfl, e, (fun _ => t), fun i => ⟨(he i).1, (he i).2, ht⟩, hsum⟩

theorem HasRationalDivisorSum.add {K B C : ℕ} {x y : ℚ}
    (hx : HasRationalDivisorSum K x B) (hy : HasRationalDivisorSum K y C) :
    HasRationalDivisorSum K (x + y) (B + C) := by
  obtain ⟨k, hk, e, t, het, hsum⟩ := hx
  obtain ⟨l, hl, f, u, hfu, hsum'⟩ := hy
  refine ⟨k + l, Nat.add_le_add hk hl, Fin.append e f, Fin.append t u, ?_, ?_⟩
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa using het j
    · intro j
      simpa using hfu j
  · rw [Fin.sum_univ_add]
    simpa using congrArg₂ (· + ·) hsum hsum'

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_RationalDivisorSupplyBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- Convert the finite-indexed supply API to the list API consumed by grouping. -/
theorem HasRationalDivisorSum.to_list {K B : ℕ} {x : ℚ}
    (h : HasRationalDivisorSum K x B) :
    ∃ terms : List (ℕ × ℕ), terms.length ≤ B ∧
      (∀ et ∈ terms, 0 < et.1 ∧ et.1 ∣ K ∧ 0 < et.2) ∧
      (terms.map (fun et => (et.1 : ℚ) / (et.2 : ℚ))).sum = x := by
  obtain ⟨k, hk, e, t, het, hsum⟩ := h
  refine ⟨List.ofFn (fun i => (e i, t i)), by simpa using hk, ?_, ?_⟩
  · intro et hmem
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hmem
    exact het i
  · simpa only [List.map_ofFn, List.sum_ofFn, Function.comp_apply] using hsum

/-- The algebraic odd-integer supply interface directly feeds the canonical
unit-fraction grouping construction. -/
theorem rational_divisor_supply_bridge {m K B : ℕ}
    (h : ∀ s : ℕ, 1 ≤ s → s ≤ m ^ 4 → HasRationalDivisorSum K (s : ℚ) B) :
    HasRationalDivisorSupply m K B := by
  intro s hs hsm
  exact (h s hs hsm).to_list

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_RationalSupplyScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- Dividing a rational-divisor representation by a positive integer does not
change its numerators or its number of summands. -/
theorem HasRationalDivisorSum.div_nat {K B : ℕ} {x : ℚ}
    (h : HasRationalDivisorSum K x B) {d : ℕ} (hd : 0 < d) :
    HasRationalDivisorSum K (x / (d : ℚ)) B := by
  obtain ⟨k, hk, e, t, het, hsum⟩ := h
  refine ⟨k, hk, e, (fun i => t i * d), ?_, ?_⟩
  · intro i
    exact ⟨(het i).1, (het i).2.1, Nat.mul_pos (het i).2.2 hd⟩
  · simp only [Nat.cast_mul, ← div_div]
    rw [← Finset.sum_div, hsum]

/-- It suffices to represent any positive integral multiple of the desired
integer. No upper bound on the multiplier is needed in this algebraic step. -/
theorem HasRationalDivisorSum.of_nat_multiple {K B d s : ℕ}
    (h : HasRationalDivisorSum K ((d * s : ℕ) : ℚ) B) (hd : 0 < d) :
    HasRationalDivisorSum K (s : ℚ) B := by
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  simpa only [Nat.cast_mul, mul_div_cancel_left₀ _ hdq] using h.div_nat hd

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_CompositeRationalSupply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- Multiplication convolves the two positive lists. Numerators divide the
product of the original supplies, and the term budgets multiply. -/
theorem HasRationalDivisorSum.mul {K L B C : ℕ} {x y : ℚ}
    (hx : HasRationalDivisorSum K x B) (hy : HasRationalDivisorSum L y C) :
    HasRationalDivisorSum (K * L) (x * y) (B * C) := by
  obtain ⟨k, hk, e, t, het, hsum⟩ := hx
  obtain ⟨l, hl, f, u, hfu, hsum'⟩ := hy
  let E : Fin (k * l) ≃ Fin k × Fin l := finProdFinEquiv.symm
  refine ⟨k * l, Nat.mul_le_mul hk hl,
    (fun i => e (E i).1 * f (E i).2),
    (fun i => t (E i).1 * u (E i).2), ?_, ?_⟩
  · intro i
    exact ⟨Nat.mul_pos (het _).1 (hfu _).1,
      Nat.mul_dvd_mul (het _).2.1 (hfu _).2.1,
      Nat.mul_pos (het _).2.2 (hfu _).2.2⟩
  · simp only [Nat.cast_mul, mul_div_mul_comm]
    rw [E.sum_comp (fun z : Fin k × Fin l =>
      ((e z.1 : ℚ) / t z.1) * ((f z.2 : ℚ) / u z.2))]
    rw [Fintype.sum_prod_type]
    dsimp only
    rw [← Fintype.sum_mul_sum, hsum, hsum']

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_CubeFreeDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

open scoped BigOperators

namespace Problem337.CubeFreeDensity

/-- A telescoping majorant with no infinite-series or asymptotic input. -/
theorem reciprocal_cube_le (j : ℕ) :
    1 / ((j : ℝ) + 2) ^ 3 ≤
      (1 / 4 : ℝ) * (1 / ((j : ℝ) + 1) - 1 / ((j : ℝ) + 2)) := by
  have h1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) < (j : ℝ) + 2 := by positivity
  have hden : 4 * ((j : ℝ) + 1) * ((j : ℝ) + 2) ≤ ((j : ℝ) + 2) ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg (j : ℝ)) h2.le]
  calc
    _ ≤ 1 / (4 * ((j : ℝ) + 1) * ((j : ℝ) + 2)) :=
      one_div_le_one_div_of_le (by positivity) hden
    _ = _ := by field_simp; ring

/-- The reciprocal cubes starting at two have every finite sum at most one
quarter. The intentionally elementary constant leaves room above density 2/3. -/
theorem sum_reciprocal_cubes_le (N : ℕ) :
    (∑ j ∈ Finset.range N, 1 / ((j : ℝ) + 2) ^ 3) ≤ (1 / 4 : ℝ) := by
  calc
    _ ≤ ∑ j ∈ Finset.range N,
        (1 / 4 : ℝ) * (1 / ((j : ℝ) + 1) - 1 / ((j : ℝ) + 2)) :=
      Finset.sum_le_sum (fun j _ => reciprocal_cube_le j)
    _ = (1 / 4 : ℝ) * (1 - 1 / ((N : ℝ) + 1)) := by
      rw [← Finset.mul_sum]
      have h := Finset.sum_range_sub' (fun j : ℕ => 1 / ((j : ℝ) + 1)) N
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add, div_one,
        add_assoc, one_add_one_eq_two] using congrArg (fun x : ℝ => (1 / 4) * x) h
    _ ≤ _ := by
      have h : (0 : ℝ) ≤ 1 / ((N : ℝ) + 1) := by positivity
      linarith

theorem card_positive_multiples (N d : ℕ) :
    ((Finset.Icc 1 N).filter (fun n => d ∣ n)).card = N / d := by
  have hI : Finset.Icc 1 N = Finset.Ioc 0 N := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hI, Nat.Ioc_filter_dvd_card_eq_div]

/-- An exact finite union bound, including all composite cube bases. -/
theorem card_bad_le_sum (N : ℕ) :
    (bad N).card ≤ ∑ j ∈ Finset.range N, N / (j + 2) ^ 3 := by
  classical
  let A : ℕ → Finset ℕ := fun j =>
    (Finset.Icc 1 N).filter (fun n => (j + 2) ^ 3 ∣ n)
  have hsub : bad N ⊆ (Finset.range N).biUnion A := by
    intro n hn
    obtain ⟨hn1, hnN, k, hk, hkdiv⟩ := mem_bad.mp hn
    have hkN : k ≤ N := (Nat.le_self_pow (by norm_num : 3 ≠ 0) k).trans
      ((Nat.le_of_dvd hn1 hkdiv).trans hnN)
    refine Finset.mem_biUnion.mpr ⟨k - 2, Finset.mem_range.mpr (by omega), ?_⟩
    dsimp [A]
    rw [Nat.sub_add_cancel hk]
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hn1, hnN⟩, hkdiv⟩
  calc
    _ ≤ ((Finset.range N).biUnion A).card := Finset.card_le_card hsub
    _ ≤ ∑ j ∈ Finset.range N, (A j).card := Finset.card_biUnion_le
    _ = _ := by simp only [A, card_positive_multiples]

/-- At most one quarter of any initial interval is divisible by a nontrivial
cube. This is uniform in the endpoint and has no additive error term. -/
theorem card_bad_le_quarter (N : ℕ) :
    ((bad N).card : ℝ) ≤ (N : ℝ) / 4 := by
  calc
    _ ≤ ∑ j ∈ Finset.range N, ((N / (j + 2) ^ 3 : ℕ) : ℝ) := by
      exact_mod_cast card_bad_le_sum N
    _ ≤ ∑ j ∈ Finset.range N, (N : ℝ) / ((j : ℝ) + 2) ^ 3 := by
      apply Finset.sum_le_sum
      intro j hj
      simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat] using
        (Nat.cast_div_le (m := N) (n := (j + 2) ^ 3) :
          ((N / (j + 2) ^ 3 : ℕ) : ℝ) ≤ (N : ℝ) / ((j + 2) ^ 3 : ℕ))
    _ = (N : ℝ) * ∑ j ∈ Finset.range N, 1 / ((j : ℝ) + 2) ^ 3 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ (N : ℝ) * (1 / 4) :=
      mul_le_mul_of_nonneg_left (sum_reciprocal_cubes_le N) (Nat.cast_nonneg N)
    _ = _ := by ring

/-- Consequently cube-free moduli have the explicit uniform density 3/4. -/
theorem card_good_ge_three_quarters (N : ℕ) :
    (3 : ℝ) * N / 4 ≤ (good N).card := by
  have hsub : bad N ⊆ Finset.Icc 1 N := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨(mem_bad.mp hn).1, (mem_bad.mp hn).2.1⟩
  have hcard : (good N).card + (bad N).card = N := by
    simpa only [good, Nat.card_Icc, Nat.add_sub_cancel] using
      Finset.card_sdiff_add_card_eq_card hsub
  have hcardR : ((good N).card : ℝ) + (bad N).card = N := by exact_mod_cast hcard
  linarith [card_bad_le_quarter N]

/-- Deleting fewer than `N/12` further exceptional moduli still leaves the
strict density `2/3` required by the dense rational-supply completion. -/
theorem card_good_sdiff_gt_two_thirds (N : ℕ) (E : Finset ℕ)
    (hE : (E.card : ℝ) < (N : ℝ) / 12) :
    (2 : ℝ) * N / 3 < (good N \ E).card := by
  have hcard : ((good N).card : ℝ) ≤ (good N \ E).card + E.card := by
    exact_mod_cast (Finset.card_le_card_sdiff_add_card :
      (good N).card ≤ (good N \ E).card + E.card)
  linarith [card_good_ge_three_quarters N]

theorem prime_cube_not_dvd_of_mem_good {N n p : ℕ} (hn : n ∈ good N)
    (hp : p.Prime) : ¬ p ^ 3 ∣ n :=
  (mem_good.mp hn).2.2 p hp.two_le

end Problem337.CubeFreeDensity

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_DenseModularPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

namespace Problem337

/-- Counting an interval by its quotient and represented residue classes. The
second bound separates complete blocks from the final incomplete block. -/
theorem interval_card_le_residue_support (A : Finset ℕ) (N s : ℕ)
    (hs : 0 < s) (hA : A ⊆ Finset.range N) :
    let H := A.image (fun n : ℕ => (n : ZMod s))
    A.card ≤ (N / s + 1) * H.card ∧
      A.card ≤ N / s * H.card + N % s := by
  classical
  let : NeZero s := ⟨hs.ne'⟩
  let H := A.image (fun n : ℕ => (n : ZMod s))
  change A.card ≤ (N / s + 1) * H.card ∧
    A.card ≤ N / s * H.card + N % s
  have hinj : Function.Injective (fun n : ℕ => (n / s, (n : ZMod s))) := by
    intro a b hab
    have hq := congrArg Prod.fst hab
    change a / s = b / s at hq
    have hr := congrArg Prod.snd hab
    have hm := (ZMod.natCast_eq_natCast_iff a b s).mp hr
    change a % s = b % s at hm
    have ha := Nat.mod_add_div a s
    have hb := Nat.mod_add_div b s
    rw [hq, hm] at ha
    omega
  have hcount (T : Finset ℕ) (hT : T ⊆ A) (Q : ℕ)
      (hQ : ∀ n ∈ T, n / s < Q) : T.card ≤ Q * H.card := by
    have hh := Finset.card_le_card_of_injOn
      (s := T) (t := Finset.range Q ×ˢ H)
      (fun n : ℕ => (n / s, (n : ZMod s)))
      (by
        intro n hn
        exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (hQ n hn),
          Finset.mem_image.mpr ⟨n, hT hn, rfl⟩⟩)
      (hinj.injOn)
    simpa only [Finset.card_product, Finset.card_range] using hh
  constructor
  · apply hcount A (fun _ h => h) (N / s + 1)
    intro n hn
    have hnN := Finset.mem_range.mp (hA hn)
    have hh : n / s ≤ N / s := Nat.div_le_div_right hnN.le
    omega
  · let Q := N / s
    have hfirst : (A.filter (fun n => n / s < Q)).card ≤ Q * H.card := by
      apply hcount _ (Finset.filter_subset _ _) Q
      intro n hn
      exact (Finset.mem_filter.mp hn).2
    have hrest : (A.filter (fun n => ¬n / s < Q)).card ≤ N % s := by
      calc
        _ ≤ (Finset.Ico (Q * s) N).card := by
          apply Finset.card_le_card
          intro n hn
          obtain ⟨hnA, hnQ⟩ := Finset.mem_filter.mp hn
          exact Finset.mem_Ico.mpr
            ⟨(Nat.le_div_iff_mul_le hs).mp (by omega),
              Finset.mem_range.mp (hA hnA)⟩
        _ = N % s := by
          rw [Nat.card_Ico, Nat.mod_eq_sub_div_mul]
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := A) (fun n => n / s < Q)
    dsimp only [Q] at hfirst hsplit hrest
    omega

/-- If a residue support avoids its reflected copy, then a subset of an
interval containing at least a full period has density at most two thirds.
The target residue is arbitrary, including self-opposite residues. -/
theorem interval_card_le_two_thirds_of_no_modular_pair
    (A : Finset ℕ) (N s : ℕ) (hs : 0 < s) (hsN : s ≤ N)
    (hA : A ⊆ Finset.range N) (t : ZMod s)
    (hno : ∀ u ∈ A, ∀ v ∈ A, (u : ZMod s) + (v : ZMod s) ≠ t) :
    3 * A.card ≤ 2 * N := by
  classical
  let : NeZero s := ⟨hs.ne'⟩
  let H := A.image (fun n : ℕ => (n : ZMod s))
  let R := H.image (fun x => t - x)
  have hdisjoint : Disjoint H R := by
    apply Finset.disjoint_left.mpr
    intro x hx hxR
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hxR
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    apply hno u hu v hv
    rw [← hxy]
    exact sub_add_cancel t (v : ZMod s)
  have hR : R.card = H.card := by
    apply Finset.card_image_of_injective
    intro x y hxy
    exact sub_right_inj.mp hxy
  have hhalf : 2 * H.card ≤ s := by
    have hh := Finset.card_le_card (Finset.subset_univ (H ∪ R))
    rw [Finset.card_union_of_disjoint hdisjoint, hR] at hh
    simpa only [Finset.card_univ, ZMod.card, two_mul] using hh
  obtain ⟨ha, hb⟩ := interval_card_le_residue_support A N s hs hA
  change A.card ≤ (N / s + 1) * H.card at ha
  change A.card ≤ N / s * H.card + N % s at hb
  have hq : 1 ≤ N / s := (Nat.one_le_div_iff hs).mpr hsN
  have hdecomp := Nat.mod_add_div N s
  have hmul := Nat.mul_le_mul_left (N / s) hhalf
  have hqs := Nat.mul_le_mul_right s hq
  by_cases hr : 2 * (N % s) ≤ s
  · nlinarith
  · have hmul' := Nat.mul_le_mul_left (N / s + 1) hhalf
    nlinarith

/-- More than two thirds of a positive initial interval contains two elements
whose sum is divisible by any prescribed modulus not exceeding the endpoint.
The two elements are allowed to agree, as rational-supply lists allow repeats. -/
theorem exists_pair_dvd_sum_of_two_thirds
    (G : Finset ℕ) (N s : ℕ) (hs : 0 < s) (hsN : s ≤ N)
    (hG : G ⊆ Finset.Icc 1 N) (hcard : 2 * N < 3 * G.card) :
    ∃ u ∈ G, ∃ v ∈ G, s ∣ u + v := by
  classical
  let : NeZero s := ⟨hs.ne'⟩
  let A := G.image (fun n => n - 1)
  have hA : A ⊆ Finset.range N := by
    intro a ha
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hu1, huN⟩ := Finset.mem_Icc.mp (hG hu)
    exact Finset.mem_range.mpr (by omega)
  have hAc : A.card = G.card := by
    apply Finset.card_image_of_injOn
    intro u hu v hv huv
    change u - 1 = v - 1 at huv
    have hu1 := (Finset.mem_Icc.mp (hG hu)).1
    have hv1 := (Finset.mem_Icc.mp (hG hv)).1
    omega
  by_contra hn
  have hno : ∀ a ∈ A, ∀ b ∈ A,
      (a : ZMod s) + (b : ZMod s) ≠ (-2 : ZMod s) := by
    intro a ha b hb hab
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
    have hu1 := (Finset.mem_Icc.mp (hG hu)).1
    have hv1 := (Finset.mem_Icc.mp (hG hv)).1
    apply hn
    refine ⟨u, hu, v, hv, ?_⟩
    apply (ZMod.natCast_eq_zero_iff (u + v) s).mp
    rw [Nat.cast_add]
    rw [Nat.cast_sub hu1, Nat.cast_sub hv1, Nat.cast_one] at hab
    linear_combination hab
  have hbound := interval_card_le_two_thirds_of_no_modular_pair A N s hs hsN
    hA (-2) hno
  rw [hAc] at hbound
  omega

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_DenseModularSupply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

namespace Problem337

/-- A supply on more than two thirds of an initial interval gives supply for
every smaller positive integer at twice the original budget. The multiplier
is removed by changing only the rational summands' denominators. -/
theorem rational_divisor_supply_of_two_thirds
    (K B N : ℕ) (G : Finset ℕ) (hG : G ⊆ Finset.Icc 1 N)
    (hcard : 2 * N < 3 * G.card)
    (hgood : ∀ u ∈ G, HasRationalDivisorSum K (u : ℚ) B) :
    ∀ s : ℕ, 1 ≤ s → s ≤ N → HasRationalDivisorSum K (s : ℚ) (2 * B) := by
  intro s hs hsN
  obtain ⟨u, hu, v, hv, hdiv⟩ := exists_pair_dvd_sum_of_two_thirds G N s hs hsN hG hcard
  have hu1 := (Finset.mem_Icc.mp (hG hu)).1
  obtain ⟨d, hd⟩ := hdiv
  have hdpos : 0 < d := by
    by_contra h
    have hd0 : d = 0 := by omega
    rw [hd0, Nat.mul_zero] at hd
    omega
  have hrep : HasRationalDivisorSum K ((d * s : ℕ) : ℚ) (B + B) := by
    rw [Nat.mul_comm d s, ← hd, Nat.cast_add]
    exact (hgood u hu).add (hgood v hv)
  simpa only [two_mul] using hrep.of_nat_multiple hdpos

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_CubeFreeRationalSupply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

namespace Problem337

/-- Removing the full common prime-power part leaves a coprime quotient.
Only primes of the supply need the displayed multiplicity bound. -/
theorem coprime_div_gcd_pow_of_prime_power_free {q P r : ℕ}
    (hq : 0 < q) (hP : 0 < P)
    (hfree : ∀ p : ℕ, p.Prime → p ∣ P → ¬p ^ (r + 1) ∣ q) :
    Nat.Coprime (q / Nat.gcd q (P ^ r)) P := by
  have hg := Nat.gcd_dvd_left q (P ^ r)
  have hgpos : 0 < Nat.gcd q (P ^ r) := Nat.pos_of_dvd_of_pos hg hq
  have hquot : q / Nat.gcd q (P ^ r) ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd hq hg) hgpos).ne'
  apply Nat.coprime_of_dvd
  intro p hp hpd hpP
  have hsmall : q.factorization p ≤ r := by
    have hh := hfree p hp hpP
    rw [hp.pow_dvd_iff_le_factorization hq.ne'] at hh
    omega
  have hPlarge : 1 ≤ P.factorization p :=
    (hp.dvd_iff_one_le_factorization hP.ne').mp hpP
  have hle : q.factorization p ≤ r * P.factorization p :=
    hsmall.trans (by nlinarith)
  have hpos := hp.factorization_pos_of_dvd hquot hpd
  rw [Nat.factorization_div hg,
    Nat.factorization_gcd hq.ne' (pow_ne_zero _ hP.ne'), Nat.factorization_pow] at hpos
  simp [Finsupp.coe_tsub, Finsupp.inf_apply, Finsupp.smul_apply,
    smul_eq_mul, min_eq_left hle] at hpos

/-- A representation of the coprime quotient, whose numerators divide `P²`,
rescales to the original integer with numerators dividing `P⁴`, and no increase
in the number of summands. -/
theorem rational_divisor_sum_of_gcd_square_quotient {q P B : ℕ}
    (hq : 0 < q)
    (hrep : HasRationalDivisorSum (P ^ 2) ((q / Nat.gcd q (P ^ 2) : ℕ) : ℚ) B) :
    HasRationalDivisorSum (P ^ 4) (q : ℚ) B := by
  have hgq := Nat.gcd_dvd_left q (P ^ 2)
  have hgpos : 0 < Nat.gcd q (P ^ 2) := Nat.pos_of_dvd_of_pos hgq hq
  have hg := hasRationalDivisorSum_of_dvd hgpos (Nat.gcd_dvd_right q (P ^ 2))
  have h := hg.mul hrep
  have heq : P ^ 2 * P ^ 2 = P ^ 4 := by ring
  have hqeq : Nat.gcd q (P ^ 2) * (q / Nat.gcd q (P ^ 2)) = q :=
    Nat.mul_div_cancel' hgq
  simpa only [heq, one_mul, ← Nat.cast_mul, hqeq] using h

/-- Supplying the coprime divisors is enough to supply a cube-free integer.
The coprime-divisor premise includes `1`, so no exceptional zero-frequency
or unit-modulus case is being suppressed. -/
theorem rational_divisor_sum_of_cube_free_divisor_supply {q P B : ℕ}
    (hq : 0 < q) (hP : 0 < P)
    (hfree : ∀ p : ℕ, p.Prime → ¬p ^ 3 ∣ q)
    (hrep : ∀ d : ℕ, 0 < d → d ∣ q → Nat.Coprime d P →
      HasRationalDivisorSum (P ^ 2) (d : ℚ) B) :
    HasRationalDivisorSum (P ^ 4) (q : ℚ) B := by
  apply rational_divisor_sum_of_gcd_square_quotient hq
  have hg := Nat.gcd_dvd_left q (P ^ 2)
  apply hrep
  · exact Nat.div_pos (Nat.le_of_dvd hq hg) (Nat.pos_of_dvd_of_pos hg hq)
  · exact Nat.div_dvd_of_dvd hg
  · exact coprime_div_gcd_pow_of_prime_power_free hq hP
      (fun p hp _ => by simpa using hfree p hp)

/-- Finite assembly for the canonical marked-grouping interface. The unknown
arithmetic inputs remain explicit: density of good cube-free moduli, and
bounded rational-divisor supply for their coprime divisors. -/
theorem marked_rational_supply_of_cube_free_set
    (m P B : ℕ) (G : Finset ℕ) (hP : 0 < P)
    (hG : G ⊆ Finset.Icc 1 (m ^ 4))
    (hcard : 2 * m ^ 4 < 3 * G.card)
    (hfree : ∀ q ∈ G, ∀ p : ℕ, p.Prime → ¬p ^ 3 ∣ q)
    (hrep : ∀ q ∈ G, ∀ d : ℕ, 0 < d → d ∣ q → Nat.Coprime d P →
      HasRationalDivisorSum (P ^ 2) (d : ℚ) B) :
    HasRationalDivisorSupply m (P ^ 4) (2 * B) := by
  apply rational_divisor_supply_bridge
  apply rational_divisor_supply_of_two_thirds (P ^ 4) B (m ^ 4) G hG hcard
  intro q hq
  exact rational_divisor_sum_of_cube_free_divisor_supply
    (Finset.mem_Icc.mp (hG hq)).1 hP (hfree q hq) (hrep q hq)

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_CubeFreeSupplyFromExceptions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

namespace Problem337

/-- Exact finite assembly of the cube-free alternative. The density premise
counts the specified exceptional moduli, not an abstract set standing in for
the desired result. The second premise is the all-divisor Fourier supply API.
Both arithmetic premises remain explicit and must be proved separately. -/
theorem marked_rational_supply_of_cube_free_bad_divisors
    (m P B : ℕ) (Q : ℕ → Prop) (hP : 0 < P)
    (hbad : ((badCoprimeDivisorMultiples (m ^ 4) P Q).card : ℝ) <
      (m ^ 4 : ℕ) / 12)
    (hrep : ∀ d : ℕ, 0 < d → d ≤ m ^ 4 → Nat.Coprime d P →
      (∀ r : ℕ, 2 ≤ r → r ∣ d → Q r) →
      HasRationalDivisorSum (P ^ 2) (d : ℚ) B) :
    HasRationalDivisorSupply m (P ^ 4) (2 * B) := by
  classical
  let E := badCoprimeDivisorMultiples (m ^ 4) P Q
  let G := CubeFreeDensity.good (m ^ 4) \ E
  have hG : G ⊆ Finset.Icc 1 (m ^ 4) := by
    intro q hq
    have h := CubeFreeDensity.mem_good.mp (Finset.mem_sdiff.mp hq).1
    exact Finset.mem_Icc.mpr ⟨h.1, h.2.1⟩
  apply marked_rational_supply_of_cube_free_set m P B G hP hG
  · have hh := CubeFreeDensity.card_good_sdiff_gt_two_thirds (m ^ 4) E hbad
    have hh' : (2 : ℝ) * (m ^ 4 : ℕ) < 3 * (G.card : ℝ) := by
      change (2 : ℝ) * (m ^ 4 : ℕ) / 3 < (G.card : ℝ) at hh
      linarith
    exact_mod_cast hh'
  · intro q hq p hp
    exact CubeFreeDensity.prime_cube_not_dvd_of_mem_good (Finset.mem_sdiff.mp hq).1 hp
  · intro q hq d hd hdq hdP
    have hqbounds := Finset.mem_Icc.mp (hG hq)
    apply hrep d hd ((Nat.le_of_dvd hqbounds.1 hdq).trans hqbounds.2) hdP
    intro r hr hrd
    by_contra hnot
    have hrcop : Nat.Coprime r P := hdP.of_dvd_left hrd
    exact (Finset.mem_sdiff.mp hq).2
      (mem_badCoprimeDivisorMultiples.mpr
        ⟨hqbounds.1, hqbounds.2, r, hr, hrd.trans hdq, hrcop, hnot⟩)

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_EightProductConductor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-!
# Eight products from a subuniform conductor collision bound

A collision exponent of `7/8`, unlike exact equidistribution, is compatible
with the rough-modulus exceptional-set construction. Eight products then
produce a cubic conductor loss, controlled by the existing uniform `3/4`
conductor budget. The index type retains all sample multiplicities.
-/

noncomputable section
open scoped BigOperators

namespace Problem337.CompositeSpectral

/-- A pointwise eighth-moment bound suffices for eight indexed products with
any prescribed sum. This formulation avoids fractional powers in consumers. -/
theorem eight_products_of_conductor_power_bound
    {q : ℕ} [NeZero q] {ι : Type*} [Fintype ι] [Nonempty ι]
    (v : ι → ZMod q)
    (hchar : ∀ r : ZMod q, r ≠ 0 →
      ‖∑ i : ι, ∑ j : ι, ZMod.stdAddChar (v i * v j * r)‖ ^ 8 ≤
        (Fintype.card ι : ℝ) ^ 16 / (addOrderOf r : ℝ) ^ 3)
    (target : ZMod q) :
    ∃ a b : Fin 8 → ι, ∑ i, v (a i) * v (b i) = target := by
  classical
  let f : ι × ι → ZMod q := fun ij => v ij.1 * v ij.2
  let B : ZMod q → ℝ := fun r => ‖∑ ij : ι × ι, ZMod.stdAddChar (f ij * r)‖
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hbudget : (∑ r ∈ (Finset.univ : Finset (ZMod q)).erase 0, B r ^ 8) <
      (Fintype.card (ι × ι) : ℝ) ^ 8 := by
    calc
      _ ≤ ∑ r ∈ (Finset.univ : Finset (ZMod q)).erase 0,
          (Fintype.card ι : ℝ) ^ 16 / (addOrderOf r : ℝ) ^ 3 := by
        apply Finset.sum_le_sum
        intro r hr
        simpa only [B, f, Fintype.sum_prod_type] using hchar r (Finset.mem_erase.mp hr).1
      _ = (Fintype.card ι : ℝ) ^ 16 *
          ∑ r ∈ (Finset.univ : Finset (ZMod q)).erase 0,
            (1 : ℝ) / (addOrderOf r : ℝ) ^ 3 := by
        simp only [Finset.mul_sum, mul_one_div]
      _ ≤ (Fintype.card ι : ℝ) ^ 16 * (3 / 4) :=
        mul_le_mul_of_nonneg_left (conductor_cube_sum_le q) (by positivity)
      _ < (Fintype.card ι : ℝ) ^ 16 := by nlinarith [pow_pos hcard 16]
      _ = _ := by simp only [Fintype.card_prod, Nat.cast_mul]; ring
  obtain ⟨w, hw⟩ := exists_sum_of_character_bounds f 8 target B
    (fun _ _ => le_rfl) hbudget
  exact ⟨fun i => (w i).1, fun i => (w i).2, hw⟩

lemma remainderCollisionCount_eq_cast {ι : Type*} [Fintype ι]
    (t : ι → ℕ) (d : ℕ) [NeZero d] :
    remainderCollisionCount t d =
      indexedResidueCollisionCount (fun i => (t i : ZMod d)) := by
  classical
  simp only [remainderCollisionCount, indexedResidueCollisionCount,
    ZMod.natCast_eq_natCast_iff']

/-- Conductor-sensitive bilinear estimate in the natural-remainder convention. -/
lemma bilinear_le_sqrt_order_mul_collisions
    {q : ℕ} [NeZero q] {ι : Type*} [Fintype ι]
    (t : ι → ℕ) (r : ZMod q) :
    ‖∑ i : ι, ∑ j : ι,
      ZMod.stdAddChar ((t i : ZMod q) * (t j : ZMod q) * r)‖ ≤
        Real.sqrt (addOrderOf r : ℝ) * remainderCollisionCount t (addOrderOf r) := by
  have ho := order_eq_reduced_modulus r
  have hdpos : 0 < q / r.val.gcd q := by rw [← ho]; exact addOrderOf_pos r
  let : NeZero (q / r.val.gcd q) := ⟨Nat.ne_of_gt hdpos⟩
  have hb := reduced_indexed_bilinear_bound t r.val q (NeZero.pos q)
  rw [← remainderCollisionCount_eq_cast, ← ho] at hb
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Nat.cast_mul, ZMod.natCast_zmod_val]
  congr 1
  ring

/-- A purely polynomial collision hypothesis at every nontrivial divisor of
`q` gives eight products with every prescribed residue. The hypothesis is the
power-eight form of collision density at most `d^(-7/8)`. -/
theorem eight_products_of_collision_power_bound
    {q : ℕ} [NeZero q] {ι : Type*} [Fintype ι] [Nonempty ι]
    (t : ι → ℕ)
    (hcollision : ∀ d : ℕ, 2 ≤ d → d ∣ q →
      (remainderCollisionCount t d : ℝ) ^ 8 * (d : ℝ) ^ 7 ≤
        (Fintype.card ι : ℝ) ^ 16)
    (target : ZMod q) :
    ∃ a b : Fin 8 → ι,
      ∑ i, (t (a i) : ZMod q) * (t (b i) : ZMod q) = target := by
  apply eight_products_of_conductor_power_bound (fun i => (t i : ZMod q)) _ target
  intro r hr
  have hdpos : 0 < addOrderOf r := addOrderOf_pos r
  have hd2 : 2 ≤ addOrderOf r := by
    have hne : addOrderOf r ≠ 1 := by
      intro h
      exact hr (AddMonoid.addOrderOf_eq_one_iff.mp h)
    omega
  have hdq : addOrderOf r ∣ q := by simpa using addOrderOf_dvd_card (x := r)
  have hbound := hcollision (addOrderOf r) hd2 hdq
  have hdR : (0 : ℝ) < addOrderOf r := by exact_mod_cast hdpos
  have hsqrt : Real.sqrt (addOrderOf r : ℝ) ^ 8 = (addOrderOf r : ℝ) ^ 4 := by
    calc
      _ = (Real.sqrt (addOrderOf r : ℝ) ^ 2) ^ 4 := by ring
      _ = _ := by rw [Real.sq_sqrt hdR.le]
  calc
    _ ≤ (Real.sqrt (addOrderOf r : ℝ) *
        remainderCollisionCount t (addOrderOf r)) ^ 8 :=
      pow_le_pow_left₀ (norm_nonneg _) (bilinear_le_sqrt_order_mul_collisions t r) 8
    _ = ((remainderCollisionCount t (addOrderOf r) : ℝ) ^ 8 *
        (addOrderOf r : ℝ) ^ 7) / (addOrderOf r : ℝ) ^ 3 := by
      rw [mul_pow, hsqrt]
      field_simp
    _ ≤ _ := div_le_div_of_nonneg_right hbound (by positivity)

/-- The fractional-power form directly matches a collision exceptional-set
threshold. The estimate is required only at divisors of the final modulus. -/
theorem eight_products_of_collision_rpow_bound
    {q : ℕ} [NeZero q] {ι : Type*} [Fintype ι] [Nonempty ι]
    (t : ι → ℕ)
    (hcollision : ∀ d : ℕ, 2 ≤ d → d ∣ q →
      (remainderCollisionCount t d : ℝ) ≤
        (Fintype.card ι : ℝ) ^ 2 / (d : ℝ) ^ ((7 : ℝ) / 8))
    (target : ZMod q) :
    ∃ a b : Fin 8 → ι,
      ∑ i, (t (a i) : ZMod q) * (t (b i) : ZMod q) = target := by
  apply eight_products_of_collision_power_bound t _ target
  intro d hd hdq
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg (remainderCollisionCount t d))
    (hcollision d hd hdq) 8
  have hexp : ((d : ℝ) ^ ((7 : ℝ) / 8)) ^ 8 = (d : ℝ) ^ 7 := by
    rw [← Real.rpow_mul_natCast hdR.le]
    norm_num
  calc
    _ ≤ ((Fintype.card ι : ℝ) ^ 2 / (d : ℝ) ^ ((7 : ℝ) / 8)) ^ 8 *
        (d : ℝ) ^ 7 := mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = _ := by
      rw [div_pow, hexp]
      field_simp

end Problem337.CompositeSpectral

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_RationalDivisorLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- An integral positive sum divisible by `p` gives a common-denominator
representation of `p`; products of divisors of `P` divide `P²`. -/
theorem rational_divisor_sum_of_divisible {k P p : ℕ} (hk : 0 < k)
    (hp : 0 < p) (a b : Fin k → ℕ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (had : ∀ i, a i ∣ P) (hbd : ∀ i, b i ∣ P)
    (hdiv : p ∣ ∑ i, a i * b i) :
    ∃ t : ℕ, 0 < t ∧ (∀ i, 0 < a i * b i ∧ a i * b i ∣ P ^ 2) ∧
      (p : ℚ) = ∑ i, ((a i * b i : ℕ) : ℚ) / t := by
  have hspos : 0 < ∑ i, a i * b i := by
    exact Finset.sum_pos' (fun i _ => Nat.zero_le _) ⟨⟨0, hk⟩,
      Finset.mem_univ _, Nat.mul_pos (ha _) (hb _)⟩
  obtain ⟨t, hsum⟩ := hdiv
  have ht : 0 < t := by
    rw [hsum] at hspos
    by_contra h
    have ht0 : t = 0 := by omega
    simp [ht0] at hspos
  refine ⟨t, ht, ?_, ?_⟩
  · intro i
    exact ⟨Nat.mul_pos (ha i) (hb i), by
      simpa only [pow_two] using Nat.mul_dvd_mul (had i) (hbd i)⟩
  · rw [← Finset.sum_div, ← Nat.cast_sum, hsum, Nat.cast_mul]
    field_simp

/-- The preceding lifting lemma can take a modular zero-sum directly. -/
theorem rational_divisor_sum_of_zmod_zero {k P p : ℕ} (hk : 0 < k)
    (hp : 0 < p) (a b : Fin k → ℕ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (had : ∀ i, a i ∣ P) (hbd : ∀ i, b i ∣ P)
    (hzero : (∑ i, (a i : ZMod p) * (b i : ZMod p)) = 0) :
    ∃ t : ℕ, 0 < t ∧ (∀ i, 0 < a i * b i ∧ a i * b i ∣ P ^ 2) ∧
      (p : ℚ) = ∑ i, ((a i * b i : ℕ) : ℚ) / t := by
  apply rational_divisor_sum_of_divisible hk hp a b ha hb had hbd
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  simpa only [Nat.cast_sum, Nat.cast_mul] using hzero

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_EightProductRationalSupply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- A conductor collision bound for an indexed family of positive divisors
gives an eight-term rational supply of the modulus. Repeated samples are
allowed; no primality assumption is made on the modulus. -/
theorem rational_divisor_sum_eight_of_collision
    {q P : ℕ} [NeZero q] {ι : Type*} [Fintype ι] [Nonempty ι]
    (a : ι → ℕ) (ha : ∀ i, 0 < a i) (had : ∀ i, a i ∣ P)
    (hcollision : ∀ d : ℕ, 2 ≤ d → d ∣ q →
      (CompositeSpectral.remainderCollisionCount a d : ℝ) ≤
        (Fintype.card ι : ℝ) ^ 2 / (d : ℝ) ^ ((7 : ℝ) / 8)) :
    HasRationalDivisorSum (P ^ 2) (q : ℚ) 8 := by
  obtain ⟨u, v, hu⟩ :=
    CompositeSpectral.eight_products_of_collision_rpow_bound a hcollision (0 : ZMod q)
  obtain ⟨t, ht, he, hsum⟩ := rational_divisor_sum_of_zmod_zero
    (by norm_num : 0 < 8) (NeZero.pos q)
    (fun i => a (u i)) (fun i => a (v i))
    (fun i => ha (u i)) (fun i => ha (v i))
    (fun i => had (u i)) (fun i => had (v i)) hu
  exact hasRationalDivisorSum_of_common_denominator
    (fun i => a (u i) * a (v i)) ht he hsum.symm

/-- The exact divisor-list specialization of the indexed collision criterion.
The collision count retains each natural divisor once, even if residues
coincide. Nonzero `P` supplies the index `1`, including the boundary `P = 1`. -/
theorem rational_divisor_sum_eight_of_divisor_collision
    {q P : ℕ} [NeZero q] (hP : P ≠ 0)
    (hcollision : ∀ d : ℕ, 2 ≤ d → d ∣ q →
      (CompositeSpectral.remainderCollisionCount
        (fun i : P.divisors => (i : ℕ)) d : ℝ) ≤
        (P.divisors.card : ℝ) ^ 2 / (d : ℝ) ^ ((7 : ℝ) / 8)) :
    HasRationalDivisorSum (P ^ 2) (q : ℚ) 8 := by
  classical
  let : Nonempty P.divisors := ⟨⟨1, Nat.mem_divisors.mpr ⟨one_dvd P, hP⟩⟩⟩
  apply rational_divisor_sum_eight_of_collision (fun i : P.divisors => (i : ℕ))
    (fun i => Nat.pos_of_mem_divisors i.property)
    (fun i => Nat.dvd_of_mem_divisors i.property)
  simpa only [Fintype.card_coe] using hcollision

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_CompositeSupplyFinal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open Filter

namespace Problem337.CompositeSupply

/-- Absence of global bad conductors gives the actual eight-term rational
representation in the ambient divisor pool. -/
lemma rational_divisor_sum_of_no_bad_divisor {Y q : ℕ}
    (hq : 0 < q) (hqY : q ≤ Y) (hc : q.Coprime (base Y))
    (hgood : ∀ d : ℕ, 2 ≤ d → d ∣ q → ¬ BadModulus d) :
    HasRationalDivisorSum (base Y ^ 2) (q : ℚ) 8 := by
  let : NeZero q := ⟨hq.ne'⟩
  apply rational_divisor_sum_eight_of_divisor_collision (base_pos Y).ne'
  intro d hd hdq
  let : NeZero d := ⟨by omega⟩
  rw [CompositeSpectral.remainderCollisionCount_eq_cast, indexed_divisor_collision_eq]
  exact ambient_collisions_le_of_not_bad hq hqY hdq hc.symm (hgood d hd hdq) hd

/-- The entire remaining arithmetic input is the density bound for the
specified global bad-divisor multiples. -/
theorem eventually_supply_of_bad_multiples
    (hbad : ∀ᶠ Y : ℕ in atTop,
      ((badCoprimeDivisorMultiples Y (base Y) (fun d => ¬ BadModulus d)).card : ℝ)
        < (Y : ℝ) / 12) :
    ∀ᶠ m : ℕ in atTop, HasRationalDivisorSupply m (multiplier m) 16 := by
  have hpow : Tendsto (fun m : ℕ => m ^ 4) atTop atTop :=
    tendsto_pow_atTop (by norm_num : 4 ≠ 0)
  filter_upwards [hpow.eventually hbad] with m hm
  exact marked_rational_supply_of_cube_free_bad_divisors m (base (m ^ 4)) 8
    (fun d => ¬ BadModulus d) (base_pos _) hm
    (fun q hq hqY hc hgood => rational_divisor_sum_of_no_bad_divisor hq hqY hc hgood)

/-- The finite exception set used by cube-free density is contained in the
single global logarithmic-tail exception set. -/
lemma badCoprimeDivisorMultiples_subset_badMultiples (Y : ℕ) :
    badCoprimeDivisorMultiples Y (base Y) (fun d => ¬ BadModulus d) ⊆
      badMultiples Y := by
  intro n hn
  obtain ⟨hn1, hnY, d, hd, hdn, hc, hbad⟩ :=
    mem_badCoprimeDivisorMultiples.mp hn
  by_contra hne
  exact hbad (not_bad_of_not_mem_badMultiples hn1 hnY hdn hc.symm hne (dvd_refl d) hd)

/-- Vanishing density of the actual global exceptional set suffices, with
strict margin between one twenty-fourth and one twelfth. -/
theorem eventually_supply_of_badMultiples_small
    (hsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ Y : ℕ in atTop,
      ((badMultiples Y).card : ℝ) ≤ ε * Y) :
    ∀ᶠ m : ℕ in atTop, HasRationalDivisorSupply m (multiplier m) 16 := by
  apply eventually_supply_of_bad_multiples
  filter_upwards [hsmall (1 / 24) (by norm_num), eventually_ge_atTop (1 : ℕ)]
    with Y hY hYpos
  have hcard :
      ((badCoprimeDivisorMultiples Y (base Y) (fun d => ¬ BadModulus d)).card : ℝ) ≤
        (badMultiples Y).card := by
    exact_mod_cast Finset.card_le_card (badCoprimeDivisorMultiples_subset_badMultiples Y)
  have hpos : (0 : ℝ) < Y := by exact_mod_cast hYpos
  linarith

/-- Unconditional sixteen-term supply for the explicit fourth-power prefix
multiplier. Every arithmetic density and energy obligation is discharged. -/
theorem eventually_hasRationalDivisorSupply :
    ∀ᶠ m : ℕ in atTop, HasRationalDivisorSupply m (multiplier m) 16 :=
  eventually_supply_of_badMultiples_small eventually_badMultiples_card_le

/-- The exact marked Egyptian-fraction theorem, proved by the composite
cube-free route without any prime-triple distribution premise. -/
theorem quantitative_marked_length :
    ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, 2 ≤ M ∧
      ∀ m : ℕ, M ≤ m → ∃ k : ℕ, ∃ n : Fin k → ℕ,
        IsOneExpansion n ∧ (∃ i, n i = m) ∧
        (k : ℝ) ≤ (257 / Real.log 2 + ε) * Real.log (Real.log (m : ℝ)) :=
  quantitative_marked_length_of_supply eventually_hasRationalDivisorSupply

end Problem337.CompositeSupply

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

open scoped BigOperators

namespace Problem337

theorem quantitative_marked_length_oai :
    ∀ ε : ℝ, 0 < ε → ∃ mε : ℕ, 2 ≤ mε ∧
  ∀ m : ℕ, mε ≤ m →
    ∃ k : ℕ, ∃ n : Fin k → ℕ,
      IsOneExpansion n ∧
      (∃ i : Fin k, n i = m) ∧
      (k : ℝ) ≤ (257 / Real.log 2 + ε) * Real.log (Real.log (m : ℝ)) := by
  exact CompositeSupply.quantitative_marked_length

end Problem337

end

end OAI
end

theorem solution : type_of% @OAI.Problem337.quantitative_marked_length_oai := @OAI.Problem337.quantitative_marked_length_oai
