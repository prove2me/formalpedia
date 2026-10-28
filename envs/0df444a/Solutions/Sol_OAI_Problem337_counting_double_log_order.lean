-- Prove2me | solution 1 for OAI.Problem337.counting_double_log_order
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T10:03:48.539269+00:00
-- url     : https://prove2.me/submissions/e7eb19c9-a6dc-4c90-a779-bd3662e34154

import Mathlib
import Definitions.Def_EgyptianFractions
import Definitions.Def_OAIQ8EF000
import Theorems.Thm_OAI_Problem337_main_double_log_order

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_CountingPadding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.CountingPadding

lemma strictMono_snoc {α : Type*} [LinearOrder α] {k : ℕ}
    (f : Fin k → α) (a : α) (hf : StrictMono f) (ha : ∀ i, f i < a) :
    StrictMono (Fin.snoc f a) := by
  intro i j hij
  cases i using Fin.lastCases with
  | last => exact False.elim (not_lt_of_ge (Fin.le_last j) hij)
  | cast i =>
    cases j using Fin.lastCases with
    | last => simpa using ha i
    | cast j => simpa using hf (show i < j from hij)

lemma pad_strictMono {k : ℕ} (n : Fin (k + 1) → ℕ)
    (hn : StrictMono n) (hmax : 1 < n (Fin.last k)) : StrictMono (pad n) := by
  apply strictMono_snoc
  · apply strictMono_snoc
    · intro i j hij
      exact hn (show i.castSucc < j.castSucc from hij)
    · intro i
      exact lt_trans (hn i.castSucc_lt_last) (Nat.lt_succ_self _)
  · intro i
    cases i using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last]
      nlinarith
    | cast i =>
      simp only [Fin.snoc_castSucc]
      have hi := hn i.castSucc_lt_last
      nlinarith

lemma pad_positive {k : ℕ} (n : Fin (k + 1) → ℕ)
    (hn : ∀ i, 1 ≤ n i) : ∀ i, 1 ≤ pad n i := by
  intro i
  cases i using Fin.lastCases with
  | last =>
    simp only [pad, Fin.snoc_last]
    have h := hn (Fin.last k)
    nlinarith
  | cast i =>
    cases i using Fin.lastCases with
    | last => simp [pad]
    | cast i => simpa [pad] using hn i.castSucc

lemma pad_sum {k : ℕ} (n : Fin (k + 1) → ℕ)
    (hmax : 0 < n (Fin.last k)) :
    (∑ i : Fin (k + 2), (1 : ℚ) / (pad n i : ℚ)) =
      ∑ i : Fin (k + 1), (1 : ℚ) / (n i : ℚ) := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp only [pad, Fin.snoc_castSucc, Fin.snoc_last, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one]
  have hn : (n (Fin.last k) : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hmax)
  have hn1 : (n (Fin.last k) : ℚ) + 1 ≠ 0 := by positivity
  field_simp
  ring

lemma pad_injective {k : ℕ} : Function.Injective (@pad k) := by
  intro n m h
  have hparts := Fin.snoc_injective2 h
  have hparts' := Fin.snoc_injective2 hparts.1
  have hlast : n (Fin.last k) = m (Fin.last k) := Nat.add_right_cancel hparts'.2
  funext i
  cases i using Fin.lastCases with
  | last => exact hlast
  | cast i => exact congr_fun hparts'.1 i

lemma last_gt_one {k : ℕ} (hk : 1 ≤ k) (n : Fin (k + 1) → ℕ)
    (hn : IsOneExpansion n) : 1 < n (Fin.last k) := by
  let i : Fin k := ⟨0, hk⟩
  exact lt_of_le_of_lt (hn.1 i.castSucc) (hn.2.1 i.castSucc_lt_last)

lemma pad_isOneExpansion {k : ℕ} (hk : 1 ≤ k) (n : Fin (k + 1) → ℕ)
    (hn : IsOneExpansion n) : IsOneExpansion (pad n) := by
  refine ⟨pad_positive n hn.1, pad_strictMono n hn.2.1 (last_gt_one hk n hn), ?_⟩
  rw [pad_sum n (lt_of_lt_of_le Nat.zero_lt_one (hn.1 _))]
  exact hn.2.2

lemma F_succ_le {k : ℕ} (hk : 1 ≤ k) (hfinite : Set.Finite (OneExpansions (k + 2))) :
    F (k + 1) ≤ F (k + 2) := by
  refine Set.ncard_le_ncard_of_injOn (@pad k) ?_ pad_injective.injOn hfinite
  intro n hn
  exact pad_isOneExpansion hk n hn

lemma F_le_succ {k : ℕ} (hk : 2 ≤ k) (hfinite : Set.Finite (OneExpansions (k + 1))) :
    F k ≤ F (k + 1) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  exact F_succ_le (by omega) hfinite

lemma F_le_of_le (hfinite : ∀ k, Set.Finite (OneExpansions k))
    {a b : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) : F a ≤ F b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih => exact le_trans ih (F_le_succ (by omega) (hfinite _))

end Problem337.CountingPadding

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_CountingTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open Filter
open scoped Topology
namespace Problem337
/-- Taking two logarithms of a natural doubly exponential lower bound. -/
theorem loglog_lower_of_two_pow_two_pow {t N : ℕ} (hN : 2 ^ (2 ^ t) ≤ N) :
    (t : ℝ) * Real.log 2 + Real.log (Real.log 2) ≤ Real.log (Real.log (N : ℝ)) := by
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hcast : (2 : ℝ) ^ (2 ^ t) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlog := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ (2 ^ t)) hcast
  rw [Real.log_pow] at hlog
  have hpre : 0 < ((2 ^ t : ℕ) : ℝ) * Real.log 2 := mul_pos (by positivity) hl2
  have hll := Real.log_le_log hpre hlog
  rw [Real.log_mul (by positivity : ((2 ^ t : ℕ) : ℝ) ≠ 0) (ne_of_gt hl2)] at hll
  simpa only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] using hll

/-- A supply of exponential counts at logarithmically short lengths transfers
by padding monotonicity to a linear double-log lower bound at every long length. -/
theorem counting_lower_transfer (f : ℕ → ℕ) {B : ℝ} (hB : 0 < B)
    (hmono : ∀ i j : ℕ, 2 ≤ i → i ≤ j → f i ≤ f j)
    (hsupply : ∀ᶠ r : ℕ in atTop, ∃ ell : ℕ, 2 ≤ ell ∧
      (ell : ℝ) ≤ B * Real.log (r : ℝ) ∧ 2 ^ (r - 1) ≤ f ell) :
    ∀ᶠ k : ℕ in atTop,
      (1 / (2 * B)) * (k : ℝ) ≤ Real.log (Real.log (f k : ℝ)) := by
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let A : ℝ := B * Real.log 2
  have hA : 0 < A := mul_pos hB hl2
  let C : ℝ := 2 * Real.log 2 + |Real.log (Real.log 2)|
  have hC : 0 ≤ C := by dsimp [C]; positivity
  obtain ⟨r0, hr0⟩ := eventually_atTop.mp hsupply
  let t : ℕ → ℕ := fun k => ⌊(k : ℝ) / A⌋₊
  have htend : Tendsto t atTop atTop :=
    tendsto_nat_floor_atTop.comp
      (Tendsto.atTop_div_const hA (tendsto_natCast_atTop_atTop (R := ℝ)))
  have htevent : ∀ᶠ k : ℕ in atTop, r0 + 2 ≤ t k :=
    htend.eventually (eventually_ge_atTop (r0 + 2))
  have hkevent : ∀ᶠ k : ℕ in atTop, 2 * B * C ≤ (k : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop (2 * B * C))
  filter_upwards [htevent, hkevent] with k htk hklarge
  let r : ℕ := 2 ^ t k
  have hr : r0 ≤ r := by
    have hpow : t k < 2 ^ t k := Nat.lt_two_pow_self
    dsimp [r]
    omega
  obtain ⟨ell, hell2, helllen, hellcount⟩ := hr0 r hr
  have htupper : (t k : ℝ) ≤ (k : ℝ) / A := Nat.floor_le (by positivity)
  have htupper' : (t k : ℝ) * A ≤ (k : ℝ) := (le_div_iff₀ hA).mp htupper
  have hellk : ell ≤ k := by
    have hlen : (ell : ℝ) ≤ B * ((t k : ℝ) * Real.log 2) := by
      simpa only [r, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] using helllen
    have : (ell : ℝ) ≤ (k : ℝ) := by dsimp [A] at htupper'; nlinarith
    exact_mod_cast this
  have heq : 2 ^ (t k - 1) + 2 ^ (t k - 1) = 2 ^ t k := by
    have h := Nat.pow_sub_mul_pow 2 (by omega : 1 ≤ t k)
    norm_num at h
    omega
  have hexp : 2 ^ (t k - 1) ≤ r - 1 := by
    have hp : 1 ≤ 2 ^ (t k - 1) := Nat.one_le_pow _ _ (by decide)
    dsimp [r]
    omega
  have hcount : 2 ^ (2 ^ (t k - 1)) ≤ f k :=
    (Nat.pow_le_pow_right (by decide : 0 < 2) hexp).trans
      (hellcount.trans (hmono ell k hell2 hellk))
  have hll := loglog_lower_of_two_pow_two_pow hcount
  rw [Nat.cast_sub (by omega : 1 ≤ t k), Nat.cast_one] at hll
  have htlower : (k : ℝ) / A < (t k : ℝ) + 1 := Nat.lt_floor_add_one _
  have htlower' : (k : ℝ) < ((t k : ℝ) + 1) * A := (div_lt_iff₀ hA).mp htlower
  have hquot : (k : ℝ) / B < ((t k : ℝ) + 1) * Real.log 2 := by
    apply (div_lt_iff₀ hB).2
    dsimp [A] at htlower'
    nlinarith
  have hlogabs : -|Real.log (Real.log 2)| ≤ Real.log (Real.log 2) := neg_abs_le _
  have hlower : (k : ℝ) / B - C ≤ Real.log (Real.log (f k : ℝ)) := by
    dsimp [C]
    linarith
  have hhalf : C ≤ (k : ℝ) / (2 * B) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * B)).2
    nlinarith [hklarge]
  have hdouble : (k : ℝ) / B = 2 * ((k : ℝ) / (2 * B)) := by
    field_simp
  have hresult : (k : ℝ) / (2 * B) ≤ Real.log (Real.log (f k : ℝ)) := by
    linarith
  simpa only [one_div, mul_comm, div_eq_mul_inv, one_mul] using hresult

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_CountingUpper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

namespace Problem337

/-- The elementary box estimate already gives a linear upper bound on the
    double logarithm, including the zero and singleton cases. -/
theorem counting_loglog_upper_of_box (f : ℕ → ℕ)
    (hbox : ∀ k : ℕ, f k ≤ k ^ (2 ^ k - 1))
    (k : ℕ) (hk : 2 ≤ k) :
    Real.log (Real.log (f k : ℝ)) ≤ 3 * (k : ℝ) := by
  by_cases hf : f k ≤ 1
  · have hcases : f k = 0 ∨ f k = 1 := by omega
    rcases hcases with hzero | hone
    · simp [hzero]
    · simp [hone]
  · have hf2 : 2 ≤ f k := by omega
    have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hfR : (2 : ℝ) ≤ (f k : ℝ) := by exact_mod_cast hf2
    have hlogf : 0 < Real.log (f k : ℝ) := Real.log_pos (by linarith)
    have hlogk : 0 < Real.log (k : ℝ) := Real.log_pos (by linarith)
    have hbox' : f k ≤ k ^ (2 ^ k) :=
      (hbox k).trans (pow_le_pow_right' (by omega : 1 ≤ k) (Nat.sub_le _ _))
    have hboxR : (f k : ℝ) ≤ (k : ℝ) ^ (2 ^ k) := by exact_mod_cast hbox'
    have hfirst : Real.log (f k : ℝ) ≤ (2 : ℝ) ^ k * Real.log (k : ℝ) := by
      have h := Real.log_le_log (by positivity : (0 : ℝ) < (f k : ℝ)) hboxR
      simpa only [Real.log_pow, Nat.cast_pow, Nat.cast_ofNat] using h
    have hsecond := Real.log_le_log hlogf hfirst
    rw [Real.log_mul (by positivity) (ne_of_gt hlogk), Real.log_pow] at hsecond
    have hlog2 : Real.log (2 : ℝ) ≤ 2 := Real.log_le_self (by norm_num)
    have hloglogk : Real.log (Real.log (k : ℝ)) ≤ (k : ℝ) :=
      (Real.log_le_self (le_of_lt hlogk)).trans (Real.log_le_self (by positivity))
    have hmul : (k : ℝ) * Real.log 2 ≤ (k : ℝ) * 2 :=
      mul_le_mul_of_nonneg_left hlog2 (by positivity)
    linarith

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_PrefixGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped BigOperators

namespace Problem337

/-- The reduced denominator of a finite rational sum divides the product of
its summands' reduced denominators. -/
theorem sum_den_dvd_prod {α : Type*} [DecidableEq α]
    (s : Finset α) (q : α → ℚ) :
    (∑ j ∈ s, q j).den ∣ ∏ j ∈ s, (q j).den := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha, Finset.prod_insert ha]
    exact (Rat.add_den_dvd _ _).trans (Nat.mul_dvd_mul_left _ ih)

/-- A positive rational with denominator dividing `P` is at least `1/P`. -/
theorem one_div_le_of_den_dvd {q : ℚ} {P : ℕ}
    (hq : 0 < q) (hP : 0 < P) (hd : q.den ∣ P) :
    (1 : ℚ) / P ≤ q := by
  have hden : q.den ≤ P := Nat.le_of_dvd hP hd
  have hnum : (1 : ℚ) ≤ q.num := by
    exact_mod_cast (Rat.num_pos.mpr hq)
  calc
    (1 : ℚ) / P ≤ 1 / q.den := by
      exact one_div_le_one_div_of_le (by exact_mod_cast q.den_pos) (by exact_mod_cast hden)
    _ ≤ (q.num : ℚ) / q.den :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ = q := Rat.num_div_den q

/-- The remainder after subtracting finitely many positive unit fractions
from one has a gap of at least the reciprocal of the denominator product. -/
theorem prefix_remainder_gap {α : Type*} [DecidableEq α]
    (s : Finset α) (n : α → ℕ)
    (hn : ∀ j ∈ s, 0 < n j)
    (hrem : 0 < 1 - ∑ j ∈ s, (1 : ℚ) / (n j : ℚ)) :
    (1 : ℚ) / (∏ j ∈ s, n j : ℕ) ≤
      1 - ∑ j ∈ s, (1 : ℚ) / (n j : ℚ) := by
  apply one_div_le_of_den_dvd hrem
  · exact Finset.prod_pos hn
  · have hd := sum_den_dvd_prod s (fun j => (1 : ℚ) / (n j : ℚ))
    have heq : (∏ j ∈ s, ((1 : ℚ) / (n j : ℚ)).den) = ∏ j ∈ s, n j := by
      apply Finset.prod_congr rfl
      intro j hj
      simpa only [one_div] using Rat.inv_natCast_den_of_pos (hn j hj)
    simpa only [Rat.ofNat_sub_den, heq] using hd

end Problem337

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_PrefixGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace Problem337

/-- The elementary growth estimate for successive products of denominators. -/
theorem prefix_growth_bound (k t : ℕ) (P : ℕ → ℕ)
    (hzero : P 0 = 1)
    (hstep : ∀ i < t, P (i + 1) ≤ k * (P i) ^ 2) :
    ∀ i ≤ t, P i ≤ k ^ (2 ^ i - 1) := by
  intro i hi
  induction i with
  | zero => simp [hzero]
  | succ i ih =>
    have hit : i < t := by omega
    have hip := ih (by omega)
    have hpow : 1 ≤ 2 ^ i := Nat.one_le_pow i 2 (by omega)
    have hexp : 1 + (2 ^ i - 1) * 2 = 2 ^ (i + 1) - 1 := by
      rw [pow_succ]
      omega
    calc
      P (i + 1) ≤ k * (P i) ^ 2 := hstep i hit
      _ ≤ k * (k ^ (2 ^ i - 1)) ^ 2 := Nat.mul_le_mul_left k (Nat.pow_le_pow_left hip 2)
      _ = k ^ (2 ^ (i + 1) - 1) := by
        rw [← pow_mul, ← pow_succ']
        congr 1
        omega

/-- The bound for the next denominator follows from the prefix-product bound. -/
theorem denominator_growth_bound (k i P n : ℕ)
    (hP : P ≤ k ^ (2 ^ i - 1)) (hn : n ≤ k * P) :
    n ≤ k ^ (2 ^ i) := by
  have hpow : 1 ≤ 2 ^ i := Nat.one_le_pow i 2 (by omega)
  calc
    n ≤ k * P := hn
    _ ≤ k * k ^ (2 ^ i - 1) := Nat.mul_le_mul_left k hP
    _ = k ^ (2 ^ i) := by
      rw [← pow_succ']
      congr 1
      omega

end Problem337

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_DenominatorBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

 theorem ordered_unit_tail_bound {k : ℕ} (n : Fin k → ℕ)
    (hn : ∀ i, 0 < n i) (hmono : Monotone n)
    (hsum : (∑ j : Fin k, (1 : ℚ) / n j) = 1) (i : Fin k) :
    0 < 1 - ∑ j ∈ Finset.univ.filter (· < i), (1 : ℚ) / n j ∧
    1 - ∑ j ∈ Finset.univ.filter (· < i), (1 : ℚ) / n j ≤
      (k : ℚ) / n i := by
  let s : Finset (Fin k) := Finset.univ.filter (· < i)
  let t : Finset (Fin k) := Finset.univ.filter (i ≤ ·)
  have hsplit : (∑ j ∈ s, (1 : ℚ) / n j) + (∑ j ∈ t, (1 : ℚ) / n j) = 1 := by
    calc
      _ = ∑ j : Fin k, (1 : ℚ) / n j := by
        simpa [s, t, not_lt] using
          (Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Fin k)))
            (p := fun j => j < i) (f := fun j => (1 : ℚ) / n j))
      _ = 1 := hsum
  have hrem : 1 - ∑ j ∈ s, (1 : ℚ) / n j = ∑ j ∈ t, (1 : ℚ) / n j := by
    linarith
  change 0 < 1 - ∑ j ∈ s, (1 : ℚ) / n j ∧ _
  rw [hrem]
  constructor
  · apply lt_of_lt_of_le (show 0 < (1 : ℚ) / n i from div_pos zero_lt_one (by exact_mod_cast hn i))
    apply Finset.single_le_sum (f := fun j => (1 : ℚ) / n j) (a := i)
    · intro j hj
      positivity
    · simp [t]
  · calc
      ∑ j ∈ t, (1 : ℚ) / n j ≤ ∑ _j ∈ t, (1 : ℚ) / n i := by
        apply Finset.sum_le_sum
        intro j hj
        apply one_div_le_one_div_of_le
        · exact_mod_cast hn i
        · exact_mod_cast hmono (by simpa [t] using hj)
      _ = (t.card : ℚ) / n i := by simp [div_eq_mul_inv]
      _ ≤ (k : ℚ) / n i := by
        apply div_le_div_of_nonneg_right
        · exact_mod_cast (show t.card ≤ k from (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_univ.trans (Fintype.card_fin k)))
        · positivity

 theorem denominator_le_prefix_product {k : ℕ} (n : Fin k → ℕ)
    (hn : ∀ i, 0 < n i) (hmono : Monotone n)
    (hsum : (∑ j : Fin k, (1 : ℚ) / n j) = 1) (i : Fin k)
    (hgap : (1 : ℚ) / (∏ j ∈ Finset.univ.filter (· < i), n j : ℕ) ≤
      1 - ∑ j ∈ Finset.univ.filter (· < i), (1 : ℚ) / n j) :
    n i ≤ k * ∏ j ∈ Finset.univ.filter (· < i), n j := by
  have hle := hgap.trans (ordered_unit_tail_bound n hn hmono hsum i).2
  have hp : (0 : ℚ) < (∏ j ∈ Finset.univ.filter (· < i), n j : ℕ) := by
    exact_mod_cast Finset.prod_pos (fun j _ => hn j)
  have hi : (0 : ℚ) < n i := by exact_mod_cast hn i
  have hcross := (div_le_div_iff₀ hp hi).mp hle
  norm_num only [one_mul] at hcross
  exact_mod_cast hcross

/-- The coordinate estimate only needs weak ordering, so it also applies to
expansions with repeated denominators. -/
theorem ordered_unit_denominator_bound {k : ℕ} (n : Fin k → ℕ)
    (hn : ∀ i, 0 < n i) (hmono : Monotone n)
    (hsum : (∑ j : Fin k, (1 : ℚ) / n j) = 1) :
    ∀ i : Fin k, n i ≤ k ^ (2 ^ i.val) := by
  let P : ℕ → ℕ := fun t => ∏ j ∈ Finset.univ.filter (fun j : Fin k => j.val < t), n j
  have hrec : ∀ i : Fin k, n i ≤ k * P i.val := by
    intro i
    apply denominator_le_prefix_product n hn hmono hsum i
    exact prefix_remainder_gap _ n (fun j _ => hn j)
      (ordered_unit_tail_bound n hn hmono hsum i).1
  have hzero : P 0 = 1 := by simp [P]
  have hstep : ∀ t < k, P (t + 1) ≤ k * (P t) ^ 2 := by
    intro t ht
    let i : Fin k := ⟨t, ht⟩
    have hs : Finset.univ.filter (fun j : Fin k => j.val < t + 1) =
        insert i (Finset.univ.filter (fun j : Fin k => j.val < t)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro hj
        by_cases hji : j = i
        · exact Or.inl hji
        · right
          have hne : j.val ≠ t := by
            intro he
            apply hji
            apply Fin.ext
            exact he
          omega
      · rintro (rfl | hj)
        · exact Nat.lt_succ_self t
        · omega
    have hnot : i ∉ Finset.univ.filter (fun j : Fin k => j.val < t) := by
      simp [i]
    have heq : P (t + 1) = n i * P t := by
      simp only [P, hs, Finset.prod_insert hnot]
    calc
      P (t + 1) = n i * P t := heq
      _ ≤ (k * P t) * P t := Nat.mul_le_mul_right (P t) (hrec i)
      _ = k * (P t) ^ 2 := by ring
  intro i
  exact denominator_growth_bound k i.val (P i.val) (n i)
    (prefix_growth_bound k k P hzero hstep i.val i.isLt.le) (hrec i)

 theorem one_expansion_denominator_bound {k : ℕ} (n : Fin k → ℕ)
    (hn : IsOneExpansion n) : ∀ i : Fin k, n i ≤ k ^ (2 ^ i.val) :=
  ordered_unit_denominator_bound n (fun i => hn.1 i) hn.2.1.monotone hn.2.2

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_DivisorSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

lemma divisorSplit_quotient_ge_two {n d : ℕ}
    (hd : 0 < d) (hdn : d ∣ n) (hlt : d < n) : 2 ≤ n / d := by
  have hmul : n / d * d = n := Nat.div_mul_cancel hdn
  by_contra h
  have hq : n / d ≤ 1 := by omega
  have : n / d * d ≤ d := by
    simpa using mul_le_mul_of_nonneg_right hq hd.le
  omega

lemma divisorSplit_order {n d : ℕ}
    (hd : 0 < d) (hdn : d ∣ n) (hlt : d < n) :
    n < n + d ∧ n + d < divisorSplitUpper n d := by
  have hq := divisorSplit_quotient_ge_two hd hdn hlt
  unfold divisorSplitUpper
  constructor
  · omega
  · have hp : 0 < n + d := by omega
    nlinarith

lemma divisorSplit_identity {n d : ℕ}
    (hd : 0 < d) (hdn : d ∣ n) (hn : 0 < n) :
    (1 : ℚ) / n = 1 / (n + d : ℕ) + 1 / divisorSplitUpper n d := by
  have hmul : n / d * d = n := Nat.div_mul_cancel hdn
  have hq : 0 < n / d := by
    by_contra h
    have hz : n / d = 0 := Nat.eq_zero_of_not_pos h
    simp [hz] at hmul
    omega
  have hnq : (n : ℚ) ≠ 0 := by positivity
  have hdq : (d : ℚ) ≠ 0 := by positivity
  have hpd : ((n + d : ℕ) : ℚ) ≠ 0 := by positivity
  have hqq : ((n / d : ℕ) : ℚ) ≠ 0 := by positivity
  have hmulq : ((n / d : ℕ) : ℚ) * d = n := by exact_mod_cast hmul
  unfold divisorSplitUpper
  push_cast
  field_simp
  nlinarith

lemma divisorSplitUpper_injOn {n : ℕ} (hn : 0 < n) :
    Set.InjOn (divisorSplitUpper n) {d : ℕ | 0 < d ∧ d ∣ n} := by
  intro d hd e he hde
  have hdi := divisorSplit_identity hd.1 hd.2 hn
  have hei := divisorSplit_identity he.1 he.2 hn
  have heq : (1 : ℚ) / (n + d : ℕ) = 1 / (n + e : ℕ) := by
    rw [hde] at hdi
    linarith
  have hnd : ((n + d : ℕ) : ℚ) ≠ 0 := by positivity
  have hne : ((n + e : ℕ) : ℚ) ≠ 0 := by positivity
  have hnat : n + d = n + e := by
    have hcast : ((n + d : ℕ) : ℚ) = (n + e : ℕ) := by
      field_simp at heq
      linarith
    exact_mod_cast hcast
  omega

lemma countingGoodSplitDivisors_spec {n d : ℕ} {s : Finset ℕ}
    (hd : d ∈ countingGoodSplitDivisors n s) :
    0 < d ∧ d ∣ n ∧ d < n ∧ n + d ∉ s ∧ divisorSplitUpper n d ∉ s := by
  rcases Finset.mem_filter.mp hd with ⟨hp, ha, hb⟩
  exact ⟨Nat.pos_of_mem_properDivisors hp, (Nat.mem_properDivisors.mp hp).1,
    (Nat.mem_properDivisors.mp hp).2, ha, hb⟩

lemma countingDivisorSplitSet_card {n d : ℕ} {s : Finset ℕ}
    (hd : d ∈ countingGoodSplitDivisors n s) :
    (countingDivisorSplitSet n d s).card = s.card + 2 := by
  obtain ⟨hpos, hdvd, hlt, ha, hb⟩ := countingGoodSplitDivisors_spec hd
  have hne := (divisorSplit_order hpos hdvd hlt).2.ne
  simp [countingDivisorSplitSet, ha, hb, hne]

lemma countingDivisorSplitSet_sum {n d : ℕ} {s : Finset ℕ}
    (hd : d ∈ countingGoodSplitDivisors n s) :
    (∑ a ∈ countingDivisorSplitSet n d s, (1 : ℚ) / a) =
      (∑ a ∈ s, (1 : ℚ) / a) + 1 / n := by
  obtain ⟨hpos, hdvd, hlt, ha, hb⟩ := countingGoodSplitDivisors_spec hd
  have hne := (divisorSplit_order hpos hdvd hlt).2.ne
  have hi := divisorSplit_identity hpos hdvd (lt_trans hpos hlt)
  simp [countingDivisorSplitSet, ha, hb, hne]
  simp only [one_div, Nat.cast_add] at hi
  linarith

lemma countingDivisorSplitSet_injOn (n : ℕ) (s : Finset ℕ) :
    Set.InjOn (fun d => countingDivisorSplitSet n d s) (countingGoodSplitDivisors n s) := by
  intro d hd e he hde
  change countingDivisorSplitSet n d s = countingDivisorSplitSet n e s at hde
  obtain ⟨hdpos, hddvd, hdlt, hda, hdb⟩ := countingGoodSplitDivisors_spec hd
  obtain ⟨hepos, hedvd, helt, hea, heb⟩ := countingGoodSplitDivisors_spec he
  have hdo := (divisorSplit_order hdpos hddvd hdlt).2
  have heo := (divisorSplit_order hepos hedvd helt).2
  have hdm : n + d ∈ countingDivisorSplitSet n e s := by
    rw [← hde]
    simp [countingDivisorSplitSet]
  have hem : n + e ∈ countingDivisorSplitSet n d s := by
    rw [hde]
    simp [countingDivisorSplitSet]
  simp only [countingDivisorSplitSet, Finset.mem_insert] at hdm hem
  rcases hdm with h | h | h
  · omega
  · rcases hem with h' | h' | h'
    · omega
    · omega
    · exact (hea h').elim
  · exact (hda h).elim

lemma countingGoodSplitDivisors_card_bound (n : ℕ) (s : Finset ℕ) :
    n.properDivisors.card ≤ (countingGoodSplitDivisors n s).card + 2 * s.card := by
  by_cases hn : n = 0
  · simp [hn]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  let bad₁ := n.properDivisors.filter (fun d => n + d ∈ s)
  let bad₂ := n.properDivisors.filter (fun d => divisorSplitUpper n d ∈ s)
  have hb₁ : bad₁.card ≤ s.card := by
    apply Finset.card_le_card_of_injOn (fun d => n + d)
    · intro d hd
      exact (Finset.mem_filter.mp hd).2
    · intro d hd e he hde
      change n + d = n + e at hde
      omega
  have hb₂ : bad₂.card ≤ s.card := by
    apply Finset.card_le_card_of_injOn (divisorSplitUpper n)
    · intro d hd
      exact (Finset.mem_filter.mp hd).2
    · intro d hd e he hde
      have hdp := (Finset.mem_filter.mp hd).1
      have hep := (Finset.mem_filter.mp he).1
      exact divisorSplitUpper_injOn hnpos
        ⟨Nat.pos_of_mem_properDivisors hdp, (Nat.mem_properDivisors.mp hdp).1⟩
        ⟨Nat.pos_of_mem_properDivisors hep, (Nat.mem_properDivisors.mp hep).1⟩ hde
  have hcover : n.properDivisors ⊆ countingGoodSplitDivisors n s ∪ (bad₁ ∪ bad₂) := by
    intro d hd
    by_cases ha : n + d ∈ s
    · simp [bad₁, ha, hd]
    by_cases hb : divisorSplitUpper n d ∈ s
    · simp [bad₂, hb, hd]
    · simp [countingGoodSplitDivisors, hd, ha, hb]
  have hc := Finset.card_le_card hcover
  have hu := Finset.card_union_le (countingGoodSplitDivisors n s) (bad₁ ∪ bad₂)
  have hv := Finset.card_union_le bad₁ bad₂
  omega

lemma countingGoodSplitDivisors_card_lower (n : ℕ) (s : Finset ℕ) :
    n.divisors.card - 1 - 2 * s.card ≤ (countingGoodSplitDivisors n s).card := by
  have hb := countingGoodSplitDivisors_card_bound n s
  by_cases hn : n = 0
  · simp [hn]
  have hc : n.divisors.card = n.properDivisors.card + 1 := by
    rw [← Nat.insert_self_properDivisors hn]
    simp
  omega

/-- Distinct good divisors give equally many different denominator sets. -/
lemma countingDivisorSplitSet_image_card (n : ℕ) (s : Finset ℕ) :
    ((countingGoodSplitDivisors n s).image (fun d => countingDivisorSplitSet n d s)).card =
      (countingGoodSplitDivisors n s).card := by
  exact Finset.card_image_of_injOn (countingDivisorSplitSet_injOn n s)

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_FiniteExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- A finite collection of denominators has a canonical increasing enumeration. -/
theorem finset_increasing_enumeration (s : Finset ℕ) :
    ∃ n : Fin s.card → ℕ, StrictMono n ∧
      (∀ m, (∃ i, n i = m) ↔ m ∈ s) ∧
      (∀ f : ℕ → ℚ, (∑ i, f (n i)) = ∑ m ∈ s, f m) := by
  refine ⟨s.orderEmbOfFin rfl, (s.orderEmbOfFin rfl).strictMono, ?_, ?_⟩
  · intro m
    change m ∈ Set.range (s.orderEmbOfFin rfl) ↔ m ∈ s
    rw [Finset.range_orderEmbOfFin]
    rfl
  · intro f
    calc
      (∑ i, f ((s.orderEmbOfFin rfl) i)) =
          ∑ m ∈ Finset.univ.image (s.orderEmbOfFin rfl), f m := by
        rw [Finset.sum_image (fun a _ b _ h => (s.orderEmbOfFin rfl).injective h)]
      _ = ∑ m ∈ s, f m := by rw [Finset.image_orderEmbOfFin_univ]

/-- Enumeration preserves a lower bound and the sum of unit fractions. -/
theorem finset_unit_fraction_representation (s : Finset ℕ) (a : ℕ) (x : ℚ)
    (hpos : ∀ m ∈ s, a ≤ m) (hsum : (∑ m ∈ s, (1 : ℚ) / m) = x) :
    ∃ n : Fin s.card → ℕ, (∀ i, a ≤ n i) ∧ StrictMono n ∧
      (∑ i, (1 : ℚ) / n i) = x ∧
      (∀ m, (∃ i, n i = m) ↔ m ∈ s) := by
  obtain ⟨n, hmono, hmem, hsum'⟩ := finset_increasing_enumeration s
  refine ⟨n, ?_, hmono, ?_, hmem⟩
  · intro i
    exact hpos (n i) ((hmem _).mp ⟨i, rfl⟩)
  · exact (hsum' (fun m => (1 : ℚ) / m)).trans hsum

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_DivisorCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- A finite family of distinct denominator sets produces the same number of
increasing one-expansions. -/
lemma finset_family_card_le_F (family : Finset (Finset ℕ)) (k : ℕ)
    (hfinite : (OneExpansions k).Finite)
    (hfamily : ∀ s ∈ family, s.card = k ∧
      (∀ m ∈ s, 1 ≤ m) ∧ (∑ m ∈ s, (1 : ℚ) / m) = 1) :
    family.card ≤ F k := by
  classical
  have hex : ∀ s : family, ∃ n : Fin k → ℕ,
      IsOneExpansion n ∧ (∀ m, (∃ i, n i = m) ↔ m ∈ s.val) := by
    intro s
    obtain ⟨hc, hp, hs⟩ := hfamily s.val s.property
    have he := finset_unit_fraction_representation s.val 1 1 hp hs
    rw [hc] at he
    obtain ⟨n, hnp, hnm, hns, hnr⟩ := he
    exact ⟨n, ⟨hnp, hnm, hns⟩, hnr⟩
  let f : family → OneExpansions k := fun s =>
    ⟨Classical.choose (hex s), (Classical.choose_spec (hex s)).1⟩
  have hf : Function.Injective f := by
    intro s t hst
    have hn : Classical.choose (hex s) = Classical.choose (hex t) :=
      congrArg Subtype.val hst
    apply Subtype.ext
    apply Finset.ext
    intro m
    rw [← (Classical.choose_spec (hex s)).2 m,
      ← (Classical.choose_spec (hex t)).2 m, hn]
  let : Fintype (OneExpansions k) := hfinite.fintype
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe, Set.fintypeCard_eq_ncard, F] using hc

lemma countingDivisorSplitSet_positive {n d : ℕ} {s : Finset ℕ}
    (hd : d ∈ countingGoodSplitDivisors n s) (hs : ∀ m ∈ s, 1 ≤ m) :
    ∀ m ∈ countingDivisorSplitSet n d s, 1 ≤ m := by
  obtain ⟨hpos, hdvd, hlt, ha, hb⟩ := countingGoodSplitDivisors_spec hd
  have ho := divisorSplit_order hpos hdvd hlt
  intro m hm
  simp only [countingDivisorSplitSet, Finset.mem_insert] at hm
  rcases hm with rfl | rfl | hm
  · omega
  · omega
  · exact hs m hm

/-- Branching over all noncolliding proper divisors of one denominator. -/
theorem divisor_branching_lower_bound (s : Finset ℕ) (n : ℕ)
    (hn : n ∈ s) (hpos : ∀ m ∈ s, 1 ≤ m)
    (hsum : (∑ m ∈ s, (1 : ℚ) / m) = 1)
    (hfinite : (OneExpansions (s.card + 1)).Finite) :
    n.divisors.card - 1 - 2 * (s.card - 1) ≤ F (s.card + 1) := by
  classical
  let t := s.erase n
  let family := (countingGoodSplitDivisors n t).image (fun d => countingDivisorSplitSet n d t)
  have htcard : t.card = s.card - 1 := Finset.card_erase_of_mem hn
  have hcpos : 0 < s.card := Finset.card_pos.mpr ⟨n, hn⟩
  have htpos : ∀ m ∈ t, 1 ≤ m := fun m hm => hpos m (Finset.mem_of_mem_erase hm)
  have htsum : (∑ m ∈ t, (1 : ℚ) / m) + 1 / n = 1 := by
    exact (Finset.sum_erase_add s (fun m => (1 : ℚ) / m) hn).trans hsum
  have hf : family.card ≤ F (s.card + 1) := by
    apply finset_family_card_le_F family (s.card + 1) hfinite
    intro u hu
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hu
    refine ⟨?_, countingDivisorSplitSet_positive hd htpos, ?_⟩
    · rw [countingDivisorSplitSet_card hd, htcard]
      omega
    · exact (countingDivisorSplitSet_sum hd).trans htsum
  have hfamily : family.card = (countingGoodSplitDivisors n t).card :=
    countingDivisorSplitSet_image_card n t
  have hl := countingGoodSplitDivisors_card_lower n t
  rw [htcard] at hl
  rw [hfamily] at hf
  exact hl.trans hf

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_EgyptianExistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped BigOperators

namespace Problem337

/-- Elementary greedy existence, stated independently of the shared definitions. -/
theorem exists_strict_unit_fraction_sum (a b : ℕ) (ha : 1 ≤ a) (hab : a < b) :
    ∃ k : ℕ, ∃ n : Fin k → ℕ,
      (∀ i, 2 ≤ n i) ∧ StrictMono n ∧
      (∑ i : Fin k, (1 : ℚ) / (n i : ℚ)) = (a : ℚ) / (b : ℚ) := by
  induction a using Nat.strong_induction_on generalizing b with
  | h a ih =>
    have ha0 : 0 < a := ha
    have hb0 : 0 < b := lt_trans ha0 hab
    have hdiv := Nat.div_add_mod b a
    have hmod := Nat.mod_lt b ha0
    by_cases hr : b % a = 0
    · have hq : 2 ≤ b / a := by
        by_contra h
        have hq' : b / a ≤ 1 := by omega
        have hmul : a * (b / a) ≤ a := by nlinarith
        omega
      refine ⟨1, fun _ => b / a, (fun _ => hq), ?_, ?_⟩
      · intro i j hij
        have hi := i.isLt
        have hj := j.isLt
        omega
      · simp only [Fin.sum_univ_one]
        have heq : a * (b / a) = b := by omega
        have hq0 : ((b / a : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (by omega : b / a ≠ 0)
        have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
        have heq' : (a : ℚ) * (b / a : ℕ) = b := by exact_mod_cast heq
        apply (div_eq_div_iff hq0 hbq).2
        simpa [mul_comm] using heq'.symm
    · let d := b / a + 1
      let c := a - b % a
      have hd : 2 ≤ d := by
        have := Nat.div_pos (Nat.le_of_lt hab) ha0
        dsimp [d]
        omega
      have hd0 : 0 < d := by omega
      have hcpos : 1 ≤ c := by dsimp [c]; omega
      have hca : c < a := by dsimp [c]; omega
      have hcb : c < b * d := by nlinarith
      obtain ⟨k, n, hn, hmono, hsum⟩ := ih c hca (b * d) hcpos hcb
      have hbq : (0 : ℚ) < b := by exact_mod_cast hb0
      have hdq : (0 : ℚ) < d := by exact_mod_cast hd0
      have hdecomp : (1 : ℚ) / d + (c : ℚ) / (b * d : ℕ) = (a : ℚ) / b := by
        have hc : (c : ℚ) = a - (b % a : ℕ) := by
          dsimp [c]
          exact Nat.cast_sub (Nat.le_of_lt hmod)
        have hdivq : (a : ℚ) * (b / a : ℕ) + (b % a : ℕ) = b := by
          exact_mod_cast hdiv
        have hddef : (d : ℚ) = (b / a : ℕ) + 1 := by simp [d]
        push_cast
        field_simp
        nlinarith
      have hsmall : (c : ℚ) / (b * d : ℕ) < (1 : ℚ) / d := by
        have hcb' : (c : ℚ) < b := by exact_mod_cast (lt_trans hca hab)
        push_cast
        apply (div_lt_div_iff₀ (mul_pos hbq hdq) hdq).2
        nlinarith
      have hdn : ∀ i, d < n i := by
        intro i
        have hle : (1 : ℚ) / n i ≤ (c : ℚ) / (b * d : ℕ) := by
          rw [← hsum]
          exact Finset.single_le_sum (f := fun j : Fin k => (1 : ℚ) / n j) (fun j _ => by positivity) (Finset.mem_univ i)
        have hni : (0 : ℚ) < n i := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) (hn i))
        have := (one_div_lt_one_div hni hdq).1 (lt_of_le_of_lt hle hsmall)
        exact_mod_cast this
      refine ⟨k + 1, Fin.cons d n, ?_, ?_, ?_⟩
      · intro i
        exact Fin.cases hd (fun j => hn j) i
      · intro i j hij
        cases i using Fin.cases with
        | zero =>
          cases j using Fin.cases with
          | zero => exact False.elim ((lt_irrefl _) hij)
          | succ j => simpa using hdn j
        | succ i =>
          cases j using Fin.cases with
          | zero => simp at hij
          | succ j => simpa using hmono (Fin.succ_lt_succ_iff.mp hij)
      · rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        rw [hsum]
        exact hdecomp

end Problem337

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_FiniteBox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- Counting positive integer functions in a varying finite box. -/
theorem finite_ncard_le_box {ι : Type*} [Fintype ι]
    (S : Set (ι → ℕ)) (B : ι → ℕ)
    (hS : ∀ n ∈ S, ∀ i, 1 ≤ n i ∧ n i ≤ B i) :
    S.Finite ∧ S.ncard ≤ ∏ i, B i := by
  classical
  have hsub : S ⊆ Set.pi Set.univ (fun i => Set.Icc 1 (B i)) := by
    intro n hn i _
    exact hS n hn i
  have hcard : (Set.pi Set.univ (fun i => Set.Icc 1 (B i))).encard =
      (∏ i, B i : ℕ) := by
    rw [Set.encard_pi_eq_prod_encard, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro i _
    rw [← (Set.finite_Icc 1 (B i)).cast_ncard_eq]
    simp
  apply Set.encard_le_coe_iff_finite_ncard_le.mp
  rw [← hcard]
  exact Set.encard_le_encard hsub

/-- Geometric exponent sum for the denominator box. -/
theorem sum_two_pow_fin (k : ℕ) :
    (∑ i : Fin k, 2 ^ i.val) = 2 ^ k - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih, pow_succ]
    have hpos : 0 < 2 ^ k := pow_pos (by decide) _
    omega

/-- The denominator box appearing in the counting bound has the stated size. -/
theorem prod_egyptian_bounds (k : ℕ) :
    (∏ i : Fin k, k ^ (2 ^ i.val)) = k ^ (2 ^ k - 1) := by
  rw [Finset.prod_pow_eq_pow_sum, sum_two_pow_fin]

/-- Pointwise denominator bounds give finiteness and the sharp box-count estimate. -/
theorem finite_ncard_le_egyptian_box (k : ℕ) (S : Set (Fin k → ℕ))
    (hpos : ∀ n ∈ S, ∀ i, 1 ≤ n i)
    (hbound : ∀ n ∈ S, ∀ i, n i ≤ k ^ (2 ^ i.val)) :
    S.Finite ∧ S.ncard ≤ k ^ (2 ^ k - 1) := by
  simpa only [prod_egyptian_bounds] using
    finite_ncard_le_box S (fun i => k ^ (2 ^ i.val))
      (fun n hn i => ⟨hpos n hn i, hbound n hn i⟩)

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_LengthBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- Existence is the only input needed to obtain a least expansion. -/
theorem egyptianLength_attained_of_exists {a b : ℕ}
    (h : ∃ k : ℕ, ∃ n : Fin k → ℕ,
      IsEgyptianExpansion ((a : ℚ) / (b : ℚ)) n) :
    ∃ n : Fin (egyptianLength a b) → ℕ,
      IsEgyptianExpansion ((a : ℚ) / (b : ℚ)) n := by
  exact Nat.sInf_mem h

/-- A pointwise length is bounded by the maximum over proper numerators. -/
theorem egyptianLength_le_max {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    egyptianLength a b ≤ maxEgyptianLength b := by
  unfold maxEgyptianLength
  simpa only [ite_eq_left ha] using
    (Finset.le_sup (f := fun a => if 1 ≤ a then egyptianLength a b else 0)
      (Finset.mem_range.mpr hab))

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_RemoveRepetitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- Effect of a one-coordinate replacement on a finite reciprocal sum. -/
theorem reciprocal_sum_update {k : ℕ} (n : Fin k → ℕ) (i : Fin k) (a : ℕ) :
    (∑ t, (1 : ℚ) / (Function.update n i a t : ℚ)) =
      (∑ t, (1 : ℚ) / (n t : ℚ)) + 1 / (a : ℚ) - 1 / (n i : ℚ) := by
  classical
  simp_rw [Function.apply_update (fun _ (v : ℕ) => (1 : ℚ) / v)]
  rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
  rw [Finset.sdiff_singleton_eq_erase, Finset.sum_erase_eq_sub (Finset.mem_univ i)]
  ring

/-- Two-coordinate replacement preserves the sum when the two reciprocals agree. -/
theorem reciprocal_sum_update_two {k : ℕ} (n : Fin k → ℕ) {i j : Fin k}
    (hij : i ≠ j) (a b : ℕ)
    (hab : (1 : ℚ) / a + 1 / b = 1 / n i + 1 / n j) :
    (∑ t, (1 : ℚ) / (Function.update (Function.update n i a) j b t : ℚ)) =
      ∑ t, (1 : ℚ) / (n t : ℚ) := by
  rw [reciprocal_sum_update, reciprocal_sum_update]
  simp only [Function.update_of_ne hij.symm]
  linarith

/-- Any first-coordinate decrease beats a later-coordinate change lexicographically. -/
theorem lex_update_two_lt {k : ℕ} (n : Fin k → ℕ) {i j : Fin k}
    (hij : i < j) (a b : ℕ) (ha : a < n i) :
    Pi.Lex (· < ·) (· < ·) (Function.update (Function.update n i a) j b) n := by
  refine ⟨i, ?_, ?_⟩
  · intro t ht
    simp [Function.update_of_ne (ne_of_lt ht), Function.update_of_ne (ne_of_lt (ht.trans hij))]
  · simpa [Function.update_of_ne (ne_of_lt hij)] using ha

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_MarkedCleanup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

open scoped BigOperators

namespace Problem337

/-- Takenouchi's duplicate replacement preserves every odd divisor of the repeated denominator. -/
theorem marked_duplicate_replacement (m : ℕ) (hm : 3 ≤ m) :
    ∃ u v : ℕ, 1 ≤ u ∧ 1 ≤ v ∧ u < m ∧
      2 * m < u + v ∧
      (2 : ℚ) / (m : ℚ) = 1 / (u : ℚ) + 1 / (v : ℚ) ∧
      (∀ Q : ℕ, Odd Q → Q ∣ m → Q ∣ v) := by
  rcases Nat.even_or_odd m with heven | hodd
  · obtain ⟨p, rfl⟩ := heven
    have hp : 2 ≤ p := by omega
    refine ⟨p + 1, p * (p + 1), by omega, by nlinarith, by omega, ?_, ?_, ?_⟩
    · nlinarith [Nat.mul_le_mul_left p hp]
    · have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
      have hp1 : (p : ℚ) + 1 ≠ 0 := by positivity
      push_cast
      field_simp
      ring
    · intro Q hQ hdiv
      have hdiv' : Q ∣ 2 * p := by simpa [two_mul] using hdiv
      have hpdiv : Q ∣ p := hQ.coprime_two_right.dvd_of_dvd_mul_left hdiv'
      exact dvd_mul_of_dvd_left hpdiv (p + 1)
  · obtain ⟨p, rfl⟩ := hodd
    have hp : 1 ≤ p := by omega
    refine ⟨p + 1, (p + 1) * (2 * p + 1), by omega, by nlinarith, by omega, ?_, ?_, ?_⟩
    · nlinarith [Nat.mul_le_mul_left p hp]
    · have hp1 : (p : ℚ) + 1 ≠ 0 := by positivity
      have hp2 : 2 * (p : ℚ) + 1 ≠ 0 := by positivity
      push_cast
      field_simp
      ring
    · intro Q _ hdiv
      exact dvd_mul_of_dvd_right hdiv (p + 1)

/-- An odd marker greater than one forces its denominator to be at least three. -/
theorem odd_marker_denominator_ge_three {Q n : ℕ} (hQ : Odd Q)
    (hQone : 1 < Q) (hn : 0 < n) (hdiv : Q ∣ n) : 3 ≤ n := by
  have hQthree : 3 ≤ Q := by
    obtain ⟨p, hp⟩ := hQ
    omega
  exact hQthree.trans (Nat.le_of_dvd hn hdiv)

/-- A positive expansion of one carrying an odd marker cannot have denominator one. -/
theorem marked_sum_one_denominators_ge_two {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ι → ℕ) (hn : ∀ i, 0 < n i)
    (hsum : (∑ i, (1 : ℚ) / (n i : ℚ)) = 1)
    {Q : ℕ} (hQ : Odd Q) (hQone : 1 < Q) (hmarker : ∃ i, Q ∣ n i) :
    ∀ i, 2 ≤ n i := by
  obtain ⟨j, hj⟩ := hmarker
  have hjthree : 3 ≤ n j := odd_marker_denominator_ge_three hQ hQone (hn j) hj
  intro i
  by_contra hni
  have hione : n i = 1 := by have := hn i; omega
  have hji : j ≠ i := by intro h; subst j; omega
  have hlt : (1 : ℚ) / (n i : ℚ) < ∑ k, (1 : ℚ) / (n k : ℚ) := by
    apply Finset.single_lt_sum hji (Finset.mem_univ i) (Finset.mem_univ j)
    · exact one_div_pos.mpr (by exact_mod_cast hn j)
    · intro k _ _
      exact le_of_lt (one_div_pos.mpr (by exact_mod_cast hn k))
  rw [hione, hsum] at hlt
  norm_num at hlt

/-- In a marked expansion of one, any repeated denominator is at least three. -/
theorem marked_sum_one_duplicate_ge_three {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ι → ℕ) (hn : ∀ i, 0 < n i)
    (hsum : (∑ i, (1 : ℚ) / (n i : ℚ)) = 1)
    {Q : ℕ} (hQ : Odd Q) (hQone : 1 < Q) (hmarker : ∃ i, Q ∣ n i)
    {i j : ι} (hij : i ≠ j) (heq : n i = n j) : 3 ≤ n i := by
  have htwo := marked_sum_one_denominators_ge_two n hn hsum hQ hQone hmarker i
  by_contra hthree
  have hitwo : n i = 2 := by omega
  have hjtwo : n j = 2 := by omega
  obtain ⟨k, hk⟩ := hmarker
  have hkthree := odd_marker_denominator_ge_three hQ hQone (hn k) hk
  have hki : k ≠ i := by intro h; subst k; omega
  have hkj : k ≠ j := by intro h; subst k; omega
  have hlt : (∑ l ∈ ({i, j} : Finset ι), (1 : ℚ) / (n l : ℚ)) <
      ∑ l, (1 : ℚ) / (n l : ℚ) := by
    apply Finset.sum_lt_sum_of_subset (Finset.subset_univ _) (Finset.mem_univ k)
      (by simp [hki, hkj])
    · exact one_div_pos.mpr (by exact_mod_cast hn k)
    · intro l _ _
      exact le_of_lt (one_div_pos.mpr (by exact_mod_cast hn l))
  rw [Finset.sum_pair hij, hitwo, hjtwo, hsum] at hlt
  norm_num at hlt

/-- A two-coordinate update retains an odd-divisibility marker whenever removed markers are restored. -/
theorem marker_update_two {k Q : ℕ} (n : Fin k → ℕ) {i j : Fin k}
    (hij : i ≠ j) (a b : ℕ) (hmarker : ∃ t, Q ∣ n t)
    (hrestore : Q ∣ n i ∨ Q ∣ n j → Q ∣ a ∨ Q ∣ b) :
    ∃ t, Q ∣ Function.update (Function.update n i a) j b t := by
  obtain ⟨t, ht⟩ := hmarker
  by_cases hti : t = i
  · subst t
    rcases hrestore (Or.inl ht) with ha | hb
    · exact ⟨i, by simpa [Function.update_of_ne hij] using ha⟩
    · exact ⟨j, by simpa using hb⟩
  · by_cases htj : t = j
    · subst t
      rcases hrestore (Or.inr ht) with ha | hb
      · exact ⟨i, by simpa [Function.update_of_ne hij] using ha⟩
      · exact ⟨j, by simpa using hb⟩
    · exact ⟨t, by simpa [Function.update_of_ne htj, Function.update_of_ne hti] using ht⟩

/-- Exact-length cleanup at total one, retaining a denominator divisible by a specified odd integer. -/
theorem marked_cleanup_exact_length {k Q : ℕ} (hQ : Odd Q) (hQone : 1 < Q)
    (original : Fin k → ℕ) (hpos : ∀ i, 1 ≤ original i)
    (hsum : (∑ i, (1 : ℚ) / (original i : ℚ)) = 1)
    (hmarker : ∃ i, Q ∣ original i) :
    ∃ n : Fin k → ℕ, IsOneExpansion n ∧ ∃ i, Q ∣ n i := by
  classical
  let S : Set (Fin k → ℕ) :=
    {n | (∀ i, 1 ≤ n i) ∧ (∑ i, (1 : ℚ) / (n i : ℚ)) = 1 ∧ ∃ i, Q ∣ n i}
  have hwf : WellFounded (Pi.Lex (· < ·) (fun {i : Fin k} (a b : ℕ) => a < b)) :=
    Pi.Lex.wellFounded (· < ·) (fun _ => wellFounded_lt)
  obtain ⟨n, hn, hminimal⟩ := hwf.has_min S ⟨original, hpos, hsum, hmarker⟩
  change (∀ i, 1 ≤ n i) ∧ (∑ i, (1 : ℚ) / (n i : ℚ)) = 1 ∧ (∃ i, Q ∣ n i) at hn
  have hreplace (i j : Fin k) (hij : i < j) (a b : ℕ)
      (ha : 1 ≤ a) (hb : 1 ≤ b) (halt : a < n i)
      (hab : (1 : ℚ) / a + 1 / b = 1 / n i + 1 / n j)
      (hrestore : Q ∣ n i ∨ Q ∣ n j → Q ∣ a ∨ Q ∣ b) : False := by
    apply hminimal (Function.update (Function.update n i a) j b) ?_
      (lex_update_two_lt n hij a b halt)
    refine ⟨?_, ?_, marker_update_two n hij.ne a b hn.2.2 hrestore⟩
    · intro t
      by_cases htj : t = j
      · subst t; simpa using hb
      · by_cases hti : t = i
        · subst t; simpa [Function.update_of_ne htj] using ha
        · simpa [Function.update_of_ne htj, Function.update_of_ne hti] using hn.1 t
    · rw [reciprocal_sum_update_two n hij.ne a b hab]
      exact hn.2.1
  refine ⟨n, ⟨hn.1, ?_, hn.2.1⟩, hn.2.2⟩
  intro i j hij
  by_contra! hnot
  rcases lt_or_eq_of_le hnot with hlt | heq
  · exact hreplace i j hij (n j) (n i) (hn.1 j) (hn.1 i) hlt
      (add_comm _ _) (fun h => h.elim Or.inr Or.inl)
  · have hm : 3 ≤ n i := marked_sum_one_duplicate_ge_three n hn.1 hn.2.1
      hQ hQone hn.2.2 hij.ne heq.symm
    obtain ⟨a, b, ha, hb, halt, _, hab, hdiv⟩ := marked_duplicate_replacement (n i) hm
    apply hreplace i j hij a b ha hb halt
    · rw [heq]
      calc
        (1 : ℚ) / a + 1 / b = 2 / (n i : ℚ) := hab.symm
        _ = 1 / (n i : ℚ) + 1 / (n i : ℚ) := by ring
    · intro h
      apply Or.inr
      apply hdiv Q hQ
      rcases h with hi | hj
      · exact hi
      · simpa [heq] using hj

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_MarkerCoverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- An expansion containing a proper unit fraction needs at least three terms. -/
theorem marker_length_ge_three {k m : ℕ} (hm : m ∈ D k) : 3 ≤ k := by
  rcases hm with ⟨hm, n, hn, i, hi⟩
  rcases hn with ⟨hpos, hmono, hsum⟩
  by_contra hk
  have hk : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hk with rfl | rfl | rfl
  · exact Fin.elim0 i
  · have hi0 : i = 0 := Subsingleton.elim _ _
    subst i
    rw [Fin.sum_univ_one, hi] at hsum
    have hmQ : (2 : ℚ) ≤ m := by exact_mod_cast hm
    have hle : (1 : ℚ) / m ≤ 1 / 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hmQ
    linarith
  · rw [Fin.sum_univ_two] at hsum
    have h01 : n 0 < n 1 := hmono (by decide)
    have hp0 := hpos 0
    have hp1 := hpos 1
    have hp1Q : (0 : ℚ) < n 1 := by exact_mod_cast (by omega : 0 < n 1)
    have hn0 : 2 ≤ n 0 := by
      by_contra h
      have heq : n 0 = 1 := by omega
      rw [heq] at hsum
      norm_num at hsum
      have := div_pos (by norm_num : (0 : ℚ) < 1) hp1Q
      linarith
    have hn1 : 3 ≤ n 1 := by omega
    have hle0 : (1 : ℚ) / n 0 ≤ 1 / 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by exact_mod_cast hn0)
    have hle1 : (1 : ℚ) / n 1 ≤ 1 / 3 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by exact_mod_cast hn1)
    linarith

end Problem337

end

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

lemma primeCounting_nth_prime (n : ℕ) :
    (Nat.nth Nat.Prime n).primeCounting = n + 1 := by
  exact Nat.count_nth_succ_of_infinite Nat.infinite_setOfPred_prime n

lemma nth_prime_chebyshev_bound (n : ℕ) :
    (Nat.nth Nat.Prime n : ℝ) * Real.log 2 ≤
      ((n : ℝ) + 3) * Real.log (Nat.nth Nat.Prime n : ℝ) := by
  let p := Nat.nth Nat.Prime n
  have hp2 : 2 ≤ p := (Nat.prime_nth_prime n).two_le
  have hp2r : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (by linarith)
  have hcheb := (div_le_iff₀ hlog).mp (Chebyshev.pi_ge p)
  have hpi : (p.primeCounting : ℝ) = (n : ℝ) + 1 := by
    rw [show p.primeCounting = n + 1 from primeCounting_nth_prime n]
    push_cast
    rfl
  rw [hpi] at hcheb
  have hlogplus : Real.log ((p : ℝ) + 1) ≤ 2 * Real.log (p : ℝ) := by
    calc
      Real.log ((p : ℝ) + 1) ≤ Real.log ((p : ℝ) ^ 2) :=
        Real.log_le_log (by positivity) (by nlinarith)
      _ = 2 * Real.log (p : ℝ) := by rw [Real.log_pow]; norm_num
  dsimp [p] at *
  nlinarith

lemma tendsto_nth_prime_atTop :
    Tendsto (fun n : ℕ => (Nat.nth Nat.Prime n : ℝ)) atTop atTop := by
  apply tendsto_atTop_mono (f := fun n : ℕ => (n : ℝ))
  · intro n
    exact_mod_cast (Nat.add_two_le_nth_prime n).trans' (by omega)
  · exact tendsto_natCast_atTop_atTop

lemma eventually_log_nth_prime_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      Real.log (Nat.nth Nat.Prime n : ℝ) ≤
        (1 + ε) * Real.log (n : ℝ) := by
  let r : ℝ := ε / (1 + ε)
  have hr : 0 < r := by dsimp [r]; positivity
  have hrlt : r < 1 := by
    dsimp [r]
    apply (div_lt_one (by positivity)).2
    linarith
  have hc : 0 < Real.log 2 / 2 := by positivity
  have hsmall := (isLittleO_log_rpow_atTop hr).bound hc
  have hevent := tendsto_nth_prime_atTop.eventually hsmall
  filter_upwards [hevent, eventually_ge_atTop 3] with n hn hn3
  let p := (Nat.nth Nat.Prime n : ℝ)
  have hp : 0 < p := by
    dsimp [p]
    exact_mod_cast (Nat.prime_nth_prime n).pos
  have hp1 : 1 ≤ p := by
    dsimp [p]
    exact_mod_cast (Nat.prime_nth_prime n).one_lt.le
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn3r : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hpR : 0 < p ^ r := Real.rpow_pos_of_pos hp r
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg hp1
  have hlog2 : 0 < Real.log 2 := by positivity
  change ‖Real.log p‖ ≤ (Real.log 2 / 2) * ‖p ^ r‖ at hn
  have hbound : Real.log p ≤ (Real.log 2 / 2) * p ^ r := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hlogp,
      abs_of_pos hpR] using hn
  have hcheb : p * Real.log 2 ≤ ((n : ℝ) + 3) * Real.log p :=
    nth_prime_chebyshev_bound n
  have hpre : p ≤ (n : ℝ) * p ^ r := by
    have h1 : ((n : ℝ) + 3) * Real.log p ≤ 2 * (n : ℝ) * Real.log p := by
      nlinarith
    have h2 : 2 * (n : ℝ) * Real.log p ≤
        2 * (n : ℝ) * ((Real.log 2 / 2) * p ^ r) := by
      gcongr
    nlinarith
  have hpow : p ^ (1 - r) ≤ (n : ℝ) := by
    rw [Real.rpow_sub hp, Real.rpow_one]
    exact (div_le_iff₀ hpR).2 hpre
  have hlogbound := Real.log_le_log (Real.rpow_pos_of_pos hp (1-r)) hpow
  rw [Real.log_rpow hp] at hlogbound
  have heq : (1 + ε) * (1 - r) = 1 := by
    dsimp [r]
    field_simp
    ring
  change Real.log p ≤ (1 + ε) * Real.log (n : ℝ)
  nlinarith

lemma log_primePrefixProduct_le (n : ℕ) :
    Real.log (primePrefixProduct n : ℝ) ≤
      (n : ℝ) * Real.log (Nat.nth Nat.Prime n : ℝ) := by
  unfold primePrefixProduct
  rw [Nat.cast_prod, Real.log_prod (by
    intro i hi
    exact_mod_cast (Nat.prime_nth_prime i).ne_zero)]
  calc
    (∑ i ∈ Finset.range n, Real.log (Nat.nth Nat.Prime i : ℝ)) ≤
        ∑ _i ∈ Finset.range n, Real.log (Nat.nth Nat.Prime n : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Real.log_le_log
      · exact_mod_cast (Nat.prime_nth_prime i).pos
      · exact_mod_cast Nat.nth_monotone Nat.infinite_setOfPred_prime
          (Finset.mem_range.mp hi).le
    _ = (n : ℝ) * Real.log (Nat.nth Nat.Prime n : ℝ) := by simp

lemma eventually_log_primePrefixProduct_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      Real.log (primePrefixProduct n : ℝ) ≤
        (1 + ε) * (n : ℝ) * Real.log (n : ℝ) := by
  filter_upwards [eventually_log_nth_prime_le hε] with n hn
  calc
    Real.log (primePrefixProduct n : ℝ) ≤
        (n : ℝ) * Real.log (Nat.nth Nat.Prime n : ℝ) := log_primePrefixProduct_le n
    _ ≤ (n : ℝ) * ((1 + ε) * Real.log (n : ℝ)) := by gcongr
    _ = _ := by ring

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_OddPrimorial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped BigOperators
noncomputable section
namespace Problem337

lemma card_divisors_prime_finset_product (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) : (∏ p ∈ s, p).divisors.card = 2 ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
      have hprime := hs p (by simp)
      have hcop : p.Coprime (∏ q ∈ s, q) := by
        apply Nat.Coprime.prod_right
        intro q hq
        apply (Nat.coprime_primes hprime (hs q (by simp [hq]))).2
        intro heq
        exact hp (heq ▸ hq)
      rw [Finset.prod_insert hp, hcop.card_divisors_mul, hprime.divisors,
        ih (fun q hq => hs q (by simp [hq])), Finset.card_insert_of_notMem hp]
      rw [Finset.card_pair hprime.ne_one.symm]
      simp [pow_succ, mul_comm]

lemma oddPrimorial_odd (r : ℕ) : Odd (oddPrimorial r) := by
  apply Nat.Coprime.odd_of_left
  apply Nat.Coprime.prod_right
  intro i hi
  apply Odd.coprime_two_left
  apply (Nat.prime_nth_prime (i+1)).odd_iff.mpr
  have := Nat.add_two_le_nth_prime (i+1)
  omega

lemma oddPrimorial_divisors_card (r : ℕ) : (oddPrimorial r).divisors.card = 2 ^ r := by
  classical
  let f := fun i => Nat.nth Nat.Prime (i+1)
  have hf : Function.Injective f := by
    intro i j h
    have h' := (Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective h
    omega
  have hs : ∀ p ∈ (Finset.range r).image f, p.Prime := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    exact Nat.prime_nth_prime (i+1)
  have h := card_divisors_prime_finset_product ((Finset.range r).image f) hs
  rw [Finset.prod_image (fun i hi j hj hij => hf hij), Finset.card_image_iff.mpr
    (fun i hi j hj hij => hf hij), Finset.card_range] at h
  exact h

lemma oddPrimorial_gt_one (r : ℕ) (hr : 1 ≤ r) : 1 < oddPrimorial r := by
  have hcard : 2 ≤ (oddPrimorial r).divisors.card := by
    rw [oddPrimorial_divisors_card]
    exact Nat.le_self_pow (by omega) 2
  have hle := Nat.card_divisors_le_self (oddPrimorial r)
  omega


lemma primePrefixProduct_succ_eq_two_mul_oddPrimorial (r : ℕ) :
    primePrefixProduct (r+1) = 2 * oddPrimorial r := by
  rw [primePrefixProduct, Finset.prod_range_succ']
  simp [oddPrimorial, mul_comm]

lemma oddPrimorial_le_primePrefixProduct (r : ℕ) :
    oddPrimorial r ≤ primePrefixProduct (r+1) := by
  rw [primePrefixProduct_succ_eq_two_mul_oddPrimorial]
  omega

/-- A deliberately coarse size bound suffices for the representation-counting argument. -/
lemma eventually_log_log_oddPrimorial_le :
    ∀ᶠ r : ℕ in Filter.atTop,
      Real.log (Real.log (oddPrimorial r : ℝ)) ≤ 4 * Real.log (r : ℝ) := by
  have he := (Filter.tendsto_add_atTop_nat 1).eventually
    (eventually_log_primePrefixProduct_le (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [he, Filter.eventually_ge_atTop 3] with r hr hr3
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr3
  have hQr : 1 < (oddPrimorial r : ℝ) := by
    exact_mod_cast oddPrimorial_gt_one r (by omega)
  have hlogQ : 0 < Real.log (oddPrimorial r : ℝ) := Real.log_pos hQr
  have hlog : Real.log (oddPrimorial r : ℝ) ≤ (r : ℝ)^4 := by
    calc
      Real.log (oddPrimorial r : ℝ) ≤ Real.log (primePrefixProduct (r+1) : ℝ) :=
        Real.log_le_log (by linarith) (by exact_mod_cast oddPrimorial_le_primePrefixProduct r)
      _ ≤ 2 * ((r : ℝ)+1) * Real.log ((r : ℝ)+1) := by
        simpa only [Nat.cast_add, Nat.cast_one, one_add_one_eq_two] using hr
      _ ≤ 2 * ((r : ℝ)+1)^2 := by
        have hh := Real.log_le_self (show 0 ≤ (r : ℝ)+1 by positivity)
        nlinarith
      _ ≤ 8 * (r : ℝ)^2 := by nlinarith
      _ ≤ (r : ℝ)^4 := by
        have hsq : 8 ≤ (r : ℝ)^2 := by nlinarith
        have hh := mul_le_mul_of_nonneg_right hsq (sq_nonneg (r : ℝ))
        nlinarith
  have h := Real.log_le_log hlogQ hlog
  simpa only [Real.log_pow, Nat.cast_ofNat] using h

/-- A supply of odd integers with exponentially many divisors but short double logarithm. -/
theorem eventually_odd_primorial_supply :
    ∀ᶠ r : ℕ in Filter.atTop, ∃ Q : ℕ,
      1 < Q ∧ Odd Q ∧ 2^r ≤ Q.divisors.card ∧
      Real.log (Real.log (Q : ℝ)) ≤ 4 * Real.log (r : ℝ) := by
  filter_upwards [eventually_log_log_oddPrimorial_le, Filter.eventually_ge_atTop 1] with r hr hr1
  exact ⟨oddPrimorial r, oddPrimorial_gt_one r hr1, oddPrimorial_odd r,
    (oddPrimorial_divisors_card r).ge, hr⟩

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_CountingFromMain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
open Filter

namespace Problem337

/-- Appending the complementary unit fraction and cleaning repetitions preserves an odd multiple. -/
theorem marked_multiple_at_minimal_length (Q : ℕ) (hQ : Odd Q) (hQone : 1 < Q) :
    ∃ n : Fin (egyptianLength (Q - 1) Q + 1) → ℕ,
      IsOneExpansion n ∧ ∃ i, Q ∣ n i := by
  have hpos : 1 ≤ Q - 1 := by omega
  have hlt : Q - 1 < Q := by omega
  obtain ⟨n, hn⟩ := egyptianLength_attained_of_exists
    (exists_strict_unit_fraction_sum (Q - 1) Q hpos hlt)
  apply marked_cleanup_exact_length hQ hQone (Fin.cons Q n)
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp; omega
    · simpa using (show 1 ≤ n j from (hn.1 j).trans' (by omega))
  · rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [hn.2.2]
    have hQzero : (Q : ℚ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
    rw [Nat.cast_sub (by omega : 1 ≤ Q)]
    push_cast
    field_simp
    ring
  · exact ⟨0, by simp⟩

/-- The length of the cleaned marked expansion is bounded by the uniform maximum. -/
theorem marked_multiple_length_le_max (Q : ℕ) (hQ : Odd Q) (hQone : 1 < Q) :
    ∃ k : ℕ, ∃ n : Fin k → ℕ, IsOneExpansion n ∧ (∃ i, Q ∣ n i) ∧
      k ≤ maxEgyptianLength Q + 1 := by
  obtain ⟨n, hn, hm⟩ := marked_multiple_at_minimal_length Q hQ hQone
  refine ⟨egyptianLength (Q - 1) Q + 1, n, hn, hm, ?_⟩
  exact Nat.add_le_add_right (egyptianLength_le_max (by omega) (by omega)) 1

/-- Tuple form of divisor branching, avoiding conversion choices in the counting assembly. -/
theorem divisor_branching_from_tuple {k : ℕ} (n : Fin k → ℕ)
    (hn : IsOneExpansion n) (i : Fin k)
    (hfinite : (OneExpansions (k + 1)).Finite) :
    (n i).divisors.card ≤ F (k + 1) + 1 + 2 * (k - 1) := by
  classical
  let s := Finset.univ.image n
  have hcard : s.card = k := by
    dsimp [s]
    rw [Finset.card_image_of_injective _ hn.2.1.injective, Finset.card_univ,
      Fintype.card_fin]
  have his : n i ∈ s := by simp [s]
  have hpos : ∀ d ∈ s, 1 ≤ d := by
    intro d hd
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hd
    exact hn.1 j
  have hsum : (∑ d ∈ s, (1 : ℚ) / d) = 1 := by
    dsimp [s]
    rw [Finset.sum_image (fun i _ j _ h => hn.2.1.injective h)]
    exact hn.2.2
  have hfinite' : (OneExpansions (s.card + 1)).Finite := by rw [hcard]; exact hfinite
  have hc := divisor_branching_lower_bound s (n i) his hpos hsum hfinite'
  rw [hcard] at hc
  omega

/-- Branching on the marked multiple counts at least as many divisors as the marker itself. -/
theorem divisor_branching_from_odd_marker {Q k : ℕ} (hQ : Odd Q) (hQone : 1 < Q)
    (n : Fin k → ℕ) (hn : IsOneExpansion n) (hm : ∃ i, Q ∣ n i)
    (hfinite : (OneExpansions (k + 1)).Finite) :
    3 ≤ k ∧ Q.divisors.card ≤ F (k + 1) + 1 + 2 * (k - 1) := by
  obtain ⟨i, hi⟩ := hm
  have hmi : 3 ≤ n i := odd_marker_denominator_ge_three hQ hQone (hn.1 i) hi
  have hDi : n i ∈ D k := ⟨by omega, n, hn, i, rfl⟩
  refine ⟨marker_length_ge_three hDi, ?_⟩
  have hcard : Q.divisors.card ≤ (n i).divisors.card :=
    Finset.card_le_card (Nat.divisors_subset_of_dvd (by have := hn.1 i; omega) hi)
  exact hcard.trans (divisor_branching_from_tuple n hn i hfinite)

/-- A short odd-marked expansion supplies a lower bound for the number of expansions one term longer. -/
theorem counting_from_uniform_max (Q : ℕ) (hQ : Odd Q) (hQone : 1 < Q)
    (hfinite : ∀ k, (OneExpansions k).Finite) :
    ∃ ell : ℕ, 4 ≤ ell ∧ ell ≤ maxEgyptianLength Q + 2 ∧
      Q.divisors.card ≤ F ell + 2 * ell := by
  obtain ⟨k, n, hn, hm, hk⟩ := marked_multiple_length_le_max Q hQ hQone
  obtain ⟨hkthree, hcount⟩ := divisor_branching_from_odd_marker hQ hQone n hn hm (hfinite _)
  refine ⟨k + 1, by omega, by omega, ?_⟩
  omega

/-- Exponential divisor counts eventually absorb the loss from the finitely many collisions. -/
theorem eventually_collision_budget (B : ℝ) (hB : 0 < B) :
    ∀ᶠ r : ℕ in atTop, 2 * B * Real.log (r : ℝ) ≤ (2 ^ (r - 1) : ℕ) := by
  have hlim : Tendsto (fun r : ℕ => (r : ℝ) / (2 : ℝ) ^ r) atTop (nhds 0) := by
    simpa using (tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1 : ℝ) < 2))
  have hsmall : ∀ᶠ r : ℕ in atTop, (r : ℝ) / (2 : ℝ) ^ r < 1 / (4 * B) :=
    hlim.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hsmall, eventually_ge_atTop 1] with r hr hrone
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hlog : Real.log (r : ℝ) ≤ r := Real.log_le_self (le_of_lt hrpos)
  have hcross := (div_lt_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ r)
    (by positivity : (0 : ℝ) < 4 * B)).mp hr
  have heq : (2 : ℝ) ^ r = 2 * (2 : ℝ) ^ (r - 1) := by
    nth_rw 1 [show r = (r - 1) + 1 by omega]
    rw [pow_succ]
    ring
  push_cast
  rw [heq] at hcross
  nlinarith

/-- Uniform logarithmic lengths and an odd many-divisor supply yield exponentially branching short lengths. -/
theorem short_counting_lengths_of_uniform_upper
    (hfinite : ∀ k, (OneExpansions k).Finite)
    (hupper : ∃ c : ℝ, 0 < c ∧ ∀ᶠ Q : ℕ in atTop,
      (maxEgyptianLength Q : ℝ) ≤ c * Real.log (Real.log (Q : ℝ)))
    (hsupply : ∃ C : ℝ, 0 < C ∧ ∀ᶠ r : ℕ in atTop,
      ∃ Q : ℕ, Odd Q ∧ 1 < Q ∧ 2 ^ r ≤ Q.divisors.card ∧
        Real.log (Real.log (Q : ℝ)) ≤ C * Real.log (r : ℝ)) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ r : ℕ in atTop,
      ∃ ell : ℕ, 2 ≤ ell ∧ (ell : ℝ) ≤ B * Real.log (r : ℝ) ∧
        2 ^ (r - 1) ≤ F ell := by
  obtain ⟨c, hc, hupper⟩ := hupper
  obtain ⟨C, hC, hsupply⟩ := hsupply
  obtain ⟨Q0, hQ0⟩ := eventually_atTop.mp hupper
  let B : ℝ := c * C + 2
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B, hB, ?_⟩
  have hlog : ∀ᶠ r : ℕ in atTop, 1 ≤ Real.log (r : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [hsupply, eventually_collision_budget B hB, hlog,
    eventually_ge_atTop Q0, eventually_ge_atTop 1] with r hr hbudget hlogr hrQ0 hrone
  obtain ⟨Q, hQodd, hQone, hdivisors, hlogQ⟩ := hr
  have hrQ : r ≤ Q := by
    have hp := Nat.lt_two_pow_self (n := r)
    have hd := Nat.card_divisors_le_self Q
    omega
  obtain ⟨ell, helfour, hell, hcount⟩ := counting_from_uniform_max Q hQodd hQone hfinite
  have hmax := hQ0 Q (hrQ0.trans hrQ)
  have hellR : (ell : ℝ) ≤ B * Real.log (r : ℝ) := by
    have hell' : (ell : ℝ) ≤ maxEgyptianLength Q + 2 := by exact_mod_cast hell
    have hmul := mul_le_mul_of_nonneg_left hlogQ hc.le
    dsimp [B]
    nlinarith
  refine ⟨ell, by omega, hellR, ?_⟩
  have hlossR : (2 * ell : ℕ) ≤ (2 ^ (r - 1) : ℕ) := by
    have hreal : (2 : ℝ) * ell ≤ (2 ^ (r - 1) : ℕ) := by nlinarith
    exact_mod_cast hreal
  have hexp : 2 ^ r = 2 ^ (r - 1) * 2 := by
    nth_rw 1 [show r = (r - 1) + 1 by omega]
    rw [pow_succ]
  rw [hexp] at hdivisors
  omega

/-- The odd-primorial many-divisor input is unconditional, so only the main uniform upper
bound remains in the short-counting-length construction. -/
theorem short_counting_lengths_of_main_upper
    (hupper : ∃ c : ℝ, 0 < c ∧ ∀ᶠ Q : ℕ in atTop,
      (maxEgyptianLength Q : ℝ) ≤ c * Real.log (Real.log (Q : ℝ))) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ r : ℕ in atTop,
      ∃ ell : ℕ, 2 ≤ ell ∧ (ell : ℝ) ≤ B * Real.log (r : ℝ) ∧
        2 ^ (r - 1) ≤ F ell := by
  apply short_counting_lengths_of_uniform_upper
  · intro k
    exact (finite_ncard_le_egyptian_box k (OneExpansions k)
      (fun n hn => hn.1) (fun n hn => one_expansion_denominator_bound n hn)).1
  · exact hupper
  · refine ⟨4, by norm_num, ?_⟩
    filter_upwards [eventually_odd_primorial_supply] with r hr
    obtain ⟨Q, hQone, hQodd, hcount, hsize⟩ := hr
    exact ⟨Q, hQodd, hQone, hcount, hsize⟩

/-- The counting order theorem follows from the main uniform upper bound alone;
this route does not use the quantitative prescribed-denominator construction. -/
theorem counting_order_of_main_upper
    (hupper : ∃ c : ℝ, 0 < c ∧ ∀ᶠ Q : ℕ in atTop,
      (maxEgyptianLength Q : ℝ) ≤ c * Real.log (Real.log (Q : ℝ))) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ k0 : ℕ,
      ∀ k : ℕ, k0 ≤ k →
        c * (k : ℝ) ≤ Real.log (Real.log (F k : ℝ)) ∧
        Real.log (Real.log (F k : ℝ)) ≤ C * (k : ℝ) := by
  have hbox (k : ℕ) : (OneExpansions k).Finite ∧ F k ≤ k ^ (2 ^ k - 1) :=
    finite_ncard_le_egyptian_box k (OneExpansions k)
      (fun n hn => hn.1) (fun n hn => one_expansion_denominator_bound n hn)
  obtain ⟨B, hB, hsupply⟩ := short_counting_lengths_of_main_upper hupper
  have hmono : ∀ i j : ℕ, 2 ≤ i → i ≤ j → F i ≤ F j := by
    intro i j hi hij
    exact CountingPadding.F_le_of_le (fun k => (hbox k).1) hi hij
  have hlower := counting_lower_transfer F hB hmono hsupply
  refine ⟨1 / (2 * B), 3, by positivity, by norm_num, ?_⟩
  apply eventually_atTop.mp
  filter_upwards [hlower, eventually_ge_atTop 2] with k hk hk2
  exact ⟨hk, counting_loglog_upper_of_box F (fun k => (hbox k).2) k hk2⟩

end Problem337

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

theorem counting_double_log_order_oai :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ k0 : ℕ,
  ∀ k : ℕ, k0 ≤ k →
    c * (k : ℝ) ≤ Real.log (Real.log (F k : ℝ)) ∧
    Real.log (Real.log (F k : ℝ)) ≤ C * (k : ℝ) := by
  apply counting_order_of_main_upper
  obtain ⟨c1, c2, hc1, hc2, b0, hbounds⟩ := main_double_log_order
  refine ⟨c2, hc2, Filter.eventually_atTop.2 ⟨b0, ?_⟩⟩
  intro b hb
  exact (hbounds b hb).2

end Problem337

end

end OAI
end

theorem solution : type_of% @OAI.Problem337.counting_double_log_order_oai := @OAI.Problem337.counting_double_log_order_oai
