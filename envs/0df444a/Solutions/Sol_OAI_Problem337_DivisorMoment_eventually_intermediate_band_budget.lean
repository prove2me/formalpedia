-- Prove2me | solution 1 for OAI.Problem337.DivisorMoment.eventually_intermediate_band_budget
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T10:05:41.777293+00:00
-- url     : https://prove2.me/submissions/ec63dfff-fe91-4603-a030-68564c377c4b

import Mathlib
import Definitions.Def_OAIQ8EF000

section
-- module Solutions.OAIQ8_EF.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_DivisorBandDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open Filter
open scoped Topology

namespace Problem337.DivisorMoment

/-- The slowly varying coefficient in the prime-prefix band estimate is negligible
    compared with the logarithm of the band parameter. -/
theorem tendsto_loglog_coefficient (r K : ℝ) :
    Tendsto (fun v : ℝ => r * (K + Real.log (Real.log v)) / Real.log v)
      atTop (𝓝 0) := by
  have hc : Tendsto (fun v : ℝ => K / Real.log v) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have hl : Tendsto (fun v : ℝ => Real.log (Real.log v) / Real.log v) atTop (𝓝 0) :=
    (Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop).tendsto_div_nhds_zero
  have hh := (hc.add hl).const_mul r
  simp only [add_zero, mul_zero] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext v
  ring

/-- Uniform domination of the two positive errors in an intermediate-prime band. -/
theorem eventually_intermediate_band_decay (r C K : ℝ) (hr : 0 ≤ r) (hC : 0 ≤ C) :
    ∀ᶠ v : ℝ in atTop, ∀ Q t B : ℝ,
      v ^ (1 / 16 : ℝ) ≤ Q → 0 < t → t ≤ v →
      B ≤ K + Real.log (Real.log v) →
      r * B * Q - Q * Real.log Q / 50 +
        C * Q ^ (1 / 5 : ℝ) * Real.log (2 * t) ≤ -Q * Real.log Q / 100 := by
  have hsmall : ∀ᶠ v : ℝ in atTop,
      r * (K + Real.log (Real.log v)) / Real.log v ≤ (1 / 3200 : ℝ) :=
    (tendsto_loglog_coefficient r K).eventually (eventually_le_nhds (by norm_num))
  have hpower : ∀ᶠ v : ℝ in atTop,
      6400 * C ≤ (v ^ (1 / 16 : ℝ)) ^ (4 / 5 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 4 / 5)).comp
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 16))).eventually
        (eventually_ge_atTop (6400 * C))
  filter_upwards [hsmall, hpower, eventually_ge_atTop (2 : ℝ)] with v hvsmall hvpower hv2
  intro Q t B hQ ht htv hB
  have hvpos : 0 < v := by linarith
  have hvlog : 0 < Real.log v := Real.log_pos (by linarith)
  have hvrootpos : 0 < v ^ (1 / 16 : ℝ) := Real.rpow_pos_of_pos hvpos _
  have hQpos : 0 < Q := hvrootpos.trans_le hQ
  have hQlog : (1 / 16 : ℝ) * Real.log v ≤ Real.log Q := by
    calc
      _ = Real.log (v ^ (1 / 16 : ℝ)) := (Real.log_rpow hvpos _).symm
      _ ≤ Real.log Q := Real.log_le_log hvrootpos hQ
  have hlogQpos : 0 < Real.log Q := by nlinarith
  have hBsmall : r * B ≤ Real.log Q / 200 := by
    have hh := (div_le_iff₀ hvlog).mp hvsmall
    have hb' : r * B ≤ r * (K + Real.log (Real.log v)) :=
      mul_le_mul_of_nonneg_left hB hr
    nlinarith
  have hlogtwo : Real.log 2 ≤ Real.log v :=
    Real.log_le_log (by norm_num) hv2
  have htlog : Real.log (2 * t) ≤ 32 * Real.log Q := by
    have hh : Real.log (2 * t) ≤ Real.log (2 * v) :=
      Real.log_le_log (by positivity) (by nlinarith)
    rw [Real.log_mul (by norm_num) hvpos.ne'] at hh
    nlinarith
  have hQpower : 6400 * C ≤ Q ^ (4 / 5 : ℝ) :=
    hvpower.trans (Real.rpow_le_rpow hvrootpos.le hQ (by norm_num))
  have hQfifth : 0 ≤ Q ^ (1 / 5 : ℝ) := (Real.rpow_pos_of_pos hQpos _).le
  have hQpowers : Q ^ (4 / 5 : ℝ) * Q ^ (1 / 5 : ℝ) = Q := by
    rw [← Real.rpow_add hQpos]
    norm_num
  have hscale : 6400 * C * Q ^ (1 / 5 : ℝ) ≤ Q := by
    nlinarith [mul_le_mul_of_nonneg_right hQpower hQfifth]
  have herror : C * Q ^ (1 / 5 : ℝ) * Real.log (2 * t) ≤ Q * Real.log Q / 200 := by
    have hll := mul_le_mul_of_nonneg_left htlog (mul_nonneg hC hQfifth)
    have hss := mul_le_mul_of_nonneg_right hscale hlogQpos.le
    nlinarith
  have hmain := mul_le_mul_of_nonneg_right hBsmall hQpos.le
  nlinarith

/-- The intermediate-prime exponent is uniformly negative over all
    admissible logarithmic scales. Only the lower bound on `v` is needed. -/
theorem eventually_uniform_intermediate_band_decay (E r C : ℝ)
    (hE : 2 ≤ E) (hr : 0 ≤ r) (hC : 0 ≤ C) :
    ∀ᶠ S : ℝ in atTop, ∀ v t : ℝ,
      S / (2 * Real.log S) ≤ v → 0 < t → t ≤ v ^ (15 / 16 : ℝ) →
      r * (1 + Real.log (E * S / v)) * (v / t) -
        (v / t) * Real.log (v / t) / 50 +
        C * (v / t) ^ (1 / 5 : ℝ) * Real.log (2 * t) ≤
          -(v / t) * Real.log (v / t) / 100 := by
  obtain ⟨V, hV⟩ := eventually_atTop.mp
    (eventually_intermediate_band_decay r C (1 + Real.log (4 * E)) hr hC)
  have hroot : ∀ᶠ S : ℝ in atTop, max 2 V ≤ S ^ (1 / 2 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).eventually
      (eventually_ge_atTop (max 2 V))
  have hlogsmall : ∀ᶠ S : ℝ in atTop,
      ‖Real.log S‖ ≤ (1 / 2 : ℝ) * ‖S ^ (1 / 2 : ℝ)‖ :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).def (by norm_num)
  filter_upwards [hroot, hlogsmall, eventually_ge_atTop (2 : ℝ)] with S hroot hlogsmall hS
  intro v t hv ht htv
  have hSpos : 0 < S := by linarith
  have hlogS : 0 < Real.log S := Real.log_pos (by linarith)
  have hrootpos : 0 < S ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hSpos _
  have hrootsq : S ^ (1 / 2 : ℝ) * S ^ (1 / 2 : ℝ) = S := by
    rw [← Real.rpow_add hSpos]
    norm_num
  have hsmall : 2 * Real.log S ≤ S ^ (1 / 2 : ℝ) := by
    simpa only [Real.norm_eq_abs, abs_of_pos hlogS, abs_of_pos hrootpos] using
      (show 2 * ‖Real.log S‖ ≤ ‖S ^ (1 / 2 : ℝ)‖ by linarith)
  have hrootle : S ^ (1 / 2 : ℝ) ≤ S / (2 * Real.log S) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * Real.log S)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hsmall hrootpos.le]
  have hvroot : S ^ (1 / 2 : ℝ) ≤ v := hrootle.trans hv
  have hv2 : 2 ≤ v := (le_max_left 2 V).trans (hroot.trans hvroot)
  have hVv : V ≤ v := (le_max_right 2 V).trans (hroot.trans hvroot)
  have hvpos : 0 < v := by linarith
  have hlogv : 0 < Real.log v := Real.log_pos (by linarith)
  have hlogs : Real.log S ≤ 2 * Real.log v := by
    have hh := Real.log_le_log hrootpos hvroot
    rw [Real.log_rpow hSpos] at hh
    linarith
  have hratio : E * S / v ≤ 4 * E * Real.log v := by
    have hbase := (div_le_iff₀ (by positivity : 0 < 2 * Real.log S)).mp hv
    have hEpos : 0 < E := by linarith
    apply (div_le_iff₀ hvpos).mpr
    have hb := mul_le_mul_of_nonneg_left hbase hEpos.le
    have hl := mul_le_mul_of_nonneg_left hlogs (by positivity : 0 ≤ 2 * E * v)
    nlinarith
  have hB : 1 + Real.log (E * S / v) ≤
      (1 + Real.log (4 * E)) + Real.log (Real.log v) := by
    have hh := Real.log_le_log (by positivity : 0 < E * S / v) hratio
    rw [Real.log_mul (by positivity : 4 * E ≠ 0) hlogv.ne'] at hh
    linarith
  have htv' : t ≤ v := by
    calc
      t ≤ v ^ (15 / 16 : ℝ) := htv
      _ ≤ v ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = v := Real.rpow_one v
  have hQ : v ^ (1 / 16 : ℝ) ≤ v / t := by
    apply (le_div_iff₀ ht).mpr
    have hh := mul_le_mul_of_nonneg_left htv
      (Real.rpow_pos_of_pos hvpos (1 / 16 : ℝ)).le
    have heq : v ^ (1 / 16 : ℝ) * v ^ (15 / 16 : ℝ) = v := by
      rw [← Real.rpow_add hvpos]
      norm_num
    exact hh.trans_eq heq
  exact hV v hVv (v / t) t (1 + Real.log (E * S / v)) hQ ht htv' hB

end Problem337.DivisorMoment

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_DivisorFactorBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- Splitting a divisor at its gcd with a fixed factor loses no information. -/
theorem divisor_gcd_pair_injective (d : ℕ) :
    Function.Injective (fun a : ℕ => (Nat.gcd a d, a / Nat.gcd a d)) := by
  intro a b hab
  have h := congrArg (fun p : ℕ × ℕ => p.1 * p.2) hab
  simpa only [Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)] using h

/-- The factor remaining after taking a gcd divides the complementary factor. -/
theorem divisor_div_gcd_dvd_quotient {a d n : ℕ} (ha : a ∣ n) (hd : d ∣ n) :
    a / Nat.gcd a d ∣ n / d := by
  apply (Nat.dvd_div_iff_mul_dvd hd).2
  have h := Nat.lcm_dvd ha hd
  rw [Nat.lcm_eq_mul_div, Nat.mul_comm a d,
    Nat.mul_div_assoc d (Nat.gcd_dvd_left a d)] at h
  exact h

/-- The truncated divisor count is submultiplicative across any factorization;
    the factors need not be coprime. -/
theorem truncatedDivisorCount_factor_bound (X : ℝ) {d n : ℕ} (hd : d ∣ n) :
    truncatedDivisorCount X n ≤ d.divisors.card * truncatedDivisorCount X (n / d) := by
  by_cases hn : n = 0
  · simp [truncatedDivisorCount, hn]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hnpos
  have hquot : n / d ≠ 0 := Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd hnpos hd) hdpos)
  unfold truncatedDivisorCount
  rw [← Finset.card_product]
  apply Finset.card_le_card_of_injOn (fun a : ℕ => (Nat.gcd a d, a / Nat.gcd a d))
  · intro a ha
    obtain ⟨ha, haX⟩ := Finset.mem_filter.mp ha
    have hadvd : a ∣ n := (Nat.mem_divisors.mp ha).1
    apply Finset.mem_product.mpr
    constructor
    · exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right a d, Nat.ne_of_gt hdpos⟩
    · apply Finset.mem_filter.mpr
      constructor
      · exact Nat.mem_divisors.mpr ⟨divisor_div_gcd_dvd_quotient hadvd hd, hquot⟩
      · exact le_trans (by exact_mod_cast Nat.div_le_self a (Nat.gcd a d)) haX
  · exact (divisor_gcd_pair_injective d).injOn

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_DivisorLocalFactor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace Problem337.DivisorMoment

/-- Polynomially weighted geometric series, with the indexing used by the
nonconstant terms of an Euler factor. -/
theorem summable_shifted_pow_geometric (r : ℕ) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    Summable (fun j : ℕ => ((j : ℝ) + 2) ^ r * ρ ^ j) := by
  have hn : ‖ρ‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_pos hρ0] using hρ1
  have hbase := summable_pow_mul_geometric_of_norm_lt_one r hn
  have hshift := (summable_nat_add_iff 2).mpr hbase
  have hscaled := hshift.mul_left ((ρ ^ 2)⁻¹)
  apply hscaled.congr
  intro j
  simp only [Nat.cast_add, Nat.cast_ofNat, pow_add]
  field_simp

/-- All nonconstant coefficients of the Euler factor have a uniform linear
majorant on any fixed compact subinterval of the geometric convergence disk. -/
theorem local_factor_linear_bound (r : ℕ) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 ≤ x → x ≤ ρ →
      Summable (fun j : ℕ => ((j : ℝ) + 2) ^ r * x ^ (j + 1)) ∧
      (∑' j : ℕ, ((j : ℝ) + 2) ^ r * x ^ (j + 1)) ≤ C * x ∧
      Real.log (1 + ∑' j : ℕ, ((j : ℝ) + 2) ^ r * x ^ (j + 1)) ≤ C * x := by
  let A : ℝ := ∑' j : ℕ, ((j : ℝ) + 2) ^ r * ρ ^ j
  have hA0 : 0 ≤ A := tsum_nonneg (fun j => by positivity)
  have hsρ := summable_shifted_pow_geometric r hρ0 hρ1
  refine ⟨A + 1, by positivity, ?_⟩
  intro x hx0 hxρ
  have hle : ∀ j : ℕ, ((j : ℝ) + 2) ^ r * x ^ j ≤
      ((j : ℝ) + 2) ^ r * ρ ^ j := by
    intro j
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx0 hxρ j) (by positivity)
  have hsx : Summable (fun j : ℕ => ((j : ℝ) + 2) ^ r * x ^ j) :=
    Summable.of_nonneg_of_le (fun j => by positivity) hle hsρ
  have hsum : (∑' j : ℕ, ((j : ℝ) + 2) ^ r * x ^ j) ≤ A :=
    Summable.tsum_le_tsum hle hsx hsρ
  have hsnext : Summable (fun j : ℕ => ((j : ℝ) + 2) ^ r * x ^ (j + 1)) := by
    simpa only [pow_succ, mul_assoc] using hsx.mul_right x
  have heq : (∑' j : ℕ, ((j : ℝ) + 2) ^ r * x ^ (j + 1)) =
      (∑' j : ℕ, ((j : ℝ) + 2) ^ r * x ^ j) * x := by
    simpa only [pow_succ, mul_assoc] using hsx.tsum_mul_right x
  have hbound : (∑' j : ℕ, ((j : ℝ) + 2) ^ r * x ^ (j + 1)) ≤ (A + 1) * x := by
    rw [heq]
    exact mul_le_mul_of_nonneg_right (hsum.trans (by linarith)) hx0
  refine ⟨hsnext, hbound, ?_⟩
  have hnonneg : 0 ≤ ∑' j : ℕ, ((j : ℝ) + 2) ^ r * x ^ (j + 1) :=
    tsum_nonneg (fun j => by positivity)
  have hlog := Real.log_le_sub_one_of_pos (by linarith :
    0 < 1 + ∑' j : ℕ, ((j : ℝ) + 2) ^ r * x ^ (j + 1))
  linarith

/-- Real moments are reduced to a larger integral moment, uniformly in x. -/
theorem local_factor_real_moment_bound (r : ℝ) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 ≤ x → x ≤ ρ →
      Summable (fun j : ℕ => ((j : ℝ) + 2) ^ r * x ^ (j + 1)) ∧
      (∑' j : ℕ, ((j : ℝ) + 2) ^ r * x ^ (j + 1)) ≤ C * x ∧
      Real.log (1 + ∑' j : ℕ, ((j : ℝ) + 2) ^ r * x ^ (j + 1)) ≤ C * x := by
  obtain ⟨R, hR⟩ := exists_nat_gt r
  obtain ⟨C, hC, hbound⟩ := local_factor_linear_bound R hρ0 hρ1
  refine ⟨C, hC, ?_⟩
  intro x hx0 hxρ
  obtain ⟨hsR, hsumR, _⟩ := hbound x hx0 hxρ
  have hle : ∀ j : ℕ, ((j : ℝ) + 2) ^ r * x ^ (j + 1) ≤
      ((j : ℝ) + 2) ^ R * x ^ (j + 1) := by
    intro j
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by have hj := Nat.cast_nonneg (α := ℝ) j; linarith) hR.le
  have hs : Summable (fun j : ℕ => ((j : ℝ) + 2) ^ r * x ^ (j + 1)) :=
    Summable.of_nonneg_of_le (fun j => by positivity) hle hsR
  have hsum : (∑' j : ℕ, ((j : ℝ) + 2) ^ r * x ^ (j + 1)) ≤ C * x :=
    (Summable.tsum_le_tsum hle hs hsR).trans hsumR
  refine ⟨hs, hsum, ?_⟩
  have hnonneg : 0 ≤ ∑' j : ℕ, ((j : ℝ) + 2) ^ r * x ^ (j + 1) :=
    tsum_nonneg (fun j => by positivity)
  have hlog := Real.log_le_sub_one_of_pos (by linarith :
    0 < 1 + ∑' j : ℕ, ((j : ℝ) + 2) ^ r * x ^ (j + 1))
  linarith

/-- Uniform local Euler-factor bound. Primality is unnecessary; p≥2 is enough.
The range σ≤1 can also be omitted from this local estimate. -/
theorem divisor_local_factor_bound (r : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p σ : ℝ, 2 ≤ p → (3 / 4 : ℝ) ≤ σ →
      Summable (fun j : ℕ => ((j : ℝ) + 2) ^ r * (p ^ (-σ)) ^ (j + 1)) ∧
      Real.log (1 + ∑' j : ℕ, ((j : ℝ) + 2) ^ r * (p ^ (-σ)) ^ (j + 1)) ≤
        C * p ^ (-σ) := by
  let ρ : ℝ := (2 : ℝ) ^ (-(3 / 4 : ℝ))
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos (by norm_num) _
  have hρ1 : ρ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  obtain ⟨C, hC, hbound⟩ := local_factor_real_moment_bound r hρ0 hρ1
  refine ⟨C, hC, ?_⟩
  intro p σ hp hσ
  have hx0 : 0 ≤ p ^ (-σ) := (Real.rpow_pos_of_pos (by linarith : 0 < p) _).le
  have hxρ : p ^ (-σ) ≤ ρ := by
    calc
      p ^ (-σ) ≤ (2 : ℝ) ^ (-σ) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hp (by linarith)
      _ ≤ (2 : ℝ) ^ (-(3 / 4 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  obtain ⟨hs, _, hl⟩ := hbound (p ^ (-σ)) hx0 hxρ
  exact ⟨hs, hl⟩

/-- Convert the shifted nonconstant series to the full Euler factor and
all its finite partial sums. -/
theorem full_local_factor_bounds {r x B : ℝ} (hx : 0 ≤ x)
    (hs : Summable (fun j : ℕ => ((j : ℝ) + 2) ^ r * x ^ (j + 1)))
    (hlog : Real.log (1 + ∑' j : ℕ, ((j : ℝ) + 2) ^ r * x ^ (j + 1)) ≤ B) :
    Summable (fun j : ℕ => ((j : ℝ) + 1) ^ r * x ^ j) ∧
    Real.log (∑' j : ℕ, ((j : ℝ) + 1) ^ r * x ^ j) ≤ B ∧
    ∀ L : ℕ, Real.log (∑ j ∈ Finset.range (L + 1),
      ((j : ℝ) + 1) ^ r * x ^ j) ≤ B := by
  have hsfull : Summable (fun j : ℕ => ((j : ℝ) + 1) ^ r * x ^ j) := by
    apply (summable_nat_add_iff 1).mp
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hs
  have hfull : Real.log (∑' j : ℕ, ((j : ℝ) + 1) ^ r * x ^ j) ≤ B := by
    rw [hsfull.tsum_eq_zero_add]
    simpa only [Nat.cast_zero, zero_add, Real.one_rpow, pow_zero, one_mul,
      Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hlog
  refine ⟨hsfull, hfull, ?_⟩
  intro L
  have hpos : 0 < ∑ j ∈ Finset.range (L + 1), ((j : ℝ) + 1) ^ r * x ^ j := by
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_add, Real.one_rpow, pow_zero, one_mul]
    have hn : 0 ≤ ∑ j ∈ Finset.range L, (((j + 1 : ℕ) : ℝ) + 1) ^ r * x ^ (j + 1) :=
      Finset.sum_nonneg (fun j _ => by positivity)
    linarith
  exact (Real.log_le_log hpos
    (hsfull.sum_le_tsum (Finset.range (L + 1)) (fun j _ => by positivity))).trans hfull

/-- Full and finite Euler factors, with a uniform constant for every real
moment and every σ≥3/4. This is convenient for both finite and infinite
Euler-product arguments. -/
theorem divisor_full_local_factor_bound (r : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p σ : ℝ, 2 ≤ p → (3 / 4 : ℝ) ≤ σ →
      Summable (fun j : ℕ => ((j : ℝ) + 1) ^ r * (p ^ (-σ)) ^ j) ∧
      Real.log (∑' j : ℕ, ((j : ℝ) + 1) ^ r * (p ^ (-σ)) ^ j) ≤ C * p ^ (-σ) ∧
      ∀ L : ℕ, Real.log (∑ j ∈ Finset.range (L + 1),
        ((j : ℝ) + 1) ^ r * (p ^ (-σ)) ^ j) ≤ C * p ^ (-σ) := by
  obtain ⟨C, hC, hfactor⟩ := divisor_local_factor_bound r
  refine ⟨C, hC, ?_⟩
  intro p σ hp hσ
  obtain ⟨hs, hl⟩ := hfactor p σ hp hσ
  exact full_local_factor_bounds (Real.rpow_nonneg (by linarith) _) hs hl

end Problem337.DivisorMoment

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_TruncatedDivisors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace Problem337.DivisorMoment

/-- Multiples of a positive integer in a translated interval satisfy the
uniform counting estimate needed for short-interval divisor moments. -/
theorem interval_multiples_card_le (N Y d : ℕ) (hd : 0 < d) :
    ((Finset.Ioc N (N + Y)).filter (fun a => d ∣ a)).card ≤ Y / d + 1 := by
  have hcard : ((Finset.Ioc N (N + Y)).filter (fun a => d ∣ a)).card ≤
      (Finset.Ioc (N / d) ((N + Y) / d)).card := by
    apply Finset.card_le_card_of_injOn (fun a : ℕ => a / d)
    · intro a ha
      obtain ⟨haI, had⟩ := Finset.mem_filter.mp ha
      obtain ⟨hNa, haNY⟩ := Finset.mem_Ioc.mp haI
      apply Finset.mem_Ioc.mpr
      constructor
      · apply (Nat.div_lt_iff_lt_mul hd).mpr
        simpa only [Nat.div_mul_cancel had] using hNa
      · exact Nat.div_le_div_right haNY
    · intro a ha b hb hab
      have had := (Finset.mem_filter.mp ha).2
      have hbd := (Finset.mem_filter.mp hb).2
      have h := congrArg (fun q => q * d) hab
      simpa only [Nat.div_mul_cancel had, Nat.div_mul_cancel hbd] using h
  rw [Nat.card_Ioc, Nat.add_div hd] at hcard
  split_ifs at hcard
  · simpa only [Nat.add_assoc, Nat.add_sub_cancel_left] using hcard
  · have h : ((Finset.Ioc N (N + Y)).filter (fun a => d ∣ a)).card ≤ Y / d := by
      simpa only [Nat.add_zero, Nat.add_sub_cancel_left] using hcard
    exact h.trans (Nat.le_succ _)

theorem interval_multiples_card_le_real (N Y d : ℕ) (hd : 0 < d) :
    (((Finset.Ioc N (N + Y)).filter (fun a => d ∣ a)).card : ℝ) ≤
      (Y : ℝ) / d + 1 := by
  calc
    _ ≤ ((Y / d + 1 : ℕ) : ℝ) := by
      exact_mod_cast interval_multiples_card_le N Y d hd
    _ = ((Y / d : ℕ) : ℝ) + 1 := by norm_cast
    _ ≤ (Y : ℝ) / d + 1 := by
      have hcast : ((Y / d : ℕ) : ℝ) ≤ (Y : ℝ) / d := Nat.cast_div_le
      linarith

theorem interval_multiples_card_le_twice (N Y d : ℕ) (hd : 0 < d)
    (hdY : d ≤ Y) :
    (((Finset.Ioc N (N + Y)).filter (fun a => d ∣ a)).card : ℝ) ≤
      2 * (Y : ℝ) / d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hratio : (1 : ℝ) ≤ (Y : ℝ) / d := by
    apply (le_div_iff₀ hdR).mpr
    simpa only [one_mul] using (show (d : ℝ) ≤ Y by exact_mod_cast hdY)
  calc
    _ ≤ (Y : ℝ) / d + 1 := interval_multiples_card_le_real N Y d hd
    _ ≤ 2 * ((Y : ℝ) / d) := by linarith
    _ = 2 * (Y : ℝ) / d := by ring

end Problem337.DivisorMoment

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_DivisorPrefixCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped BigOperators
namespace Problem337.DivisorMoment

/-- Weighted counting for divisors assigned to integers in a translated
interval. The pfx map need not be injective or canonical. -/
theorem sum_le_assigned_divisor_majorant
    (N Y : ℕ) (A D : Finset ℕ) (pfx : ℕ → ℕ) (w a : ℕ → ℝ)
    (hA : A ⊆ Finset.Ioc N (N + Y))
    (hmap : ∀ n ∈ A, pfx n ∈ D)
    (hdvd : ∀ n ∈ A, pfx n ∣ n)
    (hweight : ∀ n ∈ A, w n ≤ a (pfx n))
    (ha : ∀ d ∈ D, 0 ≤ a d)
    (hD : ∀ d ∈ D, 0 < d ∧ d ≤ Y) :
    (∑ n ∈ A, w n) ≤ 2 * (Y : ℝ) * ∑ d ∈ D, a d / d := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to hmap w, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  have hfiber : (A.filter (fun n => pfx n = d)) ⊆
      ((Finset.Ioc N (N + Y)).filter (fun n => d ∣ n)) := by
    intro n hn
    obtain ⟨hnA, hnd⟩ := Finset.mem_filter.mp hn
    apply Finset.mem_filter.mpr
    refine ⟨hA hnA, ?_⟩
    simpa only [hnd] using hdvd n hnA
  have hcard : ((A.filter (fun n => pfx n = d)).card : ℝ) ≤
      2 * (Y : ℝ) / d := by
    calc
      _ ≤ (((Finset.Ioc N (N + Y)).filter (fun n => d ∣ n)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hfiber
      _ ≤ _ := interval_multiples_card_le_twice N Y d (hD d hd).1 (hD d hd).2
  calc
    (∑ n ∈ A with pfx n = d, w n) ≤
        ∑ _n ∈ A with pfx _n = d, a d := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨hnA, hnd⟩ := Finset.mem_filter.mp hn
      simpa only [hnd] using hweight n hnA
    _ = ((A.filter (fun n => pfx n = d)).card : ℝ) * a d := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * (Y : ℝ) / d) * a d :=
      mul_le_mul_of_nonneg_right hcard (ha d hd)
    _ = 2 * (Y : ℝ) * (a d / d) := by ring

/-- A choice-free formulation: every integer only needs some admissible
pfx divisor, with a uniform nonnegative majorant indexed by that divisor. -/
theorem sum_le_divisor_majorant
    (N Y : ℕ) (A D : Finset ℕ) (w a : ℕ → ℝ)
    (hA : A ⊆ Finset.Ioc N (N + Y))
    (hassign : ∀ n ∈ A, ∃ d ∈ D, d ∣ n ∧ w n ≤ a d)
    (ha : ∀ d ∈ D, 0 ≤ a d)
    (hD : ∀ d ∈ D, 0 < d ∧ d ≤ Y) :
    (∑ n ∈ A, w n) ≤ 2 * (Y : ℝ) * ∑ d ∈ D, a d / d := by
  classical
  choose pfx hpD hpdvd hpw using fun n : A => hassign n n.property
  let p : ℕ → ℕ := fun n => if hn : n ∈ A then pfx ⟨n, hn⟩ else 0
  apply sum_le_assigned_divisor_majorant N Y A D p w a hA
  · intro n hn
    simpa only [p, dite_eq_left hn] using hpD ⟨n, hn⟩
  · intro n hn
    simpa only [p, dite_eq_left hn] using hpdvd ⟨n, hn⟩
  · intro n hn
    simpa only [p, dite_eq_left hn] using hpw ⟨n, hn⟩
  · exact ha
  · exact hD

/-- The short interval may have a real length, as in the uniform divisor
moment statement. No rounding loss is introduced. -/
theorem sum_le_divisor_majorant_real_cutoff
    (N : ℕ) (Y : ℝ) (A D : Finset ℕ) (w a : ℕ → ℝ) (hY : 0 ≤ Y)
    (hA : A ⊆ Finset.Ioc N (N + ⌊Y⌋₊))
    (hassign : ∀ n ∈ A, ∃ d ∈ D, d ∣ n ∧ w n ≤ a d)
    (ha : ∀ d ∈ D, 0 ≤ a d)
    (hD : ∀ d ∈ D, 0 < d ∧ (d : ℝ) ≤ Y) :
    (∑ n ∈ A, w n) ≤ 2 * Y * ∑ d ∈ D, a d / d := by
  have hbound := sum_le_divisor_majorant N ⌊Y⌋₊ A D w a hA hassign ha
    (fun d hd => ⟨(hD d hd).1, Nat.le_floor (hD d hd).2⟩)
  apply hbound.trans
  apply mul_le_mul_of_nonneg_right
  · exact mul_le_mul_of_nonneg_left (Nat.floor_le hY) (by norm_num)
  · exact Finset.sum_nonneg (fun d hd => div_nonneg (ha d hd) (Nat.cast_nonneg d))

end Problem337.DivisorMoment

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_PrimeReciprocalSharp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open Filter Finset Set MeasureTheory
open scoped Topology BigOperators

namespace Problem337

/-- The elementary integral estimate for the real zeta series. -/
theorem nat_rpow_series_le {s : ℝ} (hs : 1 < s) :
    (∑' n : ℕ, (n : ℝ) ^ (-s)) ≤ 1 + 1 / (s - 1) := by
  have hsneg : -s < -1 := by linarith
  have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (-s)) :=
    Real.summable_nat_rpow.mpr hsneg
  have hsumshift : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-s)) :=
    (summable_nat_add_iff 1).mpr hsum
  have htail : (∑' n : ℕ, ((n + 1 + 1 : ℕ) : ℝ) ^ (-s)) ≤ 1 / (s - 1) := by
    have hanti : AntitoneOn (fun x : ℝ => x ^ (-s)) (Set.Ici (1 : ℝ)) := by
      intro x hx y hy hxy
      exact Real.rpow_le_rpow_of_nonpos (by have hx1 : 1 ≤ x := hx; linarith) hxy (by linarith)
    have h := AntitoneOn.tsum_comp_add_le_integral (f := fun x : ℝ => x ^ (-s)) 1
      (by simpa using hanti)
      (integrableOn_Ioi_rpow_of_lt hsneg (by norm_num))
      (by
        intro x hx
        apply Real.rpow_nonneg
        have hx1 : (1 : ℝ) < x := by simpa using hx
        linarith)
    rw [integral_Ioi_rpow_of_lt hsneg (by norm_num)] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    norm_num
    rw [show -s + 1 = -(s - 1) by ring, div_neg]
    ring
  rw [hsum.tsum_eq_zero_add, hsumshift.tsum_eq_zero_add]
  simp only [Nat.cast_zero, Nat.cast_one, Real.zero_rpow (by linarith : -s ≠ 0),
    Real.one_rpow, zero_add]
  exact add_le_add_right htail 1

/-- A finite-prime Euler-product estimate, without any prime-distribution input. -/
theorem prime_rpow_sum_le_log_zeta_bound (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {s : ℝ} (hs : 1 < s) :
    (∑ p ∈ P, (p : ℝ) ^ (-s)) ≤ Real.log (1 + 1 / (s - 1)) := by
  let f : ℕ →* ℝ :=
    { toFun := fun n => (n : ℝ) ^ (-s)
      map_one' := by simp
      map_mul' := by
        intro m n
        simp only [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)] }
  have hsum : Summable f := Real.summable_nat_rpow.mpr (by linarith)
  have hprod : (∏ p ∈ P, (1 - (p : ℝ) ^ (-s))⁻¹) ≤ 1 + 1 / (s - 1) := by
    calc
      (∏ p ∈ P, (1 - (p : ℝ) ^ (-s))⁻¹) =
          ∑' n : Nat.factoredNumbers P, (n.val : ℝ) ^ (-s) := by
        simpa [f, Finset.filter_true_of_mem hP] using
          (EulerProduct.prod_filter_prime_geometric_eq_tsum_factoredNumbers hsum P)
      _ ≤ ∑' n : ℕ, (n : ℝ) ^ (-s) :=
        Summable.tsum_subtype_le _ _ (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _) hsum
      _ ≤ 1 + 1 / (s - 1) := nat_rpow_series_le hs
  have hfactor : ∀ p ∈ P, 0 < 1 - (p : ℝ) ^ (-s) := by
    intro p hp
    apply sub_pos.mpr
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (hP p hp).one_lt) (by linarith)
  calc
    (∑ p ∈ P, (p : ℝ) ^ (-s)) ≤ ∑ p ∈ P, Real.log ((1 - (p : ℝ) ^ (-s))⁻¹) := by
      apply Finset.sum_le_sum
      intro p hp
      rw [Real.log_inv]
      have := Real.log_le_sub_one_of_pos (hfactor p hp)
      linarith
    _ = Real.log (∏ p ∈ P, (1 - (p : ℝ) ^ (-s))⁻¹) := by
      apply (Real.log_prod _).symm
      intro p hp
      exact inv_ne_zero (ne_of_gt (hfactor p hp))
    _ ≤ Real.log (1 + 1 / (s - 1)) :=
      Real.log_le_log (Finset.prod_pos (fun p hp => inv_pos.mpr (hfactor p hp))) hprod

/-- The elementary logarithmic bound for reciprocals of primes in a finite interval. -/
theorem prime_reciprocal_sum_le (P : Finset ℕ) (T : ℝ) (hT : 2 ≤ T)
    (hP : ∀ p ∈ P, p.Prime) (hcap : ∀ p ∈ P, (p : ℝ) ≤ T) :
    (∑ p ∈ P, 1 / (p : ℝ)) ≤ Real.exp 1 * Real.log (1 + Real.log T) := by
  have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
  let s : ℝ := 1 + 1 / Real.log T
  have hs : 1 < s := by
    dsimp [s]
    have : 0 < 1 / Real.log T := one_div_pos.mpr hlogT
    linarith
  have hterm : ∀ p ∈ P, 1 / (p : ℝ) ≤ Real.exp 1 * (p : ℝ) ^ (-s) := by
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
    have hpdelta : (p : ℝ) ^ (1 / Real.log T) ≤ Real.exp 1 := by
      rw [Real.rpow_def_of_pos hp0]
      apply Real.exp_le_exp.mpr
      have hlog := Real.log_le_log hp0 (hcap p hp)
      have := (div_le_one hlogT).2 hlog
      simpa only [div_eq_mul_inv, one_mul] using this
    have hpow : (p : ℝ) ^ s ≤ Real.exp 1 * (p : ℝ) := by
      dsimp [s]
      rw [Real.rpow_add hp0, Real.rpow_one]
      nlinarith
    rw [Real.rpow_neg hp0.le, ← div_eq_mul_inv]
    exact (div_le_div_iff₀ hp0 (Real.rpow_pos_of_pos hp0 s)).2 (by simpa using hpow)
  calc
    (∑ p ∈ P, 1 / (p : ℝ)) ≤ ∑ p ∈ P, Real.exp 1 * (p : ℝ) ^ (-s) :=
      Finset.sum_le_sum hterm
    _ = Real.exp 1 * ∑ p ∈ P, (p : ℝ) ^ (-s) := by rw [Finset.mul_sum]
    _ ≤ Real.exp 1 * Real.log (1 + 1 / (s - 1)) :=
      mul_le_mul_of_nonneg_left (prime_rpow_sum_le_log_zeta_bound P hP hs) (Real.exp_pos 1).le
    _ = Real.exp 1 * Real.log (1 + Real.log T) := by
      simp [s]

/-- The weighted variant used in the smooth-prefix divisor estimate. -/
theorem prime_weighted_reciprocal_sum_le (P : Finset ℕ) (T δ : ℝ)
    (hT : 2 ≤ T) (hδ : 0 ≤ δ) (hP : ∀ p ∈ P, p.Prime)
    (hcap : ∀ p ∈ P, (p : ℝ) ≤ T) :
    (∑ p ∈ P, (p : ℝ) ^ (-1 + δ)) ≤
      T ^ δ * Real.exp 1 * Real.log (1 + Real.log T) := by
  have hterm : ∀ p ∈ P, (p : ℝ) ^ (-1 + δ) ≤ T ^ δ * (1 / (p : ℝ)) := by
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
    rw [Real.rpow_add hp0, Real.rpow_neg_one]
    have hpow := Real.rpow_le_rpow hp0.le (hcap p hp) hδ
    simpa only [one_div, mul_comm] using mul_le_mul_of_nonneg_left hpow (inv_nonneg.mpr hp0.le)
  calc
    (∑ p ∈ P, (p : ℝ) ^ (-1 + δ)) ≤ ∑ p ∈ P, T ^ δ * (1 / (p : ℝ)) :=
      Finset.sum_le_sum hterm
    _ = T ^ δ * (∑ p ∈ P, 1 / (p : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ T ^ δ * (Real.exp 1 * Real.log (1 + Real.log T)) :=
      mul_le_mul_of_nonneg_left (prime_reciprocal_sum_le P T hT hP hcap)
        (Real.rpow_nonneg (by linarith) _)
    _ = T ^ δ * Real.exp 1 * Real.log (1 + Real.log T) := by ring

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_SmoothRankin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

open scoped BigOperators

namespace Problem337

/-- A finite nonnegative sum over smooth numbers is bounded by the finite
Euler product. Only the local prime-power series need to be summable. -/
theorem smooth_sum_le_euler_product
    (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (hf1 : f 1 = 1)
    (hmul : ∀ {m n}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hsum : ∀ {p : ℕ}, p.Prime → Summable (fun j : ℕ => ‖f (p ^ j)‖))
    (N : ℕ) (s : Finset ℕ) (hs : ∀ n ∈ s, n ∈ N.smoothNumbers) :
    (∑ n ∈ s, f n) ≤ ∏ p ∈ N.primesBelow, ∑' j : ℕ, f (p ^ j) := by
  classical
  obtain ⟨_, hprod⟩ := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    hf1 hmul hsum N
  calc
    (∑ n ∈ s, f n) = ∑ n ∈ s.subtype (fun n => n ∈ N.smoothNumbers), f n :=
      (Finset.sum_subtype_of_mem f hs).symm
    _ ≤ ∑' n : N.smoothNumbers, f n :=
      hprod.summable.sum_le_tsum _ (fun n _ => hf n)
    _ = ∏ p ∈ N.primesBelow, ∑' j : ℕ, f (p ^ j) := hprod.tsum_eq

/-- The elementary exponential weight used in Rankin's tail estimate. -/
theorem rankin_weight_bound {V β : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hn : Real.exp V ≤ (n : ℝ)) :
    1 ≤ Real.exp (-β * V) * (n : ℝ) ^ β := by
  have hpow := Real.rpow_le_rpow (le_of_lt (Real.exp_pos V)) hn hβ
  rw [← Real.exp_mul] at hpow
  have h := mul_le_mul_of_nonneg_left hpow (le_of_lt (Real.exp_pos (-β * V)))
  have hid : Real.exp (-β * V) * Real.exp (V * β) = 1 := by
    rw [← Real.exp_add]
    have : -β * V + V * β = 0 := by ring
    rw [this, Real.exp_zero]
  rwa [hid] at h

/-- Rankin's trick followed by a finite Euler product. This form applies to
`f n = τ(n)^r / n`; the local weight then has exponent `-1 + β`. -/
theorem smooth_rankin_bound
    (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (hf1 : f 1 = 1)
    (hmul : ∀ {m n}, Nat.Coprime m n → f (m * n) = f m * f n)
    {V β : ℝ} (hβ : 0 ≤ β)
    (hsum : ∀ {p : ℕ}, p.Prime →
      Summable (fun j : ℕ => ‖f (p ^ j) * ((p ^ j : ℕ) : ℝ) ^ β‖))
    (N : ℕ) (s : Finset ℕ) (hs : ∀ n ∈ s, n ∈ N.smoothNumbers)
    (hlarge : ∀ n ∈ s, Real.exp V ≤ (n : ℝ)) :
    (∑ n ∈ s, f n) ≤ Real.exp (-β * V) *
      (∏ p ∈ N.primesBelow, ∑' j : ℕ, f (p ^ j) * ((p ^ j : ℕ) : ℝ) ^ β) := by
  have hg : ∀ n : ℕ, 0 ≤ f n * (n : ℝ) ^ β := by
    intro n
    exact mul_nonneg (hf n) (Real.rpow_nonneg (Nat.cast_nonneg n) β)
  have hg1 : f 1 * (1 : ℝ) ^ β = 1 := by simp [hf1]
  have hgmul : ∀ {m n : ℕ}, Nat.Coprime m n →
      f (m * n) * ((m * n : ℕ) : ℝ) ^ β =
        (f m * (m : ℝ) ^ β) * (f n * (n : ℝ) ^ β) := by
    intro m n hmn
    rw [hmul hmn, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
    ring
  have heuler := smooth_sum_le_euler_product (fun n => f n * (n : ℝ) ^ β)
    hg (by simpa using hg1) hgmul hsum N s hs
  calc
    (∑ n ∈ s, f n) ≤ ∑ n ∈ s, Real.exp (-β * V) * (f n * (n : ℝ) ^ β) := by
      apply Finset.sum_le_sum
      intro n hn
      have h := mul_le_mul_of_nonneg_left (rankin_weight_bound hβ (hlarge n hn)) (hf n)
      nlinarith
    _ = Real.exp (-β * V) * ∑ n ∈ s, f n * (n : ℝ) ^ β := by rw [Finset.mul_sum]
    _ ≤ Real.exp (-β * V) *
        (∏ p ∈ N.primesBelow, ∑' j : ℕ, f (p ^ j) * ((p ^ j : ℕ) : ℝ) ^ β) :=
      mul_le_mul_of_nonneg_left heuler (le_of_lt (Real.exp_pos _))

theorem divisorHarmonicWeight_nonneg (r n : ℕ) : 0 ≤ divisorHarmonicWeight r n := by
  unfold divisorHarmonicWeight
  positivity

theorem divisorHarmonicWeight_one (r : ℕ) : divisorHarmonicWeight r 1 = 1 := by
  simp [divisorHarmonicWeight]

theorem divisorHarmonicWeight_mul (r : ℕ) {m n : ℕ} (h : m.Coprime n) :
    divisorHarmonicWeight r (m * n) = divisorHarmonicWeight r m * divisorHarmonicWeight r n := by
  simp only [divisorHarmonicWeight, h.card_divisors_mul, Nat.cast_mul, mul_pow]
  ring

theorem divisorHarmonicWeight_prime_power (r : ℕ) {p : ℕ} (hp : p.Prime) (j : ℕ)
    (β : ℝ) :
    divisorHarmonicWeight r (p ^ j) * ((p ^ j : ℕ) : ℝ) ^ β =
      ((j + 1 : ℕ) : ℝ) ^ r * ((p : ℝ) ^ (β - 1)) ^ j := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpow : (0 : ℝ) < (p : ℝ) ^ j := pow_pos hpR j
  simp only [divisorHarmonicWeight, Nat.divisors_prime_pow hp, Finset.card_map,
    Finset.card_range, Nat.cast_pow]
  rw [Real.rpow_pow_comm (le_of_lt hpR), Real.rpow_sub_one (ne_of_gt hpow)]
  ring

theorem summable_successor_pow_geometric (r : ℕ) {q : ℝ} (hq : 0 < q) (hqone : q < 1) :
    Summable (fun j : ℕ => ‖((j + 1 : ℕ) : ℝ) ^ r * q ^ j‖) := by
  have hnorm : ‖q‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_pos hq] using hqone
  have h := (summable_norm_pow_mul_geometric_of_norm_lt_one r hnorm).comp_injective
    Nat.succ_injective
  have h' := h.mul_right q⁻¹
  apply h'.congr
  intro j
  change ‖((j + 1 : ℕ) : ℝ) ^ r * q ^ (j + 1)‖ * q⁻¹ =
    ‖((j + 1 : ℕ) : ℝ) ^ r * q ^ j‖
  rw [pow_succ, ← mul_assoc, norm_mul, Real.norm_eq_abs q, abs_of_pos hq]
  field_simp

theorem divisorHarmonicWeight_local_summable (r : ℕ) {β : ℝ} (hβ : β < 1)
    {p : ℕ} (hp : p.Prime) :
    Summable (fun j : ℕ => ‖divisorHarmonicWeight r (p ^ j) * ((p ^ j : ℕ) : ℝ) ^ β‖) := by
  simp_rw [divisorHarmonicWeight_prime_power r hp]
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  exact summable_successor_pow_geometric r (Real.rpow_pos_of_pos (by linarith) _)
    (Real.rpow_lt_one_of_one_lt_of_neg hpR (by linarith))

/-- Concrete smooth-prefix Rankin estimate for any natural moment order. -/
theorem divisor_smooth_rankin_bound (r : ℕ) {V β : ℝ} (hβ : 0 ≤ β) (hβone : β < 1)
    (N : ℕ) (s : Finset ℕ) (hs : ∀ n ∈ s, n ∈ N.smoothNumbers)
    (hlarge : ∀ n ∈ s, Real.exp V ≤ (n : ℝ)) :
    (∑ n ∈ s, (n.divisors.card : ℝ) ^ r / (n : ℝ)) ≤ Real.exp (-β * V) *
      (∏ p ∈ N.primesBelow, ∑' j : ℕ,
        ((j + 1 : ℕ) : ℝ) ^ r * ((p : ℝ) ^ (β - 1)) ^ j) := by
  have h := smooth_rankin_bound (divisorHarmonicWeight r) (divisorHarmonicWeight_nonneg r)
    (divisorHarmonicWeight_one r) (divisorHarmonicWeight_mul r) hβ
    (divisorHarmonicWeight_local_summable r hβone) N s hs hlarge
  change (∑ n ∈ s, divisorHarmonicWeight r n) ≤ _
  apply h.trans_eq
  apply congrArg (fun x : ℝ => Real.exp (-β * V) * x)
  apply Finset.prod_congr rfl
  intro p hp
  apply tsum_congr
  intro j
  exact divisorHarmonicWeight_prime_power r (Nat.prime_of_mem_primesBelow hp) j β

theorem divisorEulerFactor_one_le (r : ℕ) {p : ℕ} (hp : p.Prime) {β : ℝ}
    (hβ : β < 1) : 1 ≤ divisorEulerFactor r p β := by
  have hs := divisorHarmonicWeight_local_summable r hβ hp
  simp_rw [divisorHarmonicWeight_prime_power r hp] at hs
  have h := hs.of_norm.sum_le_tsum {0} (by
    intro j _
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
    positivity)
  simpa [divisorEulerFactor] using h

/-- Logarithmic local-factor estimates turn the Rankin Euler product into a
single exponential. This is the precise smooth-prefix bound used in the
divisor-moment decomposition. -/
theorem divisor_smooth_rankin_log_bound (r : ℕ) {V β C : ℝ}
    (hβ : 0 ≤ β) (hβone : β < 1) (N : ℕ) (s : Finset ℕ)
    (hs : ∀ n ∈ s, n ∈ N.smoothNumbers)
    (hlarge : ∀ n ∈ s, Real.exp V ≤ (n : ℝ))
    (hlocal : ∀ p ∈ N.primesBelow,
      Real.log (divisorEulerFactor r p β) ≤ C * (p : ℝ) ^ (β - 1)) :
    (∑ n ∈ s, (n.divisors.card : ℝ) ^ r / (n : ℝ)) ≤
      Real.exp (-β * V + C * ∑ p ∈ N.primesBelow, (p : ℝ) ^ (β - 1)) := by
  have hpos : ∀ p ∈ N.primesBelow, 0 < divisorEulerFactor r p β := by
    intro p hp
    have := divisorEulerFactor_one_le r (Nat.prime_of_mem_primesBelow hp) hβone
    linarith
  have hprodpos : 0 < ∏ p ∈ N.primesBelow, divisorEulerFactor r p β := Finset.prod_pos hpos
  have hlog : Real.log (∏ p ∈ N.primesBelow, divisorEulerFactor r p β) ≤
      C * ∑ p ∈ N.primesBelow, (p : ℝ) ^ (β - 1) := by
    rw [Real.log_prod (fun p hp => ne_of_gt (hpos p hp)), Finset.mul_sum]
    exact Finset.sum_le_sum hlocal
  have hprod := (Real.log_le_iff_le_exp hprodpos).mp hlog
  have hrank := divisor_smooth_rankin_bound r hβ hβone N s hs hlarge
  change (∑ n ∈ s, (n.divisors.card : ℝ) ^ r / (n : ℝ)) ≤
    Real.exp (-β * V) * ∏ p ∈ N.primesBelow, divisorEulerFactor r p β at hrank
  calc
    (∑ n ∈ s, (n.divisors.card : ℝ) ^ r / (n : ℝ)) ≤
        Real.exp (-β * V) * ∏ p ∈ N.primesBelow, divisorEulerFactor r p β := hrank
    _ ≤ Real.exp (-β * V) *
        Real.exp (C * ∑ p ∈ N.primesBelow, (p : ℝ) ^ (β - 1)) :=
      mul_le_mul_of_nonneg_left hprod (le_of_lt (Real.exp_pos _))
    _ = Real.exp (-β * V + C * ∑ p ∈ N.primesBelow, (p : ℝ) ^ (β - 1)) :=
      (Real.exp_add _ _).symm

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_SmoothRankinBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

open scoped BigOperators

namespace Problem337

/-- Uniform Rankin estimate for smooth harmonic divisor moments. The constant
depends only on the moment order, not on the smoothness cutoff or the tail. -/
theorem uniform_divisor_smooth_rankin_bound (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ β V : ℝ, 0 ≤ β → β ≤ 1 / 4 →
      ∀ N : ℕ, ∀ s : Finset ℕ,
      (∀ n ∈ s, n ∈ N.smoothNumbers) →
      (∀ n ∈ s, Real.exp V ≤ (n : ℝ)) →
      (∑ n ∈ s, (n.divisors.card : ℝ) ^ r / (n : ℝ)) ≤
        Real.exp (-β * V + C * ∑ p ∈ N.primesBelow, (p : ℝ) ^ (β - 1)) := by
  obtain ⟨C, hC, hfactor⟩ := DivisorMoment.divisor_full_local_factor_bound (r : ℝ)
  refine ⟨C, hC, ?_⟩
  intro β V hβ hβquarter N s hs hlarge
  apply divisor_smooth_rankin_log_bound r hβ (by linarith) N s hs hlarge
  intro p hp
  have hp2 : (2 : ℝ) ≤ p := by
    exact_mod_cast (Nat.prime_of_mem_primesBelow hp).two_le
  have h := (hfactor (p : ℝ) (1 - β) hp2 (by linarith)).2.1
  have hexp : -(1 - β) = β - 1 := by ring
  simpa only [divisorEulerFactor, Nat.cast_add, Nat.cast_one, Real.rpow_natCast, hexp] using h

theorem rankin_band_negative_exponent {v t : ℝ} (ht : t ≠ 0) :
    -(Real.log (v / t) / (10 * t)) * (v / 5) =
      -(v / t) * Real.log (v / t) / 50 := by
  field_simp
  ring

theorem rankin_band_positive_exponent {v t : ℝ} (ht : 0 < t) (hv : 0 < v) :
    Real.exp ((Real.log (v / t) / (10 * t)) * (2 * t)) =
      (v / t) ^ (1 / 5 : ℝ) := by
  rw [Real.rpow_def_of_pos (div_pos hv ht)]
  congr 1
  field_simp
  ring

theorem log_one_add_two_mul_le (t : ℝ) (ht : 1 ≤ t) :
    Real.log (1 + 2 * t) ≤ 2 * Real.log (2 * t) := by
  have htpos : 0 < 2 * t := by linarith
  have hbound : 1 + 2 * t ≤ (2 * t) ^ 2 := by nlinarith
  have h := Real.log_le_log (show 0 < 1 + 2 * t by linarith) hbound
  simpa only [Real.log_pow, Nat.cast_ofNat] using h

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_RankinBand
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

open scoped BigOperators

namespace Problem337

/-- Smooth harmonic divisor tails with all Euler and prime sums evaluated. -/
theorem uniform_divisor_smooth_rankin_loglog_bound (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ β V W : ℝ, 0 ≤ β → β ≤ 1 / 4 → 1 ≤ W →
      ∀ N : ℕ, (∀ p ∈ N.primesBelow, (p : ℝ) ≤ Real.exp W) → ∀ s : Finset ℕ,
      (∀ n ∈ s, n ∈ N.smoothNumbers) →
      (∀ n ∈ s, Real.exp V ≤ (n : ℝ)) →
      (∑ n ∈ s, (n.divisors.card : ℝ) ^ r / (n : ℝ)) ≤
        Real.exp (-β * V + C * Real.exp (β * W) * Real.log (1 + W)) := by
  obtain ⟨C, hC, hbound⟩ := uniform_divisor_smooth_rankin_bound r
  refine ⟨C * Real.exp 1, by positivity, ?_⟩
  intro β V W hβ hβquarter hW N hN s hs hlarge
  have hT : 2 ≤ Real.exp W := by
    have := Real.add_one_le_exp W
    linarith
  have hprime := prime_weighted_reciprocal_sum_le N.primesBelow (Real.exp W) β hT hβ
    (fun p hp => Nat.prime_of_mem_primesBelow hp)
    hN
  rw [Real.log_exp, ← Real.exp_mul] at hprime
  simp only [show -1 + β = β - 1 by ring, mul_comm W β] at hprime
  refine (hbound β V hβ hβquarter N s hs hlarge).trans (Real.exp_le_exp.mpr ?_)
  have h := mul_le_mul_of_nonneg_left hprime hC.le
  nlinarith

/-- The exact intermediate-prime-band Rankin estimate. The only scale
restriction is the explicit admissibility of the chosen Rankin exponent. -/
theorem divisor_rankin_intermediate_band (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ v t : ℝ, 1 ≤ t → t ≤ v →
      Real.log (v / t) / (10 * t) ≤ 1 / 4 →
      ∀ N : ℕ, (∀ p ∈ N.primesBelow, (p : ℝ) ≤ Real.exp (2 * t)) → ∀ s : Finset ℕ,
      (∀ n ∈ s, n ∈ N.smoothNumbers) →
      (∀ n ∈ s, Real.exp (v / 5) ≤ (n : ℝ)) →
      (∑ n ∈ s, (n.divisors.card : ℝ) ^ r / (n : ℝ)) ≤
        Real.exp (-(v / t) * Real.log (v / t) / 50 +
          C * (v / t) ^ (1 / 5 : ℝ) * Real.log (2 * t)) := by
  obtain ⟨C, hC, hbound⟩ := uniform_divisor_smooth_rankin_loglog_bound r
  refine ⟨2 * C, by positivity, ?_⟩
  intro v t ht htv hβquarter N hN s hs hlarge
  have htpos : 0 < t := by linarith
  have hvpos : 0 < v := by linarith
  have hQ : 1 ≤ v / t := (one_le_div htpos).mpr htv
  have hβ : 0 ≤ Real.log (v / t) / (10 * t) :=
    div_nonneg (Real.log_nonneg hQ) (by positivity)
  have h := hbound (Real.log (v / t) / (10 * t)) (v / 5) (2 * t)
    hβ hβquarter (by linarith) N hN s hs hlarge
  rw [rankin_band_negative_exponent (ne_of_gt htpos),
    rankin_band_positive_exponent htpos hvpos] at h
  refine h.trans (Real.exp_le_exp.mpr ?_)
  have hlog := mul_le_mul_of_nonneg_left (log_one_add_two_mul_le t ht)
    (mul_nonneg hC.le (Real.rpow_nonneg (le_of_lt (div_pos hvpos htpos)) (1 / 5 : ℝ)))
  nlinarith

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_IntermediatePrimeClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped BigOperators

namespace Problem337.DivisorMoment

/-- Prefix counting in the shift convention used by short-interval moments. -/
theorem sum_le_shifted_divisor_majorant_real_cutoff
    (N : ℕ) (Y : ℝ) (H D : Finset ℕ) (w a : ℕ → ℝ) (hY : 0 ≤ Y)
    (hH : H ⊆ Finset.Icc 1 ⌊Y⌋₊)
    (hassign : ∀ h ∈ H, ∃ d ∈ D, d ∣ N + h ∧ w h ≤ a d)
    (ha : ∀ d ∈ D, 0 ≤ a d)
    (hD : ∀ d ∈ D, 0 < d ∧ (d : ℝ) ≤ Y) :
    (∑ h ∈ H, w h) ≤ 2 * Y * ∑ d ∈ D, a d / d := by
  classical
  let A := H.image (fun h => N + h)
  have hA : A ⊆ Finset.Ioc N (N + ⌊Y⌋₊) := by
    intro n hn
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hh1, hhY⟩ := Finset.mem_Icc.mp (hH hh)
    exact Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
  have hassignA : ∀ n ∈ A, ∃ d ∈ D, d ∣ n ∧ w (n - N) ≤ a d := by
    intro n hn
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hn
    simpa only [Nat.add_sub_cancel_left] using hassign h hh
  have hsum : (∑ n ∈ A, w (n - N)) = ∑ h ∈ H, w h := by
    dsimp [A]
    rw [Finset.sum_image (fun a _ b _ h => Nat.add_left_cancel h)]
    simp only [Nat.add_sub_cancel_left]
  have h := sum_le_divisor_majorant_real_cutoff N Y A D (fun n => w (n - N)) a
    hY hA hassignA ha hD
  rwa [hsum] at h

/-- One actual intermediate-prime class, with all divisor-prefix counting and
smooth Rankin summation performed. Only the pointwise prefix witnesses remain
as hypotheses; no moment or counting estimate is assumed. -/
theorem intermediate_prime_class_bound (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (Y v t R : ℝ) (H : Finset ℕ) (w : ℕ → ℝ),
      0 ≤ Y → 1 ≤ t → t ≤ v → Real.log (v / t) / (10 * t) ≤ 1 / 4 →
      H ⊆ Finset.Icc 1 ⌊Y⌋₊ →
      (∀ h ∈ H, ∃ d : ℕ, d ∣ N + h ∧ (d : ℝ) ≤ Y ∧
        Real.exp (v / 5) ≤ (d : ℝ) ∧
        (∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) ≤ Real.exp (2 * t)) ∧
        w h ≤ Real.exp R * (d.divisors.card : ℝ) ^ r) →
      (∑ h ∈ H, w h) ≤ 2 * Y *
        Real.exp (R - (v / t) * Real.log (v / t) / 50 +
          C * (v / t) ^ (1 / 5 : ℝ) * Real.log (2 * t)) := by
  classical
  obtain ⟨C, hC, hRankin⟩ := Problem337.divisor_rankin_intermediate_band r
  refine ⟨C, hC, ?_⟩
  intro N Y v t R H w hY ht htv hβ hH hprefix
  let K : ℕ := ⌊Real.exp (2 * t)⌋₊ + 1
  let D : Finset ℕ := (Finset.Icc 1 ⌊Y⌋₊).filter
    (fun d => Real.exp (v / 5) ≤ (d : ℝ) ∧ d ∈ K.smoothNumbers)
  have hK : ∀ p ∈ K.primesBelow, (p : ℝ) ≤ Real.exp (2 * t) := by
    intro p hp
    have hpK := Nat.lt_of_mem_primesBelow hp
    have hpFloor : p ≤ ⌊Real.exp (2 * t)⌋₊ := by dsimp [K] at hpK; omega
    exact (Nat.cast_le.mpr hpFloor).trans (Nat.floor_le (Real.exp_pos _).le)
  have hD : ∀ d ∈ D, 0 < d ∧ (d : ℝ) ≤ Y := by
    intro d hd
    have hdI := Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1
    exact ⟨by omega, (Nat.cast_le.mpr hdI.2).trans (Nat.floor_le hY)⟩
  have hassign : ∀ h ∈ H, ∃ d ∈ D, d ∣ N + h ∧
      w h ≤ Real.exp R * (d.divisors.card : ℝ) ^ r := by
    intro h hh
    obtain ⟨d, hdvd, hdY, hdlarge, hdprime, hdw⟩ := hprefix h hh
    have hdposR : (0 : ℝ) < d := (Real.exp_pos _).trans_le hdlarge
    have hdpos : 0 < d := by exact_mod_cast hdposR
    refine ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨by omega, Nat.le_floor hdY⟩, hdlarge, ?_⟩, hdvd, hdw⟩
    apply Nat.mem_smoothNumbers'.mpr
    intro p hp hpd
    have hpFloor : p ≤ ⌊Real.exp (2 * t)⌋₊ := Nat.le_floor (hdprime p hp hpd)
    dsimp [K]
    omega
  have hcount := sum_le_shifted_divisor_majorant_real_cutoff N Y H D w
    (fun d => Real.exp R * (d.divisors.card : ℝ) ^ r) hY hH hassign
    (fun d _ => by positivity) hD
  have hrank := hRankin v t ht htv hβ K hK D
    (fun d hd => (Finset.mem_filter.mp hd).2.2)
    (fun d hd => (Finset.mem_filter.mp hd).2.1)
  calc
    (∑ h ∈ H, w h) ≤ 2 * Y *
        ∑ d ∈ D, (Real.exp R * (d.divisors.card : ℝ) ^ r) / d := hcount
    _ = 2 * Y * (Real.exp R * ∑ d ∈ D, (d.divisors.card : ℝ) ^ r / d) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ ≤ 2 * Y * (Real.exp R * Real.exp (-(v / t) * Real.log (v / t) / 50 +
          C * (v / t) ^ (1 / 5 : ℝ) * Real.log (2 * t))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrank (Real.exp_pos _).le)
        (by positivity)
    _ = _ := by
      rw [← Real.exp_add]
      congr 2
      ring

/-- The same evaluated class estimate for arbitrary real moment orders. -/
theorem intermediate_prime_class_bound_real (r : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (Y v t R : ℝ) (H : Finset ℕ) (w : ℕ → ℝ),
      0 ≤ Y → 1 ≤ t → t ≤ v → Real.log (v / t) / (10 * t) ≤ 1 / 4 →
      H ⊆ Finset.Icc 1 ⌊Y⌋₊ →
      (∀ h ∈ H, ∃ d : ℕ, d ∣ N + h ∧ (d : ℝ) ≤ Y ∧
        Real.exp (v / 5) ≤ (d : ℝ) ∧
        (∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) ≤ Real.exp (2 * t)) ∧
        w h ≤ Real.exp R * (d.divisors.card : ℝ) ^ r) →
      (∑ h ∈ H, w h) ≤ 2 * Y *
        Real.exp (R - (v / t) * Real.log (v / t) / 50 +
          C * (v / t) ^ (1 / 5 : ℝ) * Real.log (2 * t)) := by
  obtain ⟨C, hC, hbound⟩ := intermediate_prime_class_bound ⌈r⌉₊
  refine ⟨C, hC, ?_⟩
  intro N Y v t R H w hY ht htv hβ hH hprefix
  apply hbound N Y v t R H w hY ht htv hβ hH
  intro h hh
  obtain ⟨d, hdvd, hdY, hdlarge, hdprime, hdw⟩ := hprefix h hh
  refine ⟨d, hdvd, hdY, hdlarge, hdprime, hdw.trans ?_⟩
  have hdposR : (0 : ℝ) < d := (Real.exp_pos _).trans_le hdlarge
  have hdne : d ≠ 0 := by exact_mod_cast (ne_of_gt hdposR)
  have hcard : (1 : ℝ) ≤ d.divisors.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hdne⟩
  have hpow := Real.rpow_le_rpow_of_exponent_le hcard (Nat.le_ceil r)
  rw [Real.rpow_natCast] at hpow
  exact mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le

/-- The prefix cutoff `sqrt Y` used in the actual prime-factor decomposition
is directly admissible. The arbitrary loss `R` can be instantiated by `r*B*v/t`. -/
theorem intermediate_prime_class_sqrt_bound (r : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (Y v t R : ℝ) (H : Finset ℕ) (w : ℕ → ℝ),
      1 ≤ Y → 1 ≤ t → t ≤ v → Real.log (v / t) / (10 * t) ≤ 1 / 4 →
      H ⊆ Finset.Icc 1 ⌊Y⌋₊ →
      (∀ h ∈ H, ∃ d : ℕ, d ∣ N + h ∧ (d : ℝ) ≤ Real.sqrt Y ∧
        Real.exp (v / 5) ≤ (d : ℝ) ∧
        (∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) ≤ Real.exp (2 * t)) ∧
        w h ≤ Real.exp R * (d.divisors.card : ℝ) ^ r) →
      (∑ h ∈ H, w h) ≤ 2 * Y *
        Real.exp (R - (v / t) * Real.log (v / t) / 50 +
          C * (v / t) ^ (1 / 5 : ℝ) * Real.log (2 * t)) := by
  obtain ⟨C, hC, hbound⟩ := intermediate_prime_class_bound_real r
  refine ⟨C, hC, ?_⟩
  intro N Y v t R H w hY ht htv hβ hH hprefix
  apply hbound N Y v t R H w (by linarith) ht htv hβ hH
  intro h hh
  obtain ⟨d, hdvd, hdY, hdlarge, hdprime, hdw⟩ := hprefix h hh
  exact ⟨d, hdvd, hdY.trans (Real.sqrt_le_self_iff.mpr (Or.inr hY)),
    hdlarge, hdprime, hdw⟩

end Problem337.DivisorMoment

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

/-- Splitting off any prefix of the factorization gives the divisor-prefix moment bound. -/
theorem truncatedDivisorCount_prefix_moment_bound (X z W r : ℝ) {n d : ℕ}
    (hn : n ≠ 0) (hd : d ∣ n) (hX : 1 < X) (hz : 1 < z)
    (hXW : Real.log X ≤ W) (hnW : Real.log (n : ℝ) ≤ W) (hr : 0 ≤ r)
    (hlarge : ∀ p ∈ (n / d).primeFactorsList, z ≤ (p : ℝ)) :
    (truncatedDivisorCount X n : ℝ) ^ r ≤ (d.divisors.card : ℝ) ^ r *
      Real.exp (r * ((1 + Real.log (W / Real.log X)) * Real.log X / Real.log z)) := by
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hnpos
  have hquotpos : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hnpos hd) hdpos
  have hquotW : Real.log ((n / d : ℕ) : ℝ) ≤ W := by
    apply le_trans _ hnW
    apply Real.log_le_log (by exact_mod_cast hquotpos)
    exact_mod_cast Nat.div_le_self n d
  have hbound : (truncatedDivisorCount X n : ℝ) ≤ (d.divisors.card : ℝ) *
      Real.exp ((1 + Real.log (W / Real.log X)) * Real.log X / Real.log z) := by
    calc
      _ ≤ (d.divisors.card : ℝ) * (truncatedDivisorCount X (n / d) : ℝ) := by
        exact_mod_cast truncatedDivisorCount_factor_bound X hd
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (truncatedDivisorCount_large_primes_bound X z W (Nat.ne_of_gt hquotpos)
          hX hz hXW hquotW hlarge) (Nat.cast_nonneg _)
  have hp := Real.rpow_le_rpow (Nat.cast_nonneg _) hbound hr
  rw [Real.mul_rpow (Nat.cast_nonneg _) (Real.exp_pos _).le, ← Real.exp_mul] at hp
  simpa only [mul_comm r] using hp

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_PrimePrefixSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open Filter Topology

namespace Problem337.PrimePrefixSize

/-- Crossing the square-root cutoff forces a large prefix if the next prime is small. -/
lemma log_prefix_lower {d p Y v : ℝ}
    (hd : 0 < d) (hp : 0 < p) (hY : 0 < Y)
    (hYlog : v / 2 ≤ Real.log Y)
    (hcross : Real.sqrt Y < d * p)
    (hplog : Real.log p < v ^ (15 / 16 : ℝ))
    (hsmall : v ^ (15 / 16 : ℝ) ≤ v / 20) :
    v / 5 < Real.log d := by
  have hc := Real.log_lt_log (Real.sqrt_pos.2 hY) hcross
  rw [Real.log_sqrt hY.le, Real.log_mul hd.ne' hp.ne'] at hc
  linarith

lemma exp_prefix_lower {d p Y v : ℝ}
    (hd : 0 < d) (hp : 0 < p) (hY : 0 < Y)
    (hYlog : v / 2 ≤ Real.log Y)
    (hcross : Real.sqrt Y < d * p)
    (hplog : Real.log p < v ^ (15 / 16 : ℝ))
    (hsmall : v ^ (15 / 16 : ℝ) ≤ v / 20) :
    Real.exp (v / 5) < d := by
  calc
    Real.exp (v / 5) < Real.exp (Real.log d) := Real.exp_lt_exp.mpr
      (log_prefix_lower hd hp hY hYlog hcross hplog hsmall)
    _ = d := Real.exp_log hd

lemma eventually_fifteen_sixteenths_small :
    ∀ᶠ v : ℝ in atTop, v ^ (15 / 16 : ℝ) ≤ v / 20 := by
  have hlim := tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 16)
  have he := hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 20))
  filter_upwards [he, eventually_gt_atTop (0 : ℝ)] with v hv hvpos
  calc
    v ^ (15 / 16 : ℝ) = v ^ (1 : ℝ) * v ^ (-(1 / 16 : ℝ)) := by
      rw [← Real.rpow_add hvpos]
      norm_num
    _ = v * v ^ (-(1 / 16 : ℝ)) := by rw [Real.rpow_one]
    _ ≤ v * (1 / 20) := mul_le_mul_of_nonneg_left hv.le hvpos.le
    _ = v / 20 := by ring

/-- The manuscript's lower scale tends uniformly beyond every fixed threshold. -/
lemma eventually_uniform_lower_scale (V : ℝ) :
    ∀ᶠ S : ℝ in atTop, ∀ v : ℝ, S / (2 * Real.log S) ≤ v → V ≤ v := by
  let W := max V 1
  have hW : 0 < W := by dsimp [W]; positivity
  have he := Real.isLittleO_log_id_atTop.bound (by positivity : 0 < 1 / (2 * W))
  filter_upwards [he, eventually_ge_atTop (2 : ℝ)] with S hS hS2
  have hSpos : 0 < S := by linarith
  have hlog : 0 < Real.log S := Real.log_pos (by linarith)
  simp only [Real.norm_eq_abs, abs_of_pos hlog, id_eq, abs_of_pos hSpos] at hS
  have hmul : (2 * W) * Real.log S ≤ S := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2 * W)).1
      (show Real.log S ≤ S / (2 * W) by simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using hS)
    nlinarith
  intro v hv
  have hWv : W ≤ S / (2 * Real.log S) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * Real.log S)).2
    nlinarith
  exact (le_max_left _ _).trans (hWv.trans hv)

end Problem337.PrimePrefixSize

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_RankinAdmissibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- The intermediate-band Rankin exponent is admissible throughout the scale window. -/
theorem rankin_band_exponent_admissible (S v t : ℝ)
    (hS : 1 < S) (ht : 1 ≤ t) (htv : t ≤ v)
    (hv : v ≤ S ^ 2) (hlow : 4 * Real.log S ≤ t) :
    Real.log (v / t) / (10 * t) ≤ 1 / 4 := by
  have hSpos : 0 < S := by linarith
  have htpos : 0 < t := by linarith
  have hvpos : 0 < v := by linarith
  have hquot : v / t ≤ S ^ 2 := by
    apply (div_le_iff₀ htpos).mpr
    nlinarith [sq_nonneg S]
  have hlog := Real.log_le_log (div_pos hvpos htpos) hquot
  rw [Real.log_pow] at hlog
  apply (div_le_iff₀ (by positivity : 0 < 10 * t)).mpr
  nlinarith

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_IntermediatePrefixClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped BigOperators Topology
open Filter

namespace Problem337.DivisorMoment

/-- The actual intermediate prefix class: the lower-prefix and pointwise
moment hypotheses of the Rankin class bound are derived from factorization
data and the crossing of the square-root cutoff. -/
theorem intermediate_selected_prefix_moment_bound (r : ℝ) (hr : 0 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (X Y v t W : ℝ) (H : Finset ℕ),
      1 < X → Real.log X = v → 1 ≤ Y → v / 2 ≤ Real.log Y →
      1 ≤ t → t ≤ v → Real.log (v / t) / (10 * t) ≤ 1 / 4 →
      v ^ (15 / 16 : ℝ) ≤ v / 20 → v ≤ W →
      H ⊆ Finset.Icc 1 ⌊Y⌋₊ →
      (∀ h ∈ H, Real.log ((N + h : ℕ) : ℝ) ≤ W) →
      (∀ h ∈ H, ∃ d p : ℕ, IntermediatePrefixWitness (N + h) d p Y v t) →
      (∑ h ∈ H, (truncatedDivisorCount X (N + h) : ℝ) ^ r) ≤ 2 * Y *
        Real.exp (r * ((1 + Real.log (W / v)) * v / t) -
          (v / t) * Real.log (v / t) / 50 +
          C * (v / t) ^ (1 / 5 : ℝ) * Real.log (2 * t)) := by
  obtain ⟨C, hC, hbound⟩ := intermediate_prime_class_sqrt_bound r
  refine ⟨C, hC, ?_⟩
  intro N X Y v t W H hX hXv hY hYlog ht htv hβ hsmall hvW hH hNW hpfx
  apply hbound N Y v t (r * ((1 + Real.log (W / v)) * v / t)) H
    (fun h => (truncatedDivisorCount X (N + h) : ℝ) ^ r)
    hY ht htv hβ hH
  intro h hh
  obtain ⟨d, p, hdvd, hdY, hcross, hp, hplog, htp, hpt, hdfactors, hqfactors⟩ := hpfx h hh
  have hnpos : 0 < N + h := by
    have hh1 := (Finset.mem_Icc.mp (hH hh)).1
    omega
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hnpos
  have hdposR : (0 : ℝ) < d := by exact_mod_cast hdpos
  have hppos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hplarge : Real.exp (v / 5) < (d : ℝ) :=
    PrimePrefixSize.exp_prefix_lower hdposR hppos (by linarith)
      hYlog hcross hplog hsmall
  have hpcap : (p : ℝ) ≤ Real.exp (2 * t) := by
    calc
      (p : ℝ) = Real.exp (Real.log (p : ℝ)) := (Real.exp_log hppos).symm
      _ ≤ _ := Real.exp_le_exp.mpr hpt
  have hlowp : Real.exp t ≤ (p : ℝ) := by
    calc
      Real.exp t ≤ Real.exp (Real.log (p : ℝ)) := Real.exp_le_exp.mpr htp
      _ = _ := Real.exp_log hppos
  refine ⟨d, hdvd, hdY, hplarge.le, ?_, ?_⟩
  · intro q hq hqd
    exact (Nat.cast_le.mpr (hdfactors q hq hqd)).trans hpcap
  · have hmoment := truncatedDivisorCount_prefix_moment_bound X (Real.exp t) W r
      (Nat.ne_of_gt hnpos) hdvd hX (Real.one_lt_exp_iff.mpr (by linarith))
      (by simpa only [hXv] using hvW) (hNW h hh) hr (by
        intro q hq
        exact hlowp.trans (Nat.cast_le.mpr (hqfactors q hq)))
    simpa only [Real.log_exp, hXv, mul_comm] using hmoment

/-- Uniform scale version with both the Rankin admissibility and the lower
prefix size discharged. This is ready for a finite dyadic union. -/
theorem eventually_intermediate_selected_prefix_moment_bound (r : ℝ) (hr : 0 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ S : ℝ in atTop,
      ∀ (N : ℕ) (X Y v t W : ℝ) (H : Finset ℕ),
      1 < X → Real.log X = v → 1 ≤ Y → v / 2 ≤ Real.log Y →
      S / (2 * Real.log S) ≤ v → v ≤ S ^ 2 →
      1 ≤ t → t ≤ v → 4 * Real.log S ≤ t → v ≤ W →
      H ⊆ Finset.Icc 1 ⌊Y⌋₊ →
      (∀ h ∈ H, Real.log ((N + h : ℕ) : ℝ) ≤ W) →
      (∀ h ∈ H, ∃ d p : ℕ, IntermediatePrefixWitness (N + h) d p Y v t) →
      (∑ h ∈ H, (truncatedDivisorCount X (N + h) : ℝ) ^ r) ≤ 2 * Y *
        Real.exp (r * ((1 + Real.log (W / v)) * v / t) -
          (v / t) * Real.log (v / t) / 50 +
          C * (v / t) ^ (1 / 5 : ℝ) * Real.log (2 * t)) := by
  obtain ⟨C, hC, hbound⟩ := intermediate_selected_prefix_moment_bound r hr
  obtain ⟨V, hV⟩ := eventually_atTop.mp PrimePrefixSize.eventually_fifteen_sixteenths_small
  refine ⟨C, hC, ?_⟩
  filter_upwards [PrimePrefixSize.eventually_uniform_lower_scale V,
    eventually_gt_atTop (1 : ℝ)] with S hS hSone
  intro N X Y v t W H hX hXv hY hYlog hvlow hvhigh ht htv htlow hvW hH hNW hpfx
  exact hbound N X Y v t W H hX hXv hY hYlog ht htv
    (Problem337.rankin_band_exponent_admissible S v t hSone ht htv hvhigh htlow)
    (hV v (hS v hvlow)) hvW hH hNW hpfx

end Problem337.DivisorMoment

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_IntermediateBandBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open Filter
open scoped Topology BigOperators

namespace Problem337.DivisorMoment
attribute [local instance] Classical.propDecidable

/-- The final uniform intermediate-band budget for the actual canonical
prime-factor class. All arithmetic, counting, and exponent estimates are
proved here; no class-moment estimate remains as an assumption. -/
theorem eventually_intermediate_band_budget_oai (D r : ℝ) (hD : 1 ≤ D) (hr : 0 ≤ r) :
    ∀ᶠ S : ℝ in atTop, ∀ (v Y : ℝ) (N j : ℕ),
      S / (2 * Real.log S) ≤ v → v ≤ D * S →
      Real.exp (v / 2) ≤ Y → Y ≤ Real.exp v →
      (N : ℝ) ≤ Real.exp (D * S) →
      4 * Real.log S * 2 ^ j ≤ v ^ (15 / 16 : ℝ) →
      (∑ h ∈ (Finset.Icc 1 ⌊Y⌋₊).filter
        (fun h => DivisorClasses.BandClass (N + h) S v Y j),
        (truncatedDivisorCount (Real.exp v) (N + h) : ℝ) ^ r) ≤ 2 * Y := by
  classical
  obtain ⟨C, hC, hclass⟩ := eventually_intermediate_selected_prefix_moment_bound r hr
  have hdec := eventually_uniform_intermediate_band_decay (D + 1) r C
    (by linarith) hr hC.le
  filter_upwards [hclass, hdec, PrimePrefixSize.eventually_uniform_lower_scale 1,
    eventually_ge_atTop (max D (Real.exp 1)), eventually_ge_atTop (1 : ℝ)]
    with S hclass hdec hscale hS hSone
  intro v Y N j hvlow hvhigh hYlow hYhigh hN hj
  let t : ℝ := 4 * Real.log S * 2 ^ j
  let H : Finset ℕ := (Finset.Icc 1 ⌊Y⌋₊).filter
    (fun h => DivisorClasses.BandClass (N + h) S v Y j)
  have hvone : 1 ≤ v := hscale v hvlow
  have hvpos : 0 < v := by linarith
  have hSpos : 0 < S := by linarith
  have hSD : D ≤ S := (le_max_left _ _).trans hS
  have hSexp : Real.exp 1 ≤ S := (le_max_right _ _).trans hS
  have hlogS : 1 ≤ Real.log S := (Real.le_log_iff_exp_le hSpos).mpr hSexp
  have htlow : 4 * Real.log S ≤ t := by
    have hpow : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    dsimp [t]
    nlinarith
  have htone : 1 ≤ t := by linarith
  have htpos : 0 < t := by linarith
  have htv : t ≤ v := by
    calc
      t ≤ v ^ (15 / 16 : ℝ) := hj
      _ ≤ v := by simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hvone (by norm_num : (15 / 16 : ℝ) ≤ 1)
  have hvSsq : v ≤ S ^ 2 := by nlinarith
  have hYone : 1 ≤ Y := (Real.one_le_exp (by linarith : 0 ≤ v / 2)).trans hYlow
  have hYpos : 0 < Y := by linarith
  have hYlog : v / 2 ≤ Real.log Y := (Real.le_log_iff_exp_le hYpos).mpr hYlow
  have hvW : v ≤ (D + 1) * S := by nlinarith
  have hH : H ⊆ Finset.Icc 1 ⌊Y⌋₊ := Finset.filter_subset _ _
  have hNW : ∀ h ∈ H, Real.log ((N + h : ℕ) : ℝ) ≤ (D + 1) * S := by
    intro h hh
    have hhI := Finset.mem_Icc.mp (hH hh)
    have hnhpos : (0 : ℝ) < ((N + h : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < N + h by omega)
    have hhY : (h : ℝ) ≤ Y :=
      (Nat.cast_le.mpr hhI.2).trans (Nat.floor_le hYpos.le)
    have hhexp : (h : ℝ) ≤ Real.exp (D * S) :=
      hhY.trans (hYhigh.trans (Real.exp_le_exp.mpr hvhigh))
    apply (Real.log_le_iff_le_exp hnhpos).mpr
    calc
      ((N + h : ℕ) : ℝ) ≤ 2 * Real.exp (D * S) := by push_cast; linarith
      _ ≤ Real.exp S * Real.exp (D * S) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        linarith [Real.add_one_le_exp S]
      _ = Real.exp ((D + 1) * S) := by rw [← Real.exp_add]; congr 1; ring
  have hpfx : ∀ h ∈ H, ∃ d p : ℕ,
      IntermediatePrefixWitness (N + h) d p Y v t := by
    intro h hh
    obtain ⟨d, p, hpref, hpsmall, hband⟩ := (Finset.mem_filter.mp hh).2
    obtain ⟨hdpos, hp, hdvd, hdY, hcross, hpd, hdprime, hqprime⟩ := hpref
    refine ⟨d, p, hdvd, hdY, ?_, hp, hpsmall, hband.1, ?_, hdprime, ?_⟩
    · simpa only [Nat.cast_mul] using hcross
    · have hhi := hband.2
      dsimp [t]
      rw [pow_succ] at hhi
      nlinarith
    · intro q hq
      exact hqprime q (Nat.prime_of_mem_primeFactorsList hq)
        (Nat.dvd_of_mem_primeFactorsList hq)
  have hbound := hclass N (Real.exp v) Y v t ((D + 1) * S) H
    (Real.one_lt_exp_iff.mpr hvpos) (Real.log_exp v) hYone hYlog
    hvlow hvSsq htone htv htlow hvW hH hNW hpfx
  have hdecay := hdec v t hvlow htpos hj
  have hQ : 1 ≤ v / t := (one_le_div htpos).mpr htv
  have hQlog : 0 ≤ (v / t) * Real.log (v / t) :=
    mul_nonneg (by linarith) (Real.log_nonneg hQ)
  have harg : r * ((1 + Real.log ((D + 1) * S / v)) * v / t) -
      (v / t) * Real.log (v / t) / 50 +
      C * (v / t) ^ (1 / 5 : ℝ) * Real.log (2 * t) ≤ 0 := by
    have heq : r * ((1 + Real.log ((D + 1) * S / v)) * v / t) =
        r * (1 + Real.log ((D + 1) * S / v)) * (v / t) := by ring
    rw [heq]
    linarith
  change (∑ h ∈ H, (truncatedDivisorCount (Real.exp v) (N + h) : ℝ) ^ r) ≤ _
  exact hbound.trans (by
    have he := Real.exp_le_one_iff.mpr harg
    simpa only [mul_one] using mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 2 * Y))

end Problem337.DivisorMoment

end OAI
end

theorem solution : type_of% @OAI.Problem337.DivisorMoment.eventually_intermediate_band_budget_oai := @OAI.Problem337.DivisorMoment.eventually_intermediate_band_budget_oai
