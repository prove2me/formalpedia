-- Prove2me | solution 1 for OAI.Problem337.prescribed_denominator_corollary
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T10:03:25.316764+00:00
-- url     : https://prove2.me/submissions/760ef4af-2147-42f4-8a90-080519d0d08e

import Mathlib
import Definitions.Def_EgyptianFractions
import Theorems.Thm_OAI_Problem337_every_exact_marker_occurs
import Theorems.Thm_OAI_Problem337_exact_marker_padding
import Theorems.Thm_OAI_Problem337_missing_denominator_semantics
import Theorems.Thm_OAI_Problem337_quantitative_marked_length

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

/-- Exact marker padding implies monotonicity even at the empty small lengths. -/
theorem D_mono_of_padding
    (padding : ∀ r : ℕ, 3 ≤ r → ∀ n : Fin r → ℕ, IsOneExpansion n →
      ∀ m : ℕ, (∃ i : Fin r, n i = m) →
        ∃ n' : Fin (r + 1) → ℕ,
          IsOneExpansion n' ∧ ∃ i : Fin (r + 1), n' i = m) :
    Monotone D := by
  intro r k hrk m hm
  have hr : 3 ≤ r := marker_length_ge_three hm
  induction k, hrk using Nat.le_induction with
  | base => exact hm
  | succ k hrk ih =>
    rcases ih with ⟨hm2, n, hn, hmarker⟩
    obtain ⟨n', hn', hmarker'⟩ := padding k (by omega) n hn m hmarker
    exact ⟨hm2, n', hn', hmarker'⟩

/-- Finitely many markers all occur at every sufficiently large exact length. -/
theorem bounded_markers_eventually
    (hmono : Monotone D)
    (occurs : ∀ m : ℕ, 2 ≤ m → ∃ k : ℕ, m ∈ D k)
    (B : ℕ) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ m : ℕ, 2 ≤ m → m ≤ B → m ∈ D k := by
  induction B with
  | zero =>
    exact ⟨0, by intro k hk m hm hB; omega⟩
  | succ B ih =>
    obtain ⟨K, hK⟩ := ih
    by_cases hB : 2 ≤ B + 1
    · obtain ⟨r, hr⟩ := occurs (B + 1) hB
      refine ⟨max K r, ?_⟩
      intro k hk m hm hmB
      by_cases hle : m ≤ B
      · exact hK k (le_trans (le_max_left _ _) hk) m hm hle
      · have heq : m = B + 1 := by omega
        rw [heq]
        exact hmono (le_trans (le_max_right _ _) hk) hr
    · exact ⟨K, by intro k hk m hm hmB; omega⟩

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_PrescribedAnalysis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

open Filter

namespace Problem337

/-- Taking two logarithms converts a double exponential lower bound to a slope bound. -/
theorem slope_lower_of_double_exp {x c : ℝ} {k : ℕ}
    (hk : 0 < k) (h : Real.exp (Real.exp (c * (k : ℝ))) ≤ x) :
    c ≤ Real.log (Real.log x) / (k : ℝ) := by
  have hfirst : Real.exp (c * (k : ℝ)) ≤ Real.log x := by
    simpa using Real.log_le_log (Real.exp_pos _) h
  have hsecond : c * (k : ℝ) ≤ Real.log (Real.log x) := by
    simpa using Real.log_le_log (Real.exp_pos _) hfirst
  exact (le_div_iff₀ (by exact_mod_cast hk)).2 hsecond

/-- Eventual double exponential bounds lead to eventual lower bounds for the slope. -/
theorem eventually_slope_lower_of_double_exp (f : ℕ → ℝ) (c : ℝ)
    (h : ∀ᶠ k : ℕ in atTop, Real.exp (Real.exp (c * (k : ℝ))) ≤ f k) :
    ∀ᶠ k : ℕ in atTop, c ≤ Real.log (Real.log (f k)) / (k : ℝ) := by
  filter_upwards [h, eventually_gt_atTop (0 : ℕ)] with k h hk
  exact slope_lower_of_double_exp hk h

/-- The lower limiting slope uses only eventual double exponential lower bounds
and boundedness above; no Egyptian fraction constructions enter this step. -/
theorem liminf_slope_lower_of_double_exp (f : ℕ → ℝ) (A : ℝ)
    (hupper : IsBoundedUnder (· ≤ ·) atTop
      (fun k : ℕ => Real.log (Real.log (f k)) / (k : ℝ)))
    (hlower : ∀ c : ℝ, c < A →
      ∀ᶠ k : ℕ in atTop, Real.exp (Real.exp (c * (k : ℝ))) ≤ f k) :
    A ≤ liminf (fun k : ℕ => Real.log (Real.log (f k)) / (k : ℝ)) atTop ∧
    liminf (fun k : ℕ => Real.log (Real.log (f k)) / (k : ℝ)) atTop ≤
      limsup (fun k : ℕ => Real.log (Real.log (f k)) / (k : ℝ)) atTop := by
  have hlow : IsBoundedUnder (· ≥ ·) atTop
      (fun k : ℕ => Real.log (Real.log (f k)) / (k : ℝ)) :=
    ⟨A - 1, eventually_slope_lower_of_double_exp f (A - 1)
      (hlower (A - 1) (by linarith))⟩
  constructor
  · apply (le_liminf_iff' hupper.isCoboundedUnder_ge hlow).2
    intro c hc
    exact eventually_slope_lower_of_double_exp f c (hlower c hc)
  · exact liminf_le_limsup hupper hlow

/-- A coarse elementary bound for log 2 is enough for the stated constant 600. -/
theorem one_div_six_hundred_lt_prescribed_rate :
    (1 : ℝ) / 600 < Real.log 2 / 257 := by
  have hlog := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
  norm_num at hlog
  linarith

/-- Specialization of the family of rates to the explicit constant in the corollary. -/
theorem eventually_double_exp_six_hundred (f : ℕ → ℝ)
    (h : ∀ c : ℝ, c < Real.log 2 / 257 →
      ∀ᶠ k : ℕ in atTop, Real.exp (Real.exp (c * (k : ℝ))) ≤ f k) :
    ∀ᶠ k : ℕ in atTop, Real.exp (Real.exp ((k : ℝ) / 600)) ≤ f k := by
  simpa [div_eq_mul_inv, mul_comm] using
    h (1 / 600) one_div_six_hundred_lt_prescribed_rate

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_PrescribedInversion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

namespace Problem337

/-- Slack in a reciprocal bound, including nonpositive slopes. -/
theorem exists_positive_slack {A c : ℝ} (hA : 0 < A) (hc : c < 1 / A) :
    ∃ ε : ℝ, 0 < ε ∧ c * (A + ε) < 1 := by
  have hAc : c * A < 1 := (lt_div_iff₀ hA).mp hc
  by_cases hc0 : c ≤ 0
  · refine ⟨1, by norm_num, ?_⟩
    have : c * (A + 1) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc0 (by linarith)
    linarith
  · have hcpos : 0 < c := lt_of_not_ge hc0
    refine ⟨(1 / c - A) / 2, ?_, ?_⟩
    · have : A < 1 / c := (lt_div_iff₀ hcpos).mpr (by nlinarith)
      linarith
    · have hcancel : c * (1 / c) = 1 := by field_simp
      nlinarith

/-- Abstract inversion of a short marked-expansion bound.

The hypotheses isolate the combinatorial work: finite initial intervals are eventually
covered, marked expansions can be padded from length at least three, and large markers
have asymptotically short expansions. -/
theorem eventual_double_exp_lower_of_short_markers
    (D : ℕ → Set ℕ) (v : ℕ → ℕ) (A : ℝ) (hA : 0 < A)
    (hmissing : ∀ k, 2 ≤ v k ∧ v k ∉ D k)
    (hsmall : ∀ M : ℕ, ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ∀ m : ℕ, 2 ≤ m → m < M → m ∈ D k)
    (hpad : ∀ r k : ℕ, 3 ≤ r → r ≤ k → D r ⊆ D k)
    (hshort : ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, 2 ≤ M ∧
      ∀ m : ℕ, M ≤ m → ∃ r : ℕ, 3 ≤ r ∧ m ∈ D r ∧
        (r : ℝ) ≤ (A + ε) * Real.log (Real.log (m : ℝ))) :
    ∀ c : ℝ, c < 1 / A → ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      Real.exp (Real.exp (c * (k : ℝ))) ≤ (v k : ℝ) := by
  intro c hc
  obtain ⟨ε, hε, hcoef⟩ := exists_positive_slack hA hc
  obtain ⟨M, hM, hshortM⟩ := hshort ε hε
  obtain ⟨K, hK⟩ := hsmall M
  refine ⟨K, ?_⟩
  intro k hk
  by_contra hnot
  have hvlt : (v k : ℝ) < Real.exp (Real.exp (c * (k : ℝ))) := lt_of_not_ge hnot
  obtain ⟨hv2, hvmissing⟩ := hmissing k
  have hvM : M ≤ v k := by
    by_contra h
    exact hvmissing (hK k hk (v k) hv2 (lt_of_not_ge h))
  obtain ⟨r, hr3, hmem, hrlen⟩ := hshortM (v k) hvM
  have hv1 : (1 : ℝ) < (v k : ℝ) := by exact_mod_cast (show 1 < v k by omega)
  have hvpos : (0 : ℝ) < (v k : ℝ) := by linarith
  have hlogpos : 0 < Real.log (v k : ℝ) := Real.log_pos hv1
  have hlog : Real.log (v k : ℝ) ≤ Real.exp (c * (k : ℝ)) := by
    simpa only [Real.log_exp] using Real.log_le_log hvpos hvlt.le
  have hloglog : Real.log (Real.log (v k : ℝ)) ≤ c * (k : ℝ) := by
    simpa only [Real.log_exp] using Real.log_le_log hlogpos hlog
  have hrkR : (r : ℝ) ≤ (k : ℝ) := calc
    (r : ℝ) ≤ (A + ε) * Real.log (Real.log (v k : ℝ)) := hrlen
    _ ≤ (A + ε) * (c * (k : ℝ)) :=
      mul_le_mul_of_nonneg_left hloglog (by linarith)
    _ = (c * (A + ε)) * (k : ℝ) := by ring
    _ ≤ 1 * (k : ℝ) := mul_le_mul_of_nonneg_right hcoef.le (Nat.cast_nonneg k)
    _ = (k : ℝ) := one_mul _
  have hrk : r ≤ k := by exact_mod_cast hrkR
  exact hvmissing (hpad r k hr3 hrk hmem)

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_UpperSlope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open Filter
open scoped Topology

namespace Problem337

/-- A double logarithm estimate for the elementary denominator bound. -/
theorem loglog_le_of_power_bound {k : ℕ} {x : ℝ} (hk : 2 ≤ k)
    (hx : 2 ≤ x) (hbound : x ≤ 1 + (k : ℝ) ^ (2 ^ (k - 1))) :
    Real.log (Real.log x) ≤ (k : ℝ) * Real.log 2 + Real.log (Real.log k) := by
  have hkR : 2 ≤ (k : ℝ) := by exact_mod_cast hk
  have hkpos : 0 < (k : ℝ) := by linarith
  have hkone : 1 ≤ (k : ℝ) := by linarith
  have hlogk : 0 < Real.log (k : ℝ) := Real.log_pos (by linarith)
  have hp : 1 ≤ (2 : ℕ) ^ (k - 1) := Nat.one_le_pow _ _ (by decide)
  have hpow : 2 ≤ (k : ℝ) ^ (2 ^ (k - 1)) := by
    calc
      2 ≤ (k : ℝ) := hkR
      _ = (k : ℝ) ^ 1 := by simp
      _ ≤ (k : ℝ) ^ (2 ^ (k - 1)) := pow_le_pow_right₀ hkone hp
  have hexp : (2 : ℕ) ^ (k - 1) * 2 = 2 ^ k := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ k)]
  have hbound' : x ≤ (k : ℝ) ^ (2 ^ k) := by
    calc
      x ≤ 1 + (k : ℝ) ^ (2 ^ (k - 1)) := hbound
      _ ≤ ((k : ℝ) ^ (2 ^ (k - 1))) ^ 2 := by nlinarith
      _ = (k : ℝ) ^ (2 ^ k) := by rw [← pow_mul, hexp]
  have hlog : Real.log x ≤ (2 : ℝ) ^ k * Real.log (k : ℝ) := by
    simpa only [Real.log_pow, Nat.cast_pow, Nat.cast_ofNat] using
      Real.log_le_log (by linarith : 0 < x) hbound'
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  calc
    Real.log (Real.log x) ≤ Real.log ((2 : ℝ) ^ k * Real.log (k : ℝ)) :=
      Real.log_le_log hlogx hlog
    _ = (k : ℝ) * Real.log 2 + Real.log (Real.log k) := by
      rw [Real.log_mul (by positivity) (ne_of_gt hlogk), Real.log_pow]

/-- The logarithmic error in the denominator upper bound is negligible. -/
theorem tendsto_log_nat_div_nat :
    Tendsto (fun k : ℕ => Real.log (k : ℝ) / (k : ℝ)) atTop (𝓝 0) := by
  have h := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  simpa [Function.comp_def] using h.comp tendsto_natCast_atTop_atTop

/-- The elementary power upper bound forces the sharp upper logarithmic slope. -/
theorem power_bound_slope_limits (u : ℕ → ℝ)
    (hu : ∀ᶠ k in atTop, 2 ≤ u k ∧
      u k ≤ 1 + (k : ℝ) ^ (2 ^ (k - 1))) :
    0 ≤ liminf (fun k => Real.log (Real.log (u k)) / (k : ℝ)) atTop ∧
    liminf (fun k => Real.log (Real.log (u k)) / (k : ℝ)) atTop ≤
      limsup (fun k => Real.log (Real.log (u k)) / (k : ℝ)) atTop ∧
    limsup (fun k => Real.log (Real.log (u k)) / (k : ℝ)) atTop ≤ Real.log 2 := by
  let f : ℕ → ℝ := fun k => Real.log (Real.log (u k)) / (k : ℝ)
  have hupp : f ≤ᶠ[atTop] (fun k : ℕ => Real.log 2 + Real.log (k : ℝ) / (k : ℝ)) := by
    filter_upwards [hu, eventually_ge_atTop 2] with k hk hk2
    have hkR : 2 ≤ (k : ℝ) := by exact_mod_cast hk2
    have hkpos : 0 < (k : ℝ) := by linarith
    have hlog : Real.log (Real.log (k : ℝ)) ≤ Real.log (k : ℝ) := by
      apply Real.log_le_log (Real.log_pos (by linarith))
      linarith [Real.log_le_sub_one_of_pos hkpos]
    have hmain := loglog_le_of_power_bound hk2 hk.1 hk.2
    calc
      f k ≤ ((k : ℝ) * Real.log 2 + Real.log (k : ℝ)) / (k : ℝ) := by
        apply div_le_div_of_nonneg_right _ hkpos.le
        exact hmain.trans (add_le_add (le_refl _) hlog)
      _ = Real.log 2 + Real.log (k : ℝ) / (k : ℝ) := by
        field_simp
  have hlo : (fun k : ℕ => Real.log (Real.log 2) / (k : ℝ)) ≤ᶠ[atTop] f := by
    filter_upwards [hu, eventually_ge_atTop 2] with k hk hk2
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg k)
    exact Real.log_le_log (Real.log_pos (by norm_num))
      (Real.log_le_log (by norm_num) hk.1)
  have htU : Tendsto (fun k : ℕ => Real.log 2 + Real.log (k : ℝ) / (k : ℝ))
      atTop (𝓝 (Real.log 2)) := by
    simpa using tendsto_const_nhds.add tendsto_log_nat_div_nat
  have htL : Tendsto (fun k : ℕ => Real.log (Real.log 2) / (k : ℝ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hfbU : atTop.IsBoundedUnder (· ≤ ·) f := htU.isBoundedUnder_le.mono_le hupp
  have hfbL : atTop.IsBoundedUnder (· ≥ ·) f := htL.isBoundedUnder_ge.mono_ge hlo
  change 0 ≤ liminf f atTop ∧ liminf f atTop ≤ limsup f atTop ∧
    limsup f atTop ≤ Real.log 2
  refine ⟨?_, liminf_le_limsup hfbU hfbL, ?_⟩
  · calc
      0 = liminf (fun k : ℕ => Real.log (Real.log 2) / (k : ℝ)) atTop := htL.liminf_eq.symm
      _ ≤ liminf f atTop := liminf_le_liminf hlo htL.isBoundedUnder_ge hfbU.isCobounded_flip
  · calc
      limsup f atTop ≤ limsup (fun k : ℕ => Real.log 2 + Real.log (k : ℝ) / (k : ℝ)) atTop :=
        limsup_le_limsup hupp hfbL.isCobounded_flip htU.isBoundedUnder_le
      _ = Real.log 2 := htU.limsup_eq

end Problem337

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_PrescribedCorollary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open Filter

namespace Problem337

/-- The combinatorial hypotheses of the prescribed-denominator corollary imply
all its eventual double-exponential lower bounds. -/
theorem prescribed_lower_of_marked
    (padding : ∀ r : ℕ, 3 ≤ r → ∀ n : Fin r → ℕ, IsOneExpansion n →
      ∀ m : ℕ, (∃ i : Fin r, n i = m) →
        ∃ n' : Fin (r + 1) → ℕ,
          IsOneExpansion n' ∧ ∃ i : Fin (r + 1), n' i = m)
    (occurs : ∀ m : ℕ, 2 ≤ m → ∃ k : ℕ, m ∈ D k)
    (short : ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, 2 ≤ M ∧
      ∀ m : ℕ, M ≤ m → ∃ k : ℕ, ∃ n : Fin k → ℕ,
        IsOneExpansion n ∧ (∃ i : Fin k, n i = m) ∧
          (k : ℝ) ≤ (257 / Real.log 2 + ε) * Real.log (Real.log (m : ℝ)))
    (missing : ∀ k : ℕ, 2 ≤ v k ∧ v k ∉ D k) :
    ∀ c : ℝ, c < Real.log 2 / 257 → ∃ K : ℕ,
      ∀ k : ℕ, K ≤ k → Real.exp (Real.exp (c * (k : ℝ))) ≤ (v k : ℝ) := by
  have hmono : Monotone D := D_mono_of_padding padding
  have hsmall : ∀ M : ℕ, ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ∀ m : ℕ, 2 ≤ m → m < M → m ∈ D k := by
    intro M
    obtain ⟨K, hK⟩ := bounded_markers_eventually hmono occurs M
    exact ⟨K, fun k hk m hm hM => hK k hk m hm hM.le⟩
  have hshort : ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, 2 ≤ M ∧
      ∀ m : ℕ, M ≤ m → ∃ r : ℕ, 3 ≤ r ∧ m ∈ D r ∧
        (r : ℝ) ≤ (257 / Real.log 2 + ε) * Real.log (Real.log (m : ℝ)) := by
    intro ε hε
    obtain ⟨M, hM, h⟩ := short ε hε
    refine ⟨M, hM, ?_⟩
    intro m hm
    obtain ⟨r, n, hn, hmark, hlen⟩ := h m hm
    have hmem : m ∈ D r := ⟨hM.trans hm, n, hn, hmark⟩
    exact ⟨r, marker_length_ge_three hmem, hmem, hlen⟩
  have hA : (0 : ℝ) < 257 / Real.log 2 :=
    div_pos (by norm_num) (Real.log_pos (by norm_num))
  have h := eventual_double_exp_lower_of_short_markers D v (257 / Real.log 2)
    hA missing hsmall (fun r k _ hrk => hmono hrk) hshort
  simpa only [one_div_div] using h

/-- Full assembly of the prescribed-denominator consequence, conditional only
on its exact combinatorial construction and elementary denominator inputs. -/
theorem prescribed_denominator_corollary_of_inputs
    (padding : ∀ r : ℕ, 3 ≤ r → ∀ n : Fin r → ℕ, IsOneExpansion n →
      ∀ m : ℕ, (∃ i : Fin r, n i = m) →
        ∃ n' : Fin (r + 1) → ℕ,
          IsOneExpansion n' ∧ ∃ i : Fin (r + 1), n' i = m)
    (occurs : ∀ m : ℕ, 2 ≤ m → ∃ k : ℕ, m ∈ D k)
    (short : ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, 2 ≤ M ∧
      ∀ m : ℕ, M ≤ m → ∃ k : ℕ, ∃ n : Fin k → ℕ,
        IsOneExpansion n ∧ (∃ i : Fin k, n i = m) ∧
          (k : ℝ) ≤ (257 / Real.log 2 + ε) * Real.log (Real.log (m : ℝ)))
    (missing : ∀ k : ℕ, 2 ≤ v k ∧ v k ∉ D k)
    (upper : ∀ k : ℕ, 1 ≤ k → v k ≤ 1 + k ^ (2 ^ (k - 1))) :
    (∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      Real.exp (Real.exp ((k : ℝ) / 600)) ≤ (v k : ℝ) ∧
      v k ≤ 1 + k ^ (2 ^ (k - 1))) ∧
    (Real.log 2 / 257 ≤ Filter.liminf prescribedSlope Filter.atTop ∧
      Filter.liminf prescribedSlope Filter.atTop ≤
        Filter.limsup prescribedSlope Filter.atTop ∧
      Filter.limsup prescribedSlope Filter.atTop ≤ Real.log 2) ∧
    (∀ c : ℝ, c < Real.log 2 / 257 → ∃ k0 : ℕ,
      ∀ k : ℕ, k0 ≤ k →
        Real.exp (Real.exp (c * (k : ℝ))) ≤ (v k : ℝ)) := by
  have rates := prescribed_lower_of_marked padding occurs short missing
  have ratesE : ∀ c : ℝ, c < Real.log 2 / 257 →
      ∀ᶠ k : ℕ in atTop, Real.exp (Real.exp (c * (k : ℝ))) ≤ (v k : ℝ) := by
    intro c hc
    exact eventually_atTop.2 (rates c hc)
  have hpower : ∀ᶠ k : ℕ in atTop, 2 ≤ (v k : ℝ) ∧
      (v k : ℝ) ≤ 1 + (k : ℝ) ^ (2 ^ (k - 1)) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
    constructor
    · exact_mod_cast (missing k).1
    · exact_mod_cast upper k hk
  have hbounded : IsBoundedUnder (· ≤ ·) atTop prescribedSlope := by
    refine ⟨Real.log 2 + 1, ?_⟩
    change ∀ᶠ k : ℕ in atTop, prescribedSlope k ≤ Real.log 2 + 1
    filter_upwards [hpower, eventually_ge_atTop (2 : ℕ)] with k hk hk2
    have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
    have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
    have hlogpos : 0 < Real.log (k : ℝ) := Real.log_pos (by linarith)
    have hloglog : Real.log (Real.log (k : ℝ)) ≤ (k : ℝ) := by
      linarith [Real.log_le_sub_one_of_pos hkpos,
        Real.log_le_sub_one_of_pos hlogpos]
    have h := loglog_le_of_power_bound hk2 hk.1 hk.2
    unfold prescribedSlope
    apply (div_le_iff₀ hkpos).2
    nlinarith
  have hlow := liminf_slope_lower_of_double_exp (fun k => (v k : ℝ))
    (Real.log 2 / 257) hbounded ratesE
  have hupp := power_bound_slope_limits (fun k => (v k : ℝ)) hpower
  refine ⟨?_, ⟨hlow.1, hlow.2, hupp.2.2⟩, rates⟩
  have hexp := eventually_double_exp_six_hundred (fun k => (v k : ℝ)) ratesE
  apply eventually_atTop.1
  filter_upwards [hexp, eventually_ge_atTop (1 : ℕ)] with k hk hk1
  exact ⟨hk, upper k hk1⟩

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

theorem prescribed_denominator_corollary_oai :
    (∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
    Real.exp (Real.exp ((k : ℝ) / 600)) ≤ (v k : ℝ) ∧
    v k ≤ 1 + k ^ (2 ^ (k - 1))) ∧
  (Real.log 2 / 257 ≤ Filter.liminf prescribedSlope Filter.atTop ∧
    Filter.liminf prescribedSlope Filter.atTop ≤
      Filter.limsup prescribedSlope Filter.atTop ∧
    Filter.limsup prescribedSlope Filter.atTop ≤ Real.log 2) ∧
  (∀ c : ℝ, c < Real.log 2 / 257 → ∃ k0 : ℕ,
    ∀ k : ℕ, k0 ≤ k →
      Real.exp (Real.exp (c * (k : ℝ))) ≤ (v k : ℝ)) := by
  exact prescribed_denominator_corollary_of_inputs
    exact_marker_padding every_exact_marker_occurs quantitative_marked_length
    (fun k => ⟨(missing_denominator_semantics k).2.2.1,
      (missing_denominator_semantics k).2.2.2.1⟩)
    (fun k => (missing_denominator_semantics k).2.2.2.2.2)

end Problem337

end

end OAI
end

theorem solution : type_of% @OAI.Problem337.prescribed_denominator_corollary_oai := @OAI.Problem337.prescribed_denominator_corollary_oai
