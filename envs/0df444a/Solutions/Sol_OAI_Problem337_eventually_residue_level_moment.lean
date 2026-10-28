-- Prove2me | solution 1 for OAI.Problem337.eventually_residue_level_moment
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T10:07:54.012759+00:00
-- url     : https://prove2.me/submissions/b9b700d7-7a16-4fa5-be20-42a96815d352

import Mathlib
import Definitions.Def_OAIQ8EF000
import Theorems.Thm_OAI_Problem337_DivisorMoment_eventually_intermediate_band_budget

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
-- module Solutions.OAIQ8_EF.EgyptianFractions_ResidueLevels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

open Filter

namespace Problem337.ResidueLevels

theorem before_depth_iff {A m η : ℝ} (hm : 0 < m) (hη : 0 < η) (j : ℕ) :
    j < depth A m η ↔ m < A - η * m * j := by
  rw [depth, Nat.lt_ceil, lt_div_iff₀ (mul_pos hη hm)]
  constructor <;> intro h <;> nlinarith

theorem half_log_le_next {A m η : ℝ} (hm : 0 < m) (hη : 0 < η)
    (hηhalf : η ≤ 1 / 2) {j : ℕ} (hj : j < depth A m η) :
    (A - η * m * j) / 2 ≤ A - η * m * (j + 1 : ℕ) := by
  have hj' := (before_depth_iff hm hη j).1 hj
  have hηm := mul_le_mul_of_nonneg_right hηhalf hm.le
  push_cast
  nlinarith

theorem sqrt_level_le_next {A m η : ℝ} (hm : 0 < m) (hη : 0 < η)
    (hηhalf : η ≤ 1 / 2) {j : ℕ} (hj : j < depth A m η) :
    Real.sqrt (level A m η j) ≤ level A m η (j + 1) := by
  rw [Real.sqrt_le_left (level_pos A m η (j + 1)).le]
  simp only [level, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have h := half_log_le_next hm hη hηhalf hj
  norm_num at *
  linarith

theorem tendsto_div_log : Tendsto (fun S : ℝ => S / Real.log S) atTop atTop := by
  have ht : Tendsto (fun S : ℝ => Real.log S / S) atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  apply tendsto_atTop.2
  intro b
  let c : ℝ := max b 1
  have hc : 0 < c := by dsimp [c]; positivity
  filter_upwards [ht.eventually (gt_mem_nhds (one_div_pos.mpr hc)),
    eventually_gt_atTop (1 : ℝ)] with S hratio hS
  have hSp : 0 < S := by linarith
  have hlogp : 0 < Real.log S := Real.log_pos hS
  have hprod := (div_lt_div_iff₀ hSp hc).1 hratio
  have hlt : c < S / Real.log S := (lt_div_iff₀ hlogp).2 (by nlinarith)
  exact (le_max_left b 1).trans hlt.le

theorem scale_bounds {S : ℝ} (hS : 0 < S) (hlog : 0 < Real.log S)
    (hratio : 2 ≤ S / Real.log S) :
    S / (2 * Real.log S) ≤ (scale S : ℝ) ∧
      (scale S : ℝ) ≤ S / Real.log S := by
  have hx : 0 ≤ S / Real.log S := div_nonneg hS.le hlog.le
  have hfloor := Nat.lt_floor_add_one (S / Real.log S)
  have hle := Nat.floor_le hx
  change S / Real.log S < (scale S : ℝ) + 1 at hfloor
  change (scale S : ℝ) ≤ S / Real.log S at hle
  have heq : S / (2 * Real.log S) = (S / Real.log S) / 2 := by ring
  refine ⟨?_, hle⟩
  rw [heq]
  linarith

theorem eventually_scale_bounds : ∀ᶠ S : ℝ in atTop,
    1 ≤ Real.log S ∧ 2 ≤ scale S ∧
    S / (2 * Real.log S) ≤ (scale S : ℝ) ∧
    (scale S : ℝ) ≤ S / Real.log S := by
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    tendsto_div_log.eventually (eventually_ge_atTop (2 : ℝ)),
    eventually_gt_atTop (1 : ℝ)] with S hlog hratio hS
  refine ⟨hlog, Nat.le_floor hratio, ?_⟩
  exact scale_bounds (by linarith) (by linarith) hratio

theorem factor_le {A m η S : ℝ} {C : ℕ} (hC : 0 < C) (j : ℕ) :
    factor A m η S C j ≤ C := by
  unfold factor
  split_ifs <;> omega

end Problem337.ResidueLevels

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_DensityMomentBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
open Filter

namespace Problem337

/-- The density descent and the arithmetic moment use exactly the same count. -/
theorem densityDivisorCount_eq_truncated (X : ℝ) (n : ℕ) :
    densityDivisorCount X n = (truncatedDivisorCount X n : ℝ) := rfl

theorem densityMomentParameter_ge_one {DM : ℝ} (hDM : 1 < DM) :
    1 ≤ densityMomentParameter DM := by
  unfold densityMomentParameter
  linarith

/-- Each nonterminal geometric level is inside the divisor-moment window. -/
theorem residue_level_moment_window
    {DM S m η : ℝ} (hDM : 1 < DM) (hS : 0 ≤ S)
    (hm : 0 < m) (hη : 0 < η) (hηhalf : η ≤ 1 / 2)
    (hmlo : S / (2 * Real.log S) ≤ m)
    {j : ℕ} (hj : j < ResidueLevels.depth ((DM + 2) * S) m η) :
    S / (2 * Real.log S) ≤
        Real.log (ResidueLevels.level ((DM + 2) * S) m η j) ∧
    Real.log (ResidueLevels.level ((DM + 2) * S) m η j) ≤
        densityMomentParameter DM * S ∧
    Real.sqrt (ResidueLevels.level ((DM + 2) * S) m η j) ≤
        ResidueLevels.level ((DM + 2) * S) m η (j + 1) ∧
    ResidueLevels.level ((DM + 2) * S) m η (j + 1) ≤
        ResidueLevels.level ((DM + 2) * S) m η j := by
  have hjlog := (ResidueLevels.before_depth_iff hm hη j).mp hj
  have hsub : 0 ≤ η * m * (j : ℝ) := by positivity
  have hDS : (DM + 2) * S ≤ densityMomentParameter DM * S := by
    apply mul_le_mul_of_nonneg_right _ hS
    unfold densityMomentParameter
    linarith
  refine ⟨?_, ?_, ResidueLevels.sqrt_level_le_next hm hη hηhalf hj, ?_⟩
  · simpa only [ResidueLevels.level, Real.log_exp] using hmlo.trans hjlog.le
  · simp only [ResidueLevels.level, Real.log_exp]
    linarith
  · exact (ResidueLevels.level_strictAnti hm hη (Nat.lt_succ_self j)).le

/-- The changing factor and any divisor of the common denominator give a
shift with the same fixed exponential parameter, uniformly in the level. -/
theorem residue_level_shift_bound
    {DM S m η : ℝ} (_hDM : 1 < DM) (hS : 0 ≤ S)
    {C M t : ℕ} (hCpos : 0 < C) (hMpos : 0 < M)
    (hC : (C : ℝ) ≤ Real.exp (8 * (DM + 2) * S))
    (hM : (M : ℝ) ≤ Real.exp (DM * S)) (ht : t ∣ M) (j : ℕ) :
    ((ResidueLevels.factor ((DM + 2) * S) m η S C j * t : ℕ) : ℝ) ≤
      Real.exp (densityMomentParameter DM * S) := by
  have htM : (t : ℝ) ≤ M := by exact_mod_cast Nat.le_of_dvd hMpos ht
  have hfactor : (ResidueLevels.factor ((DM + 2) * S) m η S C j : ℝ) ≤ C := by
    exact_mod_cast ResidueLevels.factor_le hCpos j
  calc
    _ ≤ (C : ℝ) * M := by
      push_cast
      exact mul_le_mul hfactor htM (Nat.cast_nonneg t) (Nat.cast_nonneg C)
    _ ≤ Real.exp (8 * (DM + 2) * S) * Real.exp (DM * S) :=
      mul_le_mul hC hM (Nat.cast_nonneg M) (Real.exp_pos _).le
    _ = Real.exp ((8 * (DM + 2) + DM) * S) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (densityMomentParameter DM * S) := by
      apply Real.exp_le_exp.mpr
      unfold densityMomentParameter
      nlinarith

/-- Pointwise adapter from the uniform arithmetic estimate to the exact
shifted-moment field consumed by `DensityResidueFamily`. -/
theorem residue_level_moment_of_uniform
    {DM S m η r : ℝ} (hDM : 1 < DM) (hS : 0 ≤ S)
    (hm : 0 < m) (hη : 0 < η) (hηhalf : η ≤ 1 / 2)
    (hmlo : S / (2 * Real.log S) ≤ m)
    (hmoment : ∀ (X Y : ℝ) (N : ℕ),
      S / (2 * Real.log S) ≤ Real.log X →
      Real.log X ≤ densityMomentParameter DM * S →
      Real.sqrt X ≤ Y → Y ≤ X →
      (N : ℝ) ≤ Real.exp (densityMomentParameter DM * S) →
      (∑ h ∈ Finset.Icc 1 ⌊Y⌋₊,
        (truncatedDivisorCount X (N + h) : ℝ) ^ r) ≤
          Y * Real.exp (S ^ (1 / 4 : ℝ)))
    {C M t : ℕ} (hCpos : 0 < C) (hMpos : 0 < M)
    (hC : (C : ℝ) ≤ Real.exp (8 * (DM + 2) * S))
    (hM : (M : ℝ) ≤ Real.exp (DM * S)) (ht : t ∣ M)
    {j : ℕ} (hj : j < ResidueLevels.depth ((DM + 2) * S) m η) :
    (∑ h ∈ Finset.Icc 1 ⌊ResidueLevels.level ((DM + 2) * S) m η (j + 1)⌋₊,
      densityDivisorCount (ResidueLevels.level ((DM + 2) * S) m η j)
        (ResidueLevels.factor ((DM + 2) * S) m η S C j * t + h) ^ r) ≤
      ResidueLevels.level ((DM + 2) * S) m η (j + 1) *
        Real.exp (S ^ (1 / 4 : ℝ)) := by
  obtain ⟨hlo, hhi, hsqrt, hnext⟩ :=
    residue_level_moment_window hDM hS hm hη hηhalf hmlo hj
  simpa only [densityDivisorCount_eq_truncated] using
    hmoment _ _ _ hlo hhi hsqrt hnext
      (residue_level_shift_bound hDM hS hCpos hMpos hC hM ht j)

/-- One eventual scalar moment theorem supplies every level and divisor
simultaneously. The threshold does not depend on `C`, `M`, `j`, or `t`. -/
theorem eventually_residue_level_moment_of_uniform
    (DM η r : ℝ) (hDM : 1 < DM) (hη : 0 < η) (hηhalf : η ≤ 1 / 2)
    (hmoment : ∀ᶠ S : ℝ in atTop, ∀ (X Y : ℝ) (N : ℕ),
      S / (2 * Real.log S) ≤ Real.log X →
      Real.log X ≤ densityMomentParameter DM * S →
      Real.sqrt X ≤ Y → Y ≤ X →
      (N : ℝ) ≤ Real.exp (densityMomentParameter DM * S) →
      (∑ h ∈ Finset.Icc 1 ⌊Y⌋₊,
        (truncatedDivisorCount X (N + h) : ℝ) ^ r) ≤
          Y * Real.exp (S ^ (1 / 4 : ℝ))) :
    ∀ᶠ S : ℝ in atTop, ∀ C M : ℕ, 0 < C → 0 < M →
      (C : ℝ) ≤ Real.exp (8 * (DM + 2) * S) →
      (M : ℝ) ≤ Real.exp (DM * S) →
      ∀ j : ℕ, j < ResidueLevels.depth ((DM + 2) * S) (ResidueLevels.scale S) η →
      ∀ t : ℕ, t ∣ M →
      (∑ h ∈ Finset.Icc 1
          ⌊ResidueLevels.level ((DM + 2) * S) (ResidueLevels.scale S) η (j + 1)⌋₊,
        densityDivisorCount
          (ResidueLevels.level ((DM + 2) * S) (ResidueLevels.scale S) η j)
          (ResidueLevels.factor ((DM + 2) * S) (ResidueLevels.scale S) η S C j * t + h)
          ^ r) ≤
        ResidueLevels.level ((DM + 2) * S) (ResidueLevels.scale S) η (j + 1) *
          Real.exp (S ^ (1 / 4 : ℝ)) := by
  filter_upwards [hmoment, ResidueLevels.eventually_scale_bounds,
    eventually_ge_atTop (0 : ℝ)] with S hmoment hscale hS
  intro C M hCpos hMpos hC hM j hj t ht
  have hm : (0 : ℝ) < ResidueLevels.scale S := by
    exact_mod_cast (show 0 < ResidueLevels.scale S by omega)
  exact residue_level_moment_of_uniform hDM hS hm hη hηhalf hscale.2.2.1
    hmoment hCpos hMpos hC hM ht hj

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_DyadicBands
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.DyadicBands

lemma exists_band {a B x : ℝ} (ha : 0 < a) (hax : a ≤ x) (hxB : x ≤ B) :
    ∃ j : ℕ, j < bandCount a B ∧ InBand a j x := by
  have hratio : 1 ≤ x / a := (le_div_iff₀ ha).2 (by simpa using hax)
  obtain ⟨j, hjlo, hjhi⟩ := exists_nat_pow_near hratio (by norm_num : (1 : ℝ) < 2)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hjB : (2 : ℝ) ^ j ≤ B / a :=
    hjlo.trans (div_le_div_of_nonneg_right hxB ha.le)
  have hjlog := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ j) hjB
  rw [Real.log_pow] at hjlog
  have hjbound : (j : ℝ) ≤ Real.log (B / a) / Real.log 2 :=
    (le_div_iff₀ hlog2).2 hjlog
  refine ⟨j, ?_, ?_, ?_⟩
  · exact Nat.lt_succ_of_le (Nat.le_floor hjbound)
  · have h := (le_div_iff₀ ha).1 hjlo
    nlinarith
  · have h := (div_lt_iff₀ ha).1 hjhi
    nlinarith

lemma bandCount_le {a B : ℝ} (ha : 0 < a) (haB : a ≤ B) :
    (bandCount a B : ℝ) ≤ 1 + Real.log (B / a) / Real.log 2 := by
  have hquot : 1 ≤ B / a := (le_div_iff₀ ha).2 (by simpa using haB)
  have hlog : 0 ≤ Real.log (B / a) := Real.log_nonneg hquot
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hf := Nat.floor_le (div_nonneg hlog hlog2.le)
  unfold bandCount
  push_cast
  linarith

/-- If the entire scale lies below `S²`, only `O(log S)` bands are needed. -/
lemma bandCount_le_log {a B S : ℝ} (ha : 1 ≤ a) (haB : a ≤ B)
    (hS : 2 ≤ S) (hB : B ≤ S ^ 2) :
    (bandCount a B : ℝ) ≤ (3 / Real.log 2) * Real.log S := by
  have ha0 : 0 < a := by linarith
  have hB0 : 0 < B := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogS : Real.log 2 ≤ Real.log S := Real.log_le_log (by norm_num) hS
  have hquot : B / a ≤ S ^ 2 := by
    calc
      B / a ≤ B / 1 := div_le_div_of_nonneg_left hB0.le (by norm_num) ha
      _ ≤ S ^ 2 := by simpa using hB
  have hquot0 : 0 < B / a := div_pos hB0 ha0
  have hlog := Real.log_le_log hquot0 hquot
  rw [Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hlogdiv : Real.log (B / a) / Real.log 2 ≤
      (2 * Real.log S) / Real.log 2 :=
    div_le_div_of_nonneg_right hlog hlog2.le
  have hone : 1 ≤ Real.log S / Real.log 2 :=
    (le_div_iff₀ hlog2).2 (by simpa using hlogS)
  have hc := bandCount_le ha0 haB
  have hbudget : 1 + Real.log (B / a) / Real.log 2 ≤
      (3 / Real.log 2) * Real.log S := by
    simp only [div_eq_mul_inv] at hlogdiv hone ⊢
    nlinarith
  exact hc.trans hbudget

/-- The precise dyadic cover used for the intermediate-prime range in the
uniform divisor moment. The constant is absolute; the threshold depends on `D`. -/
theorem eventually_divisor_band_cover (D : ℝ) :
    ∀ᶠ S : ℝ in Filter.atTop, ∀ v : ℝ,
      S / (2 * Real.log S) ≤ v → v ≤ D * S →
      4 * Real.log S ≤ v ^ (15 / 16 : ℝ) →
      ∃ J : ℕ, (J : ℝ) ≤ (3 / Real.log 2) * Real.log S ∧
        ∀ w : ℝ, 4 * Real.log S ≤ w → w < v ^ (15 / 16 : ℝ) →
          ∃ j : ℕ, j < J ∧ InBand (4 * Real.log S) j w := by
  filter_upwards [Filter.eventually_ge_atTop (max D (Real.exp 4))] with S hS
  have hSD : D ≤ S := (le_max_left _ _).trans hS
  have hSe : Real.exp 4 ≤ S := (le_max_right _ _).trans hS
  have hSpos : 0 < S := (Real.exp_pos 4).trans_le hSe
  have hlog : 4 ≤ Real.log S := (Real.le_log_iff_exp_le hSpos).2 hSe
  have hS2 : 2 ≤ S := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hquad := Real.pow_div_factorial_le_exp (Real.log S) (by linarith) 2
  norm_num at hquad
  rw [Real.exp_log hSpos] at hquad
  have htwo : 2 * Real.log S ≤ S := by nlinarith
  have hlogpos : 0 < 2 * Real.log S := by positivity
  have hratio : 1 ≤ S / (2 * Real.log S) :=
    (le_div_iff₀ hlogpos).2 (by simpa using htwo)
  intro v hvlo hvhi haB
  have hv1 : 1 ≤ v := hratio.trans hvlo
  have hrpow : v ^ (15 / 16 : ℝ) ≤ v := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hv1 (by norm_num : (15 / 16 : ℝ) ≤ 1)
  have hB : v ^ (15 / 16 : ℝ) ≤ S ^ 2 := by
    calc
      v ^ (15 / 16 : ℝ) ≤ v := hrpow
      _ ≤ D * S := hvhi
      _ ≤ S ^ 2 := by nlinarith
  refine ⟨bandCount (4 * Real.log S) (v ^ (15 / 16 : ℝ)),
    bandCount_le_log (by linarith) haB hS2 hB, ?_⟩
  intro w hwlo hwhi
  exact exists_band (by positivity) hwlo hwhi.le

end Problem337.DyadicBands

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_PrimeFactorPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- A finite product crosses any threshold lying between its initial multiplier
and its final value. No monotonicity assumptions on the factors are needed. -/
theorem list_product_crossing (l : List ℕ) (d : ℕ) (y : ℝ)
    (hdy : (d : ℝ) ≤ y) (hy : y < (d * l.prod : ℕ)) :
    ∃ a : List ℕ, ∃ p : ℕ, ∃ b : List ℕ,
      l = a ++ p :: b ∧ (d * a.prod : ℕ) ≤ y ∧ y < (d * a.prod * p : ℕ) := by
  induction l generalizing d with
  | nil => simp only [List.prod_nil, mul_one] at hy; linarith
  | cons p l ih =>
    by_cases hp : y < (d * p : ℕ)
    · exact ⟨[], p, l, rfl, by simpa using hdy, by simpa using hp⟩
    · have hdp : (d * p : ℕ) ≤ y := le_of_not_gt hp
      have htail : y < ((d * p) * l.prod : ℕ) := by
        simpa only [List.prod_cons, Nat.mul_assoc] using hy
      obtain ⟨a, q, b, hl, ha, hq⟩ := ih (d * p) hdp htail
      refine ⟨p :: a, q, b, by simp [hl], ?_, ?_⟩
      · simpa only [List.prod_cons, Nat.mul_assoc] using ha
      · simpa only [List.prod_cons, Nat.mul_assoc] using hq

/-- The longest sorted prime-factor prefix below a real threshold.
The two prime-factor separation statements allow the smooth and rough parts
of the divisor-moment argument to be estimated independently. -/
theorem prime_factor_prefix (n : ℕ) (y : ℝ) (hy : 1 ≤ y) (hyn : y < n) :
    ∃ d p : ℕ, 0 < d ∧ p.Prime ∧ d ∣ n ∧
      (d : ℝ) ≤ y ∧ y < (d * p : ℕ) ∧ p ∣ n / d ∧
      (∀ q : ℕ, q.Prime → q ∣ d → q ≤ p) ∧
      (∀ q : ℕ, q.Prime → q ∣ n / d → p ≤ q) := by
  have hnpos : 0 < n := by exact_mod_cast (show (0 : ℝ) < n by linarith)
  have hprod := Nat.prod_primeFactorsList hnpos.ne'
  obtain ⟨a, p, b, hsplit, ha, hp⟩ := list_product_crossing n.primeFactorsList 1 y
    (by simpa using hy) (by simpa [hprod] using hyn)
  simp only [one_mul] at ha hp
  have hprimes : ∀ q ∈ a ++ p :: b, q.Prime := by
    intro q hq
    exact Nat.prime_of_mem_primeFactorsList (hsplit ▸ hq)
  have hpa : ∀ q ∈ a, q.Prime := fun q hq => hprimes q (List.mem_append_left _ hq)
  have hpb : ∀ q ∈ p :: b, q.Prime := fun q hq => hprimes q (List.mem_append_right _ hq)
  have hd : 0 < a.prod := List.prod_pos (fun q hq => (hpa q hq).pos)
  have he : 0 < (p :: b).prod := List.prod_pos (fun q hq => (hpb q hq).pos)
  have hmul : n = a.prod * (p :: b).prod := by
    rw [← hprod, hsplit, List.prod_append]
  have hdiv : n / a.prod = (p :: b).prod := by
    rw [hmul, Nat.mul_div_cancel_left _ hd]
  have hsort := (Nat.primeFactorsList_sorted n).pairwise
  rw [hsplit] at hsort
  obtain ⟨hasort, hbsort, hcross⟩ := List.pairwise_append.mp hsort
  refine ⟨a.prod, p, hd, hpb p (by simp), ⟨(p :: b).prod, hmul⟩,
    ha, hp, ?_, ?_, ?_⟩
  · rw [hdiv]
    exact List.dvd_prod (by simp)
  · intro q hq hqd
    have hqmem : q ∈ a := (Nat.primeFactorsList_unique rfl hpa).mem_iff.mpr
      ((Nat.mem_primeFactorsList hd.ne').mpr ⟨hq, hqd⟩)
    exact hcross q hqmem p (by simp)
  · intro q hq hqd
    rw [hdiv] at hqd
    have hqmem : q ∈ p :: b := (Nat.primeFactorsList_unique rfl hpb).mem_iff.mpr
      ((Nat.mem_primeFactorsList he.ne').mpr ⟨hq, hqd⟩)
    rcases List.mem_cons.mp hqmem with heq | hqb
    · omega
    · exact (List.pairwise_cons.mp hbsort).1 q hqb

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_DivisorClasses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.DivisorClasses

attribute [local instance] Classical.propDecidable

/-- Every integer belongs to one of the three actual prime-prefix regimes.
No choice of prefix, divisor estimate, or distribution assertion is assumed. -/
theorem class_cover (n : ℕ) (S v Y : ℝ) (J : ℕ)
    (hY : 1 ≤ Real.sqrt Y)
    (hbands : ∀ w : ℝ, 4 * Real.log S ≤ w → w < v ^ (15 / 16 : ℝ) →
      ∃ j : ℕ, j < J ∧ DyadicBands.InBand (4 * Real.log S) j w) :
    LargeClass n v Y ∨ SmallClass n S v Y ∨
      ∃ j : ℕ, j < J ∧ BandClass n S v Y j := by
  by_cases hn : (n : ℝ) ≤ Real.sqrt Y
  · exact Or.inl (Or.inl hn)
  obtain ⟨d, p, hpref⟩ := prime_factor_prefix n (Real.sqrt Y) hY (lt_of_not_ge hn)
  have hw : PrefixWitness n Y d p := hpref
  by_cases hp : v ^ (15 / 16 : ℝ) ≤ Real.log p
  · exact Or.inl (Or.inr ⟨d, p, hw, hp⟩)
  have hphi : Real.log p < v ^ (15 / 16 : ℝ) := lt_of_not_ge hp
  by_cases hsmall : Real.log p < 4 * Real.log S
  · exact Or.inr (Or.inl ⟨d, p, hw, hphi, hsmall⟩)
  obtain ⟨j, hj, hband⟩ := hbands (Real.log p) (le_of_not_gt hsmall) hphi
  exact Or.inr (Or.inr ⟨j, hj, d, p, hw, hphi, hband⟩)

/-- An occupied intermediate class automatically has an admissible lower scale. -/
theorem band_scale_lt {n : ℕ} {S v Y : ℝ} {j : ℕ}
    (h : BandClass n S v Y j) :
    4 * Real.log S * 2 ^ j < v ^ (15 / 16 : ℝ) := by
  obtain ⟨d, p, _, hp, hband⟩ := h
  exact hband.1.trans_lt hp

/-- Finite summation over the actual regimes. Overlap of prefix witnesses is
harmless because all weights are nonnegative. -/
theorem sum_le_class_bounds {ι : Type*} (H : Finset ι) (n : ι → ℕ)
    (w : ι → ℝ) (S v Y : ℝ) (J : ℕ) (L M A : ℝ)
    (hY : 1 ≤ Real.sqrt Y)
    (hbands : ∀ x : ℝ, 4 * Real.log S ≤ x → x < v ^ (15 / 16 : ℝ) →
      ∃ j : ℕ, j < J ∧ DyadicBands.InBand (4 * Real.log S) j x)
    (hw : ∀ i ∈ H, 0 ≤ w i)
    (hlarge : (∑ i ∈ H with LargeClass (n i) v Y, w i) ≤ L)
    (hsmall : (∑ i ∈ H with SmallClass (n i) S v Y, w i) ≤ M)
    (hband : ∀ j < J, (∑ i ∈ H with BandClass (n i) S v Y j, w i) ≤ A) :
    (∑ i ∈ H, w i) ≤ L + M + (J : ℝ) * A := by
  classical
  have hpoint : ∀ i ∈ H, w i ≤
      (if LargeClass (n i) v Y then w i else 0) +
      (if SmallClass (n i) S v Y then w i else 0) +
      ∑ j ∈ Finset.range J, if BandClass (n i) S v Y j then w i else 0 := by
    intro i hi
    have hl0 : 0 ≤ if LargeClass (n i) v Y then w i else 0 := by
      split_ifs <;> simp_all
    have hs0 : 0 ≤ if SmallClass (n i) S v Y then w i else 0 := by
      split_ifs <;> simp_all
    have hb0 : ∀ j : ℕ, 0 ≤ if BandClass (n i) S v Y j then w i else 0 := by
      intro j
      split_ifs <;> simp_all
    have hsum0 := Finset.sum_nonneg (s := Finset.range J) (fun j _ => hb0 j)
    rcases class_cover (n i) S v Y J hY hbands with hl | hs | ⟨j, hj, hb⟩
    · rw [ite_eq_left hl]
      linarith
    · rw [ite_eq_left hs]
      linarith
    · have hsingle := Finset.single_le_sum (s := Finset.range J)
        (fun j _ => hb0 j) (Finset.mem_range.mpr hj)
      rw [ite_eq_left hb] at hsingle
      linarith
  calc
    (∑ i ∈ H, w i) ≤ ∑ i ∈ H,
        ((if LargeClass (n i) v Y then w i else 0) +
        (if SmallClass (n i) S v Y then w i else 0) +
        ∑ j ∈ Finset.range J, if BandClass (n i) S v Y j then w i else 0) :=
      Finset.sum_le_sum hpoint
    _ = (∑ i ∈ H with LargeClass (n i) v Y, w i) +
        (∑ i ∈ H with SmallClass (n i) S v Y, w i) +
        ∑ j ∈ Finset.range J, ∑ i ∈ H with BandClass (n i) S v Y j, w i := by
      simp only [Finset.sum_add_distrib, Finset.sum_filter]
      rw [Finset.sum_comm]
    _ ≤ L + M + ∑ _j ∈ Finset.range J, A := by
      apply add_le_add (add_le_add hlarge hsmall)
      exact Finset.sum_le_sum (fun j hj => hband j (Finset.mem_range.mp hj))
    _ = L + M + (J : ℝ) * A := by simp

end Problem337.DivisorClasses

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_DivisorMomentAbsorption
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open Filter Asymptotics

namespace Problem337.DivisorMomentAbsorption

/-- The large-fiber exponent is negligible compared with the quarter power. -/
theorem large_exponent_majorant_littleO (A B : ℝ) :
    (fun S : ℝ => A * (S ^ (1 / 16 : ℝ) * Real.log S) + B * Real.log S)
      =o[atTop] (fun S : ℝ => S ^ (1 / 4 : ℝ)) := by
  have hprod := (isBigO_refl (fun S : ℝ => S ^ (1 / 16 : ℝ)) atTop).mul_isLittleO
    (isLittleO_log_rpow_atTop (show (0 : ℝ) < 3 / 16 by norm_num))
  have hprod' : (fun S : ℝ => S ^ (1 / 16 : ℝ) * Real.log S)
      =o[atTop] (fun S : ℝ => S ^ (1 / 4 : ℝ)) := by
    refine hprod.congr' (Filter.Eventually.of_forall fun _ => rfl) ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with S hS
    rw [← Real.rpow_add hS]
    norm_num
  exact (hprod'.const_mul_left A).add
    ((isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 4 by norm_num)).const_mul_left B)

/-- A flexible final absorption step: the intermediate/small-fiber term may be
any exponential with a nonpositive exponent. -/
theorem eventually_absorb_large_contribution (A B C : ℝ) (hA : 0 ≤ A) :
    ∀ᶠ S : ℝ in atTop, ∀ u : ℝ, u ≤ 0 →
      Real.exp (A * S ^ (1 / 16 : ℝ) * Real.log (Real.log S) + B * Real.log S) +
        2 * Real.exp u + C * Real.log S ≤ Real.exp (S ^ (1 / 4 : ℝ)) := by
  have hmajor := (large_exponent_majorant_littleO A B).bound
    (show (0 : ℝ) < 1 / 2 by norm_num)
  have hlog := ((isLittleO_log_rpow_atTop
    (show (0 : ℝ) < 1 / 4 by norm_num)).const_mul_left C).bound
    (show (0 : ℝ) < 1 / 2 by norm_num)
  have hg := (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 4 by norm_num)).eventually_ge_atTop 4
  filter_upwards [hmajor, hlog, hg, eventually_ge_atTop (2 : ℝ)] with S hmajor hlog hg hS
  intro u hu
  have hS0 : 0 < S := by linarith
  have hg0 : 0 ≤ S ^ (1 / 4 : ℝ) := Real.rpow_nonneg hS0.le _
  have hlog0 : 0 ≤ Real.log S := Real.log_nonneg (by linarith)
  have hmajor' : A * (S ^ (1 / 16 : ℝ) * Real.log S) + B * Real.log S ≤
      S ^ (1 / 4 : ℝ) / 2 := by
    have := (Real.le_norm_self (A * (S ^ (1 / 16 : ℝ) * Real.log S) + B * Real.log S)).trans hmajor
    simpa only [Real.norm_eq_abs, abs_of_nonneg hg0, one_div_mul_eq_div] using this
  have hlog' : C * Real.log S ≤ S ^ (1 / 4 : ℝ) / 2 := by
    have := (Real.le_norm_self (C * Real.log S)).trans hlog
    simpa only [Real.norm_eq_abs, abs_of_nonneg hg0, one_div_mul_eq_div] using this
  have hexponent : A * S ^ (1 / 16 : ℝ) * Real.log (Real.log S) + B * Real.log S ≤
      S ^ (1 / 4 : ℝ) / 2 := by
    apply le_trans _ hmajor'
    have h := mul_le_mul_of_nonneg_left (Real.log_le_self hlog0)
      (mul_nonneg hA (Real.rpow_nonneg hS0.le (1 / 16 : ℝ)))
    nlinarith
  have hE : 3 ≤ Real.exp (S ^ (1 / 4 : ℝ) / 2) := by
    have := Real.add_one_le_exp (S ^ (1 / 4 : ℝ) / 2)
    linarith
  have hu' : Real.exp u ≤ 1 := by
    simpa using Real.exp_le_exp.mpr hu
  have hC : C * Real.log S ≤ Real.exp (S ^ (1 / 4 : ℝ) / 2) :=
    hlog'.trans (by linarith [Real.add_one_le_exp (S ^ (1 / 4 : ℝ) / 2)])
  have hExp : Real.exp (A * S ^ (1 / 16 : ℝ) * Real.log (Real.log S) + B * Real.log S) ≤
      Real.exp (S ^ (1 / 4 : ℝ) / 2) := Real.exp_le_exp.mpr hexponent
  have hSquare : Real.exp (S ^ (1 / 4 : ℝ)) =
      Real.exp (S ^ (1 / 4 : ℝ) / 2) * Real.exp (S ^ (1 / 4 : ℝ) / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hSquare]
  nlinarith

theorem large_contribution_exponent_bound (D r C S v Z : ℝ)
    (hD : 1 ≤ D) (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hS : 1 ≤ S) (hlogS : 1 ≤ Real.log S) (hloglogS : 1 ≤ Real.log (Real.log S))
    (hvlo : S / (2 * Real.log S) ≤ v) (hvhi : v ≤ D * S)
    (hZ : 2 ≤ Z) (hZhi : Real.log Z ≤ D * S) :
    Real.log 2 + r * (1 + Real.log ((D + 1) * S / v)) * v ^ (1 / 16 : ℝ) +
        C * Real.log (1 + Real.log Z) ≤
      largeCoefficient D r * S ^ (1 / 16 : ℝ) * Real.log (Real.log S) +
        harmonicCoefficient D C * Real.log S := by
  have hS0 : 0 < S := by linarith
  have hD0 : 0 < D := by linarith
  have hE0 : 0 < D + 1 := by linarith
  have hlS0 : 0 < Real.log S := by linarith
  have hv0 : 0 < v := lt_of_lt_of_le (by positivity) hvlo
  have hsize : S ≤ v * (2 * Real.log S) := (div_le_iff₀ (by positivity)).1 hvlo
  have hratio : (D + 1) * S / v ≤ 2 * (D + 1) * Real.log S := by
    apply (div_le_iff₀ hv0).2
    have := mul_le_mul_of_nonneg_left hsize hE0.le
    nlinarith
  have hB : 1 + Real.log ((D + 1) * S / v) ≤
      (2 + Real.log (2 * (D + 1))) * Real.log (Real.log S) := by
    have h := Real.log_le_log (show 0 < (D + 1) * S / v by positivity) hratio
    rw [Real.log_mul (by positivity : 2 * (D + 1) ≠ 0) hlS0.ne'] at h
    have hconst : 0 ≤ 1 + Real.log (2 * (D + 1)) := by
      have := Real.log_nonneg (show 1 ≤ 2 * (D + 1) by linarith)
      linarith
    have hm := mul_le_mul_of_nonneg_left hloglogS hconst
    nlinarith
  have hpow : v ^ (1 / 16 : ℝ) ≤ D ^ (1 / 16 : ℝ) * S ^ (1 / 16 : ℝ) := by
    have h := Real.rpow_le_rpow hv0.le hvhi (show (0 : ℝ) ≤ 1 / 16 by norm_num)
    simpa only [Real.mul_rpow hD0.le hS0.le] using h
  have hcoef : 0 ≤ (2 + Real.log (2 * (D + 1))) * Real.log (Real.log S) := by
    have := Real.log_nonneg (show 1 ≤ 2 * (D + 1) by linarith)
    positivity
  have hlarge : r * (1 + Real.log ((D + 1) * S / v)) * v ^ (1 / 16 : ℝ) ≤
      largeCoefficient D r * S ^ (1 / 16 : ℝ) * Real.log (Real.log S) := by
    calc
      _ ≤ r * ((2 + Real.log (2 * (D + 1))) * Real.log (Real.log S)) *
          v ^ (1 / 16 : ℝ) := by
        gcongr
      _ ≤ r * ((2 + Real.log (2 * (D + 1))) * Real.log (Real.log S)) *
          (D ^ (1 / 16 : ℝ) * S ^ (1 / 16 : ℝ)) :=
        mul_le_mul_of_nonneg_left hpow (mul_nonneg hr hcoef)
      _ = _ := by unfold largeCoefficient; ring
  have hZ0 : 0 < 1 + Real.log Z := by
    have := Real.log_nonneg (show 1 ≤ Z by linarith)
    linarith
  have harg : 1 + Real.log Z ≤ (D + 1) * S := by nlinarith
  have hlogE : 0 ≤ Real.log (D + 1) := Real.log_nonneg (by linarith)
  have hharm : Real.log (1 + Real.log Z) ≤ (1 + Real.log (D + 1)) * Real.log S := by
    have h := Real.log_le_log hZ0 harg
    rw [Real.log_mul hE0.ne' hS0.ne'] at h
    have hm := mul_le_mul_of_nonneg_left hlogS hlogE
    nlinarith
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have htwo := mul_le_mul_of_nonneg_left hlogS hlog2
  have hch := mul_le_mul_of_nonneg_left hharm hC
  unfold harmonicCoefficient
  nlinarith

theorem largeCoefficient_nonneg {D r : ℝ} (hD : 1 ≤ D) (hr : 0 ≤ r) :
    0 ≤ largeCoefficient D r := by
  have := Real.log_nonneg (show 1 ≤ 2 * (D + 1) by linarith)
  unfold largeCoefficient
  positivity

/-- Uniform conversion of the entire large-class budget, including its factor
of two and harmonic loss. -/
theorem eventually_large_contribution_bound (D r C : ℝ)
    (hD : 1 ≤ D) (hr : 0 ≤ r) (hC : 0 ≤ C) :
    ∀ᶠ S : ℝ in atTop, ∀ v Z : ℝ,
      S / (2 * Real.log S) ≤ v → v ≤ D * S → 2 ≤ Z → Real.log Z ≤ D * S →
      2 * Real.exp (r * (1 + Real.log ((D + 1) * S / v)) * v ^ (1 / 16 : ℝ) +
          C * Real.log (1 + Real.log Z)) ≤
        Real.exp (largeCoefficient D r * S ^ (1 / 16 : ℝ) * Real.log (Real.log S) +
          harmonicCoefficient D C * Real.log S) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 1,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1]
    with S hS hlogS hloglogS
  intro v Z hvlo hvhi hZ hZhi
  have h := large_contribution_exponent_bound D r C S v Z hD hr hC
    hS hlogS hloglogS hvlo hvhi hZ hZhi
  calc
    _ = Real.exp (Real.log 2 +
        (r * (1 + Real.log ((D + 1) * S / v)) * v ^ (1 / 16 : ℝ) +
          C * Real.log (1 + Real.log Z))) := by
      rw [Real.exp_add (Real.log 2), Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end Problem337.DivisorMomentAbsorption

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_DivisorMomentFinalBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open Filter

namespace Problem337.DivisorMomentFinalBudget

/-- The square-root cutoff in the harmonic-prefix estimate satisfies the
uniform large-class parameter window. -/
theorem eventually_sqrt_cutoff_window (D : ℝ) :
    ∀ᶠ S : ℝ in atTop, ∀ v Y : ℝ,
      S / (2 * Real.log S) ≤ v → v ≤ D * S →
      Real.exp (v / 2) ≤ Y → Y ≤ Real.exp v →
      0 ≤ v ∧ 2 ≤ Real.sqrt Y ∧ Real.log (Real.sqrt Y) ≤ D * S := by
  have hlog := Real.isLittleO_log_id_atTop.bound
    (show (0 : ℝ) < 1 / 12 by norm_num)
  filter_upwards [hlog, eventually_ge_atTop (2 : ℝ)] with S hlog hS
  intro v Y hvlow hvup hYlow hYup
  have hSpos : 0 < S := by linarith
  have hlogpos : 0 < Real.log S := Real.log_pos (by linarith)
  have hlogbound : Real.log S ≤ S / 12 := by
    simpa only [Real.norm_eq_abs, id_eq, abs_of_pos hSpos,
      abs_of_pos hlogpos, one_div_mul_eq_div] using hlog
  have hv6 : 6 ≤ v := by
    apply le_trans _ hvlow
    apply (le_div_iff₀ (by positivity : 0 < 2 * Real.log S)).mpr
    linarith
  have hY4 : 4 ≤ Y := by
    have := Real.add_one_le_exp (v / 2)
    linarith
  have hYpos : 0 < Y := by linarith
  have hlogY : Real.log Y ≤ v := (Real.log_le_iff_le_exp hYpos).mpr hYup
  refine ⟨by linarith, ?_, ?_⟩
  · apply Real.le_sqrt_of_sq_le
    norm_num
    exact hY4
  · rw [Real.log_sqrt hYpos.le]
    linarith

/-- Final loss absorption with the large-class majorant supplied explicitly.
This helper isolates the harmless square-root cutoff and finite-band count
from the number-theoretic class estimates. -/
theorem final_budget_of_large_majorant
    (D r C A B : ℝ) (hA : 0 ≤ A)
    (hlarge : ∀ᶠ S : ℝ in atTop, ∀ v Z : ℝ,
      S / (2 * Real.log S) ≤ v → v ≤ D * S → 2 ≤ Z →
      Real.log Z ≤ D * S →
      2 * Real.exp (r * (1 + Real.log ((D + 1) * S / v)) *
        v ^ (1 / 16 : ℝ) + C * Real.log (1 + Real.log Z)) ≤
      Real.exp (A * S ^ (1 / 16 : ℝ) * Real.log (Real.log S) +
        B * Real.log S)) :
    ∀ᶠ S : ℝ in atTop, ∀ v Y : ℝ,
      S / (2 * Real.log S) ≤ v → v ≤ D * S →
      Real.exp (v / 2) ≤ Y → Y ≤ Real.exp v →
      2 * Real.exp (r * (1 + Real.log ((D + 1) * S / v)) *
        v ^ (1 / 16 : ℝ) + C * Real.log (1 + Real.log (Real.sqrt Y))) +
        2 * Real.exp (-v / 100) + (6 / Real.log 2) * Real.log S ≤
      Real.exp (S ^ (1 / 4 : ℝ)) := by
  filter_upwards [hlarge, eventually_sqrt_cutoff_window D,
    DivisorMomentAbsorption.eventually_absorb_large_contribution A B
      (6 / Real.log 2) hA] with S hlarge hwindow habsorb
  intro v Y hvlow hvup hYlow hYup
  obtain ⟨hv0, hZlow, hZup⟩ := hwindow v Y hvlow hvup hYlow hYup
  have hmajor := hlarge v (Real.sqrt Y) hvlow hvup hZlow hZup
  have hfinal := habsorb (-v / 100) (by linarith)
  linarith

/-- Exact final numerical budget for the large, small, and dyadic intermediate
classes. All growth estimates are unconditional and uniform in both windows. -/
theorem eventually_divisor_moment_final_budget
    (D r C : ℝ) (hD : 1 ≤ D) (hr : 0 ≤ r) (hC : 0 ≤ C) :
    ∀ᶠ S : ℝ in atTop, ∀ v Y : ℝ,
      S / (2 * Real.log S) ≤ v → v ≤ D * S →
      Real.exp (v / 2) ≤ Y → Y ≤ Real.exp v →
      2 * Real.exp (r * (1 + Real.log ((D + 1) * S / v)) *
        v ^ (1 / 16 : ℝ) + C * Real.log (1 + Real.log (Real.sqrt Y))) +
        2 * Real.exp (-v / 100) + (6 / Real.log 2) * Real.log S ≤
      Real.exp (S ^ (1 / 4 : ℝ)) := by
  exact final_budget_of_large_majorant D r C
    (DivisorMomentAbsorption.largeCoefficient D r)
    (DivisorMomentAbsorption.harmonicCoefficient D C)
    (DivisorMomentAbsorption.largeCoefficient_nonneg hD hr)
    (DivisorMomentAbsorption.eventually_large_contribution_bound D r C hD hr hC)

/-- The weighted form directly bounds the sum of the three class contributions. -/
theorem eventually_divisor_moment_weighted_budget
    (D r C : ℝ) (hD : 1 ≤ D) (hr : 0 ≤ r) (hC : 0 ≤ C) :
    ∀ᶠ S : ℝ in atTop, ∀ v Y : ℝ,
      S / (2 * Real.log S) ≤ v → v ≤ D * S →
      Real.exp (v / 2) ≤ Y → Y ≤ Real.exp v →
      2 * Y * Real.exp (r * (1 + Real.log ((D + 1) * S / v)) *
        v ^ (1 / 16 : ℝ) + C * Real.log (1 + Real.log (Real.sqrt Y))) +
        2 * Y * Real.exp (-v / 100) +
        Y * ((6 / Real.log 2) * Real.log S) ≤
      Y * Real.exp (S ^ (1 / 4 : ℝ)) := by
  filter_upwards [eventually_divisor_moment_final_budget D r C hD hr hC]
    with S hS
  intro v Y hvlow hvup hYlow hYup
  have h := mul_le_mul_of_nonneg_left (hS v Y hvlow hvup hYlow hYup)
    ((Real.exp_pos (v / 2)).le.trans hYlow)
  nlinarith

end Problem337.DivisorMomentFinalBudget

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_DivisorClassAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
open Filter

namespace Problem337.DivisorClasses

attribute [local instance] Classical.propDecidable

/-- Once the three arithmetic class estimates are supplied, the exact uniform
moment budget follows. The prime-prefix cover and every numerical loss are
discharged here, including the case of an empty intermediate range. -/
theorem eventually_class_budget_assembly (D r C : ℝ)
    (hD : 1 ≤ D) (hr : 0 ≤ r) (hC : 0 ≤ C) :
    ∀ᶠ S : ℝ in atTop, ∀ v Y : ℝ,
      S / (2 * Real.log S) ≤ v → v ≤ D * S →
      Real.exp (v / 2) ≤ Y → Y ≤ Real.exp v →
      ∀ (H : Finset ℕ) (n : ℕ → ℕ) (w : ℕ → ℝ),
      (∀ i ∈ H, 0 ≤ w i) →
      (∑ i ∈ H with LargeClass (n i) v Y, w i) ≤
        2 * Y * Real.exp (r * (1 + Real.log ((D + 1) * S / v)) *
          v ^ (1 / 16 : ℝ) + C * Real.log (1 + Real.log (Real.sqrt Y))) →
      (∑ i ∈ H with SmallClass (n i) S v Y, w i) ≤
        2 * Y * Real.exp (-v / 100) →
      (∀ j : ℕ, (∑ i ∈ H with BandClass (n i) S v Y j, w i) ≤ 2 * Y) →
      (∑ i ∈ H, w i) ≤ Y * Real.exp (S ^ (1 / 4 : ℝ)) := by
  filter_upwards [DyadicBands.eventually_divisor_band_cover D,
    DivisorMomentFinalBudget.eventually_divisor_moment_weighted_budget D r C hD hr hC,
    DivisorMomentFinalBudget.eventually_sqrt_cutoff_window D,
    eventually_ge_atTop (2 : ℝ)] with S hcover hbudget hwindow hS
  intro v Y hvlo hvhi hYlo hYhi H n w hw hlarge hsmall hband
  have hY0 : 0 ≤ Y := (Real.exp_pos (v / 2)).le.trans hYlo
  have hlogS : 0 ≤ Real.log S := Real.log_nonneg (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hexists : ∃ J : ℕ, (J : ℝ) ≤ (3 / Real.log 2) * Real.log S ∧
      ∀ x : ℝ, 4 * Real.log S ≤ x → x < v ^ (15 / 16 : ℝ) →
        ∃ j : ℕ, j < J ∧ DyadicBands.InBand (4 * Real.log S) j x := by
    by_cases hrange : 4 * Real.log S ≤ v ^ (15 / 16 : ℝ)
    · exact hcover v hvlo hvhi hrange
    · refine ⟨0, ?_, ?_⟩
      · simp only [Nat.cast_zero]
        positivity
      · intro x hx hxv
        exact (hrange (hx.trans hxv.le)).elim
  obtain ⟨J, hJ, hbands⟩ := hexists
  have hsqrt : 1 ≤ Real.sqrt Y := by
    have := (hwindow v Y hvlo hvhi hYlo hYhi).2.1
    linarith
  have hsum := sum_le_class_bounds H n w S v Y J
    (2 * Y * Real.exp (r * (1 + Real.log ((D + 1) * S / v)) *
      v ^ (1 / 16 : ℝ) + C * Real.log (1 + Real.log (Real.sqrt Y))))
    (2 * Y * Real.exp (-v / 100)) (2 * Y) hsqrt hbands hw hlarge hsmall
    (fun j _ => hband j)
  have hJY : (J : ℝ) * (2 * Y) ≤ Y * ((6 / Real.log 2) * Real.log S) := by
    calc
      _ ≤ (3 / Real.log 2) * Real.log S * (2 * Y) :=
        mul_le_mul_of_nonneg_right hJ (show 0 ≤ 2 * Y by positivity)
      _ = _ := by ring
  have hfinal := hbudget v Y hvlo hvhi hYlo hYhi
  linarith

end Problem337.DivisorClasses

end

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

end Problem337

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

/-- Uniform prefix-size conclusion over all admissible divisor-moment scales. -/
theorem eventually_uniform_prefix_large :
    ∀ᶠ S : ℝ in atTop, ∀ v d p Y : ℝ,
      S / (2 * Real.log S) ≤ v →
      0 < d → 0 < p → 0 < Y → v / 2 ≤ Real.log Y →
      Real.sqrt Y < d * p → Real.log p < v ^ (15 / 16 : ℝ) →
      Real.exp (v / 5) < d := by
  obtain ⟨V, hV⟩ := eventually_atTop.mp eventually_fifteen_sixteenths_small
  filter_upwards [eventually_uniform_lower_scale V] with S hS
  intro v d p Y hv hd hp hY hYlog hcross hplog
  exact exp_prefix_lower hd hp hY hYlog hcross hplog (hV v (hS v hv))

end Problem337.PrimePrefixSize

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_FiniteEulerBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.DivisorMoment

/-- A nonnegative multiplicative function is bounded by its finite Euler product. -/
theorem sum_Icc_le_factorial_euler (f : ArithmeticFunction ℝ)
    (hf : f.IsMultiplicative) (hpos : ∀ n, 0 ≤ f n) (T : ℕ) :
    (∑ n ∈ Finset.Icc 1 T, f n) ≤
      ∏ p ∈ T.factorial.primeFactors,
        ∑ j ∈ Finset.range (T.factorial.factorization p + 1), f (p ^ j) := by
  have hsub : Finset.Icc 1 T ⊆ T.factorial.divisors := by
    intro n hn
    obtain ⟨hnpos, hnT⟩ := Finset.mem_Icc.mp hn
    exact Nat.mem_divisors.mpr
      ⟨Nat.dvd_factorial hnpos hnT, Nat.factorial_ne_zero T⟩
  calc
    (∑ n ∈ Finset.Icc 1 T, f n) ≤ ∑ n ∈ T.factorial.divisors, f n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hpos n)
    _ = (f * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) T.factorial :=
      ArithmeticFunction.coe_mul_zeta_apply.symm
    _ = ∏ p ∈ T.factorial.primeFactors,
        (f * (ArithmeticFunction.zeta : ArithmeticFunction ℝ))
          (p ^ T.factorial.factorization p) := by
      rw [(hf.mul ArithmeticFunction.isMultiplicative_zeta.natCast).multiplicative_factorization
        _ (Nat.factorial_ne_zero T)]
      rfl
    _ = _ := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [ArithmeticFunction.coe_mul_zeta_apply,
        Nat.sum_divisors_prime_pow (Nat.prime_of_mem_primeFactors hp)]

/-- An exponential local bound turns the finite Euler product into a prime sum. -/
theorem sum_Icc_le_exp_prime_sum (f : ArithmeticFunction ℝ)
    (hf : f.IsMultiplicative) (hpos : ∀ n, 0 ≤ f n)
    (T : ℕ) (C : ℝ) (w : ℕ → ℝ)
    (hlocal : ∀ p, p.Prime → p ≤ T → ∀ L : ℕ,
      (∑ j ∈ Finset.range (L + 1), f (p ^ j)) ≤ Real.exp (C * w p)) :
    (∑ n ∈ Finset.Icc 1 T, f n) ≤
      Real.exp (C * ∑ p ∈ T.factorial.primeFactors, w p) := by
  apply (sum_Icc_le_factorial_euler f hf hpos T).trans
  rw [Finset.mul_sum, Real.exp_sum]
  apply Finset.prod_le_prod
  · intro p hp
    exact Finset.sum_nonneg (fun j _ => hpos (p ^ j))
  · intro p hp
    obtain ⟨hpprime, hpdvd, _⟩ := Nat.mem_primeFactors.mp hp
    exact hlocal p hpprime (hpprime.dvd_factorial.mp hpdvd) _

theorem divisorMomentWeight_nonneg (r : ℕ) (σ : ℝ) (n : ℕ) :
    0 ≤ divisorMomentWeight r σ n := by
  unfold divisorMomentWeight
  simp only [ArithmeticFunction.coe_mk]
  split_ifs
  · rfl
  · positivity

theorem divisorMomentWeight_multiplicative (r : ℕ) (σ : ℝ) :
    (divisorMomentWeight r σ).IsMultiplicative := by
  apply ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr
  constructor
  · simp [divisorMomentWeight]
  · intro m n hm hn hcop
    simp only [divisorMomentWeight, ArithmeticFunction.coe_mk, ite_eq_right hm, ite_eq_right hn,
      ite_eq_right (Nat.mul_ne_zero hm hn), hcop.card_divisors_mul, Nat.cast_mul, mul_pow,
      Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
    ring

theorem divisorMomentWeight_prime_pow (r : ℕ) (σ : ℝ) {p : ℕ}
    (hp : p.Prime) (j : ℕ) :
    divisorMomentWeight r σ (p ^ j) = (j + 1 : ℝ) ^ r * ((p : ℝ) ^ (-σ)) ^ j := by
  have hcard : (p ^ j).divisors.card = j + 1 := by
    rw [← ArithmeticFunction.sigma_zero_apply,
      ArithmeticFunction.sigma_zero_apply_prime_pow hp]
  simp only [divisorMomentWeight, ArithmeticFunction.coe_mk,
    ite_eq_right (pow_ne_zero j hp.ne_zero), hcard, Nat.cast_add, Nat.cast_one, Nat.cast_pow]
  rw [← Real.rpow_natCast_mul (Nat.cast_nonneg p), mul_comm (j : ℝ) (-σ),
    Real.rpow_mul_natCast (Nat.cast_nonneg p)]

theorem local_divisor_sum_pos (r L : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    0 < ∑ j ∈ Finset.range (L + 1), (j + 1 : ℝ) ^ r * x ^ j := by
  have h := Finset.single_le_sum
    (s := Finset.range (L + 1)) (f := fun j : ℕ => (j + 1 : ℝ) ^ r * x ^ j)
    (fun j _ => by positivity) (show 0 ∈ Finset.range (L + 1) by simp)
  simp only [Nat.cast_zero, zero_add, one_pow, pow_zero, mul_one] at h
  linarith

/-- A uniform logarithmic local-factor bound controls the harmonic divisor sum. -/
theorem divisor_moment_sum_le_exp (r T : ℕ) (σ C : ℝ)
    (hlocal : ∀ p, p.Prime → p ≤ T → ∀ L : ℕ,
      Real.log (∑ j ∈ Finset.range (L + 1),
        (j + 1 : ℝ) ^ r * ((p : ℝ) ^ (-σ)) ^ j) ≤ C * (p : ℝ) ^ (-σ)) :
    (∑ n ∈ Finset.Icc 1 T, (n.divisors.card : ℝ) ^ r * (n : ℝ) ^ (-σ)) ≤
      Real.exp (C * ∑ p ∈ T.factorial.primeFactors, (p : ℝ) ^ (-σ)) := by
  have h := sum_Icc_le_exp_prime_sum (divisorMomentWeight r σ)
    (divisorMomentWeight_multiplicative r σ) (divisorMomentWeight_nonneg r σ)
    T C (fun p => (p : ℝ) ^ (-σ)) (by
      intro p hp hpT L
      simp_rw [divisorMomentWeight_prime_pow r σ hp]
      have hpos := local_divisor_sum_pos r L ((p : ℝ) ^ (-σ)) (by positivity)
      calc
        _ = Real.exp (Real.log _) := (Real.exp_log hpos).symm
        _ ≤ _ := Real.exp_le_exp.mpr (hlocal p hp hpT L))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
  simp [divisorMomentWeight, hn0]

end Problem337.DivisorMoment

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_PrimeReciprocalBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped BigOperators

namespace Problem337

/-- A dyadic prime block contributes at most a constant divided by its
logarithmic index. This uses only the elementary Chebyshev upper bound. -/
theorem prime_reciprocal_dyadic_block (n : ℕ) (hn : 1 ≤ n) :
    ∑ p ∈ Nat.primesLE (2 ^ (n + 1)) \ Nat.primesLE (2 ^ n),
      (1 : ℝ) / p ≤ 4 / (n : ℝ) := by
  let s := Nat.primesLE (2 ^ (n + 1)) \ Nat.primesLE (2 ^ n)
  let A : ℝ := (2 : ℝ) ^ n * ((n : ℝ) * Real.log 2)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hA : 0 < A := by dsimp [A]; positivity
  have hpdata : ∀ p ∈ s, p.Prime ∧ 2 ^ n < p := by
    intro p hp
    obtain ⟨hp, hnot⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hpbound, hpprime⟩ := Nat.mem_primesLE.mp hp
    refine ⟨hpprime, ?_⟩
    by_contra h
    exact hnot (Nat.mem_primesLE.mpr ⟨by omega, hpprime⟩)
  have hterms : ∀ p ∈ s, (1 : ℝ) / p ≤ Real.log p / A := by
    intro p hp
    have hpdata' := hpdata p hp
    have hp : (0 : ℝ) < p := by exact_mod_cast hpdata'.1.pos
    have hple : (2 : ℝ) ^ n ≤ p := by exact_mod_cast hpdata'.2.le
    have hlogp : (n : ℝ) * Real.log 2 ≤ Real.log p := by
      calc
        (n : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ n) := (Real.log_pow _ _).symm
        _ ≤ Real.log p := Real.log_le_log (by positivity) hple
    apply (div_le_div_iff₀ hp hA).mpr
    simp only [one_mul]
    dsimp [A]
    nlinarith [mul_le_mul hple hlogp (by positivity : 0 ≤ (n : ℝ) * Real.log 2)
      hp.le]
  have hlogs : ∑ p ∈ s, Real.log (p : ℝ) ≤
      Chebyshev.theta (2 ^ (n + 1) : ℕ) := by
    rw [Chebyshev.theta_eq_sum_primesLE_log]
    apply Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
    intro p hp _
    exact Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt.le)
  have htheta := Chebyshev.theta_le_log4_mul_x
    (show (0 : ℝ) ≤ (2 ^ (n + 1) : ℕ) by positivity)
  have hfour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    calc
      Real.log (4 : ℝ) = Real.log ((2 : ℝ) ^ 2) := by norm_num
      _ = 2 * Real.log 2 := Real.log_pow _ _
  change (∑ p ∈ s, (1 : ℝ) / p) ≤ _
  calc
    ∑ p ∈ s, (1 : ℝ) / p ≤ ∑ p ∈ s, Real.log (p : ℝ) / A :=
      Finset.sum_le_sum hterms
    _ = (∑ p ∈ s, Real.log (p : ℝ)) / A := (Finset.sum_div _ _ _).symm
    _ ≤ Chebyshev.theta (2 ^ (n + 1) : ℕ) / A :=
      div_le_div_of_nonneg_right hlogs hA.le
    _ ≤ (Real.log 4 * (2 ^ (n + 1) : ℕ)) / A :=
      div_le_div_of_nonneg_right htheta hA.le
    _ = 4 / (n : ℝ) := by
      push_cast
      simp only [pow_succ, hfour, A]
      field_simp
      ring

/-- Summing dyadic blocks gives a harmonic majorant for prime reciprocals. -/
theorem prime_reciprocal_two_pow (n : ℕ) :
    ∑ p ∈ Nat.primesLE (2 ^ n), (1 : ℝ) / p ≤ 8 * (harmonic n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    by_cases hn : n = 0
    · subst n
      norm_num [Nat.primesLE_eq_filter_Icc_two, harmonic, Finset.filter_singleton, Nat.prime_two]
    have hn1 : 1 ≤ n := by omega
    have hblock := prime_reciprocal_dyadic_block n hn1
    have hsubset : Nat.primesLE (2 ^ n) ⊆ Nat.primesLE (2 ^ (n + 1)) :=
      Nat.primesLE_mono (Nat.pow_le_pow_right (by omega) (by omega))
    have hsplit := Finset.sum_sdiff (f := fun p : ℕ => (1 : ℝ) / p) hsubset
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hfrac : (4 : ℝ) / n ≤ 8 / (n + 1 : ℕ) := by
      apply (div_le_div_iff₀ hnpos (by positivity)).mpr
      norm_cast
      omega
    have hhar : (harmonic (n + 1) : ℝ) = harmonic n + 1 / (n + 1 : ℕ) := by
      simp [harmonic_succ, one_div]
    rw [hhar]
    simp only [div_eq_mul_inv] at hblock hfrac hsplit ih ⊢
    linarith

/-- A direct logarithmic majorant, with the binary logarithm only in the
argument of the outside logarithm. -/
theorem prime_reciprocal_log_bound (T : ℕ) :
    ∑ p ∈ Nat.primesLE T, (1 : ℝ) / p ≤
      8 * (1 + Real.log ((Nat.log 2 T + 1 : ℕ) : ℝ)) := by
  have hT : T ≤ 2 ^ (Nat.log 2 T + 1) :=
    (Nat.lt_pow_succ_log_self (by omega : 1 < 2) T).le
  calc
    ∑ p ∈ Nat.primesLE T, (1 : ℝ) / p ≤
        ∑ p ∈ Nat.primesLE (2 ^ (Nat.log 2 T + 1)), (1 : ℝ) / p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Nat.primesLE_mono hT)
      intro p _ _
      positivity
    _ ≤ 8 * (harmonic (Nat.log 2 T + 1) : ℝ) := prime_reciprocal_two_pow _
    _ ≤ 8 * (1 + Real.log ((Nat.log 2 T + 1 : ℕ) : ℝ)) := by
      gcongr
      exact harmonic_le_one_add_log _

/-- An elementary uniform `O(log log T)` bound for reciprocal primes. -/
theorem sum_prime_reciprocals_le_loglog (T : ℕ) (hT : 2 ≤ T) :
    ∑ p ∈ Nat.primesLE T, (1 : ℝ) / p ≤
      56 * Real.log (1 + Real.log (T : ℝ)) := by
  have hTpos : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hTzero : T ≠ 0 := by omega
  have hlogtwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    linarith
  have hlogtwo' : Real.log 2 ≤ (1 : ℝ) := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this
    exact this
  have hlogT : (1 / 2 : ℝ) ≤ Real.log (T : ℝ) :=
    hlogtwo.trans (Real.log_le_log (by norm_num) (by exact_mod_cast hT))
  have hnlog : (Nat.log 2 T : ℝ) * Real.log 2 ≤ Real.log (T : ℝ) := by
    calc
      _ = Real.log ((2 : ℝ) ^ Nat.log 2 T) := (Real.log_pow _ _).symm
      _ ≤ Real.log (T : ℝ) := Real.log_le_log (by positivity)
        (by exact_mod_cast Nat.pow_log_le_self 2 hTzero)
  have hnnonneg : (0 : ℝ) ≤ Nat.log 2 T := by positivity
  have hindex : ((Nat.log 2 T + 1 : ℕ) : ℝ) ≤ 2 * (1 + Real.log (T : ℝ)) := by
    push_cast
    nlinarith
  have hy : (1 / 3 : ℝ) ≤ Real.log (1 + Real.log (T : ℝ)) := by
    have hthree : (1 / 3 : ℝ) ≤ Real.log (3 / 2 : ℝ) := by
      have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
      norm_num at this ⊢
      exact this
    exact hthree.trans (Real.log_le_log (by norm_num) (by linarith))
  have hindexlog : Real.log ((Nat.log 2 T + 1 : ℕ) : ℝ) ≤
      1 + Real.log (1 + Real.log (T : ℝ)) := by
    calc
      _ ≤ Real.log (2 * (1 + Real.log (T : ℝ))) :=
        Real.log_le_log (by positivity) hindex
      _ = Real.log 2 + Real.log (1 + Real.log (T : ℝ)) :=
        Real.log_mul (by norm_num) (by linarith)
      _ ≤ 1 + Real.log (1 + Real.log (T : ℝ)) := by linarith
  have hh := prime_reciprocal_log_bound T
  linarith

end Problem337

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_HarmonicMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.DivisorMoment

/-- Finite Euler products combine uniform local control with a prime reciprocal bound. -/
theorem harmonic_divisor_moment_of_local_and_primes (r : ℕ) (C B : ℝ)
    (hC : 0 < C) (hB : 0 < B)
    (hlocal : ∀ p : ℕ, p.Prime → ∀ L : ℕ,
      Real.log (∑ j ∈ Finset.range (L + 1),
        (j + 1 : ℝ) ^ r * ((p : ℝ)⁻¹) ^ j) ≤ C / p)
    (hprimes : ∀ T : ℕ, 2 ≤ T →
      (∑ p ∈ T.factorial.primeFactors, (1 : ℝ) / p) ≤
        B * Real.log (1 + Real.log (T : ℝ))) :
    ∃ A : ℝ, 0 < A ∧ ∀ T : ℕ, 2 ≤ T →
      (∑ n ∈ Finset.Icc 1 T, (n.divisors.card : ℝ) ^ r / n) ≤
        Real.exp (A * Real.log (1 + Real.log (T : ℝ))) := by
  refine ⟨C * B, mul_pos hC hB, ?_⟩
  intro T hT
  have heuler := divisor_moment_sum_le_exp r T 1 C (by
    intro p hp hpT L
    simpa only [Real.rpow_neg_one, div_eq_mul_inv] using hlocal p hp L)
  have hprime := mul_le_mul_of_nonneg_left (hprimes T hT) hC.le
  have hfinal := heuler.trans (Real.exp_le_exp.mpr (by
    simpa only [Real.rpow_neg_one, one_div] using hprime))
  simpa only [Real.rpow_neg_one, div_eq_mul_inv, mul_assoc] using hfinal

/-- The prime factors of a factorial are exactly the primes up to its index. -/
theorem factorial_primeFactors_eq_primesLE (T : ℕ) :
    T.factorial.primeFactors = Nat.primesLE T := by
  ext p
  constructor
  · intro hp
    obtain ⟨hpprime, hpdvd, _⟩ := Nat.mem_primeFactors.mp hp
    exact Nat.mem_primesLE.mpr ⟨hpprime.dvd_factorial.mp hpdvd, hpprime⟩
  · intro hp
    obtain ⟨hpT, hpprime⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primeFactors.mpr
      ⟨hpprime, hpprime.dvd_factorial.mpr hpT, Nat.factorial_ne_zero T⟩

/-- An unconditional harmonic divisor-moment bound, with a constant depending only on r. -/
theorem harmonic_divisor_moment_bound (r : ℕ) :
    ∃ A : ℝ, 0 < A ∧ ∀ T : ℕ, 2 ≤ T →
      (∑ n ∈ Finset.Icc 1 T, (n.divisors.card : ℝ) ^ r / n) ≤
        Real.exp (A * Real.log (1 + Real.log (T : ℝ))) := by
  obtain ⟨C, hC, hfactor⟩ := divisor_full_local_factor_bound (r : ℝ)
  apply harmonic_divisor_moment_of_local_and_primes r C 56 hC (by norm_num)
  · intro p hp L
    have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have h := (hfactor (p : ℝ) 1 hpR (by norm_num)).2.2 L
    simpa only [Real.rpow_natCast, Real.rpow_neg_one, div_eq_mul_inv] using h
  · intro T hT
    rw [factorial_primeFactors_eq_primesLE]
    exact Problem337.sum_prime_reciprocals_le_loglog T hT

/-- Arbitrary real moments follow by increasing the moment to a natural number. -/
theorem harmonic_divisor_real_moment_bound (r : ℝ) :
    ∃ A : ℝ, 0 < A ∧ ∀ T : ℕ, 2 ≤ T →
      (∑ n ∈ Finset.Icc 1 T, (n.divisors.card : ℝ) ^ r / n) ≤
        Real.exp (A * Real.log (1 + Real.log (T : ℝ))) := by
  obtain ⟨A, hA, hbound⟩ := harmonic_divisor_moment_bound ⌈r⌉₊
  refine ⟨A, hA, ?_⟩
  intro T hT
  apply le_trans _ (hbound T hT)
  apply Finset.sum_le_sum
  intro n hn
  have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
  have hcard : 1 ≤ n.divisors.card :=
    Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (Nat.ne_of_gt hnpos)⟩
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hcard) (Nat.le_ceil r)

/-- Real cutoffs are allowed, as in the uniform divisor-moment estimate. -/
theorem harmonic_divisor_moment_real_cutoff (r : ℝ) :
    ∃ A : ℝ, 0 < A ∧ ∀ X : ℝ, 2 ≤ X →
      (∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (n.divisors.card : ℝ) ^ r / n) ≤
        Real.exp (A * Real.log (1 + Real.log X)) := by
  obtain ⟨A, hA, hbound⟩ := harmonic_divisor_real_moment_bound r
  refine ⟨A, hA, ?_⟩
  intro X hX
  have hfloor : 2 ≤ ⌊X⌋₊ := Nat.le_floor hX
  apply (hbound ⌊X⌋₊ hfloor).trans
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ hA.le
  have hfloorR : (2 : ℝ) ≤ ⌊X⌋₊ := by exact_mod_cast hfloor
  have hlognonneg : 0 ≤ Real.log (⌊X⌋₊ : ℝ) := Real.log_nonneg (by linarith)
  apply Real.log_le_log (by linarith)
  have hlogs := Real.log_le_log (by linarith : (0 : ℝ) < ⌊X⌋₊)
    (Nat.floor_le (by linarith : 0 ≤ X))
  linarith

end Problem337.DivisorMoment

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_HarmonicPrefixBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337.DivisorMoment

/-- Summing a harmonic divisor majorant over selected short-interval prefixes. -/
theorem harmonic_prefix_budget (r : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N Y : ℕ) (A : Finset ℕ) (Z H : ℝ) (w : ℕ → ℝ),
      2 ≤ Z → ⌊Z⌋₊ ≤ Y → A ⊆ Finset.Ioc N (N + Y) →
      (∀ n ∈ A, ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ Z ∧ d ∣ n ∧
        w n ≤ Real.exp H * (d.divisors.card : ℝ) ^ r) →
      (∑ n ∈ A, w n) ≤
        2 * (Y : ℝ) * Real.exp (H + C * Real.log (1 + Real.log Z)) := by
  obtain ⟨C, hC, hharm⟩ := harmonic_divisor_moment_real_cutoff r
  refine ⟨C, hC, ?_⟩
  intro N Y A Z H w hZ hZY hA hprefix
  have hbase := sum_le_divisor_majorant N Y A (Finset.Icc 1 ⌊Z⌋₊) w
    (fun d => Real.exp H * (d.divisors.card : ℝ) ^ r) hA (by
      intro n hn
      obtain ⟨d, hd0, hdZ, hdn, hdw⟩ := hprefix n hn
      exact ⟨d, Finset.mem_Icc.mpr ⟨hd0, Nat.le_floor hdZ⟩, hdn, hdw⟩)
    (by intro d hd; positivity) (by
      intro d hd
      obtain ⟨hd0, hdZ⟩ := Finset.mem_Icc.mp hd
      refine ⟨hd0, ?_⟩
      exact hdZ.trans hZY)
  calc
    (∑ n ∈ A, w n) ≤ 2 * (Y : ℝ) *
        ∑ d ∈ Finset.Icc 1 ⌊Z⌋₊, (Real.exp H * (d.divisors.card : ℝ) ^ r) / d := hbase
    _ = 2 * (Y : ℝ) * (Real.exp H *
        ∑ d ∈ Finset.Icc 1 ⌊Z⌋₊, (d.divisors.card : ℝ) ^ r / d) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ ≤ 2 * (Y : ℝ) * (Real.exp H *
        Real.exp (C * Real.log (1 + Real.log Z))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hharm Z hZ) (Real.exp_pos H).le) (by positivity)
    _ = 2 * (Y : ℝ) * Real.exp (H + C * Real.log (1 + Real.log Z)) := by
      rw [Real.exp_add]

/-- The same estimate indexed by the positive translation parameter h. -/
theorem shifted_harmonic_prefix_budget (r : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N Y : ℕ) (A : Finset ℕ) (Z H : ℝ) (w : ℕ → ℝ),
      2 ≤ Z → ⌊Z⌋₊ ≤ Y → A ⊆ Finset.Icc 1 Y →
      (∀ h ∈ A, ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ Z ∧ d ∣ N + h ∧
        w h ≤ Real.exp H * (d.divisors.card : ℝ) ^ r) →
      (∑ h ∈ A, w h) ≤
        2 * (Y : ℝ) * Real.exp (H + C * Real.log (1 + Real.log Z)) := by
  obtain ⟨C, hC, hbudget⟩ := harmonic_prefix_budget r
  refine ⟨C, hC, ?_⟩
  intro N Y A Z H w hZ hZY hA hprefix
  have h := hbudget N Y (A.image (fun h => N + h)) Z H
    (fun n => w (n - N)) hZ hZY (by
      intro n hn
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hn
      have haI := Finset.mem_Icc.mp (hA ha)
      exact Finset.mem_Ioc.mpr (by omega)) (by
      intro n hn
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hn
      simpa only [Nat.add_sub_cancel_left] using hprefix a ha)
  rw [Finset.sum_image] at h
  · simpa only [Nat.add_sub_cancel_left] using h
  · intro a ha b hb hab
    exact Nat.add_left_cancel hab

/-- The shifted prefix budget with the manuscript's real-valued interval length. -/
theorem real_shifted_harmonic_prefix_budget (r : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (Y : ℝ) (A : Finset ℕ) (Z H : ℝ) (w : ℕ → ℝ),
      2 ≤ Z → Z ≤ Y → A ⊆ Finset.Icc 1 ⌊Y⌋₊ →
      (∀ h ∈ A, ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ Z ∧ d ∣ N + h ∧
        w h ≤ Real.exp H * (d.divisors.card : ℝ) ^ r) →
      (∑ h ∈ A, w h) ≤
        2 * Y * Real.exp (H + C * Real.log (1 + Real.log Z)) := by
  obtain ⟨C, hC, hbudget⟩ := shifted_harmonic_prefix_budget r
  refine ⟨C, hC, ?_⟩
  intro N Y A Z H w hZ hZY hA hprefix
  apply (hbudget N ⌊Y⌋₊ A Z H w hZ (Nat.floor_mono hZY) hA hprefix).trans
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  exact mul_le_mul_of_nonneg_left (Nat.floor_le (by linarith : 0 ≤ Y)) (by norm_num)

end Problem337.DivisorMoment

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_LargePrefixClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- Each member of the large-prime class has a divisor-indexed moment majorant. -/
theorem large_prefix_class_majorant (X W r Z L : ℝ) {n : ℕ}
    (hn : 0 < n) (hX : 1 < X) (hXW : Real.log X ≤ W)
    (hnW : Real.log (n : ℝ) ≤ W) (hr : 0 ≤ r) (hL : 0 < L)
    (hclass : InLargePrefixClass Z L n) :
    ∃ d : ℕ, 0 < d ∧ d ∣ n ∧ (d : ℝ) ≤ Z ∧
      (truncatedDivisorCount X n : ℝ) ^ r ≤ (d.divisors.card : ℝ) ^ r *
        Real.exp (r * ((1 + Real.log (W / Real.log X)) * Real.log X / L)) := by
  have hv : 0 < Real.log X := Real.log_pos hX
  have hW : 0 < W := hv.trans_le hXW
  have hratio : 1 ≤ W / Real.log X := (le_div_iff₀ hv).2 (by simpa using hXW)
  have hB : 0 ≤ 1 + Real.log (W / Real.log X) := by
    have := Real.log_nonneg hratio
    linarith
  have hH : 0 ≤ r * ((1 + Real.log (W / Real.log X)) * Real.log X / L) := by positivity
  rcases hclass with hsmall | ⟨d, p, hd, hdZ, hp, hpL, hrough⟩
  · refine ⟨n, hn, dvd_refl n, hsmall, ?_⟩
    have hcount : truncatedDivisorCount X n ≤ n.divisors.card := by
      exact Finset.card_filter_le _ _
    have hpow : (truncatedDivisorCount X n : ℝ) ^ r ≤ (n.divisors.card : ℝ) ^ r :=
      Real.rpow_le_rpow (Nat.cast_nonneg (truncatedDivisorCount X n))
        (by exact_mod_cast hcount) hr
    apply hpow.trans
    have he : 1 ≤ Real.exp (r * ((1 + Real.log (W / Real.log X)) * Real.log X / L)) :=
      Real.one_le_exp hH
    simpa using mul_le_mul_of_nonneg_left he (Real.rpow_nonneg (Nat.cast_nonneg _) r)
  · have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hn
    refine ⟨d, hdpos, hd, hdZ, ?_⟩
    have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hbound := truncatedDivisorCount_prefix_moment_bound X (p : ℝ) W r
      hn.ne' hd hX hpR hXW hnW hr (by
        intro a ha
        exact_mod_cast hrough a (Nat.prime_of_mem_primeFactorsList ha)
          (Nat.dvd_of_mem_primeFactorsList ha))
    apply hbound.trans
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (Nat.cast_nonneg _) r)
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ hr
    exact div_le_div_of_nonneg_left (by positivity) hL hpL

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_LargePrefixHarmonic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- The actual large-prefix class has an unconditional harmonic-moment budget.
The finite set is indexed by the positive translation parameter. -/
theorem large_prefix_class_harmonic_bound (r : ℝ) (hr : 0 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X W Z L Y : ℝ) (N : ℕ) (A : Finset ℕ),
      1 < X → Real.log X ≤ W → 0 < L → 2 ≤ Z → Z ≤ Y →
      A ⊆ Finset.Icc 1 ⌊Y⌋₊ →
      (∀ h ∈ A, Real.log ((N + h : ℕ) : ℝ) ≤ W) →
      (∀ h ∈ A, InLargePrefixClass Z L (N + h)) →
      (∑ h ∈ A, (truncatedDivisorCount X (N + h) : ℝ) ^ r) ≤
        2 * Y * Real.exp (r * ((1 + Real.log (W / Real.log X)) * Real.log X / L) +
          C * Real.log (1 + Real.log Z)) := by
  obtain ⟨C, hC, hbudget⟩ := DivisorMoment.real_shifted_harmonic_prefix_budget r
  refine ⟨C, hC, ?_⟩
  intro X W Z L Y N A hX hXW hL hZ hZY hA hW hclass
  apply hbudget N Y A Z
    (r * ((1 + Real.log (W / Real.log X)) * Real.log X / L))
    (fun h => (truncatedDivisorCount X (N + h) : ℝ) ^ r) hZ hZY hA
  intro h hh
  have hn : 0 < N + h := by
    have := (Finset.mem_Icc.mp (hA hh)).1
    omega
  obtain ⟨d, hd0, hd, hdZ, hmajor⟩ :=
    large_prefix_class_majorant X W r Z L hn hX hXW (hW h hh) hr hL (hclass h hh)
  exact ⟨d, hd0, hdZ, hd, by simpa only [mul_comm] using hmajor⟩

/-- The manuscript's square-root cutoff and large-next-prime threshold,
with the harmonic divisor sum fully discharged. -/
theorem large_prefix_class_sqrt_harmonic_bound (r : ℝ) (hr : 0 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X W Y : ℝ) (N : ℕ) (A : Finset ℕ),
      1 < X → Real.log X ≤ W → 4 ≤ Y →
      A ⊆ Finset.Icc 1 ⌊Y⌋₊ →
      (∀ h ∈ A, Real.log ((N + h : ℕ) : ℝ) ≤ W) →
      (∀ h ∈ A, InLargePrefixClass (Real.sqrt Y)
        ((Real.log X) ^ (15 / 16 : ℝ)) (N + h)) →
      (∑ h ∈ A, (truncatedDivisorCount X (N + h) : ℝ) ^ r) ≤
        2 * Y * Real.exp (r * (1 + Real.log (W / Real.log X)) *
          (Real.log X) ^ (1 / 16 : ℝ) +
          C * Real.log (1 + Real.log (Real.sqrt Y))) := by
  obtain ⟨C, hC, hbudget⟩ := large_prefix_class_harmonic_bound r hr
  refine ⟨C, hC, ?_⟩
  intro X W Y N A hX hXW hY hA hW hclass
  have hv : 0 < Real.log X := Real.log_pos hX
  have hZ : 2 ≤ Real.sqrt Y :=
    (Real.le_sqrt (by norm_num) (by linarith)).2 (by nlinarith)
  have hZY : Real.sqrt Y ≤ Y := by
    apply (Real.sqrt_le_iff).2
    constructor <;> nlinarith
  have hpow : Real.log X / (Real.log X) ^ (15 / 16 : ℝ) =
      (Real.log X) ^ (1 / 16 : ℝ) := by
    calc
      _ = (Real.log X) ^ (1 : ℝ) / (Real.log X) ^ (15 / 16 : ℝ) := by
        rw [Real.rpow_one]
      _ = (Real.log X) ^ ((1 : ℝ) - 15 / 16) := (Real.rpow_sub hv _ _).symm
      _ = _ := by norm_num
  have hH : r * ((1 + Real.log (W / Real.log X)) * Real.log X /
      (Real.log X) ^ (15 / 16 : ℝ)) =
      r * (1 + Real.log (W / Real.log X)) * (Real.log X) ^ (1 / 16 : ℝ) := by
    rw [mul_div_assoc, hpow]
    ring
  simpa only [hH] using hbudget X W (Real.sqrt Y)
    ((Real.log X) ^ (15 / 16 : ℝ)) Y N A hX hXW (by positivity) hZ hZY hA hW hclass

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_LargeClassUniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
open Filter

namespace Problem337

attribute [local instance] Classical.propDecidable

/-- The canonical sorted-prefix large class satisfies the hypotheses of the
weighted large-prefix estimate. -/
theorem DivisorClasses.LargeClass.inLargePrefixClass {n : ℕ} {v Y : ℝ}
    (h : DivisorClasses.LargeClass n v Y) :
    InLargePrefixClass (Real.sqrt Y) (v ^ (15 / 16 : ℝ)) n := by
  rcases h with hsmall | ⟨d, p, hpref, hp⟩
  · exact Or.inl hsmall
  · obtain ⟨hd0, hprime, hd, hdY, hcross, hpd, hsmooth, hrough⟩ := hpref
    exact Or.inr ⟨d, p, hd, hdY, hprime, hp, hrough⟩

/-- Normalizing the size of the translated integer costs only one extra S
in its logarithmic bound. -/
theorem shifted_log_le_enlarged_scale (D S X Y : ℝ) (N h : ℕ)
    (hSlog : Real.log 2 ≤ S) (hX : 0 < X)
    (hhi : Real.log X ≤ D * S) (hN : (N : ℝ) ≤ Real.exp (D * S))
    (hh : 1 ≤ h) (hhY : (h : ℝ) ≤ Y) (hYX : Y ≤ X) :
    Real.log ((N + h : ℕ) : ℝ) ≤ (D + 1) * S := by
  have hXS : X ≤ Real.exp (D * S) := by
    have he := Real.exp_le_exp.mpr hhi
    simpa only [Real.exp_log hX] using he
  have htwo : (2 : ℝ) ≤ Real.exp S := by
    have he := Real.exp_le_exp.mpr hSlog
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using he
  have hnpos : 0 < N + h := by omega
  have hnle : ((N + h : ℕ) : ℝ) ≤ Real.exp ((D + 1) * S) := by
    have hhle : (h : ℝ) ≤ Real.exp (D * S) := hhY.trans (hYX.trans hXS)
    calc
      ((N + h : ℕ) : ℝ) ≤ 2 * Real.exp (D * S) := by push_cast; linarith
      _ ≤ Real.exp S * Real.exp (D * S) :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hl := Real.log_le_log (by exact_mod_cast hnpos) hnle
  simpa only [Real.log_exp] using hl

/-- The complete eventual large-class estimate in the uniform moment range.
All prefix, harmonic, and translated-size hypotheses are discharged; only the
manuscript's size window remains. -/
theorem eventually_large_class_moment_bound (D r : ℝ) (_hD : 1 ≤ D) (hr : 0 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ S : ℝ in atTop, ∀ X Y : ℝ, ∀ N : ℕ,
      S / (2 * Real.log S) ≤ Real.log X → Real.log X ≤ D * S →
      Real.sqrt X ≤ Y → Y ≤ X → (N : ℝ) ≤ Real.exp (D * S) →
      (∑ h ∈ (Finset.Icc 1 ⌊Y⌋₊).filter
        (fun h => DivisorClasses.LargeClass (N + h) (Real.log X) Y),
        (truncatedDivisorCount X (N + h) : ℝ) ^ r) ≤
      2 * Y * Real.exp (r * (1 + Real.log (((D + 1) * S) / Real.log X)) *
        (Real.log X) ^ (1 / 16 : ℝ) + C * Real.log (1 + Real.log (Real.sqrt Y))) := by
  classical
  obtain ⟨C, hC, hbound⟩ := large_prefix_class_sqrt_harmonic_bound r hr
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_ge_atTop (Real.exp 32),
    eventually_ge_atTop (Real.log 2)] with S hSe hSlog
  intro X Y N hlo hhi hXY hYX hN
  have hSpos : 0 < S := (Real.exp_pos 32).trans_le hSe
  have hlog32 : 32 ≤ Real.log S := (Real.le_log_iff_exp_le hSpos).2 hSe
  have hlogpos : 0 < 2 * Real.log S := by linarith
  have hquad := Real.pow_div_factorial_le_exp (Real.log S) (by linarith) 2
  norm_num at hquad
  rw [Real.exp_log hSpos] at hquad
  have hlarge : 16 * Real.log S ≤ S := by
    have hm := mul_nonneg (sub_nonneg.mpr hlog32) (show 0 ≤ Real.log S by linarith)
    nlinarith
  have hratio : 8 ≤ S / (2 * Real.log S) := (le_div_iff₀ hlogpos).2 (by linarith)
  have hlogX : 8 ≤ Real.log X := hratio.trans hlo
  have hX0 : 0 ≤ X := (Real.sqrt_nonneg X).trans (hXY.trans hYX)
  have hX1 : 1 < X := by
    by_contra hx
    have := Real.log_nonpos hX0 (le_of_not_gt hx)
    linarith
  have hXpos : 0 < X := by linarith
  have hXbig : 16 ≤ X := by
    have hexp : Real.exp 8 ≤ X := by
      simpa only [Real.exp_log hXpos] using Real.exp_le_exp.mpr hlogX
    have he := Real.pow_div_factorial_le_exp (8 : ℝ) (by norm_num) 2
    norm_num at he
    linarith
  have hY : 4 ≤ Y := by
    have hsqrt : 4 ≤ Real.sqrt X := (Real.le_sqrt (by norm_num) hX0).2 (by norm_num; exact hXbig)
    exact hsqrt.trans hXY
  apply hbound X ((D + 1) * S) Y N
    ((Finset.Icc 1 ⌊Y⌋₊).filter
      (fun h => DivisorClasses.LargeClass (N + h) (Real.log X) Y))
    hX1 (by nlinarith) hY
  · exact Finset.filter_subset _ _
  · intro h hh
    obtain ⟨hhI, _⟩ := Finset.mem_filter.mp hh
    obtain ⟨hh1, hhY⟩ := Finset.mem_Icc.mp hhI
    have hhYR : (h : ℝ) ≤ Y :=
      (by exact_mod_cast hhY : (h : ℝ) ≤ (⌊Y⌋₊ : ℝ)).trans (Nat.floor_le (by linarith))
    exact shifted_log_le_enlarged_scale D S X Y N h hSlog hXpos hhi hN hh1 hhYR hYX
  · intro h hh
    exact (Finset.mem_filter.mp hh).2.inLargePrefixClass

/-- Exponential-cutoff form of the same complete class budget. -/
theorem eventually_large_class_moment_bound_exp (D r : ℝ) (hD : 1 ≤ D) (hr : 0 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ S : ℝ in atTop, ∀ v Y : ℝ, ∀ N : ℕ,
      S / (2 * Real.log S) ≤ v → v ≤ D * S →
      Real.exp (v / 2) ≤ Y → Y ≤ Real.exp v → (N : ℝ) ≤ Real.exp (D * S) →
      (∑ h ∈ (Finset.Icc 1 ⌊Y⌋₊).filter
        (fun h => DivisorClasses.LargeClass (N + h) v Y),
        (truncatedDivisorCount (Real.exp v) (N + h) : ℝ) ^ r) ≤
      2 * Y * Real.exp (r * (1 + Real.log (((D + 1) * S) / v)) *
        v ^ (1 / 16 : ℝ) + C * Real.log (1 + Real.log (Real.sqrt Y))) := by
  obtain ⟨C, hC, hbound⟩ := eventually_large_class_moment_bound D r hD hr
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound] with S hS
  intro v Y N hlo hhi hXY hYX hN
  have hsqrt : Real.sqrt (Real.exp v) = Real.exp (v / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
    congr 1
    ring
  simpa only [Real.log_exp] using hS (Real.exp v) Y N
    (by simpa only [Real.log_exp] using hlo)
    (by simpa only [Real.log_exp] using hhi)
    (by simpa only [hsqrt] using hXY) hYX hN

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_SmallPrimeDivisors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- A number with only small prime factors has few divisors once its logarithm is bounded. -/
theorem divisor_card_small_primes_bound (z W : ℝ) {n : ℕ} (hn : n ≠ 0)
    (hz : 0 ≤ z) (hnW : Real.log (n : ℝ) ≤ W)
    (hsmall : ∀ p ∈ n.primeFactors, (p : ℝ) ≤ z) :
    (n.divisors.card : ℝ) ≤ Real.exp (z * Real.log (1 + W / Real.log 2)) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hW0 : 0 ≤ W := le_trans (Real.log_nonneg hn1) hnW
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlen : (n.primeFactorsList.length : ℝ) ≤ W / Real.log 2 := by
    apply (primeFactorsList_length_le_log hn (by norm_num : (1 : ℝ) < 2) ?_).trans
      (div_le_div_of_nonneg_right hnW hlog2.le)
    intro p hp
    exact_mod_cast (Nat.prime_of_mem_primeFactorsList hp).two_le
  have hcardNat : n.primeFactors.card ≤ ⌊z⌋₊ := by
    calc
      _ ≤ (Finset.Icc 1 ⌊z⌋₊).card := by
        apply Finset.card_le_card
        intro p hp
        apply Finset.mem_Icc.mpr
        constructor
        · exact (Nat.mem_primeFactors.mp hp).1.pos
        · exact (Nat.le_floor_iff hz).2 (hsmall p hp)
      _ = _ := by simp
  have hcard : (n.primeFactors.card : ℝ) ≤ z :=
    (by exact_mod_cast hcardNat : (n.primeFactors.card : ℝ) ≤ (⌊z⌋₊ : ℝ)).trans (Nat.floor_le hz)
  have hbase : 1 ≤ 1 + W / Real.log 2 := by have := div_nonneg hW0 hlog2.le; linarith
  have hbase0 : 0 < 1 + W / Real.log 2 := lt_of_lt_of_le zero_lt_one hbase
  calc
    (n.divisors.card : ℝ) = ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) := by
      rw [Nat.card_divisors hn, Nat.cast_prod]
      simp
    _ ≤ ∏ p ∈ n.primeFactors, (1 + W / Real.log 2) := by
      apply Finset.prod_le_prod
      · intro p hp; positivity
      · intro p hp
        have hexp : (n.factorization p : ℝ) ≤ n.primeFactorsList.length := by
          exact_mod_cast (show n.factorization p ≤ n.primeFactorsList.length by
            rw [← Nat.primeFactorsList_count_eq]
            exact List.count_le_length)
        linarith
    _ = (1 + W / Real.log 2) ^ n.primeFactors.card := by simp
    _ ≤ (1 + W / Real.log 2) ^ z := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hbase hcard
    _ = _ := by rw [Real.rpow_def_of_pos hbase0]; congr 1; ring

/-- Split the factor list at z and combine the small- and large-prime estimates. -/
theorem truncatedDivisorCount_pointwise_exp_bound (X z W : ℝ) {n : ℕ} (hn : n ≠ 0)
    (hX : 1 < X) (hz : 1 < z) (hXW : Real.log X ≤ W)
    (hnW : Real.log (n : ℝ) ≤ W) :
    (truncatedDivisorCount X n : ℝ) ≤
      Real.exp (z * Real.log (1 + W / Real.log 2) +
        (1 + Real.log (W / Real.log X)) * Real.log X / Real.log z) := by
  let a := n.primeFactorsList.filter (fun p : ℕ => (p : ℝ) < z)
  let b := n.primeFactorsList.filter (fun p : ℕ => ¬ (p : ℝ) < z)
  have hab : a.prod * b.prod = n := by
    have h := List.prod_map_filter_mul_prod_map_filter_not
      (fun p : ℕ => (p : ℝ) < z) id n.primeFactorsList
    simpa only [List.map_id, Nat.prod_primeFactorsList hn] using h
  have ha0 : a.prod ≠ 0 := by
    intro ha; rw [ha, zero_mul] at hab; exact hn hab.symm
  have hb0 : b.prod ≠ 0 := by
    intro hb; rw [hb, mul_zero] at hab; exact hn hab.symm
  have had : a.prod ∣ n := ⟨b.prod, hab.symm⟩
  have hbd : b.prod ∣ n := ⟨a.prod, by simpa [mul_comm] using hab.symm⟩
  have haW : Real.log (a.prod : ℝ) ≤ W := by
    apply le_trans _ hnW
    apply Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero ha0)
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hn) had
  have hbW : Real.log (b.prod : ℝ) ≤ W := by
    apply le_trans _ hnW
    apply Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hb0)
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hbd
  have haperm : a.Perm a.prod.primeFactorsList :=
    Nat.primeFactorsList_unique rfl (by
      intro p hp
      exact Nat.prime_of_mem_primeFactorsList (List.mem_filter.mp hp).1)
  have hbperm : b.Perm b.prod.primeFactorsList :=
    Nat.primeFactorsList_unique rfl (by
      intro p hp
      exact Nat.prime_of_mem_primeFactorsList (List.mem_filter.mp hp).1)
  have hasmall : ∀ p ∈ a.prod.primeFactors, (p : ℝ) ≤ z := by
    intro p hp
    have hpm := Nat.mem_primeFactors.mp hp
    have hpl : p ∈ a.prod.primeFactorsList :=
      (Nat.mem_primeFactorsList_iff_dvd ha0 hpm.1).2 hpm.2.1
    have hpa : p ∈ a := haperm.mem_iff.mpr hpl
    exact (of_decide_eq_true (List.mem_filter.mp hpa).2).le
  have hblarge : ∀ p ∈ b.prod.primeFactorsList, z ≤ (p : ℝ) := by
    intro p hp
    have hpb : p ∈ b := hbperm.mem_iff.mpr hp
    exact le_of_not_gt (of_decide_eq_true (List.mem_filter.mp hpb).2)
  have hquot : n / a.prod = b.prod := by
    rw [← hab, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero ha0)]
  have hsmall := divisor_card_small_primes_bound z W ha0 (by linarith) haW hasmall
  have hlarge := truncatedDivisorCount_large_primes_bound X z W hb0 hX hz hXW hbW hblarge
  calc
    (truncatedDivisorCount X n : ℝ) ≤ (a.prod.divisors.card : ℝ) *
        (truncatedDivisorCount X b.prod : ℝ) := by
      have h := truncatedDivisorCount_factor_bound X had
      rw [hquot] at h
      exact_mod_cast h
    _ ≤ Real.exp (z * Real.log (1 + W / Real.log 2)) *
        Real.exp ((1 + Real.log (W / Real.log X)) * Real.log X / Real.log z) :=
      mul_le_mul hsmall hlarge (Nat.cast_nonneg _) (Real.exp_pos _).le
    _ = _ := (Real.exp_add _ _).symm

/-- Logarithmic version of the elementary small/large-prime split. -/
theorem truncatedDivisorCount_pointwise_log_bound (X z W : ℝ) {n : ℕ} (hn : n ≠ 0)
    (hX : 1 < X) (hz : 1 < z) (hXW : Real.log X ≤ W)
    (hnW : Real.log (n : ℝ) ≤ W) :
    Real.log (truncatedDivisorCount X n : ℝ) ≤
      z * Real.log (1 + W / Real.log 2) +
        (1 + Real.log (W / Real.log X)) * Real.log X / Real.log z := by
  have hpos : 0 < truncatedDivisorCount X n := by
    apply Finset.card_pos.mpr
    refine ⟨1, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
    · exact Nat.mem_divisors.mpr ⟨one_dvd n, hn⟩
    · simpa using hX.le
  have h := Real.log_le_log (by exact_mod_cast hpos)
    (truncatedDivisorCount_pointwise_exp_bound X z W hn hX hz hXW hnW)
  simpa only [Real.log_exp] using h

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_DivisorPointwiseUniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators Topology
open Filter
namespace Problem337

theorem divisorPointwiseError_tendsto (E : ℝ) :
    Tendsto (divisorPointwiseError E) atTop (𝓝 0) := by
  have h1 : Tendsto (fun S : ℝ => (Real.log S) ^ 2 / Real.sqrt S) atTop (𝓝 0) := by
    simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have h2 : Tendsto (fun S : ℝ => Real.log (Real.log S) / Real.log S) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp Real.tendsto_log_atTop
  have hc : Tendsto (fun S : ℝ => (1 + Real.log (2 * E)) / Real.log S) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have h := (h1.const_mul 4).add ((hc.add h2).const_mul 2)
  convert h using 1
  · ext S
    simp only [divisorPointwiseError]
    ring
  · norm_num

/-- Explicit estimate uniform over the admissible logarithmic size interval. -/
theorem truncatedDivisorCount_pointwise_error_bound (E S X : ℝ) {n : ℕ}
    (hE : 1 ≤ E) (hS : 1 < S) (hES : 1 + E / Real.log 2 ≤ S)
    (hn : n ≠ 0) (hX : 1 < X)
    (hlo : S / (2 * Real.log S) ≤ Real.log X)
    (hhi : Real.log X ≤ E * S) (hnhi : Real.log (n : ℝ) ≤ E * S) :
    Real.log (truncatedDivisorCount X n : ℝ) ≤ divisorPointwiseError E S * Real.log X := by
  have hS0 : 0 < S := by linarith
  have hE0 : 0 < E := by linarith
  have hls : 0 < Real.log S := Real.log_pos hS
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hv : 0 < Real.log X := Real.log_pos hX
  have hroot : 0 < Real.sqrt S := Real.sqrt_pos.mpr hS0
  have hroot1 : 1 < Real.sqrt S := by
    nlinarith [Real.sq_sqrt hS0.le, Real.sqrt_nonneg S]
  have hsize : S ≤ Real.log X * (2 * Real.log S) :=
    (div_le_iff₀ (by positivity)).1 hlo
  have hbasePos : 0 < 1 + E * S / Real.log 2 := by positivity
  have hbase : 1 + E * S / Real.log 2 ≤ S ^ 2 := by
    have hcoef : E / Real.log 2 ≤ S - 1 := by linarith
    have hc := mul_le_mul_of_nonneg_right hcoef hS0.le
    have heq : E * S / Real.log 2 = (E / Real.log 2) * S := by ring
    rw [heq]
    nlinarith
  have hlogbase : Real.log (1 + E * S / Real.log 2) ≤ 2 * Real.log S := by
    have h := Real.log_le_log hbasePos hbase
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hterm1 : Real.sqrt S * Real.log (1 + E * S / Real.log 2) ≤
      (4 * (Real.log S) ^ 2 / Real.sqrt S) * Real.log X := by
    calc
      _ ≤ Real.sqrt S * (2 * Real.log S) :=
        mul_le_mul_of_nonneg_left hlogbase (Real.sqrt_nonneg S)
      _ = (2 * S * Real.log S) / Real.sqrt S := by
        apply (eq_div_iff hroot.ne').2
        nlinarith [Real.sq_sqrt hS0.le]
      _ ≤ (4 * (Real.log S) ^ 2 * Real.log X) / Real.sqrt S := by
        apply div_le_div_of_nonneg_right _ hroot.le
        have h := mul_le_mul_of_nonneg_right hsize (show 0 ≤ 2 * Real.log S by positivity)
        nlinarith
      _ = _ := by ring
  have hratio : E * S / Real.log X ≤ 2 * E * Real.log S := by
    apply (div_le_iff₀ hv).2
    have h := mul_le_mul_of_nonneg_left hsize hE0.le
    nlinarith
  have hB : 1 + Real.log (E * S / Real.log X) ≤
      1 + Real.log (2 * E) + Real.log (Real.log S) := by
    have h := Real.log_le_log (show 0 < E * S / Real.log X by positivity) hratio
    rw [Real.log_mul (by positivity : 2 * E ≠ 0) hls.ne'] at h
    linarith
  have hterm2 : (1 + Real.log (E * S / Real.log X)) * Real.log X /
      Real.log (Real.sqrt S) ≤
      (2 * (1 + Real.log (2 * E) + Real.log (Real.log S)) / Real.log S) * Real.log X := by
    rw [Real.log_sqrt hS0.le]
    calc
      _ ≤ (1 + Real.log (2 * E) + Real.log (Real.log S)) * Real.log X /
          (Real.log S / 2) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hB hv.le) (by positivity)
      _ = _ := by ring
  have hbound := truncatedDivisorCount_pointwise_log_bound X (Real.sqrt S) (E * S)
    hn hX hroot1 hhi hnhi
  dsimp [divisorPointwiseError]
  nlinarith

/-- Uniform subpower growth of truncated divisor moments over the full size interval. -/
theorem truncatedDivisorCount_uniform_subpower (E r ε : ℝ) (hE : 1 ≤ E)
    (hr : 0 ≤ r) (hε : 0 < ε) :
    ∃ S0 : ℝ, ∀ S : ℝ, S0 ≤ S → ∀ X : ℝ, ∀ n : ℕ,
      n ≠ 0 → 1 < X → S / (2 * Real.log S) ≤ Real.log X →
      Real.log X ≤ E * S → Real.log (n : ℝ) ≤ E * S →
      (truncatedDivisorCount X n : ℝ) ^ r ≤ Real.exp (ε * Real.log X) := by
  have herror : ∀ᶠ S : ℝ in atTop, r * divisorPointwiseError E S < ε := by
    apply Filter.Tendsto.eventually_lt_const hε
    simpa using (divisorPointwiseError_tendsto E).const_mul r
  have hevent : ∀ᶠ S : ℝ in atTop, ∀ X : ℝ, ∀ n : ℕ,
      n ≠ 0 → 1 < X → S / (2 * Real.log S) ≤ Real.log X →
      Real.log X ≤ E * S → Real.log (n : ℝ) ≤ E * S →
      (truncatedDivisorCount X n : ℝ) ^ r ≤ Real.exp (ε * Real.log X) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ),
      eventually_ge_atTop (1 + E / Real.log 2), herror] with S hS hES herr
    intro X n hn hX hlo hhi hnhi
    have hcount : 0 < truncatedDivisorCount X n := by
      apply Finset.card_pos.mpr
      exact ⟨1, Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨one_dvd n, hn⟩,
        by simpa using hX.le⟩⟩
    rw [Real.rpow_def_of_pos (by exact_mod_cast hcount)]
    apply Real.exp_le_exp.mpr
    have hb := truncatedDivisorCount_pointwise_error_bound E S X hE hS hES hn hX hlo hhi hnhi
    have hbr := mul_le_mul_of_nonneg_right hb hr
    have he := mul_le_mul_of_nonneg_right herr.le (Real.log_pos hX).le
    nlinarith
  exact hevent.exists_forall_of_atTop

/-- The uniform pointwise estimate in the shifted-interval range of the moment lemma. -/
theorem truncatedDivisorCount_shifted_uniform_subpower (D r ε : ℝ) (hD : 1 ≤ D)
    (hr : 0 ≤ r) (hε : 0 < ε) :
    ∃ S0 : ℝ, ∀ S : ℝ, S0 ≤ S → ∀ X Y : ℝ, ∀ N h : ℕ,
      1 ≤ X → S / (2 * Real.log S) ≤ Real.log X →
      Real.log X ≤ D * S → (N : ℝ) ≤ Real.exp (D * S) →
      1 ≤ h → (h : ℝ) ≤ Y → Y ≤ X →
      (truncatedDivisorCount X (N + h) : ℝ) ^ r ≤ Real.exp (ε * Real.log X) := by
  obtain ⟨S0, hS0⟩ := truncatedDivisorCount_uniform_subpower (D + 1) r ε (by linarith) hr hε
  refine ⟨max S0 (max 2 (Real.log 2)), ?_⟩
  intro S hS X Y N h hX hlo hhi hN hh hhY hYX
  have hSS : S0 ≤ S := (le_max_left _ _).trans hS
  have hS2 : 2 ≤ S := (le_max_left _ _).trans ((le_max_right _ _).trans hS)
  have hSlog : Real.log 2 ≤ S := (le_max_right _ _).trans ((le_max_right _ _).trans hS)
  have hSpos : 0 < S := by linarith
  have hlogS : 0 < Real.log S := Real.log_pos (by linarith)
  have hlogX : 0 < Real.log X := lt_of_lt_of_le (by positivity) hlo
  have hXlt : 1 < X := by
    by_contra hx
    have hXe : X = 1 := by linarith
    simp [hXe] at hlogX
  have hXS : X ≤ Real.exp (D * S) := by
    have he := Real.exp_le_exp.mpr hhi
    simpa only [Real.exp_log (by linarith : 0 < X)] using he
  have htwo : (2 : ℝ) ≤ Real.exp S := by
    have he := Real.exp_le_exp.mpr hSlog
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using he
  have hnpos : 0 < N + h := by omega
  have hnle : ((N + h : ℕ) : ℝ) ≤ Real.exp ((D + 1) * S) := by
    have hhle : (h : ℝ) ≤ Real.exp (D * S) := hhY.trans (hYX.trans hXS)
    calc
      ((N + h : ℕ) : ℝ) ≤ 2 * Real.exp (D * S) := by push_cast; linarith
      _ ≤ Real.exp S * Real.exp (D * S) :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hnlog : Real.log ((N + h : ℕ) : ℝ) ≤ (D + 1) * S := by
    have hl := Real.log_le_log (by exact_mod_cast hnpos) hnle
    simpa only [Real.log_exp] using hl
  exact hS0 S hSS X (N + h) (Nat.ne_of_gt hnpos) hXlt hlo
    (by nlinarith) hnlog

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_IntermediateBandDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open Filter
open scoped Topology

namespace Problem337

/-- Fixed affine logarithmic functions are dominated by any positive power. -/
theorem eventually_affine_log_le_rpow (A B δ a : ℝ)
    (hδ : 0 < δ) (ha : 0 < a) :
    ∀ᶠ S : ℝ in atTop, A + B * Real.log S ≤ δ * S ^ a := by
  have hlog := (isLittleO_log_rpow_atTop ha).tendsto_div_nhds_zero
  have hconst : Tendsto (fun S : ℝ => A / S ^ a) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_rpow_atTop ha)
  have hratio : Tendsto (fun S : ℝ => (A + B * Real.log S) / S ^ a)
      atTop (𝓝 0) := by
    convert hconst.add (hlog.const_mul B) using 1 <;> simp [add_div, mul_div_assoc]
  filter_upwards [hratio.eventually (gt_mem_nhds hδ),
    eventually_gt_atTop (0 : ℝ)] with S hratio hS
  exact le_of_lt ((div_lt_iff₀ (Real.rpow_pos_of_pos hS a)).mp hratio)

/-- Every fixed sublinear power lies below the divisor-moment lower range. -/
theorem eventually_rpow_le_log_range (a : ℝ) (ha : a < 1) :
    ∀ᶠ S : ℝ in atTop, S ^ a ≤ S / (2 * Real.log S) := by
  have hsmall := eventually_affine_log_le_rpow 0 2 1 (1 - a)
    (by norm_num) (by linarith)
  filter_upwards [hsmall, eventually_gt_atTop (1 : ℝ)] with S hsmall hS
  have hSpos : 0 < S := lt_trans (by norm_num) hS
  have hlogS : 0 < Real.log S := Real.log_pos hS
  have h : 2 * Real.log S ≤ S ^ (1 - a) := by simpa using hsmall
  have hmul := mul_le_mul_of_nonneg_left h (le_of_lt (Real.rpow_pos_of_pos hSpos a))
  have heq : S ^ a * S ^ (1 - a) = S := by
    rw [← Real.rpow_add hSpos]
    ring_nf
    exact Real.rpow_one S
  rw [heq] at hmul
  exact (le_div_iff₀ (by positivity : 0 < 2 * Real.log S)).2 hmul

/-- Direct interface for combining the small-prime smooth tail with an
arbitrarily small pointwise divisor exponent. -/
theorem eventually_small_rankin_exponent_le (C : ℝ) :
    ∀ᶠ S : ℝ in atTop, ∀ v R : ℝ,
      S / (2 * Real.log S) ≤ v → R ≤ v / 200 →
      -v / 50 + C * S ^ (2 / 5 : ℝ) + R ≤ -v / 100 := by
  have hlarge : ∀ᶠ S : ℝ in atTop, 200 * C ≤ S ^ (7 / 20 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7 / 20)).eventually
      (eventually_ge_atTop (200 * C))
  filter_upwards [hlarge, eventually_rpow_le_log_range (3 / 4) (by norm_num),
    eventually_gt_atTop (0 : ℝ)] with S hlarge hroot hS
  intro v R hv hR
  have h := mul_le_mul_of_nonneg_right hlarge
    (le_of_lt (Real.rpow_pos_of_pos hS (2 / 5)))
  have heq : S ^ (7 / 20 : ℝ) * S ^ (2 / 5 : ℝ) = S ^ (3 / 4 : ℝ) := by
    rw [← Real.rpow_add hS]
    norm_num
  rw [heq] at h
  have hvroot := hroot.trans hv
  nlinarith

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_SubcriticalPowerSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337.DivisorMoment

/-- Integral comparison for a subcritical power, beginning at the integer two. -/
theorem shifted_power_sum_le (n : ℕ) {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    (∑ j ∈ Finset.range n, ((j : ℝ) + 2) ^ (α - 1)) ≤
      (((n : ℝ) + 1) ^ α - 1) / α := by
  have hanti : AntitoneOn (fun x : ℝ => x ^ (α - 1))
      (Set.Icc 1 (1 + (n : ℝ))) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by linarith)
  have hsum := hanti.sum_le_integral
  have hi : (∫ x in (1 : ℝ)..1 + (n : ℝ), x ^ (α - 1)) =
      (((n : ℝ) + 1) ^ α - 1) / α := by
    rw [integral_rpow (Or.inl (by linarith : (-1 : ℝ) < α - 1))]
    simp only [sub_add_cancel, Real.one_rpow, add_comm 1 (n : ℝ)]
  rw [hi] at hsum
  simpa only [Nat.cast_add, Nat.cast_one, show ∀ j : ℕ,
    (1 : ℝ) + ((j : ℝ) + 1) = (j : ℝ) + 2 by intro j; ring] using hsum

/-- Convenient coarse form of the same estimate. -/
theorem shifted_power_sum_le_div (n : ℕ) {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    (∑ j ∈ Finset.range n, ((j : ℝ) + 2) ^ (α - 1)) ≤
      ((n : ℝ) + 1) ^ α / α := by
  refine (shifted_power_sum_le n hα0 hα1).trans ?_
  exact div_le_div_of_nonneg_right (sub_le_self _ zero_le_one) hα0.le

/-- Any collection of integers in [2,T] obeys the same subcritical power bound. -/
theorem finite_power_sum_le (T : ℕ) (s : Finset ℕ)
    (hs : ∀ a ∈ s, 2 ≤ a ∧ a ≤ T)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    (∑ a ∈ s, (a : ℝ) ^ (α - 1)) ≤ ((T : ℝ) + 1) ^ α / α := by
  have hsub : s ⊆ Finset.Ico 2 (T + 2) := by
    intro a ha
    obtain ⟨ha2, haT⟩ := hs a ha
    exact Finset.mem_Ico.mpr ⟨ha2, by omega⟩
  calc
    (∑ a ∈ s, (a : ℝ) ^ (α - 1)) ≤
        ∑ a ∈ Finset.Ico 2 (T + 2), (a : ℝ) ^ (α - 1) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro a _ _
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    _ = ∑ j ∈ Finset.range T, ((j : ℝ) + 2) ^ (α - 1) := by
      simpa only [zero_add, Nat.Ico_zero_eq_range, Nat.cast_add, Nat.cast_ofNat,
        add_comm (2 : ℝ)] using
        (Finset.sum_Ico_add (fun a : ℕ => (a : ℝ) ^ (α - 1)) 0 T 2).symm
    _ ≤ ((T : ℝ) + 1) ^ α / α := shifted_power_sum_le_div T hα0 hα1

/-- A uniform elementary logarithmic bound for geometric Euler factors. -/
theorem log_inv_one_sub_le {x ρ : ℝ} (hx0 : 0 ≤ x) (hxρ : x ≤ ρ) (hρ : ρ < 1) :
    Real.log ((1 - x)⁻¹) ≤ x / (1 - ρ) := by
  have hx : 0 < 1 - x := by linarith
  have hρpos : 0 < 1 - ρ := by linarith
  calc
    Real.log ((1 - x)⁻¹) ≤ (1 - x)⁻¹ - 1 :=
      Real.log_le_sub_one_of_pos (inv_pos.mpr hx)
    _ = x / (1 - x) := by field_simp; ring
    _ ≤ x / (1 - ρ) := div_le_div_of_nonneg_left hx0 hρpos (by linarith)

/-- Logarithm of a finite geometric Euler product, requiring only a≥2, not primality. -/
theorem log_geometric_product_le (T : ℕ) (s : Finset ℕ)
    (hs : ∀ a ∈ s, 2 ≤ a ∧ a ≤ T)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    Real.log (∏ a ∈ s, (1 - (a : ℝ) ^ (α - 1))⁻¹) ≤
      ((T : ℝ) + 1) ^ α / (α * (1 - (2 : ℝ) ^ (α - 1))) := by
  let ρ : ℝ := (2 : ℝ) ^ (α - 1)
  have hρ : ρ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hρpos : 0 < 1 - ρ := by linarith
  have hx (a : ℕ) (ha : a ∈ s) : 0 ≤ (a : ℝ) ^ (α - 1) ∧
      (a : ℝ) ^ (α - 1) ≤ ρ := by
    refine ⟨Real.rpow_nonneg (Nat.cast_nonneg _) _, ?_⟩
    exact Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast (hs a ha).1)
      (by linarith)
  have hfac (a : ℕ) (ha : a ∈ s) : 0 < (1 - (a : ℝ) ^ (α - 1))⁻¹ := by
    apply inv_pos.mpr
    have := (hx a ha).2
    linarith
  rw [Real.log_prod (fun a ha => (hfac a ha).ne')]
  calc
    (∑ a ∈ s, Real.log ((1 - (a : ℝ) ^ (α - 1))⁻¹)) ≤
        ∑ a ∈ s, (a : ℝ) ^ (α - 1) / (1 - ρ) := by
      apply Finset.sum_le_sum
      intro a ha
      exact log_inv_one_sub_le (hx a ha).1 (hx a ha).2 hρ
    _ = (∑ a ∈ s, (a : ℝ) ^ (α - 1)) / (1 - ρ) := by rw [Finset.sum_div]
    _ ≤ (((T : ℝ) + 1) ^ α / α) / (1 - ρ) :=
      div_le_div_of_nonneg_right (finite_power_sum_le T s hs hα0 hα1.le) hρpos.le
    _ = _ := by dsimp [ρ]; rw [div_div]

/-- Real cutoff version of the geometric Euler-product estimate. -/
theorem log_geometric_product_le_real {U : ℝ} (hU : 1 ≤ U) (s : Finset ℕ)
    (hs : ∀ a ∈ s, 2 ≤ a ∧ (a : ℝ) ≤ U)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    Real.log (∏ a ∈ s, (1 - (a : ℝ) ^ (α - 1))⁻¹) ≤
      ((2 : ℝ) ^ α / (α * (1 - (2 : ℝ) ^ (α - 1)))) * U ^ α := by
  have hU0 : 0 ≤ U := by linarith
  have hρ : (2 : ℝ) ^ (α - 1) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hden : 0 < α * (1 - (2 : ℝ) ^ (α - 1)) := by positivity
  have hnat : ∀ a ∈ s, 2 ≤ a ∧ a ≤ ⌊U⌋₊ := by
    intro a ha
    exact ⟨(hs a ha).1, Nat.le_floor (hs a ha).2⟩
  refine (log_geometric_product_le ⌊U⌋₊ s hnat hα0 hα1).trans ?_
  have hfloor : (⌊U⌋₊ : ℝ) + 1 ≤ 2 * U := by
    have := Nat.floor_le hU0
    linarith
  have hp : ((⌊U⌋₊ : ℝ) + 1) ^ α ≤ (2 * U) ^ α :=
    Real.rpow_le_rpow (by positivity) hfloor hα0.le
  calc
    ((⌊U⌋₊ : ℝ) + 1) ^ α / (α * (1 - (2 : ℝ) ^ (α - 1))) ≤
        (2 * U) ^ α / (α * (1 - (2 : ℝ) ^ (α - 1))) :=
      div_le_div_of_nonneg_right hp hden.le
    _ = _ := by rw [Real.mul_rpow (by norm_num) hU0]; ring

/-- The small-prime Rankin product grows at most exponentially in S^(2/5).
No primality hypothesis is needed, since summing over all integers is an upper bound. -/
theorem small_prime_rankin_product_log_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ℝ), 1 ≤ S → ∀ s : Finset ℕ,
      (∀ p ∈ s, 2 ≤ p ∧ (p : ℝ) ≤ S ^ (4 : ℕ)) →
      Real.log (∏ p ∈ s, (1 - (p : ℝ) ^ (-(9 / 10 : ℝ)))⁻¹) ≤
        C * S ^ (2 / 5 : ℝ) := by
  let C : ℝ := (2 : ℝ) ^ (1 / 10 : ℝ) /
    ((1 / 10 : ℝ) * (1 - (2 : ℝ) ^ (-(9 / 10 : ℝ))))
  have hρ : (2 : ℝ) ^ (-(9 / 10 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro S hS s hs
  have hS0 : 0 ≤ S := by linarith
  have hU : 1 ≤ S ^ (4 : ℕ) := one_le_pow₀ hS
  have h := log_geometric_product_le_real hU s hs
    (by norm_num : (0 : ℝ) < 1 / 10) (by norm_num : (1 / 10 : ℝ) < 1)
  norm_num only [show (1 / 10 : ℝ) - 1 = -(9 / 10 : ℝ) by norm_num] at h
  change _ ≤ C * (S ^ (4 : ℕ)) ^ (1 / 10 : ℝ) at h
  have heq : (S ^ (4 : ℕ)) ^ (1 / 10 : ℝ) = S ^ (2 / 5 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hS0]
    norm_num
  simpa only [heq] using h

end Problem337.DivisorMoment

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_SmallPrimeRankin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337.DivisorMoment

/-- The small-prime smooth-prefix tail estimate from the divisor-moment proof.
The constant is absolute and the finite set of prefixes is arbitrary. -/
theorem small_prime_smooth_tail_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (S v : ℝ), 1 ≤ S → ∀ (N : ℕ),
      (N : ℝ) ≤ S ^ (4 : ℕ) + 1 → ∀ s : Finset ℕ,
      (∀ n ∈ s, n ∈ N.smoothNumbers) →
      (∀ n ∈ s, Real.exp (v / 5) ≤ (n : ℝ)) →
      (∑ n ∈ s, (1 : ℝ) / n) ≤ Real.exp (-v / 50 + C * S ^ (2 / 5 : ℝ)) := by
  obtain ⟨C, hC, hprodlog⟩ := small_prime_rankin_product_log_bound
  refine ⟨C, hC, ?_⟩
  intro S v hS N hN s hs hlarge
  have hprimes : ∀ p ∈ N.primesBelow, 2 ≤ p ∧ (p : ℝ) ≤ S ^ (4 : ℕ) := by
    intro p hp
    refine ⟨(Nat.prime_of_mem_primesBelow hp).two_le, ?_⟩
    have hpN := Nat.lt_of_mem_primesBelow hp
    have hpR : (p : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hpN
    linarith
  have hrpow (p : ℕ) (hp : p ∈ N.primesBelow) :
      0 ≤ (p : ℝ) ^ (-(9 / 10 : ℝ)) ∧ (p : ℝ) ^ (-(9 / 10 : ℝ)) < 1 := by
    refine ⟨Real.rpow_nonneg (Nat.cast_nonneg _) _, ?_⟩
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primesBelow hp).one_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by norm_num)
  have hprodpos : 0 < ∏ p ∈ N.primesBelow, (1 - (p : ℝ) ^ (-(9 / 10 : ℝ)))⁻¹ := by
    apply Finset.prod_pos
    intro p hp
    exact inv_pos.mpr (sub_pos.mpr (hrpow p hp).2)
  have hprod : (∏ p ∈ N.primesBelow, (1 - (p : ℝ) ^ (-(9 / 10 : ℝ)))⁻¹) ≤
      Real.exp (C * S ^ (2 / 5 : ℝ)) :=
    (Real.log_le_iff_le_exp hprodpos).mp (hprodlog S hS N.primesBelow hprimes)
  have heuler : (∏ p ∈ N.primesBelow, ∑' j : ℕ,
      ((j + 1 : ℕ) : ℝ) ^ (0 : ℕ) * ((p : ℝ) ^ ((1 / 10 : ℝ) - 1)) ^ j) =
      ∏ p ∈ N.primesBelow, (1 - (p : ℝ) ^ (-(9 / 10 : ℝ)))⁻¹ := by
    apply Finset.prod_congr rfl
    intro p hp
    norm_num only [pow_zero, one_mul, show (1 / 10 : ℝ) - 1 = -(9 / 10 : ℝ) by norm_num]
    exact tsum_geometric_of_lt_one (hrpow p hp).1 (hrpow p hp).2
  have htail := Problem337.divisor_smooth_rankin_bound 0
    (by norm_num : (0 : ℝ) ≤ 1 / 10) (by norm_num : (1 / 10 : ℝ) < 1)
    N s hs hlarge
  simp only [pow_zero] at htail heuler
  rw [heuler] at htail
  calc
    (∑ n ∈ s, (1 : ℝ) / n) ≤ Real.exp (-(1 / 10 : ℝ) * (v / 5)) *
        ∏ p ∈ N.primesBelow, (1 - (p : ℝ) ^ (-(9 / 10 : ℝ)))⁻¹ := htail
    _ ≤ Real.exp (-(1 / 10 : ℝ) * (v / 5)) * Real.exp (C * S ^ (2 / 5 : ℝ)) :=
      mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
    _ = Real.exp (-v / 50 + C * S ^ (2 / 5 : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      ring

end Problem337.DivisorMoment

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_SmallPrimeClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

open scoped BigOperators

namespace Problem337.DivisorMoment

/-- A constant pointwise bound and a reciprocal sum over admissible prefix
divisors control the corresponding class in a translated short interval. -/
theorem divisor_class_sum_le_exp
    (N : ℕ) (Y R T : ℝ) (A D : Finset ℕ) (w : ℕ → ℝ)
    (hY : 0 ≤ Y) (hA : A ⊆ Finset.Ioc N (N + ⌊Y⌋₊))
    (hassign : ∀ n ∈ A, ∃ d ∈ D, d ∣ n)
    (hweight : ∀ n ∈ A, w n ≤ Real.exp R)
    (hD : ∀ d ∈ D, 0 < d ∧ (d : ℝ) ≤ Y)
    (htail : (∑ d ∈ D, 1 / (d : ℝ)) ≤ Real.exp T) :
    (∑ n ∈ A, w n) ≤ 2 * Y * Real.exp (T + R) := by
  have hbound := sum_le_divisor_majorant_real_cutoff N Y A D w
    (fun _ => Real.exp R) hY hA
    (fun n hn => by
      obtain ⟨d, hd, hdvd⟩ := hassign n hn
      exact ⟨d, hd, hdvd, hweight n hn⟩)
    (fun _ _ => (Real.exp_pos R).le) hD
  have hsum : (∑ d ∈ D, Real.exp R / (d : ℝ)) =
      Real.exp R * ∑ d ∈ D, 1 / (d : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    ring
  rw [hsum] at hbound
  calc
    (∑ n ∈ A, w n) ≤ 2 * Y * (Real.exp R * ∑ d ∈ D, 1 / (d : ℝ)) := hbound
    _ ≤ 2 * Y * (Real.exp R * Real.exp T) := by
      gcongr
    _ = 2 * Y * Real.exp (T + R) := by
      rw [← Real.exp_add, add_comm R T]

/-- The same bound with the short interval indexed by its displacement h.
No choice or uniqueness of the prefix divisor is required. -/
theorem shifted_divisor_class_sum_le_exp
    (N : ℕ) (Y R T : ℝ) (A D : Finset ℕ) (w : ℕ → ℝ)
    (hY : 0 ≤ Y) (hA : A ⊆ Finset.Icc 1 ⌊Y⌋₊)
    (hassign : ∀ h ∈ A, ∃ d ∈ D, d ∣ N + h)
    (hweight : ∀ h ∈ A, w (N + h) ≤ Real.exp R)
    (hD : ∀ d ∈ D, 0 < d ∧ (d : ℝ) ≤ Y)
    (htail : (∑ d ∈ D, 1 / (d : ℝ)) ≤ Real.exp T) :
    (∑ h ∈ A, w (N + h)) ≤ 2 * Y * Real.exp (T + R) := by
  classical
  let B := A.image (fun h => N + h)
  have hB : B ⊆ Finset.Ioc N (N + ⌊Y⌋₊) := by
    intro n hn
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hh1, hhY⟩ := Finset.mem_Icc.mp (hA hh)
    exact Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
  have hsum : (∑ n ∈ B, w n) = ∑ h ∈ A, w (N + h) := by
    apply Finset.sum_image
    intro a _ b _ hab
    exact Nat.add_left_cancel hab
  rw [← hsum]
  apply divisor_class_sum_le_exp N Y R T B D w hY hB
  · intro n hn
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hn
    exact hassign h hh
  · intro n hn
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hn
    exact hweight h hh
  · exact hD
  · exact htail

/-- Displacement-indexed small-prime class estimate used in the moment sum
over 1 ≤ h ≤ Y. -/
theorem small_prime_class_shifted_sum_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (S v R Y : ℝ), 1 ≤ S → 0 ≤ Y →
      ∀ (N P : ℕ), (P : ℝ) ≤ S ^ (4 : ℕ) + 1 →
      ∀ (A : Finset ℕ) (w : ℕ → ℝ), A ⊆ Finset.Icc 1 ⌊Y⌋₊ →
      (∀ h ∈ A, w (N + h) ≤ Real.exp R) →
      (∀ h ∈ A, ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ Y ∧ d ∣ N + h ∧
        d ∈ P.smoothNumbers ∧ Real.exp (v / 5) ≤ (d : ℝ)) →
      (∑ h ∈ A, w (N + h)) ≤
        2 * Y * Real.exp (-v / 50 + C * S ^ (2 / 5 : ℝ) + R) := by
  classical
  obtain ⟨C, hC, htail⟩ := small_prime_smooth_tail_bound
  refine ⟨C, hC, ?_⟩
  intro S v R Y hS hY N P hP A w hA hw hpfx
  let D : Finset ℕ := (Finset.Icc 1 ⌊Y⌋₊).filter
    (fun d => d ∈ P.smoothNumbers ∧ Real.exp (v / 5) ≤ (d : ℝ))
  have hD (d : ℕ) (hd : d ∈ D) : 0 < d ∧ (d : ℝ) ≤ Y := by
    have hdI := Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1
    exact ⟨hdI.1, (by exact_mod_cast hdI.2 : (d : ℝ) ≤ ⌊Y⌋₊).trans
      (Nat.floor_le hY)⟩
  apply shifted_divisor_class_sum_le_exp N Y R (-v / 50 + C * S ^ (2 / 5 : ℝ))
    A D w hY hA
  · intro n hn
    obtain ⟨d, hd0, hdY, hdvd, hds, hdlarge⟩ := hpfx n hn
    refine ⟨d, Finset.mem_filter.mpr ⟨?_, hds, hdlarge⟩, hdvd⟩
    exact Finset.mem_Icc.mpr ⟨hd0, Nat.le_floor hdY⟩
  · exact hw
  · exact hD
  · exact htail S v hS P hP D
      (fun d hd => (Finset.mem_filter.mp hd).2.1)
      (fun d hd => (Finset.mem_filter.mp hd).2.2)

end Problem337.DivisorMoment

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_SmallPrimeSelectedClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

open Filter Topology
open scoped BigOperators

namespace Problem337.DivisorMoment

/-- The selected-prime-prefix form of the small class estimate. The prefix
crosses sqrt(Y) at a prime p whose logarithm is below 4 log(S); its size and
smoothness are conclusions, not additional hypotheses on the class. -/
theorem small_prime_selected_prefix_sum_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ S : ℝ in atTop,
      ∀ (v R Y : ℝ), S / (2 * Real.log S) ≤ v →
      1 ≤ Y → v / 2 ≤ Real.log Y → ∀ (N : ℕ),
      ∀ (A : Finset ℕ) (w : ℕ → ℝ), A ⊆ Finset.Icc 1 ⌊Y⌋₊ →
      (∀ h ∈ A, w (N + h) ≤ Real.exp R) →
      (∀ h ∈ A, ∃ d p : ℕ, 0 < d ∧ 0 < p ∧ d ∣ N + h ∧
        (d : ℝ) ≤ Real.sqrt Y ∧ Real.sqrt Y < (d : ℝ) * p ∧
        (∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ d → ℓ ≤ p) ∧
        Real.log (p : ℝ) < v ^ (15 / 16 : ℝ) ∧
        Real.log (p : ℝ) < 4 * Real.log S) →
      (∑ h ∈ A, w (N + h)) ≤
        2 * Y * Real.exp (-v / 50 + C * S ^ (2 / 5 : ℝ) + R) := by
  obtain ⟨C, hC, hsum⟩ := small_prime_class_shifted_sum_bound
  refine ⟨C, hC, ?_⟩
  filter_upwards [Problem337.PrimePrefixSize.eventually_uniform_prefix_large,
    eventually_ge_atTop (1 : ℝ)] with S hpre hS
  intro v R Y hv hY hYlog N A w hA hw hpfx
  have hS0 : 0 < S := by linarith
  have hY0 : 0 < Y := by linarith
  have hsqrt : Real.sqrt Y ≤ Y := Real.sqrt_le_self_iff.mpr (Or.inr hY)
  apply hsum S v R Y hS hY0.le N ⌈S ^ (4 : ℕ)⌉₊
    (Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ S ^ (4 : ℕ))).le
    A w hA hw
  intro h hh
  obtain ⟨d, p, hd, hp, hdvd, hdY, hcross, hpf, hplarge, hplog⟩ := hpfx h hh
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hlarge : Real.exp (v / 5) < (d : ℝ) :=
    hpre v d p Y hv hdR hpR hY0 hYlog hcross hplarge
  have hpS : (p : ℝ) < S ^ (4 : ℕ) := by
    apply (Real.log_lt_log_iff hpR (pow_pos hS0 4)).mp
    simpa only [Real.log_pow, Nat.cast_ofNat] using hplog
  refine ⟨d, hd, hdY.trans hsqrt, hdvd, ?_, hlarge.le⟩
  apply Nat.mem_smoothNumbers.mpr
  refine ⟨hd.ne', ?_⟩
  intro ℓ hℓ
  apply Nat.lt_ceil.mpr
  have hℓp := hpf ℓ (Nat.prime_of_mem_primeFactorsList hℓ)
    (Nat.dvd_of_mem_primeFactorsList hℓ)
  have hℓpR : (ℓ : ℝ) ≤ p := by exact_mod_cast hℓp
  exact hℓpR.trans_lt hpS

end Problem337.DivisorMoment

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_SmallPrimeMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open Filter Topology
open scoped BigOperators
namespace Problem337.DivisorMoment
attribute [local instance] Classical.propDecidable

/-- Complete small-prime contribution, including the actual class, pointwise
weight control, and exponential loss absorption. -/
theorem small_class_truncated_moment_bound (D r : ℝ) (hD : 1 ≤ D) (hr : 0 ≤ r) :
    ∀ᶠ S : ℝ in atTop, ∀ X Y : ℝ, ∀ N : ℕ,
      S / (2 * Real.log S) ≤ Real.log X →
      Real.log X ≤ D * S → Real.sqrt X ≤ Y → Y ≤ X →
      (N : ℝ) ≤ Real.exp (D * S) →
      (∑ h ∈ Finset.Icc 1 ⌊Y⌋₊ with
          DivisorClasses.SmallClass (N + h) S (Real.log X) Y,
        (truncatedDivisorCount X (N + h) : ℝ) ^ r) ≤
        2 * Y * Real.exp (-Real.log X / 100) := by
  obtain ⟨C, _hC, hclass⟩ := small_prime_selected_prefix_sum_bound
  obtain ⟨S0, hpoint⟩ := truncatedDivisorCount_shifted_uniform_subpower
    D r (1 / 200) hD hr (by norm_num)
  filter_upwards [hclass, eventually_small_rankin_exponent_le C,
    eventually_ge_atTop S0, eventually_ge_atTop (2 : ℝ)] with S hclass habs hS0 hS2
  intro X Y N hlo hhi hXY hYX hN
  have hSpos : 0 < S := by linarith
  have hlogS : 0 < Real.log S := Real.log_pos (by linarith)
  have hlogX : 0 < Real.log X := (by positivity : 0 < S / (2 * Real.log S)).trans_le hlo
  have hXnonneg : 0 ≤ X := (Real.sqrt_nonneg X).trans (hXY.trans hYX)
  have hX : 1 < X := (Real.log_pos_iff hXnonneg).mp hlogX
  have hXpos : 0 < X := by linarith
  have hsqrt1 : 1 ≤ Real.sqrt X := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hX.le
  have hY : 1 ≤ Y := hsqrt1.trans hXY
  have hYpos : 0 < Y := by linarith
  have hYlog : Real.log X / 2 ≤ Real.log Y := by
    have h := Real.log_le_log (Real.sqrt_pos.mpr hXpos) hXY
    simpa only [Real.log_sqrt hXnonneg] using h
  let A : Finset ℕ := (Finset.Icc 1 ⌊Y⌋₊).filter
    (fun h => DivisorClasses.SmallClass (N + h) S (Real.log X) Y)
  have hA : A ⊆ Finset.Icc 1 ⌊Y⌋₊ := Finset.filter_subset _ _
  have hw : ∀ h ∈ A, (truncatedDivisorCount X (N + h) : ℝ) ^ r ≤
      Real.exp ((1 / 200 : ℝ) * Real.log X) := by
    intro h hh
    obtain ⟨hh1, hhY⟩ := Finset.mem_Icc.mp (hA hh)
    have hhYR : (h : ℝ) ≤ Y :=
      (by exact_mod_cast hhY : (h : ℝ) ≤ ⌊Y⌋₊).trans (Nat.floor_le hYpos.le)
    exact hpoint S hS0 X Y N h hX.le hlo hhi hN hh1 hhYR hYX
  have hpfx : ∀ h ∈ A, ∃ d p : ℕ, 0 < d ∧ 0 < p ∧ d ∣ N + h ∧
      (d : ℝ) ≤ Real.sqrt Y ∧ Real.sqrt Y < (d : ℝ) * p ∧
      (∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ d → ℓ ≤ p) ∧
      Real.log (p : ℝ) < Real.log X ^ (15 / 16 : ℝ) ∧
      Real.log (p : ℝ) < 4 * Real.log S := by
    intro h hh
    obtain ⟨d, p, hpref, hplarge, hpsmall⟩ := (Finset.mem_filter.mp hh).2
    obtain ⟨hd, hp, hdvd, hdY, hcross, _hpdvd, hpf, _hrf⟩ := hpref
    exact ⟨d, p, hd, hp.pos, hdvd, hdY,
      by simpa only [Nat.cast_mul] using hcross, hpf, hplarge, hpsmall⟩
  have hbound := hclass (Real.log X) ((1 / 200 : ℝ) * Real.log X) Y hlo hY hYlog
    N A (fun n => (truncatedDivisorCount X n : ℝ) ^ r) hA hw hpfx
  have hexp := habs (Real.log X) ((1 / 200 : ℝ) * Real.log X) hlo
    (by ring_nf; exact le_rfl)
  exact hbound.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp)
    (by positivity))

end Problem337.DivisorMoment

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_UniformDivisorMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

open Filter
open scoped BigOperators

namespace Problem337.DivisorMoment

attribute [local instance] Classical.propDecidable

/-- The complete uniform shifted divisor moment, with the upper cutoff
parameterized exponentially. All three prime-factor classes are estimated
unconditionally; the threshold depends only on the fixed `D` and `r`. -/
theorem eventually_uniform_divisor_moment_exp (D r : ℝ)
    (hD : 1 ≤ D) (hr : 0 ≤ r) :
    ∀ᶠ S : ℝ in atTop, ∀ v Y : ℝ, ∀ N : ℕ,
      S / (2 * Real.log S) ≤ v → v ≤ D * S →
      Real.exp (v / 2) ≤ Y → Y ≤ Real.exp v →
      (N : ℝ) ≤ Real.exp (D * S) →
      (∑ h ∈ Finset.Icc 1 ⌊Y⌋₊,
        (truncatedDivisorCount (Real.exp v) (N + h) : ℝ) ^ r) ≤
        Y * Real.exp (S ^ (1 / 4 : ℝ)) := by
  obtain ⟨C, hC, hlarge⟩ := eventually_large_class_moment_bound_exp D r hD hr
  filter_upwards [hlarge, small_class_truncated_moment_bound D r hD hr,
    eventually_intermediate_band_budget D r hD hr,
    DivisorClasses.eventually_class_budget_assembly D r C hD hr hC.le]
    with S hlarge hsmall hband hassemble
  intro v Y N hvlo hvhi hYlo hYhi hN
  have hYpos : 0 < Y := (Real.exp_pos (v / 2)).trans_le hYlo
  have hsqrt : Real.sqrt (Real.exp v) = Real.exp (v / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
    congr 1
    ring
  apply hassemble v Y hvlo hvhi hYlo hYhi (Finset.Icc 1 ⌊Y⌋₊)
    (fun h => N + h) (fun h => (truncatedDivisorCount (Real.exp v) (N + h) : ℝ) ^ r)
  · intro h hh
    positivity
  · exact hlarge v Y N hvlo hvhi hYlo hYhi hN
  · simpa only [Real.log_exp] using hsmall (Real.exp v) Y N
      (by simpa only [Real.log_exp] using hvlo)
      (by simpa only [Real.log_exp] using hvhi)
      (by simpa only [hsqrt] using hYlo) hYhi hN
  · intro j
    by_cases hj : 4 * Real.log S * 2 ^ j ≤ v ^ (15 / 16 : ℝ)
    · exact hband v Y N j hvlo hvhi hYlo hYhi hN hj
    · have hempty : (Finset.Icc 1 ⌊Y⌋₊).filter
          (fun h => DivisorClasses.BandClass (N + h) S v Y j) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro h hh hb
        exact hj (DivisorClasses.band_scale_lt hb).le
      simp only [hempty, Finset.sum_empty]
      positivity

/-- Uniform divisor moments with real cutoffs. The statement also covers a real
interval length through its floor. -/
theorem eventually_uniform_divisor_moment (D r : ℝ)
    (hD : 1 ≤ D) (hr : 0 ≤ r) :
    ∀ᶠ S : ℝ in atTop, ∀ X Y : ℝ, ∀ N : ℕ,
      S / (2 * Real.log S) ≤ Real.log X → Real.log X ≤ D * S →
      Real.sqrt X ≤ Y → Y ≤ X → (N : ℝ) ≤ Real.exp (D * S) →
      (∑ h ∈ Finset.Icc 1 ⌊Y⌋₊,
        (truncatedDivisorCount X (N + h) : ℝ) ^ r) ≤
        Y * Real.exp (S ^ (1 / 4 : ℝ)) := by
  filter_upwards [eventually_uniform_divisor_moment_exp D r hD hr,
    eventually_ge_atTop (2 : ℝ)] with S hmoment hS
  intro X Y N hvlo hvhi hYlo hYhi hN
  have hSpos : 0 < S := by linarith
  have hlogS : 0 < Real.log S := Real.log_pos (by linarith)
  have hlogX : 0 < Real.log X :=
    (by positivity : 0 < S / (2 * Real.log S)).trans_le hvlo
  have hXnonneg : 0 ≤ X := (Real.sqrt_nonneg X).trans (hYlo.trans hYhi)
  have hX : 1 < X := (Real.log_pos_iff hXnonneg).mp hlogX
  have hXpos : 0 < X := by linarith
  have hsqrt : Real.exp (Real.log X / 2) = Real.sqrt X := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hXpos]
    congr 1
    ring
  simpa only [Real.exp_log hXpos] using hmoment (Real.log X) Y N hvlo hvhi
    (by simpa only [hsqrt] using hYlo)
    (by simpa only [Real.exp_log hXpos] using hYhi) hN

end Problem337.DivisorMoment

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_DensityMomentBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
open Filter

namespace Problem337

/-- All moments required by the canonical geometric density family hold
unconditionally, simultaneously at each level and for every divisor of its
auxiliary denominator. Only the stated size ranges remain as hypotheses. -/
theorem eventually_residue_level_moment_oai
    (DM η r : ℝ) (hDM : 1 < DM) (hη : 0 < η) (hηhalf : η ≤ 1 / 2)
    (hr : 0 ≤ r) :
    ∀ᶠ S : ℝ in atTop, ∀ C M : ℕ, 0 < C → 0 < M →
      (C : ℝ) ≤ Real.exp (8 * (DM + 2) * S) →
      (M : ℝ) ≤ Real.exp (DM * S) →
      ∀ j : ℕ, j < ResidueLevels.depth ((DM + 2) * S) (ResidueLevels.scale S) η →
      ∀ t : ℕ, t ∣ M →
      (∑ h ∈ Finset.Icc 1
          ⌊ResidueLevels.level ((DM + 2) * S) (ResidueLevels.scale S) η (j + 1)⌋₊,
        densityDivisorCount
          (ResidueLevels.level ((DM + 2) * S) (ResidueLevels.scale S) η j)
          (ResidueLevels.factor ((DM + 2) * S) (ResidueLevels.scale S) η S C j * t + h)
          ^ r) ≤
        ResidueLevels.level ((DM + 2) * S) (ResidueLevels.scale S) η (j + 1) *
          Real.exp (S ^ (1 / 4 : ℝ)) := by
  exact eventually_residue_level_moment_of_uniform DM η r hDM hη hηhalf
    (DivisorMoment.eventually_uniform_divisor_moment (densityMomentParameter DM) r
      (densityMomentParameter_ge_one hDM) hr)

end Problem337

end

end OAI
end

theorem solution : type_of% @OAI.Problem337.eventually_residue_level_moment_oai := @OAI.Problem337.eventually_residue_level_moment_oai
