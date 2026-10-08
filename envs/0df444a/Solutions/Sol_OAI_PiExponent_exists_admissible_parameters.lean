-- Prove2me | solution 1 for OAI.PiExponent.exists_admissible_parameters
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-07T19:43:19.207106+00:00
-- url     : https://prove2.me/submissions/28bc9f20-75db-47a1-8b0a-f1f97066b1a6

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Convert
import Definitions.Def_OAI_PiExponent_AdmissibleDeterminantParameters

set_option maxHeartbeats 1200000
open scoped BigOperators

-- Adapted from openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a.

namespace OAI

namespace PiExponent

theorem exists_rational_parameters (ν : ℝ) (hν : 2 < ν) :
    ∃ θ A B C : ℚ,
      0 < (θ : ℝ) ∧ (θ : ℝ) < A ∧ (A : ℝ) < B ∧ (B : ℝ) < 1 ∧
      ν * ((A : ℝ) - θ) > 1 - θ ∧
      1 < (C : ℝ) ∧ (B : ℝ) < 1 / C ∧
      (B : ℝ) < C * θ ∧ (C : ℝ) * θ < 1 := by
  have hνpos : 0 < ν := by linarith
  have hdiv : 1 / ν < (1 / 2 : ℝ) :=
    (div_lt_iff₀ hνpos).2 (by linarith)
  obtain ⟨b, hbl, hbu⟩ := exists_rat_btwn (show (1 / 2 : ℝ) < 1 - 1 / ν by linarith)
  have hbpos : 0 < (b : ℝ) := by linarith
  have hb1 : (b : ℝ) < 1 := by
    have := one_div_pos.mpr hνpos
    linarith
  have hνb : ν * (b : ℝ) < ν - 1 := calc
    _ < ν * (1 - 1 / ν) := mul_lt_mul_of_pos_left hbu hνpos
    _ = ν - 1 := by field_simp
  have hcoeff : 0 < ν * (1 - (b : ℝ)) - 1 := by nlinarith
  have hδtop : 0 < min (1 : ℝ) ((2 * (b : ℝ) - 1) / ((b : ℝ) * b)) :=
    lt_min (by norm_num) (div_pos (by linarith) (mul_pos hbpos hbpos))
  obtain ⟨δ, hδpos, hδtop⟩ := exists_rat_btwn hδtop
  have hδ1 : (δ : ℝ) < 1 := lt_of_lt_of_le hδtop (min_le_left _ _)
  have hδsmall : (δ : ℝ) < (2 * (b : ℝ) - 1) / ((b : ℝ) * b) :=
    lt_of_lt_of_le hδtop (min_le_right _ _)
  have hδprod : (δ : ℝ) * ((b : ℝ) * b) < 2 * (b : ℝ) - 1 :=
    (lt_div_iff₀ (mul_pos hbpos hbpos)).mp hδsmall
  let θ : ℚ := 1 - δ
  let A : ℚ := 1 - b * δ
  have hθcast : (θ : ℝ) = 1 - (δ : ℝ) := by simp [θ]
  have hAcast : (A : ℝ) = 1 - (b : ℝ) * δ := by simp [A]
  have hθpos : 0 < (θ : ℝ) := by rw [hθcast]; linarith
  have hθA : (θ : ℝ) < A := by
    rw [hθcast, hAcast]
    nlinarith [mul_pos (sub_pos.mpr hb1) hδpos]
  have hApos : 0 < (A : ℝ) := lt_trans hθpos hθA
  have hA1 : (A : ℝ) < 1 := by
    rw [hAcast]
    nlinarith [mul_pos hbpos hδpos]
  have hAsq : (A : ℝ) ^ 2 < θ := by
    rw [hAcast, hθcast]
    nlinarith [mul_pos hδpos (sub_pos.mpr hδprod)]
  have hgap : 1 - (θ : ℝ) < ν * ((A : ℝ) - θ) := by
    rw [hAcast, hθcast]
    nlinarith [mul_pos hcoeff hδpos]
  have hCinterval : (A : ℝ) / θ < 1 / A := by
    apply (div_lt_div_iff₀ hθpos hApos).2
    nlinarith
  obtain ⟨C, hClo, hChi⟩ := exists_rat_btwn hCinterval
  have hC1 : 1 < (C : ℝ) := by
    have : (1 : ℝ) < (A : ℝ) / θ := (lt_div_iff₀ hθpos).2 (by simpa using hθA)
    exact lt_trans this hClo
  have hCpos : 0 < (C : ℝ) := by linarith
  have hACθ : (A : ℝ) < (C : ℝ) * θ := (div_lt_iff₀ hθpos).mp hClo
  have hCA : (C : ℝ) * A < 1 := (lt_div_iff₀ hApos).mp hChi
  have hAinvC : (A : ℝ) < 1 / C := (lt_div_iff₀ hCpos).2 (by nlinarith)
  have hCθ1 : (C : ℝ) * θ < 1 := by nlinarith [mul_lt_mul_of_pos_left hθA hCpos]
  have hBinterval : (A : ℝ) < min (1 / (C : ℝ)) ((C : ℝ) * θ) :=
    lt_min hAinvC hACθ
  obtain ⟨B, hBlo, hBhi⟩ := exists_rat_btwn hBinterval
  have hBinv : (B : ℝ) < 1 / C := lt_of_lt_of_le hBhi (min_le_left _ _)
  have hBCθ : (B : ℝ) < (C : ℝ) * θ := lt_of_lt_of_le hBhi (min_le_right _ _)
  exact ⟨θ, A, B, C, hθpos, hθA, hBlo, lt_trans hBCθ hCθ1,
    hgap, hC1, hBinv, hBCθ, hCθ1⟩

theorem exists_eta_preserving_exponent_gap
    (nu theta A : ℝ) (hnu : 2 < nu) (hA : 0 < A)
    (hgap : 1 - theta < nu * (A - theta)) :
    ∃ eta : ℝ, 0 < eta ∧ eta < 1 ∧
      0 < nu * (A * (1 - eta) - theta) - (1 - theta) := by
  let gap : ℝ := nu * (A - theta) - (1 - theta)
  have hgap_pos : 0 < gap := by dsimp [gap]; linarith
  have hnu_pos : 0 < nu := by linarith
  have hden_pos : 0 < 2 * nu * A := by positivity
  let eta : ℝ := min (1 / 2) (gap / (2 * nu * A))
  have heta_pos : 0 < eta := by
    dsimp [eta]
    exact lt_min (by norm_num) (div_pos hgap_pos hden_pos)
  have heta_half : eta ≤ 1 / 2 := min_le_left _ _
  have heta_lt_one : eta < 1 := by linarith
  have heta_gap : eta ≤ gap / (2 * nu * A) := min_le_right _ _
  have hscaled : eta * (2 * nu * A) ≤ gap :=
    (le_div_iff₀ hden_pos).mp heta_gap
  refine ⟨eta, heta_pos, heta_lt_one, ?_⟩
  dsimp [gap] at hgap_pos hscaled
  nlinarith

theorem exists_parameters (ν : ℝ) (hν : 2 < ν) : Nonempty (Parameters ν) := by
  obtain ⟨theta, A, B, C, htheta, hthetaA, hAB, hB, hgap, hC, hBinv, hBC, hCtheta⟩ :=
    exists_rational_parameters ν hν
  obtain ⟨eta, heta, heta1, hgapeta⟩ := exists_eta_preserving_exponent_gap
    ν theta A hν (lt_trans htheta hthetaA) hgap
  exact ⟨⟨theta, A, B, C, eta, htheta, hthetaA, hAB, hB, hgap, hC,
    hBinv, hBC, hCtheta, heta, heta1, hgapeta⟩⟩

namespace Parameters

variable {ν : ℝ} (p : Parameters ν)

theorem A_pos : 0 < (p.A : ℝ) := lt_trans p.theta_pos p.theta_lt_A

theorem B_pos : 0 < (p.B : ℝ) := lt_trans p.A_pos p.A_lt_B

theorem C_pos : 0 < (p.C : ℝ) := lt_trans zero_lt_one p.one_lt_C

theorem A_lt_one : (p.A : ℝ) < 1 := lt_trans p.A_lt_B p.B_lt_one

theorem theta_lt_one : (p.theta : ℝ) < 1 := lt_trans p.theta_lt_A p.A_lt_one

theorem CB_lt_one : (p.C : ℝ) * p.B < 1 := by
  have h := (lt_div_iff₀ p.C_pos).mp p.B_lt_inv_C
  simpa only [mul_comm] using h

theorem one_lt_C_theta_div_B : 1 < (p.C : ℝ) * p.theta / p.B := by
  apply (lt_div_iff₀ p.B_pos).2
  simpa using p.B_lt_C_theta

theorem one_lt_B_div_A : 1 < (p.B : ℝ) / p.A := by
  apply (lt_div_iff₀ p.A_pos).2
  simpa using p.A_lt_B

end Parameters

end PiExponent

end OAI

-- Adapted from openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a.

namespace OAI

open Filter Topology

namespace PiExponent

 theorem tendsto_nat_add_one_div_pow {r : ℝ} (hr : 1 < r) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) / r ^ n) atTop (𝓝 0) := by
  have h₁ := tendsto_pow_const_div_const_pow_of_one_lt 1 hr
  have h₀ := tendsto_pow_const_div_const_pow_of_one_lt 0 hr
  simpa only [pow_one, pow_zero, ← add_div, zero_add] using h₁.add h₀

 theorem tendsto_pow_div_nat_add_one {r : ℝ} (hr : 1 < r) :
    Tendsto (fun n : ℕ => r ^ n / ((n : ℝ) + 1)) atTop atTop := by
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < ((n : ℝ) + 1) / r ^ n :=
    Filter.Eventually.of_forall fun n =>
      div_pos (by positivity) (pow_pos (zero_lt_one.trans hr) n)
  have hwithin : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / r ^ n)
      atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_nat_add_one_div_pow hr, hpos⟩
  have hinv := hwithin.inv_tendsto_nhdsGT_zero
  change Tendsto (fun n : ℕ => (((n : ℝ) + 1) / r ^ n)⁻¹) atTop atTop at hinv
  simpa only [inv_div] using hinv

end PiExponent

end OAI

-- Adapted from openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a.

namespace OAI

noncomputable section

open Filter
open scoped Topology

namespace PiExponent

theorem dimensionK_le (C : ℝ) (hC : 0 ≤ C) (m : ℕ) :
    (dimensionK C m : ℝ) ≤ C ^ m :=
  Nat.floor_le (pow_nonneg hC m)

theorem dimensionK_one_le (C : ℝ) (hC : 1 ≤ C) (m : ℕ) :
    1 ≤ dimensionK C m := by
  exact (Nat.one_le_floor_iff _).2 (one_le_pow₀ hC)

theorem dimensionW_pos (B : ℝ) (hB : 0 < B) (m : ℕ) :
    0 < dimensionW B m := by
  exact inv_pos.mpr (pow_pos hB m)

theorem dimensionV_pos (theta B C : ℝ) (htheta : 0 < theta)
    (hB : 0 < B) (hC : 1 ≤ C) (m : ℕ) :
    0 < dimensionV theta B C m := by
  have hK : 0 < (dimensionK C m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (dimensionK_one_le C hC m))
  exact mul_pos (mul_pos (mul_pos (by norm_num) hK) (pow_pos htheta m))
    (dimensionW_pos B hB m)

theorem dimension_volume (theta B C : ℝ) (htheta : 0 < theta)
    (hB : 0 < B) (hC : 1 ≤ C) (m : ℕ) :
    (dimensionK C m : ℝ) * (dimensionW B m / dimensionV theta B C m) *
      theta ^ m = 1 / 2 := by
  have hK : (dimensionK C m : ℝ) ≠ 0 := by
    exact ne_of_gt (by exact_mod_cast
      (lt_of_lt_of_le Nat.zero_lt_one (dimensionK_one_le C hC m)))
  have ht : theta ^ m ≠ 0 := ne_of_gt (pow_pos htheta m)
  have hw : dimensionW B m ≠ 0 := ne_of_gt (dimensionW_pos B hB m)
  unfold dimensionV
  field_simp

theorem dimensionK_div_W_le (B C : ℝ) (hB : 0 < B) (hC : 0 ≤ C) (m : ℕ) :
    (dimensionK C m : ℝ) / dimensionW B m ≤ (C * B) ^ m := by
  rw [dimensionW, div_inv_eq_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (dimensionK_le C hC m) (pow_pos hB m).le

theorem dimensionV_geometric_lower (theta B C : ℝ) (htheta : 0 < theta)
    (hB : 0 < B) (m : ℕ) (hlarge : 2 ≤ C ^ m) :
    (C * theta / B) ^ m ≤ dimensionV theta B C m := by
  have hfloor : C ^ m < (dimensionK C m : ℝ) + 1 := Nat.lt_floor_add_one _
  have hK : C ^ m ≤ 2 * (dimensionK C m : ℝ) := by linarith
  rw [div_pow, mul_pow, div_eq_mul_inv]
  unfold dimensionV dimensionW
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hK (pow_pos htheta m).le)
    (inv_pos.mpr (pow_pos hB m)).le

theorem dimension_volume_lt_one (theta C : ℝ) (htheta : 0 < theta)
    (hC : 0 ≤ C) (hsmall : C * theta < 1) (m : ℕ) (hm : 1 ≤ m) :
    (dimensionK C m : ℝ) * theta ^ m < 1 := by
  calc
    (dimensionK C m : ℝ) * theta ^ m ≤ C ^ m * theta ^ m :=
      mul_le_mul_of_nonneg_right (dimensionK_le C hC m) (pow_pos htheta m).le
    _ = (C * theta) ^ m := (mul_pow _ _ _).symm
    _ < 1 := pow_lt_one₀ (mul_nonneg hC htheta.le) hsmall (by omega)

theorem dimension_error_le (theta B C a b : ℝ) (htheta : 0 < theta)
    (hB : 0 < B) (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (m : ℕ) (hlarge : 2 ≤ C ^ m) :
    (a * (m : ℝ) + b) / dimensionV theta B C m +
        100 * (dimensionK C m : ℝ) / dimensionW B m ≤
      (a * (m : ℝ) + b) / (C * theta / B) ^ m + 100 * (C * B) ^ m := by
  have hr : 0 < (C * theta / B) ^ m := by
    have hCp : 0 < C := by
      by_contra hn
      have hz : C = 0 := le_antisymm (le_of_not_gt hn) hC
      subst C
      rcases m with _ | m <;> norm_num at hlarge
    positivity
  apply add_le_add
  · exact div_le_div_of_nonneg_left (by positivity) hr
      (dimensionV_geometric_lower theta B C htheta hB m hlarge)
  · rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (dimensionK_div_W_le B C hB hC m) (by norm_num)

theorem dimension_collision_identity (theta A B C eta : ℝ)
    (htheta : 0 < theta) (hA : 0 < A) (hB : 0 < B) (hC : 1 ≤ C) (m : ℕ) :
    eta ^ 2 * (dimensionK C m : ℝ) * theta ^ m /
        (((m : ℝ) + 1) * dimensionV theta B C m * A ^ m) =
      eta ^ 2 * (B / A) ^ m / (2 * ((m : ℝ) + 1)) := by
  have hK : (dimensionK C m : ℝ) ≠ 0 := by
    exact ne_of_gt (by exact_mod_cast
      (lt_of_lt_of_le Nat.zero_lt_one (dimensionK_one_le C hC m)))
  have ht : theta ^ m ≠ 0 := ne_of_gt (pow_pos htheta m)
  have hA' : A ^ m ≠ 0 := ne_of_gt (pow_pos hA m)
  have hB' : B ^ m ≠ 0 := ne_of_gt (pow_pos hB m)
  have hm : (m : ℝ) + 1 ≠ 0 := by positivity
  unfold dimensionV dimensionW
  rw [div_pow]
  field_simp

theorem tendsto_dimension_error_majorant (theta B C a b : ℝ)
    (hB : 0 < B) (hC : 0 < C) (hsmall : C * B < 1)
    (hlarge : 1 < C * theta / B) :
    Tendsto (fun m : ℕ => (a * (m : ℝ) + b) / (C * theta / B) ^ m +
      100 * (C * B) ^ m) atTop (𝓝 0) := by
  have h₁ := tendsto_pow_const_div_const_pow_of_one_lt 1 hlarge
  have h₀ := tendsto_pow_const_div_const_pow_of_one_lt 0 hlarge
  have hlin : Tendsto (fun m : ℕ => (a * (m : ℝ) + b) /
      (C * theta / B) ^ m) atTop (𝓝 0) := by
    convert (h₁.const_mul a).add (h₀.const_mul b) using 1
    · ext m
      simp only [pow_one, pow_zero]
      ring
    · simp
  have hgeom := tendsto_pow_atTop_nhds_zero_of_lt_one (mul_pos hC hB).le hsmall
  simpa only [mul_zero, add_zero] using hlin.add (hgeom.const_mul 100)

theorem tendsto_dimension_collision (A B eta : ℝ)
    (hratio : 1 < B / A) (heta : 0 < eta) :
    Tendsto (fun m : ℕ => eta ^ 2 * (B / A) ^ m /
      (2 * ((m : ℝ) + 1))) atTop atTop := by
  have h := (tendsto_pow_div_nat_add_one hratio).const_mul_atTop
    (show 0 < eta ^ 2 / 2 by positivity)
  convert h using 1
  ext m
  rw [mul_div_mul_comm]

theorem exists_dimension_margin (theta A B C eta a b epsilon target : ℝ)
    (htheta : 0 < theta) (hB : 0 < B) (hC : 1 < C)
    (hsmall : C * B < 1) (hlarge : 1 < C * theta / B)
    (hratio : 1 < B / A) (heta : 0 < eta)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hepsilon : 0 < epsilon) :
    ∃ m : ℕ, 1 ≤ m ∧
      (a * (m : ℝ) + b) / dimensionV theta B C m +
        100 * (dimensionK C m : ℝ) / dimensionW B m < epsilon ∧
      target < eta ^ 2 * (B / A) ^ m / (2 * ((m : ℝ) + 1)) := by
  have herrors := (tendsto_dimension_error_majorant theta B C a b hB
    (zero_lt_one.trans hC) hsmall hlarge).eventually (gt_mem_nhds hepsilon)
  have hcollision := (tendsto_dimension_collision A B eta hratio heta).eventually
    (eventually_gt_atTop target)
  have hfloor := (tendsto_pow_atTop_atTop_of_one_lt hC).eventually
    (eventually_ge_atTop (2 : ℝ))
  have hgood : ∀ᶠ m : ℕ in atTop, 1 ≤ m ∧
      (a * (m : ℝ) + b) / dimensionV theta B C m +
        100 * (dimensionK C m : ℝ) / dimensionW B m < epsilon ∧
      target < eta ^ 2 * (B / A) ^ m / (2 * ((m : ℝ) + 1)) := by
    filter_upwards [herrors, hcollision, hfloor, eventually_ge_atTop 1]
      with m herror hcollision hfloor hm
    exact ⟨hm, (dimension_error_le theta B C a b htheta hB
      (zero_lt_one.trans hC).le ha hb m hfloor).trans_lt herror, hcollision⟩
  exact hgood.exists

end PiExponent

end

end OAI

-- Adapted from openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a.

namespace OAI

namespace PiExponent

theorem exists_small_rational_sigma
    (m : ℕ) (α β θ : ℝ) (hα : α < 1) (hβ : β < 1) (hθ : θ < 1) :
    ∃ σ : ℚ, 0 < (σ : ℝ) ∧
      (1 + 3 * (σ : ℝ)) ^ (m + 1) * α < 1 ∧
      (1 + 3 * (σ : ℝ)) ^ m * β < 1 ∧
      (1 + (σ : ℝ)) * θ < 1 := by
  have hopenα : IsOpen {s : ℝ | (1 + 3 * s) ^ (m + 1) * α < 1} :=
    isOpen_lt (by fun_prop) continuous_const
  have hopenβ : IsOpen {s : ℝ | (1 + 3 * s) ^ m * β < 1} :=
    isOpen_lt (by fun_prop) continuous_const
  have hopenθ : IsOpen {s : ℝ | (1 + s) * θ < 1} :=
    isOpen_lt (by fun_prop) continuous_const
  have hopen : IsOpen {s : ℝ |
      (1 + 3 * s) ^ (m + 1) * α < 1 ∧
      (1 + 3 * s) ^ m * β < 1 ∧
      (1 + s) * θ < 1} :=
    hopenα.inter (hopenβ.inter hopenθ)
  have hzero : (0 : ℝ) ∈ {s : ℝ |
      (1 + 3 * s) ^ (m + 1) * α < 1 ∧
      (1 + 3 * s) ^ m * β < 1 ∧
      (1 + s) * θ < 1} := by
    simpa using And.intro hα (And.intro hβ hθ)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen 0 hzero
  obtain ⟨σ, hσ0, hσε⟩ := exists_rat_btwn hε
  have hσmem : (σ : ℝ) ∈ Metric.ball 0 ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hσ0]
    exact hσε
  exact ⟨σ, hσ0, hball hσmem⟩

end PiExponent

end OAI

-- Adapted from openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a.

namespace OAI

namespace PiExponent

theorem exists_large_log_approximation
    (nu X : ℝ) (hnu : 0 < nu)
    (hbad : ∀ Q : ℕ, ∃ p : ℤ, ∃ q : ℕ,
      Q ≤ q ∧ |Real.pi - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu)) :
    ∃ p : ℤ, ∃ q : ℕ,
      2 ≤ q ∧ X < Real.log q ∧ p ≠ 0 ∧
        |Real.pi - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp X)
  obtain ⟨p, q, hq, happrox⟩ := hbad (max 2 N)
  have hq2 : 2 ≤ q := le_trans (le_max_left _ _) hq
  have hNq : N ≤ q := le_trans (le_max_right _ _) hq
  have hexp : Real.exp X < (q : ℝ) := lt_of_lt_of_le hN (by exact_mod_cast hNq)
  have hlog : X < Real.log q := by
    simpa using Real.log_lt_log (Real.exp_pos X) hexp
  have hp : p ≠ 0 := by
    intro hp0
    have hpow : (q : ℝ) ^ (-nu) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (by omega : 1 ≤ q))
        (by linarith)
    have hpi : Real.pi ≤ (q : ℝ) ^ (-nu) := by
      simpa [hp0, abs_of_pos Real.pi_pos] using happrox
    have hpi2 := Real.pi_gt_three
    linarith
  exact ⟨p, q, hq2, hlog, hp, happrox⟩

end PiExponent

end OAI

-- Adapted from openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a.

namespace OAI

namespace PiExponent

theorem exists_successive_approximations
    (nu : ℝ) (hnu : 0 < nu)
    (hbad : ∀ Q : ℕ, ∃ p : ℤ, ∃ q : ℕ,
      Q ≤ q ∧ |Real.pi - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu))
    (T : List ℝ → ℝ) :
    ∃ p : ℕ → ℤ, ∃ q : ℕ → ℕ, ∀ n,
      2 ≤ q n ∧ p n ≠ 0 ∧
      |Real.pi - (p n : ℝ) / q n| ≤ (q n : ℝ) ^ (-nu) ∧
      1 ≤ Nat.ceil (Real.log (q n)) ∧
      T (((List.range n).reverse).map
        (fun i => ((Nat.ceil (Real.log (q i))) : ℝ))) <
          ((Nat.ceil (Real.log (q n))) : ℝ) := by
  classical
  let wt : ℤ × ℕ → ℝ := fun a => (Nat.ceil (Real.log a.2) : ℝ)
  let Good : ℤ × ℕ → Prop := fun a =>
    2 ≤ a.2 ∧ a.1 ≠ 0 ∧
    |Real.pi - (a.1 : ℝ) / a.2| ≤ (a.2 : ℝ) ^ (-nu) ∧
    1 ≤ Nat.ceil (Real.log a.2)
  have hex (L : List (ℤ × ℕ)) :
      ∃ a : ℤ × ℕ, Good a ∧ T (L.map wt) < wt a := by
    obtain ⟨p, q, hq, hlog, hp, happ⟩ :=
      exists_large_log_approximation nu (max 1 (T (L.map wt))) hnu hbad
    have hceil : Real.log q ≤ (Nat.ceil (Real.log q) : ℝ) := Nat.le_ceil _
    have hone : 1 < (Nat.ceil (Real.log q) : ℝ) :=
      lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le hlog hceil)
    have hnat : 1 ≤ Nat.ceil (Real.log q) := by exact_mod_cast le_of_lt hone
    exact ⟨(p, q), ⟨hq, hp, happ, hnat⟩,
      lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le hlog hceil)⟩
  let next : List (ℤ × ℕ) → ℤ × ℕ := fun L => (hex L).choose
  have hnext (L : List (ℤ × ℕ)) : Good (next L) ∧ T (L.map wt) < wt (next L) :=
    (hex L).choose_spec
  let hist : ℕ → List (ℤ × ℕ) := Nat.rec [] (fun _ L => next L :: L)
  let a : ℕ → ℤ × ℕ := fun n => next (hist n)
  have hhist (n : ℕ) : hist n = (List.range n).reverse.map a := by
    induction n with
    | zero => rfl
    | succ n ih =>
      change a n :: hist n = (List.range (n + 1)).reverse.map a
      rw [ih]
      simp [List.range_succ, List.reverse_append]
  refine ⟨fun n => (a n).1, fun n => (a n).2, fun n => ?_⟩
  have hgood : Good (a n) := (hnext (hist n)).1
  refine ⟨hgood.1, hgood.2.1, hgood.2.2.1, hgood.2.2.2, ?_⟩
  have hbound := (hnext (hist n)).2
  have hmap : (hist n).map wt = (List.range n).reverse.map (wt ∘ a) := by
    rw [hhist, List.map_map]
  rw [hmap] at hbound
  exact hbound

theorem logarithmic_weight_bounds (q : ℕ) (hq : 1 ≤ q) :
    Real.log q ≤ (Nat.ceil (Real.log q) : ℝ) ∧
      (Nat.ceil (Real.log q) : ℝ) < Real.log q + 1 := by
  exact ⟨Nat.le_ceil _, Nat.ceil_lt_add_one (Real.log_nonneg (by exact_mod_cast hq))⟩

theorem approximation_error_at_logarithmic_weight
    (nu : ℝ) (hnu : 0 < nu) (p : ℤ) (q : ℕ) (hq : 1 ≤ q)
    (herror : |Real.pi - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu)) :
    |Real.pi - (p : ℝ) / q| ≤
      Real.exp (nu - nu * (Nat.ceil (Real.log q) : ℝ)) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hw := (logarithmic_weight_bounds q hq).2
  calc
    _ ≤ (q : ℝ) ^ (-nu) := herror
    _ = Real.exp (Real.log q * (-nu)) := Real.rpow_def_of_pos hqpos _
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

noncomputable def normalizedLogWeights (q : ℕ → ℕ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => (Nat.ceil (Real.log (q n)) : ℝ)

@[simp] theorem normalizedLogWeights_zero (q : ℕ → ℕ) :
    normalizedLogWeights q 0 = 1 := rfl

@[simp] theorem normalizedLogWeights_succ (q : ℕ → ℕ) (n : ℕ) :
    normalizedLogWeights q (n + 1) = (Nat.ceil (Real.log (q n)) : ℝ) := rfl

theorem reverse_logWeights_prod (q : ℕ → ℕ) (n : ℕ) :
    (((List.range n).reverse).map
      (fun i => (Nat.ceil (Real.log (q i)) : ℝ))).prod =
      ∏ j ∈ Finset.range (n + 1), normalizedLogWeights q j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.reverse_append]
    simp only [List.reverse_singleton, List.map_append, List.map_singleton,
      List.prod_append, List.prod_cons, List.prod_nil, mul_one]
    rw [Finset.prod_range_succ, ih, normalizedLogWeights_succ]
    exact mul_comm _ _

theorem exists_normalized_selection_of_selector
    (nu X D : ℝ)
    (hselect : ∀ T : List ℝ → ℝ,
      ∃ p : ℕ → ℤ, ∃ q : ℕ → ℕ, ∀ n,
        2 ≤ q n ∧ p n ≠ 0 ∧
        |Real.pi - (p n : ℝ) / q n| ≤ (q n : ℝ) ^ (-nu) ∧
        1 ≤ Nat.ceil (Real.log (q n)) ∧
        T (((List.range n).reverse).map
          (fun i => ((Nat.ceil (Real.log (q i))) : ℝ))) <
            ((Nat.ceil (Real.log (q n))) : ℝ)) :
    ∃ p : ℕ → ℤ, ∃ q : ℕ → ℕ, ∃ x : ℕ → ℝ,
      x 0 = 1 ∧
      (∀ n, x (n + 1) = (Nat.ceil (Real.log (q n)) : ℝ)) ∧
      (∀ n, 2 ≤ q n ∧ p n ≠ 0 ∧
        |Real.pi - (p n : ℝ) / q n| ≤ (q n : ℝ) ^ (-nu) ∧
        1 ≤ Nat.ceil (Real.log (q n)) ∧ X < x (n + 1)) ∧
      (∀ i, 1 ≤ x i) ∧
      (∀ i, 0 < i → D * (∏ j ∈ Finset.range i, x j) < x i) := by
  obtain ⟨p, q, h⟩ := hselect (fun L => max X (D * L.prod))
  refine ⟨p, q, normalizedLogWeights q, rfl, fun _ => rfl, ?_, ?_, ?_⟩
  · intro n
    refine ⟨(h n).1, (h n).2.1, (h n).2.2.1, (h n).2.2.2.1, ?_⟩
    exact lt_of_le_of_lt (le_max_left _ _) (h n).2.2.2.2
  · intro i
    cases i with
    | zero => simp
    | succ n =>
      change (1 : ℝ) ≤ (Nat.ceil (Real.log (q n)) : ℝ)
      exact_mod_cast (h n).2.2.2.1
  · intro i hi
    cases i with
    | zero => omega
    | succ n =>
      have hprod := lt_of_le_of_lt (le_max_right _ _) (h n).2.2.2.2
      rw [reverse_logWeights_prod] at hprod
      exact hprod

theorem exists_normalized_successive_approximations
    (nu X D : ℝ) (hnu : 0 < nu)
    (hbad : ∀ Q : ℕ, ∃ p : ℤ, ∃ q : ℕ,
      Q ≤ q ∧ |Real.pi - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu)) :
    ∃ p : ℕ → ℤ, ∃ q : ℕ → ℕ, ∃ x : ℕ → ℝ,
      x 0 = 1 ∧
      (∀ n, x (n + 1) = (Nat.ceil (Real.log (q n)) : ℝ)) ∧
      (∀ n, 2 ≤ q n ∧ p n ≠ 0 ∧
        |Real.pi - (p n : ℝ) / q n| ≤ (q n : ℝ) ^ (-nu) ∧
        1 ≤ Nat.ceil (Real.log (q n)) ∧ X < x (n + 1)) ∧
      (∀ i, 1 ≤ x i) ∧
      (∀ i, 0 < i → D * (∏ j ∈ Finset.range i, x j) < x i) := by
  exact exists_normalized_selection_of_selector nu X D
    (exists_successive_approximations nu hnu hbad)

end PiExponent

end OAI

-- Adapted from openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a.

namespace OAI

namespace PiExponent

theorem exists_weight_error_margin
    (m : ℕ) (Λ S ε : ℝ) (_hΛ : 0 < Λ) (_hS : 0 ≤ S) (hε : 0 < ε) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ wstar : ℝ, X < wstar →
      Λ * (m : ℝ) / wstar + S / wstar < ε := by
  refine ⟨max 1 ((Λ * (m : ℝ) + S) / ε), le_max_left _ _, ?_⟩
  intro wstar hwstar
  have hwpos : 0 < wstar :=
    lt_of_lt_of_le zero_lt_one (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hwstar))
  have hquot : (Λ * (m : ℝ) + S) / ε < wstar :=
    lt_of_le_of_lt (le_max_right _ _) hwstar
  have hnum : Λ * (m : ℝ) + S < ε * wstar := by
    simpa only [mul_comm] using (div_lt_iff₀ hε).mp hquot
  rw [← add_div]
  exact (div_lt_iff₀ hwpos).mpr hnum

theorem reciprocal_sum_le_common_bound
    (m : ℕ) (w : Fin m → ℝ) (wstar : ℝ) (hwpos : 0 < wstar)
    (hw : ∀ i, wstar ≤ w i) :
    (∑ i : Fin m, 1 / w i) ≤ (m : ℝ) / wstar := by
  calc
    (∑ i : Fin m, 1 / w i) ≤ ∑ _i : Fin m, 1 / wstar := by
      apply Finset.sum_le_sum
      intro i _
      exact one_div_le_one_div_of_le hwpos (hw i)
    _ = (m : ℝ) / wstar := by simp [div_eq_mul_inv]

theorem exists_uniform_weight_error_margin
    (m : ℕ) (Λ S ε : ℝ) (hΛ : 0 < Λ) (hS : 0 ≤ S) (hε : 0 < ε) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ (wstar : ℝ) (w : Fin m → ℝ),
      X < wstar → (∀ i, wstar ≤ w i) →
      Λ * (∑ i : Fin m, 1 / w i) + S / wstar < ε := by
  obtain ⟨X, hX, hmargin⟩ := exists_weight_error_margin m Λ S ε hΛ hS hε
  refine ⟨X, hX, ?_⟩
  intro wstar w hwstar hw
  have hwpos : 0 < wstar := lt_trans zero_lt_one (lt_of_le_of_lt hX hwstar)
  have hsum := reciprocal_sum_le_common_bound m w wstar hwpos hw
  have hscaled := mul_le_mul_of_nonneg_left hsum hΛ.le
  have hsmall := hmargin wstar hwstar
  calc
    Λ * (∑ i : Fin m, 1 / w i) + S / wstar
        ≤ Λ * ((m : ℝ) / wstar) + S / wstar := add_le_add hscaled le_rfl
    _ = Λ * (m : ℝ) / wstar + S / wstar := by rw [mul_div_assoc]
    _ < ε := hsmall

theorem exists_minimum_weight
    (m : ℕ) (hm : 1 ≤ m) (w : Fin m → ℝ) (X : ℝ)
    (hX : ∀ i, X < w i) :
    ∃ wstar : ℝ, X < wstar ∧ (∀ i, wstar ≤ w i) ∧
      ∃ i, wstar = w i := by
  have hne : (Finset.univ : Finset (Fin m)).Nonempty :=
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ w hne
  exact ⟨w i, hX i, (fun j => hi j (Finset.mem_univ j)), i, rfl⟩

end PiExponent

end OAI

namespace OAI.PiExponent
theorem weightErrorCoefficient_nonneg (nu theta : ℝ) (K : ℕ)
    (hnu : 0 < nu) (htheta : 0 < theta) (hK : 1 ≤ K) :
    0 ≤ weightErrorCoefficient nu theta K := by
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have h2K : 0 ≤ Real.log (2 * (K : ℝ)) := Real.log_nonneg (by linarith)
  have h200K : 0 ≤ Real.log (200 * (K : ℝ)) := Real.log_nonneg (by linarith)
  unfold weightErrorCoefficient
  linarith

theorem exists_initial_scale (nu theta epsilon : ℝ) (_htheta : 0 < theta)
    (hepsilon : 0 < epsilon) :
    ∃ F0 : ℝ, 0 < F0 ∧ 2 / theta < F0 ∧ nu / F0 < epsilon / 3 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (max (2 / theta) (3 * nu / epsilon)))
  have hF : 1 < (N : ℝ) := lt_of_le_of_lt (le_max_left _ _) hN
  have hthetaF : 2 / theta < (N : ℝ) :=
    lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hN
  have hnuF : 3 * nu / epsilon < (N : ℝ) :=
    lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hN
  refine ⟨N, by linarith, hthetaF, ?_⟩
  apply (div_lt_iff₀ (show (0 : ℝ) < N by linarith)).2
  have := (div_lt_iff₀ hepsilon).mp hnuF
  nlinarith


end OAI.PiExponent

open Filter Topology
open OAI.PiExponent

theorem solution
    (nu Lambda c : ℝ) (hnu : 2 < nu) (hLambda : 0 < Lambda) (hc : 0 < c)
    (hbad : ∀ Q : ℕ, ∃ p : ℤ, ∃ q : ℕ,
      Q ≤ q ∧ |Real.pi - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu)) :
    Nonempty (AdmissibleParameters nu Lambda c) := by
  classical
  obtain ⟨P⟩ := exists_parameters nu hnu
  let g : ℝ := nu * ((P.A : ℝ) * (1 - P.eta) - P.theta) - (1 - P.theta)
  have hg : 0 < g := P.gap_pos
  let epsilon : ℝ := min (g / 2) (1 / 2)
  have hepsilon : 0 < epsilon := lt_min (by positivity) (by norm_num)
  have hepsg : epsilon < g := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hepshalf : epsilon ≤ 1 / 2 := min_le_right _ _
  have heps3 : 0 < epsilon / 3 := by positivity
  obtain ⟨F0, hF0, hFtheta, hFmargin⟩ :=
    exists_initial_scale nu P.theta epsilon P.theta_pos hepsilon
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨m, hm, hdim, hcollision⟩ := exists_dimension_margin
    P.theta P.A P.B P.C P.eta (Lambda * F0) (2 * Real.log 2)
    (epsilon / 3) (2 / c) P.theta_pos P.B_pos P.one_lt_C
    P.CB_lt_one P.one_lt_C_theta_div_B P.one_lt_B_div_A P.eta_pos
    (mul_pos hLambda hF0).le (by positivity) heps3
  let K : ℕ := dimensionK P.C m
  let w0 : ℚ := (P.B ^ m)⁻¹
  let v0 : ℚ := 2 * (K : ℚ) * P.theta ^ m * w0
  have hK : 1 ≤ K := dimensionK_one_le P.C P.one_lt_C.le m
  have hw0eq : (w0 : ℝ) = dimensionW P.B m := by simp [w0, dimensionW]
  have hv0eq : (v0 : ℝ) = dimensionV P.theta P.B P.C m := by
    simp [v0, dimensionV, K, hw0eq]
  have hw0 : 0 < (w0 : ℝ) := by
    rw [hw0eq]
    exact dimensionW_pos P.B P.B_pos m
  have hv0 : 0 < (v0 : ℝ) := by
    rw [hv0eq]
    exact dimensionV_pos P.theta P.B P.C P.theta_pos P.B_pos P.one_lt_C.le m
  have hvolume : (K : ℝ) * ((w0 : ℝ) / v0) * (P.theta : ℝ) ^ m = 1 / 2 := by
    rw [hw0eq, hv0eq]
    exact dimension_volume P.theta P.B P.C P.theta_pos P.B_pos P.one_lt_C.le m
  have hvolume1 : (K : ℝ) * (P.theta : ℝ) ^ m < 1 :=
    dimension_volume_lt_one P.theta P.C P.theta_pos P.C_pos.le P.C_theta_lt_one m hm
  have hcollision' : 2 < c *
      (P.eta ^ 2 * (K : ℝ) * (P.theta : ℝ) ^ m /
        (((m : ℝ) + 1) * (v0 : ℝ) * (P.A : ℝ) ^ m)) := by
    rw [hv0eq]
    change 2 < c * (P.eta ^ 2 * (dimensionK (P.C : ℝ) m : ℝ) *
      (P.theta : ℝ) ^ m / (((m : ℝ) + 1) *
        dimensionV (P.theta : ℝ) P.B P.C m * (P.A : ℝ) ^ m))
    rw [dimension_collision_identity P.theta P.A P.B P.C P.eta
      P.theta_pos P.A_pos P.B_pos P.one_lt_C.le]
    have hh := (div_lt_iff₀ hc).mp hcollision
    nlinarith
  obtain ⟨sigma, hsigma, hsigmaVol, hsigmaK, hsigmaTheta⟩ :=
    exists_small_rational_sigma m (1 / 2)
      ((K : ℝ) * (P.theta : ℝ) ^ m) P.theta (by norm_num) hvolume1 P.theta_lt_one
  have hnupos : 0 < nu := by linarith
  have hS : 0 ≤ weightErrorCoefficient nu P.theta K :=
    weightErrorCoefficient_nonneg nu P.theta K hnupos P.theta_pos hK
  obtain ⟨X, hX, hXmargin⟩ := exists_uniform_weight_error_margin m Lambda
    (weightErrorCoefficient nu P.theta K) (epsilon / 3) hLambda hS heps3
  obtain ⟨p, q, x, hx0, hxlog, happ, hx1, hgrowth⟩ :=
    exists_normalized_successive_approximations nu X
      (OAI.PiExponentApprox.weightSeparationFactor m
        (interpolationSeparationConstant m sigma) w0 v0 P.theta) hnupos hbad
  obtain ⟨wstar, hwstarX, hwstarLower, hwstarAttained⟩ :=
    exists_minimum_weight m hm (fun i : Fin m => x (i.val + 1)) X
      (fun i => (happ i.val).2.2.2.2)
  have hwstar : 0 < wstar := lt_of_lt_of_le zero_lt_one (le_trans hX hwstarX.le)
  refine ⟨{
    base := P
    epsilon := epsilon
    F0 := F0
    m := m
    K := K
    w0 := w0
    v0 := v0
    sigma := sigma
    p := p
    q := q
    x := x
    wstar := wstar
    epsilon_pos := hepsilon
    epsilon_lt_gap := hepsg
    epsilon_le_half := hepshalf
    F0_pos := hF0
    F0_large := hFtheta
    initial_margin := hFmargin
    m_pos := hm
    K_eq := rfl
    K_pos := hK
    w0_eq := hw0eq
    v0_eq := hv0eq
    w0_pos := hw0
    v0_pos := hv0
    volume_eq := hvolume
    volume_lt_one := hvolume1
    dimension_margin := ?_
    collision_margin := hcollision'
    sigma_pos := hsigma
    sigma_volume := ?_
    sigma_centers := hsigmaK
    sigma_theta := hsigmaTheta
    x_zero := hx0
    x_log := hxlog
    approximations := fun n => ⟨(happ n).1, (happ n).2.1, (happ n).2.2.1⟩
    x_one_le := hx1
    weight_growth := fun i hi _ => hgrowth i hi
    wstar_pos := hwstar
    wstar_lower := hwstarLower
    wstar_attained := hwstarAttained
    weight_margin := hXmargin wstar (fun i : Fin m => x (i.val + 1))
      hwstarX hwstarLower
  }⟩
  · rw [hv0eq, hw0eq]
    exact hdim
  · rw [hvolume]
    exact hsigmaVol


#print axioms solution
