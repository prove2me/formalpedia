-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedFixedPathSlicedPerturbation_chosen_tail_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-17T10:48:44.92625+00:00
-- url     : https://prove2.me/submissions/59b4c3e1-7cd5-4b91-9cae-ac7060c259d1

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B067
import Definitions.Def_OAIE3v2B103
import Definitions.Def_OAIE3v2B105

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialParameterContinuity
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators ContDiff

theorem polynomialMassC2Budget_nonneg (N d : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ polynomialMassC2Budget N d C := by unfold polynomialMassC2Budget; positivity

theorem polynomialMassC2Budget_le_exp (N d : ℕ) {C P Q : ℝ}
    (hP : 0 ≤ P) (hC : 0 ≤ C) (hN : (N : ℝ) ≤ Real.exp P) (hCQ : C ≤ Real.exp Q) :
    polynomialMassC2Budget N d C ≤ Real.exp (2 * P + 2 * d + Q + 2) := by
  have hN1 := one_add_le_exp_succ hP hN
  have hd1 : (d : ℝ) + 1 ≤ Real.exp d := Real.add_one_le_exp _
  have hb : 1 + (N : ℝ) * d ≤ Real.exp (P + d + 1) := by
    calc
      _ ≤ (1 + (N : ℝ)) * ((d : ℝ) + 1) := by nlinarith [Nat.cast_nonneg (α := ℝ) N, Nat.cast_nonneg (α := ℝ) d]
      _ ≤ Real.exp (P + 1) * Real.exp d := by gcongr
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  calc
    _ ≤ (Real.exp (P + d + 1))^2 * Real.exp Q := by
      unfold polynomialMassC2Budget
      gcongr
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPerturbationScaleBudget
namespace OAI

section

namespace Erdos3

theorem polynomialPerturbationScale_spec {K M Q τ : ℝ}
    (hK : 0 ≤ K) (hM : 0 ≤ M) (hQ : 0 ≤ Q) (hτ : 0 < τ) (m : ℕ) :
    let t := polynomialPerturbationScale K M Q τ m
    0 < t ∧ t ≤ 1 ∧ K * (t * M) ≤ 1 / 2 ∧ t * M ≤ 1 ∧
      4 * (m : ℝ) * Real.sqrt (Q * (t * (1 + M))) ≤ τ := by
  let t := polynomialPerturbationScale K M Q τ m
  have ht : 0 < t := by dsimp [t, polynomialPerturbationScale]; positivity
  have ht1 : t ≤ 1 := min_le_left _ _
  have htK : t ≤ 1 / (2 * (1 + K) * (1 + M)) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have htQ : t ≤ τ ^ 2 / (16 * ((m : ℝ) + 1) ^ 2 * (1 + Q) * (1 + M)) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hden : t * (2 * (1 + K) * (1 + M)) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp htK
  have h2KM : 2 * K * M ≤ 2 * (1 + K) * (1 + M) := by nlinarith
  have hMden : M ≤ 2 * (1 + K) * (1 + M) := by nlinarith [mul_nonneg hK hM]
  have hsmall : K * (t * M) ≤ 1 / 2 := by
    have hh := (mul_le_mul_of_nonneg_left h2KM ht.le).trans hden
    nlinarith
  have hsecond : t * M ≤ 1 := (mul_le_mul_of_nonneg_left hMden ht.le).trans hden
  refine ⟨ht, ht1, hsmall, hsecond, ?_⟩
  have hdenQ : t * (16 * ((m : ℝ) + 1) ^ 2 * (1 + Q) * (1 + M)) ≤ τ ^ 2 :=
    (le_div_iff₀ (by positivity)).mp htQ
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hm2 : (m : ℝ) ^ 2 ≤ ((m : ℝ) + 1) ^ 2 := by nlinarith
  have hpoly : 16 * (m : ℝ) ^ 2 * Q * (1 + M) ≤
      16 * ((m : ℝ) + 1) ^ 2 * (1 + Q) * (1 + M) := by
    gcongr
    linarith
  have hb := (mul_le_mul_of_nonneg_left hpoly ht.le).trans hdenQ
  have hroot := Real.sq_sqrt (show 0 ≤ Q * (t * (1 + M)) by positivity)
  have hroot0 := Real.sqrt_nonneg (Q * (t * (1 + M)))
  have hsquare : (4 * (m : ℝ) * Real.sqrt (Q * (t * (1 + M)))) ^ 2 ≤ τ ^ 2 := by
    calc
      _ = t * (16 * (m : ℝ) ^ 2 * Q * (1 + M)) := by
        rw [mul_pow, mul_pow, hroot]
        ring
      _ ≤ _ := hb
  nlinarith [mul_nonneg (show 0 ≤ 4 * (m : ℝ) by positivity) hroot0]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.JointBooleanStability
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff NNReal

theorem slicedPrincipalComparisonBudget_nonneg (N m : ℕ) {C A r κ : ℝ}
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hr : 0 < r) (hκ : 0 < κ) :
    0 ≤ slicedPrincipalComparisonBudget N m C A r κ := by
  unfold slicedPrincipalComparisonBudget
  positivity

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff NNReal

theorem slicedPrincipalBoundaryRadius_spec (N : ℕ) {η : ℝ} (hη : 0 < η) :
    let r := slicedPrincipalBoundaryRadius N η
    0 < r ∧ r ≤ 1 / 4 ∧ 8 * N * r ≤ η / 2 := by
  let r := slicedPrincipalBoundaryRadius N η
  have hr : 0 < r := by dsimp [r, slicedPrincipalBoundaryRadius]; positivity
  have hr1 : r ≤ 1 / 4 := min_le_left _ _
  have he : r ≤ η / (16 * ((N : ℝ) + 1)) := min_le_right _ _
  have hh := (le_div_iff₀ (by positivity : 0 < 16 * ((N : ℝ) + 1))).mp he
  refine ⟨hr, hr1, ?_⟩
  nlinarith [Nat.cast_nonneg (α := ℝ) N]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPerturbationScaleLowerBound
namespace OAI

section

namespace Erdos3

theorem polynomialPerturbationScale_inverse_le_exp {K M Q τ P : ℝ}
    (hK : 0 ≤ K) (hM : 0 ≤ M) (hQ : 0 ≤ Q) (hτ : 0 < τ) (hP : 0 ≤ P)
    (m : ℕ) (hm : (m : ℝ) ≤ Real.exp P)
    (hKP : K ≤ Real.exp P) (hMP : M ≤ Real.exp P) (hQP : Q ≤ Real.exp P)
    (hτP : τ⁻¹ ≤ Real.exp P) :
    (polynomialPerturbationScale K M Q τ m)⁻¹ ≤ Real.exp (6*P+8) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h16 : (16 : ℝ) ≤ Real.exp 4 := by
    calc
      _ = (2 : ℝ)^4 := by norm_num
      _ ≤ (Real.exp 1)^4 := pow_le_pow_left₀ (by norm_num) h2 _
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hm1 : (m : ℝ)+1 ≤ Real.exp (P+1) := by
    simpa only [add_comm] using one_add_le_exp_succ hP hm
  have hK1 := one_add_le_exp_succ hP hKP
  have hM1 := one_add_le_exp_succ hP hMP
  have hQ1 := one_add_le_exp_succ hP hQP
  apply inv_min_le_of_inv_le
  · simpa only [inv_one] using Real.one_le_exp_iff.mpr (by positivity : 0 ≤ 6*P+8)
  · apply inv_min_le_of_inv_le
    · calc
        (1/(2*(1+K)*(1+M)))⁻¹ = 2*(1+K)*(1+M) := by simp
        _ ≤ Real.exp 1*Real.exp (P+1)*Real.exp (P+1) := by gcongr
        _ = Real.exp (2*P+3) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
        _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
    · calc
        (τ^2/(16*((m : ℝ)+1)^2*(1+Q)*(1+M)))⁻¹ =
            16*((m : ℝ)+1)^2*(1+Q)*(1+M)*(τ⁻¹)^2 := by
              rw [inv_div, div_eq_mul_inv, inv_pow]
        _ ≤ Real.exp 4*(Real.exp (P+1))^2*Real.exp (P+1)*Real.exp (P+1)*(Real.exp P)^2 := by
          gcongr
        _ = _ := by
          rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add,
            ← Real.exp_add, ← Real.exp_add]
          congr 1
          ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SlicedToleranceMonotonicity
namespace OAI

section

namespace Erdos3

theorem slicedPrincipalBoundaryRadius_antitone {N N' : ℕ} (hN : N ≤ N')
    {η : ℝ} (hη : 0 ≤ η) :
    slicedPrincipalBoundaryRadius N' η ≤ slicedPrincipalBoundaryRadius N η := by
  unfold slicedPrincipalBoundaryRadius
  apply min_le_min le_rfl
  apply div_le_div_of_nonneg_left hη (by positivity)
  gcongr

theorem slicedPrincipalComparisonBudget_mono {N N' m : ℕ} (hN : N ≤ N')
    {C A r r' κ κ' : ℝ} (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hr' : 0 < r') (hr : r' ≤ r) (hκ' : 0 < κ') (hκ : κ' ≤ κ) :
    slicedPrincipalComparisonBudget N m C A r κ ≤
      slicedPrincipalComparisonBudget N' m C A r' κ' := by
  have hri : 0 < r := hr'.trans_le hr
  have hκi : 0 < κ := hκ'.trans_le hκ
  have hi : κ⁻¹ ≤ κ'⁻¹ := inv_anti₀ hκ' hκ
  unfold slicedPrincipalComparisonBudget
  gcongr

theorem polynomialPerturbationScale_antitone {K K' M Q Q' τ : ℝ} {O O' : ℕ}
    (hK : 0 ≤ K) (hKK : K ≤ K') (hM : 0 ≤ M) (hQ : 0 ≤ Q) (hQQ : Q ≤ Q')
    (hO : O ≤ O') :
    polynomialPerturbationScale K' M Q' τ O' ≤ polynomialPerturbationScale K M Q τ O := by
  unfold polynomialPerturbationScale
  apply min_le_min le_rfl
  apply min_le_min
  · apply div_le_div_of_nonneg_left zero_le_one (by positivity)
    gcongr
  · apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    gcongr

theorem slicedPrincipalC2Tolerance_antitone {N N' O O' m : ℕ} (hN : N ≤ N') (hO : O ≤ O')
    {C a δ A η : ℝ} (hC : 0 ≤ C) (ha : 0 < a) (hδ : 0 < δ) (hA : 0 ≤ A) (hη : 0 < η) :
    slicedPrincipalC2Tolerance N' O' m C a δ A η ≤ slicedPrincipalC2Tolerance N O m C a δ A η := by
  let r := slicedPrincipalBoundaryRadius N η
  let r' := slicedPrincipalBoundaryRadius N' η
  have hr : 0 < r := (slicedPrincipalBoundaryRadius_spec N hη).1
  have hr' : 0 < r' := (slicedPrincipalBoundaryRadius_spec N' hη).1
  have hrr : r' ≤ r := slicedPrincipalBoundaryRadius_antitone hN hη.le
  let κ := a * δ * (δ * r) ^ m
  let κ' := a * δ * (δ * r') ^ m
  have hκ : 0 < κ := mul_pos (mul_pos ha hδ) (pow_pos (mul_pos hδ hr) _)
  have hκ' : 0 < κ' := mul_pos (mul_pos ha hδ) (pow_pos (mul_pos hδ hr') _)
  have hκκ : κ' ≤ κ := by
    dsimp only [κ, κ']
    gcongr
  exact polynomialPerturbationScale_antitone (inv_nonneg.mpr hκ.le) (inv_anti₀ hκ' hκκ)
    zero_le_one (slicedPrincipalComparisonBudget_nonneg N m hC hA hr hκ)
    (slicedPrincipalComparisonBudget_mono hN hC hA hr' hrr hκ' hκκ) hO

theorem slicedPrincipalC2Tolerance_pos_le_one (N O m : ℕ)
    {C a δ A η : ℝ} (hC : 0 ≤ C) (ha : 0 < a) (hδ : 0 < δ) (hA : 0 ≤ A) (hη : 0 < η) :
    0 < slicedPrincipalC2Tolerance N O m C a δ A η ∧
      slicedPrincipalC2Tolerance N O m C a δ A η ≤ 1 := by
  let r := slicedPrincipalBoundaryRadius N η
  have hr : 0 < r := (slicedPrincipalBoundaryRadius_spec N hη).1
  have hκ : 0 < a * δ * (δ * r) ^ m := mul_pos (mul_pos ha hδ) (pow_pos (mul_pos hδ hr) _)
  have ht := polynomialPerturbationScale_spec (inv_nonneg.mpr hκ.le) zero_le_one
    (slicedPrincipalComparisonBudget_nonneg N m hC hA hr hκ) (half_pos hη) O
  exact ⟨ht.1, ht.2.1⟩

theorem slicedEndpointUniformScale_spec (N O m : ℕ)
    {a δ A η : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hA : 0 ≤ A) (hη : 0 < η) :
    let t := slicedPolynomialScale N O N m m 1 1 a δ A η
    0 < t ∧ t ≤ 1 ∧
      ∀ (N' O' : ℕ), N' ≤ N → O' ≤ O → ∀ s : ℝ, |s| ≤ t →
        |s| * polynomialMassC2Budget N' m 1 ≤ slicedPrincipalC2Tolerance N' O' m 1 a δ A η := by
  let ε := slicedPrincipalC2Tolerance N O m 1 a δ A η
  have hε := slicedPrincipalC2Tolerance_pos_le_one N O m zero_le_one ha hδ hA hη
  have hM : 0 ≤ polynomialMassC2Budget N m 1 := polynomialMassC2Budget_nonneg N m zero_le_one
  have ht : 0 < ε / (1 + polynomialMassC2Budget N m 1) := div_pos hε.1 (by positivity)
  have htε : ε / (1 + polynomialMassC2Budget N m 1) ≤ ε := div_le_self hε.1.le (by linarith)
  refine ⟨ht, htε.trans hε.2, ?_⟩
  intro N' O' hN hO s hs
  have hMN : polynomialMassC2Budget N' m 1 ≤ polynomialMassC2Budget N m 1 := by
    unfold polynomialMassC2Budget
    gcongr
  have hh := (le_div_iff₀ (by positivity : 0 < 1 + polynomialMassC2Budget N m 1)).mp hs
  have hsmall : |s| * polynomialMassC2Budget N m 1 ≤ ε := by nlinarith [abs_nonneg s]
  exact ((mul_le_mul_of_nonneg_left hMN (abs_nonneg s)).trans hsmall).trans
    (slicedPrincipalC2Tolerance_antitone hN hO zero_le_one ha hδ hA hη)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedPerturbativeSeedPowerBudget
namespace OAI

section

namespace Erdos3

theorem slicedPrincipalBoundaryRadius_inverse_le_exp (N : ℕ) {η P : ℝ}
    (hη : 0 < η) (hP : 0 ≤ P) (hN : (N : ℝ) + 1 ≤ Real.exp P)
    (hηP : η⁻¹ ≤ Real.exp P) :
    (slicedPrincipalBoundaryRadius N η)⁻¹ ≤ Real.exp (2 * P + 4) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h16 : (16 : ℝ) ≤ Real.exp 4 := by
    calc
      _ = (2 : ℝ) ^ 4 := by norm_num
      _ ≤ (Real.exp 1) ^ 4 := pow_le_pow_left₀ (by norm_num) h2 _
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  unfold slicedPrincipalBoundaryRadius
  apply inv_min_le_of_inv_le
  · norm_num
    have he := Real.exp_le_exp.mpr (show 4 ≤ 2 * P + 4 by linarith)
    linarith [Real.add_one_le_exp (4 : ℝ)]
  · calc
      (η / (16 * ((N : ℝ) + 1)))⁻¹ = 16 * ((N : ℝ) + 1) * η⁻¹ := by rw [inv_div, div_eq_mul_inv]
      _ ≤ Real.exp 4 * Real.exp P * Real.exp P := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

theorem slicedPrincipalMinor_inverse_le_exp (N m : ℕ) {a δ η P : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (hη : 0 < η) (hP : 0 ≤ P)
    (hN : (N : ℝ) + 1 ≤ Real.exp P) (haP : a⁻¹ ≤ Real.exp P)
    (hδP : δ⁻¹ ≤ Real.exp P) (hηP : η⁻¹ ≤ Real.exp P) :
    (a * δ * (δ * slicedPrincipalBoundaryRadius N η) ^ m)⁻¹ ≤
      Real.exp (2 * P + (3 * P + 4) * m) := by
  have haInv : 0 < a⁻¹ := inv_pos.mpr ha
  have hr := (slicedPrincipalBoundaryRadius_spec N hη).1
  have hrP := slicedPrincipalBoundaryRadius_inverse_le_exp N hη hP hN hηP
  calc
    _ = (a⁻¹ * δ⁻¹) * (δ⁻¹ * (slicedPrincipalBoundaryRadius N η)⁻¹) ^ m := by
      simp only [mul_inv_rev]
      ring
    _ ≤ (Real.exp P * Real.exp P) * (Real.exp P * Real.exp (2 * P + 4)) ^ m := by gcongr
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring

theorem slicedPrincipalComparisonBudget_le_exp (N m : ℕ) {C A r κ P : ℝ}
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hr : 0 < r) (hκ : 0 < κ) (hP : 0 ≤ P)
    (hN : (N : ℝ) ≤ Real.exp P) (hm : (m : ℝ) ≤ Real.exp P)
    (hCP : C ≤ Real.exp P) (hAP : A ≤ Real.exp P)
    (hrP : r⁻¹ ≤ Real.exp P) (hκP : κ⁻¹ ≤ Real.exp P) :
    slicedPrincipalComparisonBudget N m C A r κ ≤ Real.exp (8 * P + 5) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hH : (N : ℝ) * (N * ((m : ℝ) * ((m : ℝ) * C))) ≤ Real.exp (5 * P) := by
    calc
      _ ≤ Real.exp P * (Real.exp P * (Real.exp P * (Real.exp P * Real.exp P))) := by gcongr
      _ = _ := by simp only [← Real.exp_add]; congr 1; ring
  have hH1 : (N : ℝ) * (N * ((m : ℝ) * ((m : ℝ) * C))) + 1 ≤ Real.exp (5 * P + 1) := by
    simpa only [add_comm] using one_add_le_exp_succ (by positivity : 0 ≤ 5 * P) hH
  have hS : 2 * κ⁻¹ * (2 * (N : ℝ) ^ 2 * A / r) ≤ Real.exp (5 * P + 2) := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ Real.exp 1 * Real.exp P * (Real.exp 1 * (Real.exp P)^2 * Real.exp P * Real.exp P) := by gcongr
      _ = _ := by rw [← Real.exp_nat_mul]; simp only [← Real.exp_add]; congr 1; ring
  have hT : (N : ℝ) * ((2 * κ⁻¹)^2 * (N * (N * ((m : ℝ) * ((m : ℝ) * C))) + 1)) ≤
      Real.exp (8 * P + 3) := by
    calc
      _ ≤ Real.exp P * ((Real.exp 1 * Real.exp P)^2 * Real.exp (5 * P + 1)) := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_nat_mul]; simp only [← Real.exp_add]; congr 1; ring
  have hS' := hS.trans (Real.exp_le_exp.mpr (show 5 * P + 2 ≤ 8 * P + 3 by linarith))
  have hsum : 2 * κ⁻¹ * (2 * (N : ℝ)^2 * A / r) +
      N * ((2 * κ⁻¹)^2 * (N * (N * ((m : ℝ) * ((m : ℝ) * C))) + 1)) ≤ Real.exp (8 * P + 4) := by
    calc
      _ ≤ 2 * Real.exp (8 * P + 3) := by linarith
      _ ≤ Real.exp 1 * Real.exp (8 * P + 3) := mul_le_mul_of_nonneg_right h2 (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hb := one_add_le_exp_succ (by positivity : 0 ≤ 8 * P + 4) hsum
  rw [show 8 * P + 4 + 1 = 8 * P + 5 by ring] at hb
  simpa only [slicedPrincipalComparisonBudget, ← add_assoc] using hb

end Erdos3

end

section

namespace Erdos3

theorem slicedEndpointUniformScale_inverse_le_exp (N O m : ℕ)
    {a δ A η P : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hA : 0 ≤ A) (hη : 0 < η) (hP : 0 ≤ P)
    (hN : (N : ℝ) + 1 ≤ Real.exp P) (hO : (O : ℝ) ≤ Real.exp P) (hm : (m : ℝ) ≤ Real.exp P)
    (haP : a⁻¹ ≤ Real.exp P) (hδP : δ⁻¹ ≤ Real.exp P)
    (hAP : A ≤ Real.exp P) (hηP : η⁻¹ ≤ Real.exp P) :
    let L := (3 * P + 4) * m + 5 * P + 10
    (slicedPolynomialScale N O N m m 1 1 a δ A η)⁻¹ ≤ Real.exp (48 * L + 2 * P + 2 * m + 47) := by
  let L := (3 * P + 4) * m + 5 * P + 10
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hPL : P ≤ L := by dsimp [L]; nlinarith
  have hLP : Real.exp P ≤ Real.exp L := Real.exp_le_exp.mpr hPL
  let r := slicedPrincipalBoundaryRadius N η
  let κ := a * δ * (δ * r)^m
  have hr : 0 < r := (slicedPrincipalBoundaryRadius_spec N hη).1
  have hκ : 0 < κ := mul_pos (mul_pos ha hδ) (pow_pos (mul_pos hδ hr) _)
  have hN0 : (N : ℝ) ≤ Real.exp P := by linarith
  have hrL : r⁻¹ ≤ Real.exp L :=
    (slicedPrincipalBoundaryRadius_inverse_le_exp N hη hP hN hηP).trans
      (Real.exp_le_exp.mpr (by dsimp [L]; nlinarith))
  have hκL : κ⁻¹ ≤ Real.exp L :=
    (slicedPrincipalMinor_inverse_le_exp N m ha hδ hη hP hN haP hδP hηP).trans
      (Real.exp_le_exp.mpr (by dsimp [L]; nlinarith))
  let Q := slicedPrincipalComparisonBudget N m 1 A r κ
  have hQ : 0 ≤ Q := slicedPrincipalComparisonBudget_nonneg N m zero_le_one hA hr hκ
  have hQL : Q ≤ Real.exp (8 * L + 5) := slicedPrincipalComparisonBudget_le_exp N m
    zero_le_one hA hr hκ hL (hN0.trans hLP) (hm.trans hLP)
    (Real.one_le_exp_iff.mpr hL) (hAP.trans hLP) hrL hκL
  have hLS : L ≤ 8 * L + 6 := by linarith
  have hPS : P ≤ 8 * L + 6 := hPL.trans hLS
  have hhalf : (η / 2)⁻¹ ≤ Real.exp (8 * L + 6) := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      _ = 2 * η⁻¹ := by rw [inv_div, div_eq_mul_inv]
      _ ≤ Real.exp 1 * Real.exp P := by gcongr
      _ = Real.exp (P + 1) := by rw [← Real.exp_add, add_comm]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have ht : (slicedPrincipalC2Tolerance N O m 1 a δ A η)⁻¹ ≤ Real.exp (48 * L + 44) := by
    have he := polynomialPerturbationScale_inverse_le_exp (inv_nonneg.mpr hκ.le) zero_le_one hQ
      (half_pos hη) (show 0 ≤ 8 * L + 6 by positivity) O
      (hO.trans (Real.exp_le_exp.mpr hPS))
      (hκL.trans (Real.exp_le_exp.mpr hLS))
      (Real.one_le_exp_iff.mpr (by positivity))
      (hQL.trans (Real.exp_le_exp.mpr (by linarith))) hhalf
    change (slicedPrincipalC2Tolerance N O m 1 a δ A η)⁻¹ ≤ Real.exp (6 * (8 * L + 6) + 8) at he
    convert he using 1
    congr 1
    ring
  have hM : polynomialMassC2Budget N m 1 ≤ Real.exp (2 * P + 2 * m + 2) := by
    simpa only [add_zero] using polynomialMassC2Budget_le_exp N m hP zero_le_one hN0
      (show (1 : ℝ) ≤ Real.exp 0 by simp)
  have hM1 := one_add_le_exp_succ (show 0 ≤ 2 * P + 2 * m + 2 by positivity) hM
  have htpos := (slicedPrincipalC2Tolerance_pos_le_one N O m zero_le_one ha hδ hA hη).1
  change (slicedPolynomialScale N O N m m 1 1 a δ A η)⁻¹ ≤ _
  rw [slicedPolynomialScale, inv_div, div_eq_mul_inv]
  calc
    _ ≤ Real.exp (2 * P + 2 * m + 2 + 1) * Real.exp (48 * L + 44) := by gcongr
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {D : Type*} [Fintype D] (B : D → Type*) [∀ d, Fintype (B d)]

theorem unitProfilePrincipalLowerBound_inv_le_exp {C : ℝ}
    (hsize : ((∑ d, Fintype.card (B d) : ℕ) : ℝ) ≤ C) :
    (unitProfilePrincipalLowerBound B)⁻¹ ≤ Real.exp (C + 4) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h8 : (8 : ℝ) ≤ Real.exp 3 := by
    calc
      _ = (2 : ℝ) ^ 3 := by norm_num
      _ ≤ (Real.exp 1) ^ 3 := pow_le_pow_left₀ (by norm_num) h2 _
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hcard : ((∑ d, Fintype.card (B d) : ℕ) : ℝ) + 1 ≤ Real.exp C := by
    linarith [Real.add_one_le_exp C]
  simp only [unitProfilePrincipalLowerBound, one_div, inv_inv]
  calc
    _ ≤ Real.exp 3 * Real.exp C :=
      mul_le_mul h8 hcard (by positivity) (Real.exp_nonneg _)
    _ = Real.exp (C + 3) := by rw [← Real.exp_add, add_comm]
    _ ≤ Real.exp (C + 4) := Real.exp_le_exp.mpr (by linarith)

theorem principalBlock_card_le_input_card (F : D → Type*) [∀ d, Fintype (F d)]
    (hF : ∀ d, 1 ≤ Fintype.card (F d)) :
    (∑ d, Fintype.card (B d)) ≤ Fintype.card (Σ d, B d × F d) := by
  rw [Fintype.card_sigma]
  apply Finset.sum_le_sum
  intro d _
  rw [Fintype.card_prod]
  simpa only [Nat.mul_one] using Nat.mul_le_mul_left (Fintype.card (B d)) (hF d)

theorem unitProfilePrincipalLowerBound_inv_le_exp_of_input_card
    (F : D → Type*) [∀ d, Fintype (F d)]
    (hF : ∀ d, 1 ≤ Fintype.card (F d)) {C : ℝ}
    (hsize : (Fintype.card (Σ d, B d × F d) : ℝ) ≤ C) :
    (unitProfilePrincipalLowerBound B)⁻¹ ≤ Real.exp (C + 4) := by
  apply unitProfilePrincipalLowerBound_inv_le_exp B
  apply le_trans _ hsize
  exact_mod_cast principalBlock_card_le_input_card B F hF

namespace VectorPolynomial

theorem allocatedUnitProfilePrincipalLowerBound_inv_le_exp
    {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] {C : ℝ}
    (hsize : (Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) : ℝ) ≤ C) :
    (unitProfilePrincipalLowerBound B)⁻¹ ≤ Real.exp (C + 4) := by
  exact unitProfilePrincipalLowerBound_inv_le_exp_of_input_card B
    (fun a => Fin (layerSamplerDegree I n a))
    (fun a => by
      rw [Fintype.card_fin]
      exact Nat.succ_le_succ (Nat.zero_le _)) hsize

end VectorPolynomial

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Input" => (Σ a : {a : LayerSamplerAxis I n // ¬short a},
  B (Subtype.val a) × Fin (degree (Subtype.val a)))

theorem allocatedOriginalSampleLiftInput_card_le_allAxis :
    Fintype.card Input ≤ Fintype.card (PrincipalTupleIndex B degree) := by
  simp only [PrincipalTupleIndex, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]
  apply Finset.sum_le_sum_of_injOn Subtype.val
    (fun _ _ _ _ h => Subtype.val_injective h) (Finset.subset_univ _)
  · intro a _
    exact le_rfl
  · intro a _ _
    exact Nat.zero_le _

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SlicedUniformTailTolerance
namespace OAI

section

namespace Erdos3

theorem slicedEndpointUniformScale_exp_lower (N O m : ℕ)
    {a δ A η P : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hA : 0 ≤ A) (hη : 0 < η) (hP : 0 ≤ P)
    (hN : (N : ℝ) + 1 ≤ Real.exp P) (hO : (O : ℝ) ≤ Real.exp P) (hm : (m : ℝ) ≤ Real.exp P)
    (haP : a⁻¹ ≤ Real.exp P) (hδP : δ⁻¹ ≤ Real.exp P)
    (hAP : A ≤ Real.exp P) (hηP : η⁻¹ ≤ Real.exp P) :
    Real.exp (-(48 * ((3 * P + 4) * m + 5 * P + 10) + 2 * P + 2 * m + 47)) ≤
      slicedPolynomialScale N O N m m 1 1 a δ A η := by
  have hpos := (slicedEndpointUniformScale_spec N O m ha hδ hA hη).1
  have hinv := slicedEndpointUniformScale_inverse_le_exp N O m
    ha hδ hA hη hP hN hO hm haP hδP hAP hηP
  have h := one_div_le_one_div_of_le (inv_pos.mpr hpos) hinv
  simpa only [one_div, inv_inv, ← Real.exp_neg] using h

theorem slicedEndpointUniformScale_exp_tail_tolerance (N O m : ℕ)
    {a δ A η P : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hA : 0 ≤ A) (hη : 0 < η) (hP : 0 ≤ P)
    (hN : (N : ℝ) + 1 ≤ Real.exp P) (hO : (O : ℝ) ≤ Real.exp P) (hm : (m : ℝ) ≤ Real.exp P)
    (haP : a⁻¹ ≤ Real.exp P) (hδP : δ⁻¹ ≤ Real.exp P)
    (hAP : A ≤ Real.exp P) (hηP : η⁻¹ ≤ Real.exp P)
    (N' O' : ℕ) (hN' : N' ≤ N) (hO' : O' ≤ O) :
    Real.exp (-(48 * ((3 * P + 4) * m + 5 * P + 10) + 2 * P + 2 * m + 47)) *
        polynomialMassC2Budget N' m 1 ≤
      slicedPrincipalC2Tolerance N' O' m 1 a δ A η := by
  have hs := slicedEndpointUniformScale_exp_lower N O m
    ha hδ hA hη hP hN hO hm haP hδP hAP hηP
  have h := (slicedEndpointUniformScale_spec N O m ha hδ hA hη).2.2 N' O' hN' hO'
    (Real.exp (-(48 * ((3 * P + 4) * m + 5 * P + 10) + 2 * P + 2 * m + 47)))
    (by simpa only [abs_of_pos (Real.exp_pos _)] using hs)
  simpa only [abs_of_pos (Real.exp_pos _)] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedFixedPathSlicedSourceErrorBudget
namespace OAI

section

namespace Erdos3
open scoped BigOperators NNReal Classical

theorem fixedPathSlicedPerturbation_tail
    (N O m : ℕ) {D P Pslice E a δ A η : ℝ}
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hPslice : 0 ≤ Pslice) (hE : 0 ≤ E)
    (hN : (N : ℝ) ≤ D) (hO : (O : ℝ) ≤ D)
    (ha : 0 < a) (hδ : 0 < δ) (hA : 0 ≤ A) (hη : 0 < η)
    (haP : a⁻¹ ≤ Real.exp P) (hδP : δ⁻¹ ≤ Real.exp Pslice)
    (hAP : A ≤ Real.exp P) (hηE : η⁻¹ ≤ Real.exp E)
    {N' O' : ℕ} (hNN : N' ≤ N) (hOO : O' ≤ O) {t : ℝ}
    (ht : |t| ≤ Real.exp (-fixedPathSlicedPerturbationLog D P Pslice E m)) :
    |t| * polynomialMassC2Budget N' m 1 ≤
      slicedPrincipalC2Tolerance N' O' m 1 a δ A η := by
  let Q := D + (P + Pslice) + E + m + 2
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hDQ : D ≤ Q := by dsimp only [Q]; linarith
  have hPQ : P ≤ Q := by dsimp only [Q]; linarith
  have hsQ : Pslice ≤ Q := by dsimp only [Q]; linarith
  have hEQ : E ≤ Q := by dsimp only [Q]; linarith
  have hmQ : (m : ℝ) ≤ Q := by dsimp only [Q]; linarith
  have hNQ : (N : ℝ) + 1 ≤ Real.exp Q :=
    ((show (N : ℝ) + 1 ≤ D + 1 by linarith).trans
      (Real.add_one_le_exp D)).trans (Real.exp_le_exp.mpr hDQ)
  have hOQ : (O : ℝ) ≤ Real.exp Q :=
    hO.trans ((by linarith [Real.add_one_le_exp D] : D ≤ Real.exp D).trans
      (Real.exp_le_exp.mpr hDQ))
  have hmexp : (m : ℝ) ≤ Real.exp Q :=
    (by linarith [Real.add_one_le_exp (m : ℝ)] : (m : ℝ) ≤ Real.exp m).trans
      (Real.exp_le_exp.mpr hmQ)
  have he := slicedEndpointUniformScale_exp_tail_tolerance N O m ha hδ hA hη hQ
    hNQ hOQ hmexp (haP.trans (Real.exp_le_exp.mpr hPQ))
    (hδP.trans (Real.exp_le_exp.mpr hsQ)) (hAP.trans (Real.exp_le_exp.mpr hPQ))
    (hηE.trans (Real.exp_le_exp.mpr hEQ)) N' O' hNN hOO
  have hmass : 0 ≤ polynomialMassC2Budget N' m 1 := by unfold polynomialMassC2Budget; positivity
  exact (mul_le_mul_of_nonneg_right ht hmass).trans
    (by simpa only [fixedPathSlicedPerturbationLog, fixedPathPerturbationLog, Q] using he)

theorem fixedPathSliceWidth_budget {cost : ℝ} (hcost : 0 ≤ cost) :
    0 < Real.exp (-cost) / 2 ∧ Real.exp (-cost) / 2 ≤ 1 ∧
      (Real.exp (-cost) / 2)⁻¹ ≤ Real.exp (cost + 1) := by
  have he : Real.exp (-cost) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hcost)
  refine ⟨by positivity, by linarith, ?_⟩
  rw [inv_div, div_eq_mul_inv, ← Real.exp_neg, neg_neg, Real.exp_add]
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  exact (mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg cost)).trans_eq (mul_comm _ _)

namespace VectorPolynomial
variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

theorem allocatedFixedPathSlicedPerturbation_tail_uniform
    {D P Pslice E δ η : ℝ}
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hPslice : 0 ≤ Pslice) (hE : 0 ≤ E)
    (hInput : (Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) : ℝ) ≤ D)
    (hAxis : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ D)
    (A : ℝ≥0) (hδ : 0 < δ) (hη : 0 < η)
    (haP : (unitProfilePrincipalLowerBound B)⁻¹ ≤ Real.exp P)
    (hδP : δ⁻¹ ≤ Real.exp Pslice) (hAP : (A : ℝ) ≤ Real.exp P)
    (hηE : η⁻¹ ≤ Real.exp E)
    {t : ℝ} (ht : |t| ≤ Real.exp (-fixedPathSlicedPerturbationLog D P Pslice E m))
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ) :
    let active := fun a => ¬allocatedShortAxis (I := I) U basis S.value a
    let inputs := PrincipalTupleIndex (fun a : {a // active a} => B a.val)
      (fun a => layerSamplerDegree I n a.val)
    |t| * polynomialMassC2Budget (Fintype.card inputs) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card inputs) (Fintype.card {a // active a})
        m 1 (unitProfilePrincipalLowerBound B) δ A η := by
  intro active inputs
  exact fixedPathSlicedPerturbation_tail
    (Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)))
    (Fintype.card (LayerSamplerAxis I n)) m hD hP hPslice hE hInput hAxis
    (unitProfilePrincipalLowerBound_pos B) hδ A.coe_nonneg hη haP hδP hAP hηE
    (allocatedOriginalSampleLiftInput_card_le_allAxis B U basis S)
    (Fintype.card_subtype_le _) ht

theorem allocatedFixedPathSlicedPerturbation_tail_of_inputCount
    {D P cost E η : ℝ} (hD : 0 ≤ D) (hP : 0 ≤ P) (hcost : 0 ≤ cost) (hE : 0 ≤ E)
    (hInput : (Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) : ℝ) ≤ D)
    (hAxis : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ D)
    (A : ℝ≥0) (hη : 0 < η) (hAP : (A : ℝ) ≤ Real.exp P) (hηE : η⁻¹ ≤ Real.exp E)
    {t : ℝ}
    (ht : |t| ≤ Real.exp (-fixedPathSlicedPerturbationLog D (D + P + 4) (cost + 1) E m))
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ) :
    let active := fun a => ¬allocatedShortAxis (I := I) U basis S.value a
    let inputs := PrincipalTupleIndex (fun a : {a // active a} => B a.val)
      (fun a => layerSamplerDegree I n a.val)
    |t| * polynomialMassC2Budget (Fintype.card inputs) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card inputs) (Fintype.card {a // active a})
        m 1 (unitProfilePrincipalLowerBound B) (Real.exp (-cost) / 2) A η := by
  exact allocatedFixedPathSlicedPerturbation_tail_uniform B U basis hD (by positivity)
    (by positivity) hE hInput hAxis A (fixedPathSliceWidth_budget hcost).1 hη
    ((allocatedUnitProfilePrincipalLowerBound_inv_le_exp B hInput).trans
      (Real.exp_le_exp.mpr (by linarith)))
    (fixedPathSliceWidth_budget hcost).2.2
    (hAP.trans (Real.exp_le_exp.mpr (by linarith))) hηE ht S

theorem allocatedFixedPathSlicedPerturbation_chosen_tail_s2_oai
    {D P cost E η : ℝ} (hD : 0 ≤ D) (hP : 0 ≤ P) (hcost : 0 ≤ cost) (hE : 0 ≤ E)
    (hInput : (Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) : ℝ) ≤ D)
    (hAxis : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ D)
    (A : ℝ≥0) (hη : 0 < η) (hAP : (A : ℝ) ≤ Real.exp P) (hηE : η⁻¹ ≤ Real.exp E) :
    let Qσ := fixedPathSlicedPerturbationLog D (D + P + 4) (cost + 1) E m
    let t := Real.exp (-Qσ)
    0 < t ∧ t ≤ 1 ∧ ∀ {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ),
    let active := fun a => ¬allocatedShortAxis (I := I) U basis S.value a
    let inputs := PrincipalTupleIndex (fun a : {a // active a} => B a.val)
      (fun a => layerSamplerDegree I n a.val)
    |t| * polynomialMassC2Budget (Fintype.card inputs) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card inputs) (Fintype.card {a // active a})
        m 1 (unitProfilePrincipalLowerBound B) (Real.exp (-cost) / 2) A η := by
  intro Qσ t
  refine ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr (neg_nonpos.mpr
    (fixedPathSlicedPerturbationLog_nonneg hD (by positivity) (by positivity) hE m)), ?_⟩
  intro R σ S
  exact allocatedFixedPathSlicedPerturbation_tail_of_inputCount B U basis hD hP hcost hE
    hInput hAxis A hη hAP hηE (by rw [abs_of_pos (Real.exp_pos _)]) S

end VectorPolynomial
end Erdos3

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedFixedPathSlicedPerturbation_chosen_tail_s2_oai.{u_1, u_2, u_3, u_4} := @OAI.Erdos3.VectorPolynomial.allocatedFixedPathSlicedPerturbation_chosen_tail_s2_oai.{u_1, u_2, u_3, u_4}
