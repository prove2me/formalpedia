-- Prove2me | solution 1 for OAI.Erdos3.exists_unconditioned_joint_scalar_transfer_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:16:34.048058+00:00
-- url     : https://prove2.me/submissions/545dd0ce-07bf-44a0-84ef-4d87de873e8f

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B218
import Theorems.Thm_OAI_Erdos3_adaptiveAffineCutoff_reference_bounds_s2
import Theorems.Thm_OAI_Erdos3_allocated_weighted_physical_replacement_s2
import Theorems.Thm_OAI_Erdos3_exists_niltest_geometric_scalar_transfer_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.UniformSelectedCoefficientProductLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem baseArrayJoin_injective {K I X : Type*} (tail : K × I → X) :
    Function.Injective (baseArrayJoin tail) := by
  intro b c he
  funext i
  exact congrFun he (none,i)

theorem independentProductPMF_base_split {K I X : Type*} [Fintype K] [Fintype I]
    [Countable X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (p : Option K × I → PMF X) :
    independentProductPMF p =
      (independentProductPMF (fun k : K × I => p (some k.1,k.2))).bind
        (fun tail => (independentProductPMF (fun i => p (none,i))).map (baseArrayJoin tail)) := by
  ext z
  let tail := fun k : K × I => z (some k.1,k.2)
  let base := fun i : I => z (none,i)
  have hz : baseArrayJoin tail base = z := baseArrayJoin_eta z
  rw [← hz, PMF.bind_apply, tsum_eq_single tail]
  · rw [pmf_map_injective_at _ _ (baseArrayJoin_injective tail)]
    simp only [independentProductPMF_apply, Fintype.prod_prod_type, Fintype.prod_option, baseArrayJoin]
    exact mul_comm _ _
  · intro other hother
    have hr : baseArrayJoin tail base ∉ Set.range (baseArrayJoin other) := by
      rintro ⟨b, he⟩
      apply hother
      funext k
      exact congrFun he (some k.1,k.2)
    rw [pmf_map_zero_off_range _ _ _ hr, mul_zero]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealFiniteZeroExtension
namespace OAI

section

namespace Erdos3

open scoped Classical

theorem realZeroExtendFinset_on {X : Type*} (S : Finset X) (f : X → ℝ)
    {x : X} (hx : x ∈ S) : realZeroExtendFinset S f x = f x := by
  simp only [realZeroExtendFinset, if_pos hx]

theorem realZeroExtendFinset_off {X : Type*} (S : Finset X) (f : X → ℝ)
    {x : X} (hx : x ∉ S) : realZeroExtendFinset S f x = 0 := by
  simp only [realZeroExtendFinset, if_neg hx]

theorem realZeroExtendFinset_unit {X : Type*} (S : Finset X) (f : X → ℝ)
    (hf : ∀ x ∈ S, 0 ≤ f x ∧ f x ≤ 1) (x : X) :
    0 ≤ realZeroExtendFinset S f x ∧ realZeroExtendFinset S f x ≤ 1 := by
  by_cases hx : x ∈ S
  · simpa only [realZeroExtendFinset_on S f hx] using hf x hx
  · simp only [realZeroExtendFinset_off S f hx, le_refl, zero_le_one, and_self]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineMeshRetention
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem integerBoxUniformWeights_mean {J : Type*} [Fintype J] [DecidableEq J]
    (lo hi : J → ℤ) (hlen : ∀ j, lo j < hi j)
    (f : (∀ j, Finset.Ico (lo j) (hi j)) → ℝ) :
    (integerBoxUniformWeights lo hi hlen).mean f = 𝔼 x, f x := by
  let : ∀ j, Nonempty (Finset.Ico (lo j) (hi j)) :=
    fun j => ⟨⟨lo j, Finset.mem_Ico.mpr ⟨le_rfl, hlen j⟩⟩⟩
  have he : integerBoxUniformWeights lo hi hlen =
      FiniteProbabilityWeights.uniform (∀ j, Finset.Ico (lo j) (hi j)) := by
    apply FiniteProbabilityWeights.eq_of_weight_eq
    intro x
    change (∏ j, (Fintype.card (Finset.Ico (lo j) (hi j)) : ℝ)⁻¹) =
      (Fintype.card (∀ j, Finset.Ico (lo j) (hi j)) : ℝ)⁻¹
    rw [Fintype.card_pi, Nat.cast_prod, Finset.prod_inv_distrib]
  rw [he, FiniteProbabilityWeights.uniform_mean]

end Erdos3

end

section

namespace Erdos3

theorem integerBoxBadPairBudget_nonneg (d B R r : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    0 ≤ integerBoxBadPairBudget d B R r M := by
  unfold integerBoxBadPairBudget
  positivity

theorem integerBoxBadPairBudget_le_separated (d B R r : ℕ) {M C nu : ℝ}
    (hd : 2 ≤ d) (hB : 0 < B) (hBM : (B : ℝ) ≤ M) (hC : 0 ≤ C)
    (hR : (R : ℝ) ≤ C * M) (hr : (r : ℝ) ≤ nu * M)
    (hinv : 1 / M ≤ nu) :
    integerBoxBadPairBudget d B R r M ≤
      2 ^ (d - 1) * (1 + C) / (B : ℝ) ^ (d - 1) + (3 * nu) ^ d := by
  have hBp : (0 : ℝ) < B := by exact_mod_cast hB
  have hM : 0 < M := hBp.trans_le hBM
  have hpow : (B : ℝ) ^ (d - 1) ≤ M ^ (d - 1) :=
    pow_le_pow_left₀ hBp.le hBM _
  have hR' : (R : ℝ) / M ^ d ≤ C / (B : ℝ) ^ (d - 1) := by
    calc
      _ ≤ (C * M) / M ^ d := div_le_div_of_nonneg_right hR (by positivity)
      _ = C / M ^ (d - 1) := by
        conv_lhs => rw [show d = (d - 1) + 1 by omega, pow_succ]
        field_simp
      _ ≤ C / (B : ℝ) ^ (d - 1) := div_le_div_of_nonneg_left hC (by positivity) hpow
  have hnear : (2 * (r : ℝ) + 1) / M ≤ 3 * nu := by
    have hrr : (r : ℝ) / M ≤ nu := (div_le_iff₀ hM).mpr hr
    calc
      _ = 2 * ((r : ℝ) / M) + 1 / M := by ring
      _ ≤ 3 * nu := by linarith
  unfold integerBoxBadPairBudget
  calc
    _ ≤ 2 ^ (d - 1) * (1 / (B : ℝ) ^ (d - 1) + C / (B : ℝ) ^ (d - 1)) +
        (3 * nu) ^ d := add_le_add
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl hR') (by positivity))
      (pow_le_pow_left₀ (by positivity) hnear d)
    _ = _ := by ring

theorem integerBoxBadPairBudget_le_linear (d B R r : ℕ) {M C nu : ℝ}
    (hd : 2 ≤ d) (hB : 0 < B) (hBM : (B : ℝ) ≤ M) (hC : 0 ≤ C)
    (hR : (R : ℝ) ≤ C * M) (hr : (r : ℝ) ≤ nu * M)
    (hinv : 1 / M ≤ nu) (hnu : nu ≤ 1) :
    integerBoxBadPairBudget d B R r M ≤
      2 ^ (d - 1) * (1 + C) / (B : ℝ) + 3 ^ d * nu := by
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hBp : (0 : ℝ) < B := by exact_mod_cast hB
  have hM : 0 < M := hBp.trans_le hBM
  have hnu0 : 0 ≤ nu := (by positivity : 0 ≤ 1 / M).trans hinv
  have hpow : (B : ℝ) ≤ (B : ℝ) ^ (d - 1) := by
    simpa only [pow_one] using pow_le_pow_right₀ hB1 (show 1 ≤ d - 1 by omega)
  have hnpow : nu ^ d ≤ nu := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show d ≠ 0 by omega)
    rw [pow_succ]
    exact (mul_le_mul_of_nonneg_right (pow_le_one₀ hnu0 hnu) hnu0).trans_eq (one_mul nu)
  apply (integerBoxBadPairBudget_le_separated d B R r hd hB hBM hC hR hr hinv).trans
  apply add_le_add
  · exact div_le_div_of_nonneg_left (by positivity) hBp hpow
  · rw [mul_pow]
    exact mul_le_mul_of_nonneg_left hnpow (by positivity)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem integerBox_weighted_joint_mean
    {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (lo hi : I → ℤ) (hsource : ∀ i, lo i < hi i)
    (parLo parHi : J → ℤ) (hparam : ∀ j, parLo j < parHi j)
    (w : (I → ℤ) → ℝ) (f : (I → ℤ) → (∀ j, Finset.Ico (parLo j) (parHi j)) → ℝ) :
    ((integerBoxUniformWeights parLo parHi hparam).prod
      (integerBoxUniformWeights lo hi hsource)).mean
        (fun tx => w (fun i => (tx.2 i).val) * f (fun i => (tx.2 i).val) tx.1) =
      𝔼 z ∈ Fintype.piFinset (fun i => Finset.Ico (lo i) (hi i)), w z * (𝔼 t, f z t) := by
  rw [FiniteProbabilityWeights.mean_prod, FiniteProbabilityWeights.mean_comm]
  simp only [FiniteProbabilityWeights.mean_const_mul, integerBoxUniformWeights_mean]
  rw [← finiteBoxPoints_expect (fun i => Finset.Ico (lo i) (hi i)) (fun z => w z * (𝔼 t, f z t))]
  simp only [Finset.expect_eq_sum_div_card, Finset.card_univ, Fintype.card_coe]
  congr 1
  simpa only [Finset.expect_eq_sum_div_card, Finset.card_univ] using
    Finset.sum_coe_sort (Fintype.piFinset (fun i => Finset.Ico (lo i) (hi i)))
      (fun z => w z * (𝔼 t, f z t))

theorem integerBox_joint_error_of_window_tests
    {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (lo hi : I → ℤ) (hsource : ∀ i, lo i < hi i)
    (parLo parHi : J → ℤ) (hparam : ∀ j, parLo j < parHi j)
    (f : (I → ℤ) → (∀ j, Finset.Ico (parLo j) (parHi j)) → ℝ) (accuracy : ℝ)
    (htest : ∀ v : (I → ℤ) → ℝ, (∀ z, 0 ≤ v z ∧ v z ≤ 1) →
      |𝔼 z ∈ Fintype.piFinset (fun i => Finset.Ico (lo i) (hi i)), v z * (𝔼 t, f z t)| ≤ accuracy)
    (w : (I → ℤ) → ℝ)
    (hw : ∀ z : (∀ i, Finset.Ico (lo i) (hi i)),
      0 ≤ w (fun i => (z i).val) ∧ w (fun i => (z i).val) ≤ 1) :
    |((integerBoxUniformWeights parLo parHi hparam).prod
      (integerBoxUniformWeights lo hi hsource)).mean
        (fun tx => w (fun i => (tx.2 i).val) * f (fun i => (tx.2 i).val) tx.1)| ≤ accuracy := by
  let W := Fintype.piFinset (fun i => Finset.Ico (lo i) (hi i))
  have hwW (z) (hz : z ∈ W) : 0 ≤ w z ∧ w z ≤ 1 := by
    exact hw (fun i => ⟨z i, Fintype.mem_piFinset.mp hz i⟩)
  have h := htest (realZeroExtendFinset W w) (realZeroExtendFinset_unit W w hwW)
  rw [integerBox_weighted_joint_mean lo hi hsource parLo parHi hparam w f]
  convert h using 2
  apply Finset.expect_congr rfl
  intro z hz
  rw [realZeroExtendFinset_on W w hz]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.BoundedPrimeDepthBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem boundedPrime_le (Q : ℕ) (p : BoundedPrime Q) : boundedPrime Q p ≤ Q :=
  ((mem_boundedPrimes Q p.val).mp p.property).2

theorem boundedPrime_injective (Q : ℕ) : Function.Injective (boundedPrime Q) := Subtype.val_injective

theorem boundedPrimePower_le (Q : ℕ) (p : BoundedPrime Q) : boundedPrimePower Q p ≤ Q := by
  have hQ : 0 < Q := (boundedPrime_prime Q p).pos.trans_le (boundedPrime_le Q p)
  exact Nat.pow_log_le_self p.val hQ.ne'

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.FiniteObservationRetraction
namespace OAI

section

namespace Erdos3

namespace FiniteProbabilityWeights

open scoped BigOperators Classical

theorem uniformFinset_weight {X : Type*} (Q : Finset X) (hQ : Q.Nonempty) (q : Q) :
    (uniformFinset Q hQ).weight q = (Q.card : ℝ)⁻¹ := by
  simp only [uniformFinset, uniform, Fintype.card_coe]

end FiniteProbabilityWeights
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PrimeCoordinateCells
namespace OAI

section

namespace Erdos3

theorem affineReferenceInput_bounds (epsilon : ℝ) {U : ℝ} (hU : 0 ≤ U) :
    2 ≤ affineReferenceInput epsilon U ∧ U ≤ affineReferenceInput epsilon U ∧
      affinePrimitiveLogBudget U ≤ affineReferenceInput epsilon U := by
  have hpow : 0 ≤ (affinePrimitiveLogBudget U + 2) ^ affineReferencePower epsilon :=
    pow_nonneg (by unfold affinePrimitiveLogBudget; positivity) _
  unfold affineReferenceInput affinePrimitiveLogBudget at *
  constructor
  · linarith
  constructor <;> linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerBoxCutoffLogBounds
namespace OAI

section

namespace Erdos3

theorem integerBoxGcdCutoff_spec (d : ℕ) {C epsilon : ℝ}
    (heps : 0 < epsilon) :
    0 < integerBoxGcdCutoff d C epsilon ∧
      (2 : ℝ) ^ (d - 1) * (1 + C) / integerBoxGcdCutoff d C epsilon ≤ epsilon / 2 := by
  have hp : 0 < integerBoxGcdCutoff d C epsilon := by
    unfold integerBoxGcdCutoff
    omega
  refine ⟨hp, ?_⟩
  have hpr : (0 : ℝ) < integerBoxGcdCutoff d C epsilon := by exact_mod_cast hp
  have hceil : 2 * (2 : ℝ) ^ (d - 1) * (1 + C) / epsilon ≤
      (integerBoxGcdCutoff d C epsilon : ℝ) := by
    unfold integerBoxGcdCutoff
    push_cast
    linarith [Nat.le_ceil (2 * (2 : ℝ) ^ (d - 1) * (1 + C) / epsilon)]
  have hh := (div_le_iff₀ heps).mp hceil
  apply (div_le_iff₀ hpr).mpr
  nlinarith

theorem integerBoxBadPairBudget_of_cutoffs (d R : ℕ) {C epsilon M : ℝ}
    (hd : 2 ≤ d) (hC : 0 ≤ C) (heps : 0 < epsilon)
    (hscale : integerBoxPairScale d C epsilon ≤ M) (hR : (R : ℝ) ≤ C * M) :
    integerBoxBadPairBudget d (integerBoxGcdCutoff d C epsilon) R
      ⌊integerBoxNearRatio d epsilon * M⌋₊ M ≤ epsilon := by
  have hB := integerBoxGcdCutoff_spec d (C := C) heps
  have hnu := integerBoxNearRatio_spec d heps
  have hBM : (integerBoxGcdCutoff d C epsilon : ℝ) ≤ M := (le_max_left _ _).trans hscale
  have hM : 0 < M := (by exact_mod_cast hB.1 : (0 : ℝ) < integerBoxGcdCutoff d C epsilon).trans_le hBM
  have hinv : 1 / M ≤ integerBoxNearRatio d epsilon := by
    have h := (le_max_right (integerBoxGcdCutoff d C epsilon : ℝ)
      (1 / integerBoxNearRatio d epsilon)).trans hscale
    have hh := (div_le_iff₀ hnu.1).mp h
    apply (div_le_iff₀ hM).mpr
    nlinarith
  have h := integerBoxBadPairBudget_le_linear d (integerBoxGcdCutoff d C epsilon) R
    ⌊integerBoxNearRatio d epsilon * M⌋₊ hd hB.1 hBM hC hR
    (Nat.floor_le (mul_nonneg hnu.1.le hM.le)) hinv hnu.2.1
  linarith [hB.2, hnu.2.2]

theorem integerBoxRetainedGap_spec (d D : ℕ) {c epsilon L M : ℝ}
    (hD : 0 < D) (hc : 0 < c) (heps : 0 < epsilon) (hside : c * L ≤ M) :
    0 < integerBoxRetainedGap d D c epsilon ∧
      integerBoxRetainedGap d D c epsilon * L ≤
        (D : ℝ) * (⌊integerBoxNearRatio d epsilon * M⌋₊ + 1 : ℕ) := by
  have hnu := (integerBoxNearRatio_spec d heps).1
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  constructor
  · unfold integerBoxRetainedGap
    positivity
  · unfold integerBoxRetainedGap
    push_cast
    calc
      _ = (D : ℝ) * (integerBoxNearRatio d epsilon * (c * L)) := by ring
      _ ≤ (D : ℝ) * (integerBoxNearRatio d epsilon * M) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hside hnu.le) hDr.le
      _ ≤ _ := mul_le_mul_of_nonneg_left (Nat.lt_floor_add_one _).le hDr.le

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerWindowFactor
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem integerIntervalBox_card_real {I : Type*} [Fintype I] [DecidableEq I]
    (lo hi : I → ℤ) (hlen : ∀ i, lo i ≤ hi i) :
    ((Fintype.piFinset (fun i => Finset.Ico (lo i) (hi i))).card : ℝ) =
      ∏ i, ((hi i - lo i : ℤ) : ℝ) := by
  rw [Fintype.card_piFinset, Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact_mod_cast Int.card_Ico_of_le (lo i) (hi i) (hlen i)

theorem integerIntervalBox_window_factor_le {I : Type*} [Fintype I] [DecidableEq I]
    (lo hi : I → ℤ) (hlen : ∀ i, lo i < hi i)
    (S : I → ℝ) (hS : ∀ i, 0 ≤ S i) {K : ℝ}
    (hside : ∀ i, S i ≤ K * ((hi i - lo i : ℤ) : ℝ)) :
    (3 : ℝ) ^ Fintype.card I * (∏ i, S i) /
      (Fintype.piFinset (fun i => Finset.Ico (lo i) (hi i))).card ≤
        (3 * K) ^ Fintype.card I := by
  rw [integerIntervalBox_card_real lo hi (fun i => (hlen i).le)]
  have hlenR (i : I) : (0 : ℝ) < ((hi i - lo i : ℤ) : ℝ) := by
    exact_mod_cast sub_pos.mpr (hlen i)
  calc
    _ = ∏ i, 3 * (S i / ((hi i - lo i : ℤ) : ℝ)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Finset.prod_div_distrib]
      ring
    _ ≤ ∏ _i : I, 3 * K := Finset.prod_le_prod
      (fun i _ => mul_nonneg (by norm_num) (div_nonneg (hS i) (hlenR i).le))
      (fun i _ => mul_le_mul_of_nonneg_left ((div_le_iff₀ (hlenR i)).mpr (hside i)) (by norm_num))
    _ = _ := by rw [Finset.prod_const, Finset.card_univ]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SmallWeightedPhysicalReplacement
namespace OAI

section

namespace Erdos3

theorem weightedReplacementTolerance_bound {F E epsilon beta : ℝ}
    (hF : 0 ≤ F) (hE : 0 ≤ E) (heps : 0 < epsilon) (hbeta : 0 ≤ beta)
    (hsmall : beta ≤ weightedReplacementTolerance F E epsilon) :
    F * Real.sqrt (E * beta + weightedReplacementTolerance F E epsilon) ≤ epsilon := by
  have htol := weightedReplacementTolerance_pos (F := F) hE heps
  have hcost := (replacementAccuracy_spec
    (mul_nonneg (sq_nonneg F) (by linarith : 0 ≤ 1 + E)) (sq_pos_of_pos heps)).2.2
  change F ^ 2 * (1 + E) * weightedReplacementTolerance F E epsilon ≤ epsilon ^ 2 at hcost
  have harg : 0 ≤ E * beta + weightedReplacementTolerance F E epsilon := by positivity
  have hsquare : (F * Real.sqrt (E * beta + weightedReplacementTolerance F E epsilon)) ^ 2 ≤
      epsilon ^ 2 := by
    calc
      _ = F ^ 2 * (E * beta + weightedReplacementTolerance F E epsilon) := by
        rw [mul_pow, Real.sq_sqrt harg]
      _ ≤ F ^ 2 * (E * weightedReplacementTolerance F E epsilon +
          weightedReplacementTolerance F E epsilon) :=
        mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hsmall hE) le_rfl) (sq_nonneg F)
      _ = F ^ 2 * (1 + E) * weightedReplacementTolerance F E epsilon := by ring
      _ ≤ epsilon ^ 2 := hcost
  exact (sq_le_sq₀ (mul_nonneg hF (Real.sqrt_nonneg _)) heps.le).mp hsquare

theorem cutoff_weighted_replacement_bound (d R : ℕ) {F E epsilon C M : ℝ}
    (hd : 2 ≤ d) (hF : 0 ≤ F) (hE : 0 ≤ E) (hC : 0 ≤ C) (heps : 0 < epsilon)
    (hscale : integerBoxPairScale d C (weightedReplacementTolerance F E epsilon) ≤ M)
    (hR : (R : ℝ) ≤ C * M) :
    F * Real.sqrt (E * integerBoxBadPairBudget d
      (integerBoxGcdCutoff d C (weightedReplacementTolerance F E epsilon)) R
      ⌊integerBoxNearRatio d (weightedReplacementTolerance F E epsilon) * M⌋₊ M +
      weightedReplacementTolerance F E epsilon) ≤ epsilon := by
  have htol := weightedReplacementTolerance_pos (F := F) hE heps
  have hM : 0 ≤ M := by
    have h : (integerBoxGcdCutoff d C (weightedReplacementTolerance F E epsilon) : ℝ) ≤ M :=
      (le_max_left _ _).trans hscale
    exact (Nat.cast_nonneg _).trans h
  exact weightedReplacementTolerance_bound hF hE heps
    (integerBoxBadPairBudget_nonneg _ _ _ _ hM)
    (integerBoxBadPairBudget_of_cutoffs d R hd hC htol hscale hR)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem small_weighted_physical_replacement {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (k0 : J) (D : ℕ) (anchor parLo parHi : J → ℤ) (hpar : ∀ j, parLo j < parHi j)
    (H : I → ℝ) {L C A epsilon K c Cwidth : ℝ}
    (hL : 1 ≤ L) (hC : 1 ≤ C) (hA : 0 ≤ A) (heps : 0 < epsilon)
    (hK : 0 ≤ K) (hc : 0 < c) (hCwidth : 0 ≤ Cwidth) (hD : 0 < D)
    (hleft : ∀ j, |((anchor j + (D : ℤ) * parLo j : ℤ) : ℝ) / L| ≤ C)
    (hright : ∀ j, |((anchor j + (D : ℤ) * parHi j : ℤ) : ℝ) / L| ≤ C)
    (origin : Option J × I → ℤ) (lo : I → ℤ) (N : I → ℕ)
    (degree exponent : ℕ) (hexponent : 2 ≤ exponent)
    (f : (I → ℤ) → ℝ) (hf : ∀ x ∈ translatedIntegerBox lo N, 0 ≤ f x ∧ f x ≤ 1)
    (modLog dimLog : ℝ) (hmodLog : 0 ≤ modLog)
    (hdim : (Fintype.card I : ℝ) ≤ Real.exp dimLog)
    (hupper : ∀ i, H i ≤ 2 * (N i : ℝ)) (hratio : ∀ i, (N i : ℝ) ≤ A * H i)
    (R : ℕ) (parMin : ℝ) (hparMin : 0 < parMin) (hparamDim : 2 ≤ Fintype.card J)
    (hparSide : ∀ j, parMin ≤ ((parHi j - parLo j : ℤ) : ℝ))
    (hparWidth : ∀ j, parHi j - parLo j ≤ (R : ℤ))
    (hwidthRatio : (R : ℝ) ≤ Cwidth * parMin) (hrelative : c * L ≤ parMin)
    (winLo winHi : Option J × I → ℤ) (hwin : ∀ i, winLo i < winHi i)
    (hwinScale : ∀ i, smoothPairCoefficientScale (H i.2) L i.1 ≤
      K * ((winHi i - winLo i : ℤ) : ℝ))
    (v : (Option J × I → ℤ) → ℝ) (hv : ∀ z, 0 ≤ v z ∧ v z ≤ 1) :
    let F := (3 * K) ^ Fintype.card (Option J × I)
    let E := (2 : ℝ) ^ (Fintype.card I + 1) * A ^ Fintype.card I
    let tol := weightedReplacementTolerance F E epsilon
    let B := integerBoxGcdCutoff (Fintype.card J) Cwidth tol
    let Q := D * B
    let κ := integerBoxRetainedGap (Fintype.card J) D c tol
    ∀ (hparamScale : integerBoxPairScale (Fintype.card J) Cwidth tol ≤ parMin)
      (hQlog : (Q : ℝ) ≤ Real.exp modLog)
      (hsize : ∀ i, physicalReplacementScaleThreshold (Fintype.card I) k0 Q C κ A tol degree modLog dimLog *
        L ^ exponent ≤ H i)
      (hQdegree : Q ≤ 2 ^ degree),
    let W := Fintype.piFinset (fun i => Finset.Ico (winLo i) (winHi i))
    ∀ (hW : ∀ z ∈ W, ∀ i, |(z i : ℝ) - (origin i : ℝ)| ≤ smoothPairCoefficientScale (H i.2) L i.1 / 2),
    let rho := physicalPairGridAccuracy (Fintype.card I) k0 C κ A tol
    let sc := fun i => physicalReplacementScaleThreshold_conditions (Fintype.card I) k0 Q C κ degree modLog dimLog
      (zero_le_one.trans hC) hA (weightedReplacementTolerance_pos (by positivity) heps)
      hL hexponent (hsize i) (hupper i)
    let hlarge := fun i => (sc i).2.2.1
    let hwhole := fun i => (sc i).2.2.2.2.2.2
    let P := normalizedBoxPartitions N H rho hlarge hwhole
    let hpos := normalizedBoxPartitions_positive N H rho hlarge hwhole
    |𝔼 z ∈ W, v z * (𝔼 t : (∀ j, Finset.Ico (parLo j) (parHi j)),
      physicalBoxResidual lo N P hpos (boundedPrimePower Q) degree f
        (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) z))| ≤ epsilon := by
  intro F E tol B Q κ hparamScale hQlog hsize hQdegree W hW
  let r := ⌊integerBoxNearRatio (Fintype.card J) tol * parMin⌋₊
  have hF : 0 ≤ F := by positivity
  have hE : 0 ≤ E := by positivity
  have htol : 0 < tol := weightedReplacementTolerance_pos hE heps
  have hgap := integerBoxRetainedGap_spec (Fintype.card J) D hD hc htol hrelative
  have hB := (integerBoxGcdCutoff_spec (Fintype.card J) (C := Cwidth) htol).1
  have h := allocated_weighted_physical_replacement_s2 k0 D r anchor parLo parHi hpar H Q
    hL hC hgap.1 hA htol hleft hright hgap.2 origin lo N degree exponent hexponent f hf
    modLog dimLog hmodLog hQlog hdim hupper hratio hsize hQdegree B R le_rfl hB hparamDim
    parMin hparMin hparSide hparWidth W hW v hv
  have hH (i : I) : 0 < H i :=
    (physicalReplacementScaleThreshold_conditions (Fintype.card I) k0 Q C κ degree modLog dimLog
      (zero_le_one.trans hC) hA htol hL hexponent (hsize i) (hupper i)).1
  have hfactor := integerIntervalBox_window_factor_le winLo winHi hwin
    (fun i : Option J × I => smoothPairCoefficientScale (H i.2) L i.1)
    (fun i => (smoothPairCoefficientScale_pos (hH i.2) (zero_lt_one.trans_le hL) i.1).le) hwinScale
  have hfinal := cutoff_weighted_replacement_bound (Fintype.card J) R hparamDim hF hE hCwidth heps
    hparamScale hwidthRatio
  exact h.trans ((mul_le_mul_of_nonneg_right hfactor (Real.sqrt_nonneg _)).trans hfinal)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PrimeFamilyCutoff
namespace OAI

section

namespace Erdos3

theorem boundedPrimeFamily_log_bounds (Q : ℕ) {P : ℝ} (hQ : (Q : ℝ) ≤ Real.exp P) :
    (Fintype.card (BoundedPrime Q) : ℝ) ≤ Real.exp P ∧
      ∀ p : BoundedPrime Q, (boundedPrimePower Q p : ℝ) ≤ Real.exp P := by
  exact ⟨(Nat.cast_le.mpr (boundedPrime_card_le Q)).trans hQ,
    fun p => (Nat.cast_le.mpr (boundedPrimePower_le Q p)).trans hQ⟩

theorem nat_le_two_pow_of_le_exp {Q b : ℕ} {P : ℝ}
    (hQ : (Q : ℝ) ≤ Real.exp P) (hPb : 2 * P ≤ (b : ℝ)) : Q ≤ 2 ^ b := by
  have hlog : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hP : P ≤ (b : ℝ) * Real.log 2 := by nlinarith
  have he : Real.exp P ≤ (2 : ℝ) ^ b := by
    calc
      _ ≤ Real.exp ((b : ℝ) * Real.log 2) := Real.exp_le_exp.mpr hP
      _ = _ := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  exact_mod_cast hQ.trans he

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.InitialBudgetJointReplacement
namespace OAI

section

namespace Erdos3

theorem parameter_min_of_log_scale {c P R L M : ℝ} (hc : 0 < c)
    (hcinv : c⁻¹ ≤ Real.exp P) (hL : Real.exp (R + P) ≤ L) (hrelative : c * L ≤ M) :
    Real.exp R ≤ M := by
  have hdiv : Real.exp R / c ≤ L := by
    calc
      _ = Real.exp R * c⁻¹ := div_eq_mul_inv _ _
      _ ≤ Real.exp R * Real.exp P := mul_le_mul_of_nonneg_left hcinv (Real.exp_nonneg _)
      _ = Real.exp (R + P) := (Real.exp_add _ _).symm
      _ ≤ L := hL
  have h := (div_le_iff₀ hc).mp hdiv
  exact h.trans (by simpa only [mul_comm] using hrelative)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem initial_budget_weighted_physical_replacement {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (k0 : J) (D : ℕ) (anchor parLo parHi : J → ℤ) (hpar : ∀ j, parLo j < parHi j)
    (H : I → ℝ) {L C A epsilon K c Cwidth : ℝ}
    (hL : 1 ≤ L) (hC : 1 ≤ C) (hA : 0 ≤ A) (heps : 0 < epsilon)
    (hK : 0 ≤ K) (hc : 0 < c) (hCwidth : 0 ≤ Cwidth) (hD : 0 < D)
    (hleft : ∀ j, |((anchor j + (D : ℤ) * parLo j : ℤ) : ℝ) / L| ≤ C)
    (hright : ∀ j, |((anchor j + (D : ℤ) * parHi j : ℤ) : ℝ) / L| ≤ C)
    (origin : Option J × I → ℤ) (lo : I → ℤ) (N : I → ℕ)
    (degree exponent : ℕ) (hexponent : 2 ≤ exponent)
    (f : (I → ℤ) → ℝ) (hf : ∀ x ∈ translatedIntegerBox lo N, 0 ≤ f x ∧ f x ≤ 1)
    (P0 : ℝ) (hP0 : 0 ≤ P0)
    (hdim0 : (Fintype.card I : ℝ) ≤ Real.exp P0)
    (hparamLog : (Fintype.card J : ℝ) ≤ Real.exp P0)
    (hDlog : (D : ℝ) ≤ Real.exp P0) (hKlog : K ≤ Real.exp P0)
    (hAlog : A ≤ Real.exp P0) (hClog : C ≤ Real.exp P0)
    (hWidthlog : Cwidth ≤ Real.exp P0) (hcinv : c⁻¹ ≤ Real.exp P0)
    (hepsinv : epsilon⁻¹ ≤ Real.exp P0)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P0)
    (hupper : ∀ i, H i ≤ 2 * (N i : ℝ)) (hratio : ∀ i, (N i : ℝ) ≤ A * H i)
    (R : ℕ) (parMin : ℝ) (hparMin : 0 < parMin) (hparamDim : 2 ≤ Fintype.card J)
    (hparSide : ∀ j, parMin ≤ ((parHi j - parLo j : ℤ) : ℝ))
    (hparWidth : ∀ j, parHi j - parLo j ≤ (R : ℤ))
    (hwidthRatio : (R : ℝ) ≤ Cwidth * parMin) (hrelative : c * L ≤ parMin)
    (winLo winHi : Option J × I → ℤ) (hwin : ∀ i, winLo i < winHi i)
    (hwinScale : ∀ i, smoothPairCoefficientScale (H i.2) L i.1 ≤
      K * ((winHi i - winLo i : ℤ) : ℝ))
    (v : (Option J × I → ℤ) → ℝ) (hv : ∀ z, 0 ≤ v z ∧ v z ≤ 1) :
    let F := (3 * K) ^ Fintype.card (Option J × I)
    let E := (2 : ℝ) ^ (Fintype.card I + 1) * A ^ Fintype.card I
    let tol := weightedReplacementTolerance F E epsilon
    let B := integerBoxGcdCutoff (Fintype.card J) Cwidth tol
    let Q := D * B
    let κ := integerBoxRetainedGap (Fintype.card J) D c tol
    let Z := replacementCommonInputLog (Fintype.card (Option J × I)) (Fintype.card I) (Fintype.card J) P0
    ∀ (hLlog : Real.exp (Z + P0) ≤ L) (hdegree : 2 * Z ≤ (degree : ℝ))
      (hsizeExp : ∀ i, Real.exp (2 * physicalReplacementThresholdLog (Fintype.card I)
        (Fintype.card {j : J // j ≠ k0}) degree Z + 16) * L ^ exponent ≤ H i),
    let W := Fintype.piFinset (fun i => Finset.Ico (winLo i) (winHi i))
    ∀ (hW : ∀ z ∈ W, ∀ i, |(z i : ℝ) - (origin i : ℝ)| ≤ smoothPairCoefficientScale (H i.2) L i.1 / 2),
    let hsize := fun i => (mul_le_mul_of_nonneg_right
      (selectedPhysicalReplacementThreshold_le_exp (Fintype.card (Option J × I)) (Fintype.card I)
        degree k0 D hP0 hK hA (zero_le_one.trans hC) hCwidth hc heps hD hdim0 hparamLog
        hDlog hKlog hAlog hClog hWidthlog hcinv hepsinv hprofile)
      (pow_nonneg (zero_le_one.trans hL) exponent)).trans (hsizeExp i)
    let rho := physicalPairGridAccuracy (Fintype.card I) k0 C κ A tol
    let sc := fun i => physicalReplacementScaleThreshold_conditions (Fintype.card I) k0 Q C κ degree Z Z
      (zero_le_one.trans hC) hA (weightedReplacementTolerance_pos (by positivity) heps)
      hL hexponent (hsize i) (hupper i)
    let hlarge := fun i => (sc i).2.2.1
    let hwhole := fun i => (sc i).2.2.2.2.2.2
    let P := normalizedBoxPartitions N H rho hlarge hwhole
    let hpos := normalizedBoxPartitions_positive N H rho hlarge hwhole
    |𝔼 z ∈ W, v z * (𝔼 t : (∀ j, Finset.Ico (parLo j) (parHi j)),
      physicalBoxResidual lo N P hpos (boundedPrimePower Q) degree f
        (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) z))| ≤ epsilon := by
  intro F E tol B Q κ Z hLlog hdegree hsizeExp W hW
  have hz := replacementCommonInputLog_bounds (Fintype.card (Option J × I)) (Fintype.card I)
    (Fintype.card J) hP0
  obtain ⟨_, _, _, _, hq, hs⟩ := replacement_selected_parameter_bounds
    (Fintype.card (Option J × I)) (Fintype.card I) (Fintype.card J) D
    hP0 hK hA hCwidth hc heps hD hDlog hKlog hAlog hWidthlog hcinv hepsinv
  have hparScale := hs.trans (parameter_min_of_log_scale hc hcinv hLlog hrelative)
  have hQdegree := nat_le_two_pow_of_le_exp hq hdegree
  have hdim : (Fintype.card I : ℝ) ≤ Real.exp Z :=
    hdim0.trans (Real.exp_le_exp.mpr hz.2.1)
  have hT := selectedPhysicalReplacementThreshold_le_exp (Fintype.card (Option J × I)) (Fintype.card I)
        degree k0 D hP0 hK hA (zero_le_one.trans hC) hCwidth hc heps hD hdim0 hparamLog
        hDlog hKlog hAlog hClog hWidthlog hcinv hepsinv hprofile
  have hsize (i : I) := (mul_le_mul_of_nonneg_right hT
    (pow_nonneg (zero_le_one.trans hL) exponent)).trans (hsizeExp i)
  exact small_weighted_physical_replacement k0 D anchor parLo parHi hpar H hL hC hA heps hK hc hCwidth hD
    hleft hright origin lo N degree exponent hexponent f hf Z Z hz.1 hdim hupper hratio R parMin hparMin
    hparamDim hparSide hparWidth hwidthRatio hrelative winLo winHi hwin hwinScale v hv
    hparScale hq hsize hQdegree hW

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem initial_budget_joint_physical_replacement {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (k0 : J) (D : ℕ) (anchor parLo parHi : J → ℤ) (hpar : ∀ j, parLo j < parHi j)
    (H : I → ℝ) {L C A epsilon K c Cwidth : ℝ}
    (hL : 1 ≤ L) (hC : 1 ≤ C) (hA : 0 ≤ A) (heps : 0 < epsilon)
    (hK : 0 ≤ K) (hc : 0 < c) (hCwidth : 0 ≤ Cwidth) (hD : 0 < D)
    (hleft : ∀ j, |((anchor j + (D : ℤ) * parLo j : ℤ) : ℝ) / L| ≤ C)
    (hright : ∀ j, |((anchor j + (D : ℤ) * parHi j : ℤ) : ℝ) / L| ≤ C)
    (origin : Option J × I → ℤ) (lo : I → ℤ) (N : I → ℕ)
    (degree exponent : ℕ) (hexponent : 2 ≤ exponent)
    (f : (I → ℤ) → ℝ) (hf : ∀ x ∈ translatedIntegerBox lo N, 0 ≤ f x ∧ f x ≤ 1)
    (P0 : ℝ) (hP0 : 0 ≤ P0)
    (hdim0 : (Fintype.card I : ℝ) ≤ Real.exp P0)
    (hparamLog : (Fintype.card J : ℝ) ≤ Real.exp P0)
    (hDlog : (D : ℝ) ≤ Real.exp P0) (hKlog : K ≤ Real.exp P0)
    (hAlog : A ≤ Real.exp P0) (hClog : C ≤ Real.exp P0)
    (hWidthlog : Cwidth ≤ Real.exp P0) (hcinv : c⁻¹ ≤ Real.exp P0)
    (hepsinv : epsilon⁻¹ ≤ Real.exp P0)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P0)
    (hupper : ∀ i, H i ≤ 2 * (N i : ℝ)) (hratio : ∀ i, (N i : ℝ) ≤ A * H i)
    (R : ℕ) (parMin : ℝ) (hparMin : 0 < parMin) (hparamDim : 2 ≤ Fintype.card J)
    (hparSide : ∀ j, parMin ≤ ((parHi j - parLo j : ℤ) : ℝ))
    (hparWidth : ∀ j, parHi j - parLo j ≤ (R : ℤ))
    (hwidthRatio : (R : ℝ) ≤ Cwidth * parMin) (hrelative : c * L ≤ parMin)
    (winLo winHi : Option J × I → ℤ) (hwin : ∀ i, winLo i < winHi i)
    (hwinScale : ∀ i, smoothPairCoefficientScale (H i.2) L i.1 ≤
      K * ((winHi i - winLo i : ℤ) : ℝ))
    (v : (Option J × I → ℤ) → ℝ) (hv : ∀ z : (∀ i, Finset.Ico (winLo i) (winHi i)),
      0 ≤ v (fun i => (z i).val) ∧ v (fun i => (z i).val) ≤ 1) :
    let F := (3 * K) ^ Fintype.card (Option J × I)
    let E := (2 : ℝ) ^ (Fintype.card I + 1) * A ^ Fintype.card I
    let tol := weightedReplacementTolerance F E epsilon
    let B := integerBoxGcdCutoff (Fintype.card J) Cwidth tol
    let Q := D * B
    let κ := integerBoxRetainedGap (Fintype.card J) D c tol
    let Z := replacementCommonInputLog (Fintype.card (Option J × I)) (Fintype.card I) (Fintype.card J) P0
    ∀ (hLlog : Real.exp (Z + P0) ≤ L) (hdegree : 2 * Z ≤ (degree : ℝ))
      (hsizeExp : ∀ i, Real.exp (2 * physicalReplacementThresholdLog (Fintype.card I)
        (Fintype.card {j : J // j ≠ k0}) degree Z + 16) * L ^ exponent ≤ H i),
    let W := Fintype.piFinset (fun i => Finset.Ico (winLo i) (winHi i))
    ∀ (hW : ∀ z ∈ W, ∀ i, |(z i : ℝ) - (origin i : ℝ)| ≤ smoothPairCoefficientScale (H i.2) L i.1 / 2),
    let hsize := fun i => (mul_le_mul_of_nonneg_right
      (selectedPhysicalReplacementThreshold_le_exp (Fintype.card (Option J × I)) (Fintype.card I)
        degree k0 D hP0 hK hA (zero_le_one.trans hC) hCwidth hc heps hD hdim0 hparamLog
        hDlog hKlog hAlog hClog hWidthlog hcinv hepsinv hprofile)
      (pow_nonneg (zero_le_one.trans hL) exponent)).trans (hsizeExp i)
    let rho := physicalPairGridAccuracy (Fintype.card I) k0 C κ A tol
    let sc := fun i => physicalReplacementScaleThreshold_conditions (Fintype.card I) k0 Q C κ degree Z Z
      (zero_le_one.trans hC) hA (weightedReplacementTolerance_pos (by positivity) heps)
      hL hexponent (hsize i) (hupper i)
    let hlarge := fun i => (sc i).2.2.1
    let hwhole := fun i => (sc i).2.2.2.2.2.2
    let P := normalizedBoxPartitions N H rho hlarge hwhole
    let hpos := normalizedBoxPartitions_positive N H rho hlarge hwhole
    |((integerBoxUniformWeights parLo parHi hpar).prod
      (integerBoxUniformWeights winLo winHi hwin)).mean
        (fun tz => v (fun i => (tz.2 i).val) *
          physicalBoxResidual lo N P hpos (boundedPrimePower Q) degree f
            (smoothAffineSample (fun j => anchor j + (D : ℤ) * (tz.1 j).val)
              (fun i => (tz.2 i).val)))| ≤ epsilon := by
  intro F E tol B Q κ Z hLlog hdegree hsizeExp W hW hsize rho sc hlarge hwhole P hpos
  apply integerBox_joint_error_of_window_tests winLo winHi hwin parLo parHi hpar
    (fun z t => physicalBoxResidual lo N P hpos (boundedPrimePower Q) degree f
      (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) z)) epsilon ?_ v hv
  intro v' hv'
  exact initial_budget_weighted_physical_replacement k0 D anchor parLo parHi hpar H
    hL hC hA heps hK hc hCwidth hD hleft hright origin lo N degree exponent hexponent f hf
    P0 hP0 hdim0 hparamLog hDlog hKlog hAlog hClog hWidthlog hcinv hepsinv hprofile
    hupper hratio R parMin hparMin hparamDim hparSide hparWidth hwidthRatio hrelative
    winLo winHi hwin hwinScale v' hv' hLlog hdegree hsizeExp hW

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCommonReferenceBudget
namespace OAI

section

namespace Erdos3

theorem affineCommonReferenceBudget_bounds {E : ℕ} (hE : 2 ≤ E) (epsilon : ℝ) {U : ℝ} (hU : 0 ≤ U) :
    0 ≤ affineCommonReferenceBudget E epsilon U ∧
    U ≤ affineCommonReferenceBudget E epsilon U ∧
    (⌈(affineReferenceInput epsilon U + 2) ^ E⌉₊ : ℝ) ≤ affineCommonReferenceBudget E epsilon U := by
  have hb := affineReferenceInput_bounds epsilon hU
  have hbase : 0 ≤ affineReferenceInput epsilon U + 2 := by linarith [hb.1]
  have hpow : affineReferenceInput epsilon U + 2 ≤ (affineReferenceInput epsilon U + 2) ^ E := by
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith : 1 ≤ affineReferenceInput epsilon U + 2)
      (show 1 ≤ E by omega)
  have hc := Nat.ceil_lt_add_one (by positivity : 0 ≤ (affineReferenceInput epsilon U + 2) ^ E)
  unfold affineCommonReferenceBudget
  exact ⟨by positivity, by linarith [hb.2.1], by linarith [hb.1]⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.SelectedPhysicalGridBudget
namespace OAI

section

namespace Erdos3

theorem selectedPhysicalGrid_inverse_le_exp {J : Type*} [Fintype J] [DecidableEq J]
    (m n : ℕ) (k : J) (D : ℕ) {K A C Cwidth c epsilon P : ℝ}
    (hP : 0 ≤ P) (hK0 : 0 ≤ K) (hA0 : 0 ≤ A) (hC0 : 0 ≤ C) (hCwidth0 : 0 ≤ Cwidth)
    (hc0 : 0 < c) (heps0 : 0 < epsilon) (hD : 0 < D)
    (hn : (n : ℝ) ≤ Real.exp P) (hcard : (Fintype.card J : ℝ) ≤ Real.exp P)
    (hDlog : (D : ℝ) ≤ Real.exp P) (hK : K ≤ Real.exp P) (hA : A ≤ Real.exp P)
    (hC : C ≤ Real.exp P) (hCwidth : Cwidth ≤ Real.exp P)
    (hc : c⁻¹ ≤ Real.exp P) (heps : epsilon⁻¹ ≤ Real.exp P)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) :
    let tol := weightedReplacementTolerance ((3 * K) ^ m) ((2 : ℝ) ^ (n + 1) * A ^ n) epsilon
    let _Q := D * integerBoxGcdCutoff (Fintype.card J) Cwidth tol
    let κ := integerBoxRetainedGap (Fintype.card J) D c tol
    let Z := replacementCommonInputLog m n (Fintype.card J) P
    (physicalPairGridAccuracy n k C κ A tol)⁻¹ ≤
      Real.exp (2 * physicalPairCoefficientLog n (Fintype.card {j : J // j ≠ k}) Z + 2) := by
  intro tol Q κ Z
  obtain ⟨ht, hti, hk, hki, hq, _⟩ := replacement_selected_parameter_bounds m n (Fintype.card J) D
    hP hK0 hA0 hCwidth0 hc0 heps0 hD hDlog hK hA hCwidth hc heps
  obtain ⟨hn', hcard', hC', hA', _, hrow', hpow'⟩ :=
    replacement_common_geometric_bounds m n k hP hn hcard hC hA hprofile
  exact (physicalPairPointGridAccuracy_inverse_le_exp n k Q
    (replacementCommonInputLog_bounds m n (Fintype.card J) hP).1 hC0 hk hA0 ht
    hn' hq hC' hki hA' hti hcard' hrow' hpow').2

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.IndexedComparableScalarGeometryData
namespace OAI

section

namespace Erdos3

theorem scalarTransferAllocatedLogs_bounds (b : ℕ) {common p Z U : ℝ}
    (hcommon : 0 ≤ common) (hp : 0 ≤ p) (hZ : 0 ≤ Z) (hU : 0 ≤ U) :
    0 ≤ scalarTransferCapLog b Z ∧ 0 ≤ scalarTransferAccuracyLog b p Z ∧
    0 ≤ scalarTransferCellLog common b p Z U ∧
    65536 * (common + 3) ^ 4 ≤ scalarTransferCellLog common b p Z U ∧
    Z * b + scalarTransferAccuracyLog b p Z + U + 1 ≤ scalarTransferCellLog common b p Z U ∧
    Z * b + U + 1 ≤ scalarTransferCellLog common b p Z U := by
  have hc : 0 ≤ scalarTransferCapLog b Z := by unfold scalarTransferCapLog; positivity
  have ha : 0 ≤ scalarTransferAccuracyLog b p Z := by unfold scalarTransferAccuracyLog; positivity
  have hside : 0 ≤ 65536 * (common + 3) ^ 4 := by positivity
  have hb : 0 ≤ Z * (b : ℝ) := mul_nonneg hZ (Nat.cast_nonneg b)
  unfold scalarTransferCellLog
  exact ⟨hc, ha, by positivity, by linarith, by linarith, by linarith⟩

end Erdos3

end

section

namespace Erdos3

theorem scalarInitialReferenceInput_bounds (m n d : ℕ) {p P0 : ℝ} (hp : 0 ≤ p) (hP0 : 0 ≤ P0) :
    let Z := replacementCommonInputLog m n d P0
    let G := 2 * physicalPairCoefficientLog n d Z + 2
    let U := scalarInitialReferenceInput m n d p P0
    0 ≤ U ∧ Z ≤ U ∧ G + P0 + 2 ≤ U ∧ P0 ≤ U ∧
      (m : ℝ) ≤ U ∧ (n : ℝ) ≤ U ∧ (d : ℝ) ≤ U ∧ scalarTransferTail (3 * p) ≤ U ∧ p ≤ U := by
  intro Z G U
  have hZ : 0 ≤ Z := (replacementCommonInputLog_bounds m n d hP0).1
  have hG : 0 ≤ G := by
    have h := (physicalPairCoefficientLog_bounds n d hZ).1
    dsimp only [G]
    linarith
  have hT : 0 ≤ scalarTransferTail (3 * p) := by unfold scalarTransferTail; positivity
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  dsimp only [U, scalarInitialReferenceInput]
  dsimp only [G, Z] at hG hZ ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem physicalPairCoefficientLog_mono_dimension (n : ℕ) {d e : ℕ} {P : ℝ}
    (hde : d ≤ e) (hP : 0 ≤ P) : physicalPairCoefficientLog n d P ≤ physicalPairCoefficientLog n e P := by
  have hde' : (d : ℝ) ≤ e := by exact_mod_cast hde
  unfold physicalPairCoefficientLog smoothPairErrorLog smoothPairRowErrorLog
  gcongr

end Erdos3

end

section

namespace Erdos3

theorem physicalReplacementThresholdLog_mono_dimension (n b : ℕ) {d e : ℕ} {Z : ℝ}
    (hde : d ≤ e) (hZ : 0 ≤ Z) :
    physicalReplacementThresholdLog n d b Z ≤ physicalReplacementThresholdLog n e b Z := by
  have h := physicalPairCoefficientLog_mono_dimension n hde hZ
  unfold physicalReplacementThresholdLog
  linarith

theorem scalarCombinedLogThreshold_bounds (n d b : ℕ)
    {p P0 Z G refCost cellLog meshLog : ℝ}
    (hp : 0 ≤ p) (hP0 : 0 ≤ P0) (hZ : 0 ≤ Z) (hG : 0 ≤ G)
    (href : 0 ≤ refCost) (hcell : 0 ≤ cellLog) (hmesh : 0 ≤ meshLog) :
    let S := scalarCombinedLogThreshold n d b p P0 Z G refCost cellLog meshLog
    0 ≤ S ∧ refCost ≤ S ∧ p + scalarTransferTail (3 * p) + 4 ≤ S ∧
      Z + P0 ≤ S ∧ 2 * physicalReplacementThresholdLog n d b Z + 16 ≤ S ∧
      G + max refCost cellLog + 2 ≤ S ∧ 4 * meshLog + 18 + cellLog + Z + 2 ≤ S := by
  intro S
  have hT : 0 ≤ scalarTransferTail (3 * p) := by unfold scalarTransferTail; positivity
  have hR := (physicalReplacementThresholdLog_bounds n d b hZ).1
  have hmax : max refCost cellLog ≤ refCost + cellLog := max_le (by linarith) (by linarith)
  dsimp only [S, scalarCombinedLogThreshold]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem four_mul_exp_le_exp_add_two (x : ℝ) : 4 * Real.exp x ≤ Real.exp (x + 2) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hfour : (4 : ℝ) ≤ Real.exp 2 := by
    calc
      4 = (2 : ℝ) ^ 2 := by norm_num
      _ ≤ (Real.exp 1) ^ 2 := pow_le_pow_left₀ (by norm_num) htwo 2
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  calc
    _ ≤ Real.exp 2 * Real.exp x := mul_le_mul_of_nonneg_right hfour (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add, add_comm]

theorem scalarCombinedLogThreshold_size_conditions {I : Type*} (n d b exponent : ℕ)
    {p P0 Z G refCost cellLog meshLog budget L : ℝ} (H : I → ℝ)
    (hp : 0 ≤ p) (hP0 : 0 ≤ P0) (hZ : 0 ≤ Z) (hG : 0 ≤ G)
    (href : 0 ≤ refCost) (hcell : 0 ≤ cellLog) (hmesh : 0 ≤ meshLog)
    (hbudget : scalarCombinedLogThreshold n d b p P0 Z G refCost cellLog meshLog ≤ budget)
    (hL : Real.exp budget ≤ L) (hH : ∀ i, Real.exp budget * L ^ exponent ≤ H i) :
    1 ≤ L ∧ Real.exp (Z + P0) ≤ L ∧
    (∀ i, Real.exp (2 * physicalReplacementThresholdLog n d b Z + 16) * L ^ exponent ≤ H i) ∧
    (∀ i, 4 * Real.exp (G + max refCost cellLog) ≤ H i) ∧
    4 * Real.exp (4 * meshLog + 18 + cellLog + Z) ≤ L ∧
    (∀ i, 4 * Real.exp (4 * meshLog + 18 + cellLog) * L ^ exponent ≤ H i) := by
  obtain ⟨hS, _, _, hLP, hRP, hFP, hMP⟩ := scalarCombinedLogThreshold_bounds n d b hp hP0 hZ hG href hcell hmesh
  have hLone : 1 ≤ L := (Real.one_le_exp_iff.mpr (hS.trans hbudget)).trans hL
  have hpow : 1 ≤ L ^ exponent := one_le_pow₀ hLone
  have hHbase (i) : Real.exp budget ≤ H i := by
    have hf : Real.exp budget ≤ Real.exp budget * L ^ exponent := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow (Real.exp_nonneg budget)
    exact hf.trans (hH i)
  refine ⟨hLone, (Real.exp_le_exp.mpr (hLP.trans hbudget)).trans hL, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (hRP.trans hbudget))
      (pow_nonneg (zero_le_one.trans hLone) exponent)).trans (hH i)
  · intro i
    exact ((four_mul_exp_le_exp_add_two _).trans (Real.exp_le_exp.mpr (hFP.trans hbudget))).trans (hHbase i)
  · exact ((four_mul_exp_le_exp_add_two _).trans (Real.exp_le_exp.mpr (hMP.trans hbudget))).trans hL
  · intro i
    have hm : 4 * meshLog + 18 + cellLog + 2 ≤ budget := by linarith [hMP.trans hbudget]
    exact (mul_le_mul_of_nonneg_right ((four_mul_exp_le_exp_add_two _).trans (Real.exp_le_exp.mpr hm))
      (pow_nonneg (zero_le_one.trans hLone) exponent)).trans (hH i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ScalarMeshCoefficientBudget
namespace OAI

section

namespace Erdos3

theorem scalarMeshLog_bounds {G P T : ℝ} (hG : 0 ≤ G) (hP : 0 ≤ P) (hT : 0 ≤ T) :
    0 ≤ scalarMeshLog G P T ∧ P ≤ scalarMeshLog G P T ∧ T ≤ scalarMeshLog G P T ∧
      G + 3 * P + 40 ≤ scalarMeshLog G P T ∧ 2 * P + 3 ≤ scalarMeshLog G P T := by
  unfold scalarMeshLog
  exact ⟨by positivity, by linarith, by linarith, by linarith, by linarith⟩

theorem scalarMesh_boundary_bound {n A rho c G P T : ℝ}
    (hn : 0 ≤ n) (hA : 0 ≤ A) (hrho : 0 < rho) (hc : 0 < c)
    (hG : 0 ≤ G) (hP : 0 ≤ P) (hT : 0 ≤ T)
    (hnP : n ≤ Real.exp P) (hAP : A ≤ Real.exp P)
    (hrhoG : rho⁻¹ ≤ Real.exp G) (hcP : c⁻¹ ≤ Real.exp P) :
    40 * n * A / (rho * c) ≤ Real.exp (scalarMeshLog G P T) := by
  have h40 : (40 : ℝ) ≤ Real.exp 40 := by linarith [Real.add_one_le_exp (40 : ℝ)]
  have hproduct : 40 * n * A * rho⁻¹ * c⁻¹ ≤
      Real.exp 40 * Real.exp P * Real.exp P * Real.exp G * Real.exp P := by
    gcongr
  calc
    _ = 40 * n * A * rho⁻¹ * c⁻¹ := by rw [div_eq_mul_inv, mul_inv_rev]; ring
    _ ≤ _ := hproduct
    _ = Real.exp (G + 3 * P + 40) := by simp only [← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (scalarMeshLog_bounds hG hP hT).2.2.2.1

theorem scalarMesh_movement_bound {d C B G P T : ℝ}
    (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hG : 0 ≤ G) (hP : 0 ≤ P) (hT : 0 ≤ T)
    (hdP : d ≤ Real.exp P) (hCP : C ≤ Real.exp P) (hBP : B ≤ Real.exp P) :
    1 + d * (C + B) ≤ Real.exp (scalarMeshLog G P T) := by
  have hmul : d * (C + B) ≤ Real.exp P * (Real.exp P + Real.exp P) := by gcongr
  have h1 : 1 ≤ Real.exp (2 * P) := Real.one_le_exp_iff.mpr (by linarith)
  have h3 : (3 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  have heq : Real.exp P * (Real.exp P + Real.exp P) = 2 * Real.exp (2 * P) := by
    rw [show 2 * P = P + P by ring, Real.exp_add]; ring
  rw [heq] at hmul
  calc
    _ ≤ 3 * Real.exp (2 * P) := by linarith
    _ ≤ Real.exp 3 * Real.exp (2 * P) := mul_le_mul_of_nonneg_right h3 (Real.exp_nonneg _)
    _ = Real.exp (2 * P + 3) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (scalarMeshLog_bounds hG hP hT).2.2.2.2

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnconditionedSmoothSlopeCap
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem selectedResidueSmoothPMF_one {K I : Type*} [Fintype K] [Fintype I]
    (W : K × I → ℝ) (hW : ∀ t, 0 < W t)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ => 1) {0} W z) :
    selectedResidueSmoothPMF (fun _ => 1) {0} W hW hZ =
      shiftedSmoothProductPMF 0 W hW ((selectedResidueSmoothMass_one W) ▸ hZ) := by
  ext z
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [selectedResidueSmoothPMF_toReal, shiftedSmoothProductPMF_toReal,
    selectedResidueSmoothWeight_one, selectedResidueSmoothMass_one]

theorem independentProductPMF_slopes {K I X : Type*} [Fintype K] [Fintype I]
    [Countable X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (p : Option K × I → PMF X) :
    (independentProductPMF p).map (fun z => fun t : K × I => z (some t.1,t.2)) =
      independentProductPMF (fun t : K × I => p (some t.1,t.2)) := by
  rw [independentProductPMF_base_split, PMF.map_bind]
  simp only [PMF.map_comp]
  have hconst (tail : K × I → X) :
      (independentProductPMF (fun i => p (none,i))).map
        ((fun z => fun t : K × I => z (some t.1,t.2)) ∘ baseArrayJoin tail) =
      PMF.pure tail := by
    have he : ((fun z => fun t : K × I => z (some t.1,t.2)) ∘ baseArrayJoin tail) =
        Function.const (I → X) tail := by
      funext z t
      rcases t with ⟨k,i⟩
      rfl
    rw [he, PMF.map_const]
  simp only [hconst, PMF.bind_pure]

theorem shiftedSmoothProductPMF_slopes_cap {K I : Type*} [Fintype K] [Fintype I]
    (a W : Option K × I → ℝ) (hW : ∀ t, 0 < W t)
    (hZ : 0 < shiftedSmoothProductMass a W)
    (hlarge : ∀ t : K × I, 8 * (probabilityProfileLipschitz : ℝ) ≤ W (some t.1,t.2))
    (y : K × I → ℤ) :
    (((shiftedSmoothProductPMF a W hW hZ).map
      (fun z => fun t : K × I => z (some t.1,t.2))) y).toReal ≤
      ∏ t : K × I, 2 / W (some t.1,t.2) := by
  rw [shiftedSmoothProductPMF_eq_independent, independentProductPMF_slopes,
    independentProductPMF_toReal]
  exact Finset.prod_le_prod (fun _ _ => ENNReal.toReal_nonneg)
    (fun t _ => shiftedSmoothCoefficientPMF_le (a (some t.1,t.2)) (hlarge t) (y t))

theorem selectedResidueFiniteLaw_one_slopes_cap {K I : Type*} [Fintype K] [Fintype I]
    (W : Option K × I → ℝ) (hW : ∀ t, 0 < W t)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ => 1) {0} W z)
    (hlarge : ∀ t : K × I, 8 * (probabilityProfileLipschitz : ℝ) ≤ W (some t.1,t.2))
    (y : K → I → ℤ) :
    (selectedResidueFiniteLaw (fun _ => 1) {0} W hW hZ).mean
      (fun z => if (fun k i => z.val (some k,i)) = y then 1 else 0) ≤
      ∏ t : K × I, 2 / W (some t.1,t.2) := by
  have he (z : Option K × I → ℤ) :
      ((fun k i => z (some k,i)) = y) ↔
      ((fun t : K × I => z (some t.1,t.2)) = fun t => y t.1 t.2) := by
    simp only [funext_iff, Prod.forall]
  simp_rw [he]
  rw [selectedResidueFiniteLaw_mean (fun _ => 1) {0} W hW hZ
    (fun z => if (fun t : K × I => z (some t.1,t.2)) = (fun t => y t.1 t.2) then 1 else 0),
    ← pmf_map_toReal_indicator, selectedResidueSmoothPMF_one]
  exact shiftedSmoothProductPMF_slopes_cap 0 W hW _ hlarge (fun t => y t.1 t.2)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerBoxUniformWeightVolume
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I]

theorem integerBox_volume_pos (lo hi : I → ℤ) (hlen : ∀ i, lo i < hi i) :
    0 < ∏ i, ((hi i - lo i : ℤ) : ℝ) := by
  apply Finset.prod_pos
  intro i _
  exact_mod_cast sub_pos.mpr (hlen i)

theorem integerBoxUniformWeights_weight_eq_inv_volume
    [DecidableEq I]
    (lo hi : I → ℤ) (hlen : ∀ i, lo i < hi i)
    (y : ∀ i, Finset.Ico (lo i) (hi i)) :
    (integerBoxUniformWeights lo hi hlen).weight y =
      (∏ i, ((hi i - lo i : ℤ) : ℝ))⁻¹ := by
  change (∏ i, (Fintype.card (Finset.Ico (lo i) (hi i)) : ℝ)⁻¹) = _
  rw [Finset.prod_inv_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [Fintype.card_coe, Int.card_Ico]
  exact_mod_cast Int.toNat_of_nonneg (sub_nonneg.mpr (hlen i).le)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.UnconditionedJointFrameDomination
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open FiniteProbabilityWeights
open scoped BigOperators Classical

theorem jointIntegerFrame_uniform_base_cap_at {K I : Type*}
    [Fintype K] [Fintype I]
    (A : Finset (I → ℤ)) (hA : A.Nonempty)
    (noise y : Option K × I → ℤ) :
    (uniformFinset A hA).mean
      (fun a => if jointIntegerFrame (a.val, noise) = (fun k i => y (k, i)) then 1 else 0) ≤
      (A.card : ℝ)⁻¹ *
        (if (fun k i => noise (some k, i)) = (fun k i => y (some k, i)) then 1 else 0) := by
  by_cases hslope : (fun k i => noise (some k, i)) = (fun k i => y (some k, i))
  · simp only [hslope, ite_true, mul_one]
    by_cases hex : ∃ a : A, jointIntegerFrame (a.val, noise) = (fun k i => y (k, i))
    · obtain ⟨a, ha⟩ := hex
      have heq (b : A) :
          jointIntegerFrame (b.val, noise) = (fun k i => y (k, i)) ↔ b = a := by
        constructor
        · intro hb
          apply Subtype.ext
          funext i
          have h := congrFun (congrFun (hb.trans ha.symm) none) i
          exact add_right_cancel h
        · rintro rfl
          exact ha
      simp only [mean, heq, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true]
      exact (uniformFinset_weight A hA a).le
    · have hn (a : A) : jointIntegerFrame (a.val, noise) ≠ (fun k i => y (k, i)) :=
        fun ha => hex ⟨a, ha⟩
      simp only [hn, ite_false, mean_const]
      positivity
  · have hn (a : A) : jointIntegerFrame (a.val, noise) ≠ (fun k i => y (k, i)) := by
      intro ha
      apply hslope
      funext k i
      exact congrFun (congrFun ha (some k)) i
    simp only [hn, ite_false, mean_const, hslope, mul_zero, le_refl]

theorem jointIntegerFrame_uniform_base_cap {K I Ω : Type*}
    [Fintype K] [Fintype I] [Fintype Ω]
    (A : Finset (I → ℤ)) (hA : A.Nonempty)
    (q : FiniteProbabilityWeights Ω)
    (noise : Ω → (Option K × I → ℤ)) (y : Option K × I → ℤ) :
    ((uniformFinset A hA).prod q).mean
      (fun z => if jointIntegerFrame (z.1.val, noise z.2) = (fun k i => y (k, i))
        then 1 else 0) ≤
      (A.card : ℝ)⁻¹ * q.mean
        (fun z => if (fun k i => noise z (some k, i)) = (fun k i => y (some k, i))
          then 1 else 0) := by
  rw [mean_prod]
  calc
    _ = q.mean (fun z => (uniformFinset A hA).mean
        (fun a => if jointIntegerFrame (a.val, noise z) = (fun k i => y (k, i))
          then 1 else 0)) := by
      simp only [mean, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ ≤ q.mean (fun z => (A.card : ℝ)⁻¹ *
        (if (fun k i => noise z (some k, i)) = (fun k i => y (some k, i))
          then 1 else 0)) :=
      q.mean_mono (fun z => jointIntegerFrame_uniform_base_cap_at A hA (noise z) y)
    _ = _ := by
      simp only [mean, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel
open scoped BigOperators Classical

variable {K I : Type*} [Fintype K] [Fintype I]

theorem selectedJointReference_frame_cap
    (bases : Finset (I → ℤ)) (hbases : bases.Nonempty)
    (width : Option K × I → ℝ) (hwidth : ∀ t, 0 < width t)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ => 1) {0} width z)
    (hscale : ∀ t : K × I, 8 * (probabilityProfileLipschitz : ℝ) ≤ width (some t.1,t.2))
    (y : Option K × I → ℤ) :
    (selectedJointReference bases hbases (fun _ => 1) {0} width hwidth hZ).mean
      (fun z => if jointIntegerFrame (z.1.val,z.2.val) = (fun k i => y (k,i)) then 1 else 0) ≤
      (bases.card : ℝ)⁻¹ * ∏ t : K × I, 2 / width (some t.1,t.2) := by
  have hbase := jointIntegerFrame_uniform_base_cap bases hbases
    (selectedResidueFiniteLaw (fun _ => 1) {0} width hwidth hZ) (fun z => z.val) y
  exact hbase.trans (mul_le_mul_of_nonneg_left
    (selectedResidueFiniteLaw_one_slopes_cap width hwidth hZ hscale (fun k i => y (some k,i)))
    (inv_nonneg.mpr (Nat.cast_nonneg _)))

theorem selectedJointReference_frame_box_domination
    (bases : Finset (I → ℤ)) (hbases : bases.Nonempty)
    (width : Option K × I → ℝ) (hwidth : ∀ t, 0 < width t)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ => 1) {0} width z)
    (hscale : ∀ t : K × I, 8 * (probabilityProfileLipschitz : ℝ) ≤ width (some t.1,t.2))
    (sourceLo sourceHi : Option K × I → ℤ) (hsource : ∀ t, sourceLo t < sourceHi t)
    (hframe : ∀ z : bases × rectangularWeightIndices 0 width 1, ∀ t,
      jointIntegerFrame (z.1.val,z.2.val) t.1 t.2 ∈ Finset.Ico (sourceLo t) (sourceHi t))
    {p : ℝ}
    (hbudget : (∏ t, ((sourceHi t - sourceLo t : ℤ) : ℝ)) *
      ((bases.card : ℝ)⁻¹ * ∏ t : K × I, 2 / width (some t.1,t.2)) ≤ Real.exp p)
    (y : ∀ t, Finset.Ico (sourceLo t) (sourceHi t)) :
    ((selectedJointReference bases hbases (fun _ => 1) {0} width hwidth hZ).fiberLaw
      (selectedJointFrameBoxMap bases width sourceLo sourceHi hframe)).weight y ≤
      Real.exp p * (integerBoxUniformWeights sourceLo sourceHi hsource).weight y := by
  rw [FiniteProbabilityWeights.fiberLaw_weight]
  unfold FiniteProbabilityWeights.fiberMean
  have he (z : bases × rectangularWeightIndices 0 width 1) :
      selectedJointFrameBoxMap bases width sourceLo sourceHi hframe z = y ↔
      jointIntegerFrame (z.1.val,z.2.val) = (fun k i => (y (k,i)).val) := by
    constructor
    · intro h
      funext k i
      exact congrArg Subtype.val (congrFun h (k,i))
    · intro h
      funext t
      apply Subtype.ext
      exact congrFun (congrFun h t.1) t.2
  simp_rw [he]
  apply (selectedJointReference_frame_cap bases hbases width hwidth hZ hscale
    (fun t => (y t).val)).trans
  rw [integerBoxUniformWeights_weight_eq_inv_volume]
  have hv := integerBox_volume_pos sourceLo sourceHi hsource
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ hv).mpr
  rw [mul_comm]
  exact hbudget

theorem selectedJointReference_frame_box_eventProbability
    (bases : Finset (I → ℤ)) (hbases : bases.Nonempty)
    (width : Option K × I → ℝ) (hwidth : ∀ t, 0 < width t)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ => 1) {0} width z)
    (sourceLo sourceHi : Option K × I → ℤ)
    (hframe : ∀ z : bases × rectangularWeightIndices 0 width 1, ∀ t,
      jointIntegerFrame (z.1.val,z.2.val) t.1 t.2 ∈ Finset.Ico (sourceLo t) (sourceHi t))
    (event : (∀ t, Finset.Ico (sourceLo t) (sourceHi t)) → Prop) :
    ((selectedJointReference bases hbases (fun _ => 1) {0} width hwidth hZ).fiberLaw
      (selectedJointFrameBoxMap bases width sourceLo sourceHi hframe)).eventProbability event =
    (selectedJointReference bases hbases (fun _ => 1) {0} width hwidth hZ).eventProbability
      (fun z => event (selectedJointFrameBoxMap bases width sourceLo sourceHi hframe z)) :=
  FiniteProbabilityWeights.fiberLaw_mean _ _ _

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.InitialReplacementMeshWidths
namespace OAI

section

namespace Erdos3

theorem baseWidth_of_upper_ratio {H width K : ℝ}
    (hwidth : 0 ≤ width) (hK : 0 ≤ K) (h : H ≤ K * width) :
    (K + 1)⁻¹ * H ≤ width := by
  have hden : 0 < K + 1 := by positivity
  have hmul : H ≤ width * (K + 1) := by nlinarith
  simpa only [div_eq_mul_inv, mul_comm] using (div_le_iff₀ hden).mpr hmul

theorem parameterWidth_of_relative {L width c : ℝ} {D : ℕ}
    (hL : 0 ≤ L) (hc : 0 < c) (hD : 0 < D) (h : c * L ≤ width) :
    L / (D : ℝ) ≤ c⁻¹ * width := by
  have hDr : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < D := by linarith
  have hdiv : L / (D : ℝ) ≤ L := (div_le_iff₀ hDpos).mpr (by nlinarith)
  have hrel : L ≤ width / c := (le_div_iff₀ hc).mpr (by nlinarith)
  simpa only [div_eq_mul_inv, mul_comm] using hdiv.trans hrel

theorem initialReplacement_mesh_widths {I J : Type*}
    (sourceLo sourceHi : Option J × I → ℤ) (parLo parHi : J → ℤ)
    (hsource : ∀ z, sourceLo z < sourceHi z) (hparameter : ∀ j, parLo j < parHi j)
    (H : I → ℝ) {L K c : ℝ} {D : ℕ} (hL : 0 ≤ L) (hK : 0 ≤ K) (hc : 0 < c) (hD : 0 < D)
    (hsourceScale : ∀ z : Option J × I, smoothPairCoefficientScale (H z.2) L z.1 ≤
      K * ((sourceHi z - sourceLo z : ℤ) : ℝ))
    (hrelative : ∀ j, c * L ≤ ((parHi j - parLo j : ℤ) : ℝ)) :
    (∀ i, (K + 1)⁻¹ * H i ≤ ((sourceHi (none,i) - sourceLo (none,i) : ℤ) : ℝ)) ∧
    (∀ z : Option J × I, smoothPairCoefficientScale (H z.2) L z.1 ≤
      K * ((sourceHi z - sourceLo z).toNat : ℝ)) ∧
    (∀ j, L / (D : ℝ) ≤ c⁻¹ * ((parHi j - parLo j).toNat : ℝ)) := by
  have hs (z) : (((sourceHi z - sourceLo z).toNat : ℕ) : ℝ) = ((sourceHi z - sourceLo z : ℤ) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (sub_nonneg.mpr (hsource z).le)
  have ht (j) : (((parHi j - parLo j).toNat : ℕ) : ℝ) = ((parHi j - parLo j : ℤ) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (sub_nonneg.mpr (hparameter j).le)
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact baseWidth_of_upper_ratio (by exact_mod_cast (sub_nonneg.mpr (hsource (none,i)).le)) hK (hsourceScale (none,i))
  · intro z
    rw [hs]
    exact hsourceScale z
  · intro j
    rw [ht]
    exact parameterWidth_of_relative hL hc hD (hrelative j)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedMeshLengths
namespace OAI

section

namespace Erdos3

theorem normalizedMesh_scale_lower {delta scale inverseLog lengthLog : ℝ}
    (hdelta : 0 < delta) (hinv : delta⁻¹ ≤ Real.exp inverseLog)
    (hscale : 4 * Real.exp (inverseLog + lengthLog) ≤ scale) :
    Real.exp lengthLog ≤ delta * scale / 4 := by
  have hinv' := mul_le_mul_of_nonneg_left hinv hdelta.le
  rw [mul_inv_cancel₀ hdelta.ne'] at hinv'
  have hprod := mul_le_mul_of_nonneg_right hinv' (by positivity : 0 ≤ 4 * Real.exp lengthLog)
  have hsize := mul_le_mul_of_nonneg_left hscale hdelta.le
  rw [Real.exp_add] at hsize
  nlinarith

theorem normalizedMesh_scale_large {delta scale inverseLog lengthLog : ℝ}
    (hdelta : 0 < delta) (hinv : delta⁻¹ ≤ Real.exp inverseLog)
    (hlength : 0 ≤ lengthLog) (hscale : 4 * Real.exp (inverseLog + lengthLog) ≤ scale) :
    4 ≤ delta * scale := by
  have h := normalizedMesh_scale_lower hdelta hinv hscale
  have hone := Real.one_le_exp_iff.mpr hlength
  linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestScalarTransfer
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators Classical

universe u v

theorem exists_niltest_initial_scalar_transfer (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ {I : Type u} {V : Type v} {J : Type*}
      [Fintype I] [Fintype J] [LieRing V] [LieAlgebra ℚ V]
      [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [T2Space (ℝ ⊗[ℚ] V)]
      {d0 : ℕ} (nilmanifold : RationalFilteredNilmanifold V s d0)
      (p epsilon P0 level budget : ℝ),
    2 ≤ p → 0 < epsilon → epsilon ≤ 1 → 0 ≤ P0 → 3 * p + 10 ≤ P0 →
    epsilon⁻¹ ≤ Real.exp P0 → Real.exp (-p) ≤ level → level ≤ 2 →
    (Fintype.card I : ℝ) ≤ p → 2 ≤ Fintype.card J →
    (Fintype.card J : ℝ) ≤ Real.exp P0 →
    (probabilityProfileLipschitz : ℝ) ≤ Real.exp P0 →
    ∀ g : nilmanifold.Niltest (fun _ : I => 1), g.ComplexityLE p →
    ∀ (k0 : J) (D : ℕ) (anchor parLo parHi : J → ℤ) (hpar : ∀ j, parLo j < parHi j),
    0 < D → (D : ℝ) ≤ Real.exp P0 →
    ∀ (L C B A K c Cwidth : ℝ), 1 ≤ L → 1 ≤ C → 0 ≤ B → 0 ≤ A → 0 ≤ K → 0 < c → 0 ≤ Cwidth →
    C ≤ Real.exp P0 → B ≤ Real.exp P0 → A ≤ Real.exp P0 → K ≤ Real.exp P0 →
    c⁻¹ ≤ Real.exp P0 → Cwidth ≤ Real.exp P0 →
    ∀ (lo : I → ℤ) (N : I → ℕ) (H : I → ℝ),
    (∀ i, H i ≤ 2 * (N i : ℝ)) → (∀ i, (N i : ℝ) ≤ A * H i) →
    (∀ z ∈ translatedIntegerBox lo N, (g.eval z).im = 0 ∧ 0 ≤ (g.eval z).re ∧ (g.eval z).re ≤ 1) →
    ∀ h : (I → ℤ) → ℂ,
    (∀ z ∈ translatedIntegerBox lo N, 0 ≤ (h z).re ∧ (h z).re ≤ 1) →
    ResidueSliceUpperComparison h g.eval lo N budget level (Real.exp (-budget)) →
    ∀ (R : ℕ) (parMin : ℝ), 0 < parMin →
    (∀ j, parMin ≤ ((parHi j - parLo j : ℤ) : ℝ)) →
    (∀ j, parHi j - parLo j ≤ (R : ℤ)) → (R : ℝ) ≤ Cwidth * parMin → c * L ≤ parMin →
    (∀ j, |((anchor j + (D : ℤ) * parLo j : ℤ) : ℝ) / L| ≤ C) →
    (∀ j, |((anchor j + (D : ℤ) * parHi j : ℤ) : ℝ) / L| ≤ C) →
    ∀ (origin sourceLo sourceHi : Option J × I → ℤ) (hsource : ∀ z, sourceLo z < sourceHi z),
    (∀ z : Option J × I, smoothPairCoefficientScale (H z.2) L z.1 ≤
      K * ((sourceHi z - sourceLo z : ℤ) : ℝ)) →
    (∀ z ∈ Fintype.piFinset (fun i => Finset.Ico (sourceLo i) (sourceHi i)), ∀ i,
      |(z i : ℝ) - (origin i : ℝ)| ≤ smoothPairCoefficientScale (H i.2) L i.1 / 2) →
    (∀ j i, |(sourceLo (some j,i) : ℝ)| ≤ B * H i / L) →
    (∀ j i, |(sourceHi (some j,i) : ℝ)| ≤ B * H i / L) →
    let m := Fintype.card (Option J × I)
    let n := Fintype.card I
    let d := Fintype.card J
    let Z := replacementCommonInputLog m n d P0
    let G := 2 * physicalPairCoefficientLog n d Z + 2
    let U := scalarInitialReferenceInput m n d p P0
    let pref := affineReferenceInput epsilon U
    let common := affineCommonReferenceBudget E epsilon U
    let b := adaptiveAffineCutoff ⌈(pref + 2) ^ E⌉₊ m n epsilon p
      (scalarTransferTail (3 * p)) Z (scalarTransferBaseAccuracy (3 * p)) Z
    let cellLog := scalarTransferCellLog common b p Z U
    let meshLog := scalarMeshLog G (P0 + 1) (scalarTransferAccuracyLog b p Z)
    (pref + 2) ^ E ≤ budget → p + scalarTransferTail (3 * p) + 4 ≤ budget →
    Real.exp (Z + P0) ≤ L →
    (∀ i, Real.exp (2 * physicalReplacementThresholdLog n (Fintype.card {j : J // j ≠ k0}) b Z + 16) *
      L ^ (d + 1) ≤ H i) →
    (∀ i, 4 * Real.exp (G + max ((pref + 2) ^ E) cellLog) ≤ H i) →
    4 * Real.exp (4 * meshLog + 18 + cellLog + Z) ≤ L →
    (∀ i, 4 * Real.exp (4 * meshLog + 18 + cellLog) * L ^ (d + 1) ≤ H i) →
    ∀ outer : FiniteProbabilityWeights (∀ i, Finset.Ico (sourceLo i) (sourceHi i)),
    (∀ z, outer.weight z ≤ Real.exp p * (integerBoxUniformWeights sourceLo sourceHi hsource).weight z) →
    outer.eventProbability (fun z => Real.exp (-p) <
      (integerBoxUniformWeights parLo parHi hpar).mean (fun t =>
        realZeroExtendFinset (translatedIntegerBox lo N) (fun z => (h z).re)
          (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) (fun i => (z i).val)) -
        (1 + epsilon) * level * realZeroExtendFinset (translatedIntegerBox lo N) (fun z => (g.eval z).re)
          (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) (fun i => (z i).val)))) ≤ Real.exp (-p) := by
  obtain ⟨E, hE, hgeom⟩ := exists_niltest_geometric_scalar_transfer_s2.{u,v,0} s
  refine ⟨E, hE, ?_⟩
  intro I V J _ _ _ _ _ _ _ _ d0 nilmanifold p epsilon P0 level budget
    hp hepsilon hepsilon1 hP0 htarget hepsInv hlower hlevel hnP hJ hJlog hprofile g hcomplexity
    k0 D anchor parLo parHi hpar hD hDlog L C B A K c Cwidth hL hC hB hA hK hc hCwidth
    hClog hBlog hAlog hKlog hcinv hWidthlog lo N H hupper hratio hunit h hh hnoincrement
    R parMin hparMin hparSide hparWidth hwidthRatio hrelative hleft hright
    origin sourceLo sourceHi hsource hwinScale hW hsourceLo hsourceHi
    m n d Z G U pref common b cellLog meshLog hbudget hprecision hLlog hsizeExp hfirstScale hLmesh hHmesh outer hdom
  have hp0 : 0 ≤ p := by linarith
  have hpP0 : p ≤ P0 := by linarith
  have hP0exp : P0 ≤ Real.exp P0 := by linarith [Real.add_one_le_exp P0]
  have hnlog : (n : ℝ) ≤ Real.exp P0 := hnP.trans (hpP0.trans hP0exp)
  have hZdata := replacementCommonInputLog_bounds m n d hP0
  have hZ : 0 ≤ Z := hZdata.1
  have hP0Z : P0 ≤ Z := hZdata.2.1
  obtain ⟨hU, hZU, hGU, hP0U, hmU, hnU, hdU, hTU, hpU⟩ := scalarInitialReferenceInput_bounds m n d hp0 hP0
  have hG : 0 ≤ G := by
    have hcoef := (physicalPairCoefficientLog_bounds n d hZ).1
    dsimp only [G]
    linarith
  have hbase : 0 < scalarTransferBaseAccuracy (3 * p) := Real.exp_pos _
  have hbaseInv : (scalarTransferBaseAccuracy (3 * p))⁻¹ ≤ Real.exp P0 := by
    simp only [scalarTransferBaseAccuracy, Real.exp_neg, inv_inv]
    exact Real.exp_le_exp.mpr htarget
  have hepsU := hepsInv.trans (Real.exp_le_exp.mpr hP0U)
  have hbaseU := hbaseInv.trans (Real.exp_le_exp.mpr hP0U)
  have hT : 0 ≤ scalarTransferTail (3 * p) := by unfold scalarTransferTail; positivity
  have hb := adaptiveAffineCutoff_reference_bounds_s2 hE hepsilon hepsilon1 hU hp0 hT hZ hZ
    hpU hTU hZU hZU hmU hnU hepsU hbase hbaseU
  have hdegree : 2 * Z ≤ (b : ℝ) := (mul_le_mul_of_nonneg_left hZU (by norm_num)).trans hb.1
  let tol := weightedReplacementTolerance ((3 * K) ^ m) ((2 : ℝ) ^ (n + 1) * A ^ n)
    (scalarTransferBaseAccuracy (3 * p))
  let Q := D * integerBoxGcdCutoff d Cwidth tol
  let κ := integerBoxRetainedGap d D c tol
  let rho := physicalPairGridAccuracy n k0 C κ A tol
  obtain ⟨htol, _, _, _, hQlog, _⟩ := replacement_selected_parameter_bounds m n d D hP0 hK hA hCwidth hc hbase hD
    hDlog hKlog hAlog hWidthlog hcinv hbaseInv
  have hrho := physicalPairGridAccuracy_spec n k0 C κ hA htol
  have hrhoInvSmall := selectedPhysicalGrid_inverse_le_exp m n k0 D hP0 hK hA
    (zero_le_one.trans hC) hCwidth hc hbase hD hnlog hJlog hDlog hKlog hAlog hClog hWidthlog hcinv hbaseInv hprofile
  have hsmall : physicalPairCoefficientLog n (Fintype.card {j : J // j ≠ k0}) Z ≤
      physicalPairCoefficientLog n d Z :=
    physicalPairCoefficientLog_mono_dimension n (Fintype.card_subtype_le _) hZ
  have hrhoInv : rho⁻¹ ≤ Real.exp G := hrhoInvSmall.trans (Real.exp_le_exp.mpr (by dsimp only [G]; linarith))
  have hcommon : 0 ≤ common := (affineCommonReferenceBudget_bounds hE epsilon hU).1
  have hlogs := scalarTransferAllocatedLogs_bounds b hcommon hp0 hZ hU
  have hcell : 0 ≤ cellLog := hlogs.2.2.1
  have hacc : 0 ≤ scalarTransferAccuracyLog b p Z := hlogs.2.1
  have hmeshBounds := scalarMeshLog_bounds hG (by linarith : 0 ≤ P0 + 1) hacc
  have hH (i) : 0 < H i :=
    (mul_pos (Real.exp_pos _) (pow_pos (by linarith : 0 < L) (d + 1))).trans_le (hsizeExp i)
  have hlarge (i) : 4 ≤ rho * H i :=
    normalizedMesh_scale_large hrho.1 hrhoInv (hcell.trans (le_max_right _ _)) (hfirstScale i)
  have hwhole (i) : rho * H i ≤ 2 * (N i : ℝ) :=
    ((mul_le_mul_of_nonneg_right hrho.2.1 (hH i).le).trans_eq (one_mul _)).trans (hupper i)
  have hwidths := initialReplacement_mesh_widths sourceLo sourceHi parLo parHi hsource hpar H
    (zero_le_one.trans hL) hK hc hD hwinScale (fun j => hrelative.trans (hparSide j))
  have hcSource : 0 < (K + 1)⁻¹ := inv_pos.mpr (by positivity)
  have hPup : Real.exp P0 ≤ Real.exp (P0 + 1) := Real.exp_le_exp.mpr (by linarith)
  have hcSourceLog : ((K + 1)⁻¹)⁻¹ ≤ Real.exp (P0 + 1) := by
    simpa only [inv_inv, add_comm] using one_add_le_exp_succ hP0 hKlog
  have hboundary := scalarMesh_boundary_bound (Nat.cast_nonneg n) hA hrho.1 hcSource hG
    (by linarith : 0 ≤ P0 + 1) hacc (hnlog.trans hPup) (hAlog.trans hPup) hrhoInv hcSourceLog
  have hmovement := scalarMesh_movement_bound (zero_le_one.trans hC) hB hG
    (by linarith : 0 ≤ P0 + 1) hacc (hJlog.trans hPup) (hClog.trans hPup) (hBlog.trans hPup)
  have hPMesh : P0 ≤ meshLog := (by linarith : P0 ≤ P0 + 1).trans hmeshBounds.2.1
  have hDlogZ := hDlog.trans (Real.exp_le_exp.mpr hP0Z)
  have hprimeBounds := boundedPrimeFamily_log_bounds Q hQlog
  let : ∀ i : BoundedPrime Q, NeZero (boundedPrime Q i ^ boundedPrimeExponent Q i) :=
    fun i => ⟨(boundedPrimePower_pos Q i).ne'⟩
  apply hgeom nilmanifold p epsilon Z U G P0 meshLog level budget
    hp hepsilon hepsilon1 hZ hU hmeshBounds.1 hpU hTU hZU hGU hepsU hlower hlevel hnU hmU hdU hJ
    g hcomplexity (boundedPrime Q) (boundedPrimeExponent Q) (boundedPrime_prime Q) (boundedPrime_injective Q)
    hprimeBounds.1 hprimeBounds.2 D anchor hD hDlogZ hbudget hprecision hmeshBounds.2.2.1
    lo N H rho L C B A ((K + 1)⁻¹) K c⁻¹ hrho.1 hL hH (zero_le_one.trans hC) hB hA hcSource hK
    (inv_nonneg.mpr hc.le) hrhoInv hAlog hlarge hwhole hratio hfirstScale hunit h hh hnoincrement
    sourceLo sourceHi hsource parLo parHi hpar hwidths.1 hleft hright hsourceLo hsourceHi hboundary hmovement
    (hKlog.trans (Real.exp_le_exp.mpr hPMesh)) (hcinv.trans (Real.exp_le_exp.mpr hPMesh))
    hwidths.2.1 hwidths.2.2 hLmesh hHmesh ?_ ?_ outer hdom
  · intro w hw
    exact initial_budget_joint_physical_replacement k0 D anchor parLo parHi hpar H hL hC hA hbase hK hc hCwidth hD
      hleft hright origin lo N b (d + 1) (by omega) (fun z => (h z).re) hh P0 hP0 hnlog hJlog
      hDlog hKlog hAlog hClog hWidthlog hcinv hbaseInv hprofile hupper hratio R parMin hparMin hJ
      hparSide hparWidth hwidthRatio hrelative sourceLo sourceHi hsource hwinScale w hw
      hLlog hdegree hsizeExp hW
  · intro w hw
    exact initial_budget_joint_physical_replacement k0 D anchor parLo parHi hpar H hL hC hA hbase hK hc hCwidth hD
      hleft hright origin lo N b (d + 1) (by omega) (fun z => (g.eval z).re) (fun z hz => (hunit z hz).2)
      P0 hP0 hnlog hJlog hDlog hKlog hAlog hClog hWidthlog hcinv hbaseInv hprofile hupper hratio
      R parMin hparMin hJ hparSide hparWidth hwidthRatio hrelative sourceLo sourceHi hsource hwinScale w hw
      hLlog hdegree hsizeExp hW

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators Classical

universe u v

theorem exists_niltest_threshold_scalar_transfer (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ {I : Type u} {V : Type v} {J : Type*}
      [Fintype I] [Fintype J] [LieRing V] [LieAlgebra ℚ V]
      [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [T2Space (ℝ ⊗[ℚ] V)]
      {d0 : ℕ} (nilmanifold : RationalFilteredNilmanifold V s d0)
      (p epsilon P0 level budget : ℝ),
    2 ≤ p → 0 < epsilon → epsilon ≤ 1 → 0 ≤ P0 → 3 * p + 10 ≤ P0 →
    epsilon⁻¹ ≤ Real.exp P0 → Real.exp (-p) ≤ level → level ≤ 2 →
    (Fintype.card I : ℝ) ≤ p → 2 ≤ Fintype.card J →
    (Fintype.card J : ℝ) ≤ Real.exp P0 →
    (probabilityProfileLipschitz : ℝ) ≤ Real.exp P0 →
    ∀ g : nilmanifold.Niltest (fun _ : I => 1), g.ComplexityLE p →
    ∀ (_k0 : J) (D : ℕ) (anchor parLo parHi : J → ℤ) (hpar : ∀ j, parLo j < parHi j),
    0 < D → (D : ℝ) ≤ Real.exp P0 →
    ∀ (L C B A K c Cwidth : ℝ), 1 ≤ C → 0 ≤ B → 0 ≤ A → 0 ≤ K → 0 < c → 0 ≤ Cwidth →
    C ≤ Real.exp P0 → B ≤ Real.exp P0 → A ≤ Real.exp P0 → K ≤ Real.exp P0 →
    c⁻¹ ≤ Real.exp P0 → Cwidth ≤ Real.exp P0 →
    ∀ (lo : I → ℤ) (N : I → ℕ) (H : I → ℝ),
    (∀ i, H i ≤ 2 * (N i : ℝ)) → (∀ i, (N i : ℝ) ≤ A * H i) →
    (∀ z ∈ translatedIntegerBox lo N, (g.eval z).im = 0 ∧ 0 ≤ (g.eval z).re ∧ (g.eval z).re ≤ 1) →
    ∀ h : (I → ℤ) → ℂ,
    (∀ z ∈ translatedIntegerBox lo N, 0 ≤ (h z).re ∧ (h z).re ≤ 1) →
    ResidueSliceUpperComparison h g.eval lo N budget level (Real.exp (-budget)) →
    ∀ (R : ℕ) (parMin : ℝ), 0 < parMin →
    (∀ j, parMin ≤ ((parHi j - parLo j : ℤ) : ℝ)) →
    (∀ j, parHi j - parLo j ≤ (R : ℤ)) → (R : ℝ) ≤ Cwidth * parMin → c * L ≤ parMin →
    (∀ j, |((anchor j + (D : ℤ) * parLo j : ℤ) : ℝ) / L| ≤ C) →
    (∀ j, |((anchor j + (D : ℤ) * parHi j : ℤ) : ℝ) / L| ≤ C) →
    ∀ (origin sourceLo sourceHi : Option J × I → ℤ) (hsource : ∀ z, sourceLo z < sourceHi z),
    (∀ z : Option J × I, smoothPairCoefficientScale (H z.2) L z.1 ≤
      K * ((sourceHi z - sourceLo z : ℤ) : ℝ)) →
    (∀ z ∈ Fintype.piFinset (fun i => Finset.Ico (sourceLo i) (sourceHi i)), ∀ i,
      |(z i : ℝ) - (origin i : ℝ)| ≤ smoothPairCoefficientScale (H i.2) L i.1 / 2) →
    (∀ j i, |(sourceLo (some j,i) : ℝ)| ≤ B * H i / L) →
    (∀ j i, |(sourceHi (some j,i) : ℝ)| ≤ B * H i / L) →
    let m := Fintype.card (Option J × I)
    let n := Fintype.card I
    let d := Fintype.card J
    let Z := replacementCommonInputLog m n d P0
    let G := 2 * physicalPairCoefficientLog n d Z + 2
    let U := scalarInitialReferenceInput m n d p P0
    let pref := affineReferenceInput epsilon U
    let common := affineCommonReferenceBudget E epsilon U
    let b := adaptiveAffineCutoff ⌈(pref + 2) ^ E⌉₊ m n epsilon p
      (scalarTransferTail (3 * p)) Z (scalarTransferBaseAccuracy (3 * p)) Z
    let cellLog := scalarTransferCellLog common b p Z U
    let meshLog := scalarMeshLog G (P0 + 1) (scalarTransferAccuracyLog b p Z)
    scalarCombinedLogThreshold n d b p P0 Z G ((pref + 2) ^ E) cellLog meshLog ≤ budget →
    Real.exp budget ≤ L → (∀ i, Real.exp budget * L ^ (d + 1) ≤ H i) →
    ∀ outer : FiniteProbabilityWeights (∀ i, Finset.Ico (sourceLo i) (sourceHi i)),
    (∀ z, outer.weight z ≤ Real.exp p * (integerBoxUniformWeights sourceLo sourceHi hsource).weight z) →
    outer.eventProbability (fun z => Real.exp (-p) <
      (integerBoxUniformWeights parLo parHi hpar).mean (fun t =>
        realZeroExtendFinset (translatedIntegerBox lo N) (fun z => (h z).re)
          (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) (fun i => (z i).val)) -
        (1 + epsilon) * level * realZeroExtendFinset (translatedIntegerBox lo N) (fun z => (g.eval z).re)
          (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) (fun i => (z i).val)))) ≤ Real.exp (-p) := by
  obtain ⟨E, hE, hinitial⟩ := exists_niltest_initial_scalar_transfer.{u,v} s
  refine ⟨E, hE, ?_⟩
  intro I V J _ _ _ _ _ _ _ _ d0 nilmanifold p epsilon P0 level budget
    hp hepsilon hepsilon1 hP0 htarget hepsInv hlower hlevel hnP hJ hJlog hprofile g hcomplexity
    k0 D anchor parLo parHi hpar hD hDlog L C B A K c Cwidth hC hB hA hK hc hCwidth
    hClog hBlog hAlog hKlog hcinv hWidthlog lo N H hupper hratio hunit h hh hnoincrement
    R parMin hparMin hparSide hparWidth hwidthRatio hrelative hleft hright
    origin sourceLo sourceHi hsource hwinScale hW hsourceLo hsourceHi
    m n d Z G U pref common b cellLog meshLog hbudget hLexp hHexp outer hdom
  have hp0 : 0 ≤ p := by linarith
  have hZ : 0 ≤ Z := (replacementCommonInputLog_bounds m n d hP0).1
  have hG : 0 ≤ G := by
    have h := (physicalPairCoefficientLog_bounds n d hZ).1
    dsimp only [G]; linarith
  have hU : 0 ≤ U := (scalarInitialReferenceInput_bounds m n d hp0 hP0).1
  have hpref : 0 ≤ pref + 2 := by
    have h := (affineReferenceInput_bounds epsilon hU).1
    dsimp only [pref]; linarith
  have hcost : 0 ≤ (pref + 2) ^ E := pow_nonneg hpref E
  have hcommon : 0 ≤ common := (affineCommonReferenceBudget_bounds hE epsilon hU).1
  have hlogs := scalarTransferAllocatedLogs_bounds b hcommon hp0 hZ hU
  have hcell : 0 ≤ cellLog := hlogs.2.2.1
  have hmesh : 0 ≤ meshLog := (scalarMeshLog_bounds hG (by linarith : 0 ≤ P0 + 1) hlogs.2.1).1
  obtain ⟨_, hcostBudget, hprecision, _, _, _, _⟩ :=
    scalarCombinedLogThreshold_bounds n d b hp0 hP0 hZ hG hcost hcell hmesh
  obtain ⟨hL, hLlog, hRsize, hFsize, hLmesh, hHmesh⟩ :=
    scalarCombinedLogThreshold_size_conditions n d b (d + 1) H hp0 hP0 hZ hG hcost hcell hmesh hbudget hLexp hHexp
  have hRother (i) : Real.exp (2 * physicalReplacementThresholdLog n (Fintype.card {j : J // j ≠ k0}) b Z + 16) *
      L ^ (d + 1) ≤ H i := by
    have hmono := physicalReplacementThresholdLog_mono_dimension n b (Fintype.card_subtype_le (fun j : J => j ≠ k0)) hZ
    exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith))
      (pow_nonneg (zero_le_one.trans hL) (d + 1))).trans (hRsize i)
  exact hinitial nilmanifold p epsilon P0 level budget hp hepsilon hepsilon1 hP0 htarget hepsInv hlower hlevel
    hnP hJ hJlog hprofile g hcomplexity k0 D anchor parLo parHi hpar hD hDlog
    L C B A K c Cwidth hL hC hB hA hK hc hCwidth hClog hBlog hAlog hKlog hcinv hWidthlog
    lo N H hupper hratio hunit h hh hnoincrement R parMin hparMin hparSide hparWidth hwidthRatio hrelative
    hleft hright origin sourceLo sourceHi hsource hwinScale hW hsourceLo hsourceHi
    (hcostBudget.trans hbudget) (hprecision.trans hbudget) hLlog hRother hFsize hLmesh hHmesh outer hdom

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CanonicalUnconditionedScalarTransfer
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped TensorProduct BigOperators Classical

universe u v

theorem exists_unconditioned_joint_scalar_transfer_s2_oai (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ {I : Type u} {V : Type v} {J : Type*}
      [Fintype I] [Fintype J] [LieRing V] [LieAlgebra ℚ V]
      [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [T2Space (ℝ ⊗[ℚ] V)]
      {d0 : ℕ} (nilmanifold : RationalFilteredNilmanifold V s d0)
      (p epsilon P0 level budget : ℝ),
    2 ≤ p → 0 < epsilon → epsilon ≤ 1 → 0 ≤ P0 → 3 * p + 10 ≤ P0 →
    epsilon⁻¹ ≤ Real.exp P0 → Real.exp (-p) ≤ level → level ≤ 2 →
    (Fintype.card I : ℝ) ≤ p → 2 ≤ Fintype.card J →
    (Fintype.card J : ℝ) ≤ Real.exp P0 →
    (probabilityProfileLipschitz : ℝ) ≤ Real.exp P0 →
    ∀ g : nilmanifold.Niltest (fun _ : I => 1), g.ComplexityLE p →
    ∀ (_k0 : J) (D : ℕ) (anchor parLo parHi : J → ℤ) (hpar : ∀ j, parLo j < parHi j),
    0 < D → (D : ℝ) ≤ Real.exp P0 →
    ∀ (L C B A K c Cwidth : ℝ), 1 ≤ C → 0 ≤ B → 0 ≤ A → 0 ≤ K → 0 < c → 0 ≤ Cwidth →
    C ≤ Real.exp P0 → B ≤ Real.exp P0 → A ≤ Real.exp P0 → K ≤ Real.exp P0 →
    c⁻¹ ≤ Real.exp P0 → Cwidth ≤ Real.exp P0 →
    ∀ (lo : I → ℤ) (N : I → ℕ) (H : I → ℝ),
    (∀ i, H i ≤ 2 * (N i : ℝ)) → (∀ i, (N i : ℝ) ≤ A * H i) →
    (∀ z ∈ translatedIntegerBox lo N, (g.eval z).im = 0 ∧ 0 ≤ (g.eval z).re ∧ (g.eval z).re ≤ 1) →
    ∀ h : (I → ℤ) → ℂ,
    (∀ z ∈ translatedIntegerBox lo N, 0 ≤ (h z).re ∧ (h z).re ≤ 1) →
    ResidueSliceUpperComparison h g.eval lo N budget level (Real.exp (-budget)) →
    ∀ (R : ℕ) (parMin : ℝ), 0 < parMin →
    (∀ j, parMin ≤ ((parHi j - parLo j : ℤ) : ℝ)) →
    (∀ j, parHi j - parLo j ≤ (R : ℤ)) → (R : ℝ) ≤ Cwidth * parMin → c * L ≤ parMin →
    (∀ j, |((anchor j + (D : ℤ) * parLo j : ℤ) : ℝ) / L| ≤ C) →
    (∀ j, |((anchor j + (D : ℤ) * parHi j : ℤ) : ℝ) / L| ≤ C) →
    ∀ (origin sourceLo sourceHi : Option J × I → ℤ) (_hsource : ∀ z, sourceLo z < sourceHi z),
    (∀ z : Option J × I, smoothPairCoefficientScale (H z.2) L z.1 ≤
      K * ((sourceHi z - sourceLo z : ℤ) : ℝ)) →
    (∀ z ∈ Fintype.piFinset (fun i => Finset.Ico (sourceLo i) (sourceHi i)), ∀ i,
      |(z i : ℝ) - (origin i : ℝ)| ≤ smoothPairCoefficientScale (H i.2) L i.1 / 2) →
    (∀ j i, |(sourceLo (some j,i) : ℝ)| ≤ B * H i / L) →
    (∀ j i, |(sourceHi (some j,i) : ℝ)| ≤ B * H i / L) →
    let m := Fintype.card (Option J × I)
    let n := Fintype.card I
    let d := Fintype.card J
    let Z := replacementCommonInputLog m n d P0
    let G := 2 * physicalPairCoefficientLog n d Z + 2
    let U := scalarInitialReferenceInput m n d p P0
    let pref := affineReferenceInput epsilon U
    let common := affineCommonReferenceBudget E epsilon U
    let b := adaptiveAffineCutoff ⌈(pref + 2) ^ E⌉₊ m n epsilon p
      (scalarTransferTail (3 * p)) Z (scalarTransferBaseAccuracy (3 * p)) Z
    let cellLog := scalarTransferCellLog common b p Z U
    let meshLog := scalarMeshLog G (P0 + 1) (scalarTransferAccuracyLog b p Z)
    scalarCombinedLogThreshold n d b p P0 Z G ((pref + 2) ^ E) cellLog meshLog ≤ budget →
    Real.exp budget ≤ L → (∀ i, Real.exp budget * L ^ (d + 1) ≤ H i) →
    ∀ (bases : Finset (I → ℤ)) (hbases : bases.Nonempty)
      (width : Option J × I → ℝ) (hwidth : ∀ z, 0 < width z)
      (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : I => 1) {0} width z),
    (∀ z : J × I, 8 * (probabilityProfileLipschitz : ℝ) ≤ width (some z.1,z.2)) →
    ∀ _hframe : ∀ z : bases × rectangularWeightIndices 0 width 1, ∀ t,
      jointIntegerFrame (z.1.val,z.2.val) t.1 t.2 ∈ Finset.Ico (sourceLo t) (sourceHi t),
    ((∏ t, ((sourceHi t - sourceLo t : ℤ) : ℝ)) *
      ((bases.card : ℝ)⁻¹ * ∏ t : J × I, 2 / width (some t.1,t.2))) ≤ Real.exp p →
    (selectedJointReference bases hbases (fun _ : I => 1) {0} width hwidth hZ).eventProbability
      (fun z => Real.exp (-p) <
      (integerBoxUniformWeights parLo parHi hpar).mean (fun t =>
        realZeroExtendFinset (translatedIntegerBox lo N) (fun z => (h z).re)
          (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2)) -
        (1 + epsilon) * level * realZeroExtendFinset (translatedIntegerBox lo N) (fun z => (g.eval z).re)
          (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2)))) ≤ Real.exp (-p) := by
  obtain ⟨E, hE, htransfer⟩ := exists_niltest_threshold_scalar_transfer.{u,v} s
  refine ⟨E, hE, ?_⟩
  intro I V J _ _ _ _ _ _ _ _ d0 nilmanifold p epsilon P0 level budget
    hp hepsilon hepsilon1 hP0 htarget hepsInv hlower hlevel hnP hJ hJlog hprofile g hcomplexity
    k0 D anchor parLo parHi hpar hD hDlog L C B A K c Cwidth hC hB hA hK hc hCwidth
    hClog hBlog hAlog hKlog hcinv hWidthlog lo N H hupper hratio hunit h hh hnoincrement
    R parMin hparMin hparSide hparWidth hwidthRatio hrelative hleft hright
    origin sourceLo sourceHi hsource hwinScale hW hsourceLo hsourceHi
    m n d Z G U pref common b cellLog meshLog hbudget hLexp hHexp
    bases hbases width hwidth hZ hscale hframe hframeBudget
  let reference := selectedJointReference bases hbases (fun _ : I => 1) {0} width hwidth hZ
  let frame := selectedJointFrameBoxMap bases width sourceLo sourceHi hframe
  have hdom := selectedJointReference_frame_box_domination bases hbases width hwidth hZ hscale
    sourceLo sourceHi hsource hframe hframeBudget
  have htail := htransfer nilmanifold p epsilon P0 level budget
    hp hepsilon hepsilon1 hP0 htarget hepsInv hlower hlevel hnP hJ hJlog hprofile g hcomplexity
    k0 D anchor parLo parHi hpar hD hDlog L C B A K c Cwidth hC hB hA hK hc hCwidth
    hClog hBlog hAlog hKlog hcinv hWidthlog lo N H hupper hratio hunit h hh hnoincrement
    R parMin hparMin hparSide hparWidth hwidthRatio hrelative hleft hright
    origin sourceLo sourceHi hsource hwinScale hW hsourceLo hsourceHi
    hbudget hLexp hHexp (reference.fiberLaw frame) hdom
  dsimp only [reference, frame] at htail
  rw [selectedJointReference_frame_box_eventProbability] at htail
  exact htail

end Erdos3

end

end OAI
end

theorem solution.{u, v, u_1} : type_of% @OAI.Erdos3.exists_unconditioned_joint_scalar_transfer_s2_oai.{u, v, u_1} := @OAI.Erdos3.exists_unconditioned_joint_scalar_transfer_s2_oai.{u, v, u_1}
