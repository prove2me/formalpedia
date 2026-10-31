-- Prove2me | solution 1 for OAI.Ostmann.PublishedProgressionInput.eventual_tested_character_shell_contradiction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:32:54.394061+00:00
-- url     : https://prove2.me/submissions/ca51ab08-1851-4969-9d4b-28e9e4462f71

import Mathlib
import Definitions.Def_OAIQ095D003
import Definitions.Def_OAIQ095D004
import Theorems.Thm_OAI_Ostmann_eventual_uniform_character_endpoint_contradiction

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_CyclicSumsetCover
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A bounded number of sums in a dense generating set

The good-cell construction needs a uniform covering length in a finite cyclic group.
The elementary small-doubling theorem already in Mathlib supplies this without any
additional published-input hypothesis. Constants need not be optimal here.
-/

namespace Ostmann

open scoped Pointwise

private theorem small_doubling_cover {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    (A : Finset G) (h1 : 1 ∈ A) (hgen : Subgroup.closure (A : Set G) = ⊤)
    (hsmall : ((A * A).card : ℝ) < (3 / 2 : ℝ) * A.card) :
    A * A = Finset.univ := by
  have hq : ((A * A).card : ℚ) < (3 / 2 : ℚ) * A.card := by
    have h : (2 : ℝ) * (A * A).card < 3 * A.card := by linarith
    have h' : (2 : ℚ) * (A * A).card < 3 * A.card := by exact_mod_cast h
    linarith
  let H := Finset.invMulSubgroup A hq
  have hAH : (A : Set G) ⊆ H := by
    intro a ha
    change a ∈ (Finset.invMulSubgroup A hq : Set G)
    rw [Finset.invMulSubgroup_eq_inv_mul]
    rw [← Finset.coe_mul]
    change a ∈ (A⁻¹ * A : Finset G)
    exact Finset.mem_mul.mpr ⟨1, by simpa using h1, a, ha, one_mul a⟩
  have hH : H = ⊤ := by
    apply top_unique
    rw [← hgen]
    exact (Subgroup.closure_le H).mpr hAH
  have hdiff : A⁻¹ * A = Finset.univ := by
    ext a
    have ha : a ∈ H := by rw [hH]; trivial
    change a ∈ (Finset.invMulSubgroup A hq : Set G) at ha
    rw [Finset.invMulSubgroup_eq_inv_mul, ← Finset.coe_mul] at ha
    norm_cast at ha
    simpa using ha
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  rw [← Finset.card_inv_mul_of_doubling_lt_three_halves hq, hdiff]

private theorem product_growth_or_cover {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    (A : Finset G) (h1 : 1 ∈ A) (hgen : Subgroup.closure (A : Set G) = ⊤) :
    A * A = Finset.univ ∨ (3 / 2 : ℝ) * A.card ≤ (A * A).card := by
  by_cases h : ((A * A).card : ℝ) < (3 / 2 : ℝ) * A.card
  · exact Or.inl (small_doubling_cover A h1 hgen h)
  · exact Or.inr (le_of_not_gt h)

private theorem dyadic_product_growth {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    (A : Finset G) (h1 : 1 ∈ A) (hgen : Subgroup.closure (A : Set G) = ⊤) (j : ℕ) :
    A ^ (2 ^ j) = Finset.univ ∨
      (3 / 2 : ℝ) ^ j * A.card ≤ (A ^ (2 ^ j)).card := by
  induction j with
  | zero => exact Or.inr (by simp)
  | succ j ih =>
    have hj : 1 ∈ A ^ (2 ^ j) := Finset.one_mem_pow h1
    have hAj : A ⊆ A ^ (2 ^ j) := Finset.subset_pow h1 (by positivity)
    have hgj : Subgroup.closure ((A ^ (2 ^ j) : Finset G) : Set G) = ⊤ := by
      apply top_unique
      rw [← hgen]
      exact Subgroup.closure_mono (show ((A : Finset G) : Set G) ⊆
        ((A ^ (2 ^ j) : Finset G) : Set G) from hAj)
    have hsq : A ^ (2 ^ (j + 1)) = A ^ (2 ^ j) * A ^ (2 ^ j) := by
      rw [pow_succ, Nat.mul_two, pow_add]
    rcases product_growth_or_cover (A ^ (2 ^ j)) hj hgj with hc | hg
    · exact Or.inl (hsq.trans hc)
    · rcases ih with hi | hi
      · exact Or.inl (Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by
          have hsub := Finset.pow_subset_pow_right h1 (show 2 ^ j ≤ 2 ^ (j + 1) by
            rw [pow_succ]; omega)
          rw [hi] at hsub
          exact Finset.card_le_card hsub))
      · right
        rw [hsq, pow_succ]
        calc
          (3 / 2 : ℝ) ^ j * (3 / 2) * A.card =
              (3 / 2) * ((3 / 2 : ℝ) ^ j * A.card) := by ring
          _ ≤ (3 / 2 : ℝ) * (A ^ (2 ^ j)).card := by gcongr
          _ ≤ _ := hg

/-- A positive-density generating set containing the identity covers its finite group
in a number of products depending only on the density. -/
private theorem exists_uniform_product_cover (δ : ℝ) (hδ : 0 < δ) :
    ∃ r : ℕ, 0 < r ∧ ∀ (G : Type*) [Group G] [Fintype G] [DecidableEq G]
      (A : Finset G), 1 ∈ A → Subgroup.closure (A : Set G) = ⊤ →
      δ * Fintype.card G ≤ A.card → A ^ r = Finset.univ := by
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (δ⁻¹) (by norm_num : (1 : ℝ) < 3 / 2)
  refine ⟨2 ^ j, by positivity, ?_⟩
  intro G _ _ _ A h1 hgen hdensity
  rcases dyadic_product_growth A h1 hgen j with hcover | hgrowth
  · exact hcover
  · have hcard : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
    have hδj : 1 < (3 / 2 : ℝ) ^ j * δ := by
      have := (mul_lt_mul_iff_left₀ hδ).mpr hj
      rw [inv_mul_cancel₀ hδ.ne'] at this
      simpa only [mul_comm] using this
    have hupper : ((A ^ (2 ^ j)).card : ℝ) ≤ Fintype.card G := by
      exact Nat.cast_le.mpr (Finset.card_le_univ (A ^ (2 ^ j : ℕ)))
    have hlower : (3 / 2 : ℝ) ^ j * (δ * Fintype.card G) ≤
        (A ^ (2 ^ j)).card := (mul_le_mul_of_nonneg_left hdensity (by positivity)).trans hgrowth
    nlinarith

/-- Uniform cyclic covering, expressed as an ordered tuple of summands. -/
theorem exists_uniform_cyclic_sum_cover (δ : ℝ) (hδ : 0 < δ) :
    ∃ r : ℕ, 0 < r ∧ ∀ (q : ℕ) [NeZero q] (S : Finset (ZMod q)),
      0 ∈ S → AddSubgroup.closure (S : Set (ZMod q)) = ⊤ →
      δ * q ≤ S.card → ∀ x : ZMod q,
      ∃ f : Fin r → ZMod q, (∀ i, f i ∈ S) ∧ ∑ i, f i = x := by
  obtain ⟨r, hr, hcover⟩ := exists_uniform_product_cover δ hδ
  refine ⟨r, hr, ?_⟩
  intro q _ S h0 hgen hdensity x
  let A : Finset (Multiplicative (ZMod q)) := S.image Multiplicative.ofAdd
  have hset : (A : Set (Multiplicative (ZMod q))) =
      Multiplicative.toAdd ⁻¹' (S : Set (ZMod q)) := by
    ext a
    simp [A]
  have hgenA : Subgroup.closure (A : Set (Multiplicative (ZMod q))) = ⊤ := by
    rw [hset, ← AddSubgroup.toSubgroup_closure, hgen]
    rfl
  have hcard : A.card = S.card := Finset.card_image_of_injective _
    (fun _ _ h => congrArg Multiplicative.toAdd h)
  have h1 : 1 ∈ A := by
    exact Finset.mem_image.mpr ⟨0, h0, rfl⟩
  have hd : δ * Fintype.card (Multiplicative (ZMod q)) ≤ A.card := by
    simpa [hcard, Fintype.card_multiplicative, ZMod.card] using hdensity
  have hx : Multiplicative.ofAdd x ∈ A ^ r := by
    rw [hcover (Multiplicative (ZMod q)) A h1 hgenA hd]
    exact Finset.mem_univ _
  obtain ⟨f, hf⟩ := Finset.mem_pow.mp hx
  refine ⟨fun i => Multiplicative.toAdd (f i), ?_, ?_⟩
  · intro i
    have hi := (f i).property
    change (f i).val ∈ (A : Set (Multiplicative (ZMod q))) at hi
    rwa [hset] at hi
  · have hh := congrArg Multiplicative.toAdd hf
    simpa only [List.prod_ofFn, toAdd_prod, toAdd_ofAdd] using hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_CellDifferenceGCD
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # GCD normalization of cell differences

Finite cell differences divided by their gcd generate every cyclic quotient.
Reducing a set contained in `[0,s]` modulo `s` loses at most the upper endpoint.
-/

namespace Ostmann

open scoped BigOperators

private theorem nat_gcd_mem_subgroup {q : ℕ} (H : AddSubgroup (ZMod q))
    (a b : ℕ) (ha : (a : ZMod q) ∈ H) (hb : (b : ZMod q) ∈ H) :
    (a.gcd b : ZMod q) ∈ H := by
  have he : (a.gcd b : ZMod q) =
      (Nat.gcdA a b) • (a : ZMod q) + (Nat.gcdB a b) • (b : ZMod q) := by
    have hh := congrArg (fun z : ℤ => (z : ZMod q)) (Nat.gcd_eq_gcd_ab a b)
    simpa [zsmul_eq_mul, mul_comm] using hh
  rw [he]
  exact H.add_mem (H.zsmul_mem ha _) (H.zsmul_mem hb _)

private theorem finset_gcd_mem_subgroup {q : ℕ} (H : AddSubgroup (ZMod q))
    (A : Finset ℕ) (hA : ∀ a ∈ A, (a : ZMod q) ∈ H) :
    ((A.gcd id : ℕ) : ZMod q) ∈ H := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert a A ha ih =>
    rw [Finset.gcd_insert]
    exact nat_gcd_mem_subgroup H a (A.gcd id) (hA a (Finset.mem_insert_self _ _))
      (ih (fun b hb => hA b (Finset.mem_insert_of_mem hb)))

/-- A gcd-one set of nonnegative integers generates every cyclic quotient. -/
theorem cyclic_closure_of_gcd_one (A : Finset ℕ) (hA : A.gcd id = 1) (q : ℕ) :
    AddSubgroup.closure ((A.image (fun a : ℕ => (a : ZMod q)) : Finset (ZMod q)) : Set (ZMod q)) = ⊤ := by
  let H := AddSubgroup.closure ((A.image (fun a : ℕ => (a : ZMod q)) : Finset (ZMod q)) : Set (ZMod q))
  have h1 : (1 : ZMod q) ∈ H := by
    have hh := finset_gcd_mem_subgroup H A (fun a ha =>
      AddSubgroup.subset_closure (Finset.mem_image.mpr ⟨a, ha, rfl⟩))
    simpa [hA] using hh
  apply top_unique
  intro x _
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  change (z : ZMod q) ∈ H
  simpa only [zsmul_one] using H.zsmul_mem h1 z

/-- GCD normalization gives the required generating set without a primitivity
assumption on the original cell indices. -/
theorem normalized_cyclic_closure (A : Finset ℕ) (a : ℕ) (ha : a ∈ A) (ha0 : a ≠ 0)
    (q : ℕ) :
    AddSubgroup.closure
      ((A.image (fun b => b / A.gcd id)).image (fun b : ℕ => (b : ZMod q)) : Set (ZMod q)) = ⊤ := by
  apply cyclic_closure_of_gcd_one
  rw [Finset.gcd_image]
  exact Finset.gcd_div_id_eq_one ha ha0

/-- The only collision introduced on `[0,s]` by reduction modulo `s` is
between the two endpoints. -/
theorem card_residue_image_lower (A : Finset ℕ) (s : ℕ) (_hs : 0 < s)
    (hbound : ∀ a ∈ A, a ≤ s) :
    A.card ≤ (A.image (fun a : ℕ => (a : ZMod s))).card + 1 := by
  have hinj : Set.InjOn (fun a : ℕ => (a : ZMod s)) (A.erase s) := by
    intro a ha b hb hab
    have hat : a < s := lt_of_le_of_ne (hbound a (Finset.mem_of_mem_erase ha))
      (Finset.ne_of_mem_erase ha)
    have hbt : b < s := lt_of_le_of_ne (hbound b (Finset.mem_of_mem_erase hb))
      (Finset.ne_of_mem_erase hb)
    have hh := (ZMod.natCast_eq_natCast_iff' a b s).mp hab
    simpa only [Nat.mod_eq_of_lt hat, Nat.mod_eq_of_lt hbt] using hh
  have hc := Finset.card_image_iff.mpr hinj
  have hle := Finset.card_le_card (Finset.image_subset_image
    (f := fun a : ℕ => (a : ZMod s)) (Finset.erase_subset s A))
  rw [hc] at hle
  by_cases hmem : s ∈ A
  · have he := Finset.card_erase_add_one hmem
    omega
  · simpa [Finset.erase_eq_of_notMem hmem] using hle.trans (Nat.le_succ _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PrimePartialSummation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Partial summation for the reciprocal-prime progression measure

This is the bridge from the published theta estimate (Montgomery--Vaughan,
Corollary 11.20, equations (11.32) and (11.34)) to the interval weights used
in Section 8. The conversion itself is proved here.
-/

namespace Ostmann

open scoped BigOperators
open MeasureTheory

theorem hasDerivAt_primeHarmonicWeight {x : ℝ} (hx : 1 < x) :
    HasDerivAt primeHarmonicWeight (primeHarmonicDerivative x) x := by
  have hx0 : x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx)
  have hlog : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  have h := ((hasDerivAt_id x).mul (Real.hasDerivAt_log hx0)).inv (mul_ne_zero hx0 hlog)
  change HasDerivAt (fun y : ℝ => (y * Real.log y)⁻¹)
    (-(1 * Real.log x + x * x⁻¹) / (x * Real.log x) ^ 2) x at h
  change HasDerivAt (fun y : ℝ => (y * Real.log y)⁻¹)
    (-(Real.log x + 1) / (x * Real.log x) ^ 2) x
  simpa only [one_mul, mul_inv_cancel₀ hx0] using h

theorem continuousOn_primeHarmonicDerivative {u v : ℝ} (hu : 1 < u) :
    ContinuousOn primeHarmonicDerivative (Set.Icc u v) := by
  intro x hx
  have hx1 : 1 < x := lt_of_lt_of_le hu hx.1
  have hx0 : x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx1)
  have hlog : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx1)
  exact (((Real.continuousAt_log hx0).add continuousAt_const).neg.div
    ((continuousAt_id.mul (Real.continuousAt_log hx0)).pow 2)
    (pow_ne_zero 2 (mul_ne_zero hx0 hlog))).continuousWithinAt

/-- The exact Abel formula on the actual prime progression, with arbitrary
real endpoints greater than one. -/
theorem reciprocalPrimeInterval_eq_partialSummation (q a : ℕ)
    {u v : ℝ} (hu : 1 < u) (huv : u ≤ v) :
    reciprocalPrimeInterval q a u v =
      primeHarmonicWeight v * primeProgressionTheta q a v -
      primeHarmonicWeight u * primeProgressionTheta q a u -
        ∫ t in Set.Ioc u v, primeHarmonicDerivative t * primeProgressionTheta q a t := by
  have hd (t : ℝ) (ht : t ∈ Set.Icc u v) :=
    hasDerivAt_primeHarmonicWeight (lt_of_lt_of_le hu ht.1)
  have hdi : Set.EqOn (deriv primeHarmonicWeight) primeHarmonicDerivative (Set.Icc u v) :=
    fun t ht => (hd t ht).deriv
  have hint : IntegrableOn (deriv primeHarmonicWeight) (Set.Icc u v) :=
    ((continuousOn_primeHarmonicDerivative hu).congr hdi).integrableOn_Icc
  have hab := sum_mul_eq_sub_sub_integral_mul (primeProgressionLog q a)
    (le_of_lt (lt_trans zero_lt_one hu)) huv (fun t ht => (hd t ht).differentiableAt) hint
  have hs : (∑ n ∈ Finset.Ioc ⌊u⌋₊ ⌊v⌋₊,
      primeHarmonicWeight n * primeProgressionLog q a n) = reciprocalPrimeInterval q a u v := by
    apply Finset.sum_congr rfl
    intro n _
    by_cases h : n.Prime ∧ Nat.ModEq q n a
    · have hn1 : (1 : ℝ) < n := by exact_mod_cast h.1.one_lt
      have hlog : Real.log (n : ℝ) ≠ 0 := ne_of_gt (Real.log_pos hn1)
      simp [primeProgressionLog, h, primeHarmonicWeight, mul_inv_rev,
        mul_comm, hlog]
    · simp [primeProgressionLog, h]
  rw [hs] at hab
  change reciprocalPrimeInterval q a u v =
    primeHarmonicWeight v * primeProgressionTheta q a v -
    primeHarmonicWeight u * primeProgressionTheta q a u -
    ∫ t in Set.Ioc u v, deriv primeHarmonicWeight t * primeProgressionTheta q a t at hab
  have hi : (∫ t in Set.Ioc u v, deriv primeHarmonicWeight t * primeProgressionTheta q a t) =
      ∫ t in Set.Ioc u v, primeHarmonicDerivative t * primeProgressionTheta q a t := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    exact congrArg (fun z => z * primeProgressionTheta q a t)
      (hdi (Set.Ioc_subset_Icc_self ht))
  rwa [hi] at hab

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ThetaMainTerm
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exceptional theta term and its harmonic density

Differentiating the published theta main term cancels its factor `β`.
The corresponding harmonic density is retained exactly.
-/

namespace Ostmann

open MeasureTheory

theorem continuousOn_thetaMainDensity (φ χ β : ℝ) {u v : ℝ} (hu : 0 < u) :
    ContinuousOn (thetaMainDensity φ χ β) (Set.Icc u v) := by
  intro x hx
  have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le hu hx.1)
  exact ((continuousAt_const.sub ((Real.continuousAt_rpow_const x (β - 1)
    (Or.inl hx0)).const_mul χ)).div_const φ).continuousWithinAt

theorem thetaMain_harmonic_integral (φ χ β : ℝ) (hβ : β ≠ 0)
    {u v : ℝ} (hu : 1 < u) (huv : u ≤ v) :
    (∫ t in Set.Ioc u v, primeHarmonicWeight t * thetaMainDensity φ χ β t) =
      primeHarmonicWeight v * thetaMainTerm φ χ β v -
      primeHarmonicWeight u * thetaMainTerm φ χ β u -
        ∫ t in Set.Ioc u v, primeHarmonicDerivative t * thetaMainTerm φ χ β t := by
  have hi1 : IntervalIntegrable primeHarmonicDerivative volume u v :=
    (continuousOn_primeHarmonicDerivative hu).intervalIntegrable_of_Icc huv
  have hi2 : IntervalIntegrable (thetaMainDensity φ χ β) volume u v :=
    (continuousOn_thetaMainDensity φ χ β (lt_trans zero_lt_one hu)).intervalIntegrable_of_Icc huv
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x hx => hasDerivAt_primeHarmonicWeight
      (lt_of_lt_of_le hu ((Set.uIcc_of_le huv) ▸ hx).1))
    (fun x hx => hasDerivAt_thetaMainTerm φ χ β hβ
      (lt_trans zero_lt_one (lt_of_lt_of_le hu ((Set.uIcc_of_le huv) ▸ hx).1))) hi1 hi2
  simpa only [intervalIntegral.integral_of_le huv] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_PrimeHarmonicError
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative transfer from theta errors to harmonic interval errors -/

namespace Ostmann

open MeasureTheory

/-- Partial summation loses only endpoint weights and the variation of the
harmonic weight. The theta estimate is used on exactly this interval. -/
theorem primeHarmonic_error_le (q a : ℕ) (φ χ β : ℝ) (hβ : β ≠ 0)
    {u v : ℝ} (hu : 1 < u) (huv : u ≤ v)
    (E B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hθ : ∀ t ∈ Set.Icc u v, |primeProgressionTheta q a t - thetaMainTerm φ χ β t| ≤ E)
    (hf : ∀ t ∈ Set.Icc u v, |primeHarmonicWeight t| ≤ B)
    (hdf : ∀ t ∈ Set.Icc u v, |primeHarmonicDerivative t| ≤ D) :
    |reciprocalPrimeInterval q a u v -
      ∫ t in Set.Ioc u v, primeHarmonicWeight t * thetaMainDensity φ χ β t| ≤
        E * (2 * B + (v - u) * D) := by
  let A := primeProgressionTheta q a
  let M := thetaMainTerm φ χ β
  let f := primeHarmonicWeight
  let f' := primeHarmonicDerivative
  have hdint : IntegrableOn f' (Set.Icc u v) :=
    (continuousOn_primeHarmonicDerivative hu).integrableOn_Icc
  have hAint : IntegrableOn (fun t => f' t * A t) (Set.Icc u v) :=
    integrableOn_mul_sum_Icc (primeProgressionLog q a)
      (le_of_lt (lt_trans zero_lt_one hu)) hdint
  have hMcont : ContinuousOn M (Set.Icc u v) := by
    intro x hx
    exact (hasDerivAt_thetaMainTerm φ χ β hβ
      (lt_trans zero_lt_one (lt_of_lt_of_le hu hx.1))).continuousAt.continuousWithinAt
  have hMint : IntegrableOn (fun t => f' t * M t) (Set.Icc u v) :=
    ((continuousOn_primeHarmonicDerivative hu).mul hMcont).integrableOn_Icc
  have hsub : (∫ t in Set.Ioc u v, f' t * A t) -
      (∫ t in Set.Ioc u v, f' t * M t) = ∫ t in Set.Ioc u v, f' t * (A t - M t) := by
    rw [← integral_sub (hAint.mono_set Set.Ioc_subset_Icc_self)
      (hMint.mono_set Set.Ioc_subset_Icc_self)]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t _
    dsimp
    ring
  have heq : reciprocalPrimeInterval q a u v -
      (∫ t in Set.Ioc u v, f t * thetaMainDensity φ χ β t) =
        f v * (A v - M v) - f u * (A u - M u) -
          ∫ t in Set.Ioc u v, f' t * (A t - M t) := by
    rw [reciprocalPrimeInterval_eq_partialSummation q a hu huv,
      thetaMain_harmonic_integral φ χ β hβ hu huv, ← hsub]
    dsimp [f, f', A, M]
    ring
  have hbound (t : ℝ) (ht : t ∈ Set.Icc u v) : |f t * (A t - M t)| ≤ B * E := by
    rw [abs_mul]
    exact mul_le_mul (hf t ht) (hθ t ht) (abs_nonneg _) hB
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := u) (b := v) (C := D * E) (f := fun t => f' t * (A t - M t)) (fun t ht => by
      have ht' : t ∈ Set.Icc u v := Set.Ioc_subset_Icc_self ((Set.uIoc_of_le huv) ▸ ht)
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul (hdf t ht') (hθ t ht') (abs_nonneg _) hD)
  rw [intervalIntegral.integral_of_le huv, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr huv)] at hi
  rw [heq]
  have h1 := norm_sub_le (f v * (A v - M v)) (f u * (A u - M u))
  have h2 := norm_sub_le (f v * (A v - M v) - f u * (A u - M u))
    (∫ t in Set.Ioc u v, f' t * (A t - M t))
  simp only [Real.norm_eq_abs] at h1 h2
  have hv := hbound v ⟨huv, le_rfl⟩
  have hu' := hbound u ⟨le_rfl, huv⟩
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_IntegerSumsetCover
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Lifting cyclic covering to exact integer sums

The bounded cyclic word can be padded with zero and the upper endpoint. This
is the finite, exact version of the good-cell interior sumset argument.
-/

namespace Ostmann

open scoped BigOperators

/-- A cyclic cover by `r` summands covers the interior interval with any
prescribed longer number of summands. -/
theorem integer_interval_sum_cover (A : Finset ℕ) (s r n : ℕ)
    (hs : 0 < s) (h0 : 0 ∈ A) (hend : s ∈ A)
    (hbound : ∀ a ∈ A, a ≤ s) (hrn : r ≤ n)
    (hcover : ∀ x : ZMod s, ∃ f : Fin r → ℕ,
      (∀ i, f i ∈ A) ∧ ∑ i, (f i : ZMod s) = x)
    (t : ℕ) (hlo : r * s ≤ t) (hhi : t ≤ (n - r) * s) :
    ∃ w : List ℕ, w.length = n ∧ (∀ a ∈ w, a ∈ A) ∧ w.sum = t := by
  obtain ⟨f, hf, hft⟩ := hcover (t : ZMod s)
  let b := ∑ i, f i
  have hb : b ≤ r * s := by
    calc
      b ≤ ∑ _i : Fin r, s := Finset.sum_le_sum (fun i _ => hbound _ (hf i))
      _ = r * s := by simp
  have hbt : b ≤ t := hb.trans hlo
  have hcast : ((t - b : ℕ) : ZMod s) = 0 := by
    rw [Nat.cast_sub hbt]
    have hbcast : (b : ZMod s) = (t : ZMod s) := by
      simpa only [b, Nat.cast_sum] using hft
    rw [hbcast, sub_self]
  obtain ⟨k, hk⟩ := (ZMod.natCast_eq_zero_iff (t - b) s).mp hcast
  have heq : b + k * s = t := by
    rw [Nat.mul_comm s k] at hk
    omega
  have hkbound : k ≤ n - r := by nlinarith
  let w := List.ofFn f ++ List.replicate k s ++ List.replicate (n - r - k) 0
  refine ⟨w, ?_, ?_, ?_⟩
  · simp only [w, List.length_append, List.length_ofFn, List.length_replicate]
    omega
  · intro a ha
    simp only [w, List.mem_append, List.mem_ofFn, List.mem_replicate] at ha
    rcases ha with (⟨i, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩
    · exact hf i
    · exact hend
    · exact h0
  · simpa [w, List.sum_append, List.sum_replicate, List.sum_ofFn, b] using heq

/-- The tuple version of the cyclic covering theorem lifts through the actual
residue image of a finite set of nonnegative integers. -/
theorem lift_cyclic_sum_cover (A : Finset ℕ) (s r : ℕ)
    (hcover : ∀ x : ZMod s, ∃ f : Fin r → ZMod s,
      (∀ i, f i ∈ A.image (fun a : ℕ => (a : ZMod s))) ∧ ∑ i, f i = x) :
    ∀ x : ZMod s, ∃ f : Fin r → ℕ,
      (∀ i, f i ∈ A) ∧ ∑ i, (f i : ZMod s) = x := by
  classical
  intro x
  obtain ⟨f, hf, hsum⟩ := hcover x
  have hex : ∀ i, ∃ a ∈ A, (a : ZMod s) = f i := fun i => Finset.mem_image.mp (hf i)
  choose a ha he using hex
  exact ⟨a, ha, by simpa only [he] using hsum⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GoodCellSums
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact interior sums of dense sets of cell differences

The covering length depends only on the density. Every admissible multiple of
the actual gcd in the interior interval has an ordered representation.
-/

namespace Ostmann

open scoped BigOperators

/-- Uniform exact covering of the interior by sums of a dense set of differences. -/
theorem dense_difference_sum_cover (δ : ℝ) (hδ : 0 < δ) :
    ∃ r : ℕ, 0 < r ∧ ∀ (A : Finset ℕ) (s : ℕ),
      0 < s → 0 ∈ A → s ∈ A → (∀ a ∈ A, a ≤ s) →
      δ * s + 1 ≤ A.card → ∀ n : ℕ, r ≤ n → ∀ t : ℕ,
      A.gcd id ∣ t → r * s ≤ t → t ≤ (n - r) * s →
      ∃ w : List ℕ, w.length = n ∧ (∀ a ∈ w, a ∈ A) ∧ w.sum = t := by
  classical
  obtain ⟨r, hr, hcover⟩ := exists_uniform_cyclic_sum_cover δ hδ
  refine ⟨r, hr, ?_⟩
  intro A s hs h0 hend hbound hdensity n hrn t hdiv hlo hhi
  let g : ℕ := A.gcd id
  have hgs : g ∣ s := Finset.gcd_dvd hend
  have hg : 0 < g := by
    by_contra! h
    have : g = 0 := Nat.eq_zero_of_le_zero h
    rw [this, zero_dvd_iff] at hgs
    omega
  let q := s / g
  have hgqs : g * q = s := Nat.mul_div_cancel' hgs
  have hq : 0 < q := by nlinarith
  have hqs : q ≤ s := Nat.div_le_self _ _
  let U := A.image (fun a => a / g)
  have hU0 : 0 ∈ U := Finset.mem_image.mpr ⟨0, h0, by simp⟩
  have hUq : q ∈ U := Finset.mem_image.mpr ⟨s, hend, rfl⟩
  have hUbound : ∀ a ∈ U, a ≤ q := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    exact Nat.div_le_div_right (hbound b hb)
  have hUcard : U.card = A.card := by
    apply Finset.card_image_iff.mpr
    intro a ha b hb hab
    have haeq : g * (a / g) = a := Nat.mul_div_cancel' (Finset.gcd_dvd ha)
    have hbeq : g * (b / g) = b := Nat.mul_div_cancel' (Finset.gcd_dvd hb)
    exact haeq.symm.trans ((congrArg (fun x => g * x) hab).trans hbeq)
  let V := U.image (fun a : ℕ => (a : ZMod q))
  have hV0 : (0 : ZMod q) ∈ V := Finset.mem_image.mpr ⟨0, hU0, by simp⟩
  have hVgen : AddSubgroup.closure (V : Set (ZMod q)) = ⊤ :=
    normalized_cyclic_closure A s hend hs.ne' q
  have hVcard : U.card ≤ V.card + 1 := card_residue_image_lower U q hq hUbound
  have hVdensity : δ * q ≤ V.card := by
    have hh : (q : ℝ) ≤ s := by exact_mod_cast hqs
    have hc : (U.card : ℝ) ≤ V.card + 1 := by exact_mod_cast hVcard
    rw [hUcard] at hc
    nlinarith
  let : NeZero q := ⟨hq.ne'⟩
  have hwords := lift_cyclic_sum_cover U q r (hcover q V hV0 hVgen hVdensity)
  have htlo : r * q ≤ t / g := by
    apply (Nat.le_div_iff_mul_le hg).mpr
    calc
      r * q * g = r * s := by rw [mul_assoc, mul_comm q g, hgqs]
      _ ≤ t := hlo
  have hthi : t / g ≤ (n - r) * q := by
    calc
      t / g ≤ ((n - r) * s) / g := Nat.div_le_div_right hhi
      _ = (n - r) * q := Nat.mul_div_assoc (n - r) hgs
  obtain ⟨w, hwlen, hwmem, hwsum⟩ :=
    integer_interval_sum_cover U q r n hq hU0 hUq hUbound hrn hwords (t / g) htlo hthi
  refine ⟨w.map (fun a => g * a), by simpa using hwlen, ?_, ?_⟩
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp (hwmem b hb)
    have heq : g * (c / g) = c := Nat.mul_div_cancel' (Finset.gcd_dvd hc)
    rwa [heq]
  · rw [List.sum_map_mul_left]
    simp only [List.map_id', hwsum]
    exact Nat.mul_div_cancel' hdiv

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GoodCellTargets
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Shifted cell indices and target sums -/

namespace Ostmann

theorem cellDifferences_card (I : Finset ℕ) (a : ℕ) (hlo : ∀ x ∈ I, a ≤ x) :
    (cellDifferences I a).card = I.card := by
  apply Finset.card_image_iff.mpr
  intro x hx y hy h
  have hx' := hlo x hx
  have hy' := hlo y hy
  change x - a = y - a at h
  omega

/-- A dense interval set realizes every interior target in the appropriate
residue class, with an exact prescribed number of cell labels. -/
theorem dense_cell_exact_sum (δ : ℝ) (hδ : 0 < δ) :
    ∃ r : ℕ, 0 < r ∧ ∀ (I : Finset ℕ) (a b : ℕ),
      a < b → a ∈ I → b ∈ I → (∀ x ∈ I, a ≤ x ∧ x ≤ b) →
      δ * (b - a : ℕ) + 1 ≤ I.card → ∀ n : ℕ, r ≤ n → ∀ t : ℕ,
      (cellDifferences I a).gcd id ∣ t - n * a →
      n * a + r * (b - a) ≤ t → t ≤ n * a + (n - r) * (b - a) →
      ∃ w : List ℕ, w.length = n ∧ (∀ x ∈ w, x ∈ I) ∧ w.sum = t := by
  classical
  obtain ⟨r, hr, hcover⟩ := dense_difference_sum_cover δ hδ
  refine ⟨r, hr, ?_⟩
  intro I a b hab ha hb hbounds hdensity n hrn t hdiv htlo hthi
  let A := cellDifferences I a
  have h0 : 0 ∈ A := Finset.mem_image.mpr ⟨a, ha, Nat.sub_self _⟩
  have hs : b - a ∈ A := Finset.mem_image.mpr ⟨b, hb, rfl⟩
  have hbound : ∀ x ∈ A, x ≤ b - a := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact Nat.sub_le_sub_right (hbounds y hy).2 a
  have hcard : A.card = I.card := cellDifferences_card I a (fun x hx => (hbounds x hx).1)
  obtain ⟨w, hwlen, hwmem, hwsum⟩ := hcover A (b - a) (Nat.sub_pos_of_lt hab)
    h0 hs hbound (by rwa [hcard]) n hrn (t - n * a) hdiv (by omega) (by omega)
  refine ⟨w.map (fun x => a + x), by simpa using hwlen, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp (hwmem y hy)
    rwa [Nat.add_sub_of_le (hbounds z hz).1]
  · have ht : n * a ≤ t := by omega
    have hsum (v : List ℕ) : (v.map (fun x => a + x)).sum = v.length * a + v.sum := by
      induction v with
      | nil => simp
      | cons x v ih =>
          simp only [List.map_cons, List.sum_cons, List.length_cons, ih, Nat.add_mul, Nat.one_mul]
          omega
    rw [hsum w, hwlen, hwsum]
    omega

/-- Density bounds the lattice spacing of the cell differences. -/
theorem dense_difference_gcd_bound (A : Finset ℕ) (s : ℕ) (hs : 0 < s)
    (hend : s ∈ A) (hbound : ∀ a ∈ A, a ≤ s) (δ : ℝ)
    (hdensity : δ * s + 1 ≤ A.card) :
    δ * (A.gcd id : ℕ) ≤ 1 := by
  classical
  let g : ℕ := A.gcd id
  have hgs : g ∣ s := Finset.gcd_dvd hend
  have hg : 0 < g := by
    by_contra! h
    have : g = 0 := Nat.eq_zero_of_le_zero h
    rw [this, zero_dvd_iff] at hgs
    omega
  let U := A.image (fun a => a / g)
  have hUcard : U.card = A.card := by
    apply Finset.card_image_iff.mpr
    intro a ha b hb hab
    have haeq : g * (a / g) = a := Nat.mul_div_cancel' (Finset.gcd_dvd ha)
    have hbeq : g * (b / g) = b := Nat.mul_div_cancel' (Finset.gcd_dvd hb)
    exact haeq.symm.trans ((congrArg (fun x => g * x) hab).trans hbeq)
  have hsubset : U ⊆ Finset.range (s / g + 1) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (hbound y hy)))
  have hc : A.card ≤ s / g + 1 := by
    simpa only [hUcard, Finset.card_range] using Finset.card_le_card hsubset
  have hcount : g * A.card ≤ s + g := by
    have hh := Nat.mul_le_mul_left g hc
    rw [Nat.mul_add, Nat.mul_div_cancel' hgs, Nat.mul_one] at hh
    exact hh
  have hr : (g : ℝ) * A.card ≤ s + g := by exact_mod_cast hcount
  have hgr : (0 : ℝ) < g := by exact_mod_cast hg
  have hsr : (0 : ℝ) < s := by exact_mod_cast hs
  change δ * (g : ℝ) ≤ 1
  nlinarith [mul_le_mul_of_nonneg_left hdensity hgr.le]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_RoundedCellTargets
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rounding target sums to the actual cell lattice -/

namespace Ostmann

private theorem nat_lattice_rounddown (g : ℕ) (hg : 0 < g) (T : ℝ) (hT : 0 ≤ T) :
    ∃ t : ℕ, g ∣ t ∧ (t : ℝ) ≤ T ∧ T < (t : ℝ) + g := by
  let j := ⌊T / g⌋₊
  have hgr : (0 : ℝ) < g := by exact_mod_cast hg
  have hlo : (j : ℝ) * g ≤ T :=
    (le_div_iff₀ hgr).mp (Nat.floor_le (div_nonneg hT hgr.le))
  have hhi : T < ((j : ℝ) + 1) * g :=
    (div_lt_iff₀ hgr).mp (Nat.lt_floor_add_one (T / g))
  refine ⟨g * j, dvd_mul_right _ _, ?_, ?_⟩
  · push_cast
    nlinarith
  · push_cast
    nlinarith

/-- An interior real target can be realized to bounded accuracy. The error
bound depends only on the density of good cells, not on their scale. -/
theorem dense_cell_approximate_sum (δ : ℝ) (hδ : 0 < δ) :
    ∃ r : ℕ, 0 < r ∧ ∀ (I : Finset ℕ) (a b : ℕ),
      a < b → a ∈ I → b ∈ I → (∀ x ∈ I, a ≤ x ∧ x ≤ b) →
      δ * (b - a : ℕ) + 1 ≤ I.card → ∀ n : ℕ, r ≤ n → ∀ T : ℝ,
      (n * a + r * (b - a) + (cellDifferences I a).gcd id : ℕ) ≤ T →
      T ≤ (n * a + (n - r) * (b - a) : ℕ) →
      ∃ w : List ℕ, w.length = n ∧ (∀ x ∈ w, x ∈ I) ∧
        |(w.sum : ℝ) - T| < δ⁻¹ := by
  classical
  obtain ⟨r, hr, hcover⟩ := dense_cell_exact_sum δ hδ
  refine ⟨r, hr, ?_⟩
  intro I a b hab ha hb hbounds hdensity n hrn T hlo hhi
  let A := cellDifferences I a
  let s := b - a
  let g : ℕ := A.gcd id
  have hs : 0 < s := Nat.sub_pos_of_lt hab
  have hend : s ∈ A := Finset.mem_image.mpr ⟨b, hb, rfl⟩
  have hbound : ∀ x ∈ A, x ≤ s := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact Nat.sub_le_sub_right (hbounds y hy).2 a
  have hcard : A.card = I.card := cellDifferences_card I a (fun x hx => (hbounds x hx).1)
  have hd : δ * s + 1 ≤ A.card := by rwa [hcard]
  have hspacing : δ * (g : ℝ) ≤ 1 := dense_difference_gcd_bound A s hs hend hbound δ hd
  have hgs : g ∣ s := Finset.gcd_dvd hend
  have hg : 0 < g := by
    by_contra! h
    have : g = 0 := Nat.eq_zero_of_le_zero h
    rw [this, zero_dvd_iff] at hgs
    omega
  have hlo' : (n * a : ℕ) + (r * s : ℕ) + (g : ℝ) ≤ T := by
    exact_mod_cast hlo
  have hhi' : T ≤ (n * a : ℕ) + ((n - r) * s : ℕ) := by
    exact_mod_cast hhi
  obtain ⟨t, htdiv, htlo, hthi⟩ := nat_lattice_rounddown g hg (T - (n * a : ℕ))
    (by
      have hnon : (0 : ℝ) ≤ (r * s : ℕ) := by positivity
      have hgnon : (0 : ℝ) ≤ g := by positivity
      linarith)
  have htl : r * s ≤ t := by
    have hh : (r * s : ℕ) ≤ (t : ℝ) := by linarith
    exact_mod_cast hh
  have htu : t ≤ (n - r) * s := by
    have hh : (t : ℝ) ≤ ((n - r) * s : ℕ) := by linarith
    exact_mod_cast hh
  change r * (b - a) ≤ t at htl
  change t ≤ (n - r) * (b - a) at htu
  obtain ⟨w, hwlen, hwmem, hwsum⟩ := hcover I a b hab ha hb hbounds hdensity n hrn
    (n * a + t) (by simpa using htdiv) (by omega) (by omega)
  refine ⟨w, hwlen, hwmem, ?_⟩
  have hsum : (w.sum : ℝ) = (n * a : ℕ) + (t : ℝ) := by exact_mod_cast hwsum
  have hdiff : |(w.sum : ℝ) - T| < (g : ℝ) := by
    rw [hsum, abs_of_nonpos (by linarith)]
    linarith
  rw [← one_div]
  apply (lt_div_iff₀ hδ).mpr
  calc
    |(w.sum : ℝ) - T| * δ < (g : ℝ) * δ := mul_lt_mul_of_pos_right hdiff hδ
    _ ≤ 1 := by nlinarith [hspacing]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_LargeCellTargets
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing the number of cell labels for a large target

The number of labels is the floor of the target divided by the midpoint
of the extreme cell indices. All constants depend only on the density.
-/

namespace Ostmann

/-- A dense set of positive cell indices realizes all sufficiently large
real targets, with a number of labels comparable to target divided by scale. -/
theorem dense_cell_large_target (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (I : Finset ℕ) (a b : ℕ),
      a < b → a ∈ I → b ∈ I → (∀ x ∈ I, a ≤ x ∧ x ≤ b) →
      δ * b + 2 ≤ I.card → ∀ T : ℝ, C * b ≤ T →
      ∃ (n : ℕ) (w : List ℕ), w.length = n ∧ (∀ x ∈ w, x ∈ I) ∧
        |(w.sum : ℝ) - T| < δ⁻¹ ∧ (n : ℝ) * b ≤ 2 * T ∧ T < (n + 1 : ℕ) * b := by
  classical
  obtain ⟨r, hr, happrox⟩ := dense_cell_approximate_sum δ hδ
  let K : ℕ := 2 * r + 1 + ⌈((2 : ℝ) * r + 2 + 2 / δ) / δ⌉₊
  refine ⟨(K : ℝ) + 1, by positivity, ?_⟩
  intro I a b hab ha hb hbounds hdensity T hT
  have hbpos : 0 < b := lt_of_le_of_lt (Nat.zero_le _) hab
  have hbr : (0 : ℝ) < b := by exact_mod_cast hbpos
  let s := b - a
  have hs : 0 < s := Nat.sub_pos_of_lt hab
  have hsr : (0 : ℝ) < s := by exact_mod_cast hs
  have hsb : (s : ℝ) ≤ b := by exact_mod_cast Nat.sub_le b a
  have hidentity : (s : ℝ) = (b : ℝ) - a := by
    dsimp [s]
    rw [Nat.cast_sub hab.le]
  let A := cellDifferences I a
  have hend : s ∈ A := Finset.mem_image.mpr ⟨b, hb, rfl⟩
  have hbound : ∀ x ∈ A, x ≤ s := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact Nat.sub_le_sub_right (hbounds y hy).2 a
  have hcard : A.card = I.card := cellDifferences_card I a (fun x hx => (hbounds x hx).1)
  have hcap : A.card ≤ s + 1 := by
    calc
      A.card ≤ (Finset.range (s + 1)).card := Finset.card_le_card (fun x hx =>
        Finset.mem_range.mpr (Nat.lt_succ_of_le (hbound x hx)))
      _ = _ := Finset.card_range _
  have hspan : δ * b ≤ s := by
    have hh : (I.card : ℝ) ≤ (s : ℝ) + 1 := by exact_mod_cast hcard ▸ hcap
    linarith
  have hd : δ * s + 1 ≤ A.card := by
    rw [hcard]
    nlinarith
  have hdI : δ * (b - a : ℕ) + 1 ≤ I.card := by rwa [hcard] at hd
  let g : ℕ := A.gcd id
  have hspacing : δ * (g : ℝ) ≤ 1 := dense_difference_gcd_bound A s hs hend hbound δ hd
  have hgupper : (g : ℝ) ≤ 1 / δ := (le_div_iff₀ hδ).mpr (by nlinarith)
  let μ : ℝ := ((a : ℝ) + b) / 2
  have hμ : 0 < μ := by dsimp [μ]; positivity
  have hμb : μ ≤ b := by
    dsimp [μ]
    have : (a : ℝ) ≤ b := by exact_mod_cast hab.le
    linarith
  have hbμ : (b : ℝ) ≤ 2 * μ := by
    dsimp [μ]
    have := Nat.cast_nonneg (α := ℝ) a
    linarith
  have hT0 : 0 ≤ T := by nlinarith
  let n := ⌊T / μ⌋₊
  have hnlow : (n : ℝ) * μ ≤ T := (le_div_iff₀ hμ).mp (Nat.floor_le (div_nonneg hT0 hμ.le))
  have hnup : T < ((n : ℝ) + 1) * μ := (div_lt_iff₀ hμ).mp (Nat.lt_floor_add_one (T / μ))
  have hKn : K ≤ n := Nat.le_floor ((le_div_iff₀ hμ).mpr (by nlinarith))
  have hrn : r ≤ n := by
    have : r ≤ K := by dsimp [K]; omega
    omega
  have hknδ : (2 : ℝ) * r + 2 + 2 / δ ≤ (n : ℝ) * δ := by
    have hc := Nat.le_ceil (((2 : ℝ) * r + 2 + 2 / δ) / δ)
    have hcn : ⌈((2 : ℝ) * r + 2 + 2 / δ) / δ⌉₊ ≤ n := by
      dsimp [K] at hKn
      omega
    have hcnr : (⌈((2 : ℝ) * r + 2 + 2 / δ) / δ⌉₊ : ℝ) ≤ n := by exact_mod_cast hcn
    exact (div_le_iff₀ hδ).mp (hc.trans hcnr)
  have hgb : (g : ℝ) ≤ (1 / δ) * b :=
    hgupper.trans (le_mul_of_one_le_right (by positivity) (by exact_mod_cast hbpos))
  have hwide : 2 * r * s + 2 * b + 2 * g ≤ (n : ℝ) * s := by
    calc
      _ ≤ 2 * r * b + 2 * b + 2 * ((1 / δ) * b) := by gcongr
      _ = (2 * r + 2 + 2 / δ) * b := by ring
      _ ≤ ((n : ℝ) * δ) * b := mul_le_mul_of_nonneg_right hknδ hbr.le
      _ = (n : ℝ) * (δ * b) := by ring
      _ ≤ (n : ℝ) * s := mul_le_mul_of_nonneg_left hspan (Nat.cast_nonneg _)
  have hlo : (n * a + r * (b - a) + (cellDifferences I a).gcd id : ℕ) ≤ T := by
    push_cast
    change (n : ℝ) * a + r * s + g ≤ T
    dsimp [μ] at hnlow
    nlinarith
  have hhi : T ≤ (n * a + (n - r) * (b - a) : ℕ) := by
    push_cast
    rw [Nat.cast_sub hrn]
    change T ≤ (n : ℝ) * a + ((n : ℝ) - r) * s
    dsimp [μ] at hnup
    nlinarith
  obtain ⟨w, hwlen, hwmem, hwerr⟩ := happrox I a b hab ha hb hbounds hdI n hrn T hlo hhi
  refine ⟨n, w, hwlen, hwmem, hwerr, ?_, ?_⟩
  · nlinarith
  · push_cast
    exact hnup.trans_le (mul_le_mul_of_nonneg_left hμb (by positivity))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WeightedPrimeSelection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite weighted deletion estimates for selecting the biased prime block -/

namespace Ostmann

open scoped BigOperators Classical

theorem weighted_good_mass (P : Finset ℕ) (w : ℕ → ℝ) (good : ℕ → Prop)
    [DecidablePred good] (M E : ℝ)
    (htotal : M ≤ ∑ p ∈ P, w p)
    (hbad : (∑ p ∈ P.filter (fun p => ¬good p), w p) ≤ E) :
    M - E ≤ ∑ p ∈ P.filter good, w p := by
  have hsum := Finset.sum_filter_add_sum_filter_not P good w
  linarith

theorem weighted_bias_superlevel (P : Finset ℕ) (w b : ℕ → ℝ) (δ : ℝ)
    (hw : ∀ p ∈ P, 0 ≤ w p) (hδ : 0 ≤ δ) (hb : ∀ p ∈ P, b p ≤ 1)
    (hbias : δ * (∑ p ∈ P, w p) ≤ ∑ p ∈ P, w p * b p) :
    (δ / 2) * (∑ p ∈ P, w p) ≤ ∑ p ∈ P.filter (fun p => δ / 2 ≤ b p), w p := by
  have hpoint (p : ℕ) (hp : p ∈ P) :
      w p * b p ≤ (δ / 2) * w p + if δ / 2 ≤ b p then w p else 0 := by
    split_ifs with h
    · have hh := mul_le_mul_of_nonneg_left (hb p hp) (hw p hp)
      nlinarith [mul_nonneg hδ (hw p hp)]
    · have hh := mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge h)) (hw p hp)
      nlinarith
  have hsum := Finset.sum_le_sum hpoint
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_filter] at hsum
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GoodCellSelection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Selecting many heavy cells with positive mean -/

namespace Ostmann

open scoped BigOperators Classical

/-- Removing low-mass cells from a positively biased shell retains a fixed
amount of mass. -/
theorem positiveHeavyCells_mass (I : Finset ℕ) (w score : ℕ → ℝ) (δ θ : ℝ)
    (hw : ∀ h ∈ I, 0 ≤ w h) (hδ : 0 ≤ δ) (hθ : 0 ≤ θ)
    (hscore : ∀ h ∈ I, score h ≤ 1)
    (hbias : δ * (∑ h ∈ I, w h) ≤ ∑ h ∈ I, w h * score h)
    (hthin : I.card * θ ≤ (δ / 4) * ∑ h ∈ I, w h) :
    (δ / 4) * (∑ h ∈ I, w h) ≤ ∑ h ∈ positiveHeavyCells I w score δ θ, w h := by
  let S := I.filter (fun h => δ / 2 ≤ score h)
  have hS : (δ / 2) * (∑ h ∈ I, w h) ≤ ∑ h ∈ S, w h :=
    weighted_bias_superlevel I w score δ hw hδ hscore hbias
  have hbad : (∑ h ∈ S.filter (fun h => ¬θ ≤ w h), w h) ≤ I.card * θ := by
    calc
      _ ≤ ∑ _h ∈ S.filter (fun h => ¬θ ≤ w h), θ := by
        apply Finset.sum_le_sum
        intro h hh
        exact (lt_of_not_ge (Finset.mem_filter.mp hh).2).le
      _ = ((S.filter (fun h => ¬θ ≤ w h)).card : ℝ) * θ := by simp
      _ ≤ I.card * θ := by
        gcongr
        exact fun h hh => (Finset.mem_filter.mp (Finset.mem_filter.mp hh).1).1
  have heq : S.filter (fun h => θ ≤ w h) = positiveHeavyCells I w score δ θ := by
    ext h
    simp only [S, positiveHeavyCells, Finset.mem_filter]
    tauto
  have hh := weighted_good_mass S w (fun h => θ ≤ w h)
    ((δ / 2) * ∑ h ∈ I, w h) (I.card * θ) hS hbad
  rw [heq] at hh
  linarith

/-- A cellwise upper mass bound converts retained mass into a lower bound
on the number of usable cell indices. -/
theorem positiveHeavyCells_card (I : Finset ℕ) (w score : ℕ → ℝ) (δ θ M : ℝ)
    (hw : ∀ h ∈ I, 0 ≤ w h) (hδ : 0 ≤ δ) (hθ : 0 ≤ θ)
    (hscore : ∀ h ∈ I, score h ≤ 1)
    (hbias : δ * (∑ h ∈ I, w h) ≤ ∑ h ∈ I, w h * score h)
    (hthin : I.card * θ ≤ (δ / 4) * ∑ h ∈ I, w h)
    (hcap : ∀ h ∈ I, w h ≤ M) :
    (δ / 4) * (∑ h ∈ I, w h) ≤
      (positiveHeavyCells I w score δ θ).card * M := by
  apply (positiveHeavyCells_mass I w score δ θ hw hδ hθ hscore hbias hthin).trans
  calc
    _ ≤ ∑ _h ∈ positiveHeavyCells I w score δ θ, M := by
      apply Finset.sum_le_sum
      intro h hh
      exact hcap h (Finset.mem_filter.mp hh).1
    _ = _ := by simp

/-- An arbitrary dense set of cell indices has the required target words;
its minimum and maximum need not be chosen in advance. -/
theorem dense_index_target (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (I : Finset ℕ) (B : ℕ),
      (∀ x ∈ I, x ≤ B) → δ * B + 2 ≤ I.card → ∀ T : ℝ,
      C * B ≤ T → ∃ (n : ℕ) (w : List ℕ),
      w.length = n ∧ (∀ x ∈ w, x ∈ I) ∧ |(w.sum : ℝ) - T| < δ⁻¹ ∧
      (n : ℝ) * B ≤ 2 * T / δ ∧ T < (n + 1 : ℕ) * B := by
  obtain ⟨C, hC, htarget⟩ := dense_cell_large_target δ hδ
  refine ⟨C, hC, ?_⟩
  intro I B hbound hdensity T hT
  have hcard : 2 ≤ I.card := by
    have hnon : (0 : ℝ) ≤ δ * B := mul_nonneg hδ.le (Nat.cast_nonneg _)
    have : (2 : ℝ) ≤ I.card := by linarith
    exact_mod_cast this
  have hne : I.Nonempty := Finset.card_pos.mp (by omega)
  let a := I.min' hne
  let b := I.max' hne
  have ha : a ∈ I := Finset.min'_mem _ _
  have hb : b ∈ I := Finset.max'_mem _ _
  have hminmax : ∀ x ∈ I, a ≤ x ∧ x ≤ b := fun x hx =>
    ⟨Finset.min'_le _ _ hx, Finset.le_max' _ _ hx⟩
  have hab : a < b := by
    have hab' : a ≤ b := (hminmax a ha).2
    by_contra! h
    have heq : a = b := le_antisymm hab' h
    have hsub : I ⊆ {a} := by
      intro x hx
      have hh := hminmax x hx
      simp only [Finset.mem_singleton]
      omega
    have hc := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hc
    omega
  have hbB : b ≤ B := hbound b hb
  have hd : δ * b + 2 ≤ I.card := by
    have hh : (b : ℝ) ≤ B := by exact_mod_cast hbB
    nlinarith
  have hc : I.card ≤ b + 1 := by
    have hh := Finset.card_le_card (show I ⊆ Finset.range (b + 1) from
      fun x hx => Finset.mem_range.mpr (Nat.lt_succ_of_le (hminmax x hx).2))
    simpa only [Finset.card_range] using hh
  have hδB : δ * B ≤ b := by
    have hh : (I.card : ℝ) ≤ (b : ℝ) + 1 := by exact_mod_cast hc
    linarith
  obtain ⟨n, w, hwlen, hwmem, hwerr, hn, hn'⟩ := htarget I a b hab ha hb hminmax hd T
    ((mul_le_mul_of_nonneg_left (by exact_mod_cast hbB) hC.le).trans hT)
  refine ⟨n, w, hwlen, hwmem, hwerr, ?_, ?_⟩
  · apply (le_div_iff₀ hδ).mpr
    have hh := mul_le_mul_of_nonneg_left hδB (Nat.cast_nonneg (α := ℝ) n)
    nlinarith
  · exact hn'.trans_le (mul_le_mul_of_nonneg_left (by exact_mod_cast hbB) (by positivity))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FiniteCellMeans
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Means on the actual fibers of a finite partition -/

namespace Ostmann

open scoped BigOperators Classical

theorem finiteCellMass_nonneg (P : Finset ℕ) (label : ℕ → ℕ) (μ : ℕ → ℝ)
    (hμ : ∀ p ∈ P, 0 ≤ μ p) (h : ℕ) : 0 ≤ finiteCellMass P label μ h := by
  exact Finset.sum_nonneg (fun p hp => hμ p (Finset.mem_filter.mp hp).1)

theorem finiteCellMass_mul_mean (P : Finset ℕ) (label : ℕ → ℕ) (μ f : ℕ → ℝ)
    (hμ : ∀ p ∈ P, 0 ≤ μ p) (h : ℕ) :
    finiteCellMass P label μ h * finiteCellMean P label μ f h =
      ∑ p ∈ P.filter (fun p => label p = h), μ p * f p := by
  by_cases hz : finiteCellMass P label μ h = 0
  · have hpoint : ∀ p ∈ P.filter (fun p => label p = h), μ p = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun p hp => hμ p (Finset.mem_filter.mp hp).1)).mp hz
    simp only [finiteCellMean, hz, zero_mul]
    exact (Finset.sum_eq_zero (fun p hp => by rw [hpoint p hp, zero_mul])).symm
  · simp only [finiteCellMean, ← mul_assoc, mul_inv_cancel₀ hz, one_mul]

theorem finiteCellMean_le_one (P : Finset ℕ) (label : ℕ → ℕ) (μ f : ℕ → ℝ)
    (hμ : ∀ p ∈ P, 0 ≤ μ p) (hf : ∀ p ∈ P, f p ≤ 1) (h : ℕ) :
    finiteCellMean P label μ f h ≤ 1 := by
  have hnon := finiteCellMass_nonneg P label μ hμ h
  by_cases hz : finiteCellMass P label μ h = 0
  · simp [finiteCellMean, hz]
  · have hpos : 0 < finiteCellMass P label μ h := lt_of_le_of_ne hnon (Ne.symm hz)
    apply (mul_le_mul_iff_right₀ hpos).mp
    rw [finiteCellMass_mul_mean P label μ f hμ h, mul_one]
    apply Finset.sum_le_sum
    intro p hp
    exact mul_le_of_le_one_right (hμ p (Finset.mem_filter.mp hp).1) (hf p (Finset.mem_filter.mp hp).1)

theorem finiteCellMass_sum (P I : Finset ℕ) (label : ℕ → ℕ) (μ : ℕ → ℝ)
    (hlabel : ∀ p ∈ P, label p ∈ I) :
    (∑ h ∈ I, finiteCellMass P label μ h) = ∑ p ∈ P, μ p := by
  exact Finset.sum_fiberwise_of_maps_to hlabel μ

theorem finiteCellMean_sum (P I : Finset ℕ) (label : ℕ → ℕ) (μ f : ℕ → ℝ)
    (hlabel : ∀ p ∈ P, label p ∈ I) (hμ : ∀ p ∈ P, 0 ≤ μ p) :
    (∑ h ∈ I, finiteCellMass P label μ h * finiteCellMean P label μ f h) =
      ∑ p ∈ P, μ p * f p := by
  simp_rw [finiteCellMass_mul_mean P label μ f hμ]
  exact Finset.sum_fiberwise_of_maps_to hlabel (fun p => μ p * f p)

/-- A positive average over the primes yields many heavy cells of positive
average under the actual fiber masses, without a new probabilistic input. -/
theorem finite_positive_heavy_cells (P I : Finset ℕ) (label : ℕ → ℕ) (μ f : ℕ → ℝ)
    (hlabel : ∀ p ∈ P, label p ∈ I) (hμ : ∀ p ∈ P, 0 ≤ μ p)
    (hf : ∀ p ∈ P, f p ≤ 1) (δ θ M : ℝ) (hδ : 0 ≤ δ) (hθ : 0 ≤ θ)
    (hbias : δ * (∑ p ∈ P, μ p) ≤ ∑ p ∈ P, μ p * f p)
    (hthin : I.card * θ ≤ (δ / 4) * ∑ p ∈ P, μ p)
    (hcap : ∀ h ∈ I, finiteCellMass P label μ h ≤ M) :
    (δ / 4) * (∑ p ∈ P, μ p) ≤
      (positiveHeavyCells I (finiteCellMass P label μ) (finiteCellMean P label μ f) δ θ).card * M := by
  have hh := positiveHeavyCells_card I (finiteCellMass P label μ) (finiteCellMean P label μ f)
    δ θ M (fun h _ => finiteCellMass_nonneg P label μ hμ h) hδ hθ
    (fun h _ => finiteCellMean_le_one P label μ f hμ hf h)
    (by rw [finiteCellMass_sum P I label μ hlabel, finiteCellMean_sum P I label μ f hlabel hμ]; exact hbias)
    (by rw [finiteCellMass_sum P I label μ hlabel]; exact hthin) hcap
  rwa [finiteCellMass_sum P I label μ hlabel] at hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ComplexCellMeans
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Complex averages on the actual prime cells -/

namespace Ostmann

open scoped BigOperators Classical

theorem complexCellMean_re (P : Finset ℕ) (label : ℕ → ℕ) (μ : ℕ → ℝ)
    (F : ℕ → ℂ) (h : ℕ) :
    (complexCellMean P label μ F h).re = finiteCellMean P label μ (fun p => (F p).re) h := by
  simp [complexCellMean, finiteCellMean, ← Complex.ofReal_inv, Complex.mul_re, Complex.re_sum]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PositiveWordBins
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive word means and a common product bin -/

namespace Ostmann

open scoped BigOperators Classical

theorem binnedWordAverage_sum {A B : Type*} [Fintype A] [Fintype B] {n : ℕ}
    (μ : Fin n → A → ℝ) (F : Fin n → A → ℂ) (bin : (Fin n → A) → B) :
    (∑ b, binnedWordAverage μ F bin b) = ∏ i, ∑ a, (μ i a : ℂ) * F i a := by
  unfold binnedWordAverage
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]
  simp_rw [productPrior, Complex.ofReal_prod, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun (i : Fin n) (a : A) => (μ i a : ℂ) * F i a)).symm

/-- A finite product-bin partition retains a large coefficient in at least
one bin. -/
theorem exists_large_complex_bin {B : Type*} [Fintype B] [Nonempty B]
    (v : B → ℂ) : ∃ b, ‖∑ j, v j‖ ≤ (Fintype.card B : ℝ) * ‖v b‖ := by
  obtain ⟨b, _, hb⟩ := Finset.exists_max_image Finset.univ (fun j => ‖v j‖) Finset.univ_nonempty
  refine ⟨b, (norm_sum_le _ _).trans ?_⟩
  calc
    (∑ j, ‖v j‖) ≤ ∑ _j : B, ‖v b‖ := Finset.sum_le_sum (fun j hj => hb j hj)
    _ = _ := by simp

/-- A single bin works on a proportionate set of the actual endpoints. -/
theorem common_large_bin {B : Type*} [Fintype B] [Nonempty B]
    (E : Finset ℕ) (v : ℕ → B → ℂ) (η : ℝ)
    (hE : ∀ a ∈ E, η ≤ ‖∑ b, v a b‖) :
    ∃ b, ∃ S : Finset ℕ, S ⊆ E ∧ E.card ≤ Fintype.card B * S.card ∧
      ∀ a ∈ S, η ≤ (Fintype.card B : ℝ) * ‖v a b‖ := by
  have hex : ∀ a : ℕ, ∃ b, ‖∑ j, v a j‖ ≤ (Fintype.card B : ℝ) * ‖v a b‖ :=
    fun a => exists_large_complex_bin (v a)
  choose b hb using hex
  obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ
    (fun j => (E.filter (fun a => b a = j)).card) Finset.univ_nonempty
  refine ⟨j, E.filter (fun a => b a = j), Finset.filter_subset _ _, ?_, ?_⟩
  · calc
      E.card = ∑ j : B, (E.filter (fun a => b a = j)).card := by
        simpa using (Finset.card_eq_sum_card_fiberwise (s := E) (t := Finset.univ) (fun a _ => Finset.mem_univ (b a)))
      _ ≤ ∑ _j : B, (E.filter (fun a => b a = j)).card :=
        Finset.sum_le_sum (fun k hk => hj k hk)
      _ = _ := by simp
  · intro a ha
    obtain ⟨haE, haj⟩ := Finset.mem_filter.mp ha
    exact (hE a haE).trans (by simpa [haj] using hb a)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeHarmonicWeightBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit variation cost on a short logarithmic interval -/

namespace Ostmann

open MeasureTheory

theorem primeHarmonicWeight_le {u t : ℝ} (hu : 0 < u)
    (hlogu : 1 ≤ Real.log u) (hut : u ≤ t) :
    |primeHarmonicWeight t| ≤ 1 / u := by
  have ht : 0 < t := hu.trans_le hut
  have hlogt : 1 ≤ Real.log t := hlogu.trans (Real.log_le_log hu hut)
  have hp : u ≤ t * Real.log t := hut.trans (le_mul_of_one_le_right ht.le hlogt)
  rw [primeHarmonicWeight, abs_of_nonneg (inv_nonneg.mpr (by positivity))]
  simpa only [one_div] using one_div_le_one_div_of_le hu hp

theorem primeHarmonicDerivative_le {u t : ℝ} (hu : 0 < u)
    (hlogu : 1 ≤ Real.log u) (hut : u ≤ t) :
    |primeHarmonicDerivative t| ≤ 2 / u ^ 2 := by
  have ht : 0 < t := hu.trans_le hut
  have hlogt : 1 ≤ Real.log t := hlogu.trans (Real.log_le_log hu hut)
  have hl : 0 < Real.log t := by linarith
  have hb : (Real.log t + 1) / Real.log t ^ 2 ≤ 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hl)).mpr
    nlinarith [sq_nonneg (Real.log t - 1)]
  have heq : |primeHarmonicDerivative t| =
      ((Real.log t + 1) / Real.log t ^ 2) * (1 / t) ^ 2 := by
    rw [primeHarmonicDerivative, abs_div, abs_neg, abs_of_pos (by linarith),
      abs_of_nonneg (sq_nonneg _)]
    field_simp
  rw [heq]
  calc
    _ ≤ 2 * (1 / t) ^ 2 := mul_le_mul_of_nonneg_right hb (sq_nonneg _)
    _ ≤ 2 * (1 / u) ^ 2 := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (one_div_le_one_div_of_le hu hut) 2) (by norm_num)
    _ = _ := by ring

/-- A theta error of size `E` on an interval with `v ≤ 3u` costs at most
`6E/u` in the reciprocal-prime measure. -/
theorem primeHarmonic_short_interval_error (q a : ℕ) (φ χ β : ℝ) (hβ : β ≠ 0)
    {u v : ℝ} (hu : 1 < u) (hlogu : 1 ≤ Real.log u)
    (huv : u ≤ v) (hshort : v ≤ 3 * u) (E : ℝ) (hE : 0 ≤ E)
    (hθ : ∀ t ∈ Set.Icc u v, |primeProgressionTheta q a t - thetaMainTerm φ χ β t| ≤ E) :
    |reciprocalPrimeInterval q a u v -
      ∫ t in Set.Ioc u v, primeHarmonicWeight t * thetaMainDensity φ χ β t| ≤ 6 * E / u := by
  have hu0 : 0 < u := lt_trans zero_lt_one hu
  have h := primeHarmonic_error_le q a φ χ β hβ hu huv E (1 / u) (2 / u ^ 2)
    (by positivity) (by positivity) hθ
    (fun t ht => primeHarmonicWeight_le hu0 hlogu ht.1)
    (fun t ht => primeHarmonicDerivative_le hu0 hlogu ht.1)
  refine h.trans ?_
  calc
    _ ≤ E * (2 * (1 / u) + (3 * u - u) * (2 / u ^ 2)) := by gcongr
    _ = 6 * E / u := by field_simp; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ThetaToHarmonic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reciprocal-prime estimates derived from the published theta bound -/

namespace Ostmann

open MeasureTheory

/-- The classical theta error on a multiplicative interval transfers with
an absolute factor of eighteen, uniformly in the modulus and residue. -/
theorem theta_to_harmonic_error (q a : ℕ) (φ χ β c C : ℝ) (hβ : β ≠ 0)
    (hc : 0 ≤ c) (hC : 0 ≤ C) {u v : ℝ} (hu : 1 < u)
    (hlogu : 1 ≤ Real.log u) (huv : u ≤ v) (hshort : v ≤ 3 * u)
    (hθ : ∀ t ∈ Set.Icc u v,
      |primeProgressionTheta q a t - thetaMainTerm φ χ β t| ≤
        C * t * Real.exp (-c * Real.sqrt (Real.log t))) :
    |reciprocalPrimeInterval q a u v -
      ∫ t in Set.Ioc u v, primeHarmonicWeight t * thetaMainDensity φ χ β t| ≤
        18 * C * Real.exp (-c * Real.sqrt (Real.log u)) := by
  have hu0 : 0 < u := lt_trans zero_lt_one hu
  have hv0 : 0 < v := hu0.trans_le huv
  let E := C * v * Real.exp (-c * Real.sqrt (Real.log u))
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hθ' (t : ℝ) (ht : t ∈ Set.Icc u v) :
      |primeProgressionTheta q a t - thetaMainTerm φ χ β t| ≤ E := by
    apply (hθ t ht).trans
    dsimp [E]
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left ht.2 hC
    · apply Real.exp_le_exp.mpr
      have hs := Real.sqrt_le_sqrt (Real.log_le_log hu0 ht.1)
      nlinarith
    · positivity
    · positivity
  apply (primeHarmonic_short_interval_error q a φ χ β hβ hu hlogu huv hshort E hE hθ').trans
  dsimp [E]
  apply (div_le_iff₀ hu0).mpr
  nlinarith [mul_le_mul_of_nonneg_right hshort
    (mul_nonneg hC (Real.exp_pos (-c * Real.sqrt (Real.log u))).le)]

/-- A log interval of length at most one is a multiplicative interval with
ratio less than three, as required by the uniform partial-summation bound. -/
theorem exp_short_interval_le_three {s t : ℝ} (hst : t ≤ s + 1) :
    Real.exp t ≤ 3 * Real.exp s := by
  calc
    _ ≤ Real.exp (s + 1) := Real.exp_le_exp.mpr hst
    _ = Real.exp s * Real.exp 1 := Real.exp_add s 1
    _ ≤ Real.exp s * 3 := mul_le_mul_of_nonneg_left Real.exp_one_lt_three.le (Real.exp_pos s).le
    _ = _ := mul_comm _ _

/-- The form used in the finite log-cell partition, before the harmless
change of variables in the main integral. -/
theorem theta_to_log_interval_error (q a : ℕ) (φ χ β c C : ℝ) (hβ : β ≠ 0)
    (hc : 0 ≤ c) (hC : 0 ≤ C) {s t : ℝ} (hs : 1 ≤ s)
    (hst : s ≤ t) (hshort : t ≤ s + 1)
    (hθ : ∀ x ∈ Set.Icc (Real.exp s) (Real.exp t),
      |primeProgressionTheta q a x - thetaMainTerm φ χ β x| ≤
        C * x * Real.exp (-c * Real.sqrt (Real.log x))) :
    |reciprocalPrimeInterval q a (Real.exp s) (Real.exp t) -
      ∫ x in Set.Ioc (Real.exp s) (Real.exp t),
        primeHarmonicWeight x * thetaMainDensity φ χ β x| ≤
        18 * C * Real.exp (-c * Real.sqrt s) := by
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  simpa only [Real.log_exp] using theta_to_harmonic_error q a φ χ β c C hβ hc hC
    (Real.one_lt_exp_iff.mpr hs0) (by simpa only [Real.log_exp] using hs)
    (Real.exp_le_exp.mpr hst) (exp_short_interval_le_three hshort) hθ

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PrimeLogDensity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The retained Page density in logarithmic coordinates -/

namespace Ostmann

open MeasureTheory

/-- The Jacobian cancels the `1/x` part of the harmonic weight. The
exceptional contribution has no extra factor of its zero `β`. -/
theorem thetaMain_log_substitution (φ χ β : ℝ) {s t : ℝ}
    (hs : 0 < s) (hst : s ≤ t) :
    (∫ x in Set.Ioc (Real.exp s) (Real.exp t),
      primeHarmonicWeight x * thetaMainDensity φ χ β x) =
        ∫ y in Set.Ioc s t, primeLogDensity φ χ β y := by
  let g := fun x => primeHarmonicWeight x * thetaMainDensity φ χ β x
  have hg : ContinuousOn g (Real.exp '' Set.uIcc s t) := by
    rintro _ ⟨y, hy, rfl⟩
    have hy0 : 0 < y := hs.trans_le (((Set.uIcc_of_le hst) ▸ hy).1)
    have hexp : 1 < Real.exp y := Real.one_lt_exp_iff.mpr hy0
    have hw := (hasDerivAt_primeHarmonicWeight hexp).continuousAt
    have hd : ContinuousAt (thetaMainDensity φ χ β) (Real.exp y) :=
      (continuousAt_const.sub ((Real.continuousAt_rpow_const _ (β - 1)
        (Or.inl (Real.exp_ne_zero y))).const_mul χ)).div_const φ
    exact (hw.mul hd).continuousWithinAt
  have hsub := intervalIntegral.integral_comp_mul_deriv'
    (fun y (_ : y ∈ Set.uIcc s t) => Real.hasDerivAt_exp y)
    Real.continuous_exp.continuousOn hg
  calc
    _ = ∫ x in Real.exp s..Real.exp t, g x :=
      (intervalIntegral.integral_of_le (Real.exp_le_exp.mpr hst)).symm
    _ = ∫ y in s..t, (g ∘ Real.exp) y * Real.exp y := hsub.symm
    _ = ∫ y in s..t, primeLogDensity φ χ β y := by
      apply intervalIntegral.integral_congr
      intro y hy
      have hy0 : 0 < y := hs.trans_le (((Set.uIcc_of_le hst) ▸ hy).1)
      dsimp [g, primeHarmonicWeight, thetaMainDensity, primeLogDensity]
      rw [Real.log_exp, ← Real.exp_mul]
      rw [mul_comm y (β - 1)]
      field_simp
    _ = _ := intervalIntegral.integral_of_le hst

/-- The actual reciprocal-prime interval estimate in logarithmic coordinates,
proved from the precise theta estimate. -/
theorem prime_log_interval_error (q a : ℕ) (φ χ β c C : ℝ) (hβ : β ≠ 0)
    (hc : 0 ≤ c) (hC : 0 ≤ C) {s t : ℝ} (hs : 1 ≤ s)
    (hst : s ≤ t) (hshort : t ≤ s + 1)
    (hθ : ∀ x ∈ Set.Icc (Real.exp s) (Real.exp t),
      |primeProgressionTheta q a x - thetaMainTerm φ χ β x| ≤
        C * x * Real.exp (-c * Real.sqrt (Real.log x))) :
    |reciprocalPrimeInterval q a (Real.exp s) (Real.exp t) -
      ∫ y in Set.Ioc s t, primeLogDensity φ χ β y| ≤
        18 * C * Real.exp (-c * Real.sqrt s) := by
  have h := theta_to_log_interval_error q a φ χ β c C hβ hc hC hs hst hshort hθ
  rwa [thetaMain_log_substitution φ χ β (lt_of_lt_of_le zero_lt_one hs) hst] at h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_WeightedPrimeIntervals
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Freezing a smooth cutoff on an actual prime log cell -/

namespace Ostmann

open scoped BigOperators
open MeasureTheory

theorem log_mem_of_mem_exp_interval {p : ℕ} {s t : ℝ}
    (hp : p ∈ Finset.Ioc ⌊Real.exp s⌋₊ ⌊Real.exp t⌋₊) :
    Real.log (p : ℝ) ∈ Set.Ioc s t := by
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp hp
  have hexp : Real.exp s < p := Nat.lt_of_floor_lt hlo
  have hp0 : (0 : ℝ) < p := (Real.exp_pos s).trans hexp
  exact ⟨(Real.lt_log_iff_exp_lt hp0).mpr hexp,
    (Real.log_le_iff_le_exp hp0).mpr ((Nat.le_floor_iff (Real.exp_pos t).le).mp hhi)⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PublishedProgressionInputs
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Precisely stated published inputs for primes in progressions

Reference: H. L. Montgomery and R. C. Vaughan, *Multiplicative Number
Theory I: Classical Theory*, Cambridge Studies in Advanced Mathematics 97,
Chapter 11, DOI 10.1017/CBO9780511618314.013.

`PublishedProgressionInput.theta` is Corollary 11.20, equations (11.32) and
(11.34), p. 381. `complete` specifies the exceptional zero in Theorem 11.3,
p. 360. `unique` is the real-zero specialization of Corollary 11.10 (Page),
p. 369. The positive zero-free constant can be decreased so these use one
constant and the harmless denominator `log (4*q)` throughout.

These are explicit conditional inputs. In particular, no logarithmic
interval estimate or arithmetic comparison is assumed here.
-/

namespace Ostmann

/-- The logarithmic prime estimate is derived by partial summation; it is
not included among the published assumptions. -/
theorem PublishedProgressionInput.local_log_interval (P : PublishedProgressionInput)
    (q a : ℕ) (hq : 1 ≤ q) (ha : a.Coprime q) {s t : ℝ}
    (hs : 1 ≤ s) (hst : s ≤ t) (hshort : t ≤ s + 1) :
    |reciprocalPrimeInterval q a (Real.exp s) (Real.exp t) -
      ∫ y in Set.Ioc s t, primeLogDensity (Nat.totient q)
        (pageCoefficient (P.localZero q) a) (pageBeta (P.localZero q)) y| ≤
      18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt s) := by
  apply prime_log_interval_error q a _ _ _ _ _ (ne_of_gt (pageBeta_pos _))
    P.decay_pos.le P.errorConstant_nonneg hs hst hshort
  intro x hx
  apply P.theta q hq a ha x
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have htwo : (2 : ℝ) ≤ Real.exp s := by
    have h := Real.add_one_le_exp s
    linarith
  exact htwo.trans hx.1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_OrdinaryPrimeIntervals
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The ordinary prime interval and its normalization

The conductor-one character is trivial, so the ordinary prime prior has
no Page correction. Its logarithmic interval mass and inverse bound are
derived from the same published theta input.
-/

namespace Ostmann

open Filter MeasureTheory

theorem PublishedProgressionInput.localZero_one (P : PublishedProgressionInput) :
    P.localZero 1 = none := by
  cases he : P.localZero 1 with
  | none => rfl
  | some e => exact False.elim (e.modulus_ne_one (Nat.dvd_one.mp (P.divides 1 e he)))

theorem PublishedProgressionInput.ordinary_log_interval (P : PublishedProgressionInput)
    {s t : ℝ} (hs : 1 ≤ s) (hst : s ≤ t) (hshort : t ≤ s + 1) :
    |reciprocalPrimeInterval 1 0 (Real.exp s) (Real.exp t) - Real.log (t / s)| ≤
      18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt s) := by
  have h := P.local_log_interval 1 0 (by norm_num) (by norm_num) hs hst hshort
  rw [P.localZero_one] at h
  simp only [pageCoefficient, pageBeta, Nat.totient_one, Nat.cast_one,
    primeLogDensity, zero_mul, sub_zero, one_mul] at h
  rw [← intervalIntegral.integral_of_le hst,
    integral_one_div_of_pos (by linarith) (by linarith)] at h
  exact h

theorem theta_log_error_small (C c : ℝ) (hc : 0 < c) :
    ∀ᶠ s : ℝ in atTop,
      18 * C * Real.exp (-c * Real.sqrt s) ≤ 1 / (2 * (s + 1)) := by
  have hpow := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 c hc).comp
    Real.tendsto_sqrt_atTop
  have hlin : Tendsto (fun s : ℝ => s * Real.exp (-c * Real.sqrt s)) atTop (nhds 0) := by
    apply hpow.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
    dsimp only [Function.comp_def]
    rw [Real.rpow_two, Real.sq_sqrt hs]
  have hzero := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 c hc).comp
    Real.tendsto_sqrt_atTop
  simp only [Real.rpow_zero, one_mul, Function.comp_def] at hzero
  have hsum : Tendsto (fun s : ℝ =>
      (s + 1) * (18 * C * Real.exp (-c * Real.sqrt s))) atTop (nhds 0) := by
    have hb : Tendsto (fun s : ℝ => 18 * C *
        (s * Real.exp (-c * Real.sqrt s) + Real.exp (-c * Real.sqrt s))) atTop (nhds 0) := by
      simpa only [add_zero, mul_zero] using ((hlin.add hzero).const_mul (18 * C))
    exact hb.congr (fun s => by ring)
  filter_upwards [hsum.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2),
    eventually_ge_atTop (1 : ℝ)] with s hsmall hs
  apply (le_div_iff₀ (by positivity : 0 < 2 * (s + 1))).mpr
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeLogCellUpper
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform upper mass bound on a logarithmic prime cell -/

namespace Ostmann

open Filter
open scoped BigOperators

theorem log_unit_ratio_upper {s : ℝ} (hs : 0 < s) :
    Real.log ((s + 1) / s) ≤ 1 / s := by
  have hh := Real.log_le_sub_one_of_pos (div_pos (by linarith : 0 < s + 1) hs)
  have heq : (s + 1) / s - 1 = 1 / s := by field_simp; ring
  rwa [heq] at hh

theorem PublishedProgressionInput.ordinary_interval_upper (P : PublishedProgressionInput) :
    ∀ᶠ s : ℝ in atTop,
      reciprocalPrimeInterval 1 0 (Real.exp s) (Real.exp (s + 1)) ≤ 2 / s := by
  filter_upwards [theta_log_error_small P.errorConstant P.decay P.decay_pos,
    eventually_ge_atTop (1 : ℝ)] with s herr hs
  have hmain := P.ordinary_log_interval hs (by linarith : s ≤ s + 1) le_rfl
  have hlog := log_unit_ratio_upper (by linarith : 0 < s)
  have herror : 1 / (2 * (s + 1)) ≤ 1 / s :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
  have h := (abs_le.mp hmain).2
  rw [show 2 / s = 1 / s + 1 / s by ring]
  linarith

theorem sum_primeLogCellSet_reciprocal (q a : ℕ) (s t : ℝ) :
    (∑ p ∈ primeLogCellSet q a s t, (p : ℝ)⁻¹) =
      reciprocalPrimeInterval q a (Real.exp s) (Real.exp t) := by
  simp only [primeLogCellSet, Finset.sum_filter, reciprocalPrimeInterval]

/-- Every subset of the actual prime cell has reciprocal mass `O(1/s)`,
uniformly in the subset. -/
theorem PublishedProgressionInput.prime_log_cell_upper (P : PublishedProgressionInput) :
    ∀ᶠ s : ℝ in atTop, ∀ E : Finset ℕ,
      E ⊆ primeLogCellSet 1 0 s (s + 1) → (∑ p ∈ E, (p : ℝ)⁻¹) ≤ 2 / s := by
  filter_upwards [P.ordinary_interval_upper] with s hs E hE
  calc
    _ ≤ ∑ p ∈ primeLogCellSet 1 0 s (s + 1), (p : ℝ)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg hE (fun p _ _ => by positivity)
    _ ≤ 2 / s := by rw [sum_primeLogCellSet_reciprocal]; exact hs

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeLogGrid
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete equal-mesh log cells and unit residues -/

namespace Ostmann

open scoped Classical

theorem mem_primeLogCellSet_iff {q a p : ℕ} {s t : ℝ} :
    p ∈ primeLogCellSet q a s t ↔
      p.Prime ∧ Nat.ModEq q p a ∧ Real.log (p : ℝ) ∈ Set.Ioc s t := by
  constructor
  · intro hp
    obtain ⟨hI, hprime, hres⟩ := Finset.mem_filter.mp hp
    exact ⟨hprime, hres, log_mem_of_mem_exp_interval hI⟩
  · rintro ⟨hprime, hres, hlo, hhi⟩
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ioc.mpr ⟨?_, ?_⟩, hprime, hres⟩
    · exact (Nat.floor_lt (Real.exp_pos s).le).mpr ((Real.lt_log_iff_exp_lt hp0).mp hlo)
    · exact (Nat.le_floor_iff (Real.exp_pos t).le).mpr ((Real.log_le_iff_le_exp hp0).mp hhi)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeLogCellMeans
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual prime log cells and their means -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

theorem primeLogIndex_bounds (p : ℕ) (hp : p.Prime) :
    (primeLogIndex p : ℝ) < Real.log (p : ℝ) ∧
      Real.log (p : ℝ) ≤ (primeLogIndex p : ℝ) + 1 := by
  have hx : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  let n := ⌈Real.log (p : ℝ)⌉₊
  have hn : 0 < n := by
    have h := Nat.le_ceil (Real.log (p : ℝ))
    by_contra! hz
    have he : n = 0 := Nat.eq_zero_of_le_zero hz
    change Real.log (p : ℝ) ≤ (n : ℝ) at h
    rw [he, Nat.cast_zero] at h
    linarith
  have heq : ((n - 1 : ℕ) : ℝ) + 1 = n := by
    exact_mod_cast Nat.sub_add_cancel (show 1 ≤ n by omega)
  have hu := Nat.le_ceil (Real.log (p : ℝ))
  have hl := Nat.ceil_lt_add_one hx.le
  change (n : ℝ) < Real.log (p : ℝ) + 1 at hl
  change Real.log (p : ℝ) ≤ (n : ℝ) at hu
  change ((n - 1 : ℕ) : ℝ) < Real.log (p : ℝ) ∧
    Real.log (p : ℝ) ≤ ((n - 1 : ℕ) : ℝ) + 1
  constructor <;> linarith

theorem primeLogIndex_cell (p : ℕ) (hp : p.Prime) :
    p ∈ primeLogCellSet 1 0 (primeLogIndex p) ((primeLogIndex p : ℝ) + 1) := by
  apply mem_primeLogCellSet_iff.mpr
  exact ⟨hp, by simp [Nat.ModEq, Nat.mod_one], primeLogIndex_bounds p hp⟩

/-- The actual prime fibers obey the uniform cell cap used in good-cell
selection. -/
theorem PublishedProgressionInput.primeLogIndex_mass_bound (P0 : PublishedProgressionInput) :
    ∀ᶠ B : ℝ in atTop, ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime) →
      ∀ h : ℕ, B ≤ h →
      finiteCellMass P primeLogIndex (fun p => (p : ℝ)⁻¹) h ≤ 2 / B := by
  obtain ⟨S, hS⟩ := eventually_atTop.mp P0.prime_log_cell_upper
  filter_upwards [eventually_ge_atTop (max S 1)] with B hB P hP h hh
  have hpos : 0 < B := lt_of_lt_of_le (by norm_num) ((le_max_right S 1).trans hB)
  have hbound := hS (h : ℝ) ((le_max_left S 1).trans (hB.trans hh))
    (P.filter (fun p => primeLogIndex p = h)) (by
      intro p hp
      obtain ⟨hpP, hpH⟩ := Finset.mem_filter.mp hp
      simpa only [hpH] using primeLogIndex_cell p (hP p hpP))
  apply hbound.trans
  exact div_le_div_of_nonneg_left (by norm_num) hpos hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_RichPrimeCellTargets
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Target words in a rich shell of actual primes -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

/-- A shell of positive harmonic mass and positive mean supplies heavy cells
whose ordered indices approximate every sufficiently large target. -/
theorem PublishedProgressionInput.rich_prime_cell_targets
    (P0 : PublishedProgressionInput) (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℝ in atTop, ∀ (P : Finset ℕ) (f : ℕ → ℝ),
      (∀ p ∈ P, p.Prime) →
      (∀ p ∈ P, B ≤ primeLogIndex p ∧ (primeLogIndex p : ℝ) ≤ 3 * B) →
      (∀ p ∈ P, f p ≤ 1) → c ≤ ∑ p ∈ P, (p : ℝ)⁻¹ →
      δ * (∑ p ∈ P, (p : ℝ)⁻¹) ≤ ∑ p ∈ P, (p : ℝ)⁻¹ * f p →
      ∀ T : ℝ, C * B ≤ T → ∃ (n : ℕ) (w : List ℕ),
        w.length = n ∧
        (∀ h ∈ w,
          δ * c / (32 * B) ≤ finiteCellMass P primeLogIndex (fun p => (p : ℝ)⁻¹) h ∧
          δ / 2 ≤ finiteCellMean P primeLogIndex (fun p => (p : ℝ)⁻¹) f h) ∧
        |(w.sum : ℝ) - T| < 64 / (δ * c) ∧
        (n : ℝ) * B ≤ 128 / (δ * c) * T := by
  let ε := δ * c / 64
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨C, hC, htargets⟩ := dense_index_target ε hε
  refine ⟨4 * C, by positivity, ?_⟩
  filter_upwards [P0.primeLogIndex_mass_bound,
    eventually_ge_atTop (max (1 : ℝ) (32 / (δ * c)))] with B hmass hB P f hP hlabel hf htotal hbias T hT
  have hB1 : 1 ≤ B := (le_max_left _ _).trans hB
  have hBpos : 0 < B := by linarith
  have hδc : 0 < δ * c := mul_pos hδ hc
  have hlarge : 32 ≤ δ * c * B := by
    have hh := (le_max_right (1 : ℝ) (32 / (δ * c))).trans hB
    exact (div_le_iff₀ hδc).mp hh |>.trans_eq (by ring)
  let I := P.image primeLogIndex
  let N := ⌊3 * B⌋₊
  let μ : ℕ → ℝ := fun p => (p : ℝ)⁻¹
  let θ := δ * c / (32 * B)
  let w := finiteCellMass P primeLogIndex μ
  let score := finiteCellMean P primeLogIndex μ f
  let G := positiveHeavyCells I w score δ θ
  have hIlabel : ∀ p ∈ P, primeLogIndex p ∈ I := fun p hp => Finset.mem_image.mpr ⟨p, hp, rfl⟩
  have hIbound : ∀ h ∈ I, h ≤ N := by
    intro h hh
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hh
    exact Nat.le_floor (hlabel p hp).2
  have hN : (N : ℝ) ≤ 3 * B := Nat.floor_le (by positivity)
  have hBN : B ≤ (N : ℝ) := by
    have hh := Nat.lt_floor_add_one (3 * B)
    change 3 * B < (N : ℝ) + 1 at hh
    linarith
  have hIcard : (I.card : ℝ) ≤ 4 * B := by
    have hh : I.card ≤ N + 1 := by
      simpa only [Finset.card_range] using Finset.card_le_card
        (show I ⊆ Finset.range (N + 1) from fun h hh => Finset.mem_range.mpr (Nat.lt_succ_of_le (hIbound h hh)))
    have hhr : (I.card : ℝ) ≤ (N : ℝ) + 1 := by exact_mod_cast hh
    linarith
  have hθ : 0 ≤ θ := by dsimp [θ]; positivity
  have hthin : I.card * θ ≤ (δ / 4) * ∑ p ∈ P, μ p := by
    have hh := mul_le_mul_of_nonneg_right hIcard hθ
    have heq : (4 * B) * θ = δ * c / 8 := by dsimp [θ]; field_simp; ring
    rw [heq] at hh
    have htot := mul_le_mul_of_nonneg_left htotal hδ.le
    dsimp [μ]
    linarith
  have hcap : ∀ h ∈ I, w h ≤ 2 / B := by
    intro h hh
    obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp hh
    exact hmass P hP h (heq ▸ (hlabel p hp).1)
  have hgrowth : (δ / 4) * (∑ p ∈ P, μ p) ≤ G.card * (2 / B) :=
    finite_positive_heavy_cells P I primeLogIndex μ f hIlabel
      (fun p _ => by positivity) hf δ θ (2 / B) hδ.le hθ hbias hthin hcap
  have hGcard : δ * c * B / 8 ≤ G.card := by
    have hh := mul_le_mul_of_nonneg_right hgrowth hBpos.le
    have hcW := mul_le_mul_of_nonneg_left htotal (mul_nonneg hδ.le hBpos.le)
    have heq : (G.card * (2 / B)) * B = 2 * G.card := by field_simp
    rw [heq] at hh
    dsimp [μ] at hh
    nlinarith
  have hGdensity : ε * N + 2 ≤ G.card := by
    have hh := mul_le_mul_of_nonneg_left hN hε.le
    dsimp [ε] at hh ⊢
    nlinarith
  have hGbound : ∀ h ∈ G, h ≤ N := fun h hh => hIbound h (Finset.mem_filter.mp hh).1
  have hCT : C * N ≤ T :=
    (mul_le_mul_of_nonneg_left hN hC.le).trans (by nlinarith)
  obtain ⟨n, u, hlen, hmem, herr, hn, _⟩ := htargets G N hGbound hGdensity T hCT
  refine ⟨n, u, hlen, ?_, ?_, ?_⟩
  · intro h hh
    have hh' := (Finset.mem_filter.mp (hmem h hh)).2
    exact ⟨hh'.2, hh'.1⟩
  · have heq : ε⁻¹ = 64 / (δ * c) := by dsimp [ε]; field_simp
    rwa [heq] at herr
  · have hh := (mul_le_mul_of_nonneg_left hBN (Nat.cast_nonneg (α := ℝ) n)).trans hn
    have heq : 2 * T / ε = 128 / (δ * c) * T := by dsimp [ε]; field_simp; ring
    rwa [heq] at hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeCellWordPriors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original harmonic law on each selected prime cell -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

theorem primeCellWordPrior_mass (P : Finset ℕ) (h : ℕ)
    (hmass : finiteCellMass P primeLogIndex (fun p => (p : ℝ)⁻¹) h ≠ 0) :
    (∑ p : P, primeCellWordPrior P h p) = 1 := by
  unfold primeCellWordPrior
  rw [Finset.sum_coe_sort P (fun p => if primeLogIndex p = h then
    (p : ℝ)⁻¹ / finiteCellMass P primeLogIndex (fun p => (p : ℝ)⁻¹) h else 0)]
  rw [← Finset.sum_filter, ← Finset.sum_div]
  exact div_self hmass

theorem primeCellWordPrior_mean (P : Finset ℕ) (h : ℕ) (F : ℕ → ℂ) :
    (∑ p : P, (primeCellWordPrior P h p : ℂ) * F p) =
      complexCellMean P primeLogIndex (fun p => (p : ℝ)⁻¹) F h := by
  unfold primeCellWordPrior
  simp only [apply_ite, Complex.ofReal_div, Complex.ofReal_zero, ite_mul, zero_mul]
  rw [Finset.sum_coe_sort P (fun p => if primeLogIndex p = h then
    (((p : ℝ)⁻¹ : ℝ) : ℂ) / (finiteCellMass P primeLogIndex (fun p => (p : ℝ)⁻¹) h : ℂ) * F p else 0)]
  rw [← Finset.sum_filter]
  unfold complexCellMean
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  ring

/-- The selected cells carry genuine probability laws with the claimed
positive complex means, so they can be used directly in independent words. -/
theorem PublishedProgressionInput.rich_prime_word_priors
    (P0 : PublishedProgressionInput) (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℝ in atTop, ∀ (P : Finset ℕ) (F : ℕ → ℂ),
      (∀ p ∈ P, p.Prime) →
      (∀ p ∈ P, B ≤ primeLogIndex p ∧ (primeLogIndex p : ℝ) ≤ 3 * B) →
      (∀ p ∈ P, ‖F p‖ ≤ 1) → c ≤ ∑ p ∈ P, (p : ℝ)⁻¹ →
      δ * (∑ p ∈ P, (p : ℝ)⁻¹) ≤ ∑ p ∈ P, (p : ℝ)⁻¹ * (F p).re →
      ∀ T : ℝ, C * B ≤ T → ∃ (n : ℕ) (w : List ℕ),
        w.length = n ∧
        (∀ h ∈ w,
          δ * c / (32 * B) ≤ finiteCellMass P primeLogIndex (fun p => (p : ℝ)⁻¹) h ∧
          (∑ p : P, primeCellWordPrior P h p) = 1 ∧
          δ / 2 ≤ (∑ p : P, (primeCellWordPrior P h p : ℂ) * F p).re) ∧
        |(w.sum : ℝ) - T| < 64 / (δ * c) ∧
        (n : ℝ) * B ≤ 128 / (δ * c) * T := by
  obtain ⟨C, hC, htargets⟩ := P0.rich_prime_cell_targets c δ hc hδ
  refine ⟨C, hC, ?_⟩
  filter_upwards [htargets, eventually_gt_atTop (0 : ℝ)] with B htargets hB P F hP hlabel hF hmass hbias T hT
  obtain ⟨n, w, hlen, hcells, herr, hn⟩ := htargets P (fun p => (F p).re) hP hlabel
    (fun p hp => (Complex.re_le_norm _).trans (hF p hp)) hmass hbias T hT
  refine ⟨n, w, hlen, ?_, herr, hn⟩
  intro h hh
  have hcell := hcells h hh
  have hpos : 0 < finiteCellMass P primeLogIndex (fun p => (p : ℝ)⁻¹) h :=
    lt_of_lt_of_le (by positivity) hcell.1
  refine ⟨hcell.1, primeCellWordPrior_mass P h hpos.ne', ?_⟩
  rw [primeCellWordPrior_mean, complexCellMean_re]
  exact hcell.2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HarmonicWordPriors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Harmonic laws for all word roles on one common prime sample space -/

namespace Ostmann

open scoped BigOperators Classical

theorem primeSubsetPrior_support (P Q : Finset ℕ) (p : P)
    (hp : primeSubsetPrior P Q p ≠ 0) : (p : ℕ) ∈ Q := by
  by_contra hn
  simp [primeSubsetPrior, hn] at hp

theorem primeSubsetPrior_mass (P Q : Finset ℕ) (hQP : Q ⊆ P)
    (hm : (∑ q ∈ Q, (q : ℝ)⁻¹) ≠ 0) : (∑ p : P, primeSubsetPrior P Q p) = 1 := by
  unfold primeSubsetPrior
  rw [Finset.sum_coe_sort P (fun p => if p ∈ Q then
    (p : ℝ)⁻¹ / (∑ q ∈ Q, (q : ℝ)⁻¹) else 0), ← Finset.sum_filter]
  have hf : P.filter (fun p => p ∈ Q) = Q := by
    ext p
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hQP h, h⟩⟩
  rw [hf, ← Finset.sum_div]
  exact div_self hm

theorem primeSubsetPrior_mean (P Q : Finset ℕ) (hQP : Q ⊆ P) (F : ℕ → ℂ) :
    (∑ p : P, (primeSubsetPrior P Q p : ℂ) * F p) =
      (Complex.ofReal (∑ q ∈ Q, (q : ℝ)⁻¹))⁻¹ * ∑ q ∈ Q, ((q : ℝ)⁻¹ : ℂ) * F q := by
  unfold primeSubsetPrior
  simp only [apply_ite, Complex.ofReal_div, Complex.ofReal_zero, ite_mul, zero_mul]
  rw [Finset.sum_coe_sort P (fun p => if p ∈ Q then
    (((p : ℝ)⁻¹ : ℝ) : ℂ) / (∑ q ∈ Q, (q : ℝ)⁻¹ : ℝ) * F p else 0), ← Finset.sum_filter]
  have hf : P.filter (fun p => p ∈ Q) = Q := by
    ext p
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hQP h, h⟩⟩
  rw [hf, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  simp only [Complex.ofReal_inv]
  ring

theorem primeSubsetPrior_cell_mean (P S : Finset ℕ) (hSP : S ⊆ P) (h : ℕ) (F : ℕ → ℂ) :
    (∑ p : P, (primeSubsetPrior P (S.filter (fun q => primeLogIndex q = h)) p : ℂ) * F p) =
      ∑ p : S, (primeCellWordPrior S h p : ℂ) * F p := by
  rw [primeSubsetPrior_mean P _ ((Finset.filter_subset _ _).trans hSP), primeCellWordPrior_mean]
  simp only [complexCellMean, finiteCellMass, Complex.ofReal_inv]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeShellIndex
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Whole unit shells fit the integer cell scale

Taking the floor of the lower exponential endpoint retains every prime in
the shell, including its two boundary cells.
-/

namespace Ostmann

open Filter
open scoped BigOperators Classical

theorem prime_shell_log_bounds (u : ℝ) (p : ℕ) (hp : p.Prime)
    (hlo : u < Real.log (Real.log (p : ℝ)))
    (hhi : Real.log (Real.log (p : ℝ)) ≤ u + 1) :
    Real.exp u < Real.log (p : ℝ) ∧
      Real.log (p : ℝ) ≤ Real.exp 1 * Real.exp u := by
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  constructor
  · simpa only [Real.exp_log hlog] using Real.exp_lt_exp.mpr hlo
  · have h := Real.exp_le_exp.mpr hhi
    simpa only [Real.exp_log hlog, Real.exp_add, mul_comm] using h

theorem prime_shell_index_bounds (u : ℝ) (hu : 12 ≤ Real.exp u)
    (p : ℕ) (hp : p.Prime)
    (hlo : u < Real.log (Real.log (p : ℝ)))
    (hhi : Real.log (Real.log (p : ℝ)) ≤ u + 1) :
    (⌊Real.exp u⌋₊ : ℝ) ≤ primeLogIndex p ∧
      (primeLogIndex p : ℝ) ≤ 3 * ⌊Real.exp u⌋₊ := by
  obtain ⟨hl, hh⟩ := prime_shell_log_bounds u p hp hlo hhi
  have hf := Nat.floor_le (Real.exp_pos u).le
  have hceil : ⌊Real.exp u⌋₊ < ⌈Real.log (p : ℝ)⌉₊ :=
    Nat.lt_ceil.mpr (hf.trans_lt hl)
  have hlow : ⌊Real.exp u⌋₊ ≤ primeLogIndex p := by
    unfold primeLogIndex
    omega
  have hfloor : (12 : ℝ) ≤ ⌊Real.exp u⌋₊ := by
    exact_mod_cast (Nat.le_floor hu : 12 ≤ ⌊Real.exp u⌋₊)
  have hnext := Nat.lt_floor_add_one (Real.exp u)
  have he : Real.exp 1 ≤ (11 : ℝ) / 4 := by linarith [Real.exp_one_lt_d9]
  have hupper := mul_le_mul_of_nonneg_right he (Real.exp_pos u).le
  have hind := (primeLogIndex_bounds p hp).1
  constructor
  · exact_mod_cast hlow
  · nlinarith

theorem shell_floor_scale (u : ℝ) (hu : 2 ≤ Real.exp u) :
    Real.exp u / 2 ≤ (⌊Real.exp u⌋₊ : ℝ) ∧
      (⌊Real.exp u⌋₊ : ℝ) ≤ Real.exp u := by
  have hlo : (1 : ℝ) ≤ ⌊Real.exp u⌋₊ := by
    have hone : (1 : ℝ) ≤ Real.exp u := by linarith
    exact_mod_cast (Nat.le_floor (show ((1 : ℕ) : ℝ) ≤ Real.exp u from by simpa only [Nat.cast_one] using hone) :
      1 ≤ ⌊Real.exp u⌋₊)
  have hi := Nat.lt_floor_add_one (Real.exp u)
  exact ⟨by linarith, Nat.floor_le (Real.exp_pos u).le⟩

theorem PublishedProgressionInput.rich_shell_word_priors
    (P0 : PublishedProgressionInput) (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ u : ℝ in atTop, ∀ (P : Finset ℕ) (F : ℕ → ℂ),
      (∀ p ∈ P, p.Prime) →
      (∀ p ∈ P, u < Real.log (Real.log (p : ℝ)) ∧
        Real.log (Real.log (p : ℝ)) ≤ u + 1) →
      (∀ p ∈ P, ‖F p‖ ≤ 1) → c ≤ ∑ p ∈ P, (p : ℝ)⁻¹ →
      δ * (∑ p ∈ P, (p : ℝ)⁻¹) ≤ ∑ p ∈ P, (p : ℝ)⁻¹ * (F p).re →
      ∀ T : ℝ, C * Real.exp u ≤ T → ∃ (n : ℕ) (w : List ℕ),
        w.length = n ∧
        (∀ h ∈ w,
          δ * c / (32 * Real.exp u) ≤ finiteCellMass P primeLogIndex (fun p => (p : ℝ)⁻¹) h ∧
          (∑ p : P, primeCellWordPrior P h p) = 1 ∧
          δ / 2 ≤ (∑ p : P, (primeCellWordPrior P h p : ℂ) * F p).re) ∧
        |(w.sum : ℝ) - T| < 64 / (δ * c) ∧
        (n : ℝ) * Real.exp u ≤ 256 / (δ * c) * T := by
  obtain ⟨C, hC, hwords⟩ := P0.rich_prime_word_priors c δ hc hδ
  obtain ⟨B₀, hB₀⟩ := eventually_atTop.mp hwords
  refine ⟨C, hC, ?_⟩
  have hlarge : ∀ᶠ u : ℝ in atTop, max 12 (B₀ + 1) ≤ Real.exp u :=
    Real.tendsto_exp_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [hlarge] with u hu P F hP hshell hF hmass hbias T hT
  have hu12 : 12 ≤ Real.exp u := (le_max_left _ _).trans hu
  have hscale := shell_floor_scale u (by linarith)
  have hB₀' : B₀ ≤ (⌊Real.exp u⌋₊ : ℝ) := by
    have h := (le_max_right 12 (B₀ + 1)).trans hu
    have h' := Nat.lt_floor_add_one (Real.exp u)
    linarith
  have hCT : C * (⌊Real.exp u⌋₊ : ℝ) ≤ T :=
    (mul_le_mul_of_nonneg_left hscale.2 hC.le).trans hT
  obtain ⟨n, w, hw, hcells, herr, hn⟩ := hB₀ _ hB₀' P F hP
    (fun p hp => prime_shell_index_bounds u hu12 p (hP p hp) (hshell p hp).1 (hshell p hp).2)
    hF hmass hbias T hCT
  refine ⟨n, w, hw, ?_, herr, ?_⟩
  · intro h hh
    obtain ⟨hm, hprob, hb⟩ := hcells h hh
    refine ⟨?_, hprob, hb⟩
    apply le_trans _ hm
    exact div_le_div_of_nonneg_left (mul_nonneg hδ.le hc.le)
      (by nlinarith [Real.exp_pos u]) (by nlinarith [hscale.2])
  · have h := mul_le_mul_of_nonneg_left hscale.1 (Nat.cast_nonneg n)
    calc
      (n : ℝ) * Real.exp u = 2 * ((n : ℝ) * (Real.exp u / 2)) := by ring
      _ ≤ 2 * ((n : ℝ) * (⌊Real.exp u⌋₊ : ℝ)) := mul_le_mul_of_nonneg_left h (by norm_num)
      _ ≤ 2 * (128 / (δ * c) * T) := mul_le_mul_of_nonneg_left hn (by norm_num)
      _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_PrimeWordCellGeometry
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact real cells for the selected harmonic word laws -/

namespace Ostmann
open scoped Classical

theorem primeLogIndex_eq_iff (p h : ℕ) (hp : p.Prime) :
    primeLogIndex p = h ↔ (h : ℝ) < Real.log (p : ℝ) ∧
      Real.log (p : ℝ) ≤ (h : ℝ) + 1 := by
  constructor
  · intro heq
    simpa only [heq] using primeLogIndex_bounds p hp
  · intro hh
    have hi := primeLogIndex_bounds p hp
    by_contra heq
    rcases lt_or_gt_of_ne heq with hlt | hgt
    · have hb : (primeLogIndex p : ℝ) + 1 ≤ h := by
        exact_mod_cast Nat.succ_le_of_lt hlt
      linarith
    · have hb : (h : ℝ) + 1 ≤ primeLogIndex p := by
        exact_mod_cast Nat.succ_le_of_lt hgt
      linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_BackwardTargets
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The backwards pivot-target recurrence

For coefficients `c_j = 2^j J + a_j - Delta_j`, the pivot target is `c_j`
plus the sum of all later pivot targets. This constructs the recurrence,
rather than assuming that its simultaneous equations have a solution.
-/

namespace Ostmann

theorem backwardTargets_sum_cons (c : ℝ) (cs : List ℝ) :
    (backwardTargets (c :: cs)).sum = c + 2 * (backwardTargets cs).sum := by
  simp only [backwardTargets, List.sum_cons]
  ring

theorem backwardTargets_nonneg (cs : List ℝ) (hcs : ∀ c ∈ cs, 0 ≤ c) :
    ∀ t ∈ backwardTargets cs, 0 ≤ t := by
  induction cs with
  | nil => simp [backwardTargets]
  | cons c cs ih =>
    have hc : 0 ≤ c := hcs c (by simp)
    have htail : ∀ x ∈ cs, 0 ≤ x := fun x hx => hcs x (by simp [hx])
    intro t ht
    simp only [backwardTargets, List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact add_nonneg hc (List.sum_nonneg (ih htail))
    · exact ih htail t ht

theorem backwardTargets_sum_upper (cs : List ℝ) (C : ℝ)
    (hcs : ∀ c ∈ cs, c ≤ C) :
    (backwardTargets cs).sum ≤ C * ((2 : ℝ) ^ cs.length - 1) := by
  induction cs with
  | nil => simp [backwardTargets]
  | cons c cs ih =>
    have hc := hcs c (by simp)
    have ht := ih (fun x hx => hcs x (by simp [hx]))
    rw [backwardTargets_sum_cons, List.length_cons, pow_succ]
    linarith

/-- Every target is at least the final coefficient when the coefficients
are nonnegative. Thus the last pivot controls the common lower scale. -/
theorem backwardTargets_lower_last (cs : List ℝ) (hne : cs ≠ [])
    (hcs : ∀ c ∈ cs, 0 ≤ c) :
    ∀ t ∈ backwardTargets cs, cs.getLast hne ≤ t := by
  induction cs with
  | nil => exact False.elim (hne rfl)
  | cons c cs ih =>
    cases cs with
    | nil => simp [backwardTargets]
    | cons d ds =>
      have htail : ∀ x ∈ d :: ds, 0 ≤ x := fun x hx => hcs x (by simp [hx])
      have hlast := ih (by simp) htail
      have hnonneg := backwardTargets_nonneg (d :: ds) htail
      have hhead : d + (backwardTargets ds).sum ∈ backwardTargets (d :: ds) := by
        simp [backwardTargets]
      have hsum := List.single_le_sum hnonneg _ hhead
      have hlow := hlast _ hhead
      intro t ht
      change t ∈ (c + (backwardTargets (d :: ds)).sum) :: backwardTargets (d :: ds) at ht
      rcases List.mem_cons.mp ht with rfl | ht
      · have hc := hcs c (by simp)
        simpa only [List.getLast_cons_cons] using hlow.trans (by linarith :
          d + (backwardTargets ds).sum ≤ c + (backwardTargets (d :: ds)).sum)
      · simpa only [List.getLast_cons_cons] using hlast t ht

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PivotTargetScale
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive pivot targets at the required logarithmic scale -/

namespace Ostmann

theorem pivotCoefficient_bounds (k : ℕ) (J τ : ℝ) (a Δ : Fin k → ℝ)
    (hτ : 0 < τ) (hJlo : τ / 2 ≤ J) (hJhi : J ≤ 4 * τ)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 4 * τ)
    (hΔ : ∀ i, 0 ≤ Δ i ∧ Δ i ≤ (2 : ℝ) ^ i.val * τ / 4) (i : Fin k) :
    (2 : ℝ) ^ i.val * τ / 4 ≤ (2 : ℝ) ^ i.val * J + a i - Δ i ∧
      (2 : ℝ) ^ i.val * J + a i - Δ i ≤ 8 * (2 : ℝ) ^ k * τ := by
  have hpow : (0 : ℝ) < 2 ^ i.val := by positivity
  have hpow1 : (1 : ℝ) ≤ 2 ^ i.val := one_le_pow₀ (by norm_num)
  have hpowk : (2 : ℝ) ^ i.val ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) i.isLt.le
  have hjl := mul_le_mul_of_nonneg_left hJlo hpow.le
  have hjh := mul_le_mul_of_nonneg_left hJhi hpow.le
  have hτpow := mul_le_mul_of_nonneg_right hpow1 hτ.le
  have hτpowk := mul_le_mul_of_nonneg_right hpowk hτ.le
  constructor <;> nlinarith [ha i, hΔ i]

theorem pivotTargets_bounds (k : ℕ) (hk : 0 < k) (J τ : ℝ) (a Δ : Fin k → ℝ)
    (hτ : 0 < τ) (hJlo : τ / 2 ≤ J) (hJhi : J ≤ 4 * τ)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 4 * τ)
    (hΔ : ∀ i, 0 ≤ Δ i ∧ Δ i ≤ (2 : ℝ) ^ i.val * τ / 4) :
    (pivotTargets k J a Δ).length = k ∧
      (pivotTargets k J a Δ).sum ≤ 8 * (4 : ℝ) ^ k * τ ∧
      ∀ T ∈ pivotTargets k J a Δ,
        (2 : ℝ) ^ (k - 1) * τ / 4 ≤ T ∧ T ≤ 8 * (4 : ℝ) ^ k * τ := by
  let cs := pivotCoefficients k J a Δ
  have hcslen : cs.length = k := by simp [cs, pivotCoefficients]
  have hcsne : cs ≠ [] := by intro h; have := congrArg List.length h; simp [hcslen] at this; omega
  have hcs : ∀ c ∈ cs, 0 ≤ c ∧ c ≤ 8 * (2 : ℝ) ^ k * τ := by
    dsimp [cs, pivotCoefficients]
    rw [List.forall_mem_ofFn_iff]
    intro i
    have h := pivotCoefficient_bounds k J τ a Δ hτ hJlo hJhi ha hΔ i
    exact ⟨(by positivity : 0 ≤ (2 : ℝ) ^ i.val * τ / 4).trans h.1, h.2⟩
  have he : (2 : ℝ) ^ k * 2 ^ k = (4 : ℝ) ^ k := by rw [← mul_pow]; norm_num
  have hmaxpos : 0 ≤ 8 * (2 : ℝ) ^ k * τ := by positivity
  have hsum : (backwardTargets cs).sum ≤ 8 * (4 : ℝ) ^ k * τ := by
    have h := backwardTargets_sum_upper cs (8 * (2 : ℝ) ^ k * τ) (fun c hc => (hcs c hc).2)
    rw [hcslen] at h
    have heq : (8 * (2 : ℝ) ^ k * τ) * (2 : ℝ) ^ k = 8 * (4 : ℝ) ^ k * τ := by
      calc
        _ = 8 * ((2 : ℝ) ^ k * 2 ^ k) * τ := by ring
        _ = _ := by rw [he]
    rw [← heq]
    nlinarith
  have hlast : (2 : ℝ) ^ (k - 1) * τ / 4 ≤ cs.getLast hcsne := by
    have heq := List.getLast_ofFn (f := fun i : Fin k => (2 : ℝ) ^ i.val * J + a i - Δ i)
      (show List.ofFn (fun i : Fin k => (2 : ℝ) ^ i.val * J + a i - Δ i) ≠ [] from hcsne)
    have hb := (pivotCoefficient_bounds k J τ a Δ hτ hJlo hJhi ha hΔ
      ⟨k - 1, by omega⟩).1
    exact hb.trans_eq heq.symm
  refine ⟨(backwardTargets_length cs).trans hcslen, hsum, ?_⟩
  intro T hT
  have hT' : T ∈ backwardTargets cs := hT
  refine ⟨hlast.trans (backwardTargets_lower_last cs hcsne (fun c hc => (hcs c hc).1) T hT'), ?_⟩
  exact (List.single_le_sum (backwardTargets_nonneg cs (fun c hc => (hcs c hc).1)) T hT').trans hsum

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterTargetGaps
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The prescribed gaps are small compared with the top-prime scale -/

namespace Ostmann

open Filter

theorem eventual_character_target_gaps (k : ℕ) (B z α : ℝ)
    (hB : 0 ≤ B) (hz : 1 ≤ z) (hα : 0 < α) :
    ∀ᶠ L : ℝ in atTop, ∀ m τ : ℝ, 0 ≤ m → m ≤ z * L → Real.exp (α * L) ≤ τ →
      0 ≤ characterBaseGap B z m ∧ characterBaseGap B z m ≤ τ / 4 ∧
      ∀ i < k, 0 ≤ characterPivotGap B z m i ∧
        characterPivotGap B z m i ≤ (2 : ℝ) ^ i * τ / 4 := by
  let D := B + 20 * Real.log z
  let C := (2 : ℝ) ^ k * D + (4 : ℝ) ^ (k + 1)
  have hlog : 0 ≤ Real.log z := Real.log_nonneg hz
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hDC : D ≤ C := by
    have h2 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have h4 : (0 : ℝ) ≤ 4 ^ (k + 1) := by positivity
    have h := mul_le_mul_of_nonneg_right h2 hD
    dsimp [C]
    linarith
  have hp := (isLittleO_pow_exp_pos_mul_atTop 1 hα).const_mul_left (4 * C * z)
  have hc := (isLittleO_pow_exp_pos_mul_atTop 0 hα).const_mul_left (4 * C)
  have hb := (hp.add hc).bound (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hb, eventually_ge_atTop (0 : ℝ)] with L hlarge hL m τ hm hmL hτ
  have hlarge' : 4 * C * (z * L + 1) ≤ τ := by
    have hbound := (le_abs_self _).trans (by
      simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), pow_one, pow_zero, mul_one, one_mul]
        using hlarge)
    nlinarith only [hbound, hτ]
  have hbase : characterBaseGap B z m ≤ C * (z * L + 1) := by
    change D * m ≤ _
    have h1 := mul_le_mul_of_nonneg_right hDC hm
    have h2 := mul_le_mul_of_nonneg_left hmL hC
    nlinarith
  have hτpos : 0 < τ := (Real.exp_pos _).trans_le hτ
  refine ⟨mul_nonneg hD hm, by linarith, ?_⟩
  intro i hi
  have hi2 : (2 : ℝ) ^ i ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hi.le
  have hi4 : (4 : ℝ) ^ (i + 1) ≤ 4 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hsqrt : Real.sqrt m ≤ m + 1 := by
    have hs := Real.sq_sqrt hm
    have hn := Real.sqrt_nonneg m
    nlinarith [sq_nonneg (Real.sqrt m - 1)]
  have hgap : characterPivotGap B z m i ≤ C * (m + 1) := by
    have h1 := mul_le_mul_of_nonneg_right hi2 (mul_nonneg hD hm)
    have h2 := mul_le_mul hi4 hsqrt (Real.sqrt_nonneg m) (by positivity : (0 : ℝ) ≤ 4 ^ (k + 1))
    change (2 : ℝ) ^ i * (D * m) + (4 : ℝ) ^ (i + 1) * Real.sqrt m ≤
      ((2 : ℝ) ^ k * D + (4 : ℝ) ^ (k + 1)) * (m + 1)
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 2 ^ k by positivity) hD]
  have hgap' : characterPivotGap B z m i ≤ τ / 4 := by
    have h := mul_le_mul_of_nonneg_left hmL hC
    linarith
  have hpow : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
  have hscale := mul_le_mul_of_nonneg_right hpow hτpos.le
  refine ⟨by dsimp [characterPivotGap, characterBaseGap]; positivity, ?_⟩
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FillerTargetScale
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The filler target completing the prescribed total product -/

namespace Ostmann

open scoped BigOperators

theorem fillerTarget_bounds (k : ℕ) (τ Δ₀ J A T : ℝ) (hτ : 0 < τ)
    (hΔ₀ : 0 ≤ Δ₀ ∧ Δ₀ ≤ τ / 4) (hJ : 0 ≤ J ∧ J ≤ 4 * τ)
    (hA : 0 ≤ A ∧ A ≤ 4 * k * τ) (hT : 0 ≤ T ∧ T ≤ 8 * (4 : ℝ) ^ k * τ) :
    (2 : ℝ) ^ k * τ ≤ fillerTarget k τ Δ₀ J A T ∧
      fillerTarget k τ Δ₀ J A T ≤ 501 * (4 : ℝ) ^ k * τ := by
  have hk2 : (k : ℝ) ≤ (2 : ℝ) ^ k := by exact_mod_cast (Nat.lt_two_pow_self (n := k)).le
  have h24 : (2 : ℝ) ^ k ≤ 4 ^ k := pow_le_pow_left₀ (by norm_num) (by norm_num) k
  have hk4 := hk2.trans h24
  have h41 : (1 : ℝ) ≤ 4 ^ k := one_le_pow₀ (by norm_num)
  have hτ4 := mul_le_mul_of_nonneg_right h41 hτ.le
  have hA4 := mul_le_mul_of_nonneg_right hk4 hτ.le
  have h24τ := mul_le_mul_of_nonneg_right h24 hτ.le
  dsimp [fillerTarget]
  constructor <;> nlinarith [hΔ₀.1, hΔ₀.2, hJ.1, hJ.2, hA.1, hA.2, hT.1, hT.2]

theorem constructed_fillerTarget_bounds (k : ℕ) (hk : 0 < k) (J τ Δ₀ : ℝ)
    (a Δ : Fin k → ℝ) (hτ : 0 < τ) (hJlo : τ / 2 ≤ J) (hJhi : J ≤ 4 * τ)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 4 * τ)
    (hΔ : ∀ i, 0 ≤ Δ i ∧ Δ i ≤ (2 : ℝ) ^ i.val * τ / 4)
    (hΔ₀ : 0 ≤ Δ₀ ∧ Δ₀ ≤ τ / 4) :
    let F := fillerTarget k τ Δ₀ J (∑ i, a i) (pivotTargets k J a Δ).sum
    (2 : ℝ) ^ k * τ ≤ F ∧ F ≤ 501 * (4 : ℝ) ^ k * τ := by
  have htargets := pivotTargets_bounds k hk J τ a Δ hτ hJlo hJhi ha hΔ
  have hA : 0 ≤ ∑ i, a i := Finset.sum_nonneg (fun i _ => (ha i).1)
  have hAup : (∑ i, a i) ≤ 4 * k * τ := by
    calc
      _ ≤ ∑ _i : Fin k, 4 * τ := Finset.sum_le_sum (fun i _ => (ha i).2)
      _ = _ := by simp; ring
  have hT : 0 ≤ (pivotTargets k J a Δ).sum := by
    apply List.sum_nonneg
    intro T hT
    exact (by positivity : 0 ≤ (2 : ℝ) ^ (k - 1) * τ / 4).trans (htargets.2.2 T hT).1
  exact fillerTarget_bounds k τ Δ₀ J _ _ hτ hΔ₀ ⟨by linarith, hJhi⟩ ⟨hA, hAup⟩ ⟨hT, htargets.2.1⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TargetShellLocation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Target windows lie inside the selected late block -/

namespace Ostmann

theorem target_window_in_late_block (k : ℕ) (hk : 20000 ≤ k) (U τ T : ℝ)
    (hτ : 0 < τ) (hτlo : U ≤ Real.log τ)
    (hτhi : Real.log τ ≤ U + 2 * (k : ℝ) / 10000)
    (hTlo : (2 : ℝ) ^ (k - 1) * τ / 4 ≤ T)
    (hThi : T ≤ 600 * (4 : ℝ) ^ k * τ) :
    U ≤ Real.log T - 2 * (k : ℝ) / 10000 ∧
      Real.log T - (k : ℝ) / 10000 ≤ U + 5 * k := by
  have hkr : (20000 : ℝ) ≤ k := by exact_mod_cast hk
  have hk1 : ((k - 1 : ℕ) : ℝ) = k - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
  have hlower : 0 < (2 : ℝ) ^ (k - 1) * τ / 4 := by positivity
  have hT : 0 < T := hlower.trans_le hTlo
  have hlo := Real.log_le_log hlower hTlo
  have hhi := Real.log_le_log hT hThi
  rw [Real.log_div (by positivity) (by norm_num),
    Real.log_mul (by positivity) hτ.ne', Real.log_pow, hk1] at hlo
  rw [Real.log_mul (by positivity) hτ.ne',
    Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hhi
  have hlog2lo : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog2hi : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hlog4hi : Real.log 4 ≤ 2 := by rw [Real.log_four_eq]; linarith
  have hlog600 : Real.log 600 ≤ 600 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 600 by norm_num)
    linarith
  have hlowprod := mul_le_mul_of_nonneg_left hlog2lo (show 0 ≤ (k : ℝ) - 1 by linarith)
  have hhighprod := mul_le_mul_of_nonneg_left hlog4hi (Nat.cast_nonneg k)
  constructor <;> nlinarith

theorem target_window_below_cutoff (k : ℕ) (hk : 20000 ≤ k) (τ T : ℝ)
    (hτ : 0 < τ) (hThi : T ≤ 600 * (4 : ℝ) ^ k * τ) :
    T * Real.exp (-(k : ℝ) / 10000) < (1000 * (4 : ℝ) ^ k * τ) / 4 := by
  have hkr : (20000 : ℝ) ≤ k := by exact_mod_cast hk
  have hexp : 3 ≤ Real.exp ((k : ℝ) / 10000) := by
    have := Real.add_one_le_exp ((k : ℝ) / 10000)
    linarith
  have hsmall : Real.exp (-(k : ℝ) / 10000) ≤ 1 / 3 := by
    rw [show -(k : ℝ) / 10000 = -((k : ℝ) / 10000) by ring, Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num) hexp
  have h1 := mul_le_mul_of_nonneg_right hThi (Real.exp_pos (-(k : ℝ) / 10000)).le
  have h2 := mul_le_mul_of_nonneg_left hsmall
    (show 0 ≤ 600 * (4 : ℝ) ^ k * τ by positivity)
  have hpos : 0 < (4 : ℝ) ^ k * τ := by positivity
  nlinarith

theorem target_shell_scale (ε k T u : ℝ) (hT : 0 < T)
    (hlo : Real.log T - 2 * ε * k ≤ u)
    (hhi : u + 1 ≤ Real.log T - ε * k) :
    Real.exp (ε * k) * Real.exp u ≤ T ∧
      T ≤ Real.exp (2 * ε * k) * Real.exp u := by
  constructor
  · rw [← Real.exp_add, ← Real.exp_log hT]
    exact Real.exp_le_exp.mpr (by linarith)
  · rw [← Real.exp_add, ← Real.exp_log hT]
    exact Real.exp_le_exp.mpr (by linarith)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TargetPrimeWords
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual prime-cell words for every pivot and filler target -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

/-- A target window contains a whole rich tested shell. Its good cell word
has bounded length, positive means, and bounded target error. All constants
are independent of the late block's location. -/
theorem PublishedProgressionInput.target_prime_word
    (P0 : PublishedProgressionInput) (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ U : ℝ in atTop,
      ∀ (k : ℕ), 20000 ≤ k → C ≤ Real.exp ((k : ℝ) / 10000) →
      ∀ (τ : ℝ), 0 < τ → U ≤ Real.log τ →
      Real.log τ ≤ U + 2 * (k : ℝ) / 10000 →
      ∀ (P : Finset ℕ) (F : ℕ → ℂ), (∀ p ∈ P, p.Prime) →
      (∀ p ∈ P, ‖F p‖ ≤ 1) →
      (∀ u v : ℝ, U ≤ u → v ≤ U + 5 * k → (k : ℝ) / 10000 ≤ v - u →
        ∃ j : ℕ, u ≤ U + j ∧ U + j + 1 ≤ v ∧
          c ≤ ∑ p ∈ loglogShell P (U + j), (p : ℝ)⁻¹) →
      (∀ j : ℕ, j ≤ 5 * k → c ≤ ∑ p ∈ loglogShell P (U + j), (p : ℝ)⁻¹ →
        (∀ p ∈ loglogShell P (U + j),
          Real.log (p : ℝ) ≤ (1000 * (4 : ℝ) ^ k * τ) / 4) →
        δ * (∑ p ∈ loglogShell P (U + j), (p : ℝ)⁻¹) ≤
          ∑ p ∈ loglogShell P (U + j), (p : ℝ)⁻¹ * (F p).re) →
      ∀ T : ℝ, (2 : ℝ) ^ (k - 1) * τ / 4 ≤ T → T ≤ 600 * (4 : ℝ) ^ k * τ →
      ∃ (j n : ℕ) (w : List ℕ),
        j ≤ 5 * k ∧ c ≤ ∑ p ∈ loglogShell P (U + j), (p : ℝ)⁻¹ ∧
        Real.log T - 2 * (k : ℝ) / 10000 ≤ U + j ∧
        U + j + 1 ≤ Real.log T - (k : ℝ) / 10000 ∧
        w.length = n ∧
        (∀ h ∈ w,
          δ * c / (32 * Real.exp (U + j)) ≤
            finiteCellMass (loglogShell P (U + j)) primeLogIndex (fun p => (p : ℝ)⁻¹) h ∧
          (∑ p : loglogShell P (U + j), primeCellWordPrior _ h p) = 1 ∧
          δ / 2 ≤ (∑ p : loglogShell P (U + j),
            (primeCellWordPrior _ h p : ℂ) * F p).re) ∧
        |(w.sum : ℝ) - T| < 64 / (δ * c) ∧
        (n : ℝ) ≤ 256 / (δ * c) * Real.exp (2 * (k : ℝ) / 10000) := by
  obtain ⟨C, hC, hwords⟩ := P0.rich_shell_word_priors c δ hc hδ
  obtain ⟨U₀, hU₀⟩ := eventually_atTop.mp hwords
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_ge_atTop U₀] with U hU k hk hCk τ hτ hτlo hτhi P F hP hF hrich htest T hTlo hThi
  have hT : 0 < T := (by positivity : 0 < (2 : ℝ) ^ (k - 1) * τ / 4).trans_le hTlo
  obtain ⟨hwlo, hwhi⟩ := target_window_in_late_block k hk U τ T hτ hτlo hτhi hTlo hThi
  obtain ⟨j, hjlo, hjhi, hjmass⟩ := hrich
    (Real.log T - 2 * (k : ℝ) / 10000) (Real.log T - (k : ℝ) / 10000)
    hwlo hwhi (by linarith)
  have hloc : U₀ ≤ U + j := hU.trans (le_add_of_nonneg_right (Nat.cast_nonneg j))
  have hs := target_shell_scale (1 / 10000) k T (U + j) hT
    (by convert hjlo using 1; ring) (by convert hjhi using 1; ring)
  have hslo : Real.exp ((k : ℝ) / 10000) * Real.exp (U + j) ≤ T := by
    simpa only [show (1 / 10000 : ℝ) * k = (k : ℝ) / 10000 by ring] using hs.1
  have hshi : T ≤ Real.exp (2 * (k : ℝ) / 10000) * Real.exp (U + j) := by
    simpa only [show 2 * (1 / 10000 : ℝ) * k = 2 * (k : ℝ) / 10000 by ring] using hs.2
  have hsmall : ∀ p ∈ loglogShell P (U + j),
      Real.log (p : ℝ) ≤ (1000 * (4 : ℝ) ^ k * τ) / 4 := by
    intro p hp
    obtain ⟨hpP, hpL, hpU⟩ := Finset.mem_filter.mp hp
    have hupper : Real.log (p : ℝ) ≤ T * Real.exp (-(k : ℝ) / 10000) := by
      have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast (hP p hpP).one_lt)
      have he := Real.exp_le_exp.mpr (hpU.trans hjhi)
      rw [Real.exp_log hlogp, Real.exp_sub, Real.exp_log hT] at he
      rw [show -(k : ℝ) / 10000 = -((k : ℝ) / 10000) by ring, Real.exp_neg]
      simpa only [div_eq_mul_inv] using he
    exact hupper.trans (target_window_below_cutoff k hk τ T hτ hThi).le
  have hjbound : j ≤ 5 * k := by
    have hcast : (j : ℝ) ≤ 5 * k := by linarith
    exact_mod_cast hcast
  obtain ⟨n, w, hlen, hcells, herr, hn⟩ := hU₀ (U + j) hloc (loglogShell P (U + j)) F
    (fun p hp => hP p (Finset.mem_filter.mp hp).1)
    (fun p hp => (Finset.mem_filter.mp hp).2)
    (fun p hp => hF p (Finset.mem_filter.mp hp).1) hjmass (htest j hjbound hjmass hsmall) T
    ((mul_le_mul_of_nonneg_right hCk (Real.exp_pos _).le).trans hslo)
  refine ⟨j, n, w, hjbound, hjmass, hjlo, hjhi, hlen, hcells, herr, ?_⟩
  have hcost : 0 ≤ 256 / (δ * c) := by positivity
  have hbound := hn.trans (mul_le_mul_of_nonneg_left hshi hcost)
  exact (mul_le_mul_iff_left₀ (Real.exp_pos (U + j))).mp (by
    simpa only [mul_assoc] using hbound)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterTargetWords
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Simultaneous positive-length words for every character pivot and the filler -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem CharacterTargetWord.length_pos {P : Finset ℕ} {F : ℕ → ℂ} {c δ U T : ℝ} {k : ℕ}
    (w : CharacterTargetWord P F c δ U k T) (hT : 64 / (δ * c) < T) (hT0 : 0 ≤ T) :
    0 < w.indices.length := by
  by_contra! hn
  have he : w.indices = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hn)
  have hh := w.error
  rw [he, List.sum_nil, Nat.cast_zero, zero_sub, abs_neg, abs_of_nonneg hT0] at hh
  exact (not_lt_of_ge hT.le) hh

/-- All nonanchor roles are chosen after fixing the word bin. Their total
length is bounded by the number of actual roles times the single-word bound. -/
theorem PublishedProgressionInput.character_target_words
    (P0 : PublishedProgressionInput) (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ U : ℝ in atTop,
      ∀ (k : ℕ), 20000 ≤ k → C ≤ Real.exp ((k : ℝ) / 10000) →
      ∀ (τ : ℝ), 0 < τ → U ≤ Real.log τ →
      Real.log τ ≤ U + 2 * (k : ℝ) / 10000 →
      ∀ (P : Finset ℕ) (F : ℕ → ℂ), (∀ p ∈ P, p.Prime) →
      (∀ p ∈ P, ‖F p‖ ≤ 1) →
      (∀ u v : ℝ, U ≤ u → v ≤ U + 5 * k → (k : ℝ) / 10000 ≤ v - u →
        ∃ j : ℕ, u ≤ U + j ∧ U + j + 1 ≤ v ∧
          c ≤ ∑ p ∈ loglogShell P (U + j), (p : ℝ)⁻¹) →
      (∀ j : ℕ, j ≤ 5 * k → c ≤ ∑ p ∈ loglogShell P (U + j), (p : ℝ)⁻¹ →
        (∀ p ∈ loglogShell P (U + j),
          Real.log (p : ℝ) ≤ (1000 * (4 : ℝ) ^ k * τ) / 4) →
        δ * (∑ p ∈ loglogShell P (U + j), (p : ℝ)⁻¹) ≤
          ∑ p ∈ loglogShell P (U + j), (p : ℝ)⁻¹ * (F p).re) →
      ∀ T : Option (Fin k) → ℝ,
      (∀ j, (2 : ℝ) ^ (k - 1) * τ / 4 ≤ T j) →
      (∀ j, T j ≤ 600 * (4 : ℝ) ^ k * τ) →
      ∃ w : ∀ j, CharacterTargetWord P F c δ U k (T j),
        (∀ j, 0 < (w j).indices.length) ∧
        (∑ j, ((w j).indices.length : ℝ)) ≤
          (k + 1 : ℕ) * (256 / (δ * c) * Real.exp (2 * (k : ℝ) / 10000)) := by
  obtain ⟨C, hC, hwords⟩ := P0.target_prime_word c δ hc hδ
  refine ⟨C, hC, ?_⟩
  filter_upwards [hwords, Real.tendsto_exp_atTop.eventually
    (eventually_gt_atTop (4 * (64 / (δ * c))))] with U hw hU
  intro k hk hCk τ hτ hτlo hτhi P F hP hF hrich htest T hTlo hThi
  have hchoice : ∀ j, Nonempty (CharacterTargetWord P F c δ U k (T j)) := by
    intro j
    obtain ⟨s, n, w, hs, hr, hlo, hhi, hn, hcells, herr, hlength⟩ :=
      hw k hk hCk τ hτ hτlo hτhi P F hP hF hrich htest (T j) (hTlo j) (hThi j)
    exact ⟨⟨s, w, hs, hr, hlo, hhi, hcells, herr, by simpa only [hn] using hlength⟩⟩
  let w : ∀ j, CharacterTargetWord P F c δ U k (T j) := fun j => Classical.choice (hchoice j)
  refine ⟨w, ?_, ?_⟩
  · intro j
    have hτU : Real.exp U ≤ τ := by
      simpa only [Real.exp_log hτ] using Real.exp_le_exp.mpr hτlo
    have hp : (1 : ℝ) ≤ 2 ^ (k - 1) := one_le_pow₀ (by norm_num)
    have htau := mul_le_mul_of_nonneg_right hp hτ.le
    have ht : 64 / (δ * c) < T j := by nlinarith only [hU, hτU, htau, hTlo j]
    exact (w j).length_pos ht ((by positivity : 0 < 64 / (δ * c)).trans ht).le
  · calc
      _ ≤ ∑ _j : Option (Fin k),
          256 / (δ * c) * Real.exp (2 * (k : ℝ) / 10000) :=
        Finset.sum_le_sum (fun j _ => (w j).length_le)
      _ = _ := by simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TopWordBinScale
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The top prime controls every nonempty bulk-word bin -/

namespace Ostmann

open Filter
open scoped BigOperators

theorem wordLogBin_val {m : ℕ} (τ : ℝ) (ℓ : Fin (m + 1) → ℝ)
    (h : (∑ i, ℓ i) ≤ 4 * τ) :
    (wordLogBin τ ℓ).val = ⌊∑ i, ℓ i⌋₊ := by
  exact Nat.min_eq_left (Nat.floor_mono h)

theorem wordLogBin_count (τ : ℝ) (hτ : 1 ≤ τ) :
    Real.log (Fintype.card (Fin (⌊4 * τ⌋₊ + 1))) ≤ Real.log 5 + Real.log τ := by
  have hτpos : 0 < τ := by linarith
  have hfloor := Nat.floor_le (show 0 ≤ 4 * τ by positivity)
  have hcount : ((⌊4 * τ⌋₊ + 1 : ℕ) : ℝ) ≤ 5 * τ := by
    push_cast
    linarith
  have hc : (0 : ℝ) < (⌊4 * τ⌋₊ + 1 : ℕ) := by positivity
  simpa only [Fintype.card_fin, Real.log_mul (by norm_num : (5 : ℝ) ≠ 0) hτpos.ne']
    using Real.log_le_log hc hcount

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeCellProductIntervals
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer interval endpoints for actual selected prime-cell words -/
namespace Ostmann
open scoped Classical BigOperators

theorem primeCell_interval (p h : ℕ) (hp : p.Prime) (hi : primeLogIndex p = h) :
    primeCellLower h ≤ p ∧ p ≤ primeCellUpper h := by
  have hh := (primeLogIndex_eq_iff p h hp).mp hi
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  constructor
  · apply Nat.ceil_le.mpr
    exact (Real.exp_lt_exp.mpr hh.1).le.trans_eq (Real.exp_log hp0)
  · apply Nat.le_floor
    exact (Real.exp_log hp0).symm.le.trans (Real.exp_le_exp.mpr hh.2)

theorem primeCell_products {n : ℕ} (h : Fin n → ℕ) :
    Real.exp (∑ i, (h i : ℝ)) ≤ (∏ i, primeCellLower (h i) : ℕ) ∧
      (∏ i, primeCellUpper (h i) : ℕ) ≤ Real.exp ((∑ i, (h i : ℝ)) + n) := by
  constructor
  · rw [Nat.cast_prod, Real.exp_sum]
    exact Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le)
      (fun i _ => Nat.le_ceil _)
  · rw [Nat.cast_prod]
    calc
      _ ≤ ∏ i : Fin n, Real.exp ((h i : ℝ) + 1) :=
        Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _)
          (fun i _ => Nat.floor_le (Real.exp_pos _).le)
      _ = _ := by rw [← Real.exp_sum, Finset.sum_add_distrib]; simp

theorem primeCell_target_products {n : ℕ} (h : Fin n → ℕ) (T E c : ℝ)
    (htarget : |(∑ i, (h i : ℝ)) - T| ≤ E) (hc : E + n ≤ c) :
    Real.exp (T - c) ≤ (∏ i, primeCellLower (h i) : ℕ) ∧
      (∏ i, primeCellUpper (h i) : ℕ) ≤ Real.exp (T + c) := by
  obtain ⟨htlo, hthi⟩ := abs_le.mp htarget
  obtain ⟨hl, hu⟩ := primeCell_products h
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  constructor
  · exact (Real.exp_le_exp.mpr (by linarith)).trans hl
  · exact hu.trans (Real.exp_le_exp.mpr (by linarith))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterTargetCellData
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected target words as actual harmonic cells in the common prime space -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem CharacterTargetWord.cell_subset {P : Finset ℕ} {F : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : ℝ} (w : CharacterTargetWord P F c δ U k T) (h : ℕ) :
    w.cell h ⊆ P :=
  (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)

theorem CharacterTargetWord.cell_mass {P : Finset ℕ} {F : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : ℝ} (w : CharacterTargetWord P F c δ U k T)
    (h : ℕ) (hh : h ∈ w.indices) :
    δ * c / (32 * Real.exp (U + w.shell)) ≤ ∑ p ∈ w.cell h, (p : ℝ)⁻¹ :=
  (w.cells h hh).1

theorem CharacterTargetWord.cell_mean {P : Finset ℕ} {F : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : ℝ} (w : CharacterTargetWord P F c δ U k T)
    (h : ℕ) (hh : h ∈ w.indices) :
    δ / 2 ≤ (∑ p : P, (primeSubsetPrior P (w.cell h) p : ℂ) * F p).re := by
  rw [CharacterTargetWord.cell, primeSubsetPrior_cell_mean P (loglogShell P (U + w.shell)) (Finset.filter_subset _ _) h F]
  exact (w.cells h hh).2.2

theorem CharacterTargetWord.cell_mass_exponential {P : Finset ℕ} {F : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : ℝ} (w : CharacterTargetWord P F c δ U k T)
    (hc : 0 < c) (hδ : 0 < δ) (β L : ℝ)
    (hU : U ≤ β * L) (hL : 5 * (k : ℝ) - Real.log (δ * c / 32) ≤ L)
    (h : ℕ) (hh : h ∈ w.indices) :
    Real.exp (-(β + 1) * L) ≤ ∑ p ∈ w.cell h, (p : ℝ)⁻¹ := by
  have hs : (w.shell : ℝ) ≤ 5 * k := by exact_mod_cast w.shell_le
  have he : Real.exp (-(β + 1) * L) ≤ δ * c / (32 * Real.exp (U + w.shell)) := by
    calc
      _ ≤ Real.exp (Real.log (δ * c / 32) - (U + w.shell)) :=
        Real.exp_le_exp.mpr (by nlinarith only [hs, hU, hL])
      _ = _ := by
        rw [Real.exp_sub, Real.exp_log (by positivity)]
        ring
  exact he.trans (w.cell_mass h hh)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_BinnedWordNorm
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Absolute endpoint means suffice for selecting the original character bin -/
namespace Ostmann
open scoped Classical BigOperators

theorem binnedWordAverage_total_norm_lower {A B : Type*} [Fintype A] [Fintype B] {n : ℕ}
    (μ : Fin n → A → ℝ) (F : Fin n → A → ℂ) (bin : (Fin n → A) → B)
    (δ : ℝ) (hδ : 0 ≤ δ) (hmean : ∀ i, δ ≤ ‖∑ a, (μ i a : ℂ) * F i a‖) :
    δ ^ n ≤ ‖∑ b, binnedWordAverage μ F bin b‖ := by
  rw [binnedWordAverage_sum, norm_prod]
  calc
    δ ^ n = ∏ _i : Fin n, δ := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => hδ) (fun i _ => hmean i)

/-- This pigeonhole fixes the bin before the endpoint-dependent cell lists. -/
theorem common_large_word_bin_of_norm {A B : Type*} [Fintype A] [Fintype B] [Nonempty B]
    {n : ℕ} (E : Finset ℕ) (μ : Fin n → A → ℝ) (F : ℕ → Fin n → A → ℂ)
    (bin : (Fin n → A) → B) (δ : ℝ) (hδ : 0 ≤ δ)
    (hmean : ∀ a ∈ E, ∀ i, δ ≤ ‖∑ p, (μ i p : ℂ) * F a i p‖) :
    ∃ b, ∃ S : Finset ℕ, S ⊆ E ∧ E.card ≤ Fintype.card B * S.card ∧
      ∀ a ∈ S, δ ^ n ≤ (Fintype.card B : ℝ) * ‖binnedWordAverage μ (F a) bin b‖ := by
  exact common_large_bin E (fun a => binnedWordAverage μ (F a) bin) (δ ^ n)
    (fun a ha => binnedWordAverage_total_norm_lower μ (F a) bin δ hδ (hmean a ha))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterMeanRotation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One common rotation and the original, unrotated character priors -/
namespace Ostmann
open scoped Classical BigOperators

theorem norm_weighted_common_rotation {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (F : ι → ℂ) (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    ‖∑ i, (w i : ℂ) * (ζ * F i)‖ = ‖∑ i, (w i : ℂ) * F i‖ := by
  have he : (∑ i, (w i : ℂ) * (ζ * F i)) = ζ * ∑ i, (w i : ℂ) * F i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, norm_mul, hζ, one_mul]

/-- The positive rotated cell mean supplies the norm bound used by the
unrotated initial character statistic, without modifying the harmonic law. -/
theorem CharacterTargetWord.cell_unrotated_mean {P : Finset ℕ} {G : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : ℝ} (ζ : ℂ) (hζ : ‖ζ‖ = 1)
    (w : CharacterTargetWord P (fun p => ζ * G p) c δ U k T)
    (h : ℕ) (hh : h ∈ w.indices) :
    δ / 2 ≤ ‖∑ p : P, (primeSubsetPrior P (w.cell h) p : ℂ) * G p‖ := by
  have hm := (w.cell_mean h hh).trans (Complex.re_le_norm _)
  rwa [norm_weighted_common_rotation _ _ ζ hζ] at hm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_RichAnchorCell
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A rich shell supplies an actual heavy anchor cell -/

namespace Ostmann

open Filter
open scoped BigOperators

theorem PublishedProgressionInput.rich_anchor_cell
    (P0 : PublishedProgressionInput) (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) :
    ∀ᶠ u : ℝ in atTop, ∀ (P : Finset ℕ) (F : ℕ → ℂ),
      (∀ p ∈ P, p.Prime) →
      (∀ p ∈ P, u < Real.log (Real.log (p : ℝ)) ∧
        Real.log (Real.log (p : ℝ)) ≤ u + 1) →
      (∀ p ∈ P, ‖F p‖ ≤ 1) → c ≤ ∑ p ∈ P, (p : ℝ)⁻¹ →
      δ * (∑ p ∈ P, (p : ℝ)⁻¹) ≤ ∑ p ∈ P, (p : ℝ)⁻¹ * (F p).re →
      ∃ h : ℕ, Real.exp u / 2 ≤ h ∧ (h : ℝ) ≤ 3 * Real.exp u ∧
        δ * c / (32 * Real.exp u) ≤ finiteCellMass P primeLogIndex (fun p => (p : ℝ)⁻¹) h ∧
        (∑ p : P, primeCellWordPrior P h p) = 1 ∧
        δ / 2 ≤ (∑ p : P, (primeCellWordPrior P h p : ℂ) * F p).re := by
  obtain ⟨C, hC, hwords⟩ := P0.rich_shell_word_priors c δ hc hδ
  have hlarge : ∀ᶠ u : ℝ in atTop, 12 ≤ Real.exp u :=
    Real.tendsto_exp_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [hwords, hlarge] with u hu hu12 P F hP hshell hF hmass hbias
  let T := C * Real.exp u + 128 / (δ * c) + 1
  have hδc : 0 < δ * c := mul_pos hδ hc
  have hfrac : 0 < 64 / (δ * c) := by positivity
  have hdouble : 128 / (δ * c) = 2 * (64 / (δ * c)) := by ring
  have hT : C * Real.exp u ≤ T := by dsimp [T]; rw [hdouble]; linarith
  have hTlarge : 64 / (δ * c) < T := by
    have hCexp : 0 < C * Real.exp u := mul_pos hC (Real.exp_pos _)
    dsimp [T]
    rw [hdouble]
    linarith
  have hTpos : 0 < T := hfrac.trans hTlarge
  obtain ⟨n, w, _, hcells, herr, _⟩ := hu P F hP hshell hF hmass hbias T hT
  have hw : w ≠ [] := by
    intro he
    rw [he, List.sum_nil, Nat.cast_zero, zero_sub, abs_neg,
      abs_of_pos hTpos] at herr
    linarith
  obtain ⟨h, hh⟩ := List.exists_mem_of_ne_nil w hw
  obtain ⟨hm, hprob, hmean⟩ := hcells h hh
  have hmpos : 0 < finiteCellMass P primeLogIndex (fun p => (p : ℝ)⁻¹) h :=
    (by positivity : 0 < δ * c / (32 * Real.exp u)).trans_le hm
  have hfiber : (P.filter (fun p => primeLogIndex p = h)).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    simp [finiteCellMass, he] at hmpos
  obtain ⟨p, hp⟩ := hfiber
  obtain ⟨hpP, hph⟩ := Finset.mem_filter.mp hp
  have hind := prime_shell_index_bounds u hu12 p (hP p hpP) (hshell p hpP).1 (hshell p hpP).2
  rw [hph] at hind
  have hscale := shell_floor_scale u (by linarith)
  exact ⟨h, hscale.1.trans hind.1, hind.2.trans (by nlinarith [hscale.2]), hm, hprob, hmean⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterAnchorCells
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual small and large anchor cells with their original harmonic laws -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem CharacterAnchorCell.cell_subset {P : Finset ℕ} {F : ℕ → ℂ} {c δ u : ℝ}
    (a : CharacterAnchorCell P F c δ u) : a.cell ⊆ P :=
  (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)

theorem CharacterAnchorCell.cell_eq_of_index {P : Finset ℕ} {F G : ℕ → ℂ} {c δ u : ℝ}
    (a : CharacterAnchorCell P F c δ u) (b : CharacterAnchorCell P G c δ u)
    (h : a.index = b.index) : a.cell = b.cell := by
  simp only [CharacterAnchorCell.cell, h]

theorem CharacterAnchorCell.cell_mass_pos {P : Finset ℕ} {F : ℕ → ℂ} {c δ u : ℝ}
    (a : CharacterAnchorCell P F c δ u) (hc : 0 < c) (hδ : 0 < δ) :
    0 < ∑ p ∈ a.cell, (p : ℝ)⁻¹ :=
  (by positivity : 0 < δ * c / (32 * Real.exp u)).trans_le a.mass

theorem CharacterAnchorCell.index_le {P : Finset ℕ} {F : ℕ → ℂ} {c δ u : ℝ}
    (a : CharacterAnchorCell P F c δ u) (hc : 0 < c) (hδ : 0 < δ)
    (B : ℕ) (hP : ∀ p ∈ P, primeLogIndex p ≤ B) : a.index ≤ B := by
  have hn : a.cell.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    have hm := a.cell_mass_pos hc hδ
    rw [he, Finset.sum_empty] at hm
    exact (lt_irrefl 0) hm
  obtain ⟨p, hp⟩ := hn
  have hi : primeLogIndex p = a.index := (Finset.mem_filter.mp hp).2
  rw [← hi]
  exact hP p (a.cell_subset hp)

theorem CharacterAnchorCell.unrotated_mean {P : Finset ℕ} {G : ℕ → ℂ} {c δ u : ℝ}
    (ζ : ℂ) (hζ : ‖ζ‖ = 1) (a : CharacterAnchorCell P (fun p => ζ * G p) c δ u) :
    δ / 2 ≤ ‖∑ p : P, (primeSubsetPrior P a.cell p : ℂ) * G p‖ := by
  have h := a.mean.trans (Complex.re_le_norm _)
  rwa [norm_weighted_common_rotation _ _ ζ hζ] at h

theorem CharacterAnchorCell.cell_mass_exponential {P : Finset ℕ} {F : ℕ → ℂ} {c δ u : ℝ}
    (a : CharacterAnchorCell P F c δ u) (hc : 0 < c) (hδ : 0 < δ)
    (β L : ℝ) (hu : u ≤ β * L) (hL : -Real.log (δ * c / 32) ≤ L) :
    Real.exp (-(β + 1) * L) ≤ ∑ p ∈ a.cell, (p : ℝ)⁻¹ := by
  apply le_trans _ a.mass
  calc
    _ ≤ Real.exp (Real.log (δ * c / 32) - u) :=
      Real.exp_le_exp.mpr (by nlinarith only [hu, hL])
    _ = _ := by rw [Real.exp_sub, Real.exp_log (by positivity)]; ring

/-- Anchor selection uses the same whole-shell progression theorem as the
pivot words, without clipping either boundary cell. -/
theorem PublishedProgressionInput.character_anchor_cell
    (P0 : PublishedProgressionInput) (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) :
    ∀ᶠ u : ℝ in atTop, ∀ (P : Finset ℕ) (F : ℕ → ℂ),
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, ‖F p‖ ≤ 1) →
      c ≤ ∑ p ∈ loglogShell P u, (p : ℝ)⁻¹ →
      δ * (∑ p ∈ loglogShell P u, (p : ℝ)⁻¹) ≤
        ∑ p ∈ loglogShell P u, (p : ℝ)⁻¹ * (F p).re →
      Nonempty (CharacterAnchorCell P F c δ u) := by
  filter_upwards [P0.rich_anchor_cell c δ hc hδ] with u hu P F hP hF hm hmean
  obtain ⟨h, hlo, hhi, hmass, _, hbias⟩ := hu (loglogShell P u) F
    (fun p hp => hP p (Finset.mem_filter.mp hp).1)
    (fun _ hp => (Finset.mem_filter.mp hp).2)
    (fun p hp => hF p (Finset.mem_filter.mp hp).1) hm hmean
  refine ⟨⟨h, hlo, hhi, hmass, ?_⟩⟩
  rw [primeSubsetPrior_cell_mean P (loglogShell P u) (Finset.filter_subset _ _) h F]
  exact hbias

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_CellListPigeonhole
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixing the ordered cell lists across endpoints -/

namespace Ostmann

open scoped BigOperators Classical

theorem mem_boundedCellLists (N B : ℕ) (w : List ℕ)
    (hlen : w.length ≤ N) (hw : ∀ a ∈ w, a ≤ B) : w ∈ boundedCellLists N B := by
  apply Finset.mem_biUnion.mpr
  refine ⟨w.length, Finset.mem_range.mpr (by omega), ?_⟩
  let f : Fin w.length → Fin (B + 1) := fun i =>
    ⟨w.get i, Nat.lt_succ_of_le (hw _ (List.get_mem _ _))⟩
  exact Finset.mem_image.mpr ⟨f, Finset.mem_univ _, List.ofFn_get w⟩

theorem boundedCellLists_nonempty (N B : ℕ) : (boundedCellLists N B).Nonempty :=
  ⟨[], mem_boundedCellLists N B [] (by simp) (by simp)⟩

theorem boundedCellLists_card_le (N B : ℕ) :
    (boundedCellLists N B).card ≤ (N + 1) * (B + 1) ^ N := by
  calc
    (boundedCellLists N B).card ≤ ∑ n ∈ Finset.range (N + 1),
        ((Finset.univ : Finset (Fin n → Fin (B + 1))).image
          (fun f => List.ofFn (fun i => (f i : ℕ)))).card := Finset.card_biUnion_le
    _ ≤ ∑ n ∈ Finset.range (N + 1), (B + 1) ^ n := by
      apply Finset.sum_le_sum
      intro n _
      simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin n → Fin (B + 1))))
        (f := fun f => List.ofFn (fun i => (f i : ℕ))))
    _ ≤ ∑ _n ∈ Finset.range (N + 1), (B + 1) ^ N := by
      apply Finset.sum_le_sum
      intro n hn
      have : n ≤ N := by have := Finset.mem_range.mp hn; omega
      gcongr
      omega
    _ = _ := by simp

/-- Simultaneously fixing all list lengths and ordered cell labels costs
at most the explicit finite number of bounded lists. -/
theorem common_cell_list (E : Finset ℕ) (N B : ℕ) (w : ℕ → List ℕ)
    (hlen : ∀ a ∈ E, (w a).length ≤ N)
    (hentry : ∀ a ∈ E, ∀ h ∈ w a, h ≤ B) :
    ∃ v : List ℕ, ∃ S : Finset ℕ, S ⊆ E ∧
      E.card ≤ ((N + 1) * (B + 1) ^ N) * S.card ∧ ∀ a ∈ S, w a = v := by
  let V := boundedCellLists N B
  have hmap : ∀ a ∈ E, w a ∈ V := fun a ha => mem_boundedCellLists N B (w a) (hlen a ha) (hentry a ha)
  obtain ⟨v, _, hv⟩ := Finset.exists_max_image V
    (fun v => (E.filter (fun a => w a = v)).card) (boundedCellLists_nonempty N B)
  refine ⟨v, E.filter (fun a => w a = v), Finset.filter_subset _ _, ?_, ?_⟩
  · calc
      E.card = ∑ v ∈ V, (E.filter (fun a => w a = v)).card :=
        Finset.card_eq_sum_card_fiberwise hmap
      _ ≤ ∑ _v ∈ V, (E.filter (fun a => w a = v)).card :=
        Finset.sum_le_sum (fun u hu => hv u hu)
      _ = V.card * (E.filter (fun a => w a = v)).card := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ (boundedCellLists_card_le N B)
  · intro a ha
    exact (Finset.mem_filter.mp ha).2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_CellGroupPigeonhole
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixing every cell group at the cost of the total number of labels -/

namespace Ostmann

theorem decode_encodeCellGroups (ws : List (List ℕ)) :
    decodeCellGroups ws.length (encodeCellGroups ws) = ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [encodeCellGroups, decodeCellGroups, ih]

theorem encodeCellGroups_injective_of_length {ws vs : List (List ℕ)}
    (hlen : ws.length = vs.length) (he : encodeCellGroups ws = encodeCellGroups vs) : ws = vs := by
  calc
    ws = decodeCellGroups ws.length (encodeCellGroups ws) := (decode_encodeCellGroups ws).symm
    _ = decodeCellGroups vs.length (encodeCellGroups vs) := by rw [hlen, he]
    _ = vs := decode_encodeCellGroups vs

theorem encodeCellGroups_length (ws : List (List ℕ)) :
    (encodeCellGroups ws).length = (ws.map List.length).sum + ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp only [encodeCellGroups, List.length_cons, List.length_append,
      List.map_cons, List.sum_cons, ih]; omega

theorem encodeCellGroups_entries (ws : List (List ℕ)) (N B : ℕ)
    (hl : ∀ w ∈ ws, w.length ≤ N) (he : ∀ w ∈ ws, ∀ h ∈ w, h ≤ B) :
    ∀ h ∈ encodeCellGroups ws, h ≤ max N B := by
  induction ws with
  | nil => simp [encodeCellGroups]
  | cons w ws ih =>
    intro h hh
    simp only [encodeCellGroups, List.mem_cons, List.mem_append] at hh
    rcases hh with rfl | hw | hws
    · exact (hl w (by simp)).trans (le_max_left _ _)
    · exact (he w (by simp) h hw).trans (le_max_right _ _)
    · exact ih (fun v hv => hl v (by simp [hv]))
        (fun v hv => he v (by simp [hv])) h hws

/-- Length-prefix coding retains the group boundaries while using only one
extra entry per group. Thus the pigeonhole cost depends on the total label
count, rather than the product of the separate group-length bounds. -/
theorem common_cell_groups (E : Finset ℕ) (hE : E.Nonempty) (r N B : ℕ)
    (ws : ℕ → List (List ℕ))
    (hr : ∀ a ∈ E, (ws a).length = r)
    (hlen : ∀ a ∈ E, ((ws a).map List.length).sum ≤ N)
    (hentry : ∀ a ∈ E, ∀ w ∈ ws a, ∀ h ∈ w, h ≤ B) :
    ∃ v : List (List ℕ), ∃ S : Finset ℕ, S ⊆ E ∧ S.Nonempty ∧
      E.card ≤ ((N + r + 1) * (max N B + 1) ^ (N + r)) * S.card ∧
      ∀ a ∈ S, ws a = v := by
  have hlength (a : ℕ) (ha : a ∈ E) : (encodeCellGroups (ws a)).length ≤ N + r := by
    rw [encodeCellGroups_length, hr a ha]
    exact Nat.add_le_add_right (hlen a ha) r
  have hbound (a : ℕ) (ha : a ∈ E) :
      ∀ h ∈ encodeCellGroups (ws a), h ≤ max N B := by
    apply encodeCellGroups_entries
    · intro w hw
      apply le_trans _ (hlen a ha)
      exact List.single_le_sum (fun _ _ => Nat.zero_le _) w.length (List.mem_map.mpr ⟨w, hw, rfl⟩)
    · exact hentry a ha
  obtain ⟨code, S, hSE, hcard, hsame⟩ := common_cell_list E (N + r) (max N B)
    (fun a => encodeCellGroups (ws a)) hlength hbound
  have hS : S.Nonempty := by
    by_contra hn
    have hz : S.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hn)
    rw [hz, Nat.mul_zero] at hcard
    exact (Nat.not_le_of_gt hE.card_pos) hcard
  obtain ⟨a₀, ha₀⟩ := hS
  refine ⟨ws a₀, S, hSE, ⟨a₀, ha₀⟩, hcard, ?_⟩
  intro a ha
  exact encodeCellGroups_injective_of_length ((hr a (hSE ha)).trans (hr a₀ (hSE ha₀)).symm)
    ((hsame a ha).trans (hsame a₀ ha₀).symm)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterTargetCode
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixing the actual target shells and their ordered cell lists -/
namespace Ostmann
open scoped Classical BigOperators

theorem CharacterTargetWord.index_le {P : Finset ℕ} {F : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : ℝ} (w : CharacterTargetWord P F c δ U k T)
    (hc : 0 < c) (hδ : 0 < δ) (B : ℕ) (hP : ∀ p ∈ P, primeLogIndex p ≤ B)
    (h : ℕ) (hh : h ∈ w.indices) : h ≤ B := by
  have hm : 0 < ∑ p ∈ w.cell h, (p : ℝ)⁻¹ :=
    (by positivity : 0 < δ * c / (32 * Real.exp (U + w.shell))).trans_le (w.cell_mass h hh)
  have hs : (w.cell h).Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [he, Finset.sum_empty, lt_self_iff_false] at hm
  obtain ⟨p, hp⟩ := hs
  have hi := (Finset.mem_filter.mp hp).2
  simpa only [hi] using hP p (w.cell_subset h hp)

theorem characterTargetCodeGroups_length {P : Finset ℕ} {F : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : Option (Fin k) → ℝ}
    (w : ∀ j, CharacterTargetWord P F c δ U k (T j)) :
    (characterTargetCodeGroups w).length = k + 1 := by
  simp [characterTargetCodeGroups]

theorem characterTargetCodeGroups_size {P : Finset ℕ} {F : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : Option (Fin k) → ℝ}
    (w : ∀ j, CharacterTargetWord P F c δ U k (T j)) :
    ((characterTargetCodeGroups w).map List.length).sum =
      (∑ j : Option (Fin k), (w j).indices.length) + (k + 1) := by
  simp only [characterTargetCodeGroups, List.map_ofFn, List.sum_ofFn,
    CharacterTargetWord.code, Function.comp_def, List.length_cons]
  rw [Finset.sum_add_distrib]
  have he := Equiv.sum_comp (finSuccEquiv k) (fun j => (w j).indices.length)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] using
    congrArg (fun n : ℕ => n + (k + 1)) he

theorem characterTargetCodeGroups_data {P : Finset ℕ} {F G : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T S : Option (Fin k) → ℝ}
    (w : ∀ j, CharacterTargetWord P F c δ U k (T j))
    (v : ∀ j, CharacterTargetWord P G c δ U k (S j))
    (he : characterTargetCodeGroups w = characterTargetCodeGroups v) :
    ∀ j, (w j).shell = (v j).shell ∧ (w j).indices = (v j).indices := by
  change List.ofFn (fun i : Fin (k + 1) => (w (finSuccEquiv k i)).code) =
    List.ofFn (fun i : Fin (k + 1) => (v (finSuccEquiv k i)).code) at he
  have he' := List.ofFn_injective he
  intro j
  have hc := congrFun he' ((finSuccEquiv k).symm j)
  have hj := (finSuccEquiv k).apply_symm_apply j
  rw [hj] at hc
  exact List.cons.inj hc

theorem characterTargetCodeGroups_cells {P : Finset ℕ} {F G : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T S : Option (Fin k) → ℝ}
    (w : ∀ j, CharacterTargetWord P F c δ U k (T j))
    (v : ∀ j, CharacterTargetWord P G c δ U k (S j))
    (he : characterTargetCodeGroups w = characterTargetCodeGroups v) :
    ∀ j h, (w j).cell h = (v j).cell h := by
  intro j h
  have hs := (characterTargetCodeGroups_data w v he j).1
  simp only [CharacterTargetWord.cell, hs]

/-- Shell identifiers are part of the code, so fixing it fixes the actual
prime sets even when targets and Fourier tests vary with the endpoint. -/
theorem common_character_target_cells (E : Finset ℕ) (hE : E.Nonempty)
    (P : Finset ℕ) (F : ℕ → ℕ → ℂ) (c δ U : ℝ) (k N B : ℕ)
    (T : ℕ → Option (Fin k) → ℝ)
    (w : ∀ a j, CharacterTargetWord P (F a) c δ U k (T a j))
    (hc : 0 < c) (hδ : 0 < δ) (hk : 5 * k ≤ B)
    (hP : ∀ p ∈ P, primeLogIndex p ≤ B)
    (hN : ∀ a ∈ E, (∑ j : Option (Fin k), (w a j).indices.length) ≤ N) :
    ∃ S : Finset ℕ, S ⊆ E ∧ S.Nonempty ∧
      E.card ≤ ((N + (k + 1) + (k + 1) + 1) *
        (max (N + (k + 1)) B + 1) ^ (N + (k + 1) + (k + 1))) * S.card ∧
      ∀ a ∈ S, ∀ b ∈ S, ∀ j,
        (w a j).indices = (w b j).indices ∧ ∀ h, (w a j).cell h = (w b j).cell h := by
  obtain ⟨v, S, hSE, hS, hcard, hsame⟩ := common_cell_groups E hE (k + 1) (N + (k + 1)) B
    (fun a => characterTargetCodeGroups (w a))
    (fun a _ => characterTargetCodeGroups_length (w a))
    (fun a ha => by rw [characterTargetCodeGroups_size]; exact Nat.add_le_add_right (hN a ha) _)
    (by
      intro a _ l hl h hh
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl
      rcases List.mem_cons.mp hh with hs | hi
      · subst h
        exact (w a _).shell_le.trans hk
      · exact (w a _).index_le hc hδ B hP h hi)
  refine ⟨S, hSE, hS, hcard, ?_⟩
  intro a ha b hb j
  have he := (hsame a ha).trans (hsame b hb).symm
  exact ⟨(characterTargetCodeGroups_data (w a) (w b) he j).2,
    characterTargetCodeGroups_cells (w a) (w b) he j⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_CellGroupExponentialCost
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact cell-list pigeonhole costs only a fixed exponential in m -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem eventual_cell_group_cost (N r : ℕ) (C z : ℝ)
    (hC : 0 ≤ C) (hz : 1 ≤ z) (hsize : (N + r : ℕ) ≤ z) :
    ∀ᶠ L : ℝ in atTop, ∀ (B : ℕ) (m : ℝ),
      (B + 1 : ℕ) ≤ Real.exp (C * L) → z * L ≤ 2 * m →
      (((N + r + 1) * (max N B + 1) ^ (N + r) : ℕ) : ℝ) ≤
        Real.exp (2 * (C + 2) * m) := by
  filter_upwards [eventually_ge_atTop (max 0 (max (Real.log (N + r + 1 : ℕ))
    (Real.log (N + 1 : ℕ))))] with L hL
  intro B m hB hm
  have hL0 : 0 ≤ L := (le_max_left _ _).trans hL
  have hLr : Real.log (N + r + 1 : ℕ) ≤ L :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hLN : Real.log (N + 1 : ℕ) ≤ L :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  have hpref : (N + r + 1 : ℕ) ≤ Real.exp L := by
    rw [← Real.exp_log (by positivity : (0 : ℝ) < (N + r + 1 : ℕ))]
    exact Real.exp_le_exp.mpr hLr
  have hN : (N + 1 : ℕ) ≤ Real.exp L := by
    rw [← Real.exp_log (by positivity : (0 : ℝ) < (N + 1 : ℕ))]
    exact Real.exp_le_exp.mpr hLN
  have hmax : (max N B + 1 : ℕ) ≤ Real.exp ((C + 1) * L) := by
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_max, ← max_add_add_right]
    apply max_le
    · exact (show (N : ℝ) + 1 ≤ Real.exp L from by simpa only [Nat.cast_add, Nat.cast_one] using hN).trans
        (Real.exp_le_exp.mpr (by nlinarith only [mul_nonneg hC hL0]))
    · exact (show (B : ℝ) + 1 ≤ Real.exp (C * L) from by simpa only [Nat.cast_add, Nat.cast_one] using hB).trans
        (Real.exp_le_exp.mpr (by nlinarith only [hL0]))
  calc
    _ ≤ Real.exp L * (Real.exp ((C + 1) * L)) ^ (N + r) := by
      rw [Nat.cast_mul, Nat.cast_pow]
      exact mul_le_mul hpref (pow_le_pow_left₀ (Nat.cast_nonneg _) hmax _)
        (by positivity) (Real.exp_nonneg _)
    _ = Real.exp ((1 + (C + 1) * (N + r : ℕ)) * L) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp ((C + 2) * z * L) := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left hsize (by linarith : 0 ≤ C + 1)
      have hcoef : 1 + (C + 1) * (N + r : ℕ) ≤ (C + 2) * z := by nlinarith only [hh, hz]
      exact mul_le_mul_of_nonneg_right hcoef hL0
    _ ≤ _ := Real.exp_le_exp.mpr (by
      have hh := mul_le_mul_of_nonneg_left hm (by linarith : 0 ≤ C + 2)
      nlinarith only [hh])

/-- The endpoint count after fixing all cell lists keeps an explicit
exponential rate, with no dependence on the number of fixed labels in it. -/
theorem cell_group_endpoint_rate (e s : ℕ) (F X A B m : ℝ)
    (hcount : (e : ℝ) ≤ F * s) (hF : F ≤ Real.exp (B * m))
    (he : Real.sqrt X * Real.exp (-A * m) ≤ e) :
    Real.sqrt X * Real.exp (-(A + B) * m) ≤ s := by
  have hb : Real.sqrt X * Real.exp (-A * m) ≤ Real.exp (B * m) * s :=
    he.trans (hcount.trans (mul_le_mul_of_nonneg_right hF (Nat.cast_nonneg s)))
  have hh := mul_le_mul_of_nonneg_left hb (Real.exp_nonneg (-B * m))
  have hid : Real.exp (-B * m) * (Real.exp (B * m) * (s : ℝ)) = s := by
    rw [← mul_assoc, ← Real.exp_add, show -B * m + B * m = 0 by ring, Real.exp_zero, one_mul]
  rw [hid] at hh
  calc
    _ = Real.exp (-B * m) * (Real.sqrt X * Real.exp (-A * m)) := by
      calc
        _ = Real.sqrt X * (Real.exp (-B * m) * Real.exp (-A * m)) := by
          rw [← Real.exp_add]
          congr 1
          congr 1
          ring
        _ = _ := by ring
    _ ≤ _ := hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterTargetSelectionRate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixing actual target words preserves exponentially many endpoints -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem eventual_common_character_target_cells (k N : ℕ) (C z : ℝ)
    (hC : 0 ≤ C) (hz : 1 ≤ z) (hsize : (N + (k + 1) + (k + 1) : ℕ) ≤ z) :
    ∀ᶠ L : ℝ in atTop, ∀ (B : ℕ) (m X A : ℝ),
      (B + 1 : ℕ) ≤ Real.exp (C * L) → z * L ≤ 2 * m →
      ∀ (E : Finset ℕ), E.Nonempty → Real.sqrt X * Real.exp (-A * m) ≤ E.card →
      ∀ (P : Finset ℕ) (F : ℕ → ℕ → ℂ) (c δ U : ℝ)
        (T : ℕ → Option (Fin k) → ℝ)
        (w : ∀ a j, CharacterTargetWord P (F a) c δ U k (T a j)),
      0 < c → 0 < δ → 5 * k ≤ B → (∀ p ∈ P, primeLogIndex p ≤ B) →
      (∀ a ∈ E, (∑ j : Option (Fin k), (w a j).indices.length) ≤ N) →
      ∃ S : Finset ℕ, S ⊆ E ∧ S.Nonempty ∧
        Real.sqrt X * Real.exp (-(A + 2 * (C + 2)) * m) ≤ S.card ∧
        ∀ a ∈ S, ∀ b ∈ S, ∀ j,
          (w a j).indices = (w b j).indices ∧ ∀ h, (w a j).cell h = (w b j).cell h := by
  filter_upwards [eventual_cell_group_cost (N + (k + 1)) (k + 1) C z hC hz hsize] with L hcost
  intro B m X A hB hm E hE hcount P F c δ U T w hc hδ hk hP hN
  obtain ⟨S, hSE, hS, hcard, hsame⟩ := common_character_target_cells E hE P F c δ U
    k N B T w hc hδ hk hP hN
  refine ⟨S, hSE, hS, ?_, hsame⟩
  apply cell_group_endpoint_rate E.card S.card _ X A (2 * (C + 2)) m
    (by exact_mod_cast hcard) (hcost B m hB hm) hcount

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_CommonAnchorCells
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixing the two anchor-cell indices per depth before the target words -/
namespace Ostmann
open scoped Classical BigOperators

theorem common_bounded_anchor_cells (E : Finset ℕ) (hE : E.Nonempty) (k B : ℕ)
    (anchor : ℕ → (Fin k × Bool) → ℕ)
    (hbound : ∀ a ∈ E, ∀ j, anchor a j ≤ B) :
    ∃ a₀ ∈ E, ∃ S : Finset ℕ, S ⊆ E ∧ S.Nonempty ∧
      E.card ≤ (B + 1) ^ (2 * k) * S.card ∧ ∀ a ∈ S, anchor a = anchor a₀ := by
  let q : ℕ → (Fin k × Bool) → Fin (B + 1) := fun a j =>
    if ha : a ∈ E then ⟨anchor a j, Nat.lt_succ_of_le (hbound a ha j)⟩ else 0
  obtain ⟨v, _, hv⟩ := Finset.exists_max_image Finset.univ
    (fun v => (E.filter (fun a => q a = v)).card) Finset.univ_nonempty
  let S := E.filter (fun a => q a = v)
  have hSE : S ⊆ E := Finset.filter_subset _ _
  have hcard : E.card ≤ (B + 1) ^ (2 * k) * S.card := by
    calc
      E.card = ∑ v : (Fin k × Bool) → Fin (B + 1), (E.filter (fun a => q a = v)).card := by
        simpa using (Finset.card_eq_sum_card_fiberwise (s := E) (t := Finset.univ)
          (fun a _ => Finset.mem_univ (q a)))
      _ ≤ ∑ _v : (Fin k × Bool) → Fin (B + 1), S.card :=
        Finset.sum_le_sum (fun u hu => hv u hu)
      _ = _ := by simp [Fintype.card_prod, Nat.mul_comm]
  have hS : S.Nonempty := by
    apply Finset.card_pos.mp
    by_contra! hz
    have he : S.card = 0 := Nat.eq_zero_of_le_zero hz
    rw [he, Nat.mul_zero] at hcard
    exact Nat.not_le_of_gt hE.card_pos hcard
  obtain ⟨a₀, ha₀⟩ := hS
  refine ⟨a₀, hSE ha₀, S, hSE, ⟨a₀, ha₀⟩, hcard, ?_⟩
  intro a ha
  have he : q a = q a₀ :=
    (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp ha₀).2.symm
  funext j
  have hj := congrArg Fin.val (congrFun he j)
  simpa only [q, dite_eq_left (hSE ha), dite_eq_left (hSE ha₀)] using hj

/-- The anchor pigeonhole has an absolute exponential rate when its fixed
number of slots is below the bulk scale. -/
theorem anchor_cell_cost (k B : ℕ) (C L z m : ℝ)
    (hC : 0 ≤ C) (hL : 0 ≤ L) (hsize : (2 * k : ℕ) ≤ z)
    (hB : (B + 1 : ℕ) ≤ Real.exp (C * L)) (hm : z * L ≤ 2 * m) :
    (((B + 1) ^ (2 * k) : ℕ) : ℝ) ≤ Real.exp (2 * C * m) := by
  rw [Nat.cast_pow]
  apply (pow_le_pow_left₀ (Nat.cast_nonneg _) hB (2 * k)).trans
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_right hsize (mul_nonneg hC hL)
  have hm' := mul_le_mul_of_nonneg_left hm hC
  nlinarith only [hh, hm']

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterSelectionRate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One endpoint family has common anchors and common target-cell lists -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

/-- The word bin has already been fixed. We fix the anchors and then the
actual shell/list data without changing it, retaining an explicit rate. -/
theorem eventual_common_character_selection (k N : ℕ) (C z : ℝ)
    (hC : 0 ≤ C) (hz : 1 ≤ z) (hsize : (N + (k + 1) + (k + 1) : ℕ) ≤ z) :
    ∀ᶠ L : ℝ in atTop, ∀ (B : ℕ) (m X A : ℝ),
      (B + 1 : ℕ) ≤ Real.exp (C * L) → z * L ≤ 2 * m →
      ∀ (E : Finset ℕ), E.Nonempty → Real.sqrt X * Real.exp (-A * m) ≤ E.card →
      ∀ (P : Finset ℕ) (F : ℕ → ℕ → ℂ) (c δ U : ℝ)
        (anchor : ℕ → (Fin k × Bool) → ℕ) (T : ℕ → Option (Fin k) → ℝ)
        (w : ∀ a j, CharacterTargetWord P (F a) c δ U k (T a j)),
      0 < c → 0 < δ → 5 * k ≤ B → (∀ p ∈ P, primeLogIndex p ≤ B) →
      (∀ a ∈ E, ∀ j, anchor a j ≤ B) →
      (∀ a ∈ E, (∑ j : Option (Fin k), (w a j).indices.length) ≤ N) →
      ∃ a₀ ∈ E, ∃ S : Finset ℕ, S ⊆ E ∧ S.Nonempty ∧
        Real.sqrt X * Real.exp (-(A + 4 * C + 4) * m) ≤ S.card ∧
        ∀ a ∈ S, anchor a = anchor a₀ ∧ ∀ j,
          (w a j).indices = (w a₀ j).indices ∧ ∀ h, (w a j).cell h = (w a₀ j).cell h := by
  filter_upwards [eventual_common_character_target_cells k N C z hC hz hsize,
    eventually_ge_atTop (0 : ℝ)] with L hselect hL
  intro B m X A hB hm E hE hEcount P F c δ U anchor T w hc hδ hk hP hanchor hN
  obtain ⟨a₁, _, E₁, hE₁E, hE₁, hcard, hsame⟩ :=
    common_bounded_anchor_cells E hE k B anchor hanchor
  have hsmallN : ((2 * k : ℕ) : ℝ) ≤ (N + (k + 1) + (k + 1) : ℕ) := by
    exact_mod_cast (show 2 * k ≤ N + (k + 1) + (k + 1) by omega)
  have hsmall : (2 * k : ℕ) ≤ z := hsmallN.trans hsize
  have hcount₁ : Real.sqrt X * Real.exp (-(A + 2 * C) * m) ≤ E₁.card :=
    cell_group_endpoint_rate E.card E₁.card _ X A (2 * C) m
      (by exact_mod_cast hcard) (anchor_cell_cost k B C L z m hC hL hsmall hB hm) hEcount
  obtain ⟨S, hSE₁, hS, hScount, hcodes⟩ := hselect B m X (A + 2 * C) hB hm E₁ hE₁ hcount₁
    P F c δ U T w hc hδ hk hP (fun a ha => hN a (hE₁E ha))
  obtain ⟨a₀, ha₀⟩ := hS
  refine ⟨a₀, hE₁E (hSE₁ ha₀), S, hSE₁.trans hE₁E, ⟨a₀, ha₀⟩, ?_, ?_⟩
  · rw [show A + 4 * C + 4 = (A + 2 * C) + 2 * (C + 2) by ring]
    exact hScount
  · intro a ha
    exact ⟨(hsame a (hSE₁ ha)).trans (hsame a₀ (hSE₁ ha₀)).symm,
      hcodes a ha a₀ ha₀⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterSelectionBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A single depth choice pays for all actual cell-selection codes -/
namespace Ostmann
open scoped Classical BigOperators

theorem character_target_label_bound {P : Finset ℕ} {F : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : Option (Fin k) → ℝ}
    (w : ∀ j, CharacterTargetWord P F c δ U k (T j)) :
    (∑ j : Option (Fin k), (w j).indices.length) ≤ characterTargetLabelBound c δ k := by
  have hb : ((∑ j : Option (Fin k), (w j).indices.length) : ℝ) ≤
      cellRoleCountBound (256 / (δ * c)) k := by
    calc
      _ ≤ ∑ _j : Option (Fin k),
          256 / (δ * c) * Real.exp (2 * (k : ℝ) / 10000) :=
        Finset.sum_le_sum (fun j _ => (w j).length_le)
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_option, Fintype.card_fin,
          nsmul_eq_mul, Nat.cast_add, Nat.cast_one, cellRoleCountBound, cellRoleEpsilon]
        rw [show 2 * (k : ℝ) / 10000 = 2 * (1 / 10000 : ℝ) * k by ring]
        ring
  exact_mod_cast hb.trans (Nat.le_ceil _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterTargetRanges
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact pivot and filler targets lie in the tested late-shell range -/
namespace Ostmann
open scoped Classical BigOperators

theorem characterPivotTarget_sum (k : ℕ) (J : ℝ) (a Δ : Fin k → ℝ) :
    (∑ j, characterPivotTarget k J a Δ j) = (pivotTargets k J a Δ).sum := by
  let v := pivotTargets k J a Δ
  have hlen : v.length = k := by simp [v, pivotTargets, backwardTargets_length, pivotCoefficients]
  have hlist : List.ofFn (fun j : Fin k => characterPivotTarget k J a Δ j) = v := by
    apply List.ext_getElem
    · simp [hlen]
    · intro i hi hj
      simp only [List.getElem_ofFn]
      rfl
  rw [← List.sum_ofFn, hlist]

theorem character_constructed_target_ranges (k : ℕ) (hk : 0 < k) (J τ Δ₀ : ℝ)
    (a : Fin k → Bool → ℝ) (Δ : Fin k → ℝ)
    (hτ : 0 < τ) (hJlo : τ / 2 ≤ J) (hJhi : J ≤ 4 * τ)
    (ha : ∀ j, 0 ≤ a j false + a j true ∧ a j false + a j true ≤ 4 * τ)
    (hΔ : ∀ j, 0 ≤ Δ j ∧ Δ j ≤ (2 : ℝ) ^ j.val * τ / 4)
    (hΔ₀ : 0 ≤ Δ₀ ∧ Δ₀ ≤ τ / 4) :
    let TP := characterPivotTarget k J (fun j => a j false + a j true) Δ
    let TF := characterFillerTarget (1000 * (4 : ℝ) ^ k * τ) Δ₀ J TP a
    ∀ j : Option (Fin k), (2 : ℝ) ^ (k - 1) * τ / 4 ≤ j.elim TF TP ∧
      j.elim TF TP ≤ 600 * (4 : ℝ) ^ k * τ := by
  intro TP TF j
  have ht := pivotTargets_bounds k hk J τ (fun j => a j false + a j true) Δ
    hτ hJlo hJhi ha hΔ
  cases j with
  | some j =>
    have hm : TP j ∈ pivotTargets k J (fun j => a j false + a j true) Δ := List.getElem_mem _
    have hb := ht.2.2 _ hm
    exact ⟨hb.1, hb.2.trans (by
      nlinarith only [show 0 ≤ (4 : ℝ) ^ k * τ by positivity])⟩
  | none =>
    have hf := constructed_fillerTarget_bounds k hk J τ Δ₀ (fun j => a j false + a j true) Δ
      hτ hJlo hJhi ha hΔ hΔ₀
    have he : TF = fillerTarget k τ Δ₀ J (∑ j, (a j false + a j true))
        (pivotTargets k J (fun j => a j false + a j true) Δ).sum := by
      change characterFillerTarget _ _ _ _ _ = _
      unfold characterFillerTarget fillerTarget
      rw [characterPivotTarget_sum]
      ring
    rw [← he] at hf
    change (2 : ℝ) ^ k * τ ≤ TF ∧ TF ≤ 501 * (4 : ℝ) ^ k * τ at hf
    change (2 : ℝ) ^ (k - 1) * τ / 4 ≤ TF ∧ TF ≤ 600 * (4 : ℝ) ^ k * τ
    have hp : (2 : ℝ) ^ (k - 1) ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
    constructor
    · have hh := mul_le_mul_of_nonneg_right hp hτ.le
      have hn : 0 ≤ (2 : ℝ) ^ k * τ := by positivity
      nlinarith only [hh, hn, hf.1]
    · exact hf.2.trans (by
        nlinarith only [show 0 ≤ (4 : ℝ) ^ k * τ by positivity])

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterBackwardsWords
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Whole-shell words for the actual backwards pivot and filler targets -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

/-- The words are constructed after fixing the bin and anchor indices. The
large-parameter threshold is uniform over those choices and the endpoint test. -/
theorem PublishedProgressionInput.character_backwards_words
    (P0 : PublishedProgressionInput) (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ), 20000 ≤ k →
      C ≤ Real.exp ((k : ℝ) / 10000) → ∀ (B z α : ℝ),
      0 ≤ B → 1 ≤ z → 0 < α →
      ∀ᶠ L : ℝ in atTop, ∀ (U τ J : ℝ) (m : ℕ),
      α * L ≤ U → U ≤ Real.log τ → Real.log τ ≤ U + 2 * (k : ℝ) / 10000 →
      0 < τ → (m : ℝ) ≤ z * L → τ / 2 ≤ J → J ≤ 4 * τ →
      ∀ (a : Fin k → Bool → ℕ),
      (∀ j, (a j false : ℝ) + a j true ≤ 4 * τ) →
      ∀ (P : Finset ℕ) (F : ℕ → ℂ), (∀ p ∈ P, p.Prime) →
      (∀ p ∈ P, ‖F p‖ ≤ 1) →
      (∀ u v : ℝ, U ≤ u → v ≤ U + 5 * k → (k : ℝ) / 10000 ≤ v - u →
        ∃ j : ℕ, u ≤ U + j ∧ U + j + 1 ≤ v ∧
          c ≤ ∑ p ∈ loglogShell P (U + j), (p : ℝ)⁻¹) →
      (∀ j : ℕ, j ≤ 5 * k → c ≤ ∑ p ∈ loglogShell P (U + j), (p : ℝ)⁻¹ →
        (∀ p ∈ loglogShell P (U + j),
          Real.log (p : ℝ) ≤ (1000 * (4 : ℝ) ^ k * τ) / 4) →
        δ * (∑ p ∈ loglogShell P (U + j), (p : ℝ)⁻¹) ≤
          ∑ p ∈ loglogShell P (U + j), (p : ℝ)⁻¹ * (F p).re) →
      let TP := characterPivotTarget k J (fun j => (a j false : ℝ) + a j true)
        (fun j => characterPivotGap B z m j.val)
      let TF := characterFillerTarget (1000 * (4 : ℝ) ^ k * τ)
        (characterBaseGap B z m) J TP (fun j b => (a j b : ℝ))
      ∃ w : ∀ j : Option (Fin k), CharacterTargetWord P F c δ U k (j.elim TF TP),
        (∀ j, 0 < (w j).indices.length) ∧
        (∑ j : Option (Fin k), (w j).indices.length) ≤ characterTargetLabelBound c δ k := by
  obtain ⟨C, hC, hwords⟩ := P0.character_target_words c δ hc hδ
  obtain ⟨U₀, hU₀⟩ := eventually_atTop.mp hwords
  refine ⟨C, hC, ?_⟩
  intro k hk hCk B z α hB hz hα
  have hu : ∀ᶠ L : ℝ in atTop, U₀ ≤ α * L :=
    (tendsto_id.const_mul_atTop hα).eventually (eventually_ge_atTop U₀)
  filter_upwards [hu, eventual_character_target_gaps k B z α hB hz hα] with L hU hg
  intro U τ J m hUL hτlo hτhi hτ hm hJlo hJhi a ha P F hP hF hrich htest TP TF
  have hexp : Real.exp (α * L) ≤ τ := by
    exact (Real.exp_le_exp.mpr (hUL.trans hτlo)).trans_eq (Real.exp_log hτ)
  have hgap := hg m τ (Nat.cast_nonneg m) hm hexp
  have hranges := character_constructed_target_ranges k (by omega) J τ
    (characterBaseGap B z m) (fun j b => (a j b : ℝ))
    (fun j => characterPivotGap B z m j.val) hτ hJlo hJhi
    (fun j => ⟨by positivity, ha j⟩) (fun j => hgap.2.2 j.val j.isLt)
    ⟨hgap.1, hgap.2.1⟩
  obtain ⟨w, hw, _⟩ := hU₀ U (hU.trans hUL) k hk hCk τ hτ hτlo hτhi
    P F hP hF hrich htest (fun j : Option (Fin k) => j.elim TF TP)
    (fun j => (hranges j).1) (fun j => (hranges j).2)
  exact ⟨w, hw, character_target_label_bound w⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterCellIntervals
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The pivot lists, two anchors and filler give the actual character cells -/
namespace Ostmann
open scoped Classical BigOperators

theorem characterCellIndex_target {k : ℕ} (w : Fin k → List ℕ)
    (a : Fin k → Bool → ℕ) (u : List ℕ) (J F E : ℝ) (T : Fin k → ℝ)
    (hE : 0 ≤ E) (hw : ∀ j, |((w j).sum : ℝ) - T j| ≤ E)
    (hu : |(u.sum : ℝ) - F| ≤ E) (v : CharacterCell k) :
    |(∑ i, (characterCellIndex w a u v i : ℝ)) -
      characterLogCenter J T (fun j b => (a j b : ℝ)) F (true, some v)| ≤ E := by
  cases v with
  | inl j =>
    have he : (∑ i : Fin (w j).length, (w j).get i) = (w j).sum := by
      rw [← List.sum_ofFn, List.ofFn_get]
    change |(∑ i : Fin (w j).length, ((w j).get i : ℝ)) - T j| ≤ E
    simpa only [← Nat.cast_sum, he] using hw j
  | inr v =>
    cases v with
    | inl x =>
      rcases x with ⟨j, b⟩
      change |(∑ _i : Fin 1, (a j b : ℝ)) - (a j b : ℝ)| ≤ E
      simpa using hE
    | inr x =>
      have he : (∑ i : Fin u.length, u.get i) = u.sum := by
        rw [← List.sum_ofFn, List.ofFn_get]
      change |(∑ i : Fin u.length, (u.get i : ℝ)) - F| ≤ E
      simpa only [← Nat.cast_sum, he] using hu

theorem characterCellIndex_product_bounds {k : ℕ} (w : Fin k → List ℕ)
    (a : Fin k → Bool → ℕ) (u : List ℕ) (J F E c : ℝ) (T : Fin k → ℝ)
    (hE : 0 ≤ E) (hw : ∀ j, |((w j).sum : ℝ) - T j| ≤ E)
    (hu : |(u.sum : ℝ) - F| ≤ E)
    (hc : ∀ v, E + (characterCellSize (fun j => (w j).length) u.length v : ℝ) ≤ c) :
    ∀ v : CharacterCell k,
      Real.exp (characterLogCenter J T (fun j b => (a j b : ℝ)) F (true, some v) - c) ≤
        (∏ i, primeCellLower (characterCellIndex w a u v i) : ℕ) ∧
      (∏ i, primeCellUpper (characterCellIndex w a u v i) : ℕ) ≤
        Real.exp (characterLogCenter J T (fun j b => (a j b : ℝ)) F (true, some v) + c) := by
  intro v
  exact primeCell_target_products (characterCellIndex w a u v) _ E c
    (characterCellIndex_target w a u J F E T hE hw hu v) (hc v)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FixedCharacterTargetCells
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The fixed target-cell priors after the endpoint pigeonhole -/
namespace Ostmann
open scoped Classical BigOperators

theorem fixedTargetCells_subset {P : Finset ℕ} {F : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : Option (Fin k) → ℝ}
    (w : ∀ j, CharacterTargetWord P F c δ U k (T j))
    (i : Σ j, Fin (w j).indices.length) : fixedTargetCells w i ⊆ P :=
  (w i.1).cell_subset _

theorem fixedTargetCells_mass {P : Finset ℕ} {F : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : Option (Fin k) → ℝ}
    (w : ∀ j, CharacterTargetWord P F c δ U k (T j)) (hc : 0 < c) (hδ : 0 < δ)
    (β L : ℝ) (hU : U ≤ β * L) (hL : 5 * (k : ℝ) - Real.log (δ * c / 32) ≤ L)
    (i : Σ j, Fin (w j).indices.length) :
    Real.exp (-(β + 1) * L) ≤ ∑ p ∈ fixedTargetCells w i, (p : ℝ)⁻¹ :=
  (w i.1).cell_mass_exponential hc hδ β L hU hL _ (List.get_mem _ _)

/-- Identical shell/list data preserves the positive norm at every retained
endpoint, although its test function and target certificate may differ. -/
theorem fixedTargetCells_unrotated_mean {P : Finset ℕ} {F G : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T S : Option (Fin k) → ℝ}
    (w : ∀ j, CharacterTargetWord P F c δ U k (T j))
    (ζ : ℂ) (hζ : ‖ζ‖ = 1)
    (v : ∀ j, CharacterTargetWord P (fun p => ζ * G p) c δ U k (S j))
    (hdata : ∀ j, (v j).indices = (w j).indices ∧
      ∀ h, (v j).cell h = (w j).cell h)
    (i : Σ j, Fin (w j).indices.length) :
    δ / 2 ≤ ‖∑ p : P, (primeSubsetPrior P (fixedTargetCells w i) p : ℂ) * G p‖ := by
  have hmem : (w i.1).indices.get i.2 ∈ (v i.1).indices := by
    rw [(hdata i.1).1]
    exact List.get_mem _ _
  have hm := (v i.1).cell_unrotated_mean ζ hζ _ hmem
  rw [(hdata i.1).2] at hm
  exact hm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterPrimeCells
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual pivot, anchor and filler marginals on the common prime set -/
namespace Ostmann
open scoped Classical BigOperators

theorem characterPrimeCells_subset {P : Finset ℕ} {F : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : Option (Fin k) → ℝ}
    (w : ∀ j, CharacterTargetWord P F c δ U k (T j)) (A : Fin k × Bool → Finset ℕ)
    (hA : ∀ j, A j ⊆ P) : ∀ v i, characterPrimeCells w A v i ⊆ P := by
  rintro (j | (j | u)) i
  · exact fixedTargetCells_subset w ⟨some j, i⟩
  · exact hA j
  · exact fixedTargetCells_subset w ⟨none, i⟩

theorem characterPrimeCells_norm_mean {P : Finset ℕ} {F G : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T S : Option (Fin k) → ℝ}
    (w : ∀ j, CharacterTargetWord P F c δ U k (T j))
    (A : Fin k × Bool → Finset ℕ) (ζ : ℂ) (hζ : ‖ζ‖ = 1)
    (v : ∀ j, CharacterTargetWord P (fun p => ζ * G p) c δ U k (S j))
    (hdata : ∀ j, (v j).indices = (w j).indices ∧ ∀ h, (v j).cell h = (w j).cell h)
    (hA : ∀ j, δ / 2 ≤ ‖∑ p : P, (primeSubsetPrior P (A j) p : ℂ) * G p‖) :
    ∀ a i, δ / 2 ≤
      ‖∑ p : P, (primeSubsetPrior P (characterPrimeCells w A a i) p : ℂ) * G p‖ := by
  rintro (j | (j | u)) i
  · exact fixedTargetCells_unrotated_mean w ζ hζ v hdata ⟨some j, i⟩
  · exact hA j
  · exact fixedTargetCells_unrotated_mean w ζ hζ v hdata ⟨none, i⟩

theorem characterPrimeCells_index {P : Finset ℕ} {F : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : Option (Fin k) → ℝ}
    (w : ∀ j, CharacterTargetWord P F c δ U k (T j))
    (A : Fin k × Bool → Finset ℕ) (a : Fin k → Bool → ℕ)
    (hA : ∀ j b p, p ∈ A (j, b) → primeLogIndex p = a j b) :
    ∀ v i p, p ∈ characterPrimeCells w A v i →
      primeLogIndex p = characterCellIndex (fun j => (w (some j)).indices) a (w none).indices v i := by
  rintro (j | (⟨j, b⟩ | u)) i p hp
  · exact (Finset.mem_filter.mp hp).2
  · exact hA j b p hp
  · exact (Finset.mem_filter.mp hp).2

/-- The target certificate gives the whole-atom endpoints used by the
initial amplitude and all later transfer steps. -/
theorem characterPrimeCells_product_bounds {P : Finset ℕ} {F : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : Option (Fin k) → ℝ}
    (w : ∀ j, CharacterTargetWord P F c δ U k (T j))
    (a : Fin k → Bool → ℕ) (J E : ℝ) (hc : 0 < c) (hδ : 0 < δ)
    (hE : ∀ v, 64 / (δ * c) +
      (characterCellSize (fun j => (w (some j)).indices.length) (w none).indices.length v : ℝ) ≤ E) :
    ∀ v : CharacterCell k,
      Real.exp (characterLogCenter J (fun j => T (some j)) (fun j b => (a j b : ℝ))
        (T none) (true, some v) - E) ≤
        (∏ i, primeCellLower (characterCellIndex (fun j => (w (some j)).indices) a (w none).indices v i) : ℕ) ∧
      (∏ i, primeCellUpper (characterCellIndex (fun j => (w (some j)).indices) a (w none).indices v i) : ℕ) ≤
        Real.exp (characterLogCenter J (fun j => T (some j)) (fun j b => (a j b : ℝ))
          (T none) (true, some v) + E) := by
  exact characterCellIndex_product_bounds (fun j => (w (some j)).indices) a (w none).indices
    J (T none) (64 / (δ * c)) E (fun j => T (some j)) (by positivity)
    (fun j => (w (some j)).error.le) (w none).error.le hE

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterCellCovering
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One fixed covering error for every selected character-cell list -/
namespace Ostmann
open scoped Classical BigOperators

theorem character_selected_cell_size_le {P : Finset ℕ} {F : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : Option (Fin k) → ℝ}
    (w : ∀ j, CharacterTargetWord P F c δ U k (T j)) (v : CharacterCell k) :
    characterCellSize (fun j => (w (some j)).indices.length) (w none).indices.length v ≤
      characterTargetLabelBound c δ k + 1 := by
  have hlen (j : Option (Fin k)) : (w j).indices.length ≤ characterTargetLabelBound c δ k :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans
      (character_target_label_bound w)
  rcases v with j | j | u
  · exact (hlen (some j)).trans (Nat.le_succ _)
  · exact Nat.le_add_left 1 _
  · exact (hlen none).trans (Nat.le_succ _)

/-- Neither the selected endpoint nor the number of labels creates another
range hypothesis: the explicit uniform covering error bounds every group. -/
theorem character_selected_product_intervals {P : Finset ℕ} {F : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : Option (Fin k) → ℝ}
    (w : ∀ j, CharacterTargetWord P F c δ U k (T j))
    (a : Fin k → Bool → ℕ) (J : ℝ) (hc : 0 < c) (hδ : 0 < δ) :
    let E := characterCellCoveringError c δ k
    ∀ v : CharacterCell k,
      Real.exp (characterLogCenter J (fun j => T (some j)) (fun j b => (a j b : ℝ))
        (T none) (true, some v) - E) ≤
        (∏ i, primeCellLower (characterCellIndex (fun j => (w (some j)).indices) a (w none).indices v i) : ℕ) ∧
      (∏ i, primeCellUpper (characterCellIndex (fun j => (w (some j)).indices) a (w none).indices v i) : ℕ) ≤
        Real.exp (characterLogCenter J (fun j => T (some j)) (fun j b => (a j b : ℝ))
          (T none) (true, some v) + E) := by
  intro E
  apply characterPrimeCells_product_bounds w a J E hc hδ
  intro v
  have hv : (characterCellSize (fun j => (w (some j)).indices.length) (w none).indices.length v : ℝ) ≤
      (characterTargetLabelBound c δ k : ℝ) + 1 := by
    exact_mod_cast character_selected_cell_size_le w v
  change 64 / (δ * c) + _ ≤ 64 / (δ * c) + (characterTargetLabelBound c δ k : ℝ) + 1
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstructedCharacterCells
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected pivot, filler and anchor cells form actual probability laws -/
namespace Ostmann
open scoped Classical BigOperators

theorem constructed_character_cells_mass {P : Finset ℕ} {F : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : Option (Fin k) → ℝ} {u : Fin k × Bool → ℝ}
    (w : ∀ j, CharacterTargetWord P F c δ U k (T j))
    (a : ∀ j, CharacterAnchorCell P F c δ (u j))
    (hc : 0 < c) (hδ : 0 < δ) (β L : ℝ) (hU : U ≤ β * L)
    (hu : ∀ j, u j ≤ β * L) (hL : 5 * (k : ℝ) - Real.log (δ * c / 32) ≤ L) :
    ∀ v i, Real.exp (-(β + 1) * L) ≤
      ∑ p ∈ characterPrimeCells w (characterAnchorCells a) v i, (p : ℝ)⁻¹ := by
  rintro (j | (j | v)) i
  · exact fixedTargetCells_mass w hc hδ β L hU hL ⟨some j, i⟩
  · apply (a j).cell_mass_exponential hc hδ β L (hu j)
    have hk := Nat.cast_nonneg (α := ℝ) k
    linarith
  · exact fixedTargetCells_mass w hc hδ β L hU hL ⟨none, i⟩

theorem constructed_character_cells_probability {P : Finset ℕ} {F : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : Option (Fin k) → ℝ} {u : Fin k × Bool → ℝ}
    (w : ∀ j, CharacterTargetWord P F c δ U k (T j))
    (a : ∀ j, CharacterAnchorCell P F c δ (u j))
    (hc : 0 < c) (hδ : 0 < δ) :
    ∀ v i, ∑ p : P, primeSubsetPrior P
      (characterPrimeCells w (characterAnchorCells a) v i) p = 1 := by
  intro v i
  apply primeSubsetPrior_mass
  · exact characterPrimeCells_subset w (characterAnchorCells a) (fun j => (a j).cell_subset) v i
  · rcases v with j | j | v
    · exact ((by positivity : 0 < δ * c / (32 * Real.exp (U + (w (some j)).shell))).trans_le
        ((w (some j)).cell_mass _ (List.get_mem _ _))).ne'
    · exact ((a j).cell_mass_pos hc hδ).ne'
    · exact ((by positivity : 0 < δ * c / (32 * Real.exp (U + (w none).shell))).trans_le
        ((w none).cell_mass _ (List.get_mem _ _))).ne'

theorem constructed_character_cells_endpoint_mean {P : Finset ℕ} {F G : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T S : Option (Fin k) → ℝ} {u : Fin k × Bool → ℝ}
    (w : ∀ j, CharacterTargetWord P F c δ U k (T j))
    (a : ∀ j, CharacterAnchorCell P F c δ (u j))
    (ζ : ℂ) (hζ : ‖ζ‖ = 1)
    (v : ∀ j, CharacterTargetWord P (fun p => ζ * G p) c δ U k (S j))
    (b : ∀ j, CharacterAnchorCell P (fun p => ζ * G p) c δ (u j))
    (hdata : ∀ j, (v j).indices = (w j).indices ∧ ∀ h, (v j).cell h = (w j).cell h)
    (hanchor : ∀ j, (b j).index = (a j).index) :
    ∀ j i, δ / 2 ≤ ‖∑ p : P,
      (primeSubsetPrior P (characterPrimeCells w (characterAnchorCells a) j i) p : ℂ) * G p‖ := by
  apply characterPrimeCells_norm_mean w (characterAnchorCells a) ζ hζ v hdata
  intro j
  have h := (b j).unrotated_mean ζ hζ
  rw [(b j).cell_eq_of_index (a j) (hanchor j)] at h
  exact h

theorem constructed_character_cells_prime_bounds {P : Finset ℕ} {F : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : Option (Fin k) → ℝ} {u : Fin k × Bool → ℝ}
    (w : ∀ j, CharacterTargetWord P F c δ U k (T j))
    (a : ∀ j, CharacterAnchorCell P F c δ (u j)) (hP : ∀ p ∈ P, p.Prime) :
    ∀ v i p, p ∈ characterPrimeCells w (characterAnchorCells a) v i →
      let h := characterCellIndex (fun j => (w (some j)).indices)
        (fun j b => (a (j, b)).index) (w none).indices v i
      primeCellLower h ≤ p ∧ p ≤ primeCellUpper h := by
  intro v i p hp
  apply primeCell_interval p _
    (hP p (characterPrimeCells_subset w (characterAnchorCells a)
      (fun j => (a j).cell_subset) v i hp))
  exact characterPrimeCells_index w (characterAnchorCells a) (fun j b => (a (j, b)).index)
    (fun _ _ _ h => (Finset.mem_filter.mp h).2) v i p hp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterBulkSeparation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The true bulk is disjoint from the complementary H cells -/
namespace Ostmann
open scoped Classical BigOperators

theorem CharacterTargetWord.cell_loglog_lower {P : Finset ℕ} {F : ℕ → ℂ}
    {c δ U T : ℝ} {k : ℕ} (w : CharacterTargetWord P F c δ U k T)
    (h p : ℕ) (hp : p ∈ w.cell h) : U < Real.log (Real.log (p : ℝ)) := by
  have hh := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1
  have hn : 0 ≤ (w.shell : ℝ) := Nat.cast_nonneg _
  linarith

theorem constructed_character_cells_bulk_disjoint {P : Finset ℕ} {F : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : Option (Fin k) → ℝ} {u : Fin k × Bool → ℝ}
    (w : ∀ j, CharacterTargetWord P F c δ U k (T j))
    (a : ∀ j, CharacterAnchorCell P F c δ (u j))
    (Q : Finset ℕ) (l h : ℝ)
    (hQ : ∀ p ∈ Q, l < Real.log (Real.log (p : ℝ)) ∧ Real.log (Real.log (p : ℝ)) ≤ h)
    (hU : h ≤ U) (hu : ∀ j, u j + 1 ≤ l ∨ h ≤ u j) :
    ∀ v i, Disjoint Q (characterPrimeCells w (characterAnchorCells a) v i) := by
  rintro (j | (j | v)) i
  · apply Finset.disjoint_left.mpr
    intro p hp hpc
    have hh := (w (some j)).cell_loglog_lower _ p hpc
    linarith [(hQ p hp).2]
  · apply Finset.disjoint_left.mpr
    intro p hp hpc
    have hh := (Finset.mem_filter.mp (Finset.mem_filter.mp hpc).1).2
    rcases hu j with hlow | hhigh
    · linarith [hh.2, (hQ p hp).1]
    · linarith [hh.1, (hQ p hp).2]
  · apply Finset.disjoint_left.mpr
    intro p hp hpc
    have hh := (w none).cell_loglog_lower _ p hpc
    linarith [(hQ p hp).2]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialGapRate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Choosing the initial gap without changing the endpoint rate -/

namespace Ostmann

open Filter
open scoped BigOperators

theorem eventually_bulkCount_bounds (z : ℝ) (hz : 0 < z) :
    ∀ᶠ L : ℝ in atTop, 0 < L ∧ 1 ≤ ⌊z * L⌋₊ ∧
      (⌊z * L⌋₊ : ℝ) ≤ z * L ∧ z * L ≤ 2 * ⌊z * L⌋₊ := by
  filter_upwards [eventually_ge_atTop (2 / z)] with L hL
  have h₂ : (2 : ℝ) ≤ z * L := by simpa only [mul_comm] using (div_le_iff₀ hz).mp hL
  have hLp : 0 < L := (div_pos (by norm_num : (0 : ℝ) < 2) hz).trans_le hL
  have hm : 1 ≤ ⌊z * L⌋₊ := (Nat.one_le_floor_iff (z * L)).mpr (by linarith)
  have hm' : (1 : ℝ) ≤ ⌊z * L⌋₊ := by exact_mod_cast hm
  exact ⟨hLp, hm, Nat.floor_le (by positivity), by linarith [Nat.lt_floor_add_one (z * L)]⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterConstructedCounts
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Every constructed list fits the chosen finite character budgets -/
namespace Ostmann
open scoped Classical BigOperators

theorem characterCellSlots_card {k : ℕ} (r : Fin k → ℕ) (f : ℕ) :
    Fintype.card (Σ v, Fin (characterCellSize r f v)) = (∑ j, r j) + 2 * k + f := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  simp [Fintype.sum_sum_type, characterCellSize, Nat.mul_comm, Nat.add_assoc]

theorem character_constructed_counts {P : Finset ℕ} {G : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : Option (Fin k) → ℝ}
    (w : ∀ j, CharacterTargetWord P G c δ U k (T j)) :
    let N := characterTargetLabelBound c δ k
    let r := fun j => (w (some j)).indices.length
    let f := (w none).indices.length
    (∀ j, r j ≤ N) ∧ f ≤ N ∧
      Fintype.card (Σ v, Fin (characterCellSize r f v)) ≤ N + 2 * k ∧
      1 + ((∑ j, r j) + 2 * k) ≤ N + (k + 1) + (k + 1) := by
  intro N r f
  have h := character_target_label_bound w
  rw [Fintype.sum_option] at h
  change f + (∑ j, r j) ≤ N at h
  have hr (j) : r j ≤ ∑ j, r j :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  refine ⟨fun j => (hr j).trans (by omega), by omega, ?_, by omega⟩
  rw [characterCellSlots_card]
  omega

theorem character_constructed_mass_budgets {P : Finset ℕ} {G : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : Option (Fin k) → ℝ}
    (w : ∀ j, CharacterTargetWord P G c δ U k (T j))
    (C z : ℝ) (hC : 0 ≤ C)
    (hbudget : 4 * C * (characterTargetLabelBound c δ k + (k + 1) + (k + 1) : ℕ) ≤ z) :
    let r := fun j => (w (some j)).indices.length
    let f := (w none).indices.length
    4 * Fintype.card (Σ v, Fin (characterCellSize r f v)) * C ≤ z ∧
      C * (∑ j, (r j : ℝ)) ≤ z / 4 := by
  intro r f
  have hcounts := character_constructed_counts w
  dsimp only at hcounts
  have hcard : Fintype.card (Σ v, Fin (characterCellSize r f v)) ≤
      characterTargetLabelBound c δ k + (k + 1) + (k + 1) := hcounts.2.2.1.trans (by omega)
  have hcardR : (Fintype.card (Σ v, Fin (characterCellSize r f v)) : ℝ) ≤
      (characterTargetLabelBound c δ k + (k + 1) + (k + 1) : ℕ) := by exact_mod_cast hcard
  have hsum : (∑ j, r j) ≤ characterTargetLabelBound c δ k + (k + 1) + (k + 1) := by
    have hh := hcounts.2.2.2
    change 1 + ((∑ j, r j) + 2 * k) ≤ _ at hh
    omega
  have hsumR : (∑ j, (r j : ℝ)) ≤
      (characterTargetLabelBound c δ k + (k + 1) + (k + 1) : ℕ) := by exact_mod_cast hsum
  constructor
  · have hh := mul_le_mul_of_nonneg_left hcardR (show 0 ≤ 4 * C by positivity)
    nlinarith only [hh, hbudget]
  · have hh := mul_le_mul_of_nonneg_left hsumR (show 0 ≤ 4 * C by positivity)
    nlinarith only [hh, hbudget]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterConstructedRanges
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected shells give the actual character prime ranges -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem prime_of_loglog_lower (p : ℕ) (hp : p.Prime) (a : ℝ)
    (ha : a ≤ Real.log (Real.log (p : ℝ))) : Real.exp (Real.exp a) ≤ p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have h₁ := Real.exp_le_exp.mpr ha
  rw [Real.exp_log (Real.log_pos hp1)] at h₁
  have h₂ := Real.exp_le_exp.mpr h₁
  rwa [Real.exp_log hp0] at h₂

theorem prime_of_loglog_upper (p : ℕ) (hp : p.Prime) (a : ℝ)
    (ha : Real.log (Real.log (p : ℝ)) ≤ a) : (p : ℝ) ≤ Real.exp (Real.exp a) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have h₁ := Real.exp_le_exp.mpr ha
  rw [Real.exp_log (Real.log_pos hp1)] at h₁
  have h₂ := Real.exp_le_exp.mpr h₁
  rwa [Real.exp_log hp0] at h₂

theorem CharacterAnchorCell.cell_loglog_bounds {P : Finset ℕ} {G : ℕ → ℂ} {c δ u : ℝ}
    (a : CharacterAnchorCell P G c δ u) {p : ℕ} (hp : p ∈ a.cell) :
    u < Real.log (Real.log (p : ℝ)) ∧ Real.log (Real.log (p : ℝ)) ≤ u + 1 :=
  (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2

theorem constructed_character_anchor_ranges {P : Finset ℕ} {G : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : Option (Fin k) → ℝ} {u : Fin k × Bool → ℝ}
    (hP : ∀ p ∈ P, p.Prime)
    (w : ∀ j, CharacterTargetWord P G c δ U k (T j))
    (a : ∀ j, CharacterAnchorCell P G c δ (u j)) (L γs νa : ℝ)
    (hsmall : ∀ j : Fin k, u (j, false) + 1 ≤ γs * L)
    (hbig : ∀ j : Fin k, νa * L ≤ u (j, true)) :
    let R := characterPrimeCells w (characterAnchorCells a)
    (∀ j p, p ∈ R (.inr (.inl (j, false))) ⟨0, by change 0 < 1; omega⟩ →
      (p : ℝ) ≤ Real.exp (Real.exp (γs * L))) ∧
    (∀ j p, p ∈ R (.inr (.inl (j, true))) ⟨0, by change 0 < 1; omega⟩ →
      Real.exp (Real.exp (νa * L)) ≤ p) := by
  intro R
  constructor
  · intro j p hp
    apply prime_of_loglog_upper p (hP p ((a (j, false)).cell_subset hp))
    exact ((a (j, false)).cell_loglog_bounds hp).2.trans (hsmall j)
  · intro j p hp
    apply prime_of_loglog_lower p (hP p ((a (j, true)).cell_subset hp))
    exact (hbig j).trans ((a (j, true)).cell_loglog_bounds hp).1.le

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterConstructedTargetCutoff
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructed pivot targets lie below the comparison prime cutoff -/
namespace Ostmann
open Filter
open scoped Classical BigOperators Topology

theorem eventual_exp_linear_allowance (β γ D A c : ℝ) (hgap : β < γ)
    (hβ : 0 ≤ β) (hA : 0 ≤ A) (hc : 0 ≤ c) :
    ∀ᶠ L : ℝ in atTop, ∀ τ y : ℝ, 0 < τ →
      Real.log τ ≤ β * L + D → y ≤ A * τ → y + c ≤ Real.exp (γ * L) := by
  have hlim : Tendsto (fun L : ℝ => Real.exp (-(γ - β) * L)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq, neg_mul] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop (sub_pos.mpr hgap))
  have hsmall := hlim.eventually_le_const (by positivity : 0 < (A * Real.exp D + c + 1)⁻¹)
  filter_upwards [hsmall, eventually_ge_atTop (0 : ℝ)] with L hsmall hL τ y hτ hlog hy
  have ht : τ ≤ Real.exp (β * L + D) := by
    simpa only [Real.exp_log hτ] using Real.exp_le_exp.mpr hlog
  have hcoef : (A * Real.exp D + c) * Real.exp (-(γ - β) * L) ≤ 1 := by
    have hp : 0 < A * Real.exp D + c + 1 := by positivity
    have hh := mul_le_mul_of_nonneg_left hsmall (le_of_lt hp)
    rw [mul_inv_cancel₀ (ne_of_gt hp)] at hh
    have he := Real.exp_nonneg (-(γ - β) * L)
    nlinarith only [hh, he]
  have he : 1 ≤ Real.exp (β * L) := Real.one_le_exp_iff.mpr (mul_nonneg hβ hL)
  have hrat : Real.exp (-(γ - β) * L) * Real.exp (γ * L) = Real.exp (β * L) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    y + c ≤ A * Real.exp (β * L + D) + c * Real.exp (β * L) := by
      exact add_le_add (hy.trans (mul_le_mul_of_nonneg_left ht hA))
        (by nlinarith only [he, hc])
    _ = (A * Real.exp D + c) * Real.exp (β * L) := by rw [Real.exp_add]; ring
    _ = (A * Real.exp D + c) *
        (Real.exp (-(γ - β) * L) * Real.exp (γ * L)) := by rw [hrat]
    _ ≤ Real.exp (γ * L) := by
      nlinarith only [mul_le_mul_of_nonneg_right hcoef (Real.exp_nonneg (γ * L))]

/-- The cutoff is uniform over the selected anchors, bin and original floor length. -/
theorem eventual_constructed_character_target_cutoff (k : ℕ) (hk : 0 < k)
    (B z α β βg c : ℝ) (hB : 0 ≤ B) (hz : 1 ≤ z) (hα : 0 < α)
    (hβ : 0 ≤ β) (hβg : β < βg) (hc : 0 ≤ c) :
    ∀ᶠ L : ℝ in atTop, ∀ (U τ J : ℝ) (m : ℕ) (a : Fin k → Bool → ℕ),
      α * L ≤ U → U ≤ β * L → U ≤ Real.log τ →
      Real.log τ ≤ U + 2 * (k : ℝ) / 10000 → 0 < τ →
      (m : ℝ) ≤ z * L → τ / 2 ≤ J → J ≤ 4 * τ →
      (∀ j, (a j false : ℝ) + a j true ≤ 4 * τ) →
      ∀ j, characterPivotTarget k J (fun j => (a j false : ℝ) + a j true)
        (fun j => characterPivotGap B z m j.val) j + c ≤ Real.exp (βg * L) := by
  filter_upwards [eventual_character_target_gaps k B z α hB hz hα,
    eventual_exp_linear_allowance β βg (2 * (k : ℝ) / 10000)
      (600 * (4 : ℝ) ^ k) c hβg hβ (by positivity) hc] with L hgap hcut
  intro U τ J m a hUL hUβ hUτ hτU hτ hm hJlo hJhi ha j
  have hτlo : Real.exp (α * L) ≤ τ := by
    exact (Real.exp_le_exp.mpr (hUL.trans hUτ)).trans_eq (Real.exp_log hτ)
  have hg := hgap m τ (Nat.cast_nonneg _) hm hτlo
  have hr := character_constructed_target_ranges k hk J τ (characterBaseGap B z m)
    (fun j b => (a j b : ℝ)) (fun j => characterPivotGap B z m j.val)
    hτ hJlo hJhi (fun j => ⟨by positivity, ha j⟩)
    (fun j => hg.2.2 j.val j.isLt) ⟨hg.1, hg.2.1⟩ (some j)
  exact hcut τ _ hτ (by linarith only [hUβ, hτU]) hr.2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterLengthBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform rounded character lengths -/
namespace Ostmann
open Filter

theorem eventual_character_length_bounds (z : ℝ) (hz : 1 < z) :
    ∀ᶠ L : ℝ in atTop, 0 < L ∧ 1 ≤ ⌊z * L⌋₊ ∧
      L ≤ (⌊z * L⌋₊ : ℝ) ∧ (⌊z * L⌋₊ : ℝ) ≤ z * L ∧
      z * L ≤ 2 * (⌊z * L⌋₊ : ℝ) := by
  filter_upwards [eventually_bulkCount_bounds z (by linarith),
    eventually_ge_atTop (1 / (z - 1))] with L hbounds hL
  refine ⟨hbounds.1, hbounds.2.1, ?_, hbounds.2.2.1, hbounds.2.2.2⟩
  have hz0 : 0 < z - 1 := by linarith
  have hh := (div_le_iff₀ hz0).mp hL
  have hf := Nat.lt_floor_add_one (z * L)
  nlinarith only [hh, hf]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterWordBinSelection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform rates when selecting the actual initial character word bin -/
namespace Ostmann
open scoped Classical BigOperators

theorem character_word_bin_selection {P B : Type*} [Fintype P] [Fintype B] [Nonempty B]
    (m : ℕ) (L X A C δ : ℝ) (hm : 1 ≤ m) (hLm : L ≤ m)
    (hX : 0 < X) (hC : 0 ≤ C) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (E : Finset ℕ) (hE : Real.sqrt X * Real.exp (-A * m) ≤ E.card)
    (μ : Fin (m + 1) → P → ℝ) (F : ℕ → Fin (m + 1) → P → ℂ)
    (bin : (Fin (m + 1) → P) → B)
    (hcount : (Fintype.card B : ℝ) ≤ Real.exp (C * L))
    (hmean : ∀ a ∈ E, ∀ i, δ ≤ ‖∑ p, (μ i p : ℂ) * F a i p‖) :
    ∃ b : B, ∃ S : Finset ℕ, S ⊆ E ∧ S.Nonempty ∧
      Real.sqrt X * Real.exp (-(A + C) * m) ≤ S.card ∧
      ∀ a ∈ S, Real.exp (-(C - 2 * Real.log δ) * m) ≤
        ‖binnedWordAverage μ (F a) bin b‖ := by
  obtain ⟨b, S, hSE, hcard, hword⟩ := common_large_word_bin_of_norm E μ F bin δ hδ.le hmean
  have hK : (Fintype.card B : ℝ) ≤ Real.exp (C * m) :=
    hcount.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hLm hC))
  have hcard₀ : (E.card : ℝ) ≤ (Fintype.card B : ℝ) * S.card := by
    exact_mod_cast hcard
  have hcard' : (E.card : ℝ) ≤ Real.exp (C * m) * S.card :=
    hcard₀.trans (mul_le_mul_of_nonneg_right hK (Nat.cast_nonneg _))
  have hS : Real.sqrt X * Real.exp (-(A + C) * m) ≤ S.card := by
    apply (mul_le_mul_iff_right₀ (Real.exp_pos (C * m))).mp
    calc
      _ = Real.sqrt X * Real.exp (-A * m) := by
        calc
          _ = Real.sqrt X * Real.exp (C * m + -(A + C) * m) := by
            rw [Real.exp_add]; ring
          _ = _ := by congr 2; ring
      _ ≤ E.card := hE
      _ ≤ _ := by simpa only [mul_comm] using hcard'
  have hSpos : 0 < (S.card : ℝ) :=
    (mul_pos (Real.sqrt_pos.mpr hX) (Real.exp_pos _)).trans_le hS
  refine ⟨b, S, hSE, Finset.card_pos.mp (by exact_mod_cast hSpos), hS, ?_⟩
  intro a ha
  have hlog : Real.log δ ≤ 0 := Real.log_nonpos hδ.le hδ1
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hpow : Real.exp (2 * Real.log δ * m) ≤ δ ^ (m + 1) := by
    calc
      _ ≤ Real.exp ((m + 1 : ℕ) * Real.log δ) := by
        apply Real.exp_le_exp.mpr
        push_cast
        nlinarith only [hlog, hm']
      _ = _ := by rw [Real.exp_nat_mul, Real.exp_log hδ]
  have hnorm := norm_nonneg (binnedWordAverage μ (F a) bin b)
  have he := (hpow.trans (hword a ha)).trans (mul_le_mul_of_nonneg_right hK hnorm)
  apply (mul_le_mul_iff_right₀ (Real.exp_pos (C * m))).mp
  calc
    _ = Real.exp (2 * Real.log δ * m) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := by simpa only [mul_comm] using he

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterWordSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Supported top-first words retain their actual logarithmic bin -/
namespace Ostmann
open scoped Classical BigOperators

theorem top_first_word_log_bounds (m : ℕ) (ℓ : Fin (m + 1) → ℝ) (b τ : ℝ)
    (hbulk : ∀ i : Fin m, 0 ≤ ℓ i.succ ∧ ℓ i.succ ≤ b)
    (hsize : (m : ℝ) * b ≤ τ) (htop : τ ≤ ℓ 0 ∧ ℓ 0 ≤ 3 * τ) :
    τ ≤ ∑ i, ℓ i ∧ (∑ i, ℓ i) ≤ 4 * τ := by
  have h₀ : 0 ≤ ∑ i : Fin m, ℓ i.succ :=
    Finset.sum_nonneg (fun i _ => (hbulk i).1)
  have h₁ : (∑ i : Fin m, ℓ i.succ) ≤ (m : ℝ) * b := by
    calc
      _ ≤ ∑ _i : Fin m, b := Finset.sum_le_sum (fun i _ => (hbulk i).2)
      _ = _ := by simp
  rw [Fin.sum_univ_succ]
  constructor <;> linarith [htop.1, htop.2]

theorem binnedWordAverage_support {A B : Type*} [Fintype A] {n : ℕ}
    (μ : Fin n → A → ℝ) (F : Fin n → A → ℂ) (bin : (Fin n → A) → B) (b : B)
    (h : binnedWordAverage μ F bin b ≠ 0) :
    ∃ w, bin w = b ∧ productPrior μ w ≠ 0 := by
  by_contra! hnone
  apply h
  unfold binnedWordAverage
  apply Finset.sum_eq_zero
  intro w _
  by_cases hw : bin w = b
  · simp only [hw, ite_true, if_true, hnone w hw, Complex.ofReal_zero, zero_mul]
  · simp only [hw, ite_false, if_false]

theorem supported_character_word_bounds (m : ℕ) (P U T : Finset ℕ)
    (Q : Fin (m + 1) → Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hzero : Q 0 = T) (hsucc : ∀ i : Fin m, Q i.succ = U)
    (b τ : ℝ) (hsize : (m : ℝ) * b ≤ τ)
    (htop : ∀ p ∈ T, τ ≤ Real.log (p : ℝ) ∧ Real.log (p : ℝ) ≤ 3 * τ)
    (hbulk : ∀ p ∈ U, Real.log (p : ℝ) ≤ b)
    (w : Fin (m + 1) → P)
    (hw : productPrior (fun i => primeSubsetPrior P (Q i)) w ≠ 0) :
    τ ≤ ∑ i, Real.log (w i : ℝ) ∧ (∑ i, Real.log (w i : ℝ)) ≤ 4 * τ := by
  have hs (i : Fin (m + 1)) : (w i : ℕ) ∈ Q i := by
    apply primeSubsetPrior_support P (Q i) (w i)
    exact (Finset.prod_ne_zero_iff.mp hw) i (Finset.mem_univ i)
  apply top_first_word_log_bounds m _ b τ
  · intro i
    constructor
    · exact Real.log_nonneg (by exact_mod_cast (hP (w i.succ) (w i.succ).property).one_le)
    · apply hbulk
      simpa only [hsucc] using hs i.succ
  · exact hsize
  · apply htop
    simpa only [hzero] using hs 0

theorem supported_character_bin_bounds (m : ℕ) (P U T : Finset ℕ)
    (Q : Fin (m + 1) → Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hzero : Q 0 = T) (hsucc : ∀ i : Fin m, Q i.succ = U)
    (b τ : ℝ) (hτ : 2 ≤ τ) (hsize : (m : ℝ) * b ≤ τ)
    (htop : ∀ p ∈ T, τ ≤ Real.log (p : ℝ) ∧ Real.log (p : ℝ) ≤ 3 * τ)
    (hbulk : ∀ p ∈ U, Real.log (p : ℝ) ≤ b)
    (F : Fin (m + 1) → P → ℂ) (j : Fin (⌊4 * τ⌋₊ + 1))
    (hj : binnedWordAverage (fun i => primeSubsetPrior P (Q i)) F
      (fun w => wordLogBin τ (fun i => Real.log (w i : ℝ))) j ≠ 0) :
    τ / 2 ≤ (j.val : ℝ) ∧ (j.val : ℝ) ≤ 4 * τ ∧ 0 < j.val := by
  obtain ⟨w, hwj, hw⟩ := binnedWordAverage_support _ _ _ _ hj
  have hs := supported_character_word_bounds m P U T Q hP hzero hsucc b τ hsize htop hbulk w hw
  have hjval : j.val = ⌊∑ i, Real.log (w i : ℝ)⌋₊ := by
    rw [← hwj]
    exact wordLogBin_val τ _ hs.2
  have hlo := Nat.lt_floor_add_one (∑ i, Real.log (w i : ℝ))
  have hhi := Nat.floor_le (show 0 ≤ ∑ i, Real.log (w i : ℝ) by linarith [hs.1])
  have hjlo : τ / 2 ≤ (j.val : ℝ) := by rw [hjval]; linarith [hs.1]
  refine ⟨hjlo, ?_, ?_⟩
  · rw [hjval]; exact hhi.trans hs.2
  · have : (0 : ℝ) < j.val := by linarith
    exact_mod_cast this

theorem character_select_supported_bin (m : ℕ) (L X A C δ b τ : ℝ)
    (hm : 1 ≤ m) (hLm : L ≤ m) (hX : 0 < X) (hC : 0 ≤ C)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hτ : 2 ≤ τ)
    (P U T : Finset ℕ) (Q : Fin (m + 1) → Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hzero : Q 0 = T)
    (hsucc : ∀ i : Fin m, Q i.succ = U) (hsize : (m : ℝ) * b ≤ τ)
    (htop : ∀ p ∈ T, τ ≤ Real.log (p : ℝ) ∧ Real.log (p : ℝ) ≤ 3 * τ)
    (hbulk : ∀ p ∈ U, Real.log (p : ℝ) ≤ b)
    (E : Finset ℕ) (hE : Real.sqrt X * Real.exp (-A * m) ≤ E.card)
    (F : ℕ → Fin (m + 1) → P → ℂ)
    (hcount : (Fintype.card (Fin (⌊4 * τ⌋₊ + 1)) : ℝ) ≤ Real.exp (C * L))
    (hmean : ∀ x ∈ E, ∀ i, δ ≤ ‖∑ p : P, (primeSubsetPrior P (Q i) p : ℂ) * F x i p‖) :
    ∃ j : Fin (⌊4 * τ⌋₊ + 1), τ / 2 ≤ (j.val : ℝ) ∧
      (j.val : ℝ) ≤ 4 * τ ∧ 0 < j.val ∧
      ∃ S : Finset ℕ, S ⊆ E ∧ S.Nonempty ∧
        Real.sqrt X * Real.exp (-(A + C) * m) ≤ S.card ∧
        ∀ x ∈ S, Real.exp (-(C - 2 * Real.log δ) * m) ≤
          ‖binnedWordAverage (fun i => primeSubsetPrior P (Q i)) (F x)
            (fun w => wordLogBin τ (fun i => Real.log (w i : ℝ))) j‖ := by
  obtain ⟨j, S, hSE, hSne, hScard, hword⟩ := character_word_bin_selection m L X A C δ
    hm hLm hX hC hδ hδ1 E hE (fun i => primeSubsetPrior P (Q i)) F
    (fun w => wordLogBin τ (fun i => Real.log (w i : ℝ))) hcount hmean
  obtain ⟨x, hx⟩ := hSne
  have hn : binnedWordAverage (fun i => primeSubsetPrior P (Q i)) (F x)
      (fun w => wordLogBin τ (fun i => Real.log (w i : ℝ))) j ≠ 0 :=
    norm_pos_iff.mp ((Real.exp_pos _).trans_le (hword x hx))
  obtain ⟨hjl, hju, hjpos⟩ := supported_character_bin_bounds m P U T Q hP hzero hsucc
    b τ hτ hsize htop hbulk (F x) j hn
  exact ⟨j, hjl, hju, hjpos, S, hSE, ⟨x, hx⟩, hScard, hword⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterConstructedEndpointContradiction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The endpoint contradiction for the actual constructed character cells -/
namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap FourierTransform ComplexConjugate

theorem eventual_constructed_character_endpoint_contradiction (n : ℕ)
    (a b z Cmass Ctotal Aend Bword B B₁ c s γ H α K βg βw γs βa γw νw νa ε c₀ δ β : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hz : 1 < z)
    (hCmass : 0 < Cmass) (hCtotal : 0 ≤ Ctotal) (hc : 1 ≤ c)
    (hs : 0 < s) (hγ : 0 < γ) (hH : 0 ≤ H) (hα : 0 < α)
    (hgapInitial : 2 * ((2 * Real.log (3 / a) + 3 + 2 * Ctotal) +
      (Aend + 2 * Bword + 1) + 2) ≤ B) (hB : 0 ≤ B)
    (hB₁ : 0 ≤ B₁) (hB₁eq : B₁ = Aend + 2 * Bword + 3)
    (hBstrong : 2 * B₁ + 5 ≤ B) (hBpos : 1 ≤ B) (ha1 : a ≤ 1)
    (hβg : 0 < βg) (hγw : 0 ≤ γw) (hαw : α < βw) (hsw : γs < βw)
    (hαa : α < βa) (hwa : γw < βa) (hwg : γw ≤ βg)
    (hβw : βw < νw) (hβa : βa < νa) (hε : 0 < ε)
    (hbudgetAll : 4 * Cmass *
      (characterTargetLabelBound c₀ δ (n + 1) + (n + 2) + (n + 2) : ℕ) ≤ z)
    (hgapFinal : 2 * B₁ +
      ((γw + Real.log ((Real.log 2)⁻¹ + 1)) / a + max (Real.log 3) 0 + ε) +
      Real.log 2 + 6 ≤ B + 20 * Real.log a)
    (hentropy : (βg + Real.log ((Real.log 2)⁻¹ + 1) + max (Real.log 3) 0 + ε) +
      (B + 20 * Real.log z + 1) + 2 * B₁ + 1 ≤ (n : ℝ) * Real.log 2 - 1)
    (hc₀ : 0 < c₀) (hδ : 0 < δ) (hβ : 0 ≤ β) (hβgap : β < βg)
    (hβmass : β + 1 ≤ Cmass)
    (hcover : characterCellCoveringError c₀ δ (n + 1) ≤ c)
    (ψ : 𝓢(ℝ, ℂ)) (hψ : ∀ x, 0 ≤ (ψ x).re) (hreal : ∀ x, (ψ x).im = 0)
    (heven : ∀ v : ℝ, 𝓕 ψ (-v) = 𝓕 ψ v)
    (hψK : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K)
    (hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0) :
    ∀ᶠ L : ℝ in atTop,
    let m := ⌊z * L⌋₊
    ∀ (Ulate τ bmax : ℝ) (P U T₀ : Finset ℕ) (_hP : ∀ p ∈ P, p.Prime)
      (Q : Fin (m + 1) → Finset ℕ),
    α * L ≤ Ulate → Ulate ≤ β * L → Ulate ≤ Real.log τ →
    Real.log τ ≤ Ulate + 2 * ((n + 1 : ℕ) : ℝ) / 10000 → 0 < τ →
    Q 0 = T₀ → (∀ i : Fin m, Q i.succ = U) → (∀ i, Q i ⊆ P) →
    a * L ≤ ∑ p ∈ U, (p : ℝ)⁻¹ → b ≤ ∑ p ∈ T₀, (p : ℝ)⁻¹ →
    (∑ p : P, (p : ℝ)⁻¹) ≤ Ctotal * L →
    (∀ p ∈ P, Real.exp (Real.exp (α * L)) ≤ p ∧
      (p : ℝ) ≤ Real.exp (Real.exp (βg * L))) →
    (∀ p ∈ U, Real.exp (Real.exp (νw * L)) ≤ p ∧
      (p : ℝ) ≤ Real.exp (Real.exp (γw * L))) →
    Disjoint U T₀ → (m : ℝ) * bmax ≤ τ →
    (∀ p ∈ T₀, τ ≤ Real.log (p : ℝ) ∧ Real.log (p : ℝ) ≤ 3 * τ) →
    (∀ p ∈ U, Real.log (p : ℝ) ≤ bmax) →
    ∀ (l h : ℝ),
    (∀ p ∈ U, l < Real.log (Real.log (p : ℝ)) ∧ Real.log (Real.log (p : ℝ)) ≤ h) →
    h ≤ Ulate → ∀ u : Fin (n + 1) × Bool → ℝ,
    (∀ j, u j ≤ β * L) → (∀ j, u j + 1 ≤ l ∨ h ≤ u j) →
    (∀ j, u (j, false) + 1 ≤ γs * L) → (∀ j, νa * L ≤ u (j, true)) →
    (∀ j, 3 * Real.exp (u (j, false)) + 3 * Real.exp (u (j, true)) ≤ 4 * τ) →
    ∀ (F₀ : ℕ → ℂ) (ac : ∀ j, CharacterAnchorCell P F₀ c₀ δ (u j))
      (bin : Fin (⌊4 * τ⌋₊ + 1)), τ / 2 ≤ (bin.val : ℝ) →
    (bin.val : ℝ) ≤ 4 * τ → 0 < bin.val →
    ∀ w : ∀ j, CharacterTargetWord P F₀ c₀ δ Ulate (n + 1)
      (characterConstructedTargets (n + 1) bin.val
        (1000 * (4 : ℝ) ^ (n + 1) * τ) B z m (fun j => (ac j).index) j),
    (∀ j, 0 < (w j).indices.length) →
    ∀ (χ : ∀ p : ℕ, DirichletCharacter ℂ p), (∀ p ∈ P, χ p ^ 2 ≠ 1) →
    ∀ (center : ∀ p : ℕ, ZMod p) (E : Finset ℕ) (ρ : ℝ),
    Real.sqrt (Real.exp (1000 * (4 : ℝ) ^ (n + 1) * τ)) *
      Real.exp (-Aend * m) ≤ E.card →
    Real.exp (-Bword * m) ≤ ρ →
    (∀ x ∈ E, s ≤ (ψ ((x : ℝ) / Real.exp (1000 * (4 : ℝ) ^ (n + 1) * τ))).re) →
    (∀ x ∈ E, ρ ≤ ‖binnedWordAverage (fun i => primeSubsetPrior P (Q i))
      (fun _ p => χ p ((x : ZMod p) - center p))
      (fun w => wordLogBin τ (fun i => Real.log (w i : ℝ))) bin‖) →
    (∀ x ∈ E, ∀ v i, γ ≤
      ‖∑ p : P, (primeSubsetPrior P (characterPrimeCells w (characterAnchorCells ac) v i) p : ℂ) *
        χ p ((x : ZMod p) - center p)‖) →
    False := by
  let N := characterTargetLabelBound c₀ δ (n + 1)
  let Bnb := N + (n + 2) + (n + 2)
  have hend := eventual_uniform_character_endpoint_contradiction n N Bnb
    a b z Cmass Ctotal Aend Bword B B₁ c s γ H α K βg βw γs βa γw νw νa ε
    ha hb hz hCmass hCtotal hc hs hγ hH hα hgapInitial hB hB₁ hB₁eq hBstrong hBpos
    ha1 hβg hγw hαw hsw hαa hwa hwg hβw hβa hε hbudgetAll hgapFinal hentropy
    ψ hψ hreal heven hψK hsupp
  have htarget := eventual_constructed_character_target_cutoff (n + 1) (by omega)
    B z α β βg c hB hz.le hα hβ hβgap (by linarith)
  filter_upwards [hend, htarget, eventual_character_length_bounds z hz,
    eventually_ge_atTop (5 * ((n + 1 : ℕ) : ℝ) - Real.log (δ * c₀ / 32))]
    with L hend htarget hlength hmasscut
  intro m Ulate τ bmax P U T₀ hP Q hUL hUβ hUτ hτU hτ hzero hsucc hQP hbulk htop
    htotal hPrange hUrange hUT hsize htoplog hbulklog l h hUlog hUlate u hu husep hsmall
    hbig huτ F₀ ac bin hbinlo hbinhi hbinpos w hlen χ hχ center E ρ hE hρ hsE hword hmean
  let r := fun j => (w (some j)).indices.length
  let f := (w none).indices.length
  let R := characterPrimeCells w (characterAnchorCells ac)
  let nc := Fintype.card (Σ v, Fin (characterCellSize r f v))
  have hcounts := character_constructed_counts w
  have hbudgets := character_constructed_mass_budgets w Cmass z hCmass.le hbudgetAll
  have hRmass : ∀ v i, Real.exp (-Cmass * L) ≤ ∑ p ∈ R v i, (p : ℝ)⁻¹ := by
    intro v i
    have hh := constructed_character_cells_mass w ac hc₀ hδ β L hUβ hu hmasscut v i
    exact (Real.exp_le_exp.mpr (by nlinarith only [hβmass, hlength.1.le])).trans hh
  have haRanges := constructed_character_anchor_ranges hP w ac L γs νa hsmall hbig
  have hprod := character_selected_product_intervals w (fun j b => (ac (j, b)).index)
    bin.val hc₀ hδ
  let idx := characterCellIndex (fun j => (w (some j)).indices)
    (fun j b => (ac (j, b)).index) (w none).indices
  let lo := fun v : Σ v, Fin (characterCellSize r f v) => primeCellLower (idx v.1 v.2)
  let hi := fun v : Σ v, Fin (characterCellSize r f v) => primeCellUpper (idx v.1 v.2)
  have haτ (j) : ((ac (j, false)).index : ℝ) + (ac (j, true)).index ≤ 4 * τ :=
    by linarith [(ac (j, false)).upper, (ac (j, true)).upper, huτ j]
  have hT := htarget Ulate τ bin.val m (fun j b => (ac (j, b)).index)
    hUL hUβ hUτ hτU hτ hlength.2.2.2.1 hbinlo hbinhi haτ
  have hnc : nc ≤ Bnb := hcounts.2.2.1.trans (by dsimp [Bnb, N]; omega)
  let EZ := E.image (fun x : ℕ => (x : ℤ))
  have hcard : EZ.card = E.card := Finset.card_image_of_injective _ Int.ofNat_injective
  apply hend nc hnc r f (fun j => hlen (some j)) hcounts.1 hcounts.2.1
    hcounts.2.2.2 hbudgets.2 (Fintype.equivFin _)
    (1000 * (4 : ℝ) ^ (n + 1) * τ) τ bmax P U T₀ hP Q R
    (by positivity) hzero hsucc hQP
    (characterPrimeCells_subset w (characterAnchorCells ac) (fun j => (ac j).cell_subset))
    hbulk htop hRmass htotal hPrange hUrange hUT
    (constructed_character_cells_bulk_disjoint w ac U l h hUlog hUlate husep)
    haRanges.1 haRanges.2 hsize htoplog hbulklog lo hi
    (constructed_character_cells_prime_bounds w ac hP)
    (fun j b => ((ac (j, b)).index : ℝ)) bin hbinpos hT
    (fun v => (Real.exp_le_exp.mpr (sub_le_sub_left hcover _)).trans (hprod v).1)
    (fun v => (hprod v).2.trans (Real.exp_le_exp.mpr (add_le_add_right hcover _)))
    χ hχ center EZ ρ (by rwa [hcard]) hρ
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    simpa only [Int.cast_natCast] using hsE y hy
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    simpa only [Int.cast_natCast] using hword y hy
  · intro x hx v i
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    simpa only [Int.cast_natCast] using hmean y hy v i

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterSelectionScales
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rates for the actual tail count and top-word bin count -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem eventual_character_bin_count (β D : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ τ : ℝ, 1 ≤ τ → Real.log τ ≤ β * L + D →
      (Fintype.card (Fin (⌊4 * τ⌋₊ + 1)) : ℝ) ≤ Real.exp ((β + 1) * L) := by
  filter_upwards [eventually_ge_atTop (D + Real.log 5)] with L hL τ hτ hlog
  have hc := wordLogBin_count τ hτ
  have hpos : (0 : ℝ) < Fintype.card (Fin (⌊4 * τ⌋₊ + 1)) := by simp only [Fintype.card_fin]; positivity
  rw [← Real.exp_log hpos]
  exact Real.exp_le_exp.mpr (by nlinarith only [hc, hlog, hL])

theorem characterEndpointExtension_property (E : Finset ℕ) (x₀ : ℕ) (hx₀ : x₀ ∈ E)
    (G : ℕ → ℕ → ℂ) (A : (ℕ → ℂ) → Prop)
    (h : ∀ x ∈ E, A (G x)) :
    ∀ x, A (characterEndpointExtension E x₀ G x) := by
  intro x
  by_cases hx : x ∈ E
  · have he : characterEndpointExtension E x₀ G x = G x := by
      funext p
      exact ite_eq_left hx
    rw [he]
    exact h x hx
  · have he : characterEndpointExtension E x₀ G x = G x₀ := by
      funext p
      exact ite_eq_right hx
    rw [he]
    exact h x₀ hx₀

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FixedCharacterPriors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Common normalized character priors for exponentially many endpoints -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

/-- Fixing the actual anchor and whole-shell codes leaves a single collection
of harmonic probability laws. Every retained endpoint has a large mean under
these same laws, with the explicit selection cost from the code count. -/
theorem eventual_fixed_character_priors (c δ β C z : ℝ) (k : ℕ)
    (hc : 0 < c) (hδ : 0 < δ) (hC : 0 ≤ C) (hz : 1 ≤ z)
    (hsize : ((characterTargetLabelBound c δ k + (k + 1) + (k + 1) : ℕ) : ℝ) ≤ z) :
    ∀ᶠ L : ℝ in atTop, ∀ (B : ℕ) (m X A U : ℝ),
      (B + 1 : ℕ) ≤ Real.exp (C * L) → z * L ≤ 2 * m → U ≤ β * L →
      ∀ (E : Finset ℕ), E.Nonempty → Real.sqrt X * Real.exp (-A * m) ≤ E.card →
      ∀ (P : Finset ℕ) (G : ℕ → ℕ → ℂ) (ζ : ℂ), ‖ζ‖ = 1 →
      5 * k ≤ B → (∀ p ∈ P, primeLogIndex p ≤ B) →
      ∀ (u : Fin k × Bool → ℝ), (∀ j, u j ≤ β * L) →
      ∀ (a : ∀ x j, CharacterAnchorCell P (fun p => ζ * G x p) c δ (u j)),
      (∀ x ∈ E, ∀ j, (a x j).index ≤ B) →
      ∀ (T : ℕ → Option (Fin k) → ℝ)
        (w : ∀ x j, CharacterTargetWord P (fun p => ζ * G x p) c δ U k (T x j)),
      ∃ x₀ ∈ E, ∃ S : Finset ℕ, S ⊆ E ∧ S.Nonempty ∧
        Real.sqrt X * Real.exp (-(A + 4 * C + 4) * m) ≤ S.card ∧
        let Q := characterPrimeCells (w x₀) (characterAnchorCells (a x₀))
        (∀ v i, Q v i ⊆ P) ∧
        (∀ v i, (∑ p : P, primeSubsetPrior P (Q v i) p) = 1) ∧
        (∀ v i, Real.exp (-(β + 1) * L) ≤ ∑ p ∈ Q v i, (p : ℝ)⁻¹) ∧
        (∀ x ∈ S, ∀ v i, δ / 2 ≤
          ‖∑ p : P, (primeSubsetPrior P (Q v i) p : ℂ) * G x p‖) := by
  filter_upwards [eventual_common_character_selection k (characterTargetLabelBound c δ k)
    C z hC hz hsize,
    eventually_ge_atTop (5 * (k : ℝ) - Real.log (δ * c / 32))] with L hselect hL
  intro B m X A U hB hm hU E hE hEcard P G ζ hζ hk hP u hu a ha T w
  obtain ⟨x₀, hx₀, S, hSE, hS, hScard, hdata⟩ := hselect B m X A hB hm E hE hEcard
    P (fun x p => ζ * G x p) c δ U (fun x j => (a x j).index) T w hc hδ hk hP ha
    (fun x _ => character_target_label_bound (w x))
  refine ⟨x₀, hx₀, S, hSE, hS, hScard, ?_⟩
  dsimp only
  refine ⟨characterPrimeCells_subset (w x₀) (characterAnchorCells (a x₀))
    (fun j => (a x₀ j).cell_subset),
    constructed_character_cells_probability (w x₀) (a x₀) hc hδ,
    constructed_character_cells_mass (w x₀) (a x₀) hc hδ β L hU hu hL, ?_⟩
  intro x hx
  apply constructed_character_cells_endpoint_mean (w x₀) (a x₀) ζ hζ (w x) (a x)
    (hdata x hx).2
  intro j
  exact congrFun (hdata x hx).1 j

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstructedFixedCharacterPriors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed character priors constructed from the tested shells and exact targets -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

/-- All cells below are obtained from the published progression input. No
pivot-word, cell-mean, or normalized-prior hypothesis is supplied here. -/
theorem PublishedProgressionInput.constructed_fixed_character_priors
    (P0 : PublishedProgressionInput) (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (k : ℕ), 20000 ≤ k →
      C₀ ≤ Real.exp ((k : ℝ) / 10000) → ∀ (B z α β C : ℝ),
      0 ≤ B → 1 ≤ z → 0 < α → 0 ≤ C →
      ((characterTargetLabelBound c δ k + (k + 1) + (k + 1) : ℕ) : ℝ) ≤ z →
      ∀ᶠ L : ℝ in atTop, ∀ (U τ J : ℝ) (m D : ℕ),
      α * L ≤ U → U ≤ β * L → U ≤ Real.log τ →
      Real.log τ ≤ U + 2 * (k : ℝ) / 10000 → 0 < τ →
      (m : ℝ) ≤ z * L → z * L ≤ 2 * m → τ / 2 ≤ J → J ≤ 4 * τ →
      (D + 1 : ℕ) ≤ Real.exp (C * L) → 5 * k ≤ D →
      ∀ (P : Finset ℕ) (G : ℕ → ℕ → ℂ) (ζ : ℂ),
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, primeLogIndex p ≤ D) → ‖ζ‖ = 1 →
      (∀ x p, p ∈ P → ‖G x p‖ ≤ 1) →
      (∀ u v : ℝ, U ≤ u → v ≤ U + 5 * k → (k : ℝ) / 10000 ≤ v - u →
        ∃ j : ℕ, u ≤ U + j ∧ U + j + 1 ≤ v ∧
          c ≤ ∑ p ∈ loglogShell P (U + j), (p : ℝ)⁻¹) →
      (∀ (x j : ℕ), j ≤ 5 * k → c ≤ ∑ p ∈ loglogShell P (U + j), (p : ℝ)⁻¹ →
        (∀ p ∈ loglogShell P (U + j),
          Real.log (p : ℝ) ≤ (1000 * (4 : ℝ) ^ k * τ) / 4) →
        δ * (∑ p ∈ loglogShell P (U + j), (p : ℝ)⁻¹) ≤
          ∑ p ∈ loglogShell P (U + j), (p : ℝ)⁻¹ * (ζ * G x p).re) →
      ∀ u : Fin k × Bool → ℝ,
      (∀ j, α * L ≤ u j ∧ u j ≤ β * L) →
      (∀ j : Fin k, 3 * Real.exp (u (j, false)) + 3 * Real.exp (u (j, true)) ≤ 4 * τ) →
      (∀ j, c ≤ ∑ p ∈ loglogShell P (u j), (p : ℝ)⁻¹) →
      (∀ x j, δ * (∑ p ∈ loglogShell P (u j), (p : ℝ)⁻¹) ≤
        ∑ p ∈ loglogShell P (u j), (p : ℝ)⁻¹ * (ζ * G x p).re) →
      ∀ E : Finset ℕ, E.Nonempty → ∀ X A : ℝ,
      Real.sqrt X * Real.exp (-A * m) ≤ E.card →
      ∃ a : ∀ x j, CharacterAnchorCell P (fun p => ζ * G x p) c δ (u j),
      ∃ w : ∀ x j, CharacterTargetWord P (fun p => ζ * G x p) c δ U k
        (characterConstructedTargets k J (1000 * (4 : ℝ) ^ k * τ) B z m
          (fun j => (a x j).index) j),
      (∀ x j, 0 < (w x j).indices.length) ∧
      ∃ x₀ ∈ E, ∃ S : Finset ℕ, S ⊆ E ∧ S.Nonempty ∧
        Real.sqrt X * Real.exp (-(A + 4 * C + 4) * m) ≤ S.card ∧
        let Q := characterPrimeCells (w x₀) (characterAnchorCells (a x₀))
        (∀ v i, Q v i ⊆ P) ∧
        (∀ v i, (∑ p : P, primeSubsetPrior P (Q v i) p) = 1) ∧
        (∀ v i, Real.exp (-(β + 1) * L) ≤ ∑ p ∈ Q v i, (p : ℝ)⁻¹) ∧
        (∀ x ∈ S, ∀ v i, δ / 2 ≤
          ‖∑ p : P, (primeSubsetPrior P (Q v i) p : ℂ) * G x p‖) := by
  obtain ⟨C₀, hC₀, hw⟩ := P0.character_backwards_words c δ hc hδ
  obtain ⟨u₀, hu₀⟩ := eventually_atTop.mp (P0.character_anchor_cell c δ hc hδ)
  refine ⟨C₀, hC₀, ?_⟩
  intro k hk hC₀k B z α β C hB hz hα hC hsize
  have hanchor : ∀ᶠ L : ℝ in atTop, u₀ ≤ α * L :=
    (tendsto_id.const_mul_atTop hα).eventually (eventually_ge_atTop u₀)
  filter_upwards [hw k hk hC₀k B z α hB hz hα, hanchor,
    eventual_fixed_character_priors c δ β C z k hc hδ hC hz hsize] with L hwords hanchor hfixed
  intro U τ J m D hUL hUβ hUτ hτU hτ hm hmlo hJlo hJhi hD hkD P G ζ
    hP hPD hζ hG hrich htest u hu hus hmass hmean E hE X A hEcard
  have hrot (x p : ℕ) (hp : p ∈ P) : ‖ζ * G x p‖ ≤ 1 := by
    rw [norm_mul, hζ, one_mul]
    exact hG x p hp
  have hac : ∀ x j, Nonempty (CharacterAnchorCell P (fun p => ζ * G x p) c δ (u j)) := by
    intro x j
    exact hu₀ (u j) (hanchor.trans (hu j).1) P (fun p => ζ * G x p) hP
      (hrot x) (hmass j) (hmean x j)
  let a : ∀ x j, CharacterAnchorCell P (fun p => ζ * G x p) c δ (u j) :=
    fun x j => Classical.choice (hac x j)
  have hapair (x : ℕ) (j : Fin k) : (a x (j, false)).index + (a x (j, true)).index ≤ (4 * τ : ℝ) :=
    by linarith [(a x (j, false)).upper, (a x (j, true)).upper, hus j]
  let T := fun x => characterConstructedTargets k J (1000 * (4 : ℝ) ^ k * τ) B z m
    (fun j => (a x j).index)
  have hwords' : ∀ x, ∃ w : ∀ j, CharacterTargetWord P (fun p => ζ * G x p) c δ U k (T x j),
      (∀ j, 0 < (w j).indices.length) ∧
      (∑ j : Option (Fin k), (w j).indices.length) ≤ characterTargetLabelBound c δ k := by
    intro x
    exact hwords U τ J m hUL hUτ hτU hτ hm hJlo hJhi
      (fun j b => (a x (j, b)).index) (hapair x) P (fun p => ζ * G x p) hP
      (hrot x) hrich (htest x)
  choose w hlength hcount using hwords'
  refine ⟨a, w, hlength, ?_⟩
  exact hfixed D m X A U hD hmlo hUβ E hE hEcard P G ζ hζ hkD hPD u
    (fun j => (hu j).2) a
    (fun x _ j => (a x j).index_le hc hδ D hPD) T w

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstructedEndpointCharacterPriors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual endpoint tests suffice to construct the fixed character priors -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem PublishedProgressionInput.constructed_endpoint_character_priors
    (P0 : PublishedProgressionInput) (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (k : ℕ), 20000 ≤ k →
      C₀ ≤ Real.exp ((k : ℝ) / 10000) → ∀ (B z α β C : ℝ),
      0 ≤ B → 1 ≤ z → 0 < α → 0 ≤ C →
      ((characterTargetLabelBound c δ k + (k + 1) + (k + 1) : ℕ) : ℝ) ≤ z →
      ∀ᶠ L : ℝ in atTop, ∀ (U τ J : ℝ) (m D : ℕ),
      α * L ≤ U → U ≤ β * L → U ≤ Real.log τ →
      Real.log τ ≤ U + 2 * (k : ℝ) / 10000 → 0 < τ →
      (m : ℝ) ≤ z * L → z * L ≤ 2 * m → τ / 2 ≤ J → J ≤ 4 * τ →
      (D + 1 : ℕ) ≤ Real.exp (C * L) → 5 * k ≤ D →
      ∀ (P : Finset ℕ) (G : ℕ → ℕ → ℂ) (ζ : ℂ),
      ∀ E : Finset ℕ, E.Nonempty →
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, primeLogIndex p ≤ D) → ‖ζ‖ = 1 →
      (∀ x ∈ E, ∀ p ∈ P, ‖G x p‖ ≤ 1) →
      (∀ u v : ℝ, U ≤ u → v ≤ U + 5 * k → (k : ℝ) / 10000 ≤ v - u →
        ∃ j : ℕ, u ≤ U + j ∧ U + j + 1 ≤ v ∧
          c ≤ ∑ p ∈ loglogShell P (U + j), (p : ℝ)⁻¹) →
      (∀ x ∈ E, ∀ j : ℕ, j ≤ 5 * k → c ≤ ∑ p ∈ loglogShell P (U + j), (p : ℝ)⁻¹ →
        (∀ p ∈ loglogShell P (U + j),
          Real.log (p : ℝ) ≤ (1000 * (4 : ℝ) ^ k * τ) / 4) →
        δ * (∑ p ∈ loglogShell P (U + j), (p : ℝ)⁻¹) ≤
          ∑ p ∈ loglogShell P (U + j), (p : ℝ)⁻¹ * (ζ * G x p).re) →
      ∀ u : Fin k × Bool → ℝ,
      (∀ j, α * L ≤ u j ∧ u j ≤ β * L) →
      (∀ j : Fin k, 3 * Real.exp (u (j, false)) + 3 * Real.exp (u (j, true)) ≤ 4 * τ) →
      (∀ j, c ≤ ∑ p ∈ loglogShell P (u j), (p : ℝ)⁻¹) →
      (∀ x ∈ E, ∀ j, δ * (∑ p ∈ loglogShell P (u j), (p : ℝ)⁻¹) ≤
        ∑ p ∈ loglogShell P (u j), (p : ℝ)⁻¹ * (ζ * G x p).re) →
      ∀ X A : ℝ,
      Real.sqrt X * Real.exp (-A * m) ≤ E.card →
      ∃ x₀ ∈ E,
      ∃ a : ∀ j, CharacterAnchorCell P (fun p => ζ * G x₀ p) c δ (u j),
      ∃ w : ∀ j, CharacterTargetWord P (fun p => ζ * G x₀ p) c δ U k
        (characterConstructedTargets k J (1000 * (4 : ℝ) ^ k * τ) B z m
          (fun j => (a j).index) j),
      (∀ j, 0 < (w j).indices.length) ∧
      ∃ S : Finset ℕ, S ⊆ E ∧ S.Nonempty ∧
        Real.sqrt X * Real.exp (-(A + 4 * C + 4) * m) ≤ S.card ∧
        let Q := characterPrimeCells w (characterAnchorCells a)
        (∀ v i, Q v i ⊆ P) ∧
        (∀ v i, (∑ p : P, primeSubsetPrior P (Q v i) p) = 1) ∧
        (∀ v i, Real.exp (-(β + 1) * L) ≤ ∑ p ∈ Q v i, (p : ℝ)⁻¹) ∧
        (∀ x ∈ S, ∀ v i, δ / 2 ≤
          ‖∑ p : P, (primeSubsetPrior P (Q v i) p : ℂ) * G x p‖) := by
  obtain ⟨C₀, hC₀, hconstruct⟩ := P0.constructed_fixed_character_priors c δ hc hδ
  refine ⟨C₀, hC₀, ?_⟩
  intro k hk hC₀k B z α β C hB hz hα hC hsize
  filter_upwards [hconstruct k hk hC₀k B z α β C hB hz hα hC hsize] with L hL
  intro U τ J m D hUL hUβ hUτ hτU hτ hm hmlo hJlo hJhi hD hkD P G ζ E hE
    hP hPD hζ hG hrich htest u hu hus hmass hmean X A hEcard
  obtain ⟨x₁, hx₁⟩ := hE
  let G' := characterEndpointExtension E x₁ G
  have hG' : ∀ x p, p ∈ P → ‖G' x p‖ ≤ 1 := by
    intro x
    exact characterEndpointExtension_property E x₁ hx₁ G
      (fun F => ∀ p ∈ P, ‖F p‖ ≤ 1) hG x
  have ht' : ∀ x j : ℕ, j ≤ 5 * k →
      c ≤ ∑ p ∈ loglogShell P (U + j), (p : ℝ)⁻¹ →
      (∀ p ∈ loglogShell P (U + j),
        Real.log (p : ℝ) ≤ (1000 * (4 : ℝ) ^ k * τ) / 4) →
      δ * (∑ p ∈ loglogShell P (U + j), (p : ℝ)⁻¹) ≤
        ∑ p ∈ loglogShell P (U + j), (p : ℝ)⁻¹ * (ζ * G' x p).re := by
    intro x
    exact characterEndpointExtension_property E x₁ hx₁ G
      (fun F => ∀ j : ℕ, j ≤ 5 * k →
        c ≤ ∑ p ∈ loglogShell P (U + j), (p : ℝ)⁻¹ →
        (∀ p ∈ loglogShell P (U + j),
          Real.log (p : ℝ) ≤ (1000 * (4 : ℝ) ^ k * τ) / 4) →
        δ * (∑ p ∈ loglogShell P (U + j), (p : ℝ)⁻¹) ≤
          ∑ p ∈ loglogShell P (U + j), (p : ℝ)⁻¹ * (ζ * F p).re) htest x
  have hm' : ∀ x j, δ * (∑ p ∈ loglogShell P (u j), (p : ℝ)⁻¹) ≤
      ∑ p ∈ loglogShell P (u j), (p : ℝ)⁻¹ * (ζ * G' x p).re := by
    intro x
    exact characterEndpointExtension_property E x₁ hx₁ G
      (fun F => ∀ j, δ * (∑ p ∈ loglogShell P (u j), (p : ℝ)⁻¹) ≤
        ∑ p ∈ loglogShell P (u j), (p : ℝ)⁻¹ * (ζ * F p).re) hmean x
  obtain ⟨a, w, hlen, x₀, hx₀, S, hSE, hS, hScard, hsub, hprob, hmass', hmeans⟩ :=
    hL U τ J m D hUL hUβ hUτ hτU hτ hm hmlo hJlo hJhi hD hkD P G' ζ
      hP hPD hζ hG' hrich ht' u hu hus hmass hm' E ⟨x₁, hx₁⟩ X A hEcard
  have hG₀ : G' x₀ = G x₀ := by
    funext p
    exact characterEndpointExtension_of_mem E x₁ G hx₀ p
  have hlocal : ∃ a₀ : ∀ j, CharacterAnchorCell P (fun p => ζ * G' x₀ p) c δ (u j),
      ∃ w₀ : ∀ j, CharacterTargetWord P (fun p => ζ * G' x₀ p) c δ U k
        (characterConstructedTargets k J (1000 * (4 : ℝ) ^ k * τ) B z m
          (fun j => (a₀ j).index) j),
      (∀ j, 0 < (w₀ j).indices.length) ∧
      ∃ S : Finset ℕ, S ⊆ E ∧ S.Nonempty ∧
        Real.sqrt X * Real.exp (-(A + 4 * C + 4) * m) ≤ S.card ∧
        let Q := characterPrimeCells w₀ (characterAnchorCells a₀)
        (∀ v i, Q v i ⊆ P) ∧
        (∀ v i, (∑ p : P, primeSubsetPrior P (Q v i) p) = 1) ∧
        (∀ v i, Real.exp (-(β + 1) * L) ≤ ∑ p ∈ Q v i, (p : ℝ)⁻¹) ∧
        (∀ x ∈ S, ∀ v i, δ / 2 ≤
          ‖∑ p : P, (primeSubsetPrior P (Q v i) p : ℂ) * G x p‖) := by
    refine ⟨a x₀, w x₀, hlen x₀, S, hSE, hS, hScard, hsub, hprob, hmass', ?_⟩
    intro x hx v i
    simpa only [G', characterEndpointExtension_of_mem E x₁ G (hSE hx)] using hmeans x hx v i
  have hF₀ : (fun p => ζ * G' x₀ p) = (fun p => ζ * G x₀ p) := by
    rw [hG₀]
  rw [hF₀] at hlocal
  exact ⟨x₀, hx₀, hlocal⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstructedBinnedCharacterPriors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common original word bin and all constructed cell priors -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem PublishedProgressionInput.constructed_binned_character_priors
    (P0 : PublishedProgressionInput) (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (k : ℕ), 20000 ≤ k →
      C₀ ≤ Real.exp ((k : ℝ) / 10000) → ∀ (B z α β C : ℝ),
      0 ≤ B → 1 ≤ z → 0 < α → 0 ≤ β → 0 ≤ C →
      ((characterTargetLabelBound c δ k + (k + 1) + (k + 1) : ℕ) : ℝ) ≤ z →
      ∀ᶠ L : ℝ in atTop, ∀ (U τ : ℝ) (m D : ℕ),
      α * L ≤ U → U ≤ β * L → U ≤ Real.log τ →
      Real.log τ ≤ U + 2 * (k : ℝ) / 10000 → 0 < τ → 2 ≤ τ →
      (m : ℝ) ≤ z * L → z * L ≤ 2 * m → 1 ≤ m → L ≤ m →
      (D + 1 : ℕ) ≤ Real.exp (C * L) → 5 * k ≤ D →
      ∀ (P : Finset ℕ) (G : ℕ → ℕ → ℂ) (ζ : ℂ),
      ∀ E : Finset ℕ, E.Nonempty →
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, primeLogIndex p ≤ D) → ‖ζ‖ = 1 →
      (∀ x ∈ E, ∀ p ∈ P, ‖G x p‖ ≤ 1) →
      (∀ u v : ℝ, U ≤ u → v ≤ U + 5 * k → (k : ℝ) / 10000 ≤ v - u →
        ∃ j : ℕ, u ≤ U + j ∧ U + j + 1 ≤ v ∧
          c ≤ ∑ p ∈ loglogShell P (U + j), (p : ℝ)⁻¹) →
      (∀ x ∈ E, ∀ j : ℕ, j ≤ 5 * k → c ≤ ∑ p ∈ loglogShell P (U + j), (p : ℝ)⁻¹ →
        (∀ p ∈ loglogShell P (U + j),
          Real.log (p : ℝ) ≤ (1000 * (4 : ℝ) ^ k * τ) / 4) →
        δ * (∑ p ∈ loglogShell P (U + j), (p : ℝ)⁻¹) ≤
          ∑ p ∈ loglogShell P (U + j), (p : ℝ)⁻¹ * (ζ * G x p).re) →
      ∀ (bmax : ℝ) (Ubulk T₀ : Finset ℕ) (Qword : Fin (m + 1) → Finset ℕ),
      Qword 0 = T₀ → (∀ i : Fin m, Qword i.succ = Ubulk) →
      (m : ℝ) * bmax ≤ τ →
      (∀ p ∈ T₀, τ ≤ Real.log (p : ℝ) ∧ Real.log (p : ℝ) ≤ 3 * τ) →
      (∀ p ∈ Ubulk, Real.log (p : ℝ) ≤ bmax) →
      (∀ x ∈ E, ∀ i, δ ≤
        ‖∑ p : P, (primeSubsetPrior P (Qword i) p : ℂ) * G x p‖) →
      ∀ u : Fin k × Bool → ℝ,
      (∀ j, α * L ≤ u j ∧ u j ≤ β * L) →
      (∀ j : Fin k, 3 * Real.exp (u (j, false)) + 3 * Real.exp (u (j, true)) ≤ 4 * τ) →
      (∀ j, c ≤ ∑ p ∈ loglogShell P (u j), (p : ℝ)⁻¹) →
      (∀ x ∈ E, ∀ j, δ * (∑ p ∈ loglogShell P (u j), (p : ℝ)⁻¹) ≤
        ∑ p ∈ loglogShell P (u j), (p : ℝ)⁻¹ * (ζ * G x p).re) →
      ∀ X A : ℝ, 0 < X →
      Real.sqrt X * Real.exp (-A * m) ≤ E.card →
      ∃ bin : Fin (⌊4 * τ⌋₊ + 1), τ / 2 ≤ (bin.val : ℝ) ∧
      (bin.val : ℝ) ≤ 4 * τ ∧ 0 < bin.val ∧
      let J : ℝ := bin.val
      ∃ x₀ ∈ E,
      ∃ a : ∀ j, CharacterAnchorCell P (fun p => ζ * G x₀ p) c δ (u j),
      ∃ w : ∀ j, CharacterTargetWord P (fun p => ζ * G x₀ p) c δ U k
        (characterConstructedTargets k J (1000 * (4 : ℝ) ^ k * τ) B z m
          (fun j => (a j).index) j),
      (∀ j, 0 < (w j).indices.length) ∧
      ∃ S : Finset ℕ, S ⊆ E ∧ S.Nonempty ∧
        Real.sqrt X * Real.exp (-(A + (β + 1) + 4 * C + 4) * m) ≤ S.card ∧
        let Q := characterPrimeCells w (characterAnchorCells a)
        (∀ v i, Q v i ⊆ P) ∧
        (∀ v i, (∑ p : P, primeSubsetPrior P (Q v i) p) = 1) ∧
        (∀ v i, Real.exp (-(β + 1) * L) ≤ ∑ p ∈ Q v i, (p : ℝ)⁻¹) ∧
        (∀ x ∈ S, ∀ v i, δ / 2 ≤
          ‖∑ p : P, (primeSubsetPrior P (Q v i) p : ℂ) * G x p‖) ∧
        (∀ x ∈ S, Real.exp (-((β + 1) - 2 * Real.log δ) * m) ≤
          ‖binnedWordAverage (fun i => primeSubsetPrior P (Qword i))
            (fun _ p => G x p)
            (fun w => wordLogBin τ (fun i => Real.log (w i : ℝ))) bin‖) := by
  obtain ⟨C₀, hC₀, hconstruct⟩ := P0.constructed_endpoint_character_priors c δ hc hδ
  refine ⟨C₀, hC₀, ?_⟩
  intro k hk hC₀k B z α β C hB hz hα hβ hC hsize
  filter_upwards [hconstruct k hk hC₀k B z α β C hB hz hα hC hsize,
    eventual_character_bin_count β (2 * (k : ℝ) / 10000)] with L hL hbinCount
  intro U τ m D hUL hUβ hUτ hτU hτ hτ2 hm hmlo hm1 hLm hD hkD P G ζ E hE
    hP hPD hζ hG hrich htest bmax Ubulk T₀ Qword hzero hsucc hbulksize htoplog hbulklog
    hwordMean u hu hus hmass hmean X A hX hEcard
  have hbins := hbinCount τ (by linarith only [hτ2]) (by linarith only [hUβ, hτU])
  obtain ⟨bin, hbinlo, hbinhi, hbinpos, E₁, hE₁E, hE₁, hE₁card, hword⟩ :=
    character_select_supported_bin m L X A (β + 1) δ bmax τ hm1 hLm hX
      (by linarith) hδ hδ1 hτ2 P Ubulk T₀ Qword hP hzero hsucc hbulksize htoplog hbulklog
      E hEcard (fun x _ p => G x p) hbins hwordMean
  obtain ⟨x₀, hx₀, ac, w, hlen, S, hSE₁, hS, hScard, hsub, hprob, hmass', hmeans⟩ :=
    hL U τ bin.val m D hUL hUβ hUτ hτU hτ hm hmlo hbinlo hbinhi hD hkD P G ζ E₁ hE₁
      hP hPD hζ (fun x hx => hG x (hE₁E hx)) hrich
      (fun x hx => htest x (hE₁E hx)) u hu hus hmass
      (fun x hx => hmean x (hE₁E hx)) X (A + (β + 1)) hE₁card
  refine ⟨bin, hbinlo, hbinhi, hbinpos, x₀, hE₁E hx₀, ac, w, hlen,
    S, hSE₁.trans hE₁E, hS, ?_, hsub, hprob, hmass', hmeans, ?_⟩
  · simpa only [add_assoc] using hScard
  · intro x hx
    exact hword x (hSE₁ hx)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterTestedShellContradiction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Tested original shells force the finite character contradiction -/
namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap FourierTransform ComplexConjugate

theorem PublishedProgressionInput.eventual_tested_character_shell_contradiction_oai
    (P0 : PublishedProgressionInput) (c₀ δ : ℝ) (hc₀ : 0 < c₀) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ n : ℕ, 20000 ≤ n + 1 →
      C₀ ≤ Real.exp (((n + 1 : ℕ) : ℝ) / 10000) →
    ∀
    (a b z Cmass Ctotal Aend Bword B B₁ c s γ H α K βg βw γs βa γw νw νa ε β Ccode A : ℝ)
    (_ha : 0 < a) (_hb : 0 < b) (_hz : 1 < z)
    (_hCmass : 0 < Cmass) (_hCtotal : 0 ≤ Ctotal) (_hc : 1 ≤ c)
    (_hs : 0 < s) (_hγ : 0 < γ) (_hH : 0 ≤ H) (_hα : 0 < α)
    (_hgapInitial : 2 * ((2 * Real.log (3 / a) + 3 + 2 * Ctotal) +
      (Aend + 2 * Bword + 1) + 2) ≤ B) (_hB : 0 ≤ B)
    (_hB₁ : 0 ≤ B₁) (_hB₁eq : B₁ = Aend + 2 * Bword + 3)
    (_hBstrong : 2 * B₁ + 5 ≤ B) (_hBpos : 1 ≤ B) (_ha1 : a ≤ 1)
    (_hβg : 0 < βg) (_hγw : 0 ≤ γw) (_hαw : α < βw) (_hsw : γs < βw)
    (_hαa : α < βa) (_hwa : γw < βa) (_hwg : γw ≤ βg)
    (_hβw : βw < νw) (_hβa : βa < νa) (_hε : 0 < ε)
    (_hbudgetAll : 4 * Cmass *
      (characterTargetLabelBound c₀ δ (n + 1) + (n + 2) + (n + 2) : ℕ) ≤ z)
    (_hgapFinal : 2 * B₁ +
      ((γw + Real.log ((Real.log 2)⁻¹ + 1)) / a + max (Real.log 3) 0 + ε) +
      Real.log 2 + 6 ≤ B + 20 * Real.log a)
    (_hentropy : (βg + Real.log ((Real.log 2)⁻¹ + 1) + max (Real.log 3) 0 + ε) +
      (B + 20 * Real.log z + 1) + 2 * B₁ + 1 ≤ (n : ℝ) * Real.log 2 - 1)
    (_hβ : 0 ≤ β) (_hβgap : β < βg)
    (_hβmass : β + 1 ≤ Cmass)
    (_hcover : characterCellCoveringError c₀ δ (n + 1) ≤ c)
    (_hCcode : 0 ≤ Ccode) (_hArate : A + (β + 1) + 4 * Ccode + 4 ≤ Aend)
    (_hBrate : (β + 1) - 2 * Real.log δ ≤ Bword) (_hγδ : γ ≤ δ / 2)
    (ψ : 𝓢(ℝ, ℂ)) (_hψ : ∀ x, 0 ≤ (ψ x).re) (_hreal : ∀ x, (ψ x).im = 0)
    (_heven : ∀ v : ℝ, 𝓕 ψ (-v) = 𝓕 ψ v)
    (_hψK : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K)
    (_hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0),
    ∀ᶠ L : ℝ in atTop,
    let m := ⌊z * L⌋₊
    ∀ (Ulate τ bmax : ℝ) (P U T₀ : Finset ℕ) (_hP : ∀ p ∈ P, p.Prime)
      (Q : Fin (m + 1) → Finset ℕ) (D : ℕ),
    α * L ≤ Ulate → Ulate ≤ β * L → Ulate ≤ Real.log τ →
    Real.log τ ≤ Ulate + 2 * ((n + 1 : ℕ) : ℝ) / 10000 → 0 < τ → 2 ≤ τ →
    Q 0 = T₀ → (∀ i : Fin m, Q i.succ = U) → (∀ i, Q i ⊆ P) →
    a * L ≤ ∑ p ∈ U, (p : ℝ)⁻¹ → b ≤ ∑ p ∈ T₀, (p : ℝ)⁻¹ →
    (∑ p : P, (p : ℝ)⁻¹) ≤ Ctotal * L →
    (∀ p ∈ P, Real.exp (Real.exp (α * L)) ≤ p ∧
      (p : ℝ) ≤ Real.exp (Real.exp (βg * L))) →
    (∀ p ∈ U, Real.exp (Real.exp (νw * L)) ≤ p ∧
      (p : ℝ) ≤ Real.exp (Real.exp (γw * L))) →
    Disjoint U T₀ → (m : ℝ) * bmax ≤ τ →
    (∀ p ∈ T₀, τ ≤ Real.log (p : ℝ) ∧ Real.log (p : ℝ) ≤ 3 * τ) →
    (∀ p ∈ U, Real.log (p : ℝ) ≤ bmax) →
    ∀ (l h : ℝ),
    (∀ p ∈ U, l < Real.log (Real.log (p : ℝ)) ∧ Real.log (Real.log (p : ℝ)) ≤ h) →
    h ≤ Ulate →
    (D + 1 : ℕ) ≤ Real.exp (Ccode * L) → 5 * (n + 1) ≤ D →
    (∀ p ∈ P, primeLogIndex p ≤ D) →
    (∀ u v : ℝ, Ulate ≤ u → v ≤ Ulate + 5 * (n + 1) →
      ((n + 1 : ℕ) : ℝ) / 10000 ≤ v - u →
      ∃ j : ℕ, u ≤ Ulate + j ∧ Ulate + j + 1 ≤ v ∧
        c₀ ≤ ∑ p ∈ loglogShell P (Ulate + j), (p : ℝ)⁻¹) →
    ∀ u : Fin (n + 1) × Bool → ℝ,
    (∀ j, α * L ≤ u j ∧ u j ≤ β * L) → (∀ j, u j + 1 ≤ l ∨ h ≤ u j) →
    (∀ j, u (j, false) + 1 ≤ γs * L) → (∀ j, νa * L ≤ u (j, true)) →
    (∀ j, 3 * Real.exp (u (j, false)) + 3 * Real.exp (u (j, true)) ≤ 4 * τ) →
    (∀ j, c₀ ≤ ∑ p ∈ loglogShell P (u j), (p : ℝ)⁻¹) →
    ∀ (χ : ∀ p : ℕ, DirichletCharacter ℂ p), (∀ p ∈ P, χ p ^ 2 ≠ 1) →
    ∀ (center : ∀ p : ℕ, ZMod p) (ζ : ℂ), ‖ζ‖ = 1 →
    ∀ E : Finset ℕ,
    Real.sqrt (Real.exp (1000 * (4 : ℝ) ^ (n + 1) * τ)) *
      Real.exp (-A * m) ≤ E.card →
    (∀ x ∈ E, s ≤ (ψ ((x : ℝ) / Real.exp (1000 * (4 : ℝ) ^ (n + 1) * τ))).re) →
    (∀ x ∈ E, ∀ i, δ ≤ ‖∑ p : P, (primeSubsetPrior P (Q i) p : ℂ) *
      χ p ((x : ZMod p) - center p)‖) →
    (∀ x ∈ E, ∀ j : ℕ, j ≤ 5 * (n + 1) →
      c₀ ≤ ∑ p ∈ loglogShell P (Ulate + j), (p : ℝ)⁻¹ →
      (∀ p ∈ loglogShell P (Ulate + j),
        Real.log (p : ℝ) ≤ (1000 * (4 : ℝ) ^ (n + 1) * τ) / 4) →
      δ * (∑ p ∈ loglogShell P (Ulate + j), (p : ℝ)⁻¹) ≤
        ∑ p ∈ loglogShell P (Ulate + j), (p : ℝ)⁻¹ *
          (ζ * χ p ((x : ZMod p) - center p)).re) →
    (∀ x ∈ E, ∀ j, δ * (∑ p ∈ loglogShell P (u j), (p : ℝ)⁻¹) ≤
      ∑ p ∈ loglogShell P (u j), (p : ℝ)⁻¹ * (ζ * χ p ((x : ZMod p) - center p)).re) →
    False := by
  obtain ⟨C₀, hC₀, hconstruct⟩ := P0.constructed_binned_character_priors c₀ δ hc₀ hδ hδ1
  refine ⟨C₀, hC₀, ?_⟩
  intro n hn hC₀n a b z Cmass Ctotal Aend Bword B B₁ c s γ H α K βg βw γs βa γw νw νa ε
    β Ccode A ha hb hz hCmass hCtotal hc hs hγ hH hα hgapInitial hB hB₁ hB₁eq hBstrong
    hBpos ha1 hβg hγw hαw hsw hαa hwa hwg hβw hβa hε hbudgetAll hgapFinal hentropy
    hβ hβgap hβmass hcover hCcode hArate hBrate hγδ ψ hψ hreal heven hψK hsupp
  have hsize : ((characterTargetLabelBound c₀ δ (n + 1) + (n + 2) + (n + 2) : ℕ) : ℝ) ≤ z := by
    have hnonneg := Nat.cast_nonneg (α := ℝ)
      (characterTargetLabelBound c₀ δ (n + 1) + (n + 2) + (n + 2))
    have hmul := mul_nonneg (show 0 ≤ 4 * Cmass - 1 by linarith only [hβmass, hβ]) hnonneg
    nlinarith only [hmul, hbudgetAll]
  have hchoose := hconstruct (n + 1) hn hC₀n B z α β Ccode hB hz.le hα hβ hCcode hsize
  have hfalse := eventual_constructed_character_endpoint_contradiction n
    a b z Cmass Ctotal Aend Bword B B₁ c s γ H α K βg βw γs βa γw νw νa ε c₀ δ β
    ha hb hz hCmass hCtotal hc hs hγ hH hα hgapInitial hB hB₁ hB₁eq hBstrong hBpos ha1
    hβg hγw hαw hsw hαa hwa hwg hβw hβa hε hbudgetAll hgapFinal hentropy
    hc₀ hδ hβ hβgap hβmass hcover ψ hψ hreal heven hψK hsupp
  filter_upwards [hchoose, hfalse, eventual_character_length_bounds z hz] with L hchoose hfalse hlength
  intro m Ulate τ bmax P U T₀ hP Q D hUL hUβ hUτ hτU hτ hτ2 hzero hsucc hQP hbulk htop
    htotal hPrange hUrange hUT hsizeτ htoplog hbulklog l h hUlog hUlate hD hkD hPD hrich
    u hu husep hsmall hbig huτ hmass χ hχ center ζ hζ E hE hsE hwordMean htest hmean
  have hEne : E.Nonempty := by
    apply Finset.card_pos.mp
    have hp : (0 : ℝ) < E.card :=
      (mul_pos (Real.sqrt_pos.2 (Real.exp_pos _)) (Real.exp_pos _)).trans_le hE
    exact_mod_cast hp
  obtain ⟨bin, hbinlo, hbinhi, hbinpos, x₀, hx₀, ac, w, hlen, S, hSE, hSne,
    hScard, hsub, hprob, hmass', hmeans, hword⟩ :=
    hchoose Ulate τ m D hUL hUβ hUτ hτU hτ hτ2 hlength.2.2.2.1 hlength.2.2.2.2
      hlength.2.1 hlength.2.2.1 hD hkD P
      (fun x p => χ p ((x : ZMod p) - center p)) ζ E hEne hP hPD hζ
      (fun _ _ p _ => (χ p).norm_le_one _)
      (by simpa only [Nat.cast_add, Nat.cast_one] using hrich) htest bmax U T₀ Q hzero hsucc hsizeτ
      htoplog hbulklog hwordMean u hu huτ hmass hmean
      (Real.exp (1000 * (4 : ℝ) ^ (n + 1) * τ)) A (Real.exp_pos _) hE
  apply hfalse Ulate τ bmax P U T₀ hP Q hUL hUβ hUτ hτU hτ hzero hsucc hQP hbulk htop
    htotal hPrange hUrange hUT hsizeτ htoplog hbulklog l h hUlog hUlate u
    (fun j => (hu j).2) husep hsmall hbig huτ
    (fun p => ζ * χ p ((x₀ : ZMod p) - center p)) ac bin hbinlo hbinhi hbinpos w hlen
    χ hχ center S (Real.exp (-Bword * m))
  · exact (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by nlinarith only [hArate, Nat.cast_nonneg (α := ℝ) m]))
      (Real.sqrt_nonneg _)).trans hScard
  · exact le_rfl
  · exact fun x hx => hsE x (hSE hx)
  · intro x hx
    exact (Real.exp_le_exp.mpr (by nlinarith only [hBrate, Nat.cast_nonneg (α := ℝ) m])).trans
      (hword x hx)
  · intro x hx v i
    exact hγδ.trans (hmeans x hx v i)

end Ostmann

end OAI
end

theorem solution : type_of% @OAI.Ostmann.PublishedProgressionInput.eventual_tested_character_shell_contradiction_oai := @OAI.Ostmann.PublishedProgressionInput.eventual_tested_character_shell_contradiction_oai
