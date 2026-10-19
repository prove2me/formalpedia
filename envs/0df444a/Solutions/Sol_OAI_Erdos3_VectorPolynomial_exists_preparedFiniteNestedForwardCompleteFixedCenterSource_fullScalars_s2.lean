-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.exists_preparedFiniteNestedForwardCompleteFixedCenterSource_fullScalars_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T09:38:55.832382+00:00
-- url     : https://prove2.me/submissions/15b45ca6-113a-4221-a10e-840f1b0f6f44

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B296
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_preparedFiniteNestedForwardProductiveFixedCenterSource_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.StrideSelectedResidueBadProduct
namespace OAI

section

namespace Erdos3

theorem quantitativeBadPrimeRadius_error {E : ℝ} (hE : 0 ≤ E) (Q : ℕ) (hQ : 1 ≤ Q) :
    let R := quantitativeBadPrimeRadius E
    0 < Real.exp (-E) / (2 * ((Q : ℝ) + (R : ℝ) ^ 2)) ∧
    2 / (9 * (R : ℝ) ^ 9) + ((Q : ℝ) + (R : ℝ) ^ 2) *
      (Real.exp (-E) / (2 * ((Q : ℝ) + (R : ℝ) ^ 2))) ≤ Real.exp (-E) := by
  dsimp only
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hden : 0 < (Q : ℝ) + (quantitativeBadPrimeRadius E : ℝ) ^ 2 := by positivity
  refine ⟨by positivity, ?_⟩
  have heq : ((Q : ℝ) + (quantitativeBadPrimeRadius E : ℝ) ^ 2) *
      (Real.exp (-E) / (2 * ((Q : ℝ) + (quantitativeBadPrimeRadius E : ℝ) ^ 2))) =
      Real.exp (-E) / 2 := by field_simp
  rw [heq]
  linarith [(quantitativeBadPrimeRadius_bounds hE).2.2]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PhysicalBadProductErrorBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem physicalBadProductAccuracy_pos (E Vlog : ℝ) :
    0 < physicalBadProductAccuracy E Vlog := Real.exp_pos _

theorem physicalBadProductAccuracy_inv (E Vlog : ℝ) :
    (physicalBadProductAccuracy E Vlog)⁻¹ = Real.exp (Vlog + 3 * E + 16) := by
  unfold physicalBadProductAccuracy
  rw [Real.exp_neg, inv_inv]

private theorem exp_eight_ge : (128 : ℝ) ≤ Real.exp 8 := by
  have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h1 8
  have he : Real.exp (8 : ℝ) = Real.exp 1 ^ 8 := by
    simp
  rw [he]
  norm_num at hpow ⊢
  linarith

theorem physicalBadProductAccuracy_budget {E Vlog : ℝ}
    (hE : 0 ≤ E) (hVlog : 0 ≤ Vlog) (Q : ℕ) (hQ : 1 ≤ Q)
    (hQexp : (Q : ℝ) ≤ Real.exp Vlog) :
    let κ := physicalBadProductAccuracy E Vlog
    let R := quantitativeBadPrimeRadius E
    let η := Real.exp (-E) / (2 * ((Q : ℝ) + (R : ℝ) ^ 2))
    0 < κ ∧ κ⁻¹ = Real.exp (Vlog + 3 * E + 16) ∧
      2 * κ + κ ≤ 1 / 2 ∧ 128 * κ ≤ η ∧
      12 * (2 * κ + κ) + κ ≤ η := by
  dsimp only
  let T := Vlog + 3 * E + 8
  let η := Real.exp (-E) / (2 * ((Q : ℝ) + (quantitativeBadPrimeRadius E : ℝ) ^ 2))
  have hη : 0 < η := (quantitativeBadPrimeRadius_error hE Q hQ).1
  have hi : 1 / η ≤ Real.exp T :=
    (quantitativeBadPrimeRadius_witness_budget hE hVlog Q hQexp).2
  have hlo : Real.exp (-T) ≤ η := by
    rw [Real.exp_neg, ← one_div]
    apply (div_le_iff₀ (Real.exp_pos T)).mpr
    have hh := (div_le_iff₀ hη).mp hi
    simpa only [mul_comm] using hh
  have heq : physicalBadProductAccuracy E Vlog = Real.exp (-T) / Real.exp 8 := by
    rw [physicalBadProductAccuracy, ← Real.exp_sub]
    congr 1
    dsimp [T]
    ring
  have h128 : 128 * physicalBadProductAccuracy E Vlog ≤ η := by
    rw [heq]
    apply le_trans _ hlo
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (Real.exp_pos 8)).mpr
    have h := mul_le_mul_of_nonneg_left exp_eight_ge (Real.exp_pos (-T)).le
    nlinarith
  have hκ := physicalBadProductAccuracy_pos E Vlog
  have hκsmall : physicalBadProductAccuracy E Vlog ≤ 1 / 128 := by
    have hT : 0 ≤ T := by dsimp [T]; linarith
    have hl : Real.exp (-T) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hT)
    have hh : physicalBadProductAccuracy E Vlog * Real.exp 8 = Real.exp (-T) := by
      rw [heq, div_mul_cancel₀ _ (Real.exp_pos 8).ne']
    have h := mul_le_mul_of_nonneg_left exp_eight_ge hκ.le
    nlinarith
  refine ⟨hκ, physicalBadProductAccuracy_inv E Vlog, ?_, h128, ?_⟩
  · linarith
  · linarith

theorem physicalBadProductGap_budget (N : ℕ) {E Vlog : ℝ}
    (hE : 0 ≤ E) (hVlog : 0 ≤ Vlog) (Q : ℕ) (hQ : 1 ≤ Q)
    (hQexp : (Q : ℝ) ≤ Real.exp Vlog) :
    1 ≤ physicalBadProductGap N E Vlog Q ∧
    (max Q ((quantitativeBadPrimeRadius E) ^ 2) : ℕ) ≤ physicalBadProductGap N E Vlog Q ∧
    2 * (N : ℝ) * (max Q ((quantitativeBadPrimeRadius E) ^ 2) : ℕ) /
      physicalBadProductAccuracy E Vlog ≤ physicalBadProductGap N E Vlog Q := by
  have hb := physicalBadProductAccuracy_budget hE hVlog Q hQ hQexp
  have hκ := hb.1
  have hκ1 : physicalBadProductAccuracy E Vlog ≤ 1 := by linarith [hb.2.2.1]
  have hc : (1 : ℝ) ≤ (max Q ((quantitativeBadPrimeRadius E) ^ 2) : ℕ) := by
    exact_mod_cast hQ.trans (le_max_left _ _)
  have hW : (max Q ((quantitativeBadPrimeRadius E) ^ 2) : ℕ) ≤ physicalBadProductGap N E Vlog Q := by
    unfold physicalBadProductGap
    apply (le_div_iff₀ hκ).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  refine ⟨hc.trans hW, hW, ?_⟩
  unfold physicalBadProductGap
  exact div_le_div_of_nonneg_right (by nlinarith) hκ.le

theorem physicalBadProductGap_exp_bound (N : ℕ) {E Vlog F : ℝ}
    (hE : 0 ≤ E) (hVlog : 0 ≤ Vlog) (hF : 0 ≤ F) (Q : ℕ)
    (hQexp : (Q : ℝ) ≤ Real.exp Vlog) (hN : (N : ℝ) ≤ Real.exp F) :
    physicalBadProductGap N E Vlog Q ≤ Real.exp (F + 2 * Vlog + 5 * E + 24) := by
  have hcap := (quantitativeBadPrimeRadius_witness_budget hE hVlog Q hQexp).1
  have he2 : (3 : ℝ) ≤ Real.exp 2 := by
    have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have hh := mul_le_mul he1 he1 (by norm_num : (0 : ℝ) ≤ 2) (Real.exp_pos 1).le
    have hid : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    rw [hid]
    nlinarith
  have hn : 2 * (N : ℝ) + 1 ≤ Real.exp (F + 2) := by
    rw [Real.exp_add]
    have hf := Real.one_le_exp hF
    have hh := mul_le_mul_of_nonneg_left he2 (Real.exp_pos F).le
    nlinarith
  unfold physicalBadProductGap
  rw [div_eq_mul_inv, physicalBadProductAccuracy_inv]
  calc
    _ ≤ Real.exp (F + 2) * Real.exp (Vlog + 2 * E + 6) * Real.exp (Vlog + 3 * E + 16) := by
      gcongr
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankPreparationProjectedAxisBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators
open VectorPolynomial

namespace RankPreparationFamily

variable {I J : Type} {m q : ℕ}

theorem pad_coordinate_card_le (L : RankPreparationFamily I J m) {M : ℕ}
    (hL : ∀ j, Fintype.card (L j).Coord ≤ M) :
    ∀ j, Fintype.card (L.pad q j).Coord ≤ M := by
  intro j
  by_cases hj : j.val < m
  · simpa only [pad_apply_lt L j hj] using hL ⟨j.val, hj⟩
  · rw [pad_apply_ge L j (by omega)]
    change Fintype.card PEmpty ≤ M
    simp

end RankPreparationFamily
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastPreparedScaleBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

theorem enlargedPreparedCommonSamplerDimension_allocation (m M Jalloc : ℕ) :
    Jalloc ≤ enlargedPreparedCommonSamplerDimension m M Jalloc := by
  unfold enlargedPreparedCommonSamplerDimension
  omega

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedBadProductInputBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open BooleanCubeKernel
open scoped BigOperators Classical

theorem boundedCoefficientExponent_card_le_common_dimension
    {K : Type*} [Fintype K] (m pnum : ℕ) (hK : Fintype.card K ≤ pnum)
    {h : ℕ} (hh : h ≤ m) :
    Fintype.card (BoundedCoefficientExponent K h) ≤ (m + 1) * (pnum + 1) ^ m := by
  apply (boundedCoefficientExponent_card_le h).trans
  apply Nat.mul_le_mul (Nat.add_le_add_right hh 1)
  exact (Nat.pow_le_pow_left (Nat.add_le_add_right hK 1) h).trans
    (Nat.pow_le_pow_right (Nat.succ_pos pnum) hh)

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)

theorem preparedBadProduct_input_counts
    (Jalloc nX : ℕ) {M : ℕ} (hM : ∀ j, Fintype.card (L j).Coord ≤ M) :
    let pnum := enlargedPreparedCommonSamplerDimension m M Jalloc
    let G := EnlargedPreparedCommonKernel m Jalloc
    let I := PreparedSamplerContinuous L
    let n := preparedSamplerTransverse L
    let B := EnlargedPreparedCommonSamplerBlock L Jalloc
    let vars := LayerSamplerVariables G I n B
    m ≤ pnum ∧ M ≤ pnum ∧ Jalloc ≤ pnum ∧ Fintype.card G ≤ pnum ∧
      Fintype.card vars ≤ pnum ∧
      (∀ j, Fintype.card (I j) ≤ pnum) ∧ (∀ j, n j ≤ pnum) ∧
      (∀ j, Fintype.card (L j).Coord ≤ pnum) ∧
      (∀ j : Fin m, Fintype.card (BoundedCoefficientExponent vars (j.val + 1)) ≤
        (m + 1) * (pnum + 1) ^ m) ∧
      Fintype.card (Option vars × Fin nX) ≤ (pnum + 1) * nX := by
  intro pnum G I n B vars
  obtain ⟨hvars, hI, hn⟩ := enlargedPreparedCommonSampler_dimensions L Jalloc hM
  have hpM := enlargedPreparedCommonSamplerDimension_ge m M Jalloc
  have halloc := enlargedPreparedCommonSamplerDimension_allocation m M Jalloc
  have hm : m ≤ pnum := by unfold pnum enlargedPreparedCommonSamplerDimension; omega
  have hG : Fintype.card G ≤ pnum := by
    simp only [G, EnlargedPreparedCommonKernel, Fintype.card_fin]
    unfold pnum enlargedPreparedCommonSamplerDimension
    omega
  refine ⟨hm, hpM, halloc, hG, hvars, hI, hn, fun j => (hM j).trans hpM, ?_, ?_⟩
  · intro j
    exact boundedCoefficientExponent_card_le_common_dimension m pnum hvars (Nat.succ_le_of_lt j.isLt)
  · simp only [Fintype.card_prod, Fintype.card_option, Fintype.card_fin]
    exact Nat.mul_le_mul_right nX (Nat.add_le_add_right hvars 1)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteForwardFixedCenterThreshold
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

variable {Slot : Type*} [Fintype Slot]
variable (A : ℕ) (constants : ℕ → ℕ) (innerDepth outerDepth cutoff : ℕ)
variable (x anchorGoodRequired conditionalRequired : ℝ) (detectorRequired : Slot → ℝ)

theorem anchorGoodRequired_le_preparedFiniteNestedSourceRequired :
    anchorGoodRequired ≤ preparedFiniteNestedSourceRequired A constants innerDepth outerDepth cutoff
      x anchorGoodRequired conditionalRequired detectorRequired := by
  unfold preparedFiniteNestedSourceRequired
  have hdet : 0 ≤ ∑ slot, max 0 (detectorRequired slot) :=
    Finset.sum_nonneg (fun _ _ => le_max_left _ _)
  have hcum : 0 ≤ ∑ outer : Fin (outerDepth + 1), ∑ degree : Fin (cutoff + 1),
      max 0 (preparedFiniteForwardCumulative A constants degree.val
        (candidateNestedForwardSeed A constants innerDepth outer.val x)) :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => le_max_left _ _))
  linarith [le_max_right (0 : ℝ) anchorGoodRequired,
    le_max_left (0 : ℝ) conditionalRequired]

theorem conditionalRequired_le_preparedFiniteNestedSourceRequired :
    conditionalRequired ≤ preparedFiniteNestedSourceRequired A constants innerDepth outerDepth cutoff
      x anchorGoodRequired conditionalRequired detectorRequired := by
  unfold preparedFiniteNestedSourceRequired
  have hdet : 0 ≤ ∑ slot, max 0 (detectorRequired slot) :=
    Finset.sum_nonneg (fun _ _ => le_max_left _ _)
  have hcum : 0 ≤ ∑ outer : Fin (outerDepth + 1), ∑ degree : Fin (cutoff + 1),
      max 0 (preparedFiniteForwardCumulative A constants degree.val
        (candidateNestedForwardSeed A constants innerDepth outer.val x)) :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => le_max_left _ _))
  linarith [le_max_left (0 : ℝ) anchorGoodRequired,
    le_max_right (0 : ℝ) conditionalRequired]

theorem detectorRequired_le_preparedFiniteNestedSourceRequired (slot : Slot) :
    detectorRequired slot ≤ preparedFiniteNestedSourceRequired A constants innerDepth outerDepth cutoff
      x anchorGoodRequired conditionalRequired detectorRequired := by
  unfold preparedFiniteNestedSourceRequired
  have hdet : max 0 (detectorRequired slot) ≤ ∑ slot, max 0 (detectorRequired slot) :=
    Finset.single_le_sum (fun _ _ => le_max_left _ _) (Finset.mem_univ slot)
  have hcum : 0 ≤ ∑ outer : Fin (outerDepth + 1), ∑ degree : Fin (cutoff + 1),
      max 0 (preparedFiniteForwardCumulative A constants degree.val
        (candidateNestedForwardSeed A constants innerDepth outer.val x)) :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => le_max_left _ _))
  linarith [le_max_left (0 : ℝ) anchorGoodRequired,
    le_max_left (0 : ℝ) conditionalRequired, le_max_right (0 : ℝ) (detectorRequired slot)]

theorem cumulative_le_preparedFiniteNestedSourceRequired
    (outer : Fin (outerDepth + 1)) (degree : Fin (cutoff + 1)) :
    preparedFiniteForwardCumulative A constants degree.val
      (candidateNestedForwardSeed A constants innerDepth outer.val x) ≤
    preparedFiniteNestedSourceRequired A constants innerDepth outerDepth cutoff
      x anchorGoodRequired conditionalRequired detectorRequired := by
  have hinner : max 0 (preparedFiniteForwardCumulative A constants degree.val
      (candidateNestedForwardSeed A constants innerDepth outer.val x)) ≤
      ∑ degree : Fin (cutoff + 1), max 0 (preparedFiniteForwardCumulative A constants degree.val
        (candidateNestedForwardSeed A constants innerDepth outer.val x)) :=
    Finset.single_le_sum
      (f := fun degree : Fin (cutoff + 1) => max 0
        (preparedFiniteForwardCumulative A constants degree.val
          (candidateNestedForwardSeed A constants innerDepth outer.val x)))
      (fun _ _ => le_max_left _ _) (Finset.mem_univ degree)
  have houter : (∑ degree : Fin (cutoff + 1), max 0
      (preparedFiniteForwardCumulative A constants degree.val
        (candidateNestedForwardSeed A constants innerDepth outer.val x))) ≤
      ∑ outer : Fin (outerDepth + 1), ∑ degree : Fin (cutoff + 1),
        max 0 (preparedFiniteForwardCumulative A constants degree.val
          (candidateNestedForwardSeed A constants innerDepth outer.val x)) :=
    Finset.single_le_sum
      (f := fun outer : Fin (outerDepth + 1) => ∑ degree : Fin (cutoff + 1), max 0
        (preparedFiniteForwardCumulative A constants degree.val
          (candidateNestedForwardSeed A constants innerDepth outer.val x)))
      (fun _ _ => Finset.sum_nonneg (fun _ _ => le_max_left _ _)) (Finset.mem_univ outer)
  have hdet : 0 ≤ ∑ slot, max 0 (detectorRequired slot) :=
    Finset.sum_nonneg (fun _ _ => le_max_left _ _)
  unfold preparedFiniteNestedSourceRequired
  linarith [le_max_left (0 : ℝ) anchorGoodRequired, le_max_left (0 : ℝ) conditionalRequired,
    le_max_right (0 : ℝ) (preparedFiniteForwardCumulative A constants degree.val
      (candidateNestedForwardSeed A constants innerDepth outer.val x))]

theorem preparedFiniteNestedSourceRequired_size_rank
    {X : Type*} (N : X → ℕ) (rank : ℝ)
    (hN : ∀ i, Real.exp (preparedFiniteNestedSourceRequired A constants innerDepth outerDepth cutoff
      x anchorGoodRequired conditionalRequired detectorRequired) ≤ (N i : ℝ))
    (hRank : Real.exp (preparedFiniteNestedSourceRequired A constants innerDepth outerDepth cutoff
      x anchorGoodRequired conditionalRequired detectorRequired) ≤ rank) :
    ((∀ i, Real.exp anchorGoodRequired ≤ (N i : ℝ)) ∧ Real.exp anchorGoodRequired ≤ rank) ∧
    ((∀ i, Real.exp conditionalRequired ≤ (N i : ℝ)) ∧ Real.exp conditionalRequired ≤ rank) ∧
    (∀ slot, (∀ i, Real.exp (detectorRequired slot) ≤ (N i : ℝ)) ∧
      Real.exp (detectorRequired slot) ≤ rank) ∧
    ∀ (outer : Fin (outerDepth + 1)) (degree : Fin (cutoff + 1)),
      (∀ i, Real.exp (preparedFiniteForwardCumulative A constants degree.val
        (candidateNestedForwardSeed A constants innerDepth outer.val x)) ≤ (N i : ℝ)) ∧
      Real.exp (preparedFiniteForwardCumulative A constants degree.val
        (candidateNestedForwardSeed A constants innerDepth outer.val x)) ≤ rank := by
  have hfloor : ∀ required : ℝ,
      required ≤ preparedFiniteNestedSourceRequired A constants innerDepth outerDepth cutoff
        x anchorGoodRequired conditionalRequired detectorRequired →
      (∀ i, Real.exp required ≤ (N i : ℝ)) ∧ Real.exp required ≤ rank := by
    intro required hrequired
    exact ⟨fun i => (Real.exp_le_exp.mpr hrequired).trans (hN i),
      (Real.exp_le_exp.mpr hrequired).trans hRank⟩
  exact ⟨hfloor _ (anchorGoodRequired_le_preparedFiniteNestedSourceRequired
      A constants innerDepth outerDepth cutoff x anchorGoodRequired conditionalRequired detectorRequired),
    hfloor _ (conditionalRequired_le_preparedFiniteNestedSourceRequired
      A constants innerDepth outerDepth cutoff x anchorGoodRequired conditionalRequired detectorRequired),
    fun slot => hfloor _ (detectorRequired_le_preparedFiniteNestedSourceRequired
      A constants innerDepth outerDepth cutoff x anchorGoodRequired conditionalRequired detectorRequired slot),
    fun outer degree => hfloor _ (cumulative_le_preparedFiniteNestedSourceRequired
      A constants innerDepth outerDepth cutoff x anchorGoodRequired conditionalRequired detectorRequired outer degree)⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteNestedSourceRelativeInitializerBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped BigOperators Classical

theorem preparedBadProduct_dimension_le_initial_allocation (m d : ℕ) :
    d ≤ modularInitialBlockCount m d := by
  have hp : 0 < (2 : ℕ) ^ m := by positivity
  unfold modularInitialBlockCount
  nlinarith [Nat.zero_le (modularInitialRankStrength m d)]

theorem preparedBadProduct_witness_count_le_dimension_sq (m nX M : ℕ) :
    modularInitialBlockCount m (nX + m * M) * (nX + m * M) ≤
      enlargedPreparedCommonSamplerDimension m M (modularInitialBlockCount m (nX + m * M)) ^ 2 := by
  have halloc := enlargedPreparedCommonSamplerDimension_allocation m M
    (modularInitialBlockCount m (nX + m * M))
  have hdim := (preparedBadProduct_dimension_le_initial_allocation m (nX + m * M)).trans halloc
  simpa only [pow_two] using Nat.mul_le_mul halloc hdim

theorem preparedBadProductWitnessGap_bounds (m nX M : ℕ) {P0 Elog Vlog : ℝ}
    (hpnum : (enlargedPreparedCommonSamplerDimension m M
      (modularInitialBlockCount m (nX + m * M)) : ℝ) ≤ P0)
    (hElog : 0 ≤ Elog) (hVlog : 0 ≤ Vlog) (Q : ℕ) (hQ : 1 ≤ Q)
    (hQexp : (Q : ℝ) ≤ Real.exp Vlog) :
    let W := physicalBadProductGap (modularInitialBlockCount m (nX + m * M) * (nX + m * M))
      Elog Vlog Q
    1 ≤ W ∧ W ≤ Real.exp (2 * P0 + 2 * Vlog + 5 * Elog + 24) := by
  intro W
  have hP0 : 0 ≤ P0 := (Nat.cast_nonneg _).trans hpnum
  have hN : ((modularInitialBlockCount m (nX + m * M) * (nX + m * M) : ℕ) : ℝ) ≤
      Real.exp (2 * P0) := by
    have hnum : (enlargedPreparedCommonSamplerDimension m M
        (modularInitialBlockCount m (nX + m * M)) : ℝ) ≤ Real.exp P0 :=
      hpnum.trans (by linarith [Real.add_one_le_exp P0])
    calc
      _ ≤ (enlargedPreparedCommonSamplerDimension m M
          (modularInitialBlockCount m (nX + m * M)) : ℝ) ^ 2 := by
        exact_mod_cast preparedBadProduct_witness_count_le_dimension_sq m nX M
      _ ≤ (Real.exp P0) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hnum 2
      _ = Real.exp (2 * P0) := by rw [two_mul, Real.exp_add, pow_two]
  exact ⟨(physicalBadProductGap_budget _ hElog hVlog Q hQ hQexp).1,
    physicalBadProductGap_exp_bound _ hElog hVlog (by positivity) Q hQexp hN⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open BooleanCubeKernel
open scoped BigOperators Classical

theorem preparedFiniteCanonicalSource_counts
    {m : ℕ} {X₀ J₀ : Type} (prep : RankPreparationFamily X₀ J₀ m)
    (nX M : ℕ) {Bstruct : ℝ}
    (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hnum : (enlargedPreparedCommonSamplerDimension m M
      (modularInitialBlockCount m (nX + m * M)) : ℝ) ≤ Bstruct) :
    (Fintype.card (EnlargedPreparedCommonKernel m
      (modularInitialBlockCount m (nX + m * M))) : ℝ) ≤ Bstruct ∧
    (Fintype.card (Fin nX ⊕ (Σ j, (prep j).Coord)) : ℝ) ≤ Bstruct ∧
    (Fintype.card (LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) : ℝ)
        ≤ Bstruct ∧ (m : ℝ) ≤ Bstruct := by
  let Jalloc := modularInitialBlockCount m (nX + m * M)
  have hcounts := preparedBadProduct_input_counts prep Jalloc nX hCoord
  have htags : Fintype.card (Fin nX ⊕ (Σ j, (prep j).Coord)) ≤ nX + m * M := by
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_sigma]
    apply Nat.add_le_add_left
    calc
      ∑ j : Fin m, Fintype.card (prep j).Coord ≤ ∑ _j : Fin m, M :=
        Finset.sum_le_sum (fun j _ => hCoord j)
      _ = m * M := by simp
  have htagsDimension := htags.trans
    ((preparedBadProduct_dimension_le_initial_allocation m (nX + m * M)).trans
      (enlargedPreparedCommonSamplerDimension_allocation m M Jalloc))
  exact ⟨(Nat.cast_le.mpr hcounts.2.2.2.1).trans hnum,
    (Nat.cast_le.mpr htagsDimension).trans hnum,
    (Nat.cast_le.mpr hcounts.2.2.2.2.1).trans hnum,
    (Nat.cast_le.mpr hcounts.1).trans hnum⟩

theorem preparedFiniteNestedSource_counts
    {m : ℕ} {X₀ J₀ : Type} (prep : RankPreparationFamily X₀ J₀ m)
    (nX M cutoff : ℕ) {Bstruct : ℝ}
    (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hnum : (enlargedPreparedCommonSamplerDimension (max m cutoff) M
      (modularInitialBlockCount (max m cutoff) (nX + max m cutoff * M)) : ℝ) ≤ Bstruct) :
    (Fintype.card (EnlargedPreparedCommonKernel (max m cutoff)
      (modularInitialBlockCount (max m cutoff) (nX + max m cutoff * M))) : ℝ) ≤ Bstruct ∧
    (Fintype.card (Fin nX ⊕ (Σ j, (prep.pad (max m cutoff) j).Coord)) : ℝ) ≤ Bstruct ∧
    (Fintype.card (LayerSamplerVariables
      (EnlargedPreparedCommonKernel (max m cutoff)
        (modularInitialBlockCount (max m cutoff) (nX + max m cutoff * M)))
      (PreparedSamplerContinuous (prep.pad (max m cutoff)))
      (preparedSamplerTransverse (prep.pad (max m cutoff)))
      (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff))
        (modularInitialBlockCount (max m cutoff) (nX + max m cutoff * M)))) : ℝ)
        ≤ Bstruct ∧ ((max m cutoff : ℕ) : ℝ) ≤ Bstruct :=
  preparedFiniteCanonicalSource_counts (prep.pad (max m cutoff)) nX M
    (prep.pad_coordinate_card_le hCoord) hnum

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteNestedSourceArrays
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

theorem preparedFiniteNestedSourceSliceExponent_bounds (m cutoff Cprimitive : ℕ) :
    1 ≤ preparedFiniteNestedSourceSliceExponent m cutoff Cprimitive ∧
    ∀ d ≤ cutoff, allocatedCandidateStageSliceExponent d m Cprimitive ≤
      preparedFiniteNestedSourceSliceExponent m cutoff Cprimitive := by
  constructor
  · unfold preparedFiniteNestedSourceSliceExponent
    omega
  · intro d hd
    have hsum := Finset.single_le_sum
      (f := fun i : Fin (cutoff + 1) => allocatedCandidateStageSliceExponent i.val m Cprimitive)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ (⟨d, Nat.lt_succ_of_le hd⟩ : Fin (cutoff + 1)))
    unfold preparedFiniteNestedSourceSliceExponent
    exact hsum.trans (Nat.le_add_left _ _)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedReadyPaddedRelativeInitialization
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

theorem preparedCenteredProductiveGoodCenterReady_mono
    {m nX M : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ}
    (S : LayerSamplerScale (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j : Fin m => RankPreparationLayer.Coord (prep j)) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    {E : Fin m → Type} [∀ j, Fintype (E j)]
    (bW : ∀ j, Basis (E j) ℤ
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (hm : ∀ j ex, coefficients (poly j) ex ∈ U j)
    (stride : Fin nX → ℕ)
    (width : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℝ)
    (bases : Finset (Fin nX → ℤ))
    (gainLog gain : ℝ) (Q : ℕ)
    (e : Fin 2 × Fin nX ↪ EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
    (law : (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U) → FiniteProbabilityWeights (bases × rectangularWeightIndices 0 width 1))
    (N : Fin nX → ℕ) (test : (Fin nX → ℝ) → ℝ)
    (Ready Ready' : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U → Prop)
    (hselected : PreparedCenteredProductiveGoodCenterReadyConclusion (m := m) (nX := nX) (M := M)
      prep U b S bW hb o hR hσ μ poly hm stride width bases gainLog gain Q e law N test Ready)
    (hReady : ∀ center, Ready center → Ready' center) :
    PreparedCenteredProductiveGoodCenterReadyConclusion (m := m) (nX := nX) (M := M)
      prep U b S bW hb o hR hσ μ poly hm stride width bases gainLog gain Q e law N test Ready' := by
  unfold PreparedCenteredProductiveGoodCenterReadyConclusion at hselected
  unfold PreparedCenteredProductiveGoodCenterReadyConclusion
  obtain ⟨c, hc, hcenter, sample, read, hread, hfinite⟩ := hselected
  refine ⟨c, hc, hcenter, sample, read, hread, ?_⟩
  intro primes hprime depth hdepth
  obtain ⟨center, F, hready, hmass, hF⟩ := hfinite primes hprime depth hdepth
  exact ⟨center, F, hReady center hready, hmass, hF⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteNestedForwardCanonicalFixedCenterSource
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct
variable {nX : ℕ}
attribute [local irreducible] AllocatedExternalCandidateSampler.NativeDetection

theorem exists_preparedFiniteNestedForwardCanonicalFixedCenterSource
    {m M : ℕ} {X₀ J₀ : Type} (prep : RankPreparationFamily X₀ J₀ m) (outerDepth innerDepth cutoff : ℕ)
    [∀ j : Fin (max m cutoff), DecidableEq (RankPreparationLayer.Coord ((prep.pad (max m cutoff)) j))]
    (U : ∀ j, Submodule ℝ ((fun j : Fin (max m cutoff) => RankPreparationLayer.Coord ((prep.pad (max m cutoff)) j)) j → ℝ))
    (b : ∀ j, Basis (Fin ((preparedSamplerTransverse (prep.pad (max m cutoff))) j)) ℝ (euclideanSubspace (U j))ᗮ)
    (stride N : Fin nX → ℕ)
    (Vtail : Fin (max m cutoff) → ℝ≥0)

    (Q : Fin (max m cutoff) → Type) [∀ j, Fintype (Q j)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis ((PreparedSamplerContinuous (prep.pad (max m cutoff))) j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice ((fun j : Fin (max m cutoff) => RankPreparationLayer.Coord ((prep.pad (max m cutoff)) j)) j)) (euclideanSubspace (U j))))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice ((fun j : Fin (max m cutoff) => RankPreparationLayer.Coord ((prep.pad (max m cutoff)) j)) j)) (euclideanSubspace (U j)))]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice ((fun j : Fin (max m cutoff) => RankPreparationLayer.Coord ((prep.pad (max m cutoff)) j)) j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    [CompactSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
    [BorelSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
    (μrows : Measure (CoefficientTorus (K := Fin (0 + 1)) U))
    [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]
    [MeasurableSpace (SiteTorus (Finset (Fin (0 + 1))) U)]
    [BorelSpace (SiteTorus (Finset (Fin (0 + 1))) U)]

    (e Cprimitive Cdirect extra : ℕ) (stageCountConstant : ℕ → ℕ)
    (Bstruct Qstride stageLog Econditional : ℝ)
    (Qσ Pmin requestedCoarse gainLog gain Vlog : ℝ)
    (Lmin Qgood : ℕ)
    (hm : 0 < max m cutoff) (hnX : 0 < nX)
    (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hB : 0 ≤ Bstruct) (hstage : stageLog ∈ Set.Icc 0 Bstruct)
    (hQstride : 0 ≤ Qstride)
    (hQσ : 0 ≤ Qσ) (hPmin : 0 ≤ Pmin)
    (hLmin : (Lmin : ℝ) ≤ Real.exp Pmin)
    (hg : 0 ≤ gainLog) (hVlog : 0 ≤ Vlog)
    (hQgood : 1 ≤ Qgood) (hQexp : (Qgood : ℝ) ≤ Real.exp Vlog)
    (hgain : Real.exp (-gainLog) ≤ gain)
    (hnChart : (nX : ℝ) ≤ Bstruct) (hgChart : gainLog ≤ Bstruct)
    (hstride : ∀ i, 0 < stride i)
    (hstrideBound : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride)
    (C : Fin (max m cutoff) → ℝ) (hC : ∀ j, 0 ≤ C j) (hCbound : ∀ j, C j ≤ Real.exp Bstruct)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (Cforward : Fin (max m cutoff) → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (hForward : ∀ j, (Cforward j : ℝ) ≤ Real.exp Bstruct)
    (hVtail : ∀ j, (Vtail j : ℝ) ≤ Real.exp Bstruct)
    (hVactual : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Vtail j)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Bstruct)
    (hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Bstruct)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))))) (Fin nX) stride))
    (hCells : cells.Nonempty)
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ ((fun j : Fin (max m cutoff) => RankPreparationLayer.Coord ((prep.pad (max m cutoff)) j)) j → ℝ))
    (hp : ∀ j, DegreeLE (1 : Fin nX → ℕ) (j.val + 1) (poly j))
    (hmem : ∀ j ex, coefficients (poly j) ex ∈ U j)
    (Rrank : ℝ)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j))
    (test : (Fin nX → ℝ) → ℝ) (htest : ∀ x, |test x| ≤ 1)
    (hmean : gain ≤ 𝔼 x ∈ integerBox N, test (fun i => (x i : ℝ))) :
    let A := preparedFiniteNestedSourceExponent (max m cutoff) cutoff e Cprimitive Cdirect extra
    let Cslice := preparedFiniteNestedSourceSliceExponent (max m cutoff) cutoff Cprimitive
    let forecastCap : ℝ := 1
    let Qw := 2 * Bstruct + 2 * Vlog + 5 * (gainLog + 8) + 24
    let Pdetect := preparedFiniteForwardDetectorPolynomial cutoff
    let K := PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff
    let degree : K → ℕ := preparedFiniteNestedForwardAllDegreeDegree
    let Cdetect := fun k : K => sampledSupportedSlicedDetectionConstant (degree k) Pdetect
    let kModel : K := preparedFiniteNestedForwardAllDegreeAnchor outerDepth innerDepth cutoff
    let sourceU := fun k : K =>
      preparedFiniteForwardPairedSourcePrecision A Cdirect stageCountConstant
        (preparedFiniteNestedForwardAllDegreeStage k).val (preparedFiniteNestedForwardAllDegreeIsDirect k)
        (preparedFiniteNestedForwardAllDegreeSeed A stageCountConstant Bstruct k) gainLog stageLog
    let modelLog := fun k : K => preparedFiniteForwardWork A stageCountConstant
      (preparedFiniteNestedForwardAllDegreeStage k).val
      (preparedFiniteNestedForwardAllDegreeSeed A stageCountConstant Bstruct k)
    let sliceLog := fun k : K =>
      (preparedFiniteForwardParameter A stageCountConstant (preparedFiniteNestedForwardAllDegreeStage k).val
        (preparedFiniteNestedForwardAllDegreeSeed A stageCountConstant Bstruct k) + Cslice) ^ Cslice
    let u := preparedFiniteForwardModelPrecision A stageCountConstant innerDepth
      (candidateNestedForwardSeed A stageCountConstant innerDepth outerDepth Bstruct) gainLog stageLog
    let p := preparedFiniteForwardWork A stageCountConstant innerDepth
      (candidateNestedForwardSeed A stageCountConstant innerDepth outerDepth Bstruct)
    let pnum : ℝ := enlargedPreparedCommonSamplerDimension (max m cutoff) M (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))
    let R : Fin (max m cutoff) → ℝ := fun _ => allocatedCommonProductRadius (max m cutoff) Bstruct Bstruct
    let pRadius := allocatedCommonProductRadiusLog (max m cutoff) Bstruct Bstruct
    let D := allocatedComparisonDimension (max m cutoff) pnum
    let pDetect := fun k => allocatedModelTestLog (sourceU k) (modelLog k)
    let aDetect := fun k => 2 * sourceU k + 4 * modelLog k + 7
    let detectionGain := fun s : K => slicedDetectionGainLog (degree s) (Cdetect s)
      (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))))) (pDetect s) (pDetect s) (aDetect s)
    let Pk := fun s : K => scalarKernelLogarithmicBudget (Fin ((degree s) + 1)) (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))
      (detectionGain s + pDetect s + 4)
    let Pphysical := fun k : K => preparedFiniteScheduleLocalPhysical (max m cutoff) nX
      (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))))) Qstride (Pk k)
    let target := fun k => detectionGain k + 40 + coefficientErrorSpatialLog (Pphysical k)
    let E := fun s : K => target s + D * (((max m cutoff) * 2 ^ ((max m cutoff) + 1) : ℕ) * Pk s) + 5
    let Prho := fun s : K => 2 * affineProfileInputEnvelope D
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect s + 2) + 2
    let Ptail := fun s : K => affineProfileToleranceEnvelope (max m cutoff) D (D * (D + 1) + D * D + D + 1)
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect s + 2)
    let Pscale := preparedUniformDegreeScaleLog (D + pRadius) Ptail Qσ
    let Tmod := fun s : K => (((max m cutoff) + 1 : ℕ) : ℝ) * Pk s + nX * Qstride
    let lengthLogs := fun s : K => allocatedAffineLengthLog (max m cutoff) D Pscale (Prho s) (Pk s)
      (target s) (pDetect s + 2) (Tmod s)
    let Pseed := allocatedScaleLog (Pscale + ∑ s, lengthLogs s + Pmin + 1)
    let W := physicalBadProductGap ((modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)) * (nX + (max m cutoff) * M)) (gainLog + 8) Vlog Qgood
    let Pmaster := fun k : K => preparedFiniteScheduleLocalMaster Bstruct D pRadius Qstride
      (Pphysical k) (sourceU k) (modelLog k) (Prho k) (target k) (detectionGain k)
    let coarseTarget := preparedFiniteScheduleDirectCoarse detectionGain requestedCoarse
    let Plate := ∑ k : K, preparedUniformDegreeDirectLate (Pmaster k) Pscale
      (Pphysical k) coarseTarget (allocatedWitnessScaleLog Pseed Qw)
    let τ := Real.exp (-(gainLog + (nX : ℝ) + 8))
    let α := fun k : K => Real.exp (-(2 * preparedFiniteForwardModelPrecision A stageCountConstant
      (preparedFiniteNestedForwardAllDegreeStage k).val
      (preparedFiniteNestedForwardAllDegreeSeed A stageCountConstant Bstruct k) gainLog stageLog +
      4 * modelLog k + 8))
    let baseB0 := preparedUniformDegreeProductiveCertificateBudget M nX pRadius Pscale Pseed Qw (gainLog + 8) Vlog
    let Pwidth := 4 * (Plate + 8) ^ 2
    let Bcert := preparedForecastGoodCertificateBudget baseB0 Bstruct Pwidth gainLog Vlog
    let Pgood := preparedForecastGoodAnalyticBudget (preparedCenteredShortForecastSpatialExponent (max m cutoff))
      baseB0 Bstruct Pwidth gainLog Vlog
    let anchorRequired := preparedFiniteScheduleAnchorGoodRequired (max m cutoff) (Pmaster kModel) Plate Econditional Bcert Pgood Pwidth
    let conditionalRequired := preparedConditionalExcessRequired (max m cutoff) Plate Econditional
    let detectorRequired := fun k : K => (preparedModularGeneralDetectorResources
      (preparedModularGeneralDetectorConstants (max m cutoff) (degree k)) (degree k + 1) (Pmaster k) Plate).required
    let Rreq := preparedFiniteNestedSourceRequired A stageCountConstant innerDepth outerDepth cutoff Bstruct
      anchorRequired conditionalRequired detectorRequired
    pnum ≤ Bstruct →
    (∀ i, Real.exp Rreq ≤ (N i : ℝ)) → Real.exp Rreq ≤ Rrank →
    ∃ (hR : ∀ j, 0 < R j) (σ : ℝ) (hσ : 0 < σ)
      (S : LayerSamplerScale («G» := (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))) («I» := (PreparedSamplerContinuous (prep.pad (max m cutoff)))) («n» := (preparedSamplerTransverse (prep.pad (max m cutoff)))) («J» := (fun j : Fin (max m cutoff) => RankPreparationLayer.Coord ((prep.pad (max m cutoff)) j))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) U b R (fun _ => σ)),
      0 ≤ pRadius ∧ (∀ j, R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧
      σ ≤ 1 ∧ σ ≤ Real.exp (-Qσ) ∧ σ⁻¹ ≤ Real.exp Pscale ∧
      Lmin ≤ S.value ∧ (S.value : ℝ) ≤ Real.exp (allocatedWitnessScaleLog Pseed Qw) ∧
      (∀ j i, S.value ^ (j.val + 1) < basisAxisScale (b j) i →
        8 * (probabilityProfileLipschitz : ℝ) * W ≤
          (layerSamplerGapWidth («G» := (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) R ⟨j, i⟩ / 2) *
            ((basisAxisScale (b j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))) ∧
      (∀ s : K, PreparedUniformDegreeGeometryAt («G» := (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) U b S (degree s) (Cdetect s) nX
        Bstruct Pscale D (target s) (Pk s) (Prho s) Qstride (pDetect s) pRadius (aDetect s) (detectionGain s)) ∧
      (∀ k, PreparedUniformDegreeDirectScalarBounds (max m cutoff) (degree k) nX
        (Fintype.card (LayerSamplerVariables
          (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))
          (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff)))
          (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))))
        (Cdetect k) Bstruct Pscale D (target k) (Pk k) (Prho k) Qstride (Pmaster k) Plate
        (detectionGain k) (Pphysical k) coarseTarget pRadius (sourceU k) (modelLog k) (sliceLog k)) ∧
      (∀ k, PreparedScheduledDirectSourceAvailability
          (B := EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))
          (U := U) (basis := b) (S := S) (hR := hR) (hσ := fun _ => hσ)
          (selection := enlargedPreparedCommonCanonicalSelection (max m cutoff)
            (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)) (degree k) (preparedFiniteNestedForwardAllDegreeDegree_le (Nat.le_max_right m cutoff) k))
          (stride := stride) (N := N) (Pdetect := Pdetect)
          (sourceU := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
          (Vtail := Vtail) (τ := τ) (hb := hb) (o := o)
          Bstruct Qstride (Pmaster k) Plate (detectionGain k) (Pphysical k) coarseTarget) ∧
      (∀ k, PreparedScheduledDegreeModelAvailability
          (B := EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))
          (U := U) (basis := b) (S := S) (hR := hR) (hσ := fun _ => hσ)
          (selection := enlargedPreparedCommonCanonicalSelection (max m cutoff)
            (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)) (degree k)
              (preparedFiniteNestedForwardAllDegreeDegree_le (Nat.le_max_right m cutoff) k))
          (stride := stride) (N := N) (Pdetect := Pdetect)
          (sourceU := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
          (Vtail := Vtail) (τ := τ) (hb := hb) (o := o) (μ := μ)
          Bstruct Qstride (Pmaster k) Plate (detectionGain k) (Pphysical k) coarseTarget) ∧
      PreparedUniformDegreeProductiveSourceConclusion
        (m := (max m cutoff)) (nX := nX) (M := M) (prep := (prep.pad (max m cutoff))) (U := U) (b := b) (S := S)
        (hR := hR) (hσ := fun _ => hσ) (stride := stride) (N := N)
        (Pdetect := Pdetect) (pModel := modelLog kModel) (pSlice := sliceLog kModel)
        (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
        (hb := hb) (o := o) (bW := bW) (μ := μ)
        Bstruct Qstride (Pmaster kModel) Plate (detectionGain kModel) (Pphysical kModel) coarseTarget
        pRadius Pscale Pseed Qw gainLog gain Vlog Qgood ∧
      ∃ (hmargin : ∀ i, 2 * spatialTrimMargin τ N i ≤ N i)
        (Acandidate : AllocatedExternalCandidateSamplerFamily (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) U b S hb o hR (fun _ => hσ)
          N poly hmem τ (Real.exp (-Plate)) stride cells)
        (hξone : Real.exp (-Plate) ≤ 1),
      PreparedCenteredProductiveGoodCenterReadyConclusion (m := (max m cutoff)) (nX := nX) (M := M)
        (prep.pad (max m cutoff)) U b S bW hb o hR (fun _ => hσ) μ poly hmem stride
        (allocatedExternalCandidateWidths (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) U b S N τ (Real.exp (-Plate))) (Acandidate 0).bases
        gainLog gain Qgood (preparedSpatialKernelBlocks (max m cutoff) M nX) Acandidate.law N test
        (fun center =>
          letI : DecidableEq (Fin nX) := Classical.decEq _
          (∀ k : K, (Acandidate center).NativeDetection (degree k) (sliceLog k)
            (Pdetect.eval₂ (Nat.castRingHom ℝ) (pDetect k))
            (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants (max m cutoff) (degree k))
              (degree k + 1) (Pmaster k) Plate).nativeBudget (α k)) ∧
          letI : Nonempty (Acandidate center).Site := (Acandidate center).site_nonempty
          (FiniteProbabilityWeights.uniformFinset (integerBox N) (Acandidate center).integerBox_nonempty).excessMass
            ((Acandidate center).law.siteLaw ((Acandidate center).physicalBox hξone hmargin))
            (4 * ∏ j, earlyConstantDensityCap (Fintype.card ((PreparedSamplerContinuous (prep.pad (max m cutoff))) j)) ((preparedSamplerTransverse (prep.pad (max m cutoff))) j) (R j) (Vtail j)) ≤
              6 * positiveProjectionAccuracy Econditional) := by
  intro A Cslice forecastCap Qw Pdetect K degree Cdetect kModel sourceU modelLog sliceLog u p
    pnum R pRadius D pDetect aDetect detectionGain Pk Pphysical target E Prho Ptail Pscale Tmod
    lengthLogs Pseed W Pmaster coarseTarget Plate τ α baseB0 Pwidth Bcert Pgood
    anchorRequired conditionalRequired detectorRequired Rreq hnum hNrequired hRankRequired
  obtain ⟨hA, _hextra, _hfront, hDensity, hSliceExponent, _hdegrees⟩ :=
    preparedFiniteNestedSourceExponent_bounds (max m cutoff) cutoff e Cprimitive Cdirect extra A
      (show preparedFiniteNestedSourceExponent (max m cutoff) cutoff e Cprimitive Cdirect extra ≤ A from le_rfl)
  have hQw : 0 ≤ Qw := by
    dsimp only [Qw]
    positivity
  have hWexp : W ≤ Real.exp Qw :=
    (preparedBadProductWitnessGap_bounds (max m cutoff) nX M hnum
      (show 0 ≤ gainLog + 8 by linarith only [hg]) hVlog Qgood hQgood hQexp).2
  have hCtail := prepared_commonRadius_densityCap_nested_bound (max m cutoff) A hDensity
    (prep.pad (max m cutoff)) le_rfl M
    (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))
    (prep.pad_coordinate_card_le hCoord) Bstruct hB hnum Vtail hVtail hprofile
    stageCountConstant innerDepth outerDepth innerDepth
  have hpnonneg : 0 ≤ p := preparedFiniteForwardWork_nonneg A stageCountConstant innerDepth
    (candidateNestedForwardSeed_nonneg A stageCountConstant innerDepth outerDepth hB)
  have hForecastCap : 0 ≤ forecastCap := by change (0 : ℝ) ≤ 1; norm_num
  have hForecastCapP : forecastCap ≤ Real.exp p := Real.one_le_exp_iff.mpr hpnonneg
  exact exists_preparedFiniteNestedForwardProductiveFixedCenterSource_s2
    prep outerDepth innerDepth cutoff U b stride N Vtail Q hb o bW ν μ μrows
    A Cslice Cdirect stageCountConstant hA hSliceExponent
    Bstruct Qstride forecastCap stageLog Econditional Qσ Qw Pmin requestedCoarse gainLog gain Vlog
    Lmin Qgood hm hnX hCoord hB hstage hQstride hQσ hQw hPmin hLmin hg hVlog
    hQgood hQexp hgain hnChart hgChart hstride hstrideBound
    C hC hCbound hchart Cforward hforward hForward hVtail hVactual hprofile hcutoff
    cells hCells poly hp hmem Rrank hrank test htest hmean
    hnum hWexp hCtail hForecastCap hForecastCapP hNrequired hRankRequired

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PreparedFiniteNestedDegreeSourceProfileScalars
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

private theorem nestedSourceFullScalar_and_rec {a b : Prop} {α : Sort*}
    (f : a → b → α) (h : a ∧ b) : And.rec f h = f h.1 h.2 := by
  cases h
  rfl

variable {m : ℕ} {X₀ J₀ G X : Type} [Fintype G] [Fintype X]
    (prep : RankPreparationFamily X₀ J₀ m)
    {B : LayerSamplerAxis (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) → Type}
    [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ ((prep j).Coord → ℝ)}
    {b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ ((prep j).Coord → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern
      (Option (LayerSamplerVariables G (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice ((prep j).Coord)) (euclideanSubspace (U j)))]
    (sampler : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateSampler

local notation "countConstants" => degreeSourceCountConstants

attribute [local instance] OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSampler.nestedDegreeSourceFullScalarsSiteNonempty
variable (outerDepth innerDepth cutoff exponent Cprimitive Cslice Cdirect M Jalloc : ℕ)
    (Bstruct gainLog stageLog Qstride Plate E endpoint rankThreshold : ℝ)

local notation "Slots" => PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff
local notation "count" => Fintype.card (LayerSamplerVariables G
    (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) B)
local notation "pnum" => (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ)
local notation "seed" => candidateNestedForwardSeed exponent countConstants innerDepth
local notation "native" => preparedFiniteNestedSourceNative m G count (Fintype.card X)
    (preparedFiniteForwardDetectorPolynomial cutoff) exponent Cdirect countConstants
    Bstruct pnum Qstride gainLog stageLog Plate
local notation "slotSeed" => preparedFiniteNestedForwardAllDegreeSeed exponent countConstants Bstruct
local notation "slotStage" => preparedFiniteNestedForwardAllDegreeStage
local notation "slotDegree" => preparedFiniteNestedForwardAllDegreeDegree

attribute [local irreducible] AllocatedExternalCandidateSampler.NativeDetection

theorem exists_preparedFiniteNestedDegreeSourceProfile_fullScalars
    (outerFront outerInner : Fin (outerDepth + 1)) {degree e : ℕ} {p chartLog : ℝ}
    (hdegree : degree ≤ cutoff) (hcutoff : cutoff ≤ m) (hdepth : degree ≤ innerDepth)
    (hFrontExponent : preparedFiniteForwardFrontProfileExponent e ≤ exponent)
    (hCapExponent : preparedCommonRadiusDensityCapNestedExponent m ≤ exponent)
    (hInnerExponent : allocatedCandidateForwardScheduleExponent degree m Cprimitive
      (preparedFiniteForwardInnerSourceExponent Cdirect
        (preparedFiniteForwardActualNativeBudgetExponent m
          (preparedFiniteForwardDetectorPolynomial cutoff))) 2 ≤ exponent)
    (hCslice : 1 ≤ Cslice) (hSliceExponent : Cslice + 1 ≤ exponent)
    (hInnerSlice : allocatedCandidateStageSliceExponent degree m Cprimitive ≤ Cslice)
    (hprimitive : 1 ≤ Cprimitive)
    (hBstruct : 0 ≤ Bstruct) (hg : gainLog ∈ Set.Icc 0 Bstruct)
    (hs : stageLog ∈ Set.Icc 0 Bstruct) (hQstride : Qstride ∈ Set.Icc 0 Bstruct)
    (hM : ∀ j, Fintype.card (prep j).Coord ≤ M) (hnum : pnum ≤ Bstruct)
    (hG : (Fintype.card G : ℝ) ≤ Bstruct)
    (htags : (Fintype.card (X ⊕ (Σ j, (prep j).Coord)) : ℝ) ≤ Bstruct)
    (hvariables : (count : ℝ) ≤ Bstruct)
    (hpFront : p ∈ Set.Icc 0 (seed outerFront.val Bstruct))
    (hpInner : p ≤ seed outerInner.val Bstruct)
    (hξ : ξ ≤ 1) (hmargin : ∀ i, 2 * spatialTrimMargin τ N i ≤ N i)
    (Vtail : Fin m → ℝ≥0) (hVtail : ∀ j, (Vtail j : ℝ) ≤ Real.exp Bstruct)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Bstruct)
    (hendpoint : 0 ≤ endpoint)
    (hE : preparedNestedFrontProjectionEnvelope exponent countConstants innerDepth
      (fun k : Slots => (preparedFiniteNestedForwardAllDegreeOuter k).val)
      (fun k : Slots => (slotStage k).val) native
      Bstruct gainLog stageLog endpoint ≤ E)
    (hNative : ∀ k : Slots, sampler.NativeDetection (slotDegree k)
      ((preparedFiniteForwardParameter exponent countConstants (slotStage k).val (slotSeed k) + Cslice) ^ Cslice)
      ((preparedFiniteForwardDetectorPolynomial cutoff).eval₂ (Nat.castRingHom ℝ)
        (allocatedModelTestLog
          (preparedFiniteForwardPairedSourcePrecision exponent Cdirect countConstants
            (slotStage k).val (preparedFiniteNestedForwardAllDegreeIsDirect k)
            (slotSeed k) gainLog stageLog)
          (preparedFiniteForwardWork exponent countConstants (slotStage k).val (slotSeed k))))
      (native k)
      (Real.exp (-(2 * preparedFiniteForwardModelPrecision exponent countConstants
        (slotStage k).val (slotSeed k) gainLog stageLog +
        4 * preparedFiniteForwardWork exponent countConstants (slotStage k).val (slotSeed k) + 8))))
    (hexcess :
      (FiniteProbabilityWeights.uniformFinset (integerBox N) sampler.integerBox_nonempty).excessMass
        (sampler.law.siteLaw (sampler.physicalBox hξ hmargin))
        (4 * ∏ j, earlyConstantDensityCap (Fintype.card (PreparedSamplerContinuous prep j))
          (preparedSamplerTransverse prep j) (R j) (Vtail j)) ≤
        6 * positiveProjectionAccuracy E)
    (hsize : ∀ i, Real.exp (preparedFiniteForwardCumulative exponent countConstants degree
      (seed outerInner.val Bstruct)) ≤ (N i : ℝ))
    (hrank : Real.exp (preparedFiniteForwardCumulative exponent countConstants degree
      (seed outerInner.val Bstruct)) ≤ rankThreshold)
    (hsampling : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) rankThreshold (U j) (poly j))
    (hτ : τ ≤ 1) (hσone : ∀ j, σ j ≤ 1)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v,
      ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hCbound : ∀ j, C j ≤ Real.exp chartLog) (hallow : chartLog + 1 ≤ Bstruct)
    (hRadius : ∀ j, R j = allocatedCommonProductRadius m Bstruct Bstruct) :
    ∃ P : sampler.DegreeSourceProfile degree p e,
      P.inner.x = seed outerInner.val Bstruct ∧
      P.inner.gainLog = seed outerInner.val Bstruct ∧
      P.front.u = preparedFiniteForwardModelPrecision exponent countConstants 0
        (seed outerFront.val Bstruct) gainLog stageLog ∧
      P.front.pModel = preparedFiniteForwardWork exponent countConstants 0
        (seed outerFront.val Bstruct) ∧
      P.front.nativeBudget = native
        ((outerFront, 0, ⟨degree, Nat.lt_succ_of_le hdegree⟩, false) : Slots) ∧
      P.inner.Cprimitive = Cprimitive ∧
      P.inner.scheduleExponent = exponent ∧
      P.inner.Csource = preparedFiniteNestedSourceNativeExponent m cutoff Cdirect := by
  let P := preparedFiniteNestedDegreeSourceProfile prep sampler
    outerDepth innerDepth cutoff exponent Cprimitive Cslice Cdirect M Jalloc
    Bstruct gainLog stageLog Qstride Plate E endpoint rankThreshold outerFront outerInner
    hdegree hcutoff hdepth hFrontExponent hCapExponent hInnerExponent hCslice hSliceExponent
    hInnerSlice hprimitive hBstruct hg hs hQstride hM hnum hG htags hvariables hpFront hpInner
    hξ hmargin Vtail hVtail hprofile hendpoint hE hNative hexcess hsize hrank hsampling
    hτ hσone hpoly C hC hchart hCbound hallow hRadius
  refine ⟨P, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [P, preparedFiniteNestedDegreeSourceProfile,
    nestedSourceFullScalar_and_rec,
    preparedCommonRadiusDegreeSourceProfile, preparedFiniteForwardActualFrontSourceProfile,
    preparedFiniteForwardFrontSourceProfile, preparedFixedCenterFrontSourceProfile,
    InnerSourceProfile.with_gain_detection, InnerSourceProfile.raise_gain,
    preparedFiniteForwardActualInnerSourceProfile, preparedFiniteForwardInnerSourceProfile,
    preparedFiniteNestedSourceNative, preparedFiniteNestedForwardAllDegreeDegree_slot,
    preparedFiniteNestedSourceMaster_front, preparedFiniteNestedSourceNativeExponent]

theorem exists_preparedFiniteNestedDegreeSourceProfile_of_exponent_fullScalars
    (extra : ℕ)
    (outerFront outerInner : Fin (outerDepth + 1)) {degree e : ℕ} {p chartLog : ℝ}
    (hdegree : degree ≤ cutoff) (hcutoff : cutoff ≤ m) (hdepth : degree ≤ innerDepth)
    (hExponent : preparedFiniteNestedSourceExponent m cutoff e Cprimitive Cdirect extra ≤ exponent)
    (hprimitive : 1 ≤ Cprimitive)
    (hBstruct : 0 ≤ Bstruct) (hg : gainLog ∈ Set.Icc 0 Bstruct)
    (hs : stageLog ∈ Set.Icc 0 Bstruct) (hQstride : Qstride ∈ Set.Icc 0 Bstruct)
    (hM : ∀ j, Fintype.card (prep j).Coord ≤ M) (hnum : pnum ≤ Bstruct)
    (hG : (Fintype.card G : ℝ) ≤ Bstruct)
    (htags : (Fintype.card (X ⊕ (Σ j, (prep j).Coord)) : ℝ) ≤ Bstruct)
    (hvariables : (count : ℝ) ≤ Bstruct)
    (hpFront : p ∈ Set.Icc 0 (seed outerFront.val Bstruct))
    (hpInner : p ≤ seed outerInner.val Bstruct)
    (hξ : ξ ≤ 1) (hmargin : ∀ i, 2 * spatialTrimMargin τ N i ≤ N i)
    (Vtail : Fin m → ℝ≥0) (hVtail : ∀ j, (Vtail j : ℝ) ≤ Real.exp Bstruct)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Bstruct)
    (hendpoint : 0 ≤ endpoint)
    (hE : preparedNestedFrontProjectionEnvelope exponent countConstants innerDepth
      (fun k : Slots => (preparedFiniteNestedForwardAllDegreeOuter k).val)
      (fun k : Slots => (slotStage k).val) native
      Bstruct gainLog stageLog endpoint ≤ E)
    (hNative : ∀ k : Slots, sampler.NativeDetection (slotDegree k)
      ((preparedFiniteForwardParameter exponent countConstants (slotStage k).val (slotSeed k) + (preparedFiniteNestedSourceSliceExponent m cutoff Cprimitive)) ^ (preparedFiniteNestedSourceSliceExponent m cutoff Cprimitive))
      ((preparedFiniteForwardDetectorPolynomial cutoff).eval₂ (Nat.castRingHom ℝ)
        (allocatedModelTestLog
          (preparedFiniteForwardPairedSourcePrecision exponent Cdirect countConstants
            (slotStage k).val (preparedFiniteNestedForwardAllDegreeIsDirect k)
            (slotSeed k) gainLog stageLog)
          (preparedFiniteForwardWork exponent countConstants (slotStage k).val (slotSeed k))))
      (native k)
      (Real.exp (-(2 * preparedFiniteForwardModelPrecision exponent countConstants
        (slotStage k).val (slotSeed k) gainLog stageLog +
        4 * preparedFiniteForwardWork exponent countConstants (slotStage k).val (slotSeed k) + 8))))
    (hexcess :
      (FiniteProbabilityWeights.uniformFinset (integerBox N) sampler.integerBox_nonempty).excessMass
        (sampler.law.siteLaw (sampler.physicalBox hξ hmargin))
        (4 * ∏ j, earlyConstantDensityCap (Fintype.card (PreparedSamplerContinuous prep j))
          (preparedSamplerTransverse prep j) (R j) (Vtail j)) ≤
        6 * positiveProjectionAccuracy E)
    (hsize : ∀ i, Real.exp (preparedFiniteForwardCumulative exponent countConstants degree
      (seed outerInner.val Bstruct)) ≤ (N i : ℝ))
    (hrank : Real.exp (preparedFiniteForwardCumulative exponent countConstants degree
      (seed outerInner.val Bstruct)) ≤ rankThreshold)
    (hsampling : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) rankThreshold (U j) (poly j))
    (hτ : τ ≤ 1) (hσone : ∀ j, σ j ≤ 1)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v,
      ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hCbound : ∀ j, C j ≤ Real.exp chartLog) (hallow : chartLog + 1 ≤ Bstruct)
    (hRadius : ∀ j, R j = allocatedCommonProductRadius m Bstruct Bstruct) :
    ∃ P : sampler.DegreeSourceProfile degree p e,
      P.inner.x = seed outerInner.val Bstruct ∧
      P.inner.gainLog = seed outerInner.val Bstruct ∧
      P.front.u = preparedFiniteForwardModelPrecision exponent countConstants 0
        (seed outerFront.val Bstruct) gainLog stageLog ∧
      P.front.pModel = preparedFiniteForwardWork exponent countConstants 0
        (seed outerFront.val Bstruct) ∧
      P.front.nativeBudget = native
        ((outerFront, 0, ⟨degree, Nat.lt_succ_of_le hdegree⟩, false) : Slots) ∧
      P.inner.Cprimitive = Cprimitive ∧
      P.inner.scheduleExponent = exponent ∧
      P.inner.Csource = preparedFiniteNestedSourceNativeExponent m cutoff Cdirect := by
  have he := preparedFiniteNestedSourceExponent_bounds m cutoff e Cprimitive Cdirect extra exponent hExponent
  have hc := preparedFiniteNestedSourceSliceExponent_bounds m cutoff Cprimitive
  exact exists_preparedFiniteNestedDegreeSourceProfile_fullScalars prep sampler
    outerDepth innerDepth cutoff exponent Cprimitive
    (preparedFiniteNestedSourceSliceExponent m cutoff Cprimitive) Cdirect M Jalloc
    Bstruct gainLog stageLog Qstride Plate E endpoint rankThreshold outerFront outerInner
    hdegree hcutoff hdepth he.2.2.1 he.2.2.2.1 (he.2.2.2.2.2 degree hdegree)
    hc.1 he.2.2.2.2.1 (hc.2 degree hdegree)
    hprimitive hBstruct hg hs hQstride hM hnum hG htags hvariables hpFront hpInner
    hξ hmargin Vtail hVtail hprofile hendpoint hE hNative hexcess hsize hrank hsampling
    hτ hσone hpoly C hC hchart hCbound hallow hRadius

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedCanonicalInitializedRelativeSourceConclusion
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct
variable {nX : ℕ}
attribute [local irreducible] AllocatedExternalCandidateSampler.NativeDetection

theorem exists_preparedFiniteNestedForwardCompleteFixedCenterSource_fullScalars_s2_oai
    {m M : ℕ} {X₀ J₀ : Type} (prep : RankPreparationFamily X₀ J₀ m) (outerDepth innerDepth cutoff : ℕ)
    [∀ j : Fin (max m cutoff), DecidableEq (RankPreparationLayer.Coord ((prep.pad (max m cutoff)) j))]
    (U : ∀ j, Submodule ℝ ((fun j : Fin (max m cutoff) => RankPreparationLayer.Coord ((prep.pad (max m cutoff)) j)) j → ℝ))
    (b : ∀ j, Basis (Fin ((preparedSamplerTransverse (prep.pad (max m cutoff))) j)) ℝ (euclideanSubspace (U j))ᗮ)
    (stride N : Fin nX → ℕ)
    (Vtail : Fin (max m cutoff) → ℝ≥0)

    (Q : Fin (max m cutoff) → Type) [∀ j, Fintype (Q j)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis ((PreparedSamplerContinuous (prep.pad (max m cutoff))) j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice ((fun j : Fin (max m cutoff) => RankPreparationLayer.Coord ((prep.pad (max m cutoff)) j)) j)) (euclideanSubspace (U j))))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice ((fun j : Fin (max m cutoff) => RankPreparationLayer.Coord ((prep.pad (max m cutoff)) j)) j)) (euclideanSubspace (U j)))]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice ((fun j : Fin (max m cutoff) => RankPreparationLayer.Coord ((prep.pad (max m cutoff)) j)) j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    [CompactSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
    [BorelSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
    (μrows : Measure (CoefficientTorus (K := Fin (0 + 1)) U))
    [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]
    [MeasurableSpace (SiteTorus (Finset (Fin (0 + 1))) U)]
    [BorelSpace (SiteTorus (Finset (Fin (0 + 1))) U)]

    (e Cprimitive Cdirect extra : ℕ) (hprimitive : 1 ≤ Cprimitive)
    (Bstruct Qstride stageLog endpoint chartLog : ℝ)
    (hendpoint : 0 ≤ endpoint) (hchartLog : chartLog + 1 ≤ Bstruct)
    (Qσ Pmin requestedCoarse gainLog gain Vlog : ℝ)
    (Lmin Qgood : ℕ)
    (hm : 0 < max m cutoff) (hnX : 0 < nX)
    (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hB : 0 ≤ Bstruct) (hstage : stageLog ∈ Set.Icc 0 Bstruct)
    (hQstride : Qstride ∈ Set.Icc 0 Bstruct)
    (hQσ : 0 ≤ Qσ) (hPmin : 0 ≤ Pmin)
    (hLmin : (Lmin : ℝ) ≤ Real.exp Pmin)
    (hg : 0 ≤ gainLog) (hVlog : 0 ≤ Vlog)
    (hQgood : 1 ≤ Qgood) (hQexp : (Qgood : ℝ) ≤ Real.exp Vlog)
    (hgain : Real.exp (-gainLog) ≤ gain)
    (hnChart : (nX : ℝ) ≤ Bstruct) (hgChart : gainLog ≤ Bstruct)
    (hstride : ∀ i, 0 < stride i)
    (hstrideBound : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride)
    (C : Fin (max m cutoff) → ℝ) (hC : ∀ j, 0 ≤ C j) (hCbound : ∀ j, C j ≤ Real.exp chartLog)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (Cforward : Fin (max m cutoff) → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (hForward : ∀ j, (Cforward j : ℝ) ≤ Real.exp Bstruct)
    (hVtail : ∀ j, (Vtail j : ℝ) ≤ Real.exp Bstruct)
    (hVactual : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Vtail j)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Bstruct)
    (hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Bstruct)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))))) (Fin nX) stride))
    (hCells : cells.Nonempty)
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ ((fun j : Fin (max m cutoff) => RankPreparationLayer.Coord ((prep.pad (max m cutoff)) j)) j → ℝ))
    (hp : ∀ j, DegreeLE (1 : Fin nX → ℕ) (j.val + 1) (poly j))
    (hmem : ∀ j ex, coefficients (poly j) ex ∈ U j)
    (Rrank : ℝ)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j))
    (test : (Fin nX → ℝ) → ℝ) (htest : ∀ x, |test x| ≤ 1)
    (hmean : gain ≤ 𝔼 x ∈ integerBox N, test (fun i => (x i : ℝ))) :
    let stageCountConstant := AllocatedExternalCandidateSampler.degreeSourceCountConstants
    let A := preparedFiniteNestedSourceExponent (max m cutoff) cutoff e Cprimitive Cdirect extra
    let Cslice := preparedFiniteNestedSourceSliceExponent (max m cutoff) cutoff Cprimitive
    let forecastCap : ℝ := 1
    let Qw := 2 * Bstruct + 2 * Vlog + 5 * (gainLog + 8) + 24
    let Pdetect := preparedFiniteForwardDetectorPolynomial cutoff
    let K := PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff
    let degree : K → ℕ := preparedFiniteNestedForwardAllDegreeDegree
    let Cdetect := fun k : K => sampledSupportedSlicedDetectionConstant (degree k) Pdetect
    let kModel : K := preparedFiniteNestedForwardAllDegreeAnchor outerDepth innerDepth cutoff
    let sourceU := fun k : K =>
      preparedFiniteForwardPairedSourcePrecision A Cdirect stageCountConstant
        (preparedFiniteNestedForwardAllDegreeStage k).val (preparedFiniteNestedForwardAllDegreeIsDirect k)
        (preparedFiniteNestedForwardAllDegreeSeed A stageCountConstant Bstruct k) gainLog stageLog
    let modelLog := fun k : K => preparedFiniteForwardWork A stageCountConstant
      (preparedFiniteNestedForwardAllDegreeStage k).val
      (preparedFiniteNestedForwardAllDegreeSeed A stageCountConstant Bstruct k)
    let sliceLog := fun k : K =>
      (preparedFiniteForwardParameter A stageCountConstant (preparedFiniteNestedForwardAllDegreeStage k).val
        (preparedFiniteNestedForwardAllDegreeSeed A stageCountConstant Bstruct k) + Cslice) ^ Cslice
    let u := preparedFiniteForwardModelPrecision A stageCountConstant innerDepth
      (candidateNestedForwardSeed A stageCountConstant innerDepth outerDepth Bstruct) gainLog stageLog
    let p := preparedFiniteForwardWork A stageCountConstant innerDepth
      (candidateNestedForwardSeed A stageCountConstant innerDepth outerDepth Bstruct)
    let pnum : ℝ := enlargedPreparedCommonSamplerDimension (max m cutoff) M (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))
    let R : Fin (max m cutoff) → ℝ := fun _ => allocatedCommonProductRadius (max m cutoff) Bstruct Bstruct
    let pRadius := allocatedCommonProductRadiusLog (max m cutoff) Bstruct Bstruct
    let D := allocatedComparisonDimension (max m cutoff) pnum
    let pDetect := fun k => allocatedModelTestLog (sourceU k) (modelLog k)
    let aDetect := fun k => 2 * sourceU k + 4 * modelLog k + 7
    let detectionGain := fun s : K => slicedDetectionGainLog (degree s) (Cdetect s)
      (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))))) (pDetect s) (pDetect s) (aDetect s)
    let Pk := fun s : K => scalarKernelLogarithmicBudget (Fin ((degree s) + 1)) (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))
      (detectionGain s + pDetect s + 4)
    let Pphysical := fun k : K => preparedFiniteScheduleLocalPhysical (max m cutoff) nX
      (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))))) Qstride (Pk k)
    let target := fun k => detectionGain k + 40 + coefficientErrorSpatialLog (Pphysical k)
    let E := fun s : K => target s + D * (((max m cutoff) * 2 ^ ((max m cutoff) + 1) : ℕ) * Pk s) + 5
    let Prho := fun s : K => 2 * affineProfileInputEnvelope D
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect s + 2) + 2
    let Ptail := fun s : K => affineProfileToleranceEnvelope (max m cutoff) D (D * (D + 1) + D * D + D + 1)
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect s + 2)
    let Pscale := preparedUniformDegreeScaleLog (D + pRadius) Ptail Qσ
    let Tmod := fun s : K => (((max m cutoff) + 1 : ℕ) : ℝ) * Pk s + nX * Qstride
    let lengthLogs := fun s : K => allocatedAffineLengthLog (max m cutoff) D Pscale (Prho s) (Pk s)
      (target s) (pDetect s + 2) (Tmod s)
    let Pseed := allocatedScaleLog (Pscale + ∑ s, lengthLogs s + Pmin + 1)
    let W := physicalBadProductGap ((modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)) * (nX + (max m cutoff) * M)) (gainLog + 8) Vlog Qgood
    let Pmaster := fun k : K => preparedFiniteScheduleLocalMaster Bstruct D pRadius Qstride
      (Pphysical k) (sourceU k) (modelLog k) (Prho k) (target k) (detectionGain k)
    let coarseTarget := preparedFiniteScheduleDirectCoarse detectionGain requestedCoarse
    let Plate := ∑ k : K, preparedUniformDegreeDirectLate (Pmaster k) Pscale
      (Pphysical k) coarseTarget (allocatedWitnessScaleLog Pseed Qw)
    let native : K → ℝ := fun k =>
      (preparedModularGeneralDetectorResources
        (preparedModularGeneralDetectorConstants (max m cutoff) (degree k))
        (degree k + 1) (Pmaster k) Plate).nativeBudget
    let Econditional := preparedNestedFrontProjectionEnvelope A stageCountConstant innerDepth
      (fun k : K => k.1.val) (fun k : K => k.2.1.val) native
      Bstruct gainLog stageLog endpoint
    let τ := Real.exp (-(gainLog + (nX : ℝ) + 8))
    let α := fun k : K => Real.exp (-(2 * preparedFiniteForwardModelPrecision A stageCountConstant
      (preparedFiniteNestedForwardAllDegreeStage k).val
      (preparedFiniteNestedForwardAllDegreeSeed A stageCountConstant Bstruct k) gainLog stageLog +
      4 * modelLog k + 8))
    let baseB0 := preparedUniformDegreeProductiveCertificateBudget M nX pRadius Pscale Pseed Qw (gainLog + 8) Vlog
    let Pwidth := 4 * (Plate + 8) ^ 2
    let Bcert := preparedForecastGoodCertificateBudget baseB0 Bstruct Pwidth gainLog Vlog
    let Pgood := preparedForecastGoodAnalyticBudget (preparedCenteredShortForecastSpatialExponent (max m cutoff))
      baseB0 Bstruct Pwidth gainLog Vlog
    let anchorRequired := preparedFiniteScheduleAnchorGoodRequired (max m cutoff) (Pmaster kModel) Plate Econditional Bcert Pgood Pwidth
    let conditionalRequired := preparedConditionalExcessRequired (max m cutoff) Plate Econditional
    let detectorRequired := fun k : K => (preparedModularGeneralDetectorResources
      (preparedModularGeneralDetectorConstants (max m cutoff) (degree k)) (degree k + 1) (Pmaster k) Plate).required
    let Rreq := preparedFiniteNestedSourceRequired A stageCountConstant innerDepth outerDepth cutoff Bstruct
      anchorRequired conditionalRequired detectorRequired
    pnum ≤ Bstruct →
    (∀ i, Real.exp Rreq ≤ (N i : ℝ)) → Real.exp Rreq ≤ Rrank →
    ∃ (hR : ∀ j, 0 < R j) (σ : ℝ) (hσ : 0 < σ)
      (S : LayerSamplerScale («G» := (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))) («I» := (PreparedSamplerContinuous (prep.pad (max m cutoff)))) («n» := (preparedSamplerTransverse (prep.pad (max m cutoff)))) («J» := (fun j : Fin (max m cutoff) => RankPreparationLayer.Coord ((prep.pad (max m cutoff)) j))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) U b R (fun _ => σ)),
      0 ≤ pRadius ∧ (∀ j, R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧
      σ ≤ 1 ∧ σ ≤ Real.exp (-Qσ) ∧ σ⁻¹ ≤ Real.exp Pscale ∧
      Lmin ≤ S.value ∧ (S.value : ℝ) ≤ Real.exp (allocatedWitnessScaleLog Pseed Qw) ∧
      (∀ j i, S.value ^ (j.val + 1) < basisAxisScale (b j) i →
        8 * (probabilityProfileLipschitz : ℝ) * W ≤
          (layerSamplerGapWidth («G» := (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) R ⟨j, i⟩ / 2) *
            ((basisAxisScale (b j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))) ∧
      (∀ s : K, PreparedUniformDegreeGeometryAt («G» := (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) U b S (degree s) (Cdetect s) nX
        Bstruct Pscale D (target s) (Pk s) (Prho s) Qstride (pDetect s) pRadius (aDetect s) (detectionGain s)) ∧
      (∀ k, PreparedUniformDegreeDirectScalarBounds (max m cutoff) (degree k) nX
        (Fintype.card (LayerSamplerVariables
          (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))
          (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff)))
          (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))))
        (Cdetect k) Bstruct Pscale D (target k) (Pk k) (Prho k) Qstride (Pmaster k) Plate
        (detectionGain k) (Pphysical k) coarseTarget pRadius (sourceU k) (modelLog k) (sliceLog k)) ∧
      (∀ k, PreparedScheduledDirectSourceAvailability
          (B := EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))
          (U := U) (basis := b) (S := S) (hR := hR) (hσ := fun _ => hσ)
          (selection := enlargedPreparedCommonCanonicalSelection (max m cutoff)
            (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)) (degree k) (preparedFiniteNestedForwardAllDegreeDegree_le (Nat.le_max_right m cutoff) k))
          (stride := stride) (N := N) (Pdetect := Pdetect)
          (sourceU := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
          (Vtail := Vtail) (τ := τ) (hb := hb) (o := o)
          Bstruct Qstride (Pmaster k) Plate (detectionGain k) (Pphysical k) coarseTarget) ∧
      (∀ k, PreparedScheduledDegreeModelAvailability
          (B := EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))
          (U := U) (basis := b) (S := S) (hR := hR) (hσ := fun _ => hσ)
          (selection := enlargedPreparedCommonCanonicalSelection (max m cutoff)
            (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)) (degree k)
              (preparedFiniteNestedForwardAllDegreeDegree_le (Nat.le_max_right m cutoff) k))
          (stride := stride) (N := N) (Pdetect := Pdetect)
          (sourceU := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
          (Vtail := Vtail) (τ := τ) (hb := hb) (o := o) (μ := μ)
          Bstruct Qstride (Pmaster k) Plate (detectionGain k) (Pphysical k) coarseTarget) ∧
      PreparedUniformDegreeProductiveSourceConclusion
        (m := (max m cutoff)) (nX := nX) (M := M) (prep := (prep.pad (max m cutoff))) (U := U) (b := b) (S := S)
        (hR := hR) (hσ := fun _ => hσ) (stride := stride) (N := N)
        (Pdetect := Pdetect) (pModel := modelLog kModel) (pSlice := sliceLog kModel)
        (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
        (hb := hb) (o := o) (bW := bW) (μ := μ)
        Bstruct Qstride (Pmaster kModel) Plate (detectionGain kModel) (Pphysical kModel) coarseTarget
        pRadius Pscale Pseed Qw gainLog gain Vlog Qgood ∧
      ∃ (hmargin : ∀ i, 2 * spatialTrimMargin τ N i ≤ N i)
        (Acandidate : AllocatedExternalCandidateSamplerFamily (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) U b S hb o hR (fun _ => hσ)
          N poly hmem τ (Real.exp (-Plate)) stride cells)
        (hξone : Real.exp (-Plate) ≤ 1),
      PreparedCenteredProductiveGoodCenterReadyConclusion (m := (max m cutoff)) (nX := nX) (M := M)
        (prep.pad (max m cutoff)) U b S bW hb o hR (fun _ => hσ) μ poly hmem stride
        (allocatedExternalCandidateWidths (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) U b S N τ (Real.exp (-Plate))) (Acandidate 0).bases
        gainLog gain Qgood (preparedSpatialKernelBlocks (max m cutoff) M nX) Acandidate.law N test
        (fun center =>
          let _ : DecidableEq (Fin nX) := Classical.decEq _
          ((∀ k : K, (Acandidate center).NativeDetection (degree k) (sliceLog k)
            (Pdetect.eval₂ (Nat.castRingHom ℝ) (pDetect k))
            (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants (max m cutoff) (degree k))
              (degree k + 1) (Pmaster k) Plate).nativeBudget (α k)) ∧
          letI : Nonempty (Acandidate center).Site := (Acandidate center).site_nonempty
          (FiniteProbabilityWeights.uniformFinset (integerBox N) (Acandidate center).integerBox_nonempty).excessMass
            ((Acandidate center).law.siteLaw ((Acandidate center).physicalBox hξone hmargin))
            (4 * ∏ j, earlyConstantDensityCap (Fintype.card ((PreparedSamplerContinuous (prep.pad (max m cutoff))) j)) ((preparedSamplerTransverse (prep.pad (max m cutoff))) j) (R j) (Vtail j)) ≤
              6 * positiveProjectionAccuracy Econditional) ∧
          ∀ (outerFront outerInner : Fin (outerDepth + 1)) (d : ℕ),
            ∀ (hd : d ≤ cutoff), d ≤ innerDepth → ∀ (pInput : ℝ),
            pInput ∈ Set.Icc 0 (candidateNestedForwardSeed A stageCountConstant innerDepth outerFront.val Bstruct) →
            pInput ≤ candidateNestedForwardSeed A stageCountConstant innerDepth outerInner.val Bstruct →
            ∃ profile : (Acandidate center).DegreeSourceProfile d pInput e,
              profile.inner.x = candidateNestedForwardSeed A stageCountConstant innerDepth outerInner.val Bstruct ∧
              profile.inner.gainLog = candidateNestedForwardSeed A stageCountConstant innerDepth outerInner.val Bstruct ∧
              profile.front.u = preparedFiniteForwardModelPrecision A stageCountConstant 0
                (candidateNestedForwardSeed A stageCountConstant innerDepth outerFront.val Bstruct) gainLog stageLog ∧
              profile.front.pModel = preparedFiniteForwardWork A stageCountConstant 0
                (candidateNestedForwardSeed A stageCountConstant innerDepth outerFront.val Bstruct) ∧
              profile.front.nativeBudget = native (outerFront, 0, ⟨d, Nat.lt_succ_of_le hd⟩, false) ∧
              profile.inner.Cprimitive = Cprimitive ∧
              profile.inner.scheduleExponent = A ∧
              profile.inner.Csource = preparedFiniteNestedSourceNativeExponent (max m cutoff) cutoff Cdirect) := by
  intro stageCountConstant A Cslice forecastCap Qw Pdetect K degree Cdetect kModel sourceU modelLog sliceLog u p
    pnum R pRadius D pDetect aDetect detectionGain Pk Pphysical target E Prho Ptail Pscale Tmod
    lengthLogs Pseed W Pmaster coarseTarget Plate native Econditional τ α baseB0 Pwidth Bcert Pgood
    anchorRequired conditionalRequired detectorRequired Rreq hnum hNrequired hRankRequired
  have hCB (j) : C j ≤ Real.exp Bstruct :=
    (hCbound j).trans (Real.exp_le_exp.mpr (by linarith only [hchartLog]))
  obtain ⟨hR, σ, hσ, S, hpRadius, hRadiusBounds, hσone, hσQ, hσinv, hSmin, hSmax,
    hgap, hgeometry, hscalars, havailable, hmodels, hproductive, hmargin, Acandidate,
    hξone, hready⟩ := exists_preparedFiniteNestedForwardCanonicalFixedCenterSource
      prep outerDepth innerDepth cutoff U b stride N Vtail Q hb o bW ν μ μrows
      e Cprimitive Cdirect extra stageCountConstant Bstruct Qstride stageLog Econditional
      Qσ Pmin requestedCoarse gainLog gain Vlog Lmin Qgood hm hnX hCoord hB hstage
      hQstride.1 hQσ hPmin hLmin hg hVlog hQgood hQexp hgain hnChart hgChart
      hstride hstrideBound C hC hCB hchart Cforward hforward hForward
      hVtail hVactual hprofile hcutoff cells hCells poly hp hmem Rrank hrank test htest hmean
      hnum hNrequired hRankRequired
  refine ⟨hR, σ, hσ, S, hpRadius, hRadiusBounds, hσone, hσQ, hσinv, hSmin, hSmax,
    hgap, hgeometry, hscalars, havailable, hmodels, hproductive, hmargin, Acandidate,
    hξone, ?_⟩
  apply preparedCenteredProductiveGoodCenterReady_mono
    (prep.pad (max m cutoff)) U b S bW hb o hR (fun _ => hσ) μ poly hmem stride
    _ (Acandidate 0).bases gainLog gain Qgood (preparedSpatialKernelBlocks (max m cutoff) M nX)
    Acandidate.law N test _ _ hready
  intro center hactual
  refine ⟨hactual, ?_⟩
  intro outerFront outerInner d hd hdepth pInput hpFront hpInner
  let _ : DecidableEq (Fin nX) := Classical.decEq _
  obtain ⟨hNative, hexcess⟩ := hactual
  have hcumulative := (preparedFiniteNestedSourceRequired_size_rank A stageCountConstant
    innerDepth outerDepth cutoff Bstruct anchorRequired conditionalRequired detectorRequired
    N Rrank hNrequired hRankRequired).2.2.2 outerInner ⟨d, Nat.lt_succ_of_le hd⟩
  have hτ : τ ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hg, (Nat.cast_nonneg nX : (0 : ℝ) ≤ (nX : ℝ))])
  obtain ⟨hG, htags, hvariables, _hq⟩ :=
    preparedFiniteNestedSource_counts prep nX M cutoff hCoord hnum
  have hdec : Classical.decEq (Fin nX) = (fun a b => Classical.propDecidable (a = b)) :=
    Subsingleton.elim _ _
  rw [hdec] at hNative
  have hNativeEq : preparedFiniteNestedSourceNative (max m cutoff)
      (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))
      (Fintype.card (LayerSamplerVariables
        (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))
        (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff)))
        (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))))
      nX Pdetect A Cdirect stageCountConstant Bstruct pnum Qstride gainLog stageLog Plate = native := by
    funext k
    rfl
  dsimp only [Pdetect, stageCountConstant, pnum] at hNativeEq
  have hcard : Fintype.card (Fin nX) = nX := Fintype.card_fin nX
  obtain ⟨profile, hx, hgain, hu, hpmodel, hnative, hprim, hschedule, hsource⟩ :=
    AllocatedExternalCandidateSampler.exists_preparedFiniteNestedDegreeSourceProfile_of_exponent_fullScalars
    (prep.pad (max m cutoff)) (Acandidate center) outerDepth innerDepth cutoff A Cprimitive Cdirect M
    (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))
    Bstruct gainLog stageLog Qstride Plate Econditional endpoint Rrank extra outerFront outerInner
    (e := e) (p := pInput) (chartLog := chartLog) hd (Nat.le_max_right m cutoff) hdepth le_rfl
    hprimitive hB ⟨hg, hgChart⟩ hstage hQstride (prep.pad_coordinate_card_le hCoord) hnum
    hG htags hvariables hpFront hpInner hξone hmargin Vtail hVtail hprofile hendpoint
    (by rw [hcard, hNativeEq]; exact le_rfl)
    (by rw [hcard, hNativeEq]; exact hNative) hexcess hcumulative.1 hcumulative.2 hrank
    hτ (fun _ => hσone) hp C hC hchart hCbound hchartLog (fun _ => rfl)
  refine ⟨profile, hx, hgain, hu, hpmodel, ?_, hprim, hschedule, hsource⟩
  rw [hcard, hNativeEq] at hnative
  exact hnative

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.exists_preparedFiniteNestedForwardCompleteFixedCenterSource_fullScalars_s2_oai := @OAI.Erdos3.VectorPolynomial.exists_preparedFiniteNestedForwardCompleteFixedCenterSource_fullScalars_s2_oai
