-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.exists_preparedCanonicalInitializedRelativeSource_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T09:29:16.614984+00:00
-- url     : https://prove2.me/submissions/8ed40f06-6b58-4edf-9c4f-94e0e6afc115

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B294
import Theorems.Thm_OAI_Erdos3_PolynomialPatch_LowestLayerModel_returned_fibers_of_productive_padded_relative_induction_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_preparedFiniteNestedForwardCompleteFixedCenterSource_fullScalars_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPatchProductBudget
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

namespace PolynomialPatch

variable {σ : Type*} {s d D E : ℕ}

theorem value_mem_Icc (A : PolynomialPatch σ s d) (t : σ → ℝ) :
    A.value t ∈ Set.Icc (0 : ℝ) 1 := (A.form.slots t).patchValue_mem_Icc A.kernel

end PolynomialPatch

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialSymbolicShearWeightedDegree
namespace OAI

section

namespace Erdos3.PolynomialSlots

open _root_.MvPolynomial

variable {σ τ : Type*} {d : ℕ} {w : Fin d → ℕ}

theorem parameterSubstitution_slot_homogeneous
    (f : σ → MvPolynomial τ ℝ) (i : Fin d) (v : σ ⊕ Fin i.val) :
    (parameterSubstitution f i v).IsWeightedHomogeneous
      (patchSlotWeight w i) (patchSlotWeight w i v) := by
  cases v with
  | inl a =>
    apply aeval_isWeightedHomogeneous (fun _ : τ => 0) (patchSlotWeight w i)
    · intro b
      exact isWeightedHomogeneous_X ℝ _ (Sum.inl b)
    · intro α _
      simp [Finsupp.weight_apply, Finsupp.sum, patchSlotWeight]
  | inr j => exact isWeightedHomogeneous_X ℝ _ (Sum.inr j)

end Erdos3.PolynomialSlots

end

section

namespace Erdos3.PolynomialSlots

open _root_.MvPolynomial

variable {σ τ : Type*} {d : ℕ} {w : Fin d → ℕ}

theorem reparam_topPart_center (A : PolynomialSlots σ d w)
    (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ a, f a ∈ weightedSupportLE (fun _ : τ => 1) 1) (i : Fin d) :
    (A.reparam f hf).topPart.center i =
      aeval (parameterSubstitution f i) (A.topPart.center i) := by
  exact (aeval_weightedHomogeneousComponent (patchSlotWeight w i)
    (patchSlotWeight w i) (parameterSubstitution f i)
    (parameterSubstitution_slot_homogeneous f i) (w i) (A.center i)).symm

theorem reparam_topPart_specializeCenter (A : PolynomialSlots σ d w)
    (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ a, f a ∈ weightedSupportLE (fun _ : τ => 1) 1) (i : Fin d) :
    (A.reparam f hf).topPart.specializeCenter 0 i =
      A.topPart.specializeCenter 0 i := by
  unfold specializeCenter
  rw [A.reparam_topPart_center f hf, MvPolynomial.comp_aeval_apply]
  let q : σ → MvPolynomial (Fin i.val) ℝ := fun a =>
    aeval (Sum.elim (fun _ : τ => 0) X) (parameterSubstitution f i (Sum.inl a))
  have hinput :
      (fun a => aeval (Sum.elim (fun j : τ => C ((0 : τ → ℝ) j)) X)
        (parameterSubstitution f i a)) = Sum.elim q X := by
    funext a
    cases a <;> simp [q, parameterSubstitution]
  rw [hinput]
  exact A.topPart_aeval_independent i q (fun a => C ((0 : σ → ℝ) a)) X

theorem reparam_topResidualEquiv (A : PolynomialSlots σ d w)
    (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ a, f a ∈ weightedSupportLE (fun _ : τ => 1) 1) :
    (A.reparam f hf).topResidualEquiv = A.topResidualEquiv := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply MvPolynomial.algHom_ext
  intro i
  change (A.reparam f hf).topResidualEquiv (X i) = A.topResidualEquiv (X i)
  rw [topResidualEquiv_X, topResidualEquiv_X,
    A.reparam_topPart_specializeCenter f hf]

theorem reparam_specialized_residualHom (A : PolynomialSlots σ d w)
    (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ a, f a ∈ weightedSupportLE (fun _ : τ => 1) 1) (t : τ → ℝ) :
    (patchParameterSpecialization t).comp (A.reparam f hf).residualHom =
      (patchParameterSpecialization (fun a => aeval t (f a))).comp A.residualHom := by
  apply MvPolynomial.algHom_ext
  intro i
  apply MvPolynomial.funext
  intro x
  simp only [AlgHom.comp_apply, ← MvPolynomial.aeval_eq_eval]
  rw [patchParameterSpecialization_eval, patchParameterSpecialization_eval,
    residualHom_X, residualHom_X, residualCoordinate_eval, residualCoordinate_eval,
    reparam_slots]

theorem reparam_loweringAt (A : PolynomialSlots σ d w)
    (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ a, f a ∈ weightedSupportLE (fun _ : τ => 1) 1) (t : τ → ℝ) :
    (A.reparam f hf).loweringAt t = A.loweringAt (fun a => aeval t (f a)) := by
  have hc := (A.reparam f hf).loweringAt_comp_top t
  rw [A.reparam_topResidualEquiv f hf, A.reparam_specialized_residualHom f hf,
    ← A.loweringAt_comp_top] at hc
  apply Subtype.ext
  apply AlgEquiv.coe_toAlgHom_injective
  apply AlgHom.ext
  intro P
  have h := congrArg (fun F : MvPolynomial (Fin d) ℝ →ₐ[ℝ] MvPolynomial (Fin d) ℝ =>
    F (A.topResidualEquiv.symm P)) hc
  simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply] using h

end Erdos3.PolynomialSlots

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedPatchReparam
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

namespace WeightedParameterPatch

variable {σ : Type*} {p : σ → ℕ} {s d : ℕ}

theorem value_mem_Icc (A : WeightedParameterPatch σ p s d) (t : σ → ℝ) :
    A.value t ∈ Set.Icc (0 : ℝ) 1 := (A.form.slots t).patchValue_mem_Icc A.kernel

end WeightedParameterPatch

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RelativePatchAmplification
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem RelativePatchSliceConclusion.mono {X : Type*} [Fintype X] {s : ℕ}
    {N : X → ℕ} {f : (X → ℤ) → ℝ} {target : ℝ} {rankBound rankBound' : ℕ}
    {cost cost' : ℝ} (h : RelativePatchSliceConclusion s N f target rankBound cost)
    (hrank : rankBound ≤ rankBound') (hcost : cost ≤ cost') :
    RelativePatchSliceConclusion s N f target rankBound' cost' := by
  obtain ⟨q, hq, S, d, A, hlength, hd, hcomplexity, hscore⟩ := h
  have he : Real.exp (-cost') ≤ Real.exp (-cost) :=
    Real.exp_le_exp.mpr (neg_le_neg hcost)
  exact ⟨q, hq, S, d, A, fun i =>
    (mul_le_mul_of_nonneg_right he (Nat.cast_nonneg _)).trans (hlength i),
    hd.trans hrank, hcomplexity.trans hcost, he.trans hscore⟩

end Erdos3

end

section

namespace Erdos3

theorem recursive_discount_target_mem_Icc {discount Λ : ℝ}
    (hdiscount : discount ∈ Set.Icc (0 : ℝ) 1) (hΛ : Λ ∈ Set.Icc (0 : ℝ) 1)
    (stage : ℕ) : (1 - discount) ^ (stage + 1) * Λ ∈ Set.Icc (0 : ℝ) 1 := by
  have hbase : 0 ≤ 1 - discount := sub_nonneg.mpr hdiscount.2
  have hbase1 : 1 - discount ≤ 1 := by linarith only [hdiscount.1]
  have hpow : (1 - discount) ^ (stage + 1) ≤ 1 := pow_le_one₀ hbase hbase1
  exact ⟨mul_nonneg (pow_nonneg hbase _) hΛ.1,
    (mul_le_mul hpow hΛ.2 hΛ.1 zero_le_one).trans_eq (one_mul 1)⟩

end Erdos3

end

section

namespace Erdos3

theorem RelativePatchAbsoluteRule.mono {s n₀ d₀ : ℕ} {p p' a Λ : ℝ}
    (h : RelativePatchAbsoluteRule s n₀ p a Λ d₀) (hpp : p ≤ p') :
    RelativePatchAbsoluteRule s n₀ p' a Λ d₀ := by
  intro N hprime hinj hratio hsize f hf hfree hmean
  exact (h N hprime hinj hratio
    (fun i => (Real.exp_le_exp.mpr hpp).trans (hsize i)) f hf hfree hmean).mono le_rfl hpp

end Erdos3

end

section

namespace Erdos3

theorem relativePatchComplexity_kernel_bound {X : Type*} {s d : ℕ}
    (A : PolynomialPatch X s d) {U : ℝ} (hA : relativePatchComplexity A ≤ U) :
    (A.kernel.lip : ℝ) + 1 ≤ Real.exp U := by
  have hlog : Real.log (1 + (A.kernel.lip : ℝ)) ≤ U := by
    unfold relativePatchComplexity at hA
    have := Nat.cast_nonneg (α := ℝ) d
    linarith
  have hpos : 0 < 1 + (A.kernel.lip : ℝ) := by positivity
  have h := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log hpos] at h
  linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RelativePatchBoxRestriction
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem relativeBoxInput_unitInterval {X : Type*} [Fintype X]
    (N : X → ℕ) (f : (X → ℤ) → ℝ)
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1) :
    ∀ x, relativeBoxInput N f x ∈ Set.Icc (0 : ℝ) 1 := by
  intro x
  by_cases hx : x ∈ integerBox N
  · simpa only [relativeBoxInput_eq N f hx] using hf x hx
  · simp only [relativeBoxInput, if_neg hx, Set.mem_Icc]
    constructor <;> norm_num

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

namespace RankPreparationLayer

theorem empty_samplingRank {I J : Type} (d : ℕ) (T : I → ℝ) (R : ℝ) :
    HasLayerSamplingRank d T R (empty : RankPreparationLayer I J).space
      (empty : RankPreparationLayer I J).poly := by
  intro a _ hw
  obtain ⟨w, hw⟩ := hw
  exact (hw (Finset.sum_eq_zero (fun j _ => j.elim))).elim

end RankPreparationLayer

namespace RankPreparationFamily

variable {I J : Type} {m q : ℕ}

theorem pad_samplingRank (L : RankPreparationFamily I J m) (T : I → ℝ) (R : ℝ)
    (hL : ∀ j, HasLayerSamplingRank (j.val + 1) T R (L j).space (L j).poly) :
    ∀ j, HasLayerSamplingRank (j.val + 1) T R (L.pad q j).space
      (L.pad q j).poly := by
  intro j
  by_cases hj : j.val < m
  · rw [pad_apply_lt L j hj]
    exact hL ⟨j.val, hj⟩
  · rw [pad_apply_ge L j (by omega)]
    exact RankPreparationLayer.empty_samplingRank _ _ _

theorem pad_degreeLE (L : RankPreparationFamily I J m)
    (hL : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (L j).poly) :
    ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (L.pad q j).poly := by
  intro j
  by_cases hj : j.val < m
  · rw [pad_apply_lt L j hj]
    exact hL ⟨j.val, hj⟩
  · rw [pad_apply_ge L j (by omega)]
    exact (RankPreparationLayer.empty_valid _ 0 0).1

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

theorem cumulative_le_preparedFiniteNestedSourceRequired_of_le
    (outer degree : ℕ) (houter : outer ≤ outerDepth) (hdegree : degree ≤ cutoff) :
    preparedFiniteForwardCumulative A constants degree
      (candidateNestedForwardSeed A constants innerDepth outer x) ≤
    preparedFiniteNestedSourceRequired A constants innerDepth outerDepth cutoff
      x anchorGoodRequired conditionalRequired detectorRequired :=
  cumulative_le_preparedFiniteNestedSourceRequired A constants innerDepth outerDepth cutoff
    x anchorGoodRequired conditionalRequired detectorRequired
    ⟨outer, Nat.lt_succ_of_le houter⟩ ⟨degree, Nat.lt_succ_of_le hdegree⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

theorem four_le_exp_neg_mul_of_exp_floor {t required value : ℝ}
    (hgap : t + 2 ≤ required) (hfloor : Real.exp required ≤ value) :
    4 ≤ Real.exp (-t) * value := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    linarith [Real.add_one_le_exp (1 : ℝ)]
  have hfour : (4 : ℝ) ≤ Real.exp 2 := by
    calc
      4 = (2 : ℝ) * 2 := by norm_num
      _ ≤ Real.exp 1 * Real.exp 1 :=
        mul_le_mul htwo htwo (by norm_num) (Real.exp_nonneg _)
      _ = Real.exp 2 := by rw [← Real.exp_add]; norm_num
  calc
    4 ≤ Real.exp 2 := hfour
    _ ≤ Real.exp (-t + required) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (-t) * Real.exp required := Real.exp_add _ _
    _ ≤ Real.exp (-t) * value :=
      mul_le_mul_of_nonneg_left hfloor (Real.exp_nonneg _)

theorem preparedFiniteNestedSourceTrimExponential (nX : ℕ) {X : Type*}
    (N : X → ℕ) {gainLog required : ℝ} (hg : 0 ≤ gainLog)
    (hgap : gainLog + (nX : ℝ) + 10 ≤ required)
    (hN : ∀ i, Real.exp required ≤ (N i : ℝ)) :
    let τ := Real.exp (-(gainLog + (nX : ℝ) + 8))
    0 < τ ∧ τ ≤ 1 / 2 ∧ (nX : ℝ) * τ ≤ 1 / 2 ∧
      ∀ i, 4 ≤ τ * (N i : ℝ) := by
  have hwidth := preparedEarlySpatialWidth nX hg
  refine ⟨hwidth.2.1, hwidth.2.2.1, hwidth.2.2.2.1, ?_⟩
  intro i
  exact four_le_exp_neg_mul_of_exp_floor (by linarith) (hN i)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

theorem two_mul_add_ten_le_preparedFiniteForwardCumulative_one
    (A : ℕ) (constants : ℕ → ℕ) {Bstruct : ℝ}
    (hA : 2 ≤ A) (hBstruct : 0 ≤ Bstruct) :
    2 * Bstruct + 10 ≤ preparedFiniteForwardCumulative A constants 1 Bstruct := by
  have hwork := preparedFiniteForwardWork_nonneg A constants 0 hBstruct
  have hbase : 1 ≤ 4 * Bstruct +
      4 * preparedFiniteForwardWork A constants 0 Bstruct + 16 + A := by
    linarith only [hBstruct, hwork, Nat.cast_nonneg (α := ℝ) A]
  have hlinear : 2 * Bstruct + 10 ≤ 4 * Bstruct +
      4 * preparedFiniteForwardWork A constants 0 Bstruct + 16 + A := by
    linarith only [hBstruct, hwork, Nat.cast_nonneg (α := ℝ) A]
  have hpower : 4 * Bstruct + 4 * preparedFiniteForwardWork A constants 0 Bstruct + 16 + A ≤
      (4 * Bstruct + 4 * preparedFiniteForwardWork A constants 0 Bstruct + 16 + A) ^ A := by
    simpa only [pow_one] using pow_le_pow_right₀ hbase (show 1 ≤ A by omega)
  simpa only [preparedFiniteForwardCumulative, Finset.sum_range_one,
    preparedFiniteForwardCap_eq, preparedFiniteForwardParameter_zero] using hlinear.trans hpower

theorem preparedFiniteNestedSourceRequired_trim_log
    {Slot : Type*} [Fintype Slot]
    (A : ℕ) (constants : ℕ → ℕ) (innerDepth outerDepth cutoff : ℕ)
    (Bstruct anchorGoodRequired conditionalRequired : ℝ) (detectorRequired : Slot → ℝ)
    (nX : ℕ) {gainLog : ℝ}
    (hA : 2 ≤ A) (hcutoff : 1 ≤ cutoff) (hBstruct : 0 ≤ Bstruct)
    (hgain : gainLog ≤ Bstruct) (hdimension : (nX : ℝ) ≤ Bstruct) :
    gainLog + (nX : ℝ) + 10 ≤
      preparedFiniteNestedSourceRequired A constants innerDepth outerDepth cutoff Bstruct
        anchorGoodRequired conditionalRequired detectorRequired := by
  have hfirst := two_mul_add_ten_le_preparedFiniteForwardCumulative_one A constants hA hBstruct
  have htotal : preparedFiniteForwardCumulative A constants 1 Bstruct ≤
      preparedFiniteNestedSourceRequired A constants innerDepth outerDepth cutoff Bstruct
        anchorGoodRequired conditionalRequired detectorRequired := by
    simpa only [candidateNestedForwardSeed_zero] using
      cumulative_le_preparedFiniteNestedSourceRequired_of_le
        A constants innerDepth outerDepth cutoff Bstruct
        anchorGoodRequired conditionalRequired detectorRequired 0 1 (Nat.zero_le _) hcutoff
  exact (by linarith only [hgain, hdimension] :
    gainLog + (nX : ℝ) + 10 ≤ 2 * Bstruct + 10).trans (hfirst.trans htotal)

theorem preparedFiniteNestedSourceRequired_trim_bounds
    {Slot X : Type*} [Fintype Slot]
    (A : ℕ) (constants : ℕ → ℕ) (innerDepth outerDepth cutoff : ℕ)
    (Bstruct anchorGoodRequired conditionalRequired : ℝ) (detectorRequired : Slot → ℝ)
    (nX : ℕ) (N : X → ℕ) {gainLog : ℝ}
    (hA : 2 ≤ A) (hcutoff : 1 ≤ cutoff) (hBstruct : 0 ≤ Bstruct)
    (hgain : gainLog ≤ Bstruct) (hdimension : (nX : ℝ) ≤ Bstruct)
    (hg : 0 ≤ gainLog)
    (hN : ∀ i, Real.exp
      (preparedFiniteNestedSourceRequired A constants innerDepth outerDepth cutoff Bstruct
        anchorGoodRequired conditionalRequired detectorRequired) ≤ (N i : ℝ)) :
    let τ := Real.exp (-(gainLog + (nX : ℝ) + 8))
    0 < τ ∧ τ ≤ 1 / 2 ∧ (nX : ℝ) * τ ≤ 1 / 2 ∧
      ∀ i, 4 ≤ τ * (N i : ℝ) := by
  exact preparedFiniteNestedSourceTrimExponential nX N hg
    (preparedFiniteNestedSourceRequired_trim_log A constants innerDepth outerDepth cutoff
      Bstruct anchorGoodRequired conditionalRequired detectorRequired nX
      hA hcutoff hBstruct hgain hdimension) hN

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedRelativeFinalPower
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical NNReal

theorem RelativeReturnedFiberLaw.mono {X : Type*} [Fintype X] [DecidableEq X]
    {keep : X → Prop} [DecidablePred keep] {N : X → ℕ} {cost cost' : ℝ}
    {law : FiniteProbabilityWeights (integerBox N)}
    (h : RelativeReturnedFiberLaw keep N cost law) (hcost : cost ≤ cost') :
    RelativeReturnedFiberLaw keep N cost' law := by
  obtain ⟨fixed, hfixed, q, hq, S, hlen, hlength, hlaw⟩ := h
  refine ⟨fixed, hfixed, q, hq, S, hlen, ?_, hlaw⟩
  intro i
  exact (mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (neg_le_neg hcost)) (Nat.cast_nonneg _)).trans (hlength i)

end Erdos3

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

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped Classical BigOperators

theorem preparedFiniteNestedSource_relative_radius
    {m : ℕ} {X₀ J₀ : Type} (prep : RankPreparationFamily X₀ J₀ m)
    (nX M cutoff : ℕ) {Bstruct Pearly : ℝ}
    (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hB : 0 ≤ Bstruct)
    (hnum : (enlargedPreparedCommonSamplerDimension (max m cutoff) M
      (modularInitialBlockCount (max m cutoff) (nX + max m cutoff * M)) : ℝ) ≤ Bstruct)
    (hEarly : Pearly ≤ Bstruct) :
    ∀ C : Fin (max m cutoff) → ℝ, (∀ j, 0 ≤ C j) →
      (∀ j, C j ≤ Real.exp Pearly) → ∀ j,
      C j * ((Fintype.card (PreparedSamplerContinuous (prep.pad (max m cutoff)) j) : ℝ) + 1) *
        allocatedCommonProductRadius (max m cutoff) Bstruct Bstruct ≤ 1 / 4 := by
  let q := max m cutoff
  let Jalloc := modularInitialBlockCount q (nX + q * M)
  let rows : Fin q → Finset (Finset (Fin 0)) := fun _ => {∅}
  let _ : ∀ j, Nonempty (rows j) := fun _ => ⟨⟨∅, by simp [rows]⟩⟩
  obtain ⟨_, _, hvariables, _⟩ := preparedFiniteNestedSource_counts prep nX M cutoff hCoord hnum
  obtain ⟨_, hI, hn⟩ := enlargedPreparedCommonSampler_dimensions
    (prep.pad q) Jalloc (prep.pad_coordinate_card_le hCoord)
  obtain ⟨_, _, hfam⟩ := (Classical.choose_spec (exists_preparedUniformEarlyRadius q)).2 hB hB
  have hgeo := hfam (G := EnlargedPreparedCommonKernel q Jalloc)
    (EnlargedPreparedCommonSamplerBlock (prep.pad q) Jalloc) rows
    (by simp) hvariables
    (fun j => (Nat.cast_le.mpr (hI j)).trans hnum)
    (fun j => (Nat.cast_le.mpr (hn j)).trans hnum)
  intro C hC hCB
  exact (hgeo.2.2.2.2.2 C hC
    (fun j => (hCB j).trans (Real.exp_le_exp.mpr hEarly))).1

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.FixedPatchShearFiberCandidateScore
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

namespace PolynomialSlots

variable {I : Type*} [Fintype I] [DecidableEq I] {d : ℕ} {w : Fin d → ℕ}

omit [Fintype I] [DecidableEq I] in
theorem coordinateFiberForm_loweringAt_integer (A : PolynomialSlots I d w)
    (keep : I → Prop) [DecidablePred keep] (fixed : {i // ¬keep i} → ℤ)
    (u : {i // keep i} → ℤ) :
    (A.coordinateFiberForm keep fixed).loweringAt (fun i => (u i : ℝ)) =
      A.loweringAt (fun i => ((finiteSplitPoint keep u fixed i : ℤ) : ℝ)) := by
  rw [coordinateFiberForm, reparam_loweringAt]
  congr 1
  funext i
  by_cases hi : keep i <;> simp [coordinateFiberParameters, finiteSplitPoint, hi]

end PolynomialSlots

namespace PolynomialPatch

variable {X I : Type*} [Fintype I] [DecidableEq I] {s d : ℕ}
    (P : PolynomialPatch X s d)

theorem fiberSliceLaw_shear_score_eq_fullSliceLaw
    (A : PolynomialSlots I d P.weight) (keep : I → Prop) [DecidablePred keep]
    {N : I → ℕ} {q : ℕ}
    (S : ResidueBoxSlice (fun i : {i // keep i} => N i.val) q)
    (hlen : ∀ i, 0 < S.length i) (fixed : {i // ¬keep i} → ℤ)
    (hfixed : ∀ i, 0 ≤ fixed i ∧ fixed i < (N i.val : ℤ))
    (f : (I → ℤ) → ℝ) (lam : ℝ) :
    (S.fiberSliceLaw hlen fixed hfixed).mean (fun u => (f u.val - lam) *
      (P.form.shearTransformedSlots P.weight_mono
        (A.loweringAt (fun i => (u.val i : ℝ)))).patchValue P.kernel) =
      (S.fullSliceLaw hlen).mean (fun u => (f (finiteSplitPoint keep u.val fixed) - lam) *
        (P.form.shearTransformedSlots P.weight_mono
          ((A.coordinateFiberForm keep fixed).loweringAt
            (fun i => (u.val i : ℝ)))).patchValue P.kernel) := by
  rw [S.fiberSliceLaw_mean hlen fixed hfixed, S.fullSliceLaw_mean hlen]
  simp only [PolynomialSlots.coordinateFiberForm_loweringAt_integer]
  rfl

end PolynomialPatch

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnconditionedArbitraryFixedPatchFamily
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

theorem exists_allocatedNormalizedShearProblem_of_returned_fiber_laws
    {V : Type*} {s d : ℕ} (keep : LayerSamplerVariables G I n B → Prop)
    (centerLift : ∀ j, U j)
    (hcenter : coefficientConstantCenter U center =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray U (fun a => centerLift a.1))))
    (productive : Finset A.Path) {massThreshold cost scoreThreshold : ℝ}
    (hmass : massThreshold ≤ A.law.mass productive)
    (hsupported : ∀ z : productive, 0 < A.law.weight z.val)
    (sample : productive → CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : productive → AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (hread : ∀ z : productive,
      AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm
        centerLift z.val.1.val z.val.2.val (sample z) (read z))
    (hshort : ∀ i : {i // ¬keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost)
    (patch : PolynomialPatch V s d)
    [Fintype (PolynomialShearIndex patch.weight)]
    (localForm : productive → PolynomialSlots (LayerSamplerVariables G I n B) d patch.weight)
    (law : productive → FiniteProbabilityWeights A.Site)
    (hslice : ∀ z, RelativeReturnedFiberLaw keep A.sides cost (law z))
    (f : (X → ℤ) → ℝ) (lam : ℝ)
    (hscore : ∀ z, scoreThreshold ≤ (law z).mean
      (fun u => (f (A.physical z.val u) - lam) *
        (patch.form.shearTransformedSlots patch.weight_mono
          ((localForm z).loweringAt (fun i => (u.val i : ℝ)))).patchValue patch.kernel)) :
    ∃ P : AllocatedExternalCandidateProblem (E := E) A
      (polynomialShearNilmanifold patch.weight s patch.weight_le)
      (RationalTorus.trivialFiltration s) 0 1
      (fun _ y => (patch.shearObservable y : ℂ))
      (fun x => ((f x - lam : ℝ) : ℂ)) cost massThreshold scoreThreshold,
      P.productive = productive ∧ P.centerLift = centerLift ∧
        ∀ z, (P.chart z).keep = keep := by
  have hcert := hslice
  unfold RelativeReturnedFiberLaw at hcert
  choose fixed hfixed q hq slice hlen hlength hlaw using hcert
  let source : ∀ z : productive,
      AllocatedReturnedPatchSource (E := E) (A := A) keep centerLift z.val := fun z =>
    ⟨hsupported z, sample z, read z, hread z, fixed z, hfixed z⟩
  let keptForm := fun z => (localForm z).coordinateFiberForm keep (fixed z)
  have hkeptScore (z : productive) : scoreThreshold ≤
      ((slice z).fullSliceLaw (hlen z)).mean (fun u =>
        (f ((source z).physical u.val) - lam) *
          (patch.form.shearTransformedSlots patch.weight_mono
            ((keptForm z).loweringAt (fun i => (u.val i : ℝ)))).patchValue patch.kernel) := by
    have hs := hscore z
    rw [hlaw z] at hs
    dsimp only [AllocatedExternalCandidateSampler.physical] at hs
    rw [patch.fiberSliceLaw_shear_score_eq_fullSliceLaw (localForm z) keep
      (slice z) (hlen z) (fixed z) (hfixed z)
      (fun u => f (jointIntegerPhysicalSite u (z.val.1.val, z.val.2.val))) lam] at hs
    have hdec :
        (fun a b : {i // keep i} => Classical.propDecidable (a = b)) =
        (fun a b => @Subtype.instDecidableEq _ keep
          (inferInstance : DecidableEq (LayerSamplerVariables G I n B)) a b) :=
      Subsingleton.elim _ _
    rw [← hdec] at hs
    simpa only [keptForm, AllocatedReturnedPatchSource.physical, source] using hs
  let P := allocatedNormalizedShearProblem keep centerLift hcenter productive hmass
    source hshort patch keptForm q hq slice hlen hlength f lam hkeptScore
  exact ⟨P, rfl, rfl, fun _ => rfl⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

theorem exists_allocatedFixedCenterNormalizedShearProblem
    (s : ℕ) (keep : LayerSamplerVariables G I n B → Prop)
    (centerLift : ∀ j, U j)
    (hcenter : coefficientConstantCenter U center =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray U (fun a => centerLift a.1))))
    (productive : Finset A.Path) (hmass : 0 < A.law.mass productive)
    (hsupported : ∀ z : productive, 0 < A.law.weight z.val)
    (sample : productive → CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : productive → AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (hread : ∀ z : productive,
      AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm
        centerLift z.val.1.val z.val.2.val (sample z) (read z))
    (p cost : ℝ) (hp : 0 ≤ p) (hpcost : p ≤ cost)
    (hshort : ∀ i : {i // ¬keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost)
    (rankBound : ℕ) (f : (X → ℤ) → ℝ) (target : ℝ)
    (htarget : target ∈ Set.Icc (0 : ℝ) 1)
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1) (hξ1 : ξ ≤ 1)
    (hreturned : ∀ z ∈ productive, ∃ (fixed : {i // ¬keep i} → ℤ),
      (∀ i, 0 ≤ fixed i ∧ fixed i < (A.sides i.val : ℤ)) ∧
      RelativePatchSliceConclusion s (fun i : {i // keep i} => A.sides i.val)
        (fun u => f (jointIntegerPhysicalSite (finiteSplitPoint keep u fixed)
          (z.1.val, z.2.val))) target rankBound p) :
    let normalizationPower := (exists_relative_finite_returned_fiber_normalization.{0,0} s).choose
    let q := p + (Fintype.card (LayerSamplerVariables G I n B) : ℝ) + 2
    let D := min rankBound ⌊p⌋₊
    let normalizedBudget := (q + 2) ^ normalizationPower
    let retainedMass := (A.law.mass productive / ((D + 1) * (s + 1) ^ D : ℕ)) *
      Real.exp (-normalizedBudget)
    ∃ (d : ℕ) (patch : PolynomialPatch (LayerSamplerVariables G I n B) s d),
      d ≤ D ∧ d ≤ rankBound ∧
      (patch.kernel.lip : ℝ) ≤ Real.exp normalizedBudget ∧
      (∀ i, realPolynomialMass (patch.form.center i) ≤ normalizedBudget) ∧
      let := polynomialShearIndexFintype patch.weight (fun i => patch.weight_pos i)
      ∃ P : AllocatedExternalCandidateProblem (E := E) A
        (polynomialShearNilmanifold patch.weight s patch.weight_le)
        (RationalTorus.trivialFiltration s) 0 1
        (fun _ y => (patch.shearObservable y : ℂ))
        (fun x => ((f x - target : ℝ) : ℂ)) cost retainedMass (Real.exp (-normalizedBudget)),
        P.productive ⊆ productive ∧ P.centerLift = centerLift ∧
          ∀ z, (P.chart z).keep = keep := by
  intro normalizationPower q D normalizedBudget retainedMass
  have hne : productive.Nonempty := Finset.nonempty_iff_ne_empty.mpr (by
    intro he
    simp only [he, FiniteProbabilityWeights.mass, Finset.sum_empty] at hmass
    linarith)
  let : Nonempty A.Path := hne.to_subtype.map Subtype.val
  let pathInput := fun (z : A.Path) (u : LayerSamplerVariables G I n B → ℤ) =>
    f (jointIntegerPhysicalSite u (z.1.val, z.2.val))
  have hinput : ∀ z u, u ∈ integerBox A.sides → pathInput z u ∈ Set.Icc (0 : ℝ) 1 := by
    intro z u hu
    exact hf _ (A.physical_mem_integerBox hξ1 z ⟨u, hu⟩)
  obtain ⟨localLaw, d, w, hw, Ψ, slots, localForm, retained,
      hd, hdrank, hwpos, hwle, hLip, hslots, hsub, hretained, hslice, hscore⟩ :=
    (exists_relative_finite_returned_fiber_normalization.{0,0} s).choose_spec.2
      A.law productive hmass A.sides keep A.sides_pos p hp target htarget rankBound
      pathInput hinput hreturned
  let patch : PolynomialPatch (LayerSamplerVariables G I n B) s d :=
    ⟨w, hwpos, hwle, hw, slots, Ψ⟩
  let := polynomialShearIndexFintype patch.weight (fun i => patch.weight_pos i)
  obtain ⟨P, hP, hcenterP, hkeep⟩ :=
    exists_allocatedNormalizedShearProblem_of_returned_fiber_laws
      (E := E) (A := A) keep centerLift hcenter retained hretained
      (fun z => hsupported ⟨z.val, hsub z.property⟩)
      (fun z => sample ⟨z.val, hsub z.property⟩)
      (fun z => read ⟨z.val, hsub z.property⟩)
      (fun z => hread ⟨z.val, hsub z.property⟩)
      hshort patch (fun z => localForm z.val) (fun z => localLaw z.val)
      (fun z => (hslice z.val z.property).mono hpcost) f target
      (fun z => hscore z.val z.property)
  exact ⟨d, patch, hd, hdrank, hLip, hslots, P, hP ▸ hsub, hcenterP, hkeep⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RelativePatchSourceTestFinBounds
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem relativePatchSourceTest_abs_le_one {X : Type*} [Fintype X] {s d : ℕ}
    (N : X → ℕ) (f : (X → ℤ) → ℝ) (a : ℝ) (A : PolynomialPatch X s d)
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (y : X → ℝ) :
    |relativePatchSourceTest N f a A y| ≤ 1 := by
  have hinput := relativeBoxInput_unitInterval N f hf (fun i => ⌊y i⌋)
  have hpatch := A.value_mem_Icc y
  have hdiff : |relativeBoxInput N f (fun i => ⌊y i⌋) - a| ≤ 1 :=
    abs_le.mpr ⟨by linarith only [hinput.1, ha.2], by linarith only [hinput.2, ha.1]⟩
  unfold relativePatchSourceTest
  rw [abs_mul, abs_of_nonneg hpatch.1]
  exact (mul_le_mul_of_nonneg_right hdiff hpatch.1).trans (by simpa only [one_mul] using hpatch.2)

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem relativePatchSourceTest_fin_mean {nX s d : ℕ}
    (N : Fin nX → ℕ) (f : (Fin nX → ℤ) → ℝ) (a : ℝ)
    (A : PolynomialPatch (Fin nX) s d) :
    (𝔼 x ∈ integerBox N, relativePatchSourceTest N f a A (fun i => (x i : ℝ))) =
      relativePatchBoxScore N f a A := by
  unfold relativePatchBoxScore
  apply Finset.expect_congr rfl
  intro x hx
  rw [relativePatchSourceTest_integer,
    relativeBoxInput_eq N f (by simpa only [mem_integerBox] using hx)]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

attribute [local irreducible] integerBox

theorem relativePatchSourceTest_fin_productive_data_of_box {nX s d : ℕ}
    (N : Fin nX → ℕ) (f : (Fin nX → ℤ) → ℝ) (a : ℝ)
    (A : PolynomialPatch (Fin nX) s d)
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (ha : a ∈ Set.Icc (0 : ℝ) 1) {gain : ℝ}
    (hscore : gain ≤ relativePatchBoxScore N f a A) :
    (∀ y, |relativePatchSourceTest N f a A y| ≤ 1) ∧
      gain ≤ 𝔼 x ∈ integerBox N,
        relativePatchSourceTest N f a A (fun i => (x i : ℝ)) := by
  refine ⟨relativePatchSourceTest_abs_le_one N f a A ?_ ha, ?_⟩
  · intro x hx
    exact hf x (by simpa only [mem_integerBox] using hx)
  · rwa [relativePatchSourceTest_fin_mean]

theorem relativePatchSourceTrim_bounds {gainLog : ℝ} (hgainLog : 0 ≤ gainLog)
    (nX : ℕ) :
    0 < Real.exp (-(gainLog + (nX : ℝ) + 8)) ∧
      Real.exp (-(gainLog + (nX : ℝ) + 8)) ≤ 1 / 2 := by
  refine ⟨Real.exp_pos _, ?_⟩
  rw [Real.exp_neg, ← one_div]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  have h := Real.add_one_le_exp (gainLog + (nX : ℝ) + 8)
  have hnX : 0 ≤ (nX : ℝ) := Nat.cast_nonneg _
  linarith only [h, hgainLog, hnX]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedProductivePaddedRelativeInitialization
namespace OAI

section

namespace Erdos3.PolynomialPatch.LowestLayerModel
open VectorPolynomial Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators TensorProduct Classical

variable {m q s D E nX : ℕ} {G : Type} [Fintype G] [Nonempty G]
variable (L : RankPreparationFamily (Fin nX) (Fin D) m) (hmq : m ≤ q)
variable {I Deck : Fin q → Type} [∀ j, Fintype (I j)]
variable {n : Fin q → ℕ} (B : LayerSamplerAxis I n → Type) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ ((L.pad q j).Coord → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin q → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable [∀ j, IsZLattice ℝ (latticeSection
  (standardEuclideanLattice (L.pad q j).Coord) (euclideanSubspace (U j)))]
local notation "Vars" => LayerSamplerVariables G I n B

include hmq in

theorem exists_normalizedProblem_of_productive_padded_relative_induction
    {oldPatch : PolynomialPatch (Fin nX) s (D + E)} (F : oldPatch.LowestLayerModel m)
    (ip : Fin D → MvPolynomial (Fin nX) ℤ) (hip : ∀ i, (ip i).totalDegree ≤ m)
    (c₀ : Fin D → ℝ) (err : VectorPolynomial (Fin nX) ℝ (Fin D → ℝ))
    (hprepare : VectorPolynomial.ofCoordinates (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin =
      L.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c₀) + err)
    (hm : ∀ j d, coefficients (L.pad q j).poly d ∈ U j)
    (hp : ∀ j, DegreeLE (1 : Fin nX → ℕ) (j.val + 1) (L.pad q j).poly)
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin q → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (N : Fin nX → ℕ) {τ ξ : ℝ} (hτhalf : τ ≤ 1 / 2) (hξ1 : ξ ≤ 1)
    (hsize : ∀ x, 4 ≤ τ * (N x : ℝ))
    (stride : Fin nX → ℕ)
    (cells : Finset (ColumnResiduePattern (Option Vars) (Fin nX) stride))
    (center : CoefficientTorus (K := Vars) U)
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N
      (fun j => (L.pad q j).poly) hm τ ξ stride cells center)
    (centerLift : ∀ j, U j)
    (hcenter : coefficientConstantCenter U center =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray U (fun a => centerLift a.1))))
    (productive : Finset A.Path) (hmass : 0 < A.law.mass productive)
    (hsupported : ∀ z : productive, 0 < A.law.weight z.val)
    (sample : productive → CoefficientSamplerArrays (K := Vars) I n)
    (read : productive → AllocatedActualCoefficientIndex G (Fin nX) I Deck n B → ℤ)
    (hread : ∀ z : productive,
      AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ
        (fun j => (L.pad q j).poly) hm centerLift z.val.1.val z.val.2.val (sample z) (read z))
    {δ gain : ℝ} (hδ : 0 ≤ δ) (hgain : 0 < gain) (hgain1 : gain ≤ 1)
    (herr : ∀ x ∈ integerBox N, ∀ i, |eval (fun z => (x z : ℝ)) err i| ≤ δ)
    {p Pearly : ℝ} (hp0 : 0 ≤ p)
    (hDlog : (D : ℝ) ≤ Real.exp p) (hqlog : (q : ℝ) ≤ Real.exp p)
    (hLlog : (oldPatch.kernel.lip : ℝ) ≤ Real.exp p)
    (hNlog : ∀ j, (Fintype.card (L.pad q j).Coord : ℝ) ≤ Real.exp p)
    (hClog : ∀ j, C j ≤ Real.exp p) (hgainlog : Real.exp (-p) ≤ gain)
    (hδearly : δ ≤ Real.exp (-(3 * p + 130)))
    (hPearly : 6 * p + 35 ≤ Pearly)
    (hearly : ∀ C' : Fin q → ℝ, (∀ j, 0 ≤ C' j) →
      (∀ j, C' j ≤ Real.exp Pearly) →
      ∀ j, C' j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {n₀ stage d₀ : ℕ} {discount : ℝ} {cutoff childCost : ℝ → ℝ}
    (ih : RelativePatchInductionRule s n₀ stage discount cutoff childCost)
    {pchild a Λ : ℝ} (hp2 : 2 ≤ p) (hpchild : p + 2 ≤ pchild)
    (ha : Real.exp (-p) ≤ a) (haΛ : a ≤ Λ) (hΛ : Λ ≤ 1)
    (habsolute : RelativePatchAbsoluteRule s n₀ p a Λ d₀)
    (hDim : (Fintype.card Vars : ℝ) ≤ pchild)
    (H : ℕ) (hH : H ≤ S.value) (hHcut : Real.exp (cutoff pchild) ≤ H)
    (hDpos : 0 < D) (hrest : ∀ i : Fin E, m < oldPatch.weight (i.natAdd D))
    (hA : relativePatchComplexity oldPatch ≤ pchild)
    (hstage : relativePatchDistinctWeights oldPatch ≤ stage + 1)
    (f : (Fin nX → ℤ) → ℝ)
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2))
    (hproductive : ∀ z : productive,
      AllocatedPathProductivity B U b S N A.widths A.bases
        (relativePatchSourceTest N f a oldPatch) gain z.val)
    (hdiscount : discount ∈ Set.Icc (0 : ℝ) 1)
    (hchildCost : 0 ≤ childCost pchild) (initialCost : ℝ)
    (hCost : childCost pchild ≤ initialCost) (hHcost : (H : ℝ) ≤ Real.exp initialCost) :
    let normalizationPower := (exists_relative_finite_returned_fiber_normalization.{0,0} s).choose
    let Qnorm := childCost pchild + (Fintype.card Vars : ℝ) + 2
    let Dnorm := min (d₀ + s * E) ⌊childCost pchild⌋₊
    let normalizedBudget := (Qnorm + 2) ^ normalizationPower
    let retainedMass := (A.law.mass productive / ((Dnorm + 1) * (s + 1) ^ Dnorm : ℕ)) *
      Real.exp (-normalizedBudget)
    ∃ (d : ℕ) (patch : PolynomialPatch Vars s d),
      d ≤ Dnorm ∧ d ≤ d₀ + s * E ∧
      (patch.kernel.lip : ℝ) ≤ Real.exp normalizedBudget ∧
      (∀ i, realPolynomialMass (patch.form.center i) ≤ normalizedBudget) ∧
      let := polynomialShearIndexFintype patch.weight (fun i => patch.weight_pos i)
      ∃ P : AllocatedExternalCandidateProblem (E := Deck) A
        (polynomialShearNilmanifold patch.weight s patch.weight_le)
        (RationalTorus.trivialFiltration s) 0 1
        (fun _ y => (patch.shearObservable y : ℂ))
        (fun x => ((f x - (1 - discount) ^ (stage + 1) * Λ : ℝ) : ℂ))
        initialCost retainedMass (Real.exp (-normalizedBudget)),
        P.productive ⊆ productive ∧ P.centerLift = centerLift ∧
          ∀ z, (P.chart z).keep = fun k => H ≤ A.sides k := by
  classical
  have htarget := recursive_discount_target_mem_Icc hdiscount
    ⟨(Real.exp_pos (-p)).le.trans (ha.trans haΛ), hΛ⟩ stage
  have hreturned := F.returned_fibers_of_productive_padded_relative_induction_s2
    (I := I) (Deck := Deck) (n := n) L hmq B U b hb o S hR hσ ip hip c₀ err hprepare hm hp hσ1 C hC hchart
    N hτhalf hξ1 hsize stride cells center A centerLift productive
    sample read hread hδ hgain hgain1 herr hp0 hDlog hqlog hLlog hNlog hClog hgainlog
    hδearly hPearly hearly ih hp2 hpchild ha haΛ hΛ habsolute hDim H hH hHcut hDpos
    hrest hA hstage f hf hfree hproductive
  have hdec : (fun k : Vars => H.decLe (A.sides k)) =
      (fun k : Vars => Classical.propDecidable (H ≤ A.sides k)) := Subsingleton.elim _ _
  rw [hdec] at hreturned
  exact exists_allocatedFixedCenterNormalizedShearProblem (A := A) (E := Deck)
    s (fun k => H ≤ A.sides k) centerLift hcenter productive hmass hsupported
    sample read hread (childCost pchild) initialCost hchildCost hCost
    (fun i => (Nat.cast_le.mpr (Nat.le_of_lt (Nat.lt_of_not_ge i.property))).trans hHcost)
    (d₀ + s * E) f ((1 - discount) ^ (stage + 1) * Λ) htarget (fun x hx => hf x (by simpa only [mem_integerBox] using hx)) hξ1 hreturned

end Erdos3.PolynomialPatch.LowestLayerModel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedReadyPaddedRelativeInitialization
namespace OAI

section

namespace Erdos3.PolynomialPatch.LowestLayerModel
open VectorPolynomial Module Submodule MeasureTheory BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators TensorProduct Classical

variable {m q s D E nX Mslot : ℕ}
variable (L : RankPreparationFamily (Fin nX) (Fin D) m) (hmq : m ≤ q)
variable {Deck : Fin q → Type} [∀ j, Fintype (Deck j)]
variable (U : ∀ j, Submodule ℝ ((L.pad q j).Coord → ℝ))
variable (b : ∀ j, Basis (Fin ((preparedSamplerTransverse (L.pad q)) j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis ((PreparedSamplerContinuous (L.pad q)) j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin q → ℝ} (S : LayerSamplerScale (G := (EnlargedPreparedCommonKernel q (modularInitialBlockCount q (nX + q * Mslot)))) (EnlargedPreparedCommonSamplerBlock (L.pad q) (modularInitialBlockCount q (nX + q * Mslot))) U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable [∀ j, IsZLattice ℝ (latticeSection
  (standardEuclideanLattice (L.pad q j).Coord) (euclideanSubspace (U j)))]

variable (bW : ∀ j, Basis (Deck j) ℤ
  (latticeSection (standardEuclideanLattice (L.pad q j).Coord) (euclideanSubspace (U j))))
variable [MeasurableSpace (CoefficientTorus (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel q (modularInitialBlockCount q (nX + q * Mslot))) (PreparedSamplerContinuous (L.pad q)) (preparedSamplerTransverse (L.pad q)) (EnlargedPreparedCommonSamplerBlock (L.pad q) (modularInitialBlockCount q (nX + q * Mslot))))) U)]
variable (μ : Measure (CoefficientTorus (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel q (modularInitialBlockCount q (nX + q * Mslot))) (PreparedSamplerContinuous (L.pad q)) (preparedSamplerTransverse (L.pad q)) (EnlargedPreparedCommonSamplerBlock (L.pad q) (modularInitialBlockCount q (nX + q * Mslot))))) U))

include hmq in

theorem exists_normalizedProblem_of_preparedReady_relative_induction
    {oldPatch : PolynomialPatch (Fin nX) s (D + E)} (F : oldPatch.LowestLayerModel m)
    (ip : Fin D → MvPolynomial (Fin nX) ℤ) (hip : ∀ i, (ip i).totalDegree ≤ m)
    (c₀ : Fin D → ℝ) (err : VectorPolynomial (Fin nX) ℝ (Fin D → ℝ))
    (hprepare : VectorPolynomial.ofCoordinates (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin =
      L.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c₀) + err)
    (hm : ∀ j d, coefficients (L.pad q j).poly d ∈ U j)
    (hp : ∀ j, DegreeLE (1 : Fin nX → ℕ) (j.val + 1) (L.pad q j).poly)
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin q → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (N : Fin nX → ℕ) {τ ξ : ℝ} (hτhalf : τ ≤ 1 / 2) (hξ1 : ξ ≤ 1)
    (hsize : ∀ x, 4 ≤ τ * (N x : ℝ))
    (stride : Fin nX → ℕ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel q (modularInitialBlockCount q (nX + q * Mslot))) (PreparedSamplerContinuous (L.pad q)) (preparedSamplerTransverse (L.pad q)) (EnlargedPreparedCommonSamplerBlock (L.pad q) (modularInitialBlockCount q (nX + q * Mslot))))) (Fin nX) stride))
    (Acandidate : AllocatedExternalCandidateSamplerFamily (EnlargedPreparedCommonSamplerBlock (L.pad q) (modularInitialBlockCount q (nX + q * Mslot))) U b S hb o hR hσ N
      (fun j => (L.pad q j).poly) hm τ ξ stride cells)
    {δ gain : ℝ} (hδ : 0 ≤ δ) (hgain : 0 < gain) (hgain1 : gain ≤ 1)
    (herr : ∀ x ∈ integerBox N, ∀ i, |eval (fun z => (x z : ℝ)) err i| ≤ δ)
    {p Pearly : ℝ} (hp0 : 0 ≤ p)
    (hDlog : (D : ℝ) ≤ Real.exp p) (hqlog : (q : ℝ) ≤ Real.exp p)
    (hLlog : (oldPatch.kernel.lip : ℝ) ≤ Real.exp p)
    (hNlog : ∀ j, (Fintype.card (L.pad q j).Coord : ℝ) ≤ Real.exp p)
    (hClog : ∀ j, C j ≤ Real.exp p) (hgainlog : Real.exp (-p) ≤ gain)
    (hδearly : δ ≤ Real.exp (-(3 * p + 130)))
    (hPearly : 6 * p + 35 ≤ Pearly)
    (hearly : ∀ C' : Fin q → ℝ, (∀ j, 0 ≤ C' j) →
      (∀ j, C' j ≤ Real.exp Pearly) →
      ∀ j, C' j * ((Fintype.card ((PreparedSamplerContinuous (L.pad q)) j) : ℝ) + 1) * R j ≤ 1 / 4)
    {n₀ stage d₀ : ℕ} {discount : ℝ} {cutoff childCost : ℝ → ℝ}
    (ih : RelativePatchInductionRule s n₀ stage discount cutoff childCost)
    {pchild a Λ : ℝ} (hp2 : 2 ≤ p) (hpchild : p + 2 ≤ pchild)
    (ha : Real.exp (-p) ≤ a) (haΛ : a ≤ Λ) (hΛ : Λ ≤ 1)
    (habsolute : RelativePatchAbsoluteRule s n₀ p a Λ d₀)
    (hDim : (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel q (modularInitialBlockCount q (nX + q * Mslot))) (PreparedSamplerContinuous (L.pad q)) (preparedSamplerTransverse (L.pad q)) (EnlargedPreparedCommonSamplerBlock (L.pad q) (modularInitialBlockCount q (nX + q * Mslot)))) : ℝ) ≤ pchild)
    (H : ℕ) (hH : H ≤ S.value) (hHcut : Real.exp (cutoff pchild) ≤ H)
    (hDpos : 0 < D) (hrest : ∀ i : Fin E, m < oldPatch.weight (i.natAdd D))
    (hA : relativePatchComplexity oldPatch ≤ pchild)
    (hstage : relativePatchDistinctWeights oldPatch ≤ stage + 1)
    (f : (Fin nX → ℤ) → ℝ)
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2))
    (hdiscount : discount ∈ Set.Icc (0 : ℝ) 1)
    (hchildCost : 0 ≤ childCost pchild) (initialCost : ℝ)
    (hCost : childCost pchild ≤ initialCost) (hHcost : (H : ℝ) ≤ Real.exp initialCost)
    (gainLog : ℝ) (Qgood : ℕ) (eReady : Fin 2 × Fin nX ↪ (EnlargedPreparedCommonKernel q (modularInitialBlockCount q (nX + q * Mslot))))
    (Ready : CoefficientTorus (K := (LayerSamplerVariables (EnlargedPreparedCommonKernel q (modularInitialBlockCount q (nX + q * Mslot))) (PreparedSamplerContinuous (L.pad q)) (preparedSamplerTransverse (L.pad q)) (EnlargedPreparedCommonSamplerBlock (L.pad q) (modularInitialBlockCount q (nX + q * Mslot))))) U → Prop)
    (hready : PreparedCenteredProductiveGoodCenterReadyConclusion
      (m := q) (nX := nX) (M := Mslot) (L.pad q) U b S bW hb o hR hσ μ
      (fun j => (L.pad q j).poly) hm stride
      (allocatedExternalCandidateWidths (EnlargedPreparedCommonSamplerBlock (L.pad q) (modularInitialBlockCount q (nX + q * Mslot))) U b S N τ ξ) (Acandidate 0).bases
      gainLog gain Qgood eReady Acandidate.law N (relativePatchSourceTest N f a oldPatch) Ready) :
    PreparedCenteredProductiveGoodCenterEnhancedConclusion
      (m := q) (nX := nX) (M := Mslot) (L.pad q) U b S bW hb o hR hσ μ
      (fun j => (L.pad q j).poly) hm stride
      (allocatedExternalCandidateWidths (EnlargedPreparedCommonSamplerBlock (L.pad q) (modularInitialBlockCount q (nX + q * Mslot))) U b S N τ ξ) (Acandidate 0).bases
      gainLog gain Qgood eReady Acandidate.law N (relativePatchSourceTest N f a oldPatch) Ready
      (fun center centerLift productive =>
        AllocatedNormalizedCandidateConclusion (E := Deck) (A := Acandidate center)
          s (fun k => H ≤ (Acandidate center).sides k) centerLift productive
          (childCost pchild) initialCost (d₀ + s * E) f ((1 - discount) ^ (stage + 1) * Λ)) := by
  classical
  let : Nonempty (EnlargedPreparedCommonKernel q (modularInitialBlockCount q (nX + q * Mslot))) := ⟨enlargedPreparedCommonCanonicalSelection q
    (modularInitialBlockCount q (nX + q * Mslot)) 0 (Nat.zero_le q) 0⟩
  unfold PreparedCenteredProductiveGoodCenterReadyConclusion at hready
  unfold PreparedCenteredProductiveGoodCenterEnhancedConclusion
  obtain ⟨c, hc, hcenter, sample, read, hglobal, hfinite⟩ := hready
  refine ⟨c, hc, hcenter, sample, read, hglobal, ?_⟩
  intro primes hprime
  let : ∀ p : primes, NeZero p.val := fun p => ⟨(hprime p.val p.property).ne_zero⟩
  intro depth hdepth
  obtain ⟨center, productive, hReady, hmass, hF⟩ := hfinite primes hprime depth hdepth
  refine ⟨center, productive, hReady, hmass, hF, ?_⟩
  have hmasspos : 0 < (Acandidate center).law.mass productive :=
    lt_trans (div_pos hgain (by norm_num)) hmass
  have hdecG : instDecidableEqFin
      ((q + 1) * (q + 3) + (q + 1) * modularInitialBlockCount q (nX + q * Mslot)) =
      (fun a b => Classical.propDecidable (a = b)) := Subsingleton.elim _ _
  have hinit := F.exists_normalizedProblem_of_productive_padded_relative_induction
    (m := m) (q := q) (s := s) (D := D) (E := E) (nX := nX) (Deck := Deck)
    (R := R) (σ := σ) (τ := τ) (ξ := ξ) (δ := δ) (gain := gain)
    (p := p) (Pearly := Pearly) (n₀ := n₀) (stage := stage) (d₀ := d₀)
    (discount := discount) (cutoff := cutoff) (childCost := childCost)
    (pchild := pchild) (a := a) (Λ := Λ)
    L hmq (EnlargedPreparedCommonSamplerBlock (L.pad q) (modularInitialBlockCount q (nX + q * Mslot))) U b hb o S hR hσ ip hip c₀ err hprepare hm hp hσ1 C hC hchart
    N hτhalf hξ1 hsize stride cells center (Acandidate center)
    (c center) (hcenter center) productive hmasspos
    (fun z => (hF z.val z.property).1)
    (fun z => sample center z.val.1.val z.val.2.val)
    (fun z => allocatedJointFrameRead z.val.1.val (read center z.val.1.val z.val.2.val))
    (fun z => (hF z.val z.property).2.2.2.1)
    hδ hgain hgain1 herr hp0 hDlog hqlog hLlog hNlog hClog hgainlog hδearly hPearly hearly
    ih hp2 hpchild ha haΛ hΛ habsolute hDim H hH hHcut hDpos hrest hA hstage f hf hfree
    (fun z => by
      have hz := (hF z.val z.property).2.1
      rw [hdecG] at hz
      exact hz) hdiscount hchildCost initialCost hCost hHcost
  exact hinit

end Erdos3.PolynomialPatch.LowestLayerModel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedRelativeInitializerScalarInputs
namespace OAI

section

namespace Erdos3

open VectorPolynomial

theorem preparationCoordinateCap_mono {m s D t T : ℕ}
    (hms : m ≤ s) (htT : t ≤ T) :
    preparationCoordinateCap m D t ≤ preparationCoordinateCap s D T := by
  have hpow : (t + 1) ^ m ≤ (T + 1) ^ s :=
    (Nat.pow_le_pow_left (Nat.add_le_add_right htT 1) m).trans
      (Nat.pow_le_pow_right (by omega) hms)
  have hprod := Nat.mul_le_mul_left D hpow
  unfold preparationCoordinateCap
  omega

variable {m s D nX : ℕ}

theorem preparedRelativeInitializer_padded_coordinate_card_le
    (prep : RankPreparationFamily (Fin nX) (Fin D) m) (hms : m ≤ s)
    (hcoord : ∀ j, Fintype.card (prep j).Coord ≤
      preparationCoordinateCap m D (m * D)) :
    ∀ j, Fintype.card (prep.pad (max m s) j).Coord ≤
      preparationCoordinateCap s D (s * D) := by
  apply prep.pad_coordinate_card_le
  intro j
  exact (hcoord j).trans
    (preparationCoordinateCap_mono hms (Nat.mul_le_mul_right D hms))

theorem preparedRelativeInitializerVariableCount_le
    (prep : RankPreparationFamily (Fin nX) (Fin D) m) (hms : m ≤ s)
    {M : ℕ} (hcoord : ∀ j, Fintype.card (prep j).Coord ≤ M) :
    preparedRelativeInitializerVariableCount prep s M ≤
      enlargedPreparedCommonSamplerDimension s M
        (modularInitialBlockCount s (nX + s * M)) := by
  have hdim := (enlargedPreparedCommonSampler_dimensions
    (prep.pad (max m s))
    (modularInitialBlockCount (max m s) (nX + max m s * M))
    (prep.pad_coordinate_card_le hcoord)).1
  calc
    preparedRelativeInitializerVariableCount prep s M ≤
        enlargedPreparedCommonSamplerDimension (max m s) M
          (modularInitialBlockCount (max m s) (nX + max m s * M)) := hdim
    _ = _ := by rw [max_eq_right hms]

theorem preparedRelativeInitializerVariableCount_le_dimension
    (prep : RankPreparationFamily (Fin nX) (Fin D) m) (hms : m ≤ s)
    (hcoord : ∀ j, Fintype.card (prep j).Coord ≤
      preparationCoordinateCap m D (m * D)) :
    let M := preparationCoordinateCap s D (s * D)
    preparedRelativeInitializerVariableCount prep s M ≤
      enlargedPreparedCommonSamplerDimension s M
        (modularInitialBlockCount s (nX + s * M)) := by
  apply preparedRelativeInitializerVariableCount_le prep hms
  intro j
  exact (hcoord j).trans
    (preparationCoordinateCap_mono hms (Nat.mul_le_mul_right D hms))

end Erdos3

end

section

namespace Erdos3
open VectorPolynomial

theorem preparedRelativeInitializer_scalarInputs_of_bounds
    {X : Type*} {s D E q M variableCount n₀ d₀ : ℕ}
    (oldPatch : PolynomialPatch X s (D + E)) (coordinates : Fin q → ℕ)
    {p pRelative precisionBudget chartLog a Λ : ℝ}
    (hp : 2 ≤ p) (hpp : p ≤ pRelative)
    (hq : (q : ℝ) ≤ pRelative) (hM : (M : ℝ) ≤ pRelative)
    (hcoordinates : ∀ j, coordinates j ≤ M)
    (hvariableCount : (variableCount : ℝ) ≤ pRelative)
    (hchart : chartLog + 1 ≤ pRelative)
    (hprecision : 3 * pRelative + 130 ≤ precisionBudget)
    (hcomplexity : relativePatchComplexity oldPatch ≤ p)
    (ha : Real.exp (-p) ≤ a)
    (habsolute : RelativePatchAbsoluteRule s n₀ p a Λ d₀) :
    PreparedRelativeInitializerScalarInputs oldPatch coordinates variableCount
      p pRelative precisionBudget chartLog a Λ n₀ d₀ := by
  have hRexp : pRelative ≤ Real.exp pRelative :=
    (by linarith : pRelative ≤ pRelative + 1).trans (Real.add_one_le_exp pRelative)
  have hD : (D : ℝ) ≤ p := by
    have hrank := (relativePatchComplexity_rank_le oldPatch).trans hcomplexity
    simp only [Nat.cast_add] at hrank
    linarith only [hrank, Nat.cast_nonneg (α := ℝ) E]
  have hkernel := relativePatchComplexity_kernel_bound oldPatch hcomplexity
  have hgain : Real.exp (-pRelative) ≤ Real.exp (-p) :=
    Real.exp_le_exp.mpr (neg_le_neg hpp)
  refine ⟨hp.trans hpp, (hD.trans hpp).trans hRexp, hq.trans hRexp,
    ?_, ?_, ?_, hgain, Real.exp_le_exp.mpr (neg_le_neg hprecision), le_rfl,
    hgain.trans ha, habsolute.mono hpp, ?_, ?_, ?_, (Real.exp_pos _).le⟩
  · exact (by linarith only [hkernel] : (oldPatch.kernel.lip : ℝ) ≤ Real.exp p).trans
      (Real.exp_le_exp.mpr hpp)
  · intro j
    exact ((Nat.cast_le.mpr (hcoordinates j)).trans hM).trans hRexp
  · intro _
    exact Real.exp_le_exp.mpr (by linarith only [hchart])
  · linarith only [hvariableCount]
  · exact hcomplexity.trans (by linarith only [hpp])
  · exact Real.exp_le_one_iff.mpr (by linarith only [hp])

theorem preparedRelativeInitializer_scalarInputs
    {nX s D E m n₀ d₀ : ℕ}
    (oldPatch : PolynomialPatch (Fin nX) s (D + E))
    (prep : RankPreparationFamily (Fin nX) (Fin D) m)
    {p pRelative precisionBudget a Λ : ℝ}
    (hp : 2 ≤ p) (hms : m ≤ s)
    (hcoord : ∀ j, Fintype.card (prep j).Coord ≤
      preparationCoordinateCap m D (m * D))
    (hstructure :
      let M := preparationCoordinateCap s D (s * D)
      let Jalloc := modularInitialBlockCount s (nX + s * M)
      let dim := enlargedPreparedCommonSamplerDimension s M Jalloc
      p ≤ pRelative ∧ (s : ℝ) + 3 ≤ pRelative ∧
        (M : ℝ) ≤ pRelative ∧ (Jalloc : ℝ) ≤ pRelative ∧
        (dim : ℝ) ≤ pRelative ∧ allocatedUniformChartLog (M : ℝ) + 1 ≤ pRelative)
    (hprecision : 3 * pRelative + 130 ≤ precisionBudget)
    (hcomplexity : relativePatchComplexity oldPatch ≤ p)
    (ha : Real.exp (-p) ≤ a)
    (habsolute : RelativePatchAbsoluteRule s n₀ p a Λ d₀) :
    let M := preparationCoordinateCap s D (s * D)
    PreparedRelativeInitializerScalarInputs oldPatch
      (fun j => Fintype.card (prep.pad (max m s) j).Coord)
      (preparedRelativeInitializerVariableCount prep s M)
      p pRelative precisionBudget (allocatedUniformChartLog (M : ℝ)) a Λ n₀ d₀ := by
  obtain ⟨hpp, hs, hM, _hJalloc, hdim, hchart⟩ := hstructure
  refine preparedRelativeInitializer_scalarInputs_of_bounds oldPatch _ hp hpp
    ?_ hM (preparedRelativeInitializer_padded_coordinate_card_le prep hms hcoord)
    ?_ hchart hprecision hcomplexity ha habsolute
  · rw [max_eq_right hms]
    linarith only [hs]
  · exact (Nat.cast_le.mpr
      (preparedRelativeInitializerVariableCount_le_dimension prep hms hcoord)).trans hdim

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedCanonicalRelativeEndpointBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

theorem preparedCanonicalRelative_scalarInputs
    {nX m s D : ℕ} (prep : RankPreparationFamily (Fin nX) (Fin D) m)
    {p pRelative Bstruct : ℝ}
    (hsize : prep.Sized D (m * D)) (hms : m ≤ s) (hp : 2 ≤ p)
    (hstructure :
      let M := preparationCoordinateCap s D (s * D)
      let Jalloc := modularInitialBlockCount s (nX + s * M)
      let dim := enlargedPreparedCommonSamplerDimension s M Jalloc
      p ≤ pRelative ∧ (s : ℝ) + 3 ≤ pRelative ∧
        (M : ℝ) ≤ pRelative ∧ (Jalloc : ℝ) ≤ pRelative ∧
        (dim : ℝ) ≤ pRelative ∧ allocatedUniformChartLog (M : ℝ) + 1 ≤ pRelative)
    (hBrelative : 6 * pRelative + 35 ≤ Bstruct) :
    PreparedCanonicalRelativeScalarInputs prep s p pRelative Bstruct := by
  let q := max m s
  let M := preparationCoordinateCap q D (s * D)
  let Jalloc := modularInitialBlockCount q (nX + q * M)
  have hq : q = s := max_eq_right hms
  have hcoord : ∀ j, Fintype.card (prep j).Coord ≤ preparationCoordinateCap m D (m * D) :=
    fun j => (preparationCoordinateCap_bounds hsize le_rfl j).1
  have hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M := by
    intro j
    exact (hcoord j).trans (preparationCoordinateCap_mono (Nat.le_max_left m s)
      (Nat.mul_le_mul_right D hms))
  have hp0 : 0 ≤ p := (by norm_num : (0 : ℝ) ≤ 2).trans hp
  have hpInput : p ≤ pRelative := hstructure.1
  have hpRelative : 0 ≤ pRelative := hp0.trans hpInput
  have hpB : pRelative ≤ Bstruct := by linarith only [hpRelative, hBrelative]
  have hB : 0 ≤ Bstruct := hpRelative.trans hpB
  have hnum : (enlargedPreparedCommonSamplerDimension q M Jalloc : ℝ) ≤ Bstruct := by
    have h := hstructure.2.2.2.2.1
    simpa only [M, Jalloc, hq] using h.trans hpB
  have hchartBudget : allocatedUniformChartLog (M : ℝ) + 1 ≤ Bstruct := by
    have h := hstructure.2.2.2.2.2
    simpa only [M, hq] using h.trans hpB
  have hChartExp : Real.exp (allocatedUniformChartLog (M : ℝ)) ≤ Real.exp Bstruct :=
    Real.exp_le_exp.mpr (by linarith only [hchartBudget])
  exact {
    hcoord := hcoord
    hCoord := hCoord
    hpRelative := hpRelative
    hpB := hpB
    hB := hB
    hp0 := hp0
    hpInput := hpInput
    hpSource := hpInput.trans hpB
    hnum := hnum
    hchartBudget := hchartBudget
    hChartExp := hChartExp
    hEarlyRadius := preparedFiniteNestedSource_relative_radius prep nX M s hCoord hB hnum hBrelative
      (fun _ => Real.exp (6 * pRelative + 35)) (fun _ => (Real.exp_pos _).le) (fun _ => le_rfl) }

theorem preparedCanonicalRelativeSourceRequired_physicalSize
    {nX D m : ℕ} (prep : RankPreparationFamily (Fin nX) (Fin D) m)
    (s outerDepth innerDepth e Cprimitive Cdirect extra : ℕ)
    {Bstruct p knob : ℝ} (N : Fin nX → ℕ)
    (hs : 1 ≤ s) (hB : 0 ≤ Bstruct) (hp0 : 0 ≤ p)
    (hpSource : p ≤ Bstruct) (hnXp : (nX : ℝ) ≤ p)
    (hN : ∀ i, Real.exp (preparedCanonicalRelativeSourceRequired prep s outerDepth innerDepth
      e Cprimitive Cdirect extra Bstruct p knob) ≤ (N i : ℝ)) :
    ∀ i, 4 ≤ Real.exp (-(p + nX + 8)) * (N i : ℝ) := by
  have hA := (preparedFiniteNestedSourceExponent_bounds (max m s) s e Cprimitive Cdirect extra
    (preparedFiniteNestedSourceExponent (max m s) s e Cprimitive Cdirect extra) le_rfl).1
  exact (preparedFiniteNestedSourceRequired_trim_bounds
    (preparedFiniteNestedSourceExponent (max m s) s e Cprimitive Cdirect extra)
    AllocatedExternalCandidateSampler.degreeSourceCountConstants innerDepth outerDepth s
    Bstruct _ _ _ nX N hA hs hB hpSource (hnXp.trans hpSource) hp0 hN).2.2.2

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
attribute [local irreducible] AllocatedExternalCandidateSampler.NativeDetection integerBox

theorem exists_preparedFiniteNestedInitializedRelativeSource_fullScalars
    {m M Dold Erest s : ℕ} (prep : RankPreparationFamily (Fin nX) (Fin Dold) m) (outerDepth innerDepth cutoff : ℕ)
    (oldPatch : PolynomialPatch (Fin nX) s (Dold + Erest)) (F : oldPatch.LowestLayerModel m)
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
    (hp : ∀ j, DegreeLE (1 : Fin nX → ℕ) (j.val + 1) ((fun j => (prep.pad (max m cutoff) j).poly) j))
    (hmem : ∀ j ex, coefficients ((fun j => (prep.pad (max m cutoff) j).poly) j) ex ∈ U j)
    (Rrank : ℝ)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) ((fun j => (prep.pad (max m cutoff) j).poly) j))
    (ip : Fin Dold → MvPolynomial (Fin nX) ℤ) (hip : ∀ i, (ip i).totalDegree ≤ m)
    (c₀ : Fin Dold → ℝ) (err : VectorPolynomial (Fin nX) ℝ (Fin Dold → ℝ))
    (hprepare : ofCoordinates (Pi.basisFun ℝ (Fin Dold)) F.normalizedOrigin =
      prep.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c₀) + err)
    {δ pInit Pearly : ℝ} (hδ : 0 ≤ δ) (hgain1 : gain ≤ 1)
    (herr : ∀ x ∈ integerBox N, ∀ i, |eval (fun z => (x z : ℝ)) err i| ≤ δ)
    (hpInit : 2 ≤ pInit)
    (hDlog : (Dold : ℝ) ≤ Real.exp pInit)
    (hqlog : ((max m cutoff : ℕ) : ℝ) ≤ Real.exp pInit)
    (hLlog : (oldPatch.kernel.lip : ℝ) ≤ Real.exp pInit)
    (hNlog : ∀ j, (Fintype.card (prep.pad (max m cutoff) j).Coord : ℝ) ≤ Real.exp pInit)
    (hClog : ∀ j, C j ≤ Real.exp pInit)
    (hgainlog : Real.exp (-pInit) ≤ gain)
    (hδearly : δ ≤ Real.exp (-(3 * pInit + 130)))
    (hPearly : 6 * pInit + 35 ≤ Pearly)
    (hEarlyRadius : ∀ j,
      Real.exp Pearly * ((Fintype.card (PreparedSamplerContinuous (prep.pad (max m cutoff)) j) : ℝ) + 1) *
        allocatedCommonProductRadius (max m cutoff) Bstruct Bstruct ≤ 1 / 4)
    (hPhysicalSize : ∀ x, 4 ≤ Real.exp (-(gainLog + (nX : ℝ) + 8)) * (N x : ℝ))
    {n₀ stage d₀ : ℕ} {discount : ℝ} {childCutoff childCost : ℝ → ℝ}
    (ih : RelativePatchInductionRule s n₀ stage discount childCutoff childCost)
    {pchild a Λ : ℝ} (hpchild : pInit + 2 ≤ pchild)
    (ha : Real.exp (-pInit) ≤ a) (haΛ : a ≤ Λ) (hΛ : Λ ≤ 1)
    (habsolute : RelativePatchAbsoluteRule s n₀ pInit a Λ d₀)
    (hDim : (Fintype.card (LayerSamplerVariables
      (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))
      (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff)))
      (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))) : ℝ) ≤ pchild)
    (H : ℕ) (hHLmin : H ≤ Lmin) (hHcut : Real.exp (childCutoff pchild) ≤ H)
    (hDpos : 0 < Dold) (hrest : ∀ i : Fin Erest, m < oldPatch.weight (i.natAdd Dold))
    (hOldComplexity : relativePatchComplexity oldPatch ≤ pchild)
    (hOldStage : relativePatchDistinctWeights oldPatch ≤ stage + 1)
    (f : (Fin nX → ℤ) → ℝ)
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2))
    (hscore : gain ≤ relativePatchBoxScore N f a oldPatch)
    (hdiscount : discount ∈ Set.Icc (0 : ℝ) 1)
    (hchildCost : 0 ≤ childCost pchild) (initialCost : ℝ)
    (hCost : childCost pchild ≤ initialCost) (hHcost : (H : ℝ) ≤ Real.exp initialCost) :
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
          N (fun j => (prep.pad (max m cutoff) j).poly) hmem τ (Real.exp (-Plate)) stride cells)
        (hξone : Real.exp (-Plate) ≤ 1),
      PreparedCenteredProductiveGoodCenterEnhancedConclusion (m := (max m cutoff)) (nX := nX) (M := M)
        (prep.pad (max m cutoff)) U b S bW hb o hR (fun _ => hσ) μ (fun j => (prep.pad (max m cutoff) j).poly) hmem stride
        (allocatedExternalCandidateWidths (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) U b S N τ (Real.exp (-Plate))) (Acandidate 0).bases
        gainLog gain Qgood (preparedSpatialKernelBlocks (max m cutoff) M nX) Acandidate.law N (relativePatchSourceTest N f a oldPatch)
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
              profile.inner.Csource = preparedFiniteNestedSourceNativeExponent (max m cutoff) cutoff Cdirect)
        (fun center centerLift productive =>
          AllocatedNormalizedCandidateConclusion (E := Q) (A := Acandidate center)
            s (fun k => H ≤ (Acandidate center).sides k) centerLift productive
            (childCost pchild) initialCost (d₀ + s * Erest) f
            ((1 - discount) ^ (stage + 1) * Λ)) := by
  intro stageCountConstant A Cslice forecastCap Qw Pdetect K degree Cdetect kModel sourceU modelLog sliceLog u p
    pnum R pRadius D pDetect aDetect detectionGain Pk Pphysical target E Prho Ptail Pscale Tmod
    lengthLogs Pseed W Pmaster coarseTarget Plate native Econditional τ α baseB0 Pwidth Bcert Pgood
    anchorRequired conditionalRequired detectorRequired Rreq hnum hNrequired hRankRequired
  have ha01 : a ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨(Real.exp_pos _).le.trans ha, haΛ.trans hΛ⟩
  obtain ⟨htest, hmean⟩ := relativePatchSourceTest_fin_productive_data_of_box
    N f a oldPatch hf ha01 hscore
  obtain ⟨hR, σ, hσ, S, hpRadius, hRadiusBounds, hσone, hσQ, hσinv, hSmin, hSmax,
    hgap, hgeometry, hscalars, havailable, hmodels, hproductive, hmargin, Acandidate,
    hξone, hready⟩ := exists_preparedFiniteNestedForwardCompleteFixedCenterSource_fullScalars_s2
      prep outerDepth innerDepth cutoff U b stride N Vtail Q hb o bW ν μ μrows
      e Cprimitive Cdirect extra hprimitive Bstruct Qstride stageLog endpoint chartLog
      hendpoint hchartLog Qσ Pmin requestedCoarse gainLog gain Vlog Lmin Qgood
      hm hnX hCoord hB hstage hQstride hQσ hPmin hLmin hg hVlog hQgood hQexp hgain
      hnChart hgChart hstride hstrideBound C hC hCbound hchart Cforward hforward hForward
      hVtail hVactual hprofile hcutoff cells hCells
      (fun j => (prep.pad (max m cutoff) j).poly) hp hmem Rrank hrank
      (relativePatchSourceTest N f a oldPatch) htest hmean hnum hNrequired hRankRequired
  refine ⟨hR, σ, hσ, S, hpRadius, hRadiusBounds, hσone, hσQ, hσinv, hSmin, hSmax,
    hgap, hgeometry, hscalars, havailable, hmodels, hproductive, hmargin, Acandidate, hξone, ?_⟩
  have hearly : ∀ C' : Fin (max m cutoff) → ℝ, (∀ j, 0 ≤ C' j) →
      (∀ j, C' j ≤ Real.exp Pearly) →
      ∀ j, C' j * ((Fintype.card (PreparedSamplerContinuous (prep.pad (max m cutoff)) j) : ℝ) + 1) * R j ≤ 1 / 4 := by
    intro C' _hC' hC'bound j
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hC'bound j) (by positivity)) (hR j).le).trans (hEarlyRadius j)
  have hτhalf : τ ≤ 1 / 2 := (relativePatchSourceTrim_bounds hg nX).2
  exact F.exists_normalizedProblem_of_preparedReady_relative_induction
    prep (Nat.le_max_left m cutoff) U b hb o S hR (fun _ => hσ) bW μ
    ip hip c₀ err hprepare hmem hp (fun _ => hσone) C hC hchart N hτhalf hξone
    hPhysicalSize stride cells Acandidate hδ ((Real.exp_pos _).trans_le hgain) hgain1
    herr (by linarith only [hpInit]) hDlog hqlog hLlog hNlog hClog hgainlog hδearly hPearly hearly
    ih hpInit hpchild ha haΛ hΛ habsolute hDim H (hHLmin.trans hSmin) hHcut
    hDpos hrest hOldComplexity hOldStage f hf hfree hdiscount hchildCost initialCost hCost hHcost
    gainLog Qgood (preparedSpatialKernelBlocks (max m cutoff) M nX) _ hready

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedCanonicalInitializedRelativeSource
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

theorem preparedFiniteNestedSourceLiteralRequired_eq
    (m cutoff A Cdirect outerDepth innerDepth : ℕ) (constants : ℕ → ℕ)
    (G : Type) [Fintype G] (M count nX : ℕ)
    (Bstruct pnum Qstride gainLog stageLog Vlog Qσ Pmin requestedCoarse endpoint : ℝ) :
    preparedFiniteNestedSourceLiteralRequired m cutoff A Cdirect outerDepth innerDepth constants
      G M count nX Bstruct pnum Qstride gainLog stageLog Vlog Qσ Pmin requestedCoarse endpoint =
    preparedFiniteNestedSourceRequiredLog m cutoff A Cdirect outerDepth innerDepth constants
      G M count nX Bstruct pnum Qstride gainLog stageLog Vlog Qσ Pmin requestedCoarse endpoint := by
  rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

theorem preparedCanonicalRelative_initializerInputs
    {nX s D E m n₀ d₀ : ℕ}
    (oldPatch : PolynomialPatch (Fin nX) s (D + E))
    (prep : RankPreparationFamily (Fin nX) (Fin D) m)
    {p pRelative precisionBudget a Λ : ℝ}
    (hsize : prep.Sized D (m * D)) (hms : m ≤ s) (hp : 2 ≤ p)
    (hstructure :
      let M := preparationCoordinateCap s D (s * D)
      let Jalloc := modularInitialBlockCount s (nX + s * M)
      let dim := enlargedPreparedCommonSamplerDimension s M Jalloc
      p ≤ pRelative ∧ (s : ℝ) + 3 ≤ pRelative ∧
        (M : ℝ) ≤ pRelative ∧ (Jalloc : ℝ) ≤ pRelative ∧
        (dim : ℝ) ≤ pRelative ∧ allocatedUniformChartLog (M : ℝ) + 1 ≤ pRelative)
    (hprecision : 3 * pRelative + 130 ≤ precisionBudget)
    (hcomplexity : relativePatchComplexity oldPatch ≤ p)
    (ha : Real.exp (-p) ≤ a)
    (habsolute : RelativePatchAbsoluteRule s n₀ p a Λ d₀) :
    let M := preparationCoordinateCap (max m s) D (s * D)
    PreparedRelativeInitializerScalarInputs oldPatch
      (fun j => Fintype.card (prep.pad (max m s) j).Coord)
      (preparedRelativeInitializerVariableCount prep s M)
      p pRelative precisionBudget (allocatedUniformChartLog (M : ℝ)) a Λ n₀ d₀ := by
  intro M
  have hcoord : ∀ j, Fintype.card (prep j).Coord ≤ preparationCoordinateCap m D (m * D) :=
    fun j => (preparationCoordinateCap_bounds hsize le_rfl j).1
  have hM : M = preparationCoordinateCap s D (s * D) := by
    dsimp only [M]
    rw [max_eq_right hms]
  rw [hM]
  exact preparedRelativeInitializer_scalarInputs oldPatch prep hp hms hcoord
    hstructure hprecision hcomplexity ha habsolute

theorem preparedCanonicalRelativeLiteralRequired_eq
    {nX D m : ℕ} (prep : RankPreparationFamily (Fin nX) (Fin D) m)
    (s outerDepth innerDepth e Cprimitive Cdirect extra : ℕ)
    (Bstruct p knob : ℝ) :
    preparedCanonicalRelativeLiteralRequired prep s outerDepth innerDepth e Cprimitive Cdirect extra
      Bstruct p knob =
    preparedCanonicalRelativeSourceRequired prep s outerDepth innerDepth e Cprimitive Cdirect extra
      Bstruct p knob := by
  exact preparedFiniteNestedSourceLiteralRequired_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem preparedCanonicalRelativeLiteralRequired_floors
    {nX D m : ℕ} (prep : RankPreparationFamily (Fin nX) (Fin D) m)
    (s outerDepth innerDepth e Cprimitive Cdirect extra : ℕ)
    (Bstruct p knob : ℝ) (N : Fin nX → ℕ) (rankThreshold : ℝ)
    (hN : ∀ i, Real.exp (preparedCanonicalRelativeSourceRequired prep s outerDepth innerDepth
      e Cprimitive Cdirect extra Bstruct p knob) ≤ (N i : ℝ))
    (hrank : Real.exp (preparedCanonicalRelativeSourceRequired prep s outerDepth innerDepth
      e Cprimitive Cdirect extra Bstruct p knob) ≤ rankThreshold) :
    (∀ i, Real.exp (preparedCanonicalRelativeLiteralRequired prep s outerDepth innerDepth
      e Cprimitive Cdirect extra Bstruct p knob) ≤ (N i : ℝ)) ∧
    Real.exp (preparedCanonicalRelativeLiteralRequired prep s outerDepth innerDepth
      e Cprimitive Cdirect extra Bstruct p knob) ≤ rankThreshold := by
  rw [preparedCanonicalRelativeLiteralRequired_eq]
  exact ⟨hN, hrank⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct
attribute [local irreducible] AllocatedExternalCandidateSampler.NativeDetection integerBox
  RankPreparationFamily.PreparedHeights.canonicalPaddedSamplerData
  preparedFiniteNestedSourceRequiredLog

theorem preparedCanonicalInitializedRelativeSourceCore
    {nX m s D Erest : ℕ} (prep : RankPreparationFamily (Fin nX) (Fin D) m)
    (oldPatch : PolynomialPatch (Fin nX) s (D + Erest)) (F : oldPatch.LowestLayerModel m)
    (outerDepth innerDepth e Cprimitive Cdirect extra : ℕ)
    {p pRelative Bstruct knob pPrep pLate precisionBudget : ℝ} {Rrank : ℕ}
    (hheight : prep.PreparedHeights pPrep Rrank) (hsize : prep.Sized D (m * D))
    (hms : m ≤ s) (hs : 1 ≤ s) (hnX : 0 < nX)
    (hp : 2 ≤ p) (hpPrep : 0 ≤ pPrep) (hRank : 1 ≤ Rrank)
    (hPrepLate : pPrep ≤ pLate) (hRankLate : (Rrank : ℝ) ≤ Real.exp pLate)
    (hCapLate : (preparationCoordinateCap (max m s) D (s * D) : ℝ) ≤ pLate)
    (hprimitive : 1 ≤ Cprimitive) (hknob : 0 ≤ knob)
    (hstructure :
      let M := preparationCoordinateCap s D (s * D)
      let Jalloc := modularInitialBlockCount s (nX + s * M)
      let dim := enlargedPreparedCommonSamplerDimension s M Jalloc
      p ≤ pRelative ∧ (s : ℝ) + 3 ≤ pRelative ∧
        (M : ℝ) ≤ pRelative ∧ (Jalloc : ℝ) ≤ pRelative ∧
        (dim : ℝ) ≤ pRelative ∧ allocatedUniformChartLog (M : ℝ) + 1 ≤ pRelative)
    (hBrelative : 6 * pRelative + 35 ≤ Bstruct)
    (hprecision : 3 * pRelative + 130 ≤ precisionBudget)
    (hnXp : (nX : ℝ) ≤ p)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Bstruct)
    (hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Bstruct)
    (N : Fin nX → ℕ)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ))
      (Rrank : ℝ) (prep j).space (prep j).poly)
    (hN : ∀ i, Real.exp (preparedCanonicalRelativeSourceRequired prep s outerDepth innerDepth
      e Cprimitive Cdirect extra Bstruct p knob) ≤ (N i : ℝ))
    (hSourceRank : Real.exp (preparedCanonicalRelativeSourceRequired prep s outerDepth innerDepth
      e Cprimitive Cdirect extra Bstruct p knob) ≤ (Rrank : ℝ))
    (ip : Fin D → MvPolynomial (Fin nX) ℤ) (hip : ∀ i, (ip i).totalDegree ≤ m)
    (c₀ : Fin D → ℝ) (err : VectorPolynomial (Fin nX) ℝ (Fin D → ℝ))
    (hprepare : ofCoordinates (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin =
      prep.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c₀) + err)
    (herr : ∀ x ∈ integerBox N, ∀ i,
      |eval (fun z => (x z : ℝ)) err i| ≤ Real.exp (-precisionBudget))
    {n₀ stage d₀ : ℕ} {discount : ℝ} {childCutoff childCost : ℝ → ℝ}
    (ih : RelativePatchInductionRule s n₀ stage discount childCutoff childCost)
    {a Λ initialCost : ℝ}
    (ha : Real.exp (-p) ≤ a) (haΛ : a ≤ Λ) (hΛ : Λ ≤ 1)
    (habsolute : RelativePatchAbsoluteRule s n₀ p a Λ d₀)
    (hOldComplexity : relativePatchComplexity oldPatch ≤ p)
    (hDpos : 0 < D) (hrest : ∀ i : Fin Erest, m < oldPatch.weight (i.natAdd D))
    (hOldStage : relativePatchDistinctWeights oldPatch ≤ stage + 1)
    (f : (Fin nX → ℤ) → ℝ)
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2))
    (hscore : Real.exp (-p) ≤ relativePatchBoxScore N f a oldPatch)
    (hdiscount : discount ∈ Set.Icc (0 : ℝ) 1)
    (hchildCost : 0 ≤ childCost (pRelative + 2))
    (hCost : childCost (pRelative + 2) ≤ initialCost)
    (H Lmin Qgood : ℕ) (hHLmin : H ≤ Lmin)
    (hHcut : Real.exp (childCutoff (pRelative + 2)) ≤ (H : ℝ))
    (hHcost : (H : ℝ) ≤ Real.exp initialCost)
    (hLmin : (Lmin : ℝ) ≤ Real.exp knob)
    (hQgood : 1 ≤ Qgood) (hQexp : (Qgood : ℝ) ≤ Real.exp knob)
    (data :
      let q := max m s
      let M := preparationCoordinateCap q D (s * D)
      let Jalloc := modularInitialBlockCount q (nX + q * M)
      let G := EnlargedPreparedCommonKernel q Jalloc
      let Vars := LayerSamplerVariables G (PreparedSamplerContinuous (prep.pad q))
        (preparedSamplerTransverse (prep.pad q)) (EnlargedPreparedCommonSamplerBlock (prep.pad q) Jalloc)
      (prep.pad q).CanonicalSamplerData Vars M pLate)
    (hScalar : PreparedCanonicalRelativeScalarInputs prep s p pRelative Bstruct)
    (hInputs :
      let q := max m s
      let M := preparationCoordinateCap q D (s * D)
      let Jalloc := modularInitialBlockCount q (nX + q * M)
      let G := EnlargedPreparedCommonKernel q Jalloc
      let Vars := LayerSamplerVariables G (PreparedSamplerContinuous (prep.pad q))
        (preparedSamplerTransverse (prep.pad q)) (EnlargedPreparedCommonSamplerBlock (prep.pad q) Jalloc)
      PreparedRelativeInitializerScalarInputs oldPatch
        (fun j => Fintype.card (prep.pad q j).Coord) (Fintype.card Vars)
        p pRelative precisionBudget (allocatedUniformChartLog (M : ℝ)) a Λ n₀ d₀)
    (hPhysicalSize : ∀ i, 4 ≤ Real.exp (-(p + nX + 8)) * (N i : ℝ))

    (hNliteral : ∀ i, Real.exp (preparedCanonicalRelativeLiteralRequired prep s outerDepth innerDepth
      e Cprimitive Cdirect extra Bstruct p knob) ≤ (N i : ℝ))
    (hRankLiteral : Real.exp (preparedCanonicalRelativeLiteralRequired prep s outerDepth innerDepth
      e Cprimitive Cdirect extra Bstruct p knob) ≤ (Rrank : ℝ)) :
    preparedCanonicalInitializedRelativeSourceDataConclusion
      (nX := nX) (m := m) (s := s) (D := D)
      (Erest := Erest) (prep := prep) (oldPatch := oldPatch) (F := F)
      (outerDepth := outerDepth) (innerDepth := innerDepth) (e := e) (Cprimitive := Cprimitive)
      (Cdirect := Cdirect) (extra := extra) (p := p) (pRelative := pRelative)
      (Bstruct := Bstruct) (knob := knob) (pPrep := pPrep) (pLate := pLate)
      (precisionBudget := precisionBudget) (Rrank := Rrank) (hheight := hheight) (_hsize := hsize)
      (_hms := hms) (_hs := hs) (_hnX := hnX) (_hp := hp)
      (_hpPrep := hpPrep) (_hRank := hRank) (_hPrepLate := hPrepLate) (_hRankLate := hRankLate)
      (_hCapLate := hCapLate) (_hprimitive := hprimitive) (_hknob := hknob) (_hstructure := hstructure)
      (_hBrelative := hBrelative) (_hprecision := hprecision) (_hnXp := hnXp) (_hprofile := hprofile)
      (_hcutoff := hcutoff) (N := N) (_hrank := hrank) (_hN := hN)
      (_hSourceRank := hSourceRank) (ip := ip) (_hip := hip) (c₀ := c₀)
      (err := err) (_hprepare := hprepare) (_herr := herr) (n₀ := n₀)
      (stage := stage) (d₀ := d₀) (discount := discount) (childCutoff := childCutoff)
      (childCost := childCost) (_ih := ih) (a := a) (Λ := Λ)
      (initialCost := initialCost) (_ha := ha) (_haΛ := haΛ) (_hΛ := hΛ)
      (_habsolute := habsolute) (_hOldComplexity := hOldComplexity) (_hDpos := hDpos) (_hrest := hrest)
      (_hOldStage := hOldStage) (f := f) (_hf := hf) (_hfree := hfree)
      (_hscore := hscore) (_hdiscount := hdiscount) (_hchildCost := hchildCost) (_hCost := hCost)
      (H := H) (Lmin := Lmin) (Qgood := Qgood) (_hHLmin := hHLmin)
      (_hHcut := hHcut) (_hHcost := hHcost) (_hLmin := hLmin) (_hQgood := hQgood)
      (_hQexp := hQexp)
      (data := data) := by
  let q := max m s
  let M := preparationCoordinateCap q D (s * D)
  let Jalloc := modularInitialBlockCount q (nX + q * M)
  let G := EnlargedPreparedCommonKernel q Jalloc
  let Vars := LayerSamplerVariables G (PreparedSamplerContinuous (prep.pad q))
    (preparedSamplerTransverse (prep.pad q)) (EnlargedPreparedCommonSamplerBlock (prep.pad q) Jalloc)
  let chartLog := allocatedUniformChartLog (M : ℝ)
  let C : Fin q → ℝ := fun _ => Real.exp chartLog
  let Vtail : Fin q → ℝ≥0 := fun _ => ⟨Real.exp chartLog, (Real.exp_pos _).le⟩
  let stride : Fin nX → ℕ := fun _ => 1
  let cells : Finset (ColumnResiduePattern (Option Vars) (Fin nX) stride) := {0}
  let U := fun j => (prep.pad q j).space
  let : ∀ j, DecidableEq (prep.pad q j).Coord := fun _ => Classical.decEq _
  let := data.measures.lattice
  let := data.measures.coefficientCompact
  let := data.measures.coefficientBorel
  let := data.measures.rowCompact
  let := data.measures.rowBorel
  let := data.measures.siteBorel
  let := data.measures.layerInvariant
  let := data.measures.layerProbability
  let := data.measures.coefficientInvariant
  let := data.measures.coefficientProbability
  let := data.measures.rowInvariant
  let := data.measures.rowProbability
  exact exists_preparedFiniteNestedInitializedRelativeSource_fullScalars
    (M := M) (δ := Real.exp (-precisionBudget)) (pInit := pRelative)
    (Pearly := 6 * pRelative + 35) (pchild := pRelative + 2)
    prep outerDepth innerDepth s oldPatch F U data.b stride N Vtail
    (PreparedSamplerContinuous (prep.pad q)) data.span_eq data.o data.bW
    data.measures.layer data.measures.coefficient data.measures.row
    e Cprimitive Cdirect extra hprimitive Bstruct 0 0 knob chartLog
    hknob hScalar.hchartBudget knob knob knob p (Real.exp (-p)) knob Lmin Qgood
    (Nat.lt_of_lt_of_le Nat.zero_lt_one (hs.trans (Nat.le_max_right m s))) hnX hScalar.hCoord hScalar.hB ⟨le_rfl, hScalar.hB⟩ ⟨le_rfl, hScalar.hB⟩
    hknob hknob hLmin hScalar.hp0 hknob hQgood hQexp le_rfl (hnXp.trans hScalar.hpSource) hScalar.hpSource
    (fun _ => Nat.zero_lt_one) (fun _ => by simp only [stride, Nat.cast_one, Real.exp_zero]; exact le_rfl)
    C (fun _ => (Real.exp_pos _).le) (fun _ => le_rfl) data.inverse_chart_bound
    Vtail data.chart_bound (fun _ => hScalar.hChartExp) (fun _ => hScalar.hChartExp) data.covolume_bound
    hprofile hcutoff cells (Finset.singleton_nonempty _) (prep.pad_degreeLE (fun j => (hheight j).1))
    (prep.pad_coefficients_mem (fun j => (hheight j).2.1))
    (Rrank : ℝ) (prep.pad_samplingRank _ _ hrank) ip hip c₀ err hprepare
    hInputs.hδ hInputs.hgain1 herr hInputs.hpInit hInputs.hDlog hInputs.hqlog hInputs.hLlog
    hInputs.hNlog hInputs.hClog hInputs.hgainlog hInputs.hδearly le_rfl hScalar.hEarlyRadius hPhysicalSize
    ih hInputs.hpchild hInputs.ha haΛ hΛ hInputs.habsolute hInputs.hDim H hHLmin hHcut
    hDpos hrest hInputs.hOldComplexity hOldStage f hf hfree hscore hdiscount hchildCost
    initialCost hCost hHcost hScalar.hnum hNliteral hRankLiteral

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct
attribute [local irreducible] AllocatedExternalCandidateSampler.NativeDetection integerBox
  RankPreparationFamily.PreparedHeights.canonicalPaddedSamplerData
  preparedFiniteNestedSourceRequiredLog

theorem preparedCanonicalInitializedRelativeSourceDataProof
    {nX m s D Erest : ℕ} (prep : RankPreparationFamily (Fin nX) (Fin D) m)
    (oldPatch : PolynomialPatch (Fin nX) s (D + Erest)) (F : oldPatch.LowestLayerModel m)
    (outerDepth innerDepth e Cprimitive Cdirect extra : ℕ)
    {p pRelative Bstruct knob pPrep pLate precisionBudget : ℝ} {Rrank : ℕ}
    (hheight : prep.PreparedHeights pPrep Rrank) (hsize : prep.Sized D (m * D))
    (hms : m ≤ s) (hs : 1 ≤ s) (hnX : 0 < nX)
    (hp : 2 ≤ p) (hpPrep : 0 ≤ pPrep) (hRank : 1 ≤ Rrank)
    (hPrepLate : pPrep ≤ pLate) (hRankLate : (Rrank : ℝ) ≤ Real.exp pLate)
    (hCapLate : (preparationCoordinateCap (max m s) D (s * D) : ℝ) ≤ pLate)
    (hprimitive : 1 ≤ Cprimitive) (hknob : 0 ≤ knob)
    (hstructure :
      let M := preparationCoordinateCap s D (s * D)
      let Jalloc := modularInitialBlockCount s (nX + s * M)
      let dim := enlargedPreparedCommonSamplerDimension s M Jalloc
      p ≤ pRelative ∧ (s : ℝ) + 3 ≤ pRelative ∧
        (M : ℝ) ≤ pRelative ∧ (Jalloc : ℝ) ≤ pRelative ∧
        (dim : ℝ) ≤ pRelative ∧ allocatedUniformChartLog (M : ℝ) + 1 ≤ pRelative)
    (hBrelative : 6 * pRelative + 35 ≤ Bstruct)
    (hprecision : 3 * pRelative + 130 ≤ precisionBudget)
    (hnXp : (nX : ℝ) ≤ p)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Bstruct)
    (hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Bstruct)
    (N : Fin nX → ℕ)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ))
      (Rrank : ℝ) (prep j).space (prep j).poly)
    (hN : ∀ i, Real.exp (preparedCanonicalRelativeSourceRequired prep s outerDepth innerDepth
      e Cprimitive Cdirect extra Bstruct p knob) ≤ (N i : ℝ))
    (hSourceRank : Real.exp (preparedCanonicalRelativeSourceRequired prep s outerDepth innerDepth
      e Cprimitive Cdirect extra Bstruct p knob) ≤ (Rrank : ℝ))
    (ip : Fin D → MvPolynomial (Fin nX) ℤ) (hip : ∀ i, (ip i).totalDegree ≤ m)
    (c₀ : Fin D → ℝ) (err : VectorPolynomial (Fin nX) ℝ (Fin D → ℝ))
    (hprepare : ofCoordinates (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin =
      prep.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c₀) + err)
    (herr : ∀ x ∈ integerBox N, ∀ i,
      |eval (fun z => (x z : ℝ)) err i| ≤ Real.exp (-precisionBudget))
    {n₀ stage d₀ : ℕ} {discount : ℝ} {childCutoff childCost : ℝ → ℝ}
    (ih : RelativePatchInductionRule s n₀ stage discount childCutoff childCost)
    {a Λ initialCost : ℝ}
    (ha : Real.exp (-p) ≤ a) (haΛ : a ≤ Λ) (hΛ : Λ ≤ 1)
    (habsolute : RelativePatchAbsoluteRule s n₀ p a Λ d₀)
    (hOldComplexity : relativePatchComplexity oldPatch ≤ p)
    (hDpos : 0 < D) (hrest : ∀ i : Fin Erest, m < oldPatch.weight (i.natAdd D))
    (hOldStage : relativePatchDistinctWeights oldPatch ≤ stage + 1)
    (f : (Fin nX → ℤ) → ℝ)
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2))
    (hscore : Real.exp (-p) ≤ relativePatchBoxScore N f a oldPatch)
    (hdiscount : discount ∈ Set.Icc (0 : ℝ) 1)
    (hchildCost : 0 ≤ childCost (pRelative + 2))
    (hCost : childCost (pRelative + 2) ≤ initialCost)
    (H Lmin Qgood : ℕ) (hHLmin : H ≤ Lmin)
    (hHcut : Real.exp (childCutoff (pRelative + 2)) ≤ (H : ℝ))
    (hHcost : (H : ℝ) ≤ Real.exp initialCost)
    (hLmin : (Lmin : ℝ) ≤ Real.exp knob)
    (hQgood : 1 ≤ Qgood) (hQexp : (Qgood : ℝ) ≤ Real.exp knob)
    (data :
      let q := max m s
      let M := preparationCoordinateCap q D (s * D)
      let Jalloc := modularInitialBlockCount q (nX + q * M)
      let G := EnlargedPreparedCommonKernel q Jalloc
      let Vars := LayerSamplerVariables G (PreparedSamplerContinuous (prep.pad q))
        (preparedSamplerTransverse (prep.pad q)) (EnlargedPreparedCommonSamplerBlock (prep.pad q) Jalloc)
      (prep.pad q).CanonicalSamplerData Vars M pLate) :
    preparedCanonicalInitializedRelativeSourceDataConclusion
      (nX := nX) (m := m) (s := s) (D := D)
      (Erest := Erest) (prep := prep) (oldPatch := oldPatch) (F := F)
      (outerDepth := outerDepth) (innerDepth := innerDepth) (e := e) (Cprimitive := Cprimitive)
      (Cdirect := Cdirect) (extra := extra) (p := p) (pRelative := pRelative)
      (Bstruct := Bstruct) (knob := knob) (pPrep := pPrep) (pLate := pLate)
      (precisionBudget := precisionBudget) (Rrank := Rrank) (hheight := hheight) (_hsize := hsize)
      (_hms := hms) (_hs := hs) (_hnX := hnX) (_hp := hp)
      (_hpPrep := hpPrep) (_hRank := hRank) (_hPrepLate := hPrepLate) (_hRankLate := hRankLate)
      (_hCapLate := hCapLate) (_hprimitive := hprimitive) (_hknob := hknob) (_hstructure := hstructure)
      (_hBrelative := hBrelative) (_hprecision := hprecision) (_hnXp := hnXp) (_hprofile := hprofile)
      (_hcutoff := hcutoff) (N := N) (_hrank := hrank) (_hN := hN)
      (_hSourceRank := hSourceRank) (ip := ip) (_hip := hip) (c₀ := c₀)
      (err := err) (_hprepare := hprepare) (_herr := herr) (n₀ := n₀)
      (stage := stage) (d₀ := d₀) (discount := discount) (childCutoff := childCutoff)
      (childCost := childCost) (_ih := ih) (a := a) (Λ := Λ)
      (initialCost := initialCost) (_ha := ha) (_haΛ := haΛ) (_hΛ := hΛ)
      (_habsolute := habsolute) (_hOldComplexity := hOldComplexity) (_hDpos := hDpos) (_hrest := hrest)
      (_hOldStage := hOldStage) (f := f) (_hf := hf) (_hfree := hfree)
      (_hscore := hscore) (_hdiscount := hdiscount) (_hchildCost := hchildCost) (_hCost := hCost)
      (H := H) (Lmin := Lmin) (Qgood := Qgood) (_hHLmin := hHLmin)
      (_hHcut := hHcut) (_hHcost := hHcost) (_hLmin := hLmin) (_hQgood := hQgood)
      (_hQexp := hQexp)
      (data := data) :=
  have hScalar := preparedCanonicalRelative_scalarInputs prep hsize hms hp hstructure hBrelative
  have hInputs := preparedCanonicalRelative_initializerInputs oldPatch prep hsize hms hp
    hstructure hprecision hOldComplexity ha habsolute
  have hPhysicalSize := preparedCanonicalRelativeSourceRequired_physicalSize
    prep s outerDepth innerDepth e Cprimitive Cdirect extra N hs hScalar.hB hScalar.hp0
    hScalar.hpSource hnXp hN
  have hFloors := preparedCanonicalRelativeLiteralRequired_floors prep s outerDepth innerDepth
    e Cprimitive Cdirect extra Bstruct p knob N (Rrank : ℝ) hN hSourceRank
  preparedCanonicalInitializedRelativeSourceCore
      (nX := nX) (m := m) (s := s) (D := D)
      (Erest := Erest) (prep := prep) (oldPatch := oldPatch) (F := F)
      (outerDepth := outerDepth) (innerDepth := innerDepth) (e := e) (Cprimitive := Cprimitive)
      (Cdirect := Cdirect) (extra := extra) (p := p) (pRelative := pRelative)
      (Bstruct := Bstruct) (knob := knob) (pPrep := pPrep) (pLate := pLate)
      (precisionBudget := precisionBudget) (Rrank := Rrank) (hheight := hheight) (hsize := hsize)
      (hms := hms) (hs := hs) (hnX := hnX) (hp := hp)
      (hpPrep := hpPrep) (hRank := hRank) (hPrepLate := hPrepLate) (hRankLate := hRankLate)
      (hCapLate := hCapLate) (hprimitive := hprimitive) (hknob := hknob) (hstructure := hstructure)
      (hBrelative := hBrelative) (hprecision := hprecision) (hnXp := hnXp) (hprofile := hprofile)
      (hcutoff := hcutoff) (N := N) (hrank := hrank) (hN := hN)
      (hSourceRank := hSourceRank) (ip := ip) (hip := hip) (c₀ := c₀)
      (err := err) (hprepare := hprepare) (herr := herr) (n₀ := n₀)
      (stage := stage) (d₀ := d₀) (discount := discount) (childCutoff := childCutoff)
      (childCost := childCost) (ih := ih) (a := a) (Λ := Λ)
      (initialCost := initialCost) (ha := ha) (haΛ := haΛ) (hΛ := hΛ)
      (habsolute := habsolute) (hOldComplexity := hOldComplexity) (hDpos := hDpos) (hrest := hrest)
      (hOldStage := hOldStage) (f := f) (hf := hf) (hfree := hfree)
      (hscore := hscore) (hdiscount := hdiscount) (hchildCost := hchildCost) (hCost := hCost)
      (H := H) (Lmin := Lmin) (Qgood := Qgood) (hHLmin := hHLmin)
      (hHcut := hHcut) (hHcost := hHcost) (hLmin := hLmin) (hQgood := hQgood)
      (hQexp := hQexp)
      (data := data)
      (hScalar := hScalar) (hInputs := hInputs) (hPhysicalSize := hPhysicalSize)
      (hNliteral := hFloors.1) (hRankLiteral := hFloors.2)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct
attribute [local irreducible] AllocatedExternalCandidateSampler.NativeDetection integerBox
  RankPreparationFamily.PreparedHeights.canonicalPaddedSamplerData
  preparedFiniteNestedSourceRequiredLog

theorem exists_preparedCanonicalInitializedRelativeSource_of_data
    {nX m s D Erest : ℕ} (prep : RankPreparationFamily (Fin nX) (Fin D) m)
    (oldPatch : PolynomialPatch (Fin nX) s (D + Erest)) (F : oldPatch.LowestLayerModel m)
    (outerDepth innerDepth e Cprimitive Cdirect extra : ℕ)
    {p pRelative Bstruct knob pPrep pLate precisionBudget : ℝ} {Rrank : ℕ}
    (hheight : prep.PreparedHeights pPrep Rrank) (hsize : prep.Sized D (m * D))
    (hms : m ≤ s) (hs : 1 ≤ s) (hnX : 0 < nX)
    (hp : 2 ≤ p) (hpPrep : 0 ≤ pPrep) (hRank : 1 ≤ Rrank)
    (hPrepLate : pPrep ≤ pLate) (hRankLate : (Rrank : ℝ) ≤ Real.exp pLate)
    (hCapLate : (preparationCoordinateCap (max m s) D (s * D) : ℝ) ≤ pLate)
    (hprimitive : 1 ≤ Cprimitive) (hknob : 0 ≤ knob)
    (hstructure :
      let M := preparationCoordinateCap s D (s * D)
      let Jalloc := modularInitialBlockCount s (nX + s * M)
      let dim := enlargedPreparedCommonSamplerDimension s M Jalloc
      p ≤ pRelative ∧ (s : ℝ) + 3 ≤ pRelative ∧
        (M : ℝ) ≤ pRelative ∧ (Jalloc : ℝ) ≤ pRelative ∧
        (dim : ℝ) ≤ pRelative ∧ allocatedUniformChartLog (M : ℝ) + 1 ≤ pRelative)
    (hBrelative : 6 * pRelative + 35 ≤ Bstruct)
    (hprecision : 3 * pRelative + 130 ≤ precisionBudget)
    (hnXp : (nX : ℝ) ≤ p)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Bstruct)
    (hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Bstruct)
    (N : Fin nX → ℕ)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ))
      (Rrank : ℝ) (prep j).space (prep j).poly)
    (hN : ∀ i, Real.exp (preparedCanonicalRelativeSourceRequired prep s outerDepth innerDepth
      e Cprimitive Cdirect extra Bstruct p knob) ≤ (N i : ℝ))
    (hSourceRank : Real.exp (preparedCanonicalRelativeSourceRequired prep s outerDepth innerDepth
      e Cprimitive Cdirect extra Bstruct p knob) ≤ (Rrank : ℝ))
    (ip : Fin D → MvPolynomial (Fin nX) ℤ) (hip : ∀ i, (ip i).totalDegree ≤ m)
    (c₀ : Fin D → ℝ) (err : VectorPolynomial (Fin nX) ℝ (Fin D → ℝ))
    (hprepare : ofCoordinates (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin =
      prep.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c₀) + err)
    (herr : ∀ x ∈ integerBox N, ∀ i,
      |eval (fun z => (x z : ℝ)) err i| ≤ Real.exp (-precisionBudget))
    {n₀ stage d₀ : ℕ} {discount : ℝ} {childCutoff childCost : ℝ → ℝ}
    (ih : RelativePatchInductionRule s n₀ stage discount childCutoff childCost)
    {a Λ initialCost : ℝ}
    (ha : Real.exp (-p) ≤ a) (haΛ : a ≤ Λ) (hΛ : Λ ≤ 1)
    (habsolute : RelativePatchAbsoluteRule s n₀ p a Λ d₀)
    (hOldComplexity : relativePatchComplexity oldPatch ≤ p)
    (hDpos : 0 < D) (hrest : ∀ i : Fin Erest, m < oldPatch.weight (i.natAdd D))
    (hOldStage : relativePatchDistinctWeights oldPatch ≤ stage + 1)
    (f : (Fin nX → ℤ) → ℝ)
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2))
    (hscore : Real.exp (-p) ≤ relativePatchBoxScore N f a oldPatch)
    (hdiscount : discount ∈ Set.Icc (0 : ℝ) 1)
    (hchildCost : 0 ≤ childCost (pRelative + 2))
    (hCost : childCost (pRelative + 2) ≤ initialCost)
    (H Lmin Qgood : ℕ) (hHLmin : H ≤ Lmin)
    (hHcut : Real.exp (childCutoff (pRelative + 2)) ≤ (H : ℝ))
    (hHcost : (H : ℝ) ≤ Real.exp initialCost)
    (hLmin : (Lmin : ℝ) ≤ Real.exp knob)
    (hQgood : 1 ≤ Qgood) (hQexp : (Qgood : ℝ) ≤ Real.exp knob)
    (data :
      let q := max m s
      let M := preparationCoordinateCap q D (s * D)
      let Jalloc := modularInitialBlockCount q (nX + q * M)
      let G := EnlargedPreparedCommonKernel q Jalloc
      let Vars := LayerSamplerVariables G (PreparedSamplerContinuous (prep.pad q))
        (preparedSamplerTransverse (prep.pad q)) (EnlargedPreparedCommonSamplerBlock (prep.pad q) Jalloc)
      (prep.pad q).CanonicalSamplerData Vars M pLate) :
    preparedCanonicalInitializedRelativeSourceDataConclusion
      (nX := nX) (m := m) (s := s) (D := D)
      (Erest := Erest) (prep := prep) (oldPatch := oldPatch) (F := F)
      (outerDepth := outerDepth) (innerDepth := innerDepth) (e := e) (Cprimitive := Cprimitive)
      (Cdirect := Cdirect) (extra := extra) (p := p) (pRelative := pRelative)
      (Bstruct := Bstruct) (knob := knob) (pPrep := pPrep) (pLate := pLate)
      (precisionBudget := precisionBudget) (Rrank := Rrank) (hheight := hheight) (_hsize := hsize)
      (_hms := hms) (_hs := hs) (_hnX := hnX) (_hp := hp)
      (_hpPrep := hpPrep) (_hRank := hRank) (_hPrepLate := hPrepLate) (_hRankLate := hRankLate)
      (_hCapLate := hCapLate) (_hprimitive := hprimitive) (_hknob := hknob) (_hstructure := hstructure)
      (_hBrelative := hBrelative) (_hprecision := hprecision) (_hnXp := hnXp) (_hprofile := hprofile)
      (_hcutoff := hcutoff) (N := N) (_hrank := hrank) (_hN := hN)
      (_hSourceRank := hSourceRank) (ip := ip) (_hip := hip) (c₀ := c₀)
      (err := err) (_hprepare := hprepare) (_herr := herr) (n₀ := n₀)
      (stage := stage) (d₀ := d₀) (discount := discount) (childCutoff := childCutoff)
      (childCost := childCost) (_ih := ih) (a := a) (Λ := Λ)
      (initialCost := initialCost) (_ha := ha) (_haΛ := haΛ) (_hΛ := hΛ)
      (_habsolute := habsolute) (_hOldComplexity := hOldComplexity) (_hDpos := hDpos) (_hrest := hrest)
      (_hOldStage := hOldStage) (f := f) (_hf := hf) (_hfree := hfree)
      (_hscore := hscore) (_hdiscount := hdiscount) (_hchildCost := hchildCost) (_hCost := hCost)
      (H := H) (Lmin := Lmin) (Qgood := Qgood) (_hHLmin := hHLmin)
      (_hHcut := hHcut) (_hHcost := hHcost) (_hLmin := hLmin) (_hQgood := hQgood)
      (_hQexp := hQexp)
      (data := data) :=
  preparedCanonicalInitializedRelativeSourceDataProof
      (nX := nX) (m := m) (s := s) (D := D)
      (Erest := Erest) (prep := prep) (oldPatch := oldPatch) (F := F)
      (outerDepth := outerDepth) (innerDepth := innerDepth) (e := e) (Cprimitive := Cprimitive)
      (Cdirect := Cdirect) (extra := extra) (p := p) (pRelative := pRelative)
      (Bstruct := Bstruct) (knob := knob) (pPrep := pPrep) (pLate := pLate)
      (precisionBudget := precisionBudget) (Rrank := Rrank) (hheight := hheight) (hsize := hsize)
      (hms := hms) (hs := hs) (hnX := hnX) (hp := hp)
      (hpPrep := hpPrep) (hRank := hRank) (hPrepLate := hPrepLate) (hRankLate := hRankLate)
      (hCapLate := hCapLate) (hprimitive := hprimitive) (hknob := hknob) (hstructure := hstructure)
      (hBrelative := hBrelative) (hprecision := hprecision) (hnXp := hnXp) (hprofile := hprofile)
      (hcutoff := hcutoff) (N := N) (hrank := hrank) (hN := hN)
      (hSourceRank := hSourceRank) (ip := ip) (hip := hip) (c₀ := c₀)
      (err := err) (hprepare := hprepare) (herr := herr) (n₀ := n₀)
      (stage := stage) (d₀ := d₀) (discount := discount) (childCutoff := childCutoff)
      (childCost := childCost) (ih := ih) (a := a) (Λ := Λ)
      (initialCost := initialCost) (ha := ha) (haΛ := haΛ) (hΛ := hΛ)
      (habsolute := habsolute) (hOldComplexity := hOldComplexity) (hDpos := hDpos) (hrest := hrest)
      (hOldStage := hOldStage) (f := f) (hf := hf) (hfree := hfree)
      (hscore := hscore) (hdiscount := hdiscount) (hchildCost := hchildCost) (hCost := hCost)
      (H := H) (Lmin := Lmin) (Qgood := Qgood) (hHLmin := hHLmin)
      (hHcut := hHcut) (hHcost := hHcost) (hLmin := hLmin) (hQgood := hQgood)
      (hQexp := hQexp)
      (data := data)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct
attribute [local irreducible] AllocatedExternalCandidateSampler.NativeDetection integerBox
  RankPreparationFamily.PreparedHeights.canonicalPaddedSamplerData

theorem exists_preparedCanonicalInitializedRelativeSource_s2_oai
    {nX m s D Erest : ℕ} (prep : RankPreparationFamily (Fin nX) (Fin D) m)
    (oldPatch : PolynomialPatch (Fin nX) s (D + Erest)) (F : oldPatch.LowestLayerModel m)
    (outerDepth innerDepth e Cprimitive Cdirect extra : ℕ)
    {p pRelative Bstruct knob pPrep pLate precisionBudget : ℝ} {Rrank : ℕ}
    (hheight : prep.PreparedHeights pPrep Rrank) (hsize : prep.Sized D (m * D))
    (hms : m ≤ s) (hs : 1 ≤ s) (hnX : 0 < nX)
    (hp : 2 ≤ p) (hpPrep : 0 ≤ pPrep) (hRank : 1 ≤ Rrank)
    (hPrepLate : pPrep ≤ pLate) (hRankLate : (Rrank : ℝ) ≤ Real.exp pLate)
    (hCapLate : (preparationCoordinateCap (max m s) D (s * D) : ℝ) ≤ pLate)
    (hprimitive : 1 ≤ Cprimitive) (hknob : 0 ≤ knob)
    (hstructure :
      let M := preparationCoordinateCap s D (s * D)
      let Jalloc := modularInitialBlockCount s (nX + s * M)
      let dim := enlargedPreparedCommonSamplerDimension s M Jalloc
      p ≤ pRelative ∧ (s : ℝ) + 3 ≤ pRelative ∧
        (M : ℝ) ≤ pRelative ∧ (Jalloc : ℝ) ≤ pRelative ∧
        (dim : ℝ) ≤ pRelative ∧ allocatedUniformChartLog (M : ℝ) + 1 ≤ pRelative)
    (hBrelative : 6 * pRelative + 35 ≤ Bstruct)
    (hprecision : 3 * pRelative + 130 ≤ precisionBudget)
    (hnXp : (nX : ℝ) ≤ p)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Bstruct)
    (hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Bstruct)
    (N : Fin nX → ℕ)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ))
      (Rrank : ℝ) (prep j).space (prep j).poly)
    (hN : ∀ i, Real.exp (preparedCanonicalRelativeSourceRequired prep s outerDepth innerDepth
      e Cprimitive Cdirect extra Bstruct p knob) ≤ (N i : ℝ))
    (hSourceRank : Real.exp (preparedCanonicalRelativeSourceRequired prep s outerDepth innerDepth
      e Cprimitive Cdirect extra Bstruct p knob) ≤ (Rrank : ℝ))
    (ip : Fin D → MvPolynomial (Fin nX) ℤ) (hip : ∀ i, (ip i).totalDegree ≤ m)
    (c₀ : Fin D → ℝ) (err : VectorPolynomial (Fin nX) ℝ (Fin D → ℝ))
    (hprepare : ofCoordinates (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin =
      prep.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c₀) + err)
    (herr : ∀ x ∈ integerBox N, ∀ i,
      |eval (fun z => (x z : ℝ)) err i| ≤ Real.exp (-precisionBudget))
    {n₀ stage d₀ : ℕ} {discount : ℝ} {childCutoff childCost : ℝ → ℝ}
    (ih : RelativePatchInductionRule s n₀ stage discount childCutoff childCost)
    {a Λ initialCost : ℝ}
    (ha : Real.exp (-p) ≤ a) (haΛ : a ≤ Λ) (hΛ : Λ ≤ 1)
    (habsolute : RelativePatchAbsoluteRule s n₀ p a Λ d₀)
    (hOldComplexity : relativePatchComplexity oldPatch ≤ p)
    (hDpos : 0 < D) (hrest : ∀ i : Fin Erest, m < oldPatch.weight (i.natAdd D))
    (hOldStage : relativePatchDistinctWeights oldPatch ≤ stage + 1)
    (f : (Fin nX → ℤ) → ℝ)
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2))
    (hscore : Real.exp (-p) ≤ relativePatchBoxScore N f a oldPatch)
    (hdiscount : discount ∈ Set.Icc (0 : ℝ) 1)
    (hchildCost : 0 ≤ childCost (pRelative + 2))
    (hCost : childCost (pRelative + 2) ≤ initialCost)
    (H Lmin Qgood : ℕ) (hHLmin : H ≤ Lmin)
    (hHcut : Real.exp (childCutoff (pRelative + 2)) ≤ (H : ℝ))
    (hHcost : (H : ℝ) ≤ Real.exp initialCost)
    (hLmin : (Lmin : ℝ) ≤ Real.exp knob)
    (hQgood : 1 ≤ Qgood) (hQexp : (Qgood : ℝ) ≤ Real.exp knob) :
    preparedCanonicalInitializedRelativeSourceConclusion
      (nX := nX) (m := m) (s := s) (D := D)
      (Erest := Erest) (prep := prep) (oldPatch := oldPatch) (F := F)
      (outerDepth := outerDepth) (innerDepth := innerDepth) (e := e) (Cprimitive := Cprimitive)
      (Cdirect := Cdirect) (extra := extra) (p := p) (pRelative := pRelative)
      (Bstruct := Bstruct) (knob := knob) (pPrep := pPrep) (pLate := pLate)
      (precisionBudget := precisionBudget) (Rrank := Rrank) (hheight := hheight) (hsize := hsize)
      (hms := hms) (_hs := hs) (_hnX := hnX) (_hp := hp)
      (hpPrep := hpPrep) (hRank := hRank) (hPrepLate := hPrepLate) (hRankLate := hRankLate)
      (hCapLate := hCapLate) (_hprimitive := hprimitive) (_hknob := hknob) (_hstructure := hstructure)
      (_hBrelative := hBrelative) (_hprecision := hprecision) (_hnXp := hnXp) (_hprofile := hprofile)
      (_hcutoff := hcutoff) (N := N) (_hrank := hrank) (_hN := hN)
      (_hSourceRank := hSourceRank) (ip := ip) (_hip := hip) (c₀ := c₀)
      (err := err) (_hprepare := hprepare) (_herr := herr) (n₀ := n₀)
      (stage := stage) (d₀ := d₀) (discount := discount) (childCutoff := childCutoff)
      (childCost := childCost) (_ih := ih) (a := a) (Λ := Λ)
      (initialCost := initialCost) (_ha := ha) (_haΛ := haΛ) (_hΛ := hΛ)
      (_habsolute := habsolute) (_hOldComplexity := hOldComplexity) (_hDpos := hDpos) (_hrest := hrest)
      (_hOldStage := hOldStage) (f := f) (_hf := hf) (_hfree := hfree)
      (_hscore := hscore) (_hdiscount := hdiscount) (_hchildCost := hchildCost) (_hCost := hCost)
      (H := H) (Lmin := Lmin) (Qgood := Qgood) (_hHLmin := hHLmin)
      (_hHcut := hHcut) (_hHcost := hHcost) (_hLmin := hLmin) (_hQgood := hQgood)
      (_hQexp := hQexp) := by
  let q := max m s
  let M := preparationCoordinateCap q D (s * D)
  let Jalloc := modularInitialBlockCount q (nX + q * M)
  let G := EnlargedPreparedCommonKernel q Jalloc
  let Vars := LayerSamplerVariables G (PreparedSamplerContinuous (prep.pad q))
    (preparedSamplerTransverse (prep.pad q)) (EnlargedPreparedCommonSamplerBlock (prep.pad q) Jalloc)
  let data := hheight.canonicalPaddedSamplerData prep Vars (Nat.le_max_left m s)
    hpPrep hRank hPrepLate hRankLate hsize (Nat.mul_le_mul_right D hms) hCapLate
  exact exists_preparedCanonicalInitializedRelativeSource_of_data
      (nX := nX) (m := m) (s := s) (D := D)
      (Erest := Erest) (prep := prep) (oldPatch := oldPatch) (F := F)
      (outerDepth := outerDepth) (innerDepth := innerDepth) (e := e) (Cprimitive := Cprimitive)
      (Cdirect := Cdirect) (extra := extra) (p := p) (pRelative := pRelative)
      (Bstruct := Bstruct) (knob := knob) (pPrep := pPrep) (pLate := pLate)
      (precisionBudget := precisionBudget) (Rrank := Rrank) (hheight := hheight) (hsize := hsize)
      (hms := hms) (hs := hs) (hnX := hnX) (hp := hp)
      (hpPrep := hpPrep) (hRank := hRank) (hPrepLate := hPrepLate) (hRankLate := hRankLate)
      (hCapLate := hCapLate) (hprimitive := hprimitive) (hknob := hknob) (hstructure := hstructure)
      (hBrelative := hBrelative) (hprecision := hprecision) (hnXp := hnXp) (hprofile := hprofile)
      (hcutoff := hcutoff) (N := N) (hrank := hrank) (hN := hN)
      (hSourceRank := hSourceRank) (ip := ip) (hip := hip) (c₀ := c₀)
      (err := err) (hprepare := hprepare) (herr := herr) (n₀ := n₀)
      (stage := stage) (d₀ := d₀) (discount := discount) (childCutoff := childCutoff)
      (childCost := childCost) (ih := ih) (a := a) (Λ := Λ)
      (initialCost := initialCost) (ha := ha) (haΛ := haΛ) (hΛ := hΛ)
      (habsolute := habsolute) (hOldComplexity := hOldComplexity) (hDpos := hDpos) (hrest := hrest)
      (hOldStage := hOldStage) (f := f) (hf := hf) (hfree := hfree)
      (hscore := hscore) (hdiscount := hdiscount) (hchildCost := hchildCost) (hCost := hCost)
      (H := H) (Lmin := Lmin) (Qgood := Qgood) (hHLmin := hHLmin)
      (hHcut := hHcut) (hHcost := hHcost) (hLmin := hLmin) (hQgood := hQgood)
      (hQexp := hQexp)
      (data := data)

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.exists_preparedCanonicalInitializedRelativeSource_s2_oai := @OAI.Erdos3.VectorPolynomial.exists_preparedCanonicalInitializedRelativeSource_s2_oai
