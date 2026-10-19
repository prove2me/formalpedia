-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.exists_preparedFiniteNestedForwardProductiveFixedCenterSource_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T08:28:56.220499+00:00
-- url     : https://prove2.me/submissions/b9741f7e-df2c-4750-a7d8-a93d3729c8de

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B285
import Definitions.Def_OAIE3v2B290
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_preparedFiniteScheduleLocalProductiveSource_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_preparedFiniteScheduleProductiveFixedCenterSource_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SmoothSpatialCostBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem smoothSpatialDisplacementCost_nonneg {I J : Type*} [Fintype I] [Fintype J]
    (N : Type*) [Fintype N] (s : I ↪ J) (M : ℕ) :
    0 ≤ smoothSpatialDisplacementCost N s M := by
  unfold smoothSpatialDisplacementCost spatialKernelErrorConstant
    scalarSpatialIndexAllowance scalarSpatialInverseAllowance
  positivity

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem spatialKernelErrorConstant_le_exp (j e : ℕ) {U P : ℝ} (K : ℝ≥0)
    (hU0 : 0 ≤ U) (hU : U ≤ Real.exp P) (hK : (K : ℝ) ≤ Real.exp P) :
    spatialKernelErrorConstant j e U 1 K ≤
      Real.exp ((j : ℝ)^2+(j+2)*P+2*e) := by
  have htwo : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  unfold spatialKernelErrorConstant
  norm_num only [mul_one]
  calc
    _ ≤ (Real.exp ((j : ℝ)^2)*(Real.exp P)^j)*(Real.exp 2)^e*Real.exp P*Real.exp P := by
      gcongr
      exact factorial_le_exp_sq j
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
      simp only [← Real.exp_add]
      congr 1
      ring

theorem smoothSpatialDisplacementCost_le_exp {I J : Type*} [Fintype I] [Fintype J]
    (N : Type*) [Fintype N] (s : I ↪ J) {M : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hM : (M : ℝ) ≤ Real.exp p) :
    smoothSpatialDisplacementCost N s M ≤
      Real.exp (spatialDisplacementLog (Fintype.card (Unit ⊕ I))
        (Fintype.card (UnselectedColumn s ⊕ N)) (Fintype.card (UnselectedColumn s))
        (Fintype.card N) p) := by
  let j := Fintype.card (Unit ⊕ I)
  let d := Fintype.card (UnselectedColumn s ⊕ N)
  let e := Fintype.card (UnselectedColumn s)
  let P := spatialProfileLog j d p
  obtain ⟨hG, hU, _, hK⟩ := spatialProfileLog_bounds N s hp hM
  have he : (e : ℝ) ≤ d := by
    simp only [d, e, Fintype.card_sum, Nat.cast_add]
    exact le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hsmall : ((e+j : ℝ)*probabilityProfileLipschitz) ≤ Real.exp P := by
    apply le_trans _ hK
    gcongr
  have hc := spatialKernelErrorConstant_le_exp j e ((e+j)*probabilityProfileLipschitz)
    (by unfold scalarSpatialInverseAllowance; positivity) hU
    (by simpa only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_natCast] using hsmall)
  have hn : (Fintype.card N : ℝ) ≤ Real.exp (Fintype.card N : ℝ) := by
    linarith [Real.add_one_le_exp (Fintype.card N : ℝ)]
  unfold smoothSpatialDisplacementCost
  calc
    _ ≤ Real.exp P * Real.exp ((j : ℝ)^2+(j+2)*P+2*e) * Real.exp (Fintype.card N : ℝ) := by
      apply mul_le_mul _ hn (Nat.cast_nonneg _) (by positivity)
      exact mul_le_mul hG hc (by unfold spatialKernelErrorConstant scalarSpatialInverseAllowance; positivity)
        (Real.exp_pos _).le
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      dsimp [spatialDisplacementLog, P]
      ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SpatialNumericEnvelopeFunctoriality
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel VectorPolynomial
open scoped NNReal

theorem normalizedTupleNarrowWidth_pos (X N : Type*) [Fintype X] [Fintype N]
    {G : Type*} [Fintype G] {q : ℕ} (s : Fin q ↪ G) (M : ℕ) (p E : ℝ) :
    0 < normalizedTupleNarrowWidth X N s M p E := by
  have ht : 0 < normalizedTupleTolerance X p E := (spatialTupleTolerance_spec (Fintype.card X) (Real.exp_nonneg _)
    (Real.exp_nonneg _) (half_pos (Real.exp_pos (-(E + 2))))).1
  exact (twoTermErrorWidth_spec (smoothSpatialDisplacementCost_nonneg N s M) ht).1

end Erdos3

end

section

namespace Erdos3

theorem spatialPrimitiveEnvelope_bounds {p E l : ℝ}
    (hp : 0 ≤ p) (hE : 0 ≤ E) (hl : 0 ≤ l) :
    let R := spatialPrimitiveEnvelope p E l
    0 ≤ R ∧ p ≤ R ∧ E + 3 ≤ R ∧ p ^ 3 + anisotropicSpatialCapLog p ≤ R ∧
      coefficientErrorVolumeLog p + 4 ≤ R ∧ spatialDisplacementEnvelope p ≤ R ∧
      spatialDiscretizationEnvelope p l ≤ R ∧ spatialLipschitzCostEnvelope p l ≤ R ∧
      spatialThresholdEnvelope p l ≤ R ∧ spatialBoundaryEnvelope p l ≤ R ∧
      spatialMovementEnvelope p l ≤ R := by
  obtain ⟨_, hd, ha, hm, hk⟩ := spatialCostEnvelopes_nonneg hp hl
  have hcap : 0 ≤ p ^ 3 + anisotropicSpatialCapLog p := by
    have := anisotropicSpatialCapLog_nonneg hp
    positivity
  have hvol : 0 ≤ coefficientErrorVolumeLog p + 4 := by
    unfold coefficientErrorVolumeLog
    positivity
  have hK : 0 ≤ spatialLipschitzCostEnvelope p l := by
    unfold spatialLipschitzCostEnvelope
    positivity
  have hT : 0 ≤ spatialThresholdEnvelope p l := by
    unfold spatialThresholdEnvelope
    positivity
  have hQ : 0 ≤ spatialBoundaryEnvelope p l := by
    unfold spatialBoundaryEnvelope
    positivity
  have hD : 0 ≤ spatialMovementEnvelope p l := by
    unfold spatialMovementEnvelope
    positivity
  dsimp only [spatialPrimitiveEnvelope]
  repeat' constructor
  all_goals linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedTupleParameterBounds
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem normalizedSpatialShare_half_inv_le (E : ℝ) :
    (normalizedSpatialShare E / 2)⁻¹ ≤ Real.exp (E + 3) := by
  unfold normalizedSpatialShare
  rw [inv_div, div_eq_mul_inv, ← Real.exp_neg, neg_neg]
  calc
    _ ≤ Real.exp 1 * Real.exp (E + 2) := mul_le_mul_of_nonneg_right
      (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem normalizedTupleEarlyParameters_bound {G N X : Type*}
    [Fintype G] [Fintype N] [Fintype X] {q M : ℕ} (s : Fin q ↪ G)
    {p E l : ℝ} (hp : 0 ≤ p) (hE : 0 ≤ E) (hl : 0 ≤ l)
    (hMp : (M : ℝ) ≤ Real.exp p) (hq : ((q + 1 : ℕ) : ℝ) ≤ p)
    (hG : (Fintype.card G : ℝ) ≤ p) (hN : (Fintype.card N : ℝ) ≤ p)
    (hX : (Fintype.card X : ℝ) ≤ p) :
    let R := spatialPrimitiveEnvelope p E l
    (normalizedTupleTolerance X p E)⁻¹ ≤ Real.exp (spatialTupleToleranceLog R) ∧
      (normalizedTupleNarrowWidth X N s M p E)⁻¹ ≤
        Real.exp (2 * (R + spatialTupleToleranceLog R) + 4) := by
  obtain ⟨hR, hpR, hER, hcapR, hvolR, hdispR, _⟩ :=
    spatialPrimitiveEnvelope_bounds hp hE hl
  obtain ⟨he, hd, _⟩ := spatialAuxiliaryDimensions (N := N) s hG hN
  have hI : (Fintype.card (Unit ⊕ Fin q) : ℝ) ≤ p := by
    simpa only [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin, Nat.add_comm 1] using hq
  have hB := (smoothSpatialDisplacementCost_le_exp N s hp hMp).trans
    (Real.exp_le_exp.mpr ((spatialDisplacementLog_le_envelope _ _ _ _ hp hI hd he hN).trans hdispR))
  have hε : 0 < normalizedSpatialShare E / 2 := half_pos (Real.exp_pos _)
  have hεR := (normalizedSpatialShare_half_inv_le E).trans (Real.exp_le_exp.mpr hER)
  exact ⟨spatialTupleTolerance_inv_bound (Fintype.card X) (Real.exp_nonneg _) (Real.exp_nonneg _)
    hε hR (hX.trans hpR) (Real.exp_le_exp.mpr hcapR) (Real.exp_le_exp.mpr hvolR) hεR,
    spatialTupleEarlyWidth_inv_bound (Fintype.card X) (Real.exp_nonneg _) (Real.exp_nonneg _)
      (smoothSpatialDisplacementCost_nonneg N s M) hε hR (hX.trans hpR)
      (Real.exp_le_exp.mpr hcapR) (Real.exp_le_exp.mpr hvolR) hB hεR⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AveragedNormalizedTwistForecastJointModel
namespace OAI

section

namespace Erdos3

theorem fixedCenterForecast_source_threshold
    {u p sourceU sourceModel : ℝ}
    (hsource : u + 2 * p + 1 ≤ sourceU) (hmodel : 0 ≤ sourceModel) :
    Real.exp (-(2 * sourceU + 4 * sourceModel + 7)) ≤
      Real.exp (-(2 * u + 4 * p + 8)) / 2 := by
  calc
    _ ≤ Real.exp (-(2 * u + 4 * p + 9)) :=
      Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (-(2 * u + 4 * p + 8)) / Real.exp 1 := by
      rw [← Real.exp_sub]
      congr 1
      ring
    _ ≤ _ := div_le_div_of_nonneg_left (Real.exp_nonneg _) (by norm_num)
      (by linarith [Real.add_one_le_exp (1 : ℝ)])

theorem fixedCenterForecast_source_threshold_half_le_one
    {u p : ℝ} (hu : 0 ≤ u) (hp : 0 ≤ p) :
    Real.exp (-(2 * u + 4 * p + 8)) / 2 ≤ 1 := by
  have h := Real.exp_le_one_iff.mpr (show -(2 * u + 4 * p + 8) ≤ 0 by linarith)
  linarith

end Erdos3

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

section

namespace Erdos3.VectorPolynomial

theorem preparedFiniteForwardPairedSourcePrecision_model_lower
    (A Cdirect : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ) (isDirect : Bool)
    {x gainLog stageLog : ℝ} (hx : 0 ≤ x)
    (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x) :
    preparedFiniteForwardModelPrecision A stageCountConstant n x gainLog stageLog +
        2 * preparedFiniteForwardWork A stageCountConstant n x + 1 ≤
      preparedFiniteForwardPairedSourcePrecision A Cdirect stageCountConstant n isDirect
        x gainLog stageLog := by
  change preparedFiniteForwardSourcePrecision A stageCountConstant n x gainLog stageLog ≤ _
  have hsource := (preparedFiniteForward_model_precision_bounds A stageCountConstant n hx hg hs).2.1
  have hwork := preparedFiniteForwardWork_nonneg A stageCountConstant n hx
  cases isDirect with
  | false => simp only [preparedFiniteForwardPairedSourcePrecision_model, le_refl]
  | true =>
    rw [preparedFiniteForwardPairedSourcePrecision_direct]
    exact le_add_of_nonneg_right
      (pow_nonneg (add_nonneg (add_nonneg hsource hwork) (Nat.cast_nonneg Cdirect)) Cdirect)

theorem preparedFiniteForwardFixedCenterThreshold_lower
    (A Cdirect : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ) (isDirect : Bool)
    {x gainLog stageLog : ℝ} (hx : 0 ≤ x)
    (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x) :
    Real.exp (-(2 * preparedFiniteForwardPairedSourcePrecision A Cdirect stageCountConstant n
        isDirect x gainLog stageLog + 4 * preparedFiniteForwardWork A stageCountConstant n x + 7)) ≤
      Real.exp (-(2 * preparedFiniteForwardModelPrecision A stageCountConstant n x gainLog stageLog +
        4 * preparedFiniteForwardWork A stageCountConstant n x + 8)) / 2 :=
  fixedCenterForecast_source_threshold
    (preparedFiniteForwardPairedSourcePrecision_model_lower A Cdirect stageCountConstant n isDirect
      hx hg hs)
    (preparedFiniteForwardWork_nonneg A stageCountConstant n hx)

theorem preparedFiniteForwardFixedCenterThreshold_half_le_one
    (A : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ)
    {x gainLog stageLog : ℝ} (hx : 0 ≤ x)
    (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x) :
    Real.exp (-(2 * preparedFiniteForwardModelPrecision A stageCountConstant n x gainLog stageLog +
      4 * preparedFiniteForwardWork A stageCountConstant n x + 8)) / 2 ≤ 1 :=
  fixedCenterForecast_source_threshold_half_le_one
    (preparedFiniteForward_model_precision_bounds A stageCountConstant n hx hg hs).1
    (preparedFiniteForwardWork_nonneg A stageCountConstant n hx)

end Erdos3.VectorPolynomial

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PreparedModularCanonicalDetectorSpatialBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ b, Fintype (B b)]

theorem preparedModularDetector_narrow_width {q Mk nX : ℕ} (selection : Fin q ↪ G)
    {Pphysical coarseTarget : ℝ} (hp : 0 ≤ Pphysical) (htarget : 0 ≤ coarseTarget)
    (hMk : (Mk : ℝ) ≤ Real.exp Pphysical) (hq : ((q + 1 : ℕ) : ℝ) ≤ Pphysical)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pphysical)
    (hnX : (nX : ℝ) ≤ Pphysical) :
    let R := spatialPrimitiveEnvelope Pphysical coarseTarget 0
    let ξLog := 2 * (R + spatialTupleToleranceLog R) + 4
    0 ≤ ξLog ∧
      (normalizedTupleNarrowWidth (Fin nX) (PrincipalTupleIndex B (layerSamplerDegree I n))
        selection Mk Pphysical coarseTarget)⁻¹ ≤ Real.exp ξLog := by
  intro R ξLog
  have hG := (Nat.cast_le.mpr (allocatedKernelVariables_card_le_variables (G := G) B)).trans hvars
  have hN := (Nat.cast_le.mpr (allocatedPrincipalIndex_card_le_variables (G := G) B)).trans hvars
  have hX : (Fintype.card (Fin nX) : ℝ) ≤ Pphysical := by simpa only [Fintype.card_fin] using hnX
  have hR : 0 ≤ R := (spatialPrimitiveEnvelope_bounds hp htarget (le_refl 0)).1
  have ht := spatialTupleToleranceLog_nonneg hR
  refine ⟨by dsimp only [ξLog]; positivity, ?_⟩
  exact (normalizedTupleEarlyParameters_bound
    (N := PrincipalTupleIndex B (layerSamplerDegree I n)) (X := Fin nX)
    selection hp htarget (le_refl 0) hMk hq hG hN hX).2

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SharedWidthPreparedChoice
namespace OAI

section

namespace Erdos3

theorem sharedWidthPreparedChoice {T : Type*} (width : T → ℝ) (Plate : ℝ)
    (hpositive : ∀ t, 0 < width t)
    (hreciprocal : ∀ t, (width t)⁻¹ ≤ Real.exp Plate) :
    let ξ := Real.exp (-Plate)
    0 < ξ ∧ ξ⁻¹ = Real.exp Plate ∧ ∀ t, ξ ≤ width t := by
  refine ⟨Real.exp_pos _, ?_, ?_⟩
  · simp only [Real.exp_neg, inv_inv]
  · intro t
    have h := (inv_le_inv₀ (Real.exp_pos Plate) (inv_pos.mpr (hpositive t))).2
      (hreciprocal t)
    simpa only [Real.exp_neg, inv_inv] using h

theorem sharedWidthPreparedChoice_le_one {Plate : ℝ} (hPlate : 0 ≤ Plate) :
    Real.exp (-Plate) ≤ 1 := by
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hPlate)

theorem sharedWidthNormalizedTuplePreparedChoice {T G N X : Type*}
    [Fintype G] [Fintype N] [Fintype X]
    (q M : T → ℕ) (selection : ∀ t, Fin (q t) ↪ G) (p E : T → ℝ) (Plate : ℝ)
    (hreciprocal : ∀ t,
      (normalizedTupleNarrowWidth X N (selection t) (M t) (p t) (E t))⁻¹ ≤
        Real.exp Plate) :
    let ξ := Real.exp (-Plate)
    0 < ξ ∧ ξ⁻¹ = Real.exp Plate ∧ ∀ t,
      ξ ≤ normalizedTupleNarrowWidth X N (selection t) (M t) (p t) (E t) := by
  exact sharedWidthPreparedChoice
    (fun t => normalizedTupleNarrowWidth X N (selection t) (M t) (p t) (E t)) Plate
    (fun t => normalizedTupleNarrowWidth_pos X N (selection t) (M t) (p t) (E t))
    hreciprocal

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteScheduleCandidateDetection
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m s : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {nX : ℕ} (selection : Fin (s + 1) ↪ G) (Pdetect : Polynomial ℕ)

theorem preparedFiniteScheduleDirectWidth_inv
    (Cdetect : ℕ)
    (hCdetect : Cdetect = sampledSupportedSlicedDetectionConstant s Pdetect)
    (Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget
      pRadius sourceU pModel pSlice α : ℝ)
    (scalar : PreparedUniformDegreeDirectScalarBounds m s nX
      (Fintype.card (LayerSamplerVariables G I n B)) Cdetect
      Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget
      pRadius sourceU pModel pSlice)
    (geometryAt : PreparedUniformDegreeGeometryAt B U basis S s Cdetect nX
      Pchart Pscale D target Pk Prho Qstride (allocatedModelTestLog sourceU pModel) pRadius
      (2 * sourceU + 4 * pModel + 7) pGain)
    (hα : Real.exp (-(2 * sourceU + 4 * pModel + 7)) ≤ α) :
    (normalizedTupleNarrowWidth (Fin nX) (PrincipalTupleIndex B (layerSamplerDegree I n))
      selection (allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B))
        Pdetect (allocatedModelTestLog sourceU pModel) (allocatedModelTestLog sourceU pModel) α)
      Pphysical coarseTarget)⁻¹ ≤ Real.exp Plate := by
  rw [hCdetect] at scalar geometryAt
  have hMk := (geometryAt.2 α hα).2.1
  have hCoarse : 0 ≤ coarseTarget := by
    linarith only [scalar.gain_master.1, scalar.coarse_lower]
  have hwidth := preparedModularDetector_narrow_width B selection scalar.physical_master.1
    hCoarse (hMk.trans (Real.exp_le_exp.mpr scalar.kernel_physical))
    scalar.detector_physical scalar.variables_physical scalar.ambient_physical
  exact hwidth.2.trans (Real.exp_le_exp.mpr scalar.xi_late)

theorem preparedFiniteScheduleDirectWidth
    (Cdetect : ℕ)
    (hCdetect : Cdetect = sampledSupportedSlicedDetectionConstant s Pdetect)
    (Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget
      pRadius sourceU pModel pSlice α : ℝ)
    (scalar : PreparedUniformDegreeDirectScalarBounds m s nX
      (Fintype.card (LayerSamplerVariables G I n B)) Cdetect
      Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget
      pRadius sourceU pModel pSlice)
    (geometryAt : PreparedUniformDegreeGeometryAt B U basis S s Cdetect nX
      Pchart Pscale D target Pk Prho Qstride (allocatedModelTestLog sourceU pModel) pRadius
      (2 * sourceU + 4 * pModel + 7) pGain)
    (hα : Real.exp (-(2 * sourceU + 4 * pModel + 7)) ≤ α) :
    Real.exp (-Plate) ≤ normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection
      (allocatedDetectedKernelCutoff s G (Fintype.card (LayerSamplerVariables G I n B))
        Pdetect (allocatedModelTestLog sourceU pModel) (allocatedModelTestLog sourceU pModel) α)
      Pphysical coarseTarget := by
  have h := preparedFiniteScheduleDirectWidth_inv B U basis S selection Pdetect Cdetect
    hCdetect Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical
    coarseTarget pRadius sourceU pModel pSlice α scalar geometryAt hα
  have hchoice := sharedWidthNormalizedTuplePreparedChoice (fun _ : Unit => s + 1)
    (fun _ => allocatedDetectedKernelCutoff s G
      (Fintype.card (LayerSamplerVariables G I n B)) Pdetect
      (allocatedModelTestLog sourceU pModel) (allocatedModelTestLog sourceU pModel) α)
    (fun _ => selection) (fun _ => Pphysical) (fun _ => coarseTarget) Plate (fun _ => h)
  exact hchoice.2.2 ()

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteForwardSeededIndexedProductiveSource
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

theorem exists_preparedFiniteForwardSeededIndexedProductiveSource
    {m nX M : ℕ} {X₀ J₀ : Type} (prep : RankPreparationFamily X₀ J₀ m)
    [∀ j : Fin m, DecidableEq (RankPreparationLayer.Coord (prep j))]
    (U : ∀ j, Submodule ℝ ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j → ℝ))
    (b : ∀ j, Basis (Fin ((preparedSamplerTransverse prep) j)) ℝ (euclideanSubspace (U j))ᗮ)
    (stride N : Fin nX → ℕ) (Pdetect : Polynomial ℕ)
    (Vtail : Fin m → ℝ≥0)

    (Q : Fin m → Type) [∀ j, Fintype (Q j)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis ((PreparedSamplerContinuous prep) j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j)) (euclideanSubspace (U j))))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j)) (euclideanSubspace (U j)))]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    [CompactSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
    [BorelSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
    (μrows : Measure (CoefficientTorus (K := Fin (0 + 1)) U))
    [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]
    [MeasurableSpace (SiteTorus (Finset (Fin (0 + 1))) U)]
    [BorelSpace (SiteTorus (Finset (Fin (0 + 1))) U)]

    (depth A Cslice Cdirect : ℕ) (stageCountConstant : ℕ → ℕ)
    {Stage : Type} [Fintype Stage]
    (stageIndex : Stage → Fin (depth + 1)) (isDirect : Stage → Bool)
    (stageSeed : Stage → ℝ)
    (degree : Stage → ℕ) (anchorStage : Stage)
    (hdegree : ∀ k, degree k ≤ m)
    (hanchor : degree anchorStage = 0) (hanchorModel : isDirect anchorStage = false)
    (hA : 2 ≤ A) (hSliceExponent : Cslice + 1 ≤ A)
    (Bstruct Qstride forecastCap stageLog : ℝ)
    (Qσ Qw Pmin requestedCoarse gainLog gain Vlog : ℝ)
    (Lmin Qgood : ℕ)
    (hm : 0 < m) (hnX : 0 < nX)
    (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hB : 0 ≤ Bstruct) (hSeedLower : ∀ k, Bstruct ≤ stageSeed k)
    (hstage : stageLog ∈ Set.Icc 0 Bstruct)
    (hQstride : 0 ≤ Qstride)
    (hQσ : 0 ≤ Qσ) (hQw : 0 ≤ Qw) (hPmin : 0 ≤ Pmin)
    (hLmin : (Lmin : ℝ) ≤ Real.exp Pmin)
    (hg : 0 ≤ gainLog) (hVlog : 0 ≤ Vlog)
    (hQgood : 1 ≤ Qgood) (hQexp : (Qgood : ℝ) ≤ Real.exp Vlog)
    (hgain : Real.exp (-gainLog) ≤ gain)
    (hnChart : (nX : ℝ) ≤ Bstruct) (hgChart : gainLog ≤ Bstruct) :
    let K := Stage
    let Cdetect := fun k : K => sampledSupportedSlicedDetectionConstant (degree k) Pdetect
    let kModel : K := anchorStage
    let sourceU := fun k : K =>
      preparedFiniteForwardPairedSourcePrecision A Cdirect stageCountConstant (stageIndex k).val (isDirect k) (stageSeed k) gainLog stageLog
    let modelLog := fun k : K => preparedFiniteForwardWork A stageCountConstant (stageIndex k).val (stageSeed k)
    let sliceLog := fun k : K =>
      (preparedFiniteForwardParameter A stageCountConstant (stageIndex k).val (stageSeed k) + Cslice) ^ Cslice
    let u := preparedFiniteForwardModelPrecision A stageCountConstant (stageIndex anchorStage).val (stageSeed anchorStage) gainLog stageLog
    let p := preparedFiniteForwardWork A stageCountConstant (stageIndex anchorStage).val (stageSeed anchorStage)
    let pnum : ℝ := enlargedPreparedCommonSamplerDimension m M (modularInitialBlockCount m (nX + m * M))
    let R : Fin m → ℝ := fun _ => allocatedCommonProductRadius m Bstruct Bstruct
    let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
    let D := allocatedComparisonDimension m pnum
    let pDetect := fun k => allocatedModelTestLog (sourceU k) (modelLog k)
    let aDetect := fun k => 2 * sourceU k + 4 * modelLog k + 7
    let detectionGain := fun s : K => slicedDetectionGainLog (degree s) (Cdetect s)
      (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) (pDetect s) (pDetect s) (aDetect s)
    let Pk := fun s : K => scalarKernelLogarithmicBudget (Fin ((degree s) + 1)) (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (detectionGain s + pDetect s + 4)
    let Pphysical := fun k : K => preparedFiniteScheduleLocalPhysical m nX
      (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) Qstride (Pk k)
    let target := fun k => detectionGain k + 40 + coefficientErrorSpatialLog (Pphysical k)
    let E := fun s : K => target s + D * ((m * 2 ^ (m + 1) : ℕ) * Pk s) + 5
    let Prho := fun s : K => 2 * affineProfileInputEnvelope D
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect s + 2) + 2
    let Ptail := fun s : K => affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect s + 2)
    let Pscale := preparedUniformDegreeScaleLog (D + pRadius) Ptail Qσ
    let Tmod := fun s : K => ((m + 1 : ℕ) : ℝ) * Pk s + nX * Qstride
    let lengthLogs := fun s : K => allocatedAffineLengthLog m D Pscale (Prho s) (Pk s)
      (target s) (pDetect s + 2) (Tmod s)
    let Pseed := allocatedScaleLog (Pscale + ∑ s, lengthLogs s + Pmin + 1)
    let W := physicalBadProductGap ((modularInitialBlockCount m (nX + m * M)) * (nX + m * M)) (gainLog + 8) Vlog Qgood
    let Pmaster := fun k : K => preparedFiniteScheduleLocalMaster Bstruct D pRadius Qstride
      (Pphysical k) (sourceU k) (modelLog k) (Prho k) (target k) (detectionGain k)
    let coarseTarget := preparedFiniteScheduleDirectCoarse detectionGain requestedCoarse
    let Plate := ∑ k : K, preparedUniformDegreeDirectLate (Pmaster k) Pscale
      (Pphysical k) coarseTarget (allocatedWitnessScaleLog Pseed Qw)
    let τ := Real.exp (-(gainLog + (nX : ℝ) + 8))
    pnum ≤ Bstruct →
    W ≤ Real.exp Qw →
    (4 * ∏ j, earlyConstantDensityCap (Fintype.card ((PreparedSamplerContinuous prep) j)) ((preparedSamplerTransverse prep) j) (R j) (Vtail j)) ≤ Real.exp p →
    0 ≤ forecastCap → forecastCap ≤ Real.exp p →
    ∃ (hR : ∀ j, 0 < R j) (σ : ℝ) (hσ : 0 < σ)
      (S : LayerSamplerScale («G» := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) («I» := (PreparedSamplerContinuous prep)) («n» := (preparedSamplerTransverse prep)) («J» := (fun j : Fin m => RankPreparationLayer.Coord (prep j))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R (fun _ => σ)),
      0 ≤ pRadius ∧ (∀ j, R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧
      σ ≤ 1 ∧ σ ≤ Real.exp (-Qσ) ∧ σ⁻¹ ≤ Real.exp Pscale ∧
      Lmin ≤ S.value ∧ (S.value : ℝ) ≤ Real.exp (allocatedWitnessScaleLog Pseed Qw) ∧
      (∀ j i, S.value ^ (j.val + 1) < basisAxisScale (b j) i →
        8 * (probabilityProfileLipschitz : ℝ) * W ≤
          (layerSamplerGapWidth («G» := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) R ⟨j, i⟩ / 2) *
            ((basisAxisScale (b j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))) ∧
      (∀ s : K, PreparedUniformDegreeGeometryAt («G» := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S (degree s) (Cdetect s) nX
        Bstruct Pscale D (target s) (Pk s) (Prho s) Qstride (pDetect s) pRadius (aDetect s) (detectionGain s)) ∧
      (∀ k, PreparedUniformDegreeDirectScalarBounds m (degree k) nX
        (Fintype.card (LayerSamplerVariables
          (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
          (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
          (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))))
        (Cdetect k) Bstruct Pscale D (target k) (Pk k) (Prho k) Qstride (Pmaster k) Plate
        (detectionGain k) (Pphysical k) coarseTarget pRadius (sourceU k) (modelLog k) (sliceLog k)) ∧
      (∀ k, PreparedScheduledDirectSourceAvailability
          (B := EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))
          (U := U) (basis := b) (S := S) (hR := hR) (hσ := fun _ => hσ)
          (selection := enlargedPreparedCommonCanonicalSelection m
            (modularInitialBlockCount m (nX + m * M)) (degree k) (hdegree k))
          (stride := stride) (N := N) (Pdetect := Pdetect)
          (sourceU := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
          (Vtail := Vtail) (τ := τ) (hb := hb) (o := o)
          Bstruct Qstride (Pmaster k) Plate (detectionGain k) (Pphysical k) coarseTarget) ∧
      (∀ k, PreparedScheduledDegreeModelAvailability
          (B := EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))
          (U := U) (basis := b) (S := S) (hR := hR) (hσ := fun _ => hσ)
          (selection := enlargedPreparedCommonCanonicalSelection m
            (modularInitialBlockCount m (nX + m * M)) (degree k)
              (hdegree k))
          (stride := stride) (N := N) (Pdetect := Pdetect)
          (sourceU := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
          (Vtail := Vtail) (τ := τ) (hb := hb) (o := o) (μ := μ)
          Bstruct Qstride (Pmaster k) Plate (detectionGain k) (Pphysical k) coarseTarget) ∧
      PreparedUniformDegreeProductiveSourceConclusion
        (m := m) (nX := nX) (M := M) (prep := prep) (U := U) (b := b) (S := S)
        (hR := hR) (hσ := fun _ => hσ) (stride := stride) (N := N)
        (Pdetect := Pdetect) (pModel := modelLog kModel) (pSlice := sliceLog kModel)
        (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
        (hb := hb) (o := o) (bW := bW) (μ := μ)
        Bstruct Qstride (Pmaster kModel) Plate (detectionGain kModel) (Pphysical kModel) coarseTarget
        pRadius Pscale Pseed Qw gainLog gain Vlog Qgood := by
  intro K Cdetect kModel sourceU modelLog sliceLog u p
    pnum R pRadius D pDetect aDetect detectionGain Pk Pphysical target E Prho Ptail Pscale Tmod
    lengthLogs Pseed W Pmaster coarseTarget Plate τ hnum hWexp
    hCtail hForecastCap hForecastCapP
  have hcount : (Fintype.card (LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) : ℝ)
      ≤ Bstruct :=
    (Nat.cast_le.mpr (enlargedPreparedCommonSampler_dimensions prep
      (modularInitialBlockCount m (nX + m * M)) hCoord).1).trans hnum
  have hseed (k : K) : 0 ≤ stageSeed k := hB.trans (hSeedLower k)
  have hseedGain (k : K) : gainLog ∈ Set.Icc 0 (stageSeed k) :=
    ⟨hg, hgChart.trans (hSeedLower k)⟩
  have hseedStage (k : K) : stageLog ∈ Set.Icc 0 (stageSeed k) :=
    ⟨hstage.1, hstage.2.trans (hSeedLower k)⟩
  have hmodelLog (k : K) : 0 ≤ modelLog k :=
    preparedFiniteForwardWork_nonneg A stageCountConstant (stageIndex k).val (hseed k)
  have hcountModel (k : K) : (Fintype.card (LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) : ℝ)
      ≤ Real.exp (modelLog k) :=
    (preparedFiniteForward_model_scalar_bounds A stageCountConstant (stageIndex k).val
      (Fintype.card (LayerSamplerVariables
        (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
        (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
        (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))))
      hA (hseed k) (hcount.trans (hSeedLower k))).2.2.1
  have hcontrolledSlice (k : K) := preparedFiniteForward_controlled_slice_bounds
    A Cslice stageCountConstant (stageIndex k).val
    (Fintype.card (LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))))
    hA hSliceExponent (hseed k) (hcount.trans (hSeedLower k))
  have hsliceModel : ∀ k, sliceLog k ≤ modelLog k := fun k => (hcontrolledSlice k).2.1
  have hsourceU (k : K) : 0 ≤ sourceU k :=
    preparedFiniteForwardPairedSourcePrecision_nonneg A Cdirect stageCountConstant
      (stageIndex k).val (isDirect k) (hseed k) (hseedGain k) (hseedStage k)
  have hModelSource : sourceU kModel = u + 2 * p + 1 := by
    dsimp only [sourceU, kModel, u, p]
    rw [hanchorModel, preparedFiniteForwardPairedSourcePrecision_model]
    rfl
  have hSliceLog : sliceLog kModel * Fintype.card (LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) ≤ p :=
    (hcontrolledSlice kModel).2.2
  have hu : 0 ≤ u :=
    (preparedFiniteForward_model_precision_bounds A stageCountConstant (stageIndex anchorStage).val
      (hseed anchorStage) (hseedGain anchorStage) (hseedStage anchorStage)).1
  have hp : 0 ≤ p := hmodelLog kModel
  have original := exists_preparedFiniteScheduleLocalProductiveSource_s2
    (m := m) (nX := nX) (M := M) prep U b stride N Pdetect Vtail
    Q hb o bW ν μ μrows degree Cdetect kModel hdegree hanchor
    (by simp only [Cdetect, kModel, hanchor])
    Bstruct Qstride u p forecastCap sourceU modelLog sliceLog hModelSource
    Qσ Qw Pmin requestedCoarse gainLog gain Vlog Lmin Qgood hm hnX hCoord
    hB hu hp hsourceU hmodelLog hsliceModel hcountModel hQstride hQσ hQw hPmin hLmin
    hg hVlog hQgood hQexp hgain hnChart hgChart
  obtain ⟨hR, σ, hσ, S, hRadius, hRbounds, hσone, hσexp, hσinv, hFloor,
    hS, hgap, hgeometry, hscalar, hdirect, _hmodelZero, hdegreeModel, hproductive⟩ :=
    original hnum hWexp hSliceLog hCtail hForecastCap hForecastCapP
  refine ⟨hR, σ, hσ, S, hRadius, hRbounds, hσone, hσexp, hσinv, hFloor,
    hS, hgap, hgeometry, hscalar, ?_, ?_, hproductive⟩
  · intro k
    exact hdirect k rfl
  · intro k
    exact hdegreeModel k rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PreparedFiniteNestedForwardAllDegreePaddedSource
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

theorem exists_preparedFiniteNestedForwardAllDegreePaddedProductiveSource
    {m nX M : ℕ} {X₀ J₀ : Type} (prep : RankPreparationFamily X₀ J₀ m) (outerDepth innerDepth cutoff : ℕ)
    [∀ j : Fin (max m cutoff), DecidableEq (RankPreparationLayer.Coord ((prep.pad (max m cutoff)) j))]
    (U : ∀ j, Submodule ℝ ((fun j : Fin (max m cutoff) => RankPreparationLayer.Coord ((prep.pad (max m cutoff)) j)) j → ℝ))
    (b : ∀ j, Basis (Fin ((preparedSamplerTransverse (prep.pad (max m cutoff))) j)) ℝ (euclideanSubspace (U j))ᗮ)
    (stride N : Fin nX → ℕ) (Pdetect : Polynomial ℕ)
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

    (A Cslice Cdirect : ℕ) (stageCountConstant : ℕ → ℕ)
    (hA : 2 ≤ A) (hSliceExponent : Cslice + 1 ≤ A)
    (Bstruct Qstride forecastCap stageLog : ℝ)
    (Qσ Qw Pmin requestedCoarse gainLog gain Vlog : ℝ)
    (Lmin Qgood : ℕ)
    (hm : 0 < max m cutoff) (hnX : 0 < nX)
    (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hB : 0 ≤ Bstruct) (hstage : stageLog ∈ Set.Icc 0 Bstruct)
    (hQstride : 0 ≤ Qstride)
    (hQσ : 0 ≤ Qσ) (hQw : 0 ≤ Qw) (hPmin : 0 ≤ Pmin)
    (hLmin : (Lmin : ℝ) ≤ Real.exp Pmin)
    (hg : 0 ≤ gainLog) (hVlog : 0 ≤ Vlog)
    (hQgood : 1 ≤ Qgood) (hQexp : (Qgood : ℝ) ≤ Real.exp Vlog)
    (hgain : Real.exp (-gainLog) ≤ gain)
    (hnChart : (nX : ℝ) ≤ Bstruct) (hgChart : gainLog ≤ Bstruct) :
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
    pnum ≤ Bstruct →
    W ≤ Real.exp Qw →
    (4 * ∏ j, earlyConstantDensityCap (Fintype.card ((PreparedSamplerContinuous (prep.pad (max m cutoff))) j)) ((preparedSamplerTransverse (prep.pad (max m cutoff))) j) (R j) (Vtail j)) ≤ Real.exp p →
    0 ≤ forecastCap → forecastCap ≤ Real.exp p →
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
        pRadius Pscale Pseed Qw gainLog gain Vlog Qgood := by
  exact exists_preparedFiniteForwardSeededIndexedProductiveSource
    (m := max m cutoff) (nX := nX) (M := M) (prep.pad (max m cutoff)) U b stride N Pdetect Vtail
    Q hb o bW ν μ μrows innerDepth A Cslice Cdirect stageCountConstant
    preparedFiniteNestedForwardAllDegreeStage preparedFiniteNestedForwardAllDegreeIsDirect
    (preparedFiniteNestedForwardAllDegreeSeed A stageCountConstant Bstruct)
    preparedFiniteNestedForwardAllDegreeDegree (preparedFiniteNestedForwardAllDegreeAnchor outerDepth innerDepth cutoff)
    (preparedFiniteNestedForwardAllDegreeDegree_le (Nat.le_max_right m cutoff))
    (preparedFiniteNestedForwardAllDegreeAnchor_degree outerDepth innerDepth cutoff)
    (preparedFiniteNestedForwardAllDegreeAnchor_model outerDepth innerDepth cutoff)
    hA hSliceExponent
    Bstruct Qstride forecastCap stageLog Qσ Qw Pmin requestedCoarse gainLog gain Vlog
    Lmin Qgood hm hnX
    (prep.pad_coordinate_card_le hCoord)
    hB (fun k => le_preparedFiniteNestedForwardAllDegreeSeed A stageCountConstant hA hB k)
    hstage hQstride hQσ hQw hPmin hLmin hg hVlog hQgood hQexp hgain hnChart hgChart

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PreparedGeometryDecidableTransport
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped Classical NNReal

theorem preparedUniformDegreeGeometryAt_decidableTransport
    {m : ℕ} {G : Type} [fG : Fintype G]
    {I : Fin m → Type} [fI : ∀ j, Fintype (I j)] {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type} [fB : ∀ a, Fintype (B a)]
    {J : Fin m → Type} [fJ : ∀ j, Fintype (J j)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U basis R σ}
    {s Cdetect nX : ℕ}
    {Bstruct Pscale D target Pk Prho Qstride pDetect pRadius aDetect gainLog : ℝ}
    {dG dG' : DecidableEq G}
    {dB dB' : ∀ a, DecidableEq (B a)}
    (h : @PreparedUniformDegreeGeometryAt m G fG dG I fI n B fB dB J fJ
      U basis R σ S s Cdetect nX Bstruct Pscale D target Pk Prho Qstride
      pDetect pRadius aDetect gainLog) :
    @PreparedUniformDegreeGeometryAt m G fG dG' I fI n B fB dB' J fJ
      U basis R σ S s Cdetect nX Bstruct Pscale D target Pk Prho Qstride
      pDetect pRadius aDetect gainLog := by
  cases Subsingleton.elim dG dG'
  cases Subsingleton.elim dB dB'
  exact h

theorem preparedScheduledDirectSourceAvailability_decidableTransport
    {m s : ℕ} {G : Type} [Fintype G]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {J : Fin m → Type} [∀ j, Fintype (J j)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {S : LayerSamplerScale (G := G) B U basis R σ} {nX : ℕ}
    {selection : Fin (s + 1) ↪ G} {stride N : Fin nX → ℕ}
    {Pdetect : Polynomial ℕ} {sourceU pModel pSlice : ℝ} {Vtail : Fin m → ℝ≥0}
    {τ : ℝ}
    {hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget : ℝ}
    {dG dG' : DecidableEq G}
    (h : letI := dG
      PreparedScheduledDirectSourceAvailability
        (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
        (selection := selection) (stride := stride) (N := N)
        (Pdetect := Pdetect) (sourceU := sourceU) (pModel := pModel) (pSlice := pSlice)
        (Vtail := Vtail) (τ := τ) (hb := hb) (o := o)
        Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget) :
    letI := dG'
    PreparedScheduledDirectSourceAvailability
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (sourceU := sourceU) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (hb := hb) (o := o)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget := by
  cases Subsingleton.elim dG dG'
  exact h

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteNestedForwardCanonicalFixedCenterSource
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators

theorem preparedUniformDegreeDirectLate_extra_le
    (Pmaster Pscale Pphysical coarseTarget extraLate : ℝ) :
    extraLate ≤ preparedUniformDegreeDirectLate Pmaster Pscale Pphysical coarseTarget extraLate :=
  (le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _)))

theorem preparedFiniteScheduleDirectLate_extra_le_sum
    {Stage : Type*} [Fintype Stage] (k₀ : Stage)
    (Pmaster Pphysical : Stage → ℝ) (Pscale coarseTarget extraLate : ℝ)
    (hmaster : ∀ k, 0 ≤ Pmaster k) :
    extraLate ≤ ∑ k, preparedUniformDegreeDirectLate (Pmaster k) Pscale
      (Pphysical k) coarseTarget extraLate := by
  apply (preparedUniformDegreeDirectLate_extra_le (Pmaster k₀) Pscale
    (Pphysical k₀) coarseTarget extraLate).trans
  exact Finset.single_le_sum
    (f := fun k => preparedUniformDegreeDirectLate (Pmaster k) Pscale
      (Pphysical k) coarseTarget extraLate)
    (fun k _ => (hmaster k).trans (le_max_left _ _)) (Finset.mem_univ k₀)

theorem preparedFiniteSchedule_kernel_input_le
    (I G : Type*) [Fintype I] [Fintype G] {R : ℝ} (hR : 0 ≤ R) :
    R ≤ scalarKernelLogarithmicBudget I G R := by
  let base : ℝ := 10 + (Fintype.card I : ℝ) + Fintype.card G +
    Fintype.card G * (Fintype.card I + 1) + R
  have hI : (0 : ℝ) ≤ Fintype.card I := Nat.cast_nonneg _
  have hG : (0 : ℝ) ≤ Fintype.card G := Nat.cast_nonneg _
  have hcross : (0 : ℝ) ≤ Fintype.card G * (Fintype.card I + 1) := by positivity
  have hbase : 1 ≤ base := by dsimp only [base]; linarith only [hI, hG, hcross, hR]
  have hRbase : R ≤ base := by dsimp only [base]; linarith only [hI, hG, hcross]
  have hcube : base ≤ base ^ 3 := le_self_pow₀ hbase (by norm_num)
  have hproduct : (0 : ℝ) ≤ (Fintype.card G : ℝ) *
      (Fintype.card I + 1) * Fintype.card I := by positivity
  have hfactor : (1 : ℝ) ≤ 4 + 3 * ((Fintype.card G : ℝ) *
      (Fintype.card I + 1) * Fintype.card I) := by linarith only [hproduct]
  have hinner : 0 ≤ 16 * base ^ 3 + 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hfactor hinner
  rw [scalarKernelLogarithmicBudget_eq]
  change R ≤ 2 * ((4 + 3 * ((Fintype.card G : ℝ) *
    (Fintype.card I + 1) * Fintype.card I)) * (16 * base ^ 3 + 2)) + 8
  linarith only [hRbase, hcube, hmul, hbase]

theorem preparedFiniteForwardPairedSourcePrecision_gain_lower
    (A Cdirect : ℕ) (constants : ℕ → ℕ) (stage : ℕ) (direct : Bool)
    {x gainLog stageLog : ℝ} (hx : 0 ≤ x)
    (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x) :
    gainLog ≤ preparedFiniteForwardPairedSourcePrecision A Cdirect constants stage direct
      x gainLog stageLog := by
  have hsource := preparedFiniteForwardPairedSourcePrecision_model_lower
    A Cdirect constants stage direct hx hg hs
  have hprefix := (preparedFiniteForward_prefix_bounds A constants stage hx).2.1
  have hwork := preparedFiniteForwardWork_nonneg A constants stage hx
  dsimp only [preparedFiniteForwardModelPrecision] at hsource
  linarith only [hsource, hprefix, hwork, hs.1]

theorem preparedFiniteScheduleLocalPhysical_gain
    (m nX count degree Cdetect : ℕ) (G : Type*) [Fintype G]
    {u pModel gainLog Qstride : ℝ}
    (hu : 0 ≤ u) (hmodel : 0 ≤ pModel) (hgain : gainLog ≤ u) (hstride : 0 ≤ Qstride) :
    let pDetect := allocatedModelTestLog u pModel
    let pGain := slicedDetectionGainLog degree Cdetect count pDetect pDetect
      (2 * u + 4 * pModel + 7)
    let Pk := scalarKernelLogarithmicBudget (Fin (degree + 1)) G (pGain + pDetect + 4)
    gainLog + (nX : ℝ) + 8 ≤ preparedFiniteScheduleLocalPhysical m nX count Qstride Pk := by
  intro pDetect pGain Pk
  have hdetect : 0 ≤ pDetect := by dsimp only [pDetect, allocatedModelTestLog]; positivity
  have hgainDetect : 0 ≤ pGain := slicedDetectionGainLog_nonneg degree Cdetect count
    hdetect hdetect (by positivity)
  have hinput : 0 ≤ pGain + pDetect + 4 := by positivity
  have hkernel := preparedFiniteSchedule_kernel_input_le (Fin (degree + 1)) G hinput
  have hm : (0 : ℝ) ≤ (m + 2 : ℕ) := Nat.cast_nonneg _
  have hcount : (0 : ℝ) ≤ count := Nat.cast_nonneg _
  change pGain + pDetect + 4 ≤ Pk at hkernel
  dsimp only [preparedFiniteScheduleLocalPhysical]
  dsimp only [pDetect, allocatedModelTestLog] at hkernel
  linarith only [hkernel, hm, hcount, hgainDetect, hgain, hu, hmodel, hstride]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct
variable {nX : ℕ}
attribute [local irreducible] AllocatedExternalCandidateSampler.NativeDetection

theorem exists_preparedFiniteNestedForwardProductiveFixedCenterSource_s2_oai
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

    (A Cslice Cdirect : ℕ) (stageCountConstant : ℕ → ℕ)
    (hA : 2 ≤ A) (hSliceExponent : Cslice + 1 ≤ A)
    (Bstruct Qstride forecastCap stageLog Econditional : ℝ)
    (Qσ Qw Pmin requestedCoarse gainLog gain Vlog : ℝ)
    (Lmin Qgood : ℕ)
    (hm : 0 < max m cutoff) (hnX : 0 < nX)
    (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hB : 0 ≤ Bstruct) (hstage : stageLog ∈ Set.Icc 0 Bstruct)
    (hQstride : 0 ≤ Qstride)
    (hQσ : 0 ≤ Qσ) (hQw : 0 ≤ Qw) (hPmin : 0 ≤ Pmin)
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
    W ≤ Real.exp Qw →
    (4 * ∏ j, earlyConstantDensityCap (Fintype.card ((PreparedSamplerContinuous (prep.pad (max m cutoff))) j)) ((preparedSamplerTransverse (prep.pad (max m cutoff))) j) (R j) (Vtail j)) ≤ Real.exp p →
    0 ≤ forecastCap → forecastCap ≤ Real.exp p →
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
  intro Pdetect K degree Cdetect kModel sourceU modelLog sliceLog u p
    pnum R pRadius D pDetect aDetect detectionGain Pk Pphysical target E Prho Ptail Pscale Tmod
    lengthLogs Pseed W Pmaster coarseTarget Plate τ α baseB0 Pwidth Bcert Pgood
    anchorRequired conditionalRequired detectorRequired Rreq hnum hWexp hCtail hForecastCap hForecastCapP
    hNrequired hRankRequired
  have sourceResult :
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
        pRadius Pscale Pseed Qw gainLog gain Vlog Qgood := by
    exact exists_preparedFiniteNestedForwardAllDegreePaddedProductiveSource
      prep outerDepth innerDepth cutoff U b stride N Pdetect Vtail Q hb o bW ν μ μrows
      A Cslice Cdirect stageCountConstant hA hSliceExponent Bstruct Qstride forecastCap stageLog
      Qσ Qw Pmin requestedCoarse gainLog gain Vlog Lmin Qgood hm hnX hCoord hB hstage
      hQstride hQσ hQw hPmin hLmin hg hVlog hQgood hQexp hgain hnChart hgChart
      hnum hWexp hCtail hForecastCap hForecastCapP
  obtain ⟨hR, σ, hσ, S, hRadius, hRbounds, hσone, hσexp, hσinv, hFloor,
    hS, hgap, hgeometry, hscalar, hdirect, hdegreeModel, hproductive⟩ :=
    sourceResult
  have hseedLower (k : K) : Bstruct ≤ preparedFiniteNestedForwardAllDegreeSeed A stageCountConstant Bstruct k :=
    le_preparedFiniteNestedForwardAllDegreeSeed A stageCountConstant hA hB k
  have hseed (k : K) : 0 ≤ preparedFiniteNestedForwardAllDegreeSeed A stageCountConstant Bstruct k := hB.trans (hseedLower k)
  have hseedGain (k : K) : gainLog ∈ Set.Icc 0 (preparedFiniteNestedForwardAllDegreeSeed A stageCountConstant Bstruct k) :=
    ⟨hg, hgChart.trans (hseedLower k)⟩
  have hseedStage (k : K) : stageLog ∈ Set.Icc 0 (preparedFiniteNestedForwardAllDegreeSeed A stageCountConstant Bstruct k) :=
    ⟨hstage.1, hstage.2.trans (hseedLower k)⟩
  have hαLower (k : K) : Real.exp (-(2 * sourceU k + 4 * modelLog k + 7)) ≤ α k / 2 :=
    preparedFiniteForwardFixedCenterThreshold_lower A Cdirect stageCountConstant
      (preparedFiniteNestedForwardAllDegreeStage k).val (preparedFiniteNestedForwardAllDegreeIsDirect k)
      (hseed k) (hseedGain k) (hseedStage k)
  have hαHalfOne (k : K) : α k / 2 ≤ 1 :=
    preparedFiniteForwardFixedCenterThreshold_half_le_one A stageCountConstant
      (preparedFiniteNestedForwardAllDegreeStage k).val (hseed k) (hseedGain k) (hseedStage k)
  let selection := (fun k : K => enlargedPreparedCommonCanonicalSelection (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)) (degree k) (preparedFiniteNestedForwardAllDegreeDegree_le (Nat.le_max_right m cutoff) k))
  have hξSmall (k : K) := preparedFiniteScheduleDirectWidth
    (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) U b S (selection k) Pdetect (Cdetect k) rfl
    Bstruct Pscale D (target k) (Pk k) (Prho k) Qstride (Pmaster k) Plate
    (detectionGain k) (Pphysical k) coarseTarget pRadius (sourceU k) (modelLog k) (sliceLog k)
    (α k / 2) (hscalar k) (hgeometry k) (hαLower k)
  have hξ : 0 < Real.exp (-Plate) := Real.exp_pos _
  have hξLate : (Real.exp (-Plate))⁻¹ ≤ Real.exp Plate := by simp only [Real.exp_neg, inv_inv, le_refl]
  have hξone : Real.exp (-Plate) ≤ 1 := sharedWidthPreparedChoice_le_one
    ((hscalar kModel).master_nonneg.trans (hscalar kModel).late)
  have hSLate : (S.value : ℝ) ≤ Real.exp Plate := by
    exact hS.trans (Real.exp_le_exp.mpr (preparedFiniteScheduleDirectLate_extra_le_sum
      kModel Pmaster Pphysical Pscale coarseTarget (allocatedWitnessScaleLog Pseed Qw)
      (fun k => (hscalar k).master_nonneg)))
  obtain ⟨_, hτ, hτHalf, hτDim, _, hτBudget, _⟩ := preparedEarlySpatialWidth nX hg
  have hτInv (k : K) : τ⁻¹ ≤ Real.exp (Pphysical k) := by
    apply hτBudget
    exact preparedFiniteScheduleLocalPhysical_gain (max m cutoff) nX (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))))
      (degree k) (Cdetect k)
      (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))
      (hscalar k).u_master.1 (hscalar k).model_master.1
      (preparedFiniteForwardPairedSourcePrecision_gain_lower A Cdirect stageCountConstant
        (preparedFiniteNestedForwardAllDegreeStage k).val (preparedFiniteNestedForwardAllDegreeIsDirect k)
        (hseed k) (hseedGain k) (hseedStage k)) hQstride
  have hcount : ((Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))))) : ℝ) ≤ Bstruct :=
    (Nat.cast_le.mpr (enlargedPreparedCommonSampler_dimensions (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))
      (prep.pad_coordinate_card_le hCoord)).1).trans hnum
  have hdimension (k : K) : ((Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))))) : ℝ) ≤
      Pdetect.eval₂ (Nat.castRingHom ℝ) (pDetect k) := by
    have hwork := preparedFiniteForward_shiftedPower_le_work A 1 stageCountConstant
      (preparedFiniteNestedForwardAllDegreeStage k).val hA (by omega : 1 ≤ A) (hseed k)
    have hseedWork : preparedFiniteNestedForwardAllDegreeSeed A stageCountConstant Bstruct k ≤ modelLog k := by
      have := hwork
      simp only [pow_one, Nat.cast_one] at this
      linarith only [this]
    exact (hcount.trans (hseedLower k)).trans (hseedWork.trans
      (preparedFiniteForwardDetectorPolynomial_stage_bounds cutoff A Cdirect stageCountConstant
        (preparedFiniteNestedForwardAllDegreeStage k).val (preparedFiniteNestedForwardAllDegreeIsDirect k)
        (hseed k) (hseedGain k) (hseedStage k)).1)
  have hu : 0 ≤ u := (preparedFiniteForward_model_precision_bounds A stageCountConstant innerDepth
    (hseed kModel) (hseedGain kModel) (hseedStage kModel)).1
  have hpModel : 0 ≤ p := (hscalar kModel).model_master.1
  have hsourceModel : sourceU kModel = u + 2 * p + 1 := by
    change preparedFiniteForwardPairedSourcePrecision A Cdirect stageCountConstant innerDepth false
      (candidateNestedForwardSeed A stageCountConstant innerDepth outerDepth Bstruct) gainLog stageLog = _
    rw [preparedFiniteForwardPairedSourcePrecision_model]
    rfl
  have hsliceModel : sliceLog kModel * (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))))) ≤ p :=
    (preparedFiniteForward_controlled_slice_bounds A Cslice stageCountConstant innerDepth (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))))
      hA hSliceExponent (hseed kModel) (hcount.trans (hseedLower kModel))).2.2
  have hmodel := hdegreeModel kModel u p forecastCap hsourceModel hu hpModel hsliceModel hCtail hForecastCap hForecastCapP
  rw [hsourceModel] at hmodel
  have hξProductive := (sharedWidthNormalizedTuplePreparedChoice
    (fun _ : Unit => 1)
    (fun _ => allocatedDetectedKernelCutoff 0 (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))))) Pdetect
      (allocatedModelTestLog (u + 2 * p + 1) (modelLog kModel))
      (allocatedModelTestLog (u + 2 * p + 1) (modelLog kModel))
      (forecastAugmentedUnitThreshold u p (Real.exp (sliceLog kModel * (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))))))
        (max 1 (4 * ∏ j, earlyConstantDensityCap (Fintype.card ((PreparedSamplerContinuous (prep.pad (max m cutoff))) j)) ((preparedSamplerTransverse (prep.pad (max m cutoff))) j) (R j) (Vtail j))) forecastCap / 2))
    (fun _ => enlargedPreparedCommonCanonicalSelection (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)) 0 (Nat.zero_le _))
    (fun _ => Pphysical kModel) (fun _ => coarseTarget) Plate
    (fun _ => hmodel.2)).2.2 ()
  obtain ⟨⟨hGoodSize, hGoodRank⟩, ⟨hConditionalSize, hConditionalRank⟩, hDirectFloors, _⟩ :=
    preparedFiniteNestedSourceRequired_size_rank A stageCountConstant innerDepth outerDepth cutoff Bstruct
      anchorRequired conditionalRequired detectorRequired N Rrank hNrequired hRankRequired
  obtain ⟨hmargin, Acandidate, hready⟩ :=
    exists_preparedFiniteScheduleProductiveFixedCenterSource_s2
      (m := (max m cutoff)) (nX := nX) (M := M) (prep := (prep.pad (max m cutoff))) (E := Econditional)
      (U := U) (basis := b) (hR := hR) (hσ := fun _ => hσ) (S := S)
      (degree := degree) (selection := selection) (stride := stride) (N := N) (Pdetect := Pdetect)
      (sourceU := sourceU) (modelLog := modelLog) (sliceLog := sliceLog) (α := α)
      (Vtail := Vtail) (τ := τ) (hb := hb) (o := o) (bW := bW)
      kModel Bstruct Qstride Pmaster Plate Pphysical coarseTarget detectionGain
      (fun k => preparedScheduledDirectSourceAvailability_decidableTransport (hdirect k)) μ ν
      (hscalar kModel) (preparedUniformDegreeGeometryAt_decidableTransport (hgeometry kModel)) hSLate hαLower hαHalfOne hstride hstrideBound
      C hC hCbound hchart Cforward hforward hForward hVtail hVactual hprofile hcutoff
      hτ hτInv hτHalf hτDim hξ hξSmall hξLate cells poly hp hmem
      (fun k => (hDirectFloors k).1) hrank (fun k => (hDirectFloors k).2)
      hConditionalSize hConditionalRank hCells hdimension
      (enlargedPreparedCommonCanonicalSelection (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)) 0 (Nat.zero_le _))
      (u + 2 * p + 1) (modelLog kModel) (sliceLog kModel) u p forecastCap
      (Pmaster kModel) (detectionGain kModel) (Pphysical kModel)
      Bcert gainLog gain Pgood Qgood (preparedSpatialKernelBlocks (max m cutoff) M nX) Pwidth
      hproductive (hτInv kModel) hξProductive hGoodSize hGoodRank test htest hgain
      (by
        have hdec : productiveFixedSourceFinDecidableEq (nX := nX) = instDecidableEqFin nX :=
          Subsingleton.elim _ _
        rw [hdec]
        exact hmean)
  exact ⟨hR, σ, hσ, S, hRadius, hRbounds, hσone, hσexp, hσinv, hFloor,
    hS, hgap, hgeometry, hscalar, hdirect, hdegreeModel, hproductive,
    hmargin, Acandidate, hξone, hready⟩

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.exists_preparedFiniteNestedForwardProductiveFixedCenterSource_s2_oai := @OAI.Erdos3.VectorPolynomial.exists_preparedFiniteNestedForwardProductiveFixedCenterSource_s2_oai
