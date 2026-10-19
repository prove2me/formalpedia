-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.preparedUniformDegreeProductiveSourceRawBounds_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T07:33:41.260547+00:00
-- url     : https://prove2.me/submissions/cdc5b36b-2e7a-479a-b2e7-6405943c77a2

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B286
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocated_short_physical_certified_bad_product_s2

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

theorem finite_residue_error_le_of_common_gap {ι : Type*} [Fintype ι]
    (width : ι → ℝ) {A cap W κ : ℝ} (hA : 0 < A) (hcap : 0 ≤ cap)
    (hW : 0 < W) (hwidth : ∀ i, 8 * A * W ≤ width i)
    (hbudget : 2 * (Fintype.card ι : ℝ) * cap ≤ κ * W) :
    (∑ i, 16 * A * cap / width i) ≤ κ := by
  have hterm (i : ι) : 16 * A * cap / width i ≤ 2 * cap / W := by
    calc
      _ ≤ 16 * A * cap / (8 * A * W) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (hwidth i)
      _ = 2 * cap / W := by field_simp; ring
  calc
    _ ≤ ∑ _i : ι, 2 * cap / W := Finset.sum_le_sum (fun i _ => hterm i)
    _ = (2 * (Fintype.card ι : ℝ) * cap) / W := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    _ ≤ κ := (div_le_iff₀ hW).mpr hbudget

theorem finite_residue_error_common_gap_budget {ι : Type*} [Fintype ι]
    (width : ι → ℝ) {A cap W κ : ℝ} (hA : 0 < A) (hcap : 0 < cap)
    (hκ : 0 < κ) (hcapW : cap ≤ W) (hwidth : ∀ i, 8 * A * W ≤ width i)
    (hWbudget : 2 * (Fintype.card ι : ℝ) * cap / κ ≤ W) :
    (∀ i, 8 * A * cap ≤ width i) ∧ (∑ i, 16 * A * cap / width i) ≤ κ := by
  refine ⟨fun i => (mul_le_mul_of_nonneg_left hcapW (by positivity)).trans (hwidth i), ?_⟩
  apply finite_residue_error_le_of_common_gap width hA hcap.le (hcap.trans_le hcapW) hwidth
  have h := (div_le_iff₀ hκ).mp hWbudget
  simpa only [mul_comm] using h

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedJointMaskedDensityComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

theorem allocatedMaskedTiltedConstant_ge_two (m : ℕ) :
    2 ≤ allocatedMaskedTiltedConstant m :=
  (Classical.choose_spec (exists_affine_coefficient_cover_tilted_family_comparison.{0, 0, 0, 0} m)).1

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.PreparedSpatialKernelBlocks
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem modularRankSmallBallExponent_eq {s : ℕ} (hs : 0 < s) :
    modularRankSmallBallExponent s = 1 / (2 : ℝ) ^ (s - 1) := by
  have hexp : 1 - (s : ℝ) = -((s - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
    ring
  rw [modularRankSmallBallExponent, hexp, Real.rpow_neg (by norm_num), Real.rpow_natCast,
    one_div]

end Erdos3

end

section

namespace Erdos3

theorem modularInitialBlockCount_threshold {s : ℕ} (hs : 0 < s) (d : ℕ) :
    ⌈2 * ((modularInitialRankStrength s d : ℝ) + d + 10) /
      modularRankSmallBallExponent s⌉₊ ≤ modularInitialBlockCount s d := by
  apply Nat.ceil_le.mpr
  rw [modularRankSmallBallExponent_eq hs, div_div_eq_mul_div, div_one]
  have hpow : 2 * (2 : ℝ) ^ (s - 1) = (2 : ℝ) ^ s := by
    rw [← pow_succ', Nat.sub_add_cancel hs]
  calc
    _ = (2 : ℝ) ^ s * ((modularInitialRankStrength s d : ℝ) + d + 10) := by
      rw [← hpow]
      ring
    _ ≤ (modularInitialBlockCount s d : ℝ) := by
      simp only [modularInitialBlockCount, Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
        Nat.cast_ofNat, Nat.cast_one]
      linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankCongruenceOutput
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}

theorem spatialDegreeOutput_card [Fintype X] (j : Fin m) :
    Fintype.card (SpatialDegreeOutput X j) = if j.val = 0 then Fintype.card X else 0 := by
  rw [Fintype.card_subtype]
  by_cases hj : j.val = 0 <;> simp only [hj, ite_true, ite_false, Finset.filter_true,
    Finset.filter_false, Finset.card_univ, Finset.card_empty]

theorem spatialDegreeOutput_sum_card [Fintype X] (hm : 0 < m) :
    (∑ j : Fin m, Fintype.card (SpatialDegreeOutput X j)) = Fintype.card X := by
  simp_rw [spatialDegreeOutput_card]
  rw [Finset.sum_eq_single (⟨0, hm⟩ : Fin m)]
  · rfl
  · intro j _ hj
    have hne : j.val ≠ 0 := fun he => hj (Fin.ext he)
    simp only [hne, ite_false]
  · simp only [Finset.mem_univ, not_true_eq_false, false_implies]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedShortRankWitnessWidth
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U basis R σ)

noncomputable local instance shortSpatialReferenceSmoothFintype_ra4a7f0_1 :
    Fintype (AllocatedFullSmoothCoefficientIndex G X I n B) := inferInstance
noncomputable local instance shortSpatialReferenceDeckFintype_ra4a7f0_1 :
    Fintype (CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E) := inferInstance
noncomputable local instance shortSpatialReferenceDeckDecidableEq_ra4a7f0_1 :
    DecidableEq (CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E) := Classical.decEq _
theorem allocatedShortPrincipalRank_active (j : Fin m)
    (i : AllocatedCongruenceIntegerAxis (allocatedShortAxis (I := I) U basis S.value) j) :
    S.value ^ (j.val + 1) < basisAxisScale (basis j) i.val := by
  exact Nat.lt_of_not_ge i.property

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

omit [Fintype X] in

theorem allocatedShortRankSelectedWidth_common_gap {L : ℕ}
    (spatial : Fin L ↪ G) (stride : X → ℕ)
    (V : Option (LayerSamplerVariables G I n B) × X → ℝ) {W : ℝ}
    (hprincipal : ∀ j i, S.value ^ (j.val + 1) < basisAxisScale (basis j) i →
      8 * (probabilityProfileLipschitz : ℝ) * W ≤
        (layerSamplerGapWidth (G := G) B R ⟨j, i⟩ / 2) *
          ((basisAxisScale (basis j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1)))
    (hspatial : ∀ l x, 8 * (probabilityProfileLipschitz : ℝ) * W ≤
      residueProfileWidth stride V (some (.inl (spatial l)), x)) :
    ∀ a, 8 * (probabilityProfileLipschitz : ℝ) * W ≤
      allocatedShortRankSelectedWidth B U basis S spatial stride V a := by
  rintro ⟨j, (x | i), l⟩
  · exact hspatial l x.val
  · exact hprincipal j i.val (allocatedShortPrincipalRank_active B U basis S j i)

theorem allocatedShortRankSelectedWidth_budget {L : ℕ}
    (spatial : Fin L ↪ G) (stride : X → ℕ)
    (V : Option (LayerSamplerVariables G I n B) × X → ℝ) {cap W κ : ℝ}
    (hcap : 0 < cap) (hκ : 0 < κ) (hcapW : cap ≤ W)
    (hprincipal : ∀ j i, S.value ^ (j.val + 1) < basisAxisScale (basis j) i →
      8 * (probabilityProfileLipschitz : ℝ) * W ≤
        (layerSamplerGapWidth (G := G) B R ⟨j, i⟩ / 2) *
          ((basisAxisScale (basis j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1)))
    (hspatial : ∀ l x, 8 * (probabilityProfileLipschitz : ℝ) * W ≤
      residueProfileWidth stride V (some (.inl (spatial l)), x))
    (hbudget : 2 * (Fintype.card (AllocatedSmoothRankCoefficientIndex X
        (allocatedShortAxis (I := I) U basis S.value) L) : ℝ) * cap / κ ≤ W) :
    (∀ a, 8 * (probabilityProfileLipschitz : ℝ) * cap ≤
      allocatedShortRankSelectedWidth B U basis S spatial stride V a) ∧
    (∑ a, 16 * (probabilityProfileLipschitz : ℝ) * cap /
      allocatedShortRankSelectedWidth B U basis S spatial stride V a) ≤ κ := by
  apply finite_residue_error_common_gap_budget
    (allocatedShortRankSelectedWidth B U basis S spatial stride V)
    (lt_of_lt_of_le zero_lt_one probabilityProfileLipschitz_one_le) hcap hκ hcapW
  · exact allocatedShortRankSelectedWidth_common_gap B U basis S spatial stride V hprincipal hspatial
  · exact hbudget

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedSameScaleBadProductBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem allocatedWitnessScaleLog_mono {P P' Q Q' : ℝ}
    (hP : 0 ≤ P) (hPP' : P ≤ P') (hQ : 0 ≤ Q) (hQQ' : Q ≤ Q') :
    allocatedWitnessScaleLog P Q ≤ allocatedWitnessScaleLog P' Q' := by
  unfold allocatedWitnessScaleLog allocatedScaleLog
  gcongr

theorem allocatedWitnessScaleLog_le_prepared_envelope {B P0 Qw E V : ℝ}
    (hB : 0 ≤ B) (hP0 : P0 ∈ Set.Icc 0 B) (hQw : Qw ∈ Set.Icc 0 B)
    (hE : 0 ≤ E) (hV : 0 ≤ V) :
    allocatedWitnessScaleLog P0 Qw ≤
      allocatedWitnessScaleLog B (2 * B + 2 * V + 5 * E + 24) := by
  apply allocatedWitnessScaleLog_mono hP0.1 hP0.2 hQw.1
  exact hQw.2.trans (by linarith)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankSmoothWidthBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m L : ℕ} {X : Type*} [Fintype X]
    {I : Fin m → Type*} {n : Fin m → ℕ}

theorem allocatedSmoothRankCoefficientIndex_card_le (hm : 0 < m)
    (inactive : LayerSamplerAxis I n → Prop) :
    Fintype.card (AllocatedSmoothRankCoefficientIndex X inactive L) ≤
      L * (Fintype.card X + ∑ j : Fin m, n j) := by
  have hcount (j : Fin m) : Fintype.card (AllocatedCongruenceIntegerAxis inactive j) ≤ n j := by
    simpa only [Fintype.card_fin] using Fintype.card_subtype_le
      (fun i : Fin (n j) => ¬ inactive ⟨j, Sum.inr i⟩)
  change Fintype.card (Σ j : Fin m,
    (SpatialDegreeOutput X j ⊕ AllocatedCongruenceIntegerAxis inactive j) × Fin L) ≤ _
  simp only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_sum, Fintype.card_fin]
  calc
    _ ≤ ∑ j : Fin m, (Fintype.card (SpatialDegreeOutput X j) + n j) * L :=
      Finset.sum_le_sum (fun j _ => Nat.mul_le_mul_right L (Nat.add_le_add_left (hcount j) _))
    _ = L * (Fintype.card X + ∑ j : Fin m, n j) := by
      rw [← Finset.sum_mul, Finset.sum_add_distrib, spatialDegreeOutput_sum_card hm, Nat.mul_comm]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.PreparedDeckRankCardinality
namespace OAI

section

namespace Erdos3

variable {J I E : Type*} [Fintype J] [Fintype I] [Fintype E]

theorem standardLatticeSection_basis_card_eq
    (W : Submodule ℝ (EuclideanSpace ℝ J))
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice J) W)]
    (o : OrthonormalBasis I ℝ W)
    (bW : Module.Basis E ℤ (latticeSection (standardEuclideanLattice J) W)) :
    Fintype.card E = Fintype.card I := by
  rw [← Module.finrank_eq_card_basis bW, ZLattice.rank ℝ,
    Module.finrank_eq_card_basis o.toBasis]

theorem preparedDeckBasis_card_eq
    (U : Submodule ℝ (J → ℝ))
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice J) (euclideanSubspace U))]
    (o : OrthonormalBasis I ℝ (euclideanSubspace U))
    (bW : Module.Basis E ℤ (latticeSection (standardEuclideanLattice J) (euclideanSubspace U))) :
    Fintype.card E = Fintype.card I :=
  standardLatticeSection_basis_card_eq (euclideanSubspace U) o bW

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedEnlargedModularAllocation
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {X₀ J₀ : Type} {m : ℕ} (prep : RankPreparationFamily X₀ J₀ m)

section Dimension

variable {J E : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (E j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

include U o bW

theorem preparedInitialRank_layer_card (j : Fin m) :
    Fintype.card (E j) + preparedSamplerTransverse prep j = Fintype.card (prep j).Coord := by
  rw [preparedDeckBasis_card_eq (U j) (o j) (bW j)]
  exact preparedSampler_axis_card prep j

theorem preparedInitialRank_dimension_le (nX M : ℕ)
    (hM : ∀ j, Fintype.card (prep j).Coord ≤ M) :
    Fintype.card (Fin nX) +
        ∑ j : Fin m, (Fintype.card (E j) + preparedSamplerTransverse prep j) ≤ nX + m * M := by
  simp only [Fintype.card_fin]
  apply Nat.add_le_add_left
  calc
    _ = ∑ j : Fin m, Fintype.card (prep j).Coord :=
      Finset.sum_congr rfl (fun j _ => preparedInitialRank_layer_card prep U o bW j)
    _ ≤ ∑ _j : Fin m, M := Finset.sum_le_sum (fun j _ => hM j)
    _ = m * M := by simp

theorem preparedInitialRank_parameters (nX M : ℕ)
    (hM : ∀ j, Fintype.card (prep j).Coord ≤ M) (hm : 0 < m) :
    0 ≤ (modularInitialRankStrength m (nX + m * M) : ℝ) ∧
    (Fintype.card (Fin nX) +
      ∑ j : Fin m, (Fintype.card (E j) + preparedSamplerTransverse prep j) ≤ nX + m * M) ∧
    ⌈2 * ((modularInitialRankStrength m (nX + m * M) : ℝ) + (nX + m * M : ℕ) + 10) /
      modularRankSmallBallExponent m⌉₊ ≤ modularInitialBlockCount m (nX + m * M) :=
  ⟨Nat.cast_nonneg _, preparedInitialRank_dimension_le prep U o bW nX M hM,
    modularInitialBlockCount_threshold hm _⟩

end Dimension

theorem preparedInitialRank_smooth_card_le (nX M : ℕ)
    (hM : ∀ j, Fintype.card (prep j).Coord ≤ M) (hm : 0 < m)
    (inactive : LayerSamplerAxis (PreparedSamplerContinuous prep)
      (preparedSamplerTransverse prep) → Prop) :
    Fintype.card (AllocatedSmoothRankCoefficientIndex (Fin nX) inactive
      (modularInitialBlockCount m (nX + m * M))) ≤
        modularInitialBlockCount m (nX + m * M) * (nX + m * M) := by
  apply (allocatedSmoothRankCoefficientIndex_card_le hm inactive).trans
  apply Nat.mul_le_mul_left
  simp only [Fintype.card_fin]
  apply Nat.add_le_add_left
  calc
    ∑ j : Fin m, preparedSamplerTransverse prep j ≤ ∑ _j : Fin m, M := by
      apply Finset.sum_le_sum
      intro j _
      have h := preparedSampler_axis_card prep j
      have := hM j
      omega
    _ = m * M := by simp

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PreparedSpatialWitnessWidth
namespace OAI

section

namespace Erdos3

private theorem witness_width_power_lower {P : ℝ} (hP : 0 ≤ P) {C : ℕ} (hC : 2 ≤ C) :
    4 * P + 3 ≤ (P + C) ^ C := by
  have hC' : (2 : ℝ) ≤ C := by exact_mod_cast hC
  have hbase : 1 ≤ P + C := by linarith
  calc
    _ ≤ (P + 2) ^ 2 := by nlinarith [sq_nonneg P]
    _ ≤ (P + C) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) _
    _ ≤ _ := pow_le_pow_right₀ hbase hC

private theorem eight_le_exp_three : (8 : ℝ) ≤ Real.exp 3 := by
  have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h3 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h1 3
  have he : Real.exp (3 : ℝ) = Real.exp (1 : ℝ) ^ 3 := by
    simp
  rw [he]
  norm_num at h3 ⊢
  exact h3

theorem spatial_witness_width_of_exp_size
    {P ρ H V d W : ℝ} {C : ℕ} (hP : 0 ≤ P) (hC : 2 ≤ C)
    (hρ : 0 < ρ) (hρinv : 1 / ρ ≤ Real.exp P)
    (hH : Real.exp ((P + C) ^ C) ≤ H) (hV : ρ * H ≤ V)
    (hd : 0 < d) (hdexp : d ≤ Real.exp P)
    (hLip : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hW : 0 ≤ W) (hWexp : W ≤ Real.exp P) :
    8 * (probabilityProfileLipschitz : ℝ) * W ≤ V / d := by
  have hquot : (8 * (probabilityProfileLipschitz : ℝ) * W * d) / ρ ≤ H := by
    calc
      _ = 8 * (probabilityProfileLipschitz : ℝ) * W * d * (1 / ρ) := by ring
      _ ≤ 8 * Real.exp P * Real.exp P * Real.exp P * Real.exp P := by
        gcongr
      _ = 8 * Real.exp (4 * P) := by
        have he : Real.exp (4 * P) = Real.exp P ^ 4 := by
          simpa using Real.exp_nat_mul P 4
        rw [he]
        ring
      _ ≤ Real.exp 3 * Real.exp (4 * P) :=
        mul_le_mul_of_nonneg_right eight_le_exp_three (Real.exp_nonneg _)
      _ = Real.exp (4 * P + 3) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp ((P + C) ^ C) := Real.exp_le_exp.mpr (witness_width_power_lower hP hC)
      _ ≤ H := hH
  apply (le_div_iff₀ hd).mpr
  calc
    _ ≤ H * ρ := (div_le_iff₀ hρ).mp hquot
    _ = ρ * H := mul_comm _ _
    _ ≤ V := hV

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedCenteredShortJointBadProduct
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

variable {m nX M : ℕ} {X₀ J₀ : Type} (prep : RankPreparationFamily X₀ J₀ m)
variable {E : Fin m → Type} [∀ j, Fintype (E j)]
variable [∀ j : Fin m, DecidableEq (RankPreparationLayer.Coord (prep j))]
variable (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale
  (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
  (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
  (J := fun j : Fin m => RankPreparationLayer.Coord (prep j))
  (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)

variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

variable (Elog Vlog : ℝ) (Q : ℕ)

include bW hC hV in

theorem exists_prepared_short_certified_physical_bad_product
    (hElog : 0 ≤ Elog) (hVlog : 0 ≤ Vlog) (hQ : 1 ≤ Q)
    (hQexp : (Q : ℝ) ≤ Real.exp Vlog)
    (hmpos : 0 < m) (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (hσ1 : ∀ j, σ j ≤ 1)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card ((PreparedSamplerContinuous prep) j) : ℝ) + 1) * R j ≤ 1/4)
    {P : ℝ} (hP : 0 ≤ P)
    (hprimitive : (((((m + 1) * ((enlargedPreparedCommonSamplerDimension m M (modularInitialBlockCount m (nX + m * M))) + 1) ^ m : ℕ)) + (enlargedPreparedCommonSamplerDimension m M (modularInitialBlockCount m (nX + m * M))) : ℕ) : ℝ) ≤ P)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hLP : (S.value : ℝ) ≤ Real.exp P)
    (hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (hbudgetP : Vlog + 3 * Elog + 16 ≤ P)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (((fun j : Fin m => RankPreparationLayer.Coord (prep j))) j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (((fun j : Fin m => RankPreparationLayer.Coord (prep j))) j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (((fun j : Fin m => RankPreparationLayer.Coord (prep j))) j → ℝ))
    (hp : ∀ j, DegreeLE (1 : Fin nX → ℕ) (j.val + 1) (poly j))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    {Ps ρ Rs Smax : ℝ} (hPs : 0 ≤ Ps) (hframePrimitive : ((((enlargedPreparedCommonSamplerDimension m M (modularInitialBlockCount m (nX + m * M))) + 1) * nX : ℕ) : ℝ) ≤ Ps)
    (hbudgetPs : Vlog + 3 * Elog + 16 ≤ Ps)
    (hρ : 0 < ρ) (hρPs : 1 / ρ ≤ Real.exp Ps)
    (stride : Fin nX → ℕ) (hstride : ∀ x, 0 < stride x)
    (hSmax : 0 ≤ Smax) (hSmaxPs : Smax ≤ Real.exp Ps) (hstrideMax : ∀ x, ((stride x * ((max Q ((quantitativeBadPrimeRadius Elog) ^ 2) : ℕ)) : ℕ) : ℝ) ≤ Smax)
    (H : Fin nX → ℝ)
    (hsize : ∀ x, Real.exp ((Ps + allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m) ≤ H x)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H Rs (U j) (poly j))
    (hRs : Real.exp ((Ps + allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m) ≤ Rs)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) (Fin nX) stride))
    (hcells : cells.Nonempty)
    (width : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℝ) (hwidth : ∀ z, 0 < width z)
    (hwide : ∀ z, ρ * H z.2 ≤ width z)
    (hfreqPs : (4 * allocatedFourierLogBudget m P + 2)^4 ≤ Ps)
    (hmassPs : 4 * allocatedFourierLogBudget m P * (4 * allocatedFourierLogBudget m P + 2)^4 +
      allocatedFourierLogBudget m P ≤ Ps)
    (hprincipal : ∀ j i, S.value ^ (j.val + 1) < basisAxisScale (b j) i →
      8 * (probabilityProfileLipschitz : ℝ) * (physicalBadProductGap (((modularInitialBlockCount m (nX + m * M)) * ((nX + m * M : ℕ)) : ℕ)) Elog Vlog Q) ≤
        (layerSamplerGapWidth (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) R ⟨j,i⟩ / 2) *
          ((basisAxisScale (b j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1)))
    (hPPS : P ≤ Ps) (hWlog : 2 * P + 2 * Vlog + 5 * Elog + 24 ≤ Ps) :
    let Dphysical := fun z : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ =>
      allocatedCoefficientDensity (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o hR hσ S
        (affineSampleCoefficientTorus U poly hm (fun k x => (z (k, x) : ℝ)))
    ∃ hD0 : ∀ z, 0 ≤ Dphysical z,
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells width z,
    ∃ hDpos : 0 < selectedResidueDensityMass stride cells width Dphysical,
    ∃ read : (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ) →
        AllocatedActualCoefficientIndex (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (Fin nX) (PreparedSamplerContinuous prep) E (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) → ℤ,
      (∀ z, allocatedReadNoise (read z) = z) ∧
      (∀ z, Dphysical z ≠ 0 →
        ∀ (primes : Finset ℕ) (hne : ∀ p : primes, NeZero p.val),
          letI := hne
          ∀ (depth : ℕ → ℕ) (q : ℕ) (hq : 0 < q),
            letI : NeZero q := ⟨hq.ne'⟩
            ∀ hdiv : ∀ p : primes, p.val ^ depth p.val ∣ q,
              coefficientDeckChartEvent U bW b hb o q
                (allocatedChartResiduePrimePowerWitness (allocatedShortAxis (I := (PreparedSamplerContinuous prep)) U b S.value) ((modularInitialRankStrength m (nX + m * M) : ℝ)) primes depth q hdiv
                  (fun v => (z v : ZMod q)))
                (affineCoefficientCoverSample U poly hm q (fun k x => (z (k, x) : ℝ))) ↔
              ∀ p : primes, allocatedActualModulusBad (allocatedShortAxis (I := (PreparedSamplerContinuous prep)) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedShortAxis (I := (PreparedSamplerContinuous prep)) U b S.value)) ((modularInitialRankStrength m (nX + m * M) : ℝ))
                (p.val ^ depth p.val) (read z)) ∧
      |selectedResidueDensityMass stride cells width Dphysical - 1| ≤ 3 * (physicalBadProductAccuracy Elog Vlog) ∧
      1 / 2 ≤ selectedResidueDensityMass stride cells width Dphysical ∧
      selectedResidueDensityMass stride cells width Dphysical ≤ 3 / 2 ∧
      0 < (quantitativeBadPrimeRadius Elog) ∧ ((quantitativeBadPrimeRadius Elog) : ℝ) ≤ Real.exp (Elog + 3) ∧
      ∀ (primes : Finset ℕ) (hprime : ∀ p ∈ primes, p.Prime),
        letI : ∀ p : primes, NeZero p.val := fun p => ⟨(hprime p.val p.property).ne_zero⟩
        ∀ (depth : ℕ → ℕ), (∀ p ∈ primes, p ^ depth p ≤ Q) →
          (∑' z, (selectedResidueDensityPMF stride cells width hwidth hZ Dphysical hD0 hDpos z).toReal *
            (if (∏ x, stride x) ^ 2 *
              (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) * (quantitativeBadPrimeRadius Elog)) <
                ∏ p ∈ primes, p ^ largestTestedBadDepth depth
                  (fun p a z => allocatedActualPrimeBad (allocatedShortAxis (I := (PreparedSamplerContinuous prep)) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedShortAxis (I := (PreparedSamplerContinuous prep)) U b S.value)) primes ((modularInitialRankStrength m ((nX + m * M : ℕ)) : ℝ)) p a (read z)) p z
              then (1 : ℝ) else 0)) ≤ Real.exp (-Elog) := by
  obtain ⟨hmCount, _, hAllocCount, _, hvCount, hIcount, hnCount, hJcount, hcoeffCount, hframeCount⟩ :=
    preparedBadProduct_input_counts prep (modularInitialBlockCount m (nX + m * M)) nX hCoord
  have hpnum : ((enlargedPreparedCommonSamplerDimension m M (modularInitialBlockCount m (nX + m * M))) : ℝ) ≤ P := (Nat.cast_le.mpr (Nat.le_add_left (enlargedPreparedCommonSamplerDimension m M (modularInitialBlockCount m (nX + m * M))) (((m + 1) * ((enlargedPreparedCommonSamplerDimension m M (modularInitialBlockCount m (nX + m * M))) + 1) ^ m : ℕ)))).trans hprimitive
  have hcoeff : ((((m + 1) * ((enlargedPreparedCommonSamplerDimension m M (modularInitialBlockCount m (nX + m * M))) + 1) ^ m : ℕ)) : ℝ) ≤ P := (Nat.cast_le.mpr (Nat.le_add_right (((m + 1) * ((enlargedPreparedCommonSamplerDimension m M (modularInitialBlockCount m (nX + m * M))) + 1) ^ m : ℕ)) (enlargedPreparedCommonSamplerDimension m M (modularInitialBlockCount m (nX + m * M))))).trans hprimitive
  have hmP : (m : ℝ) ≤ P := (Nat.cast_le.mpr hmCount).trans hpnum
  have hK : (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) : ℝ) ≤ P :=
    (Nat.cast_le.mpr hvCount).trans hpnum
  have hI : ∀ j, (Fintype.card ((PreparedSamplerContinuous prep) j) : ℝ) ≤ P := fun j => (Nat.cast_le.mpr (hIcount j)).trans hpnum
  have hn : ∀ j, ((preparedSamplerTransverse prep) j : ℝ) ≤ P := fun j => (Nat.cast_le.mpr (hnCount j)).trans hpnum
  have hJ : ∀ j, (Fintype.card (((fun j : Fin m => RankPreparationLayer.Coord (prep j))) j) : ℝ) ≤ P := fun j => (Nat.cast_le.mpr (hJcount j)).trans hpnum
  have hcount : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) (j.val+1)) : ℝ) ≤ P :=
    fun j => (Nat.cast_le.mpr (hcoeffCount j)).trans hcoeff
  have hframe : (Fintype.card (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX) : ℝ) ≤ Ps :=
    (Nat.cast_le.mpr hframeCount).trans hframePrimitive
  have hX : (Fintype.card (Fin nX) : ℝ) ≤ Ps := by
    simp only [Fintype.card_fin]
    apply le_trans (Nat.cast_le.mpr ?_) hframePrimitive
    nlinarith
  obtain ⟨hrankC, hD, hL⟩ := preparedInitialRank_parameters prep U o bW nX M hCoord hmpos
  obtain ⟨hWone, hcapW, hWbudget⟩ := physicalBadProductGap_budget (((modularInitialBlockCount m (nX + m * M)) * ((nX + m * M : ℕ)) : ℕ)) hElog hVlog Q hQ hQexp
  have hκ := physicalBadProductAccuracy_pos Elog Vlog
  have hDalloc : ((nX + m * M : ℕ)) ≤ (modularInitialBlockCount m (nX + m * M)) := by
    unfold modularInitialBlockCount
    have hpow : 0 < (2 : ℕ) ^ m := pow_pos (by norm_num) m
    calc
      nX + m * M ≤ modularInitialRankStrength m (nX + m * M) + (nX + m * M) + 10 := by omega
      _ ≤ 2 ^ m * (modularInitialRankStrength m (nX + m * M) + (nX + m * M) + 10) :=
        Nat.le_mul_of_pos_left _ hpow
      _ ≤ _ := Nat.le_succ _
  have hNsq : (((modularInitialBlockCount m (nX + m * M)) * ((nX + m * M : ℕ)) : ℕ)) ≤ (enlargedPreparedCommonSamplerDimension m M (modularInitialBlockCount m (nX + m * M))) * (enlargedPreparedCommonSamplerDimension m M (modularInitialBlockCount m (nX + m * M))) := Nat.mul_le_mul hAllocCount (hDalloc.trans hAllocCount)
  have hpnumExp : ((enlargedPreparedCommonSamplerDimension m M (modularInitialBlockCount m (nX + m * M))) : ℝ) ≤ Real.exp P := hpnum.trans (by linarith [Real.add_one_le_exp P])
  have hNexp : ((((modularInitialBlockCount m (nX + m * M)) * ((nX + m * M : ℕ)) : ℕ)) : ℝ) ≤ Real.exp (2 * P) := by
    have hh := mul_le_mul hpnumExp hpnumExp (Nat.cast_nonneg (enlargedPreparedCommonSamplerDimension m M (modularInitialBlockCount m (nX + m * M)))) (Real.exp_nonneg P)
    rw [← Real.exp_add] at hh
    have hs : (((enlargedPreparedCommonSamplerDimension m M (modularInitialBlockCount m (nX + m * M))) * (enlargedPreparedCommonSamplerDimension m M (modularInitialBlockCount m (nX + m * M))) : ℕ) : ℝ) ≤ Real.exp (2 * P) := by
      simpa only [Nat.cast_mul, two_mul] using hh
    exact (Nat.cast_le.mpr hNsq).trans hs
  have hWPs : (physicalBadProductGap (((modularInitialBlockCount m (nX + m * M)) * ((nX + m * M : ℕ)) : ℕ)) Elog Vlog Q) ≤ Real.exp Ps :=
    (physicalBadProductGap_exp_bound (((modularInitialBlockCount m (nX + m * M)) * ((nX + m * M : ℕ)) : ℕ)) hElog hVlog (by positivity : 0 ≤ 2 * P) Q hQexp hNexp).trans
      (Real.exp_le_exp.mpr hWlog)
  have hstrideExp : ∀ x, (stride x : ℝ) ≤ Real.exp Ps := by
    intro x
    apply le_trans _ (hSmaxPs)
    apply le_trans (Nat.cast_le.mpr ?_) (hstrideMax x)
    have hc : 1 ≤ ((max Q ((quantitativeBadPrimeRadius Elog) ^ 2) : ℕ)) := hQ.trans (le_max_left _ _)
    nlinarith
  have hnoiseGap : ∀ z, 8 * (probabilityProfileLipschitz : ℝ) * (physicalBadProductGap (((modularInitialBlockCount m (nX + m * M)) * ((nX + m * M : ℕ)) : ℕ)) Elog Vlog Q) ≤ residueProfileWidth stride width z := by
    intro z
    exact spatial_witness_width_of_exp_size hPs (allocatedMaskedTiltedConstant_ge_two m)
      hρ hρPs (hsize z.2) (hwide z) (by exact_mod_cast hstride z.2) (hstrideExp z.2)
      (hAP.trans (Real.exp_le_exp.mpr hPPS)) (le_trans zero_le_one hWone) hWPs
  have hcap : (0 : ℝ) < (((max Q ((quantitativeBadPrimeRadius Elog) ^ 2) : ℕ)) : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by omega : 0 < Q) (le_max_left Q ((quantitativeBadPrimeRadius Elog) ^ 2))
  have hcountSmooth := preparedInitialRank_smooth_card_le prep nX M hCoord hmpos (allocatedShortAxis (I := (PreparedSamplerContinuous prep)) U b S.value)
  have hactualBudget : 2 * (Fintype.card (AllocatedSmoothRankCoefficientIndex (Fin nX) (allocatedShortAxis (I := (PreparedSamplerContinuous prep)) U b S.value) (modularInitialBlockCount m (nX + m * M))) : ℝ) *
      (((max Q ((quantitativeBadPrimeRadius Elog) ^ 2) : ℕ)) : ℝ) / (physicalBadProductAccuracy Elog Vlog) ≤ (physicalBadProductGap (((modularInitialBlockCount m (nX + m * M)) * ((nX + m * M : ℕ)) : ℕ)) Elog Vlog Q) := by
    apply le_trans _ hWbudget
    apply div_le_div_of_nonneg_right _ hκ.le
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hcountSmooth) (by norm_num)) hcap.le
  obtain ⟨hlarge, hresidueError⟩ := allocatedShortRankSelectedWidth_budget (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S (preparedInitialRankSpatialEmbedding (m := m) nX M) stride width
    hcap hκ hcapW hprincipal (fun l x => hnoiseGap _) hactualBudget
  have hscale : ∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth stride width z := by
    intro z
    calc
      _ = 8 * (probabilityProfileLipschitz : ℝ) * 1 := (mul_one _).symm
      _ ≤ _ := (mul_le_mul_of_nonneg_left hWone (by positivity)).trans (hnoiseGap z)
  exact exists_allocated_short_physical_certified_bad_product_s2 (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U bW b hb o S C V hC hV Elog Vlog Q
    hElog hVlog hQ hQexp hmpos hR hσ hσ1 Cinv hCinv hchart hsmall hP hmP hK hRP hσP hcount hI hn hJ
    hAP hLP hCP hVP hbudgetP μ ν poly hp hm hPs hX hframe hbudgetPs hρ hρPs stride hstride
    hSmax hSmaxPs hstrideMax H hsize hrank hRs cells hcells (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedShortAxis (I := (PreparedSamplerContinuous prep)) U b S.value))
    ((modularInitialRankStrength m ((nX + m * M : ℕ)) : ℝ)) hrankC hD hL width hwidth hwide hfreqPs hmassPs hscale hlarge hresidueError

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

variable {m nX M : ℕ} {X₀ J₀ : Type} (prep : RankPreparationFamily X₀ J₀ m)
variable [∀ j : Fin m, DecidableEq (RankPreparationLayer.Coord (prep j))]
variable (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale
  (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
  (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
  (J := fun j : Fin m => RankPreparationLayer.Coord (prep j))
  (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)

theorem preparedShortCertifiedSameScaleBadProductInterface_of_bounds
    {B Elog Vlog : ℝ} (Q : ℕ) (hB : 1 ≤ B) (hMB : (M : ℝ) ≤ B) (hnXB : (nX : ℝ) ≤ B)
    (hElogB : Elog ∈ Set.Icc 0 B) (hVlogB : Vlog ∈ Set.Icc 0 B)
    (hQ : 1 ≤ Q) (hQexp : (Q : ℝ) ≤ Real.exp Vlog)
    (hmpos : 0 < m) (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp B) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp B)
    (hS : (S.value : ℝ) ≤ Real.exp (allocatedWitnessScaleLog B (2 * B + 2 * Vlog + 5 * Elog + 24)))
    (hprincipal : ∀ j i, S.value ^ (j.val + 1) < basisAxisScale (b j) i →
      8 * (probabilityProfileLipschitz : ℝ) *
        physicalBadProductGap (modularInitialBlockCount m (nX + m * M) * (nX + m * M)) Elog Vlog Q ≤
          (layerSamplerGapWidth (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
            (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) R ⟨j,i⟩ / 2) *
              ((basisAxisScale (b j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))) :
    PreparedShortCertifiedSameScaleBadProductInterface prep U b S B Elog Vlog Q := by
  unfold PreparedShortCertifiedSameScaleBadProductInterface
  intro Ps E instE bW hb o C V hC hV hR hσ hσ1
    Cinv hCinv hchart hsmall hAP hCP hVP
    instLattice instCompact instMeasurable instBorel μ instLeft instProbability ν instνLeft instνProb
    poly hp hm ρ Rs Smax hρ hρPs stride hstride
    hSmax hSmaxPs hstrideMax H hsize hrank hRs cells hcells width hwidth hwide
  let P := (B + preparedBadProductCoefficientExponent m) ^ preparedBadProductCoefficientExponent m
  have hbudget := (exists_preparedBadProductFinalBudget m).choose_spec.choose_spec
  obtain ⟨hP1, hPs1, hBP, hP0P, hprimitive, hPscale, hbudgetP, hframe, hPPS, hWlog, hfreq, hmass⟩ :=
    hbudget.2.2 hB hMB hnXB (show B ∈ Set.Icc 0 B from ⟨zero_le_one.trans hB, le_rfl⟩) hElogB hVlogB
  have hP : 0 ≤ P := zero_le_one.trans hP1
  have hPs : 0 ≤ Ps := zero_le_one.trans hPs1
  have hbudgetPs := hbudgetP.trans hPPS
  have hcounts : (((m + 1) * (enlargedPreparedCommonSamplerDimension m M
        (modularInitialBlockCount m (nX + m * M)) + 1) ^ m +
        enlargedPreparedCommonSamplerDimension m M (modularInitialBlockCount m (nX + m * M)) : ℕ) : ℝ) ≤ P := by
    simpa only [P, preparedBadProductCoefficientExponent, Nat.cast_add] using hprimitive
  exact exists_prepared_short_certified_physical_bad_product prep U bW b hb o S C V hC hV Elog Vlog Q
    hElogB.1 hVlogB.1 hQ hQexp hmpos hCoord hR hσ hσ1 Cinv hCinv hchart hsmall hP hcounts
    (fun j => (hRi j).trans (Real.exp_le_exp.mpr hBP))
    (fun j => (hσi j).trans (Real.exp_le_exp.mpr hBP))
    (hAP.trans (Real.exp_le_exp.mpr hBP)) (hS.trans (Real.exp_le_exp.mpr hPscale))
    (fun j => (hCP j).trans (Real.exp_le_exp.mpr hBP))
    (fun j => (hVP j).trans (Real.exp_le_exp.mpr hBP)) hbudgetP μ ν poly hp hm
    hPs hframe hbudgetPs hρ (hρPs.trans (Real.exp_le_exp.mpr (hBP.trans hPPS))) stride hstride
    hSmax (hSmaxPs.trans (Real.exp_le_exp.mpr (hBP.trans hPPS))) hstrideMax
    H hsize hrank hRs cells hcells width hwidth hwide hfreq hmass hprincipal hPPS hWlog

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PreparedUniformDegreeProductiveSource
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

variable {m nX M : ℕ} {X₀ J₀ : Type} (prep : RankPreparationFamily X₀ J₀ m)
variable [∀ j : Fin m, DecidableEq (RankPreparationLayer.Coord (prep j))]
variable (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale
  (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
  (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
  (J := fun j : Fin m => RankPreparationLayer.Coord (prep j))
  (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)

theorem preparedUniformDegreeProductiveSourceCertificate
    {pRadius Pscale Pseed Qw Elog Vlog : ℝ} (Qbad : ℕ)
    (hpRadius : 0 ≤ pRadius) (hPscale : 0 ≤ Pscale)
    (hPseed : 0 ≤ Pseed) (hQw : 0 ≤ Qw)
    (hElog : 0 ≤ Elog) (hVlog : 0 ≤ Vlog)
    (hQbad : 1 ≤ Qbad) (hQexp : (Qbad : ℝ) ≤ Real.exp Vlog)
    (hm : 0 < m) (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius)
    (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp Pscale)
    (hS : (S.value : ℝ) ≤ Real.exp (allocatedWitnessScaleLog Pseed Qw))
    (hprincipal : ∀ j i, S.value ^ (j.val + 1) < basisAxisScale (b j) i →
      8 * (probabilityProfileLipschitz : ℝ) *
        physicalBadProductGap (modularInitialBlockCount m (nX + m * M) * (nX + m * M))
          Elog Vlog Qbad ≤
          (layerSamplerGapWidth
            (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
            (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))
            R ⟨j, i⟩ / 2) *
              ((basisAxisScale (b j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))) :
    ∀ Bcert : ℝ,
      preparedUniformDegreeProductiveCertificateBudget M nX pRadius Pscale Pseed Qw Elog Vlog ≤ Bcert →
      PreparedShortCertifiedSameScaleBadProductInterface prep U b S Bcert Elog Vlog Qbad := by
  intro Bcert hcert
  unfold preparedUniformDegreeProductiveCertificateBudget at hcert
  have hM : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
  have hnX : 0 ≤ (nX : ℝ) := Nat.cast_nonneg nX
  have hB : 1 ≤ Bcert := by linarith only [hcert, hM, hnX, hpRadius, hPscale, hPseed, hQw, hElog, hVlog]
  have hMB : (M : ℝ) ≤ Bcert := by linarith only [hcert, hnX, hpRadius, hPscale, hPseed, hQw, hElog, hVlog]
  have hnXB : (nX : ℝ) ≤ Bcert := by linarith only [hcert, hM, hpRadius, hPscale, hPseed, hQw, hElog, hVlog]
  have hRadiusB : pRadius ≤ Bcert := by linarith only [hcert, hM, hnX, hPscale, hPseed, hQw, hElog, hVlog]
  have hScaleB : Pscale ≤ Bcert := by linarith only [hcert, hM, hnX, hpRadius, hPseed, hQw, hElog, hVlog]
  have hSeedB : Pseed ≤ Bcert := by linarith only [hcert, hM, hnX, hpRadius, hPscale, hQw, hElog, hVlog]
  have hQwB : Qw ≤ Bcert := by linarith only [hcert, hM, hnX, hpRadius, hPscale, hPseed, hElog, hVlog]
  have hEB : Elog ≤ Bcert := by linarith only [hcert, hM, hnX, hpRadius, hPscale, hPseed, hQw, hVlog]
  have hVB : Vlog ≤ Bcert := by linarith only [hcert, hM, hnX, hpRadius, hPscale, hPseed, hQw, hElog]
  apply preparedShortCertifiedSameScaleBadProductInterface_of_bounds prep U b S Qbad
    hB hMB hnXB ⟨hElog, hEB⟩ ⟨hVlog, hVB⟩ hQbad hQexp hm hCoord
    (fun j => (hRi j).trans (Real.exp_le_exp.mpr hRadiusB))
    (fun j => (hσi j).trans (Real.exp_le_exp.mpr hScaleB))
  · exact hS.trans (Real.exp_le_exp.mpr
      (allocatedWitnessScaleLog_le_prepared_envelope (zero_le_one.trans hB)
        ⟨hPseed, hSeedB⟩ ⟨hQw, hQwB⟩ hElog hVlog))
  · exact hprincipal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m nX M : ℕ} {X₀ J₀ : Type} (prep : RankPreparationFamily X₀ J₀ m)
variable [∀ j : Fin m, DecidableEq (RankPreparationLayer.Coord (prep j))]
variable (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale
  (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
  (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
  (J := fun j : Fin m => RankPreparationLayer.Coord (prep j))
  (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)

theorem preparedUniformDegreeProductiveSourceRawBounds_s2_oai
    (selection : Fin (0 + 1) ↪ EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
    (Pdetect : Polynomial ℕ) (uSource pModel pSlice : ℝ)
    (Vtail : Fin m → ℝ≥0) (u p forecastCap : ℝ)
    {Pchart Qstride Pmaster Plate Pphysical coarseTarget pRadius Pscale Pseed Qw
      gainLog gain Vlog D target Pk Prho : ℝ} (Qgood : ℕ)
    (geometry : AllocatedEarlyNativeSourceGeometryGeneral
      (B := EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))
      (U := U) (basis := b) (S := S) (s := 0) (nX := nX)
      Pchart Pscale D target Pk Prho Qstride (allocatedModelTestLog uSource pModel)
      (Real.toNNReal (Real.exp pRadius)))
    (hm : 0 < m) (hnX : 0 < nX)
    (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hpRadius : 0 ≤ pRadius) (hPseed : 0 ≤ Pseed) (hQw : 0 ≤ Qw)
    (hVlog : 0 ≤ Vlog) (hg : 0 ≤ gainLog)
    (hQgood : 1 ≤ Qgood) (hQexp : (Qgood : ℝ) ≤ Real.exp Vlog)
    (hMaster : 0 ≤ Pmaster) (hLate : Pmaster ≤ Plate)
    (hD : D ≤ Pmaster) (hnMaster : (nX : ℝ) ≤ Pmaster)
    (hRadiusMaster : pRadius ≤ Pmaster) (hScaleLate : Pscale ≤ Plate)
    (hWitnessLate : allocatedWitnessScaleLog Pseed Qw ≤ Plate)
    (hStrideMaster : Qstride ≤ Pmaster) (hPhysicalMaster : Pphysical ≤ Pmaster)
    (hgain : Real.exp (-gainLog) ≤ gain)
    (hchart : 0 ≤ Pchart) (hnChart : (nX : ℝ) ≤ Pchart)
    (hgChart : gainLog ≤ Pchart)
    (hS : (S.value : ℝ) ≤ Real.exp (allocatedWitnessScaleLog Pseed Qw))
    (hprincipal : ∀ j i, S.value ^ (j.val + 1) < basisAxisScale (b j) i →
      8 * (probabilityProfileLipschitz : ℝ) *
        physicalBadProductGap (modularInitialBlockCount m (nX + m * M) * (nX + m * M))
          (gainLog + 8) Vlog Qgood ≤
          (layerSamplerGapWidth
            (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
            (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))
            R ⟨j, i⟩ / 2) *
              ((basisAxisScale (b j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1)))
    (hξLate : (normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) (layerSamplerDegree (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))) selection
      (allocatedDetectedKernelCutoff 0 (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
        (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))))
        Pdetect (allocatedModelTestLog uSource pModel) (allocatedModelTestLog uSource pModel) ((forecastAugmentedUnitThreshold u p (Real.exp (pSlice * Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))))) (max 1 (4 * ∏ j, earlyConstantDensityCap (Fintype.card ((PreparedSamplerContinuous prep) j)) ((preparedSamplerTransverse prep) j) (R j) (Vtail j))) forecastCap) / 2)) Pphysical coarseTarget)⁻¹ ≤ Real.exp Plate) :
    let baseB0 := preparedUniformDegreeProductiveCertificateBudget
      M nX pRadius Pscale Pseed Qw (gainLog + 8) Vlog
    let Pwidth := 4 * (Plate + 8) ^ 2
    PreparedShortForecastSourceRawBounds prep U b S selection Pdetect uSource pModel pSlice
      Vtail u p forecastCap Pchart Qstride Pmaster Plate Pphysical coarseTarget
      baseB0 Vlog gainLog gain Pwidth Qgood D ∧ Plate ≤ Pwidth := by
  intro baseB0 Pwidth
  have hPlate : 0 ≤ Plate := hMaster.trans hLate
  have hLateWidth : Plate ≤ Pwidth := by
    dsimp only [Pwidth]
    nlinarith only [sq_nonneg Plate]
  have hRi (j) : (R j)⁻¹ ≤ Real.exp pRadius := by
    have h := geometry.hK j
    simpa only [Real.coe_toNNReal (Real.exp pRadius) (Real.exp_pos pRadius).le] using h
  have hcert := preparedUniformDegreeProductiveSourceCertificate prep U b S Qgood
    hpRadius geometry.hP hPseed hQw (by linarith only [hg]) hVlog hQgood hQexp hm hCoord
    hRi geometry.hσi hS hprincipal
  refine ⟨{
    hcert := hcert
    hnX := hnX
    hσ1 := fun j => (geometry.hσsmall j).trans geometry.htone
    hsmall := fun C hC hCB => (geometry.hbudgets C hC hCB).1
    hMaster := hMaster
    hLate := hLate
    hd := geometry.hdimensions
    hD := hD
    hnMaster := hnMaster
    hRi := fun j => (hRi j).trans (Real.exp_le_exp.mpr hRadiusMaster)
    hσi := fun j => (geometry.hσi j).trans (Real.exp_le_exp.mpr hScaleLate)
    hS := hS.trans (Real.exp_le_exp.mpr hWitnessLate)
    hprojection := le_rfl
    hVlog := hVlog
    hQexp := hQexp
    hg := hg
    hgain := hgain
    hstrideWidth := hStrideMaster.trans (hLate.trans hLateWidth)
    hτWidth := hPhysicalMaster.trans (hLate.trans hLateWidth)
    hξWidth := hξLate.trans (Real.exp_le_exp.mpr hLateWidth)
    hbase := ?_
    hchart := hchart
    hwidth := hPlate.trans hLateWidth
    hnChart := hnChart
    hgChart := hgChart }, hLateWidth⟩
  dsimp only [baseB0, preparedUniformDegreeProductiveCertificateBudget]
  have hPscale := geometry.hP
  positivity

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.preparedUniformDegreeProductiveSourceRawBounds_s2_oai := @OAI.Erdos3.VectorPolynomial.preparedUniformDegreeProductiveSourceRawBounds_s2_oai
