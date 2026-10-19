-- Prove2me | solution 1 for OAI.Erdos3.exists_preparedRelativePatchPowerPassage_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T10:13:13.705963+00:00
-- url     : https://prove2.me/submissions/1690a802-cd32-427a-8912-345228fa0d70

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B297
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_preparedCanonicalInitializedRelativeSource_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_preparedFiniteNestedCanonicalRequired_power_budget_of_inputPower_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_preparedRelativeEndpoint_source_bounds_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_preparedRelativePositiveForecastSource_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_relativePatchSliceConclusion_of_prepared_source_geometry_s2

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedScalarStructuralBasePower
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem exists_preparedScalarStructuralBasePower (s : ℕ) :
    ∃ baseMin : ℕ, 1 ≤ baseMin ∧
      ∀ basePower : ℕ, baseMin ≤ basePower → ∀ p : ℝ, 2 ≤ p →
        let B := (p + 2) ^ basePower
        (scalarNativeDimension s : ℝ) ≤ B ∧
          (probabilityProfileLipschitz : ℝ) ≤ Real.exp B ∧
          (normalizedSiteCutoffBound : ℝ) ≤ Real.exp B ∧ p ≤ B := by
  let profileCeil := ⌈(probabilityProfileLipschitz : ℝ)⌉₊
  let cutoffCeil := ⌈(normalizedSiteCutoffBound : ℝ)⌉₊
  let baseMin := scalarNativeDimension s + profileCeil + cutoffCeil + 1
  refine ⟨baseMin, by dsimp [baseMin]; omega, ?_⟩
  intro basePower hbasePower p hp
  dsimp only
  have hdim : scalarNativeDimension s ≤ basePower := by
    dsimp [baseMin] at hbasePower
    omega
  have hprofile : profileCeil ≤ basePower := by
    dsimp [baseMin] at hbasePower
    omega
  have hcutoff : cutoffCeil ≤ basePower := by
    dsimp [baseMin] at hbasePower
    omega
  have hone : 1 ≤ basePower := by
    dsimp [baseMin] at hbasePower
    omega
  have hpower : (basePower : ℝ) ≤ (p + 2) ^ basePower := by
    calc
      (basePower : ℝ) ≤ (2 : ℝ) ^ basePower := by
        exact_mod_cast (show basePower < 2 ^ basePower from Nat.lt_two_pow_self).le
      _ ≤ (p + 2) ^ basePower :=
        pow_le_pow_left₀ (by norm_num) (by linarith) basePower
  have hexp : (p + 2) ^ basePower ≤ Real.exp ((p + 2) ^ basePower) :=
    le_trans (by linarith) (Real.add_one_le_exp _)
  refine ⟨(Nat.cast_le.mpr hdim).trans hpower, ?_, ?_,
    le_power_budget (by linarith) hone⟩
  · exact (Nat.le_ceil _).trans ((Nat.cast_le.mpr hprofile).trans (hpower.trans hexp))
  · exact (Nat.le_ceil _).trans ((Nat.cast_le.mpr hcutoff).trans (hpower.trans hexp))

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

theorem pad_coordinate_card_le (L : RankPreparationFamily I J m) {M : ℕ}
    (hL : ∀ j, Fintype.card (L j).Coord ≤ M) :
    ∀ j, Fintype.card (L.pad q j).Coord ≤ M := by
  intro j
  by_cases hj : j.val < m
  · simpa only [pad_apply_lt L j hj] using hL ⟨j.val, hj⟩
  · rw [pad_apply_ge L j (by omega)]
    change Fintype.card PEmpty ≤ M
    simp

theorem pad_sum {V : Type*} [AddCommMonoid V]
    (L : RankPreparationFamily I J m) (hmq : m ≤ q)
    (f : RankPreparationLayer I J → V) (hf : f RankPreparationLayer.empty = 0) :
    (∑ j, f (L.pad q j)) = ∑ j, f (L j) := by
  symm
  apply Fintype.sum_of_injective (Fin.castLE hmq)
    (fun i j hij => Fin.ext (congrArg (fun k : Fin q => k.val) hij))
  · intro j hj
    have hge : m ≤ j.val := by
      by_contra hnot
      have hlt : j.val < m := by omega
      exact hj ⟨⟨j.val, hlt⟩, Fin.ext rfl⟩
    rw [pad_apply_ge L j hge, hf]
  · intro j
    rw [pad_apply_castLE]

@[simp] theorem pad_value [DecidableEq J] (L : RankPreparationFamily I J m)
    (hmq : m ≤ q) (x : I → ℝ) : (L.pad q).value x = L.value x :=
  pad_sum L hmq (fun layer => layer.value x) (RankPreparationLayer.empty_value x)

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedEarlyStructuralPowerBudget
namespace OAI

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

private theorem early_preparationCoordinateCap_bound {s m D : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hm : m ≤ s) (hD : (D : ℝ) ≤ p) :
    (preparationCoordinateCap m D (m * D) : ℝ) ≤
      p * ((s : ℝ) * p + 1) ^ s + p + (s : ℝ) * p + 1 := by
  have hT : (m : ℝ) * D ≤ (s : ℝ) * p :=
    mul_le_mul (Nat.cast_le.mpr hm) hD (Nat.cast_nonneg D) (Nat.cast_nonneg s)
  have hpowers : ((m : ℝ) * D + 1) ^ m ≤ ((s : ℝ) * p + 1) ^ s :=
    (pow_le_pow_left₀ (by positivity) (add_le_add hT le_rfl) m).trans
      (pow_le_pow_right₀ (by nlinarith [mul_nonneg (Nat.cast_nonneg s) hp]) hm)
  have hmul := mul_le_mul hD hpowers (by positivity : 0 ≤ ((m : ℝ) * D + 1) ^ m) hp
  simp only [preparationCoordinateCap, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_one]
  linarith

theorem exists_prepared_early_structural_power_budget (s paddingDepth : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 2 ≤ p →
      ∀ m D nX : ℕ, m ≤ s → (D : ℝ) ≤ p → (nX : ℝ) ≤ p →
        let M := preparationCoordinateCap m D (m * D)
        let q := max m paddingDepth
        let Jalloc := modularInitialBlockCount q (nX + q * M)
        (M : ℝ) + Jalloc + enlargedPreparedCommonSamplerDimension q M Jalloc +
          allocatedUniformChartLog (M : ℝ) ≤ (p + 2) ^ C := by
  classical
  let K := max s paddingDepth
  let A : ℕ := ∑ r : Fin (K + 1),
    (2 ^ r.val * (2 ^ (2 * r.val) * r.val.factorial + 1) + 1)
  let B : ℕ := ∑ r : Fin (K + 1), ∑ j : Fin r.val, preparedCommonBlockCount r.val j
  let Mpoly : Polynomial ℕ :=
    Polynomial.X * (Polynomial.C s * Polynomial.X + 1) ^ s + Polynomial.X +
      Polynomial.C s * Polynomial.X + 1
  let Jpoly : Polynomial ℕ :=
    Polynomial.C A * (Polynomial.X + Polynomial.C K * Mpoly + 11)
  let P : Polynomial ℕ :=
    Mpoly + Jpoly +
      (Polynomial.C ((K + 1) * (K + 3)) + Mpoly * Polynomial.C K * Polynomial.C B +
        Mpoly + Polynomial.C K + 2 +
        (Polynomial.C (K + 2) + Mpoly * Polynomial.C K * Polynomial.C K) * Jpoly) +
      20 * (Mpoly + 1) ^ 3
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_fixed_power_budget P
  refine ⟨C, hC, ?_⟩
  intro p hp m D nX hm hD hnX
  dsimp only
  let M := preparationCoordinateCap m D (m * D)
  let q := max m paddingDepth
  let Jalloc := modularInitialBlockCount q (nX + q * M)
  let Mup := p * ((s : ℝ) * p + 1) ^ s + p + (s : ℝ) * p + 1
  let Jup := (A : ℝ) * (p + (K : ℝ) * Mup + 11)
  have hp0 : 0 ≤ p := by linarith
  have hMup : 0 ≤ Mup := by dsimp [Mup]; positivity
  have hJup : 0 ≤ Jup := by dsimp [Jup]; positivity
  have hq : q ≤ K := max_le_max hm le_rfl
  have hqR : (q : ℝ) ≤ K := Nat.cast_le.mpr hq
  have hA : 2 ^ q * (2 ^ (2 * q) * q.factorial + 1) + 1 ≤ A := by
    exact Finset.single_le_sum
      (f := fun r : Fin (K + 1) =>
        2 ^ r.val * (2 ^ (2 * r.val) * r.val.factorial + 1) + 1)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ ⟨q, Nat.lt_succ_of_le hq⟩)
  have hB : (∑ j : Fin q, preparedCommonBlockCount q j) ≤ B := by
    exact Finset.single_le_sum
      (f := fun r : Fin (K + 1) => ∑ j : Fin r.val, preparedCommonBlockCount r.val j)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ ⟨q, Nat.lt_succ_of_le hq⟩)
  have hM : (M : ℝ) ≤ Mup := early_preparationCoordinateCap_bound hp0 hm hD
  have hJnat : Jalloc ≤ A * (nX + q * M + 11) :=
    (modularInitialBlockCount_linear_bound q (nX + q * M)).trans
      (Nat.mul_le_mul_right _ hA)
  have hJ : (Jalloc : ℝ) ≤ Jup := by
    have hJreal : (Jalloc : ℝ) ≤ (A : ℝ) * ((nX : ℝ) + (q : ℝ) * M + 11) := by
      exact_mod_cast hJnat
    refine hJreal.trans ?_
    dsimp only [Jup]
    gcongr
  have hdim : (enlargedPreparedCommonSamplerDimension q M Jalloc : ℝ) ≤
      ((K : ℝ) + 1) * (K + 3) + Mup * K * B + Mup + K + 2 +
        (K + 2 + Mup * K * K) * Jup := by
    rw [enlargedPreparedCommonSamplerDimension_polynomial]
    simp only [preparedCommonSamplerDimension, Nat.cast_add, Nat.cast_mul, Nat.cast_one,
      Nat.cast_ofNat]
    have hBR : ((∑ j : Fin q, preparedCommonBlockCount q j : ℕ) : ℝ) ≤ B :=
      Nat.cast_le.mpr hB
    gcongr
  have hchart : allocatedUniformChartLog (M : ℝ) ≤ 20 * (Mup + 1) ^ 3 := by
    unfold allocatedUniformChartLog
    gcongr
  have htotal : Mup + Jup +
      (((K : ℝ) + 1) * (K + 3) + Mup * K * B + Mup + K + 2 +
        (K + 2 + Mup * K * K) * Jup) + 20 * (Mup + 1) ^ 3 ≤ (p + 2) ^ C := by
    simpa [P, Mpoly, Jpoly, Mup, Jup, Polynomial.eval₂_pow,
      Nat.cast_add, Nat.cast_mul] using hbound p hp0
  exact (add_le_add (add_le_add (add_le_add hM hJ) hdim) hchart).trans htotal

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteForwardTreeStorage
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem preparedFiniteForward_slice_mul_count_le_work
    (A Cslice : ℕ) (constants : ℕ → ℕ) (n count : ℕ) {x : ℝ}
    (hA : 2 ≤ A) (hC : Cslice + 1 ≤ A) (hx : 0 ≤ x)
    (hcount : (count : ℝ) ≤ x) :
    (preparedFiniteForwardParameter A constants n x + Cslice) ^ Cslice * count ≤
      preparedFiniteForwardWork A constants n x := by
  let b := preparedFiniteForwardParameter A constants n x
  have hb : 0 ≤ b := preparedFiniteForwardParameter_nonneg A constants n hx
  have hxb : x ≤ b := le_preparedFiniteForwardParameter A constants n hx
  have hCA : (Cslice : ℝ) ≤ A := Nat.cast_le.mpr (by omega)
  have hAreal : (2 : ℝ) ≤ A := Nat.cast_le.mpr hA
  have hbase : 1 ≤ b + A := by linarith
  have hpow : (b + Cslice) ^ Cslice ≤ (b + A) ^ Cslice :=
    pow_le_pow_left₀ (add_nonneg hb (Nat.cast_nonneg Cslice))
      (add_le_add (le_refl b) hCA) Cslice
  have hcount' : (count : ℝ) ≤ b + A :=
    (hcount.trans hxb).trans (le_add_of_nonneg_right (Nat.cast_nonneg A))
  rw [preparedFiniteForwardWork_eq]
  change (b + Cslice) ^ Cslice * count ≤ (b + A) ^ A
  calc
    _ ≤ (b + A) ^ Cslice * (b + A) :=
      mul_le_mul hpow hcount' (Nat.cast_nonneg count)
        (pow_nonneg (le_trans zero_le_one hbase) Cslice)
    _ = (b + A) ^ (Cslice + 1) := (pow_succ _ _).symm
    _ ≤ (b + A) ^ A := pow_le_pow_right₀ hbase hC

theorem preparedFiniteForward_endpoint_scalar_bounds
    (A Cslice : ℕ) (constants : ℕ → ℕ) (n count : ℕ)
    {x gainLog stageLog : ℝ}
    (hA : 2 ≤ A) (hCslice : 1 ≤ Cslice) (hC : Cslice + 1 ≤ A)
    (hx : 0 ≤ x) (hgain : 0 ≤ gainLog) (hstage : 0 ≤ stageLog)
    (hcount : (count : ℝ) ≤ x) :
    let b := preparedFiniteForwardParameter A constants n x
    let p := preparedFiniteForwardWork A constants n x
    let u := preparedFiniteForwardModelPrecision A constants n x gainLog stageLog
    let cost := b + 1
    let slice := (b + Cslice) ^ Cslice
    0 ≤ p ∧ 0 ≤ u ∧ 0 ≤ cost ∧ 0 ≤ slice ∧ cost ≤ slice ∧
      slice * count ≤ p ∧ (∀ chartCost : ℝ, chartCost ≤ x → chartCost ≤ slice) ∧
      2 * cost + 6 ≤ u := by
  intro b p u cost slice
  have hb : 0 ≤ b := preparedFiniteForwardParameter_nonneg A constants n hx
  have hp : 0 ≤ p := preparedFiniteForwardWork_nonneg A constants n hx
  have hprefix : 0 ≤ preparedFiniteForwardPrefixLog A constants n x :=
    (preparedFiniteForward_prefix_bounds A constants n hx).2.1
  have hueq : u = preparedFiniteForwardPrefixLog A constants n x + gainLog +
      p + stageLog + 6 := rfl
  have hu : 0 ≤ u := by linarith
  have hCsliceReal : (1 : ℝ) ≤ Cslice := by exact_mod_cast hCslice
  have hbase : 1 ≤ b + Cslice := by linarith
  have hcost : 0 ≤ cost := by dsimp [cost]; linarith
  have hslice : 0 ≤ slice := pow_nonneg (le_trans zero_le_one hbase) _
  have hcostSlice : cost ≤ slice := by
    have hpower : b + Cslice ≤ (b + Cslice) ^ Cslice := by
      simpa only [pow_one] using pow_le_pow_right₀ hbase hCslice
    dsimp only [cost, slice]
    linarith
  have hsliceCount : slice * count ≤ p :=
    preparedFiniteForward_slice_mul_count_le_work A Cslice constants n count hA hC hx hcount
  have hchart : ∀ chartCost : ℝ, chartCost ≤ x → chartCost ≤ slice := by
    intro chartCost hchartCost
    have hxb : x ≤ b := le_preparedFiniteForwardParameter A constants n hx
    have hbcost : b ≤ cost := by dsimp [cost]; linarith
    exact hchartCost.trans (hxb.trans (hbcost.trans hcostSlice))
  have hAreal : (2 : ℝ) ≤ A := Nat.cast_le.mpr hA
  have hbaseA : 1 ≤ b + A := by linarith
  have hsquare : (b + 2) ^ 2 ≤ p := by
    rw [show p = (b + A) ^ A from preparedFiniteForwardWork_eq A constants n x]
    exact (pow_le_pow_left₀ (by linarith) (by linarith : b + 2 ≤ b + A) 2).trans
      (pow_le_pow_right₀ hbaseA hA)
  have hcostWork : 2 * cost ≤ p := by
    dsimp only [cost]
    nlinarith [sq_nonneg b]
  refine ⟨hp, hu, hcost, hslice, hcostSlice, hsliceCount, hchart, ?_⟩
  linarith

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

end Erdos3.VectorPolynomial

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

theorem boundedPrimePower_le (Q : ℕ) (p : BoundedPrime Q) : boundedPrimePower Q p ≤ Q := by
  have hQ : 0 < Q := (boundedPrime_prime Q p).pos.trans_le (boundedPrime_le Q p)
  exact Nat.pow_log_le_self p.val hQ.ne'

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedActualSlicedForecastSetup
namespace OAI

section

namespace Erdos3

theorem modularInitialRankStrength_eq_forecast (s D : ℕ) :
    modularInitialRankStrength s D = modularForecastRankConstant s D := by
  unfold modularInitialRankStrength modularForecastRankConstant
  rw [show 2 * s = s + s by omega, pow_add]
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ActualFixedSpatialSlicedTargetReal
namespace OAI

section

namespace Erdos3

theorem boundedPrimes_log_prime_power_le (Q : ℕ) :
    ∀ p ∈ boundedPrimes Q, p ^ Nat.log p Q ≤ Q := by
  intro p hp
  exact boundedPrimePower_le Q ⟨p, hp⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedSlicedForecastComparisonLogs
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem preparedSlicedForecastChildSize_lower (childLog : ℝ) :
    Real.exp childLog ≤ (preparedSlicedForecastChildSize childLog : ℝ) :=
  Nat.le_ceil _

theorem preparedSlicedForecastChildSize_upper {childLog : ℝ} (hchildLog : 0 ≤ childLog) :
    (preparedSlicedForecastChildSize childLog : ℝ) ≤ Real.exp (childLog + 1) :=
  ceil_exp_le_exp_add_one hchildLog

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem preparedSlicedForecastCommonFloor_bounds
    (periodLog childLog cost comparisonLog : ℝ) :
    let F := preparedSlicedForecastCommonFloorExponent periodLog childLog cost comparisonLog
    let Lmin := preparedSlicedForecastCommonFloor periodLog childLog cost comparisonLog
    0 ≤ F ∧ 0 < Lmin ∧ (Lmin : ℝ) ≤ Real.exp (F + 1) ∧
      preparedSlicedForecastChildSize childLog ≤ Lmin ∧
      2 * Real.exp cost ≤ (Lmin : ℝ) ∧
      (∀ T : ℕ, (T : ℝ) ≤ Real.exp periodLog → T ≤ Lmin) ∧
      (∀ Lcompare : ℕ, (Lcompare : ℝ) ≤ Real.exp comparisonLog → Lcompare ≤ Lmin) := by
  intro F Lmin
  have hF : 0 ≤ F := le_max_left _ _
  have hp : periodLog ≤ F := (le_max_left _ _).trans (le_max_right _ _)
  have hc : childLog ≤ F :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hs : cost + 1 ≤ F :=
    (le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))
  have ha : comparisonLog ≤ F :=
    (le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))
  have hfloor : Real.exp F ≤ (Lmin : ℝ) := Nat.le_ceil _
  have hnat (a : ℝ) (haF : a ≤ F) (k : ℕ) (hk : (k : ℝ) ≤ Real.exp a) :
      k ≤ Lmin := by
    exact_mod_cast hk.trans ((Real.exp_le_exp.mpr haF).trans hfloor)
  refine ⟨hF, one_le_ceil_exp F, ceil_exp_le_exp_add_one hF, ?_, ?_, hnat _ hp, hnat _ ha⟩
  · exact Nat.ceil_mono (Real.exp_le_exp.mpr hc)
  · have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1 : ℝ)]
    calc
      2 * Real.exp cost ≤ Real.exp 1 * Real.exp cost :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg cost)
      _ = Real.exp (cost + 1) := by rw [← Real.exp_add, add_comm]
      _ ≤ Real.exp F := Real.exp_le_exp.mpr hs
      _ ≤ Lmin := hfloor

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedRelativeEndpointSourceBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem preparedRelativeEndpointMinimumScale_bounds
    {seed : ℝ} (hseed : 0 ≤ seed) (periodLog childLog cost comparisonLog : ℝ) :
    let Lmin := preparedRelativeEndpointMinimumScale seed periodLog childLog cost comparisonLog
    let Pmin := preparedRelativeEndpointMinimumLog seed periodLog childLog cost comparisonLog
    0 ≤ Pmin ∧ 1 ≤ Lmin ∧ (Lmin : ℝ) ≤ Real.exp Pmin ∧
      ⌈Real.exp seed⌉₊ ≤ Lmin ∧
      preparedSlicedForecastCommonFloor periodLog childLog cost comparisonLog ≤ Lmin ∧
      preparedSlicedForecastChildSize childLog ≤ Lmin ∧
      2 * Real.exp cost ≤ (Lmin : ℝ) ∧
      (∀ T : ℕ, (T : ℝ) ≤ Real.exp periodLog → T ≤ Lmin) ∧
      (∀ Lcompare : ℕ, (Lcompare : ℝ) ≤ Real.exp comparisonLog → Lcompare ≤ Lmin) := by
  intro Lmin Pmin
  obtain ⟨hF, hL, hLexp, hchild, hcost, hperiod, hcompare⟩ :=
    preparedSlicedForecastCommonFloor_bounds periodLog childLog cost comparisonLog
  have hseedFloor : ⌈Real.exp seed⌉₊ ≤ Lmin := le_max_left _ _
  have hcommon : preparedSlicedForecastCommonFloor periodLog childLog cost comparisonLog ≤ Lmin :=
    le_max_right _ _
  have hseedP : seed + 1 ≤ Pmin := le_max_left _ _
  have hcommonP :
      preparedSlicedForecastCommonFloorExponent periodLog childLog cost comparisonLog + 1 ≤ Pmin :=
    le_max_right _ _
  refine ⟨by linarith only [hseed, hseedP],
    (one_le_ceil_exp seed).trans hseedFloor, ?_, hseedFloor, hcommon,
    hchild.trans hcommon, hcost.trans (Nat.cast_le.mpr hcommon),
    fun T hT => (hperiod T hT).trans hcommon,
    fun L hL => (hcompare L hL).trans hcommon⟩
  change ((max ⌈Real.exp seed⌉₊
    (preparedSlicedForecastCommonFloor periodLog childLog cost comparisonLog) : ℕ) : ℝ) ≤ _
  rw [Nat.cast_max]
  exact max_le ((ceil_exp_le_exp_add_one hseed).trans (Real.exp_le_exp.mpr hseedP))
    (hLexp.trans (Real.exp_le_exp.mpr hcommonP))

theorem preparedRelativeEndpointGoodCutoff_bounds {Ptest : ℝ} (hPtest : 0 ≤ Ptest) :
    0 ≤ preparedRelativeEndpointGoodLog Ptest ∧
    1 ≤ preparedRelativeEndpointGoodCutoff Ptest ∧
    Real.exp (2 * Ptest) ≤ (preparedRelativeEndpointGoodCutoff Ptest : ℝ) ∧
    (preparedRelativeEndpointGoodCutoff Ptest : ℝ) ≤
      Real.exp (preparedRelativeEndpointGoodLog Ptest) := by
  refine ⟨by unfold preparedRelativeEndpointGoodLog; positivity,
    one_le_ceil_exp _, Nat.le_ceil _, ?_⟩
  exact ceil_exp_le_exp_add_one (by positivity)

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedExternalCandidateAllSiteLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

theorem allocatedExternalConditionalExcessExponent_spec (m : ℕ) :
    2 ≤ allocatedExternalConditionalExcessExponent m ∧
      AllocatedCenteredNarrowPrescribedMarginalPointwiseStatement.{0,0,0,0,0,0}
        m (allocatedExternalConditionalExcessExponent m) :=
  (exists_allocated_centered_narrow_prescribed_marginal_pointwise.{0,0,0,0,0,0} m).choose_spec

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteScheduleLocalScalarConstruction
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

theorem preparedFiniteScheduleDirectCoarse_requested {K : Type*} [Fintype K]
    (gainLog : K → ℝ) (requestedCoarse : ℝ) :
    requestedCoarse ≤ preparedFiniteScheduleDirectCoarse gainLog requestedCoarse :=
  le_max_right _ _

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedRelativeFinalPower
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem preparedFinalScalarBudget_ready_requirements
    (m degree D Dmod cardVars : ℕ)
    {t childCost preparationP crtBudget qcap qnative cost : ℝ}
    (ht : 1 ≤ t) (hchild : childCost ≤ t)
    (hRank : (degree : ℝ) * D ≤ t) (hDmod : (Dmod : ℝ) ≤ t)
    (hCRTzero : 0 ≤ crtBudget) (hCRT : crtBudget ≤ t)
    (hPrepzero : 0 ≤ preparationP) (hPrep : preparationP ≤ t)
    (hNorm : (((childCost + (cardVars : ℝ) + 2) + 2) ^
      (exists_relative_finite_returned_fiber_normalization.{0,0} degree).choose) ≤ t)
    (hcap : qcap ≤ t) (hnative : qnative ≤ t) (hcost : cost ≤ t) :
    let budget := preparedFinalScalarBudget m degree t
    1 ≤ budget ∧
      childCost + (degree : ℝ) * D ≤ budget ∧
      (Dmod : ℝ) ≤ budget ∧
      2048 * crtBudget ^ 3 +
        (preparationP + 2) ^ (preparedIntegralBasisExponent m + 1) ≤ budget ∧
      2 * (((childCost + (cardVars : ℝ) + 2) + 2) ^
        (exists_relative_finite_returned_fiber_normalization.{0,0} degree).choose) + 1 ≤ budget ∧
      qcap ≤ budget ∧ qnative ≤ budget ∧ cost ≤ budget := by
  intro budget
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hcube : 0 ≤ 2048 * t ^ 3 := mul_nonneg (by norm_num) (pow_nonneg ht0 _)
  have hpower : 0 ≤ (t + 2) ^ (preparedIntegralBasisExponent m + 1) :=
    pow_nonneg (by linarith only [ht0]) _
  have hdegree : 0 ≤ (degree : ℝ) * t := mul_nonneg (Nat.cast_nonneg _) ht0
  have htwo : 2 * t + 1 ≤ budget := by
    dsimp only [budget, preparedFinalScalarBudget]
    linarith only [hcube, hpower, hdegree]
  have htBudget : t ≤ budget := (by linarith only [ht0] : t ≤ 2 * t + 1).trans htwo
  have hmatrixBase : 2048 * t ^ 3 +
      (t + 2) ^ (preparedIntegralBasisExponent m + 1) ≤ budget := by
    dsimp only [budget, preparedFinalScalarBudget]
    linarith only [ht0, hdegree]
  have hmatrix : 2048 * crtBudget ^ 3 +
      (preparationP + 2) ^ (preparedIntegralBasisExponent m + 1) ≤ budget := by
    apply le_trans _ hmatrixBase
    exact add_le_add
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hCRTzero hCRT 3) (by norm_num))
      (pow_le_pow_left₀ (by linarith only [hPrepzero])
        (by linarith only [hPrep] : preparationP + 2 ≤ t + 2)
        (preparedIntegralBasisExponent m + 1))
  refine ⟨ht.trans htBudget, ?_, hDmod.trans htBudget, hmatrix, ?_,
    hcap.trans htBudget, hnative.trans htBudget, hcost.trans htBudget⟩
  · exact (by linarith only [hchild, hRank] : childCost + (degree : ℝ) * D ≤
      2 * t + 1).trans htwo
  · exact (by linarith only [hNorm] :
      2 * (((childCost + (cardVars : ℝ) + 2) + 2) ^
        (exists_relative_finite_returned_fiber_normalization.{0,0} degree).choose) + 1 ≤
          2 * t + 1).trans htwo

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem preparedRelativeFinalEnvelope_bounds
    (degree basePower inputPower preparationPower requiredPower : ℕ)
    (discount : ℝ) {p K : ℝ} (hp : 0 ≤ p)
    (hK : K ≤ ((p + 2) ^ basePower + 2) ^ inputPower) :
    let t := preparedRelativeFinalEnvelope degree basePower inputPower
      preparationPower requiredPower discount p
    1 ≤ t ∧
      max ((p + 2) ^ preparationPower) ((p + 2) ^ requiredPower + 1) ≤ t ∧
      K ≤ t ∧ discount⁻¹ ≤ t ∧ (p + 2) ^ basePower ≤ t ∧
      (degree : ℝ) * p ≤ t ∧ max 1 (max discount⁻¹ K) ≤ t := by
  intro t
  have hb : 0 ≤ p + 2 := by linarith only [hp]
  have hprep := pow_nonneg hb preparationPower
  have hreq := pow_nonneg hb requiredPower
  have hbase := pow_nonneg hb basePower
  have hinput := pow_nonneg (add_nonneg hbase (by norm_num : (0 : ℝ) ≤ 2)) inputPower
  have hceil := Nat.cast_nonneg (α := ℝ) ⌈discount⁻¹⌉₊
  have hdegree := mul_nonneg (Nat.cast_nonneg (α := ℝ) degree) hp
  have hinv : discount⁻¹ ≤ (⌈discount⁻¹⌉₊ : ℝ) := Nat.le_ceil _
  have ht : 1 ≤ t := by
    dsimp only [t, preparedRelativeFinalEnvelope]
    linarith only [hprep, hreq, hbase, hinput, hceil, hdegree]
  have hlate : max ((p + 2) ^ preparationPower) ((p + 2) ^ requiredPower + 1) ≤ t := by
    apply max_le <;> dsimp only [t, preparedRelativeFinalEnvelope] <;>
      linarith only [hprep, hreq, hbase, hinput, hceil, hdegree]
  have hKt : K ≤ t := by
    dsimp only [t, preparedRelativeFinalEnvelope]
    linarith only [hK, hprep, hreq, hbase, hceil, hdegree]
  have hit : discount⁻¹ ≤ t := by
    dsimp only [t, preparedRelativeFinalEnvelope]
    linarith only [hinv, hprep, hreq, hbase, hinput, hdegree]
  have hbt : (p + 2) ^ basePower ≤ t := by
    dsimp only [t, preparedRelativeFinalEnvelope]
    linarith only [hprep, hreq, hinput, hceil, hdegree]
  have hdt : (degree : ℝ) * p ≤ t := by
    dsimp only [t, preparedRelativeFinalEnvelope]
    linarith only [hprep, hreq, hbase, hinput, hceil]
  exact ⟨ht, hlate, hKt, hit, hbt, hdt, max_le ht (max_le hit hKt)⟩

theorem preparedRelativeFinalEnvelope_ready_requirements
    (m degree D Dmod cardVars basePower inputPower preparationPower requiredPower : ℕ)
    (discount : ℝ) {p K childCost preparationP qcap qnative cost : ℝ}
    (hp : 0 ≤ p) (hK : K ≤ ((p + 2) ^ basePower + 2) ^ inputPower)
    (hD : (D : ℝ) ≤ p) (hDmod : (Dmod : ℝ) ≤ K)
    (hchild : childCost ≤ (p + 2) ^ basePower)
    (hPrepzero : 0 ≤ preparationP)
    (hPrep : preparationP ≤ max ((p + 2) ^ basePower)
      (max ((p + 2) ^ preparationPower) ((p + 2) ^ requiredPower + 1)))
    (hNorm : (((childCost + (cardVars : ℝ) + 2) + 2) ^
      (exists_relative_finite_returned_fiber_normalization.{0,0} degree).choose) ≤
        (p + 2) ^ basePower)
    (hcap : qcap ≤ K) (hnative : qnative ≤ K) (hcost : cost ≤ K) :
    let t := preparedRelativeFinalEnvelope degree basePower inputPower
      preparationPower requiredPower discount p
    let crtBudget := max 1 (max discount⁻¹ K)
    let budget := preparedFinalScalarBudget m degree t
    1 ≤ budget ∧
      childCost + (degree : ℝ) * D ≤ budget ∧
      (Dmod : ℝ) ≤ budget ∧
      2048 * crtBudget ^ 3 +
        (preparationP + 2) ^ (preparedIntegralBasisExponent m + 1) ≤ budget ∧
      2 * (((childCost + (cardVars : ℝ) + 2) + 2) ^
        (exists_relative_finite_returned_fiber_normalization.{0,0} degree).choose) + 1 ≤ budget ∧
      qcap ≤ budget ∧ qnative ≤ budget ∧ cost ≤ budget := by
  intro t crtBudget budget
  obtain ⟨ht, hLateT, hKT, _, hBT, hDegreeT, hCRTT⟩ :=
    preparedRelativeFinalEnvelope_bounds degree basePower inputPower
      preparationPower requiredPower discount hp hK
  have hCRTzero : 0 ≤ crtBudget := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
  exact preparedFinalScalarBudget_ready_requirements m degree D Dmod cardVars
    ht (hchild.trans hBT)
    ((mul_le_mul_of_nonneg_left hD (Nat.cast_nonneg degree)).trans hDegreeT)
    (hDmod.trans hKT) hCRTzero hCRTT hPrepzero
    (hPrep.trans (max_le hBT hLateT)) (hNorm.trans hBT)
    (hcap.trans hKT) (hnative.trans hKT) (hcost.trans hKT)

theorem exists_preparedRelativeFinalExtraction_power
    (m degree basePower inputPower preparationPower requiredPower : ℕ)
    (discount : ℝ) :
    ∃ passagePower : ℕ, 2 ≤ passagePower ∧ ∀ p : ℝ, 0 ≤ p →
      let t := preparedRelativeFinalEnvelope degree basePower inputPower
        preparationPower requiredPower discount p
      spatialPatchExtractionCost (recoveredKernelScalarBudget
        (preparedFinalScalarBudget m degree t)) ≤ (p + 2) ^ passagePower := by
  let X : Polynomial ℕ := Polynomial.X
  let t : Polynomial ℕ := 2 + (X + 2) ^ preparationPower + (X + 2) ^ requiredPower +
    ((X + 2) ^ basePower + 2) ^ inputPower + Polynomial.C ⌈discount⁻¹⌉₊ +
      (X + 2) ^ basePower + Polynomial.C degree * X
  let B : Polynomial ℕ := 2048 * t ^ 3 +
    (t + 2) ^ (preparedIntegralBasisExponent m + 1) + 2 * t + 1 + Polynomial.C degree * t
  obtain ⟨C, hC, hbound⟩ :=
    exists_natPolynomial_fixed_power_budget (20 * (8 * (B + 1) ^ 2 + 1) ^ 2)
  refine ⟨C, hC, ?_⟩
  intro p hp
  simpa [B, t, X, preparedRelativeFinalEnvelope, preparedFinalScalarBudget,
    recoveredKernelScalarBudget, spatialPatchExtractionCost, Polynomial.eval₂_pow] using hbound p hp

theorem preparedRelativeFinalExtraction_side_floor
    {X : Type*} (N : X → ℕ) {p extraction : ℝ} {C passagePower : ℕ}
    (hp : 0 ≤ p) (hC : C ≤ passagePower)
    (hextraction : extraction ≤ (p + 2) ^ C)
    (hN : ∀ i, Real.exp ((p + 2) ^ passagePower) ≤ (N i : ℝ)) :
    extraction ≤ (p + 2) ^ passagePower ∧
      ∀ i, Real.exp extraction ≤ (N i : ℝ) := by
  have h := hextraction.trans (pow_le_pow_right₀ (by linarith only [hp]) hC)
  exact ⟨h, fun i => (Real.exp_le_exp.mpr h).trans (hN i)⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.PreparedRoundedRank
namespace OAI

section

namespace Erdos3

theorem preparedRoundedRank_exp_le (p : ℝ) (e : ℕ) :
    Real.exp ((p + 2)^e) ≤ (preparedRoundedRank p e : ℝ) :=
  Nat.le_ceil _

theorem preparedRoundedRank_one_le (p : ℝ) (e : ℕ) :
    1 ≤ preparedRoundedRank p e := by
  have hpos := (Real.exp_pos ((p + 2)^e)).trans_le (preparedRoundedRank_exp_le p e)
  have : 0 < preparedRoundedRank p e := by exact_mod_cast hpos
  omega

theorem preparedRoundedRank_exp_requirement {p required : ℝ} {e : ℕ}
    (hrequired : required ≤ (p + 2)^e) :
    Real.exp required ≤ (preparedRoundedRank p e : ℝ) :=
  (Real.exp_le_exp.mpr hrequired).trans (preparedRoundedRank_exp_le p e)

end Erdos3

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedFiniteNestedCanonicalEarlyPrimitiveBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

theorem preparedCommonRadiusPrimitiveExponent_two_le (s : ℕ) :
    2 ≤ preparedCommonRadiusPrimitiveExponent s :=
  (exists_preparedCommonRadiusPrimitive_budget s).choose_spec.1

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedNestedEndpointDimensionBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

theorem preparedNestedEndpointDimensionExponent_two_le (s : ℕ) :
    2 ≤ preparedNestedEndpointDimensionExponent s :=
  (exists_endpointDimension_uniform_budget s).choose_spec.1

theorem preparedNestedEndpointDimension_bounds
    (s m : ℕ) (hm : m ≤ s) (A : ℕ) (constants : ℕ → ℕ)
    (innerDepth outer inner : ℕ) {Bstruct pnum : ℝ}
    (hA : preparedNestedEndpointDimensionExponent s ≤ A)
    (houter : 1 ≤ outer) (hB : 0 ≤ Bstruct) (hnum : pnum ∈ Set.Icc 0 Bstruct)
    (nX M : ℕ) (hnX : (nX : ℝ) ≤ Bstruct) (hM : (M : ℝ) ≤ Bstruct) :
    allocatedComparisonDimension m pnum ≤ preparedFiniteForwardParameter A constants inner
      (candidateNestedForwardSeed A constants innerDepth outer Bstruct) ∧
    ((nX + m * M : ℕ) : ℝ) ≤ preparedFiniteForwardParameter A constants inner
      (candidateNestedForwardSeed A constants innerDepth outer Bstruct) := by
  have hAtwo := (preparedNestedEndpointDimensionExponent_two_le s).trans hA
  have hlocal := (exists_endpointDimension_uniform_budget s).choose_spec.2 m hm
    hB hnum nX M hnX hM
  have hwork := preparedFiniteForward_shiftedPower_le_work A
    (preparedNestedEndpointDimensionExponent s) constants innerDepth hAtwo hA hB
  have hseed : preparedFiniteForwardWork A constants innerDepth Bstruct ≤
      candidateNestedForwardSeed A constants innerDepth outer Bstruct := by
    simpa only [candidateNestedForwardSeed_succ, candidateNestedForwardSeed_zero] using
      candidateNestedForwardSeed_monotone A constants innerDepth hAtwo hB houter
  have hparameter := le_preparedFiniteForwardParameter A constants inner
    (candidateNestedForwardSeed_nonneg A constants innerDepth outer hB)
  exact ⟨hlocal.1.trans (hwork.trans (hseed.trans hparameter)),
    hlocal.2.trans (hwork.trans (hseed.trans hparameter))⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteNestedEndpointRequirement
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

theorem le_preparedConditionalExcessRequired (m : ℕ) (Plate E : ℝ) :
    E ≤ preparedConditionalExcessRequired m Plate E := by
  let C := allocatedExternalConditionalExcessExponent m
  have hC : 2 ≤ C := (allocatedExternalConditionalExcessExponent_spec m).1
  have hCReal : (2 : ℝ) ≤ C := Nat.cast_le.mpr hC
  have hbase : 1 ≤ max (4 * (Plate + 8) ^ 2) E + C := by
    have hzero : (0 : ℝ) ≤ max (4 * (Plate + 8) ^ 2) E :=
      (by positivity : (0 : ℝ) ≤ 4 * (Plate + 8) ^ 2).trans (le_max_left _ _)
    linarith only [hzero, hCReal]
  calc
    E ≤ max (4 * (Plate + 8) ^ 2) E + C :=
      (le_max_right _ _).trans (le_add_of_nonneg_right (Nat.cast_nonneg _))
    _ = (max (4 * (Plate + 8) ^ 2) E + C) ^ 1 := (pow_one _).symm
    _ ≤ (max (4 * (Plate + 8) ^ 2) E + C) ^ C :=
      pow_le_pow_right₀ hbase (by omega)

theorem preparedNestedFrontProjectionEnvelope_endpoint_le
    {K : Type*} [Fintype K]
    (A : ℕ) (constants : ℕ → ℕ) (innerDepth : ℕ)
    (outer inner : K → ℕ) (native : K → ℝ)
    {x gainLog stageLog : ℝ} (endpoint : ℝ)
    (hA : 2 ≤ A) (hx : 0 ≤ x)
    (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x) :
    endpoint ≤ preparedNestedFrontProjectionEnvelope A constants innerDepth
      outer inner native x gainLog stageLog endpoint := by
  have hsum : 0 ≤ ∑ k : K, preparedFiniteForwardFrontProjectionPrecision
      (preparedFiniteForwardModelPrecision A constants (inner k)
        (candidateNestedForwardSeed A constants innerDepth (outer k) x) gainLog stageLog)
      (preparedFiniteForwardWork A constants (inner k)
        (candidateNestedForwardSeed A constants innerDepth (outer k) x)) (native k) := by
    apply Finset.sum_nonneg
    intro k _
    have hseed := le_candidateNestedForwardSeed A constants innerDepth (outer k) hA hx
    have hseed0 := candidateNestedForwardSeed_nonneg A constants innerDepth (outer k) hx
    exact preparedFiniteForwardFrontProjectionPrecision_nonneg
      (preparedFiniteForward_model_precision_bounds A constants (inner k) hseed0
        ⟨hg.1, hg.2.trans hseed⟩ ⟨hs.1, hs.2.trans hseed⟩).1
      (preparedFiniteForwardWork_nonneg A constants (inner k) hseed0)
  unfold preparedNestedFrontProjectionEnvelope
  linarith only [hsum]

theorem preparedFiniteNestedSourceRequired_endpoint_le
    {Slot : Type*} [Fintype Slot]
    (m A : ℕ) (constants : ℕ → ℕ) (innerDepth outerDepth cutoff : ℕ)
    (x anchorRequired Plate E : ℝ) (detectorRequired : Slot → ℝ)
    {endpoint : ℝ} (hendpoint : endpoint ≤ E) :
    endpoint ≤ preparedFiniteNestedSourceRequired A constants innerDepth outerDepth cutoff
      x anchorRequired (preparedConditionalExcessRequired m Plate E) detectorRequired :=
  hendpoint.trans ((le_preparedConditionalExcessRequired m Plate E).trans
    (conditionalRequired_le_preparedFiniteNestedSourceRequired A constants innerDepth outerDepth cutoff
      x anchorRequired (preparedConditionalExcessRequired m Plate E) detectorRequired))

end Erdos3.VectorPolynomial

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

private theorem early_input_components {p t c z r B : ℝ} (s : ℕ)
    (hp : 0 ≤ p) (ht : 0 ≤ t) (hc : 0 ≤ c) (hz : 0 ≤ z) (hr : 0 ≤ r)
    (hB : r + 2 * z + ((s : ℝ) + 2) * c + 6 * t + p + s + 60 ≤ B) :
    z ≤ B ∧ r ≤ B ∧ p + 16 + ((s : ℝ) + 1) * c + z ≤ B ∧
      c + 1 ≤ B ∧ 6 * t + 35 ≤ B := by
  have hsc : 0 ≤ (s : ℝ) * c := mul_nonneg (Nat.cast_nonneg s) hc
  have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  constructor
  · nlinarith only [hp, ht, hc, hz, hr, hs, hsc, hB]
  constructor
  · nlinarith only [hp, ht, hc, hz, hr, hs, hsc, hB]
  constructor
  · nlinarith only [hp, ht, hc, hz, hr, hs, hsc, hB]
  constructor
  · nlinarith only [hp, ht, hc, hz, hr, hs, hsc, hB]
  · nlinarith only [hp, ht, hc, hz, hr, hs, hsc, hB]

theorem exists_preparedRelative_structural_input_power (s : ℕ) :
    ∃ relativePower : ℕ, 2 ≤ relativePower ∧ ∀ {p : ℝ}, 2 ≤ p →
    ∀ D nX : ℕ, (D : ℝ) ≤ p → (nX : ℝ) ≤ p →
      let M := preparationCoordinateCap s D (s * D)
      let Jalloc := modularInitialBlockCount s (nX + s * M)
      let dim := enlargedPreparedCommonSamplerDimension s M Jalloc
      let pRelative := (p + 2) ^ relativePower
      p ≤ pRelative ∧ (s : ℝ) + 3 ≤ pRelative ∧
        (M : ℝ) ≤ pRelative ∧ (Jalloc : ℝ) ≤ pRelative ∧
        (dim : ℝ) ≤ pRelative ∧ allocatedUniformChartLog (M : ℝ) + 1 ≤ pRelative := by
  obtain ⟨C, _, hstruct⟩ := exists_prepared_early_structural_power_budget s s
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + 2) ^ C + X + Polynomial.C (s + 3) + 2
  obtain ⟨relativePower, hpower, hbound⟩ := exists_natPolynomial_fixed_power_budget P
  refine ⟨relativePower, hpower, ?_⟩
  intro p hp D nX hD hnX M Jalloc dim pRelative
  have hp0 : 0 ≤ p := by linarith
  have hb : (p + 2) ^ C + p + ((s : ℝ) + 3) + 2 ≤ pRelative := by
    simpa [P, X, Polynomial.eval₂_pow, Nat.cast_add] using hbound p hp0
  have hs := hstruct p hp s D nX le_rfl hD hnX
  simp only [max_self] at hs
  change (M : ℝ) + Jalloc + dim + allocatedUniformChartLog (M : ℝ) ≤ (p + 2) ^ C at hs
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  have hJ : (0 : ℝ) ≤ Jalloc := Nat.cast_nonneg _
  have hdim : (0 : ℝ) ≤ dim := Nat.cast_nonneg _
  have hchart : 0 ≤ allocatedUniformChartLog (M : ℝ) := by
    unfold allocatedUniformChartLog
    positivity
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have hC0 : 0 ≤ (p + 2) ^ C := by positivity
  clear_value pRelative M Jalloc dim
  exact ⟨by linarith only [hb, hC0, hs0], by linarith only [hb, hC0, hp0],
    by linarith only [hb, hs, hJ, hdim, hchart, hp0, hs0],
    by linarith only [hb, hs, hM, hdim, hchart, hp0, hs0],
    by linarith only [hb, hs, hM, hJ, hchart, hp0, hs0],
    by linarith only [hb, hs, hM, hJ, hdim, hp0, hs0]⟩

theorem exists_preparedRelative_candidate_input_powers
    (s relativePower childExponent normalizationPower regularityPower : ℕ) :
    ∃ basePower precisionPower : ℕ, 2 ≤ basePower ∧ 2 ≤ precisionPower ∧
    ∀ {p vars : ℝ}, 0 ≤ p → 0 ≤ vars → vars ≤ (p + 2) ^ relativePower →
      let pRelative := (p + 2) ^ relativePower
      let childCost := (pRelative + 4) ^ childExponent
      let normBudget := (childCost + vars + 4) ^ normalizationPower
      let Bstruct := (p + 2) ^ basePower
      normBudget ≤ Bstruct ∧ (normBudget + 2) ^ regularityPower ≤ Bstruct ∧
        p + 16 + ((s : ℝ) + 1) * childCost + normBudget ≤ Bstruct ∧
        childCost + 1 ≤ Bstruct ∧ 6 * pRelative + 35 ≤ Bstruct ∧
        3 * pRelative + 130 ≤ (p + 2) ^ precisionPower := by
  let X : Polynomial ℕ := Polynomial.X
  let t := (X + 2) ^ relativePower
  let c := (t + 4) ^ childExponent
  let z := (c + t + 4) ^ normalizationPower
  let r := (z + 2) ^ regularityPower
  let P := r + 2 * z + (Polynomial.C s + 2) * c + 6 * t + X + Polynomial.C s + 60
  obtain ⟨basePower, hbase, hbound⟩ := exists_natPolynomial_fixed_power_budget P
  obtain ⟨precisionPower, hprecision, herror⟩ :=
    exists_natPolynomial_fixed_power_budget (3 * t + 130)
  refine ⟨basePower, precisionPower, hbase, hprecision, ?_⟩
  intro p vars hp hv hvt pRelative childCost normBudget Bstruct
  let zBound := (childCost + pRelative + 4) ^ normalizationPower
  let rBound := (zBound + 2) ^ regularityPower
  have ht0 : 0 ≤ pRelative := by dsimp only [pRelative]; positivity
  have hc0 : 0 ≤ childCost := by dsimp only [childCost]; positivity
  have hz0 : 0 ≤ zBound := by dsimp only [zBound]; positivity
  have hr0 : 0 ≤ rBound := by dsimp only [rBound]; positivity
  have hn0 : 0 ≤ normBudget := by dsimp only [normBudget]; positivity
  have hn : normBudget ≤ zBound :=
    pow_le_pow_left₀ (by positivity : 0 ≤ childCost + vars + 4)
      (by linarith only [hvt] : childCost + vars + 4 ≤ childCost + pRelative + 4) _
  have hreg : (normBudget + 2) ^ regularityPower ≤ rBound :=
    pow_le_pow_left₀ (by positivity) (add_le_add hn (le_refl (2 : ℝ))) _
  have hb : rBound + 2 * zBound + ((s : ℝ) + 2) * childCost + 6 * pRelative + p + s + 60 ≤ Bstruct := by
    simpa only [P, r, z, c, t, X, Polynomial.eval₂_add, Polynomial.eval₂_mul,
      Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_ofNat,
      Nat.coe_castRingHom, rBound, zBound, childCost, pRelative, Bstruct] using hbound p hp
  have herr : 3 * pRelative + 130 ≤ (p + 2) ^ precisionPower := by
    simpa only [t, X, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_ofNat, pRelative] using herror p hp
  obtain ⟨hz, hr, hm, hc, ht⟩ := early_input_components s hp ht0 hc0 hz0 hr0 hb
  exact ⟨hn.trans hz, hreg.trans hr,
    (add_le_add (le_refl _) hn).trans hm, hc, ht, herr⟩

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

namespace Erdos3.RankPreparationFamily

open Module Submodule VectorPolynomial
open scoped BigOperators

variable {X J : Type} {m q : ℕ} (L : RankPreparationFamily X J m)

theorem pad_rank_sum (hmq : m ≤ q) :
    (∑ j, (L.pad q j).rank) = ∑ j, (L j).rank :=
  L.pad_sum hmq RankPreparationLayer.rank RankPreparationLayer.empty_rank

end Erdos3.RankPreparationFamily

end

section

namespace Erdos3
open VectorPolynomial
open scoped BigOperators

theorem preparedRelative_padded_input
    {X J : Type} {m q D : ℕ} (L : RankPreparationFamily X J m)
    (hmq : m ≤ q) {p Bstruct Rreq : ℝ}
    (preparationPower requiredPower passagePower : ℕ)
    (hp : 0 ≤ p) (hB : 0 ≤ Bstruct)
    (hcap : (preparationCoordinateCap q D (q * D) : ℝ) ≤ Bstruct)
    (hheight : L.PreparedHeights ((p + 2) ^ preparationPower)
      (preparedRoundedRank p requiredPower))
    (hsize : L.Sized D (m * D)) (hrankSum : (∑ j, (L j).rank) ≤ m * D)
    (N : X → ℕ)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ))
      (preparedRoundedRank p requiredPower) (L j).space (L j).poly)
    (hRreq : Rreq ≤ (p + 2) ^ requiredPower)
    (hpower : requiredPower ≤ passagePower)
    (hN : ∀ i, Real.exp ((p + 2) ^ passagePower) ≤ (N i : ℝ)) :
    let pLate := preparedRelativeLateHeight Bstruct p preparationPower requiredPower
    let R := preparedRoundedRank p requiredPower
    0 ≤ pLate ∧
      (L.pad q).PreparedHeights pLate R ∧
      (L.pad q).Sized D (m * D) ∧
      (∀ j, (Fintype.card (L.pad q j).Coord : ℝ) ≤ pLate) ∧
      (∑ j, (L.pad q j).rank) ≤ m * D ∧
      1 ≤ R ∧ (R : ℝ) ≤ Real.exp pLate ∧ Real.exp Rreq ≤ (R : ℝ) ∧
      (∀ i, Real.exp Rreq ≤ (N i : ℝ)) ∧
      (∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ))
        (R : ℝ) (L.pad q j).space (L.pad q j).poly) ∧
      (∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (L.pad q j).poly) ∧
      (∀ j ex, coefficients (L.pad q j).poly ex ∈ (L.pad q j).space) := by
  intro pLate R
  have hbase : 0 ≤ p + 2 := by linarith only [hp]
  have hprep0 : 0 ≤ (p + 2) ^ preparationPower := pow_nonneg hbase _
  have hreq0 : 0 ≤ (p + 2) ^ requiredPower := pow_nonneg hbase _
  have hBlate : Bstruct ≤ pLate := le_max_left _ _
  have hpreplate : (p + 2) ^ preparationPower ≤ pLate :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hreqlate : (p + 2) ^ requiredPower + 1 ≤ pLate :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hpad := hheight.pad hmq hprep0
  have hlate := hpad.mono_parameter (L.pad q) hprep0 hpreplate
  have hsized := hsize.pad hmq
  have hcoordinate := preparationCoordinateCap_bounds hsized
    (Nat.mul_le_mul_right D hmq)
  have hRupper : (R : ℝ) ≤ Real.exp pLate :=
    (ceil_exp_le_exp_add_one hreq0).trans (Real.exp_le_exp.mpr hreqlate)
  refine ⟨hB.trans hBlate, hlate, hsized,
    fun j => (Nat.cast_le.mpr (hcoordinate j).1).trans (hcap.trans hBlate),
    ?_, preparedRoundedRank_one_le p requiredPower, hRupper,
    preparedRoundedRank_exp_requirement hRreq, ?_, L.pad_samplingRank _ _ hrank,
    fun j => (hlate j).1, fun j => (hlate j).2.1⟩
  · rwa [L.pad_rank_sum hmq]
  · intro i
    exact (Real.exp_le_exp.mpr (hRreq.trans
      (pow_le_pow_right₀ (by linarith only [hp]) hpower))).trans (hN i)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

 theorem preparedFiniteNestedSourceProjectionPrecision_endpoint_le
    (m cutoff A Cdirect outerDepth innerDepth : ℕ)
    (constants : ℕ → ℕ) (G : Type) [Fintype G] (count nX : ℕ)
    {Bstruct gainLog stageLog : ℝ} (pnum Qstride Plate endpoint : ℝ)
    (hA : 2 ≤ A) (hB : 0 ≤ Bstruct)
    (hg : gainLog ∈ Set.Icc 0 Bstruct) (hs : stageLog ∈ Set.Icc 0 Bstruct) :
    endpoint ≤ preparedFiniteNestedSourceProjectionPrecision
      (outerDepth := outerDepth) (innerDepth := innerDepth) (cutoff := cutoff)
      m G count nX A Cdirect constants Bstruct pnum Qstride gainLog stageLog Plate endpoint := by
  exact preparedNestedFrontProjectionEnvelope_endpoint_le A constants innerDepth
    _ _ _ endpoint hA hB hg hs

 theorem preparedFiniteNestedSourceRequiredLog_endpoint_le
    (m cutoff A Cdirect outerDepth innerDepth : ℕ)
    (constants : ℕ → ℕ) (G : Type) [Fintype G] (M count nX : ℕ)
    {Bstruct gainLog stageLog : ℝ} (pnum Qstride Vlog Qσ Pmin requestedCoarse endpoint : ℝ)
    (hA : 2 ≤ A) (hB : 0 ≤ Bstruct)
    (hg : gainLog ∈ Set.Icc 0 Bstruct) (hs : stageLog ∈ Set.Icc 0 Bstruct) :
    endpoint ≤ preparedFiniteNestedSourceRequiredLog m cutoff A Cdirect outerDepth innerDepth
      constants G M count nX Bstruct pnum Qstride gainLog stageLog Vlog Qσ Pmin requestedCoarse endpoint := by
  unfold preparedFiniteNestedSourceRequiredLog
  apply preparedFiniteNestedSourceRequired_endpoint_le m A constants innerDepth outerDepth cutoff Bstruct
  exact preparedFiniteNestedSourceProjectionPrecision_endpoint_le m cutoff A Cdirect
    outerDepth innerDepth constants G count nX pnum Qstride _ endpoint hA hB hg hs

theorem preparedCanonicalRelativeSourceRequired_endpoint_le
    {nX D m : ℕ} (prep : RankPreparationFamily (Fin nX) (Fin D) m)
    (s outerDepth innerDepth e Cprimitive Cdirect extra : ℕ)
    {Bstruct p : ℝ} (knob : ℝ) (hB : 0 ≤ Bstruct) (hp : p ∈ Set.Icc 0 Bstruct) :
    knob ≤ preparedCanonicalRelativeSourceRequired prep s outerDepth innerDepth
      e Cprimitive Cdirect extra Bstruct p knob := by
  unfold preparedCanonicalRelativeSourceRequired
  apply preparedFiniteNestedSourceRequiredLog_endpoint_le
  · exact (preparedFiniteNestedSourceExponent_bounds (max m s) s e Cprimitive Cdirect extra
      (preparedFiniteNestedSourceExponent (max m s) s e Cprimitive Cdirect extra) le_rfl).1
  · exact hB
  · exact hp
  · exact ⟨le_rfl, hB⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedRelativeEndpointNumericalBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem preparedRelativeEndpointUniformKnob_bounds (m : ℕ)
    {t seed childCost cost Ptest Ecompare D primitiveCap modelRequired nativeAmbient : ℝ}
    (ht : 0 ≤ t)
    (hseed : seed ≤ preparedRelativeEndpointGeometryScale m t)
    (hchild : childCost ≤ preparedRelativeEndpointGeometryScale m t)
    (hcost : cost ∈ Set.Icc 0 (preparedRelativeEndpointGeometryScale m t))
    (hTest : Ptest ∈ Set.Icc 0 (preparedRelativeEndpointGeometryScale m t))
    (hCompare : Ecompare ∈ Set.Icc 0 (preparedRelativeEndpointGeometryScale m t))
    (hD : D ∈ Set.Icc 0 (preparedRelativeEndpointGeometryScale m t))
    (hcap : primitiveCap ∈ Set.Icc 0 (preparedRelativeEndpointGeometryScale m t))
    (hModel : modelRequired ∈ Set.Icc 0 (preparedRelativeEndpointGeometryScale m t))
    (hAmbient : nativeAmbient ∈ Set.Icc 0 (preparedRelativeEndpointGeometryScale m t)) :
    let T := preparedRelativeEndpointGeometryScale m t
    let floorLog := (T + 10) ^ (2 * m + 20)
    let K := preparedRelativeEndpointUniformKnob m t
    1 ≤ K ∧ T ≤ K ∧
      preparedRelativeEndpointMinimumLog seed 0 childCost cost floorLog ≤ K ∧
      preparedRelativeEndpointGoodLog Ptest ≤ K ∧
      preparedRelativeEndpointSigmaLog D primitiveCap Ptest Ecompare cost m ≤ K ∧
      preparedRelativeEndpointCoarseLog D primitiveCap Ptest Ecompare ≤ K ∧
      preparedRelativeEndpointAmbientLog modelRequired nativeAmbient floorLog ≤ K := by
  intro T floorLog K
  have hT := (preparedRelativeEndpointGeometryScale_bounds m ht).1
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  let V := (T + preparedRelativeEndpointPerturbationExponent m) ^
    preparedRelativeEndpointPerturbationExponent m
  have hV0 : 0 ≤ V := by dsimp only [V]; positivity
  have hF0 : 0 ≤ floorLog := by dsimp only [floorLog]; positivity
  have hK : K = 4 * T + V + floorLog + 20 := rfl
  obtain ⟨hSigma, hCoarse⟩ :=
    (exists_preparedRelativeEndpointPerturbationLog_budget m).choose_spec.2
      hT0 hD hcap hTest hCompare hcost
  change preparedRelativeEndpointSigmaLog D primitiveCap Ptest Ecompare cost m ∈ Set.Icc 0 V at hSigma
  change preparedRelativeEndpointCoarseLog D primitiveCap Ptest Ecompare ∈ Set.Icc 0 V at hCoarse
  have hcommon : preparedSlicedForecastCommonFloorExponent 0 childCost cost floorLog ≤
      T + floorLog + 1 := by
    unfold preparedSlicedForecastCommonFloorExponent
    refine max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ ?_)))
    · linarith only [hT0, hF0]
    · linarith only [hT0, hF0]
    · linarith only [hchild, hF0]
    · linarith only [hcost.2, hF0]
    · linarith only [hT0]
  have hMinimum : preparedRelativeEndpointMinimumLog seed 0 childCost cost floorLog ≤
      T + floorLog + 2 := by
    unfold preparedRelativeEndpointMinimumLog
    exact max_le (by linarith only [hseed, hF0]) (by linarith only [hcommon])
  have hGood : preparedRelativeEndpointGoodLog Ptest ≤ 2 * T + 1 := by
    unfold preparedRelativeEndpointGoodLog
    linarith only [hTest.2]
  have hEnd : preparedRelativeEndpointAmbientLog modelRequired nativeAmbient floorLog ≤
      T + floorLog := by
    unfold preparedRelativeEndpointAmbientLog
    exact max_le (by linarith only [hModel.2, hF0])
      (max_le (by linarith only [hAmbient.2, hF0]) (by linarith only [hT0]))
  exact ⟨by linarith only [hK, hT, hV0, hF0],
    by linarith only [hK, hT0, hV0, hF0],
    by linarith only [hMinimum, hK, hT0, hV0],
    by linarith only [hGood, hK, hT0, hV0, hF0],
    by linarith only [hSigma.2, hK, hT0, hF0],
    by linarith only [hCoarse.2, hK, hT0, hF0],
    by linarith only [hEnd, hK, hT0, hV0]⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem preparedRelativeEndpointInputScale_setup_bounds (m earlyPower M nX Jalloc : ℕ)
    {B Pdim cost pRadius gainLog Qstride Pchart PF childCost : ℝ} (hB : 0 ≤ B)
    (hDbase : allocatedComparisonDimension m
      (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ≤ preparedRelativeEndpointInputBase earlyPower B)
    (hDmod : ((nX + m * M : ℕ) : ℝ) ≤ preparedRelativeEndpointInputBase earlyPower B)
    (hPdim : Pdim ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B))
    (hcost : cost ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B))
    (hRadius : pRadius ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B))
    (hGain : gainLog ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B))
    (hStride : Qstride ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B))
    (hChart : Pchart ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B))
    (hPF : PF ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B))
    (hChild : childCost ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B)) :
    let t := preparedRelativeEndpointInputScale m earlyPower B
    preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost ∈ Set.Icc 0 t ∧
    preparedSlicedForecastBadLog m nX Qstride gainLog ∈ Set.Icc 0 t ∧
    cost + 1 ∈ Set.Icc 0 t ∧ gainLog + nX + 8 ∈ Set.Icc 0 t ∧
    pRadius ∈ Set.Icc 0 t ∧
    allocatedComparisonDimension m
      (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ∈ Set.Icc 0 t ∧
    preparedSlicedForecastPrimitiveCap ∈ Set.Icc 0 t ∧
    (m : ℝ) ≤ t ∧ ((nX + m * M : ℕ) : ℝ) ≤ t ∧ (nX : ℝ) ≤ t ∧
    allocatedComparisonDimension m
      (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) + pRadius + 1 ∈ Set.Icc 0 t ∧
    preparedSlicedForecastJacobianLog m M nX pRadius gainLog Pchart ∈ Set.Icc 0 t ∧
    PF ∈ Set.Icc 0 t ∧ childCost + 1 ∈ Set.Icc 0 t := by
  intro t
  have ha := (preparedRelativeEndpointInputBase_bounds earlyPower hB).1
  obtain ⟨hP, hBad, hPres, hτ, hK, hD, hCap, hm, hDim, hnX, hscale, hJac, hF, hchild⟩ :=
    (exists_preparedSlicedForecastScalarEnvelope m).choose_spec.2 M nX Jalloc
      (zero_le_one.trans ha) hDbase hDmod hPdim hcost hRadius hGain hStride hChart hPF hChild
  have hW := (preparedRelativeEndpointInputScale_bounds m earlyPower hB).2.2
  have lift {a : ℝ}
      (h : a ∈ Set.Icc 0 ((preparedRelativeEndpointInputBase earlyPower B +
        preparedRelativeEndpointPrimitiveExponent m) ^ preparedRelativeEndpointPrimitiveExponent m)) :
      a ∈ Set.Icc 0 t := ⟨h.1, h.2.trans hW⟩
  exact ⟨lift hP, lift hBad, lift hPres, lift hτ, lift hK, lift hD, lift hCap,
    hm.trans hW, hDim.trans hW, hnX.trans hW, lift hscale, lift hJac, lift hF, lift hchild⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

 theorem preparedRelativeEndpoint_numerical_bounds
    (m earlyPower M nX Jalloc : ℕ)
    {B Pdim cost pRadius gainLog Qstride Pchart PF childCost u p budget seed : ℝ}
    (hB : 0 ≤ B)
    (hDbase : allocatedComparisonDimension m
      (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ≤ preparedRelativeEndpointInputBase earlyPower B)
    (hDmod : ((nX + m * M : ℕ) : ℝ) ≤ preparedRelativeEndpointInputBase earlyPower B)
    (hPdim : Pdim ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B))
    (hcost : cost ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B))
    (hRadius : pRadius ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B))
    (hGain : gainLog ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B))
    (hStride : Qstride ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B))
    (hChart : Pchart ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B))
    (hPF : PF ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B))
    (hChild : childCost ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B))
    (hu : u ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B))
    (hp : p ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B))
    (hbudget : budget ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B))
    (hseed : seed ≤ preparedRelativeEndpointInputBase earlyPower B) :
    let t := preparedRelativeEndpointInputScale m earlyPower B
    let T := preparedRelativeEndpointGeometryScale m t
    let K := preparedRelativeEndpointUniformKnob m t
    let Eearly := 2 * u + 4 * p + 12
    let nativeEarly := preparedConcreteSlicedForecastNativeLog m M nX Jalloc
      Pdim cost pRadius gainLog Qstride PF Pchart childCost Eearly
    let massEarly := preparedConcreteSlicedForecastMassLog m M nX Jalloc
      Pdim cost pRadius gainLog Qstride Pchart childCost Eearly
    let Ptest := preparedRelativeEndpointTestLog budget nativeEarly
    let Ecompare := preparedRelativeEndpointComparisonLog budget nativeEarly massEarly u p cost
    let nativeLate := preparedConcreteSlicedForecastNativeLog m M nX Jalloc
      Pdim cost pRadius gainLog Qstride PF Pchart childCost (Ecompare + 8)
    let massLate := preparedConcreteSlicedForecastMassLog m M nX Jalloc
      Pdim cost pRadius gainLog Qstride Pchart childCost (Ecompare + 8)
    let Pspatial := preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost
    let nativeAmbient := (max (max Pspatial (2 * max Ptest (3 * nativeLate + 3) + 1))
      (massLate + Ecompare + 8) + nativeForecastAmbientExponent m) ^ nativeForecastAmbientExponent m
    let modelRequired := actualForecastDataModelRequired budget nativeEarly massEarly u p
    let floorLog := (T + 10) ^ (2 * m + 20)
    1 ≤ T ∧ t ≤ T ∧ T ≤ K ∧ 1 ≤ K ∧
    Ptest ∈ Set.Icc 0 T ∧ Ecompare ∈ Set.Icc 0 T ∧
    nativeEarly ∈ Set.Icc 0 T ∧ massEarly ∈ Set.Icc 0 T ∧
    nativeLate ∈ Set.Icc 0 T ∧ massLate ∈ Set.Icc 0 T ∧
    modelRequired ∈ Set.Icc 0 T ∧ nativeAmbient ∈ Set.Icc 0 T ∧
    preparedRelativeEndpointMinimumLog seed 0 childCost cost floorLog ≤ K ∧
    preparedRelativeEndpointGoodLog Ptest ≤ K ∧
    preparedRelativeEndpointSigmaLog
      (allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ))
      preparedSlicedForecastPrimitiveCap Ptest Ecompare cost m ≤ K ∧
    preparedRelativeEndpointCoarseLog
      (allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ))
      preparedSlicedForecastPrimitiveCap Ptest Ecompare ≤ K ∧
    preparedRelativeEndpointAmbientLog modelRequired nativeAmbient floorLog ≤ K ∧ floorLog ≤ K := by
  intro t T K Eearly nativeEarly massEarly Ptest Ecompare nativeLate massLate Pspatial nativeAmbient modelRequired floorLog
  have hInput := preparedRelativeEndpointInputScale_bounds m earlyPower hB
  have ht : 0 ≤ t := zero_le_one.trans hInput.1
  have hGeo := preparedRelativeEndpointGeometryScale_bounds m ht
  have hbase : preparedRelativeEndpointInputBase earlyPower B ≤ t := hInput.2.1
  have lift {a : ℝ} (ha : a ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B)) :
      a ∈ Set.Icc 0 t := ⟨ha.1, ha.2.trans hbase⟩
  have liftT {a : ℝ} (ha : a ∈ Set.Icc 0 t) : a ∈ Set.Icc 0 T :=
    ⟨ha.1, ha.2.trans hGeo.2.1⟩
  obtain ⟨hSpatial, _, _, _, _, hD, hCap, _, _, _, _, _, _, _⟩ :=
    preparedRelativeEndpointInputScale_setup_bounds m earlyPower M nX Jalloc hB hDbase hDmod
      hPdim hcost hRadius hGain hStride hChart hPF hChild
  obtain ⟨hTest, hCompare, hnEarly, hmEarly, hnLate, hmLate, hModel, hAmbient⟩ :=
    (exists_preparedRelativeEndpointForecast_budget m).choose_spec.2 M nX Jalloc ht
      (hDbase.trans hbase) (hDmod.trans hbase) (lift hPdim) (lift hcost) (lift hRadius)
      (lift hGain) (lift hStride) (lift hPF) (lift hChart) (lift hChild) (lift hu)
      (lift hp) (lift hbudget) hSpatial
  have up {a : ℝ} (ha : a ∈ Set.Icc 0 ((t + preparedRelativeEndpointForecastExponent m) ^
      preparedRelativeEndpointForecastExponent m)) : a ∈ Set.Icc 0 T :=
    ⟨ha.1, ha.2.trans hGeo.2.2⟩
  have hTest' : Ptest ∈ Set.Icc 0 T := up hTest
  have hCompare' : Ecompare ∈ Set.Icc 0 T := up hCompare
  have hnEarly' : nativeEarly ∈ Set.Icc 0 T := up hnEarly
  have hmEarly' : massEarly ∈ Set.Icc 0 T := up hmEarly
  have hnLate' : nativeLate ∈ Set.Icc 0 T := up hnLate
  have hmLate' : massLate ∈ Set.Icc 0 T := up hmLate
  have hModel' : modelRequired ∈ Set.Icc 0 T := up hModel
  have hAmbient' : nativeAmbient ∈ Set.Icc 0 T := up hAmbient
  obtain ⟨hK, hTK, hMin, hGood, hSigma, hCoarse, hEnd⟩ :=
    preparedRelativeEndpointUniformKnob_bounds m ht
      (hseed.trans (hbase.trans hGeo.2.1))
      ((lift hChild).2.trans hGeo.2.1) (liftT (lift hcost)) hTest' hCompare'
      (liftT hD) (liftT hCap) hModel' hAmbient'
  have hFloor : floorLog ≤ K :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hEnd
  exact ⟨hGeo.1, hGeo.2.1, hTK, hK, hTest', hCompare', hnEarly', hmEarly', hnLate', hmLate',
    hModel', hAmbient', hMin, hGood, hSigma, hCoarse, hEnd, hFloor⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedConcreteSlicedForecastPrimitiveCapBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem preparedConcreteSlicedForecastPrimitiveCapLog_le_work (m Ccontrol Cchild Cprimitive A : ℕ)
    (stageCountConstant : ℕ → ℕ) (stage M nX Jalloc : ℕ)
    {x Pdim pRadius gainLog Qstride Pchart childLog : ℝ}
    (hA : 2 ≤ A) (hC : preparedConcreteSlicedForecastPrimitiveCapExponent m Ccontrol Cchild Cprimitive ≤ A)
    (hx : 0 ≤ x) :
    let b := preparedFiniteForwardParameter A stageCountConstant stage x
    allocatedComparisonDimension m
      (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ≤ b →
    ((nX + m * M : ℕ) : ℝ) ≤ b →
    Pdim ∈ Set.Icc 0 ((b + Cprimitive) ^ Cprimitive) →
      pRadius ∈ Set.Icc 0 ((b + Cprimitive) ^ Cprimitive) →
      gainLog ∈ Set.Icc 0 ((b + Cprimitive) ^ Cprimitive) →
    Qstride ∈ Set.Icc 0 ((b + Cprimitive) ^ Cprimitive) →
      Pchart ∈ Set.Icc 0 ((b + Cprimitive) ^ Cprimitive) →
    childLog ∈ Set.Icc 0 ((b + Cchild) ^ Cchild) →
    preparedConcreteSlicedForecastCapLog m M nX Jalloc
      Pdim ((b + Ccontrol) ^ Ccontrol) pRadius gainLog Qstride Pchart childLog ≤
        preparedFiniteForwardWork A stageCountConstant stage x := by
  intro b hDbase hDmod hPdim hRadius hGain hStride hChart hChild
  have hb : 0 ≤ b := preparedFiniteForwardParameter_nonneg A stageCountConstant stage hx
  have hcap := (Classical.choose_spec
    (exists_preparedConcreteSlicedForecastPrimitiveCapLog_budget m Ccontrol Cchild Cprimitive)).2
      M nX Jalloc hb hDbase hDmod hPdim hRadius hGain hStride hChart hChild
  apply hcap.2.trans
  have hshift := preparedFiniteForward_shiftedPower_le_work A
    (preparedConcreteSlicedForecastPrimitiveCapExponent m Ccontrol Cchild Cprimitive) stageCountConstant 0 hA hC hb
  simpa only [preparedFiniteForwardWork_eq, preparedFiniteForwardParameter_zero,
    b, preparedConcreteSlicedForecastPrimitiveCapExponent] using hshift

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedRelativePositiveNativeRuleCanonical
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators NNReal

theorem preparedRelativeEndpointCapExponent_two_le (s : ℕ) :
    2 ≤ preparedRelativeEndpointCapExponent s := by
  unfold preparedRelativeEndpointCapExponent
  omega

theorem preparedRelativeEndpointCapExponent_primitive_le {s m : ℕ} (hm : m ≤ s) :
    preparedConcreteSlicedForecastPrimitiveCapExponent
      m 1 1 (preparedCommonRadiusPrimitiveExponent s) ≤
        preparedRelativeEndpointCapExponent s := by
  classical
  let j : Fin (s + 1) := ⟨m, by omega⟩
  have hsum : preparedConcreteSlicedForecastPrimitiveCapExponent
      m 1 1 (preparedCommonRadiusPrimitiveExponent s) ≤
      ∑ i : Fin (s + 1), preparedConcreteSlicedForecastPrimitiveCapExponent
        i.val 1 1 (preparedCommonRadiusPrimitiveExponent s) :=
    by
      have h := Finset.single_le_sum
        (f := fun i : Fin (s + 1) => preparedConcreteSlicedForecastPrimitiveCapExponent
          i.val 1 1 (preparedCommonRadiusPrimitiveExponent s))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      exact h
  unfold preparedRelativeEndpointCapExponent
  omega

theorem preparedRelativeEndpointCapExponent_density_le (s : ℕ) :
    preparedCommonRadiusDensityCapNestedExponent s ≤
      preparedRelativeEndpointCapExponent s := by
  unfold preparedRelativeEndpointCapExponent
  omega

theorem preparedRelativeEndpointForecastCap_le_work
    (s m A : ℕ) (hm : m ≤ s)
    (hA : preparedRelativeEndpointCapExponent s ≤ A)
    (constants : ℕ → ℕ) (innerDepth outer inner M nX Jalloc : ℕ)
    {p gainLog Pchart childLog : ℝ} (hp : 0 ≤ p)
    (hgain : gainLog ∈ Set.Icc 0 p) (hchart : Pchart ∈ Set.Icc 0 p)
    (hchild : childLog ∈ Set.Icc 0 p) :
    let x := candidateNestedForwardSeed A constants innerDepth outer p
    let b := preparedFiniteForwardParameter A constants inner x
    allocatedComparisonDimension m
      (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ≤ b →
    ((nX + m * M : ℕ) : ℝ) ≤ b →
    preparedConcreteSlicedForecastCapLog m M nX Jalloc
      p (b + 1) (allocatedCommonProductRadiusLog m p p) gainLog 0 Pchart childLog ≤
      preparedFiniteForwardWork A constants inner x := by
  intro x b hDbase hDmod
  have hAtwo := (preparedRelativeEndpointCapExponent_two_le s).trans hA
  have hx : 0 ≤ x := candidateNestedForwardSeed_nonneg A constants innerDepth outer hp
  have hpb : p ≤ b :=
    (le_candidateNestedForwardSeed A constants innerDepth outer hAtwo hp).trans
      (le_preparedFiniteForwardParameter A constants inner hx)
  have hb : 0 ≤ b := hp.trans hpb
  let C := preparedCommonRadiusPrimitiveExponent s
  have hC : 2 ≤ C := preparedCommonRadiusPrimitiveExponent_two_le s
  have hCreal : (2 : ℝ) ≤ C := by exact_mod_cast hC
  have hbase : 1 ≤ b + C := by linarith only [hb, hCreal]
  have hpower : b + C ≤ (b + C) ^ C := by
    simpa only [pow_one] using pow_le_pow_right₀ hbase (show 1 ≤ C by omega)
  have hpbound : p ≤ (b + C) ^ C := (by linarith only [hpb, hCreal] : p ≤ b + C).trans hpower
  have lift {a : ℝ} (ha : a ∈ Set.Icc 0 p) : a ∈ Set.Icc 0 ((b + C) ^ C) :=
    ⟨ha.1, ha.2.trans hpbound⟩
  have hrad := preparedCommonRadiusPrimitive_bound s m hm hp
  have hrad' : allocatedCommonProductRadiusLog m p p ∈ Set.Icc 0 ((b + C) ^ C) :=
    ⟨hrad.1, hrad.2.trans (pow_le_pow_left₀ (by positivity)
      (add_le_add hpb le_rfl) C)⟩
  have hchild' : childLog ∈ Set.Icc 0 ((b + (1 : ℕ)) ^ (1 : ℕ)) := by
    simp only [Nat.cast_one, pow_one]
    exact ⟨hchild.1, by linarith only [hchild.2, hpb]⟩
  have hcap := preparedConcreteSlicedForecastPrimitiveCapLog_le_work m 1 1 C A
    constants inner M nX Jalloc hAtwo
    ((preparedRelativeEndpointCapExponent_primitive_le hm).trans hA) hx
    hDbase hDmod (lift ⟨hp, le_rfl⟩) hrad' (lift hgain)
    (lift ⟨le_rfl, hp⟩) (lift hchart) hchild'
  simpa only [Nat.cast_one, pow_one] using hcap

theorem preparedRelativeEndpointMarginalCap_le_exp_work
    (s A : ℕ) (hA : preparedRelativeEndpointCapExponent s ≤ A)
    {X J : Type} {m : ℕ} (prep : RankPreparationFamily X J m)
    (hm : m ≤ s) (M Jalloc : ℕ)
    (hM : ∀ j, Fintype.card (prep j).Coord ≤ M)
    {p : ℝ} (hp : 0 ≤ p)
    (hnum : (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ≤ p)
    (V : Fin m → ℝ≥0) (hV : ∀ j, (V j : ℝ) ≤ Real.exp p)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp p)
    (constants : ℕ → ℕ) (innerDepth outer inner : ℕ) :
    max 1 (4 * ∏ j, earlyConstantDensityCap
      (Fintype.card (PreparedSamplerContinuous prep j))
      (preparedSamplerTransverse prep j) (allocatedCommonProductRadius m p p) (V j)) ≤
      Real.exp (preparedFiniteForwardWork A constants inner
        (candidateNestedForwardSeed A constants innerDepth outer p)) := by
  apply max_le
  · exact Real.one_le_exp (preparedFiniteForwardWork_nonneg A constants inner
      (candidateNestedForwardSeed_nonneg A constants innerDepth outer hp))
  · exact prepared_commonRadius_densityCap_nested_bound s A
      ((preparedRelativeEndpointCapExponent_density_le s).trans hA)
      prep hm M Jalloc hM p hp hnum V hV hprofile constants innerDepth outer inner

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem preparedRelativePositiveSourceExponent_bounds (s : ℕ) :
    2 ≤ preparedRelativePositiveSourceExponent s ∧
    preparedRelativeNativeSourceExponent s ≤ preparedRelativePositiveSourceExponent s ∧
    preparedRelativeEndpointCapExponent s ≤ preparedRelativePositiveSourceExponent s ∧
    preparedNestedEndpointDimensionExponent s ≤ preparedRelativePositiveSourceExponent s ∧
    preparedFiniteNestedSourceSliceExponent s s (preparedCommonRadiusPrimitiveExponent s) + 1 ≤
      preparedRelativePositiveSourceExponent s := by
  obtain ⟨hA, hExtra, _, _, hSlice, _⟩ :=
    preparedFiniteNestedSourceExponent_bounds s s (candidateNestedDegreeNetBound s 0)
      (preparedCommonRadiusPrimitiveExponent s) 2 (preparedRelativePositiveExtra s)
      (preparedRelativePositiveSourceExponent s) le_rfl
  unfold preparedRelativePositiveExtra at hExtra
  exact ⟨hA, by omega, by omega, by omega, hSlice⟩

theorem preparedRelativePositiveInputExponent_spec (s : ℕ) :
    2 ≤ preparedRelativePositiveInputExponent s ∧ ∀ {B : ℝ}, 0 ≤ B →
      preparedRelativeEndpointUniformKnob s
        (preparedRelativeEndpointInputScale s (preparedRelativePositiveEarlyExponent s) B) ≤
          (B + 2) ^ preparedRelativePositiveInputExponent s :=
  (exists_preparedRelativeEndpointInputScale_power_budget s
    (preparedRelativePositiveEarlyExponent s)).choose_spec

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open AllocatedExternalCandidateSampler
open scoped BigOperators Classical TensorProduct NNReal
attribute [local irreducible] AllocatedExternalCandidateSampler.DegreeGlobalizationAt

variable {m : ℕ} {G X : Type} [Fintype G] [Nonempty G] [Fintype X]
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
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

theorem degreeGlobalizationAt_of_preparedRelativePositiveSource_canonical
    (s : ℕ) (hms : m = s)
    (sourceExponent : ℕ)
    (hExponent : sourceExponent = preparedRelativePositiveSourceExponent s)
    (weight : (X → ℤ) → ℂ)
    (x pnum Qstride gainLog stageLog Plate : ℝ)
    (hx : 0 ≤ x) (hnum : pnum ∈ Set.Icc 0 x) (hstride : Qstride ∈ Set.Icc 0 x)
    (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x)
    (hlayers : (m : ℝ) ≤ x)
    (hvariables : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ x)
    (hX : (Fintype.card X : ℝ) ≤ x) (hG : (Fintype.card G : ℝ) ≤ x)
    (hprofiles :
      ∀ (outerFront outerInner : Fin (2 * s + 2 + 1)) (d : ℕ),
      ∀ (hd : d ≤ s), d ≤ s + 1 → ∀ pInput : ℝ,
      pInput ∈ Set.Icc 0
        (candidateNestedForwardSeed sourceExponent
          degreeSourceCountConstants (s + 1) outerFront.val x) →
      pInput ≤ candidateNestedForwardSeed sourceExponent
        degreeSourceCountConstants (s + 1) outerInner.val x →
      ∃ profile : A.DegreeSourceProfile d pInput (candidateNestedDegreeNetBound s 0),
        profile.inner.x = candidateNestedForwardSeed sourceExponent
          degreeSourceCountConstants (s + 1) outerInner.val x ∧
        profile.inner.gainLog = candidateNestedForwardSeed sourceExponent
          degreeSourceCountConstants (s + 1) outerInner.val x ∧
        profile.front.u = preparedFiniteForwardModelPrecision sourceExponent
          degreeSourceCountConstants 0
          (candidateNestedForwardSeed sourceExponent
            degreeSourceCountConstants (s + 1) outerFront.val x) gainLog stageLog ∧
        profile.front.pModel = preparedFiniteForwardWork sourceExponent
          degreeSourceCountConstants 0
          (candidateNestedForwardSeed sourceExponent
            degreeSourceCountConstants (s + 1) outerFront.val x) ∧
        profile.front.nativeBudget = preparedFiniteNestedSourceNative m G
          (Fintype.card (LayerSamplerVariables G I n B)) (Fintype.card X)
          (preparedFiniteForwardDetectorPolynomial s) sourceExponent 2
          degreeSourceCountConstants x pnum Qstride gainLog stageLog Plate
          (outerFront, (0 : Fin (s + 1 + 1)), ⟨d, Nat.lt_succ_of_le hd⟩, false) ∧
        profile.inner.Cprimitive = preparedCommonRadiusPrimitiveExponent s ∧
        profile.inner.scheduleExponent = sourceExponent ∧
        profile.inner.Csource = preparedFiniteNestedSourceNativeExponent m s 2)
    (hscale : Real.exp (candidateNestedForwardSeed sourceExponent
        degreeSourceCountConstants (s + 1) (2 * s + 2) x) ≤ (S.value : ℝ)) :
    A.DegreeGlobalizationAt (E := E) weight s 0 x
      (preparedFiniteForwardParameter sourceExponent
        degreeSourceCountConstants (s + 1)
        (candidateNestedForwardSeed sourceExponent
          degreeSourceCountConstants (s + 1) (2 * s + 2) x) + 1) := by
  classical
  have hthreshold : (exists_degreeGlobalizationAt_of_complete_nested_source_data s m
      (preparedCommonRadiusPrimitiveExponent s) (preparedFiniteForwardDetectorPolynomial s)).choose ≤
      sourceExponent := by
    rw [hExponent]
    simpa only [hms, preparedRelativeNativeSourceExponent] using
      (preparedRelativePositiveSourceExponent_bounds s).2.1
  have rawRule := (exists_degreeGlobalizationAt_of_complete_nested_source_data s m
    (preparedCommonRadiusPrimitiveExponent s) (preparedFiniteForwardDetectorPolynomial s)).choose_spec.2
    (E := E) A weight 0 sourceExponent
    (2 * s + 2) (s + 1) s 2 (preparedFiniteNestedSourceNativeExponent m s 2)
    x pnum Qstride gainLog stageLog Plate hthreshold
    (by omega) (by omega) le_rfl (by omega) hx hnum hstride hg hs
    hlayers hvariables hX hG hprofiles hscale
  exact rawRule

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankPreparationPaddedFreezingLifts
namespace OAI

section

namespace Erdos3.RankPreparationFamily

open VectorPolynomial
open scoped BigOperators TensorProduct

variable {X J : Type} {m q : ℕ} (L : RankPreparationFamily X J m)

@[simp] theorem pad_polynomial [DecidableEq J] (hmq : m ≤ q) :
    (L.pad q).polynomial = L.polynomial := by
  apply L.pad_sum hmq (fun layer => map (coordinateCopySum layer.label) layer.poly)
  change map (coordinateCopySum (R := ℝ) (PEmpty.elim : PEmpty → J))
    (0 : VectorPolynomial X ℝ (PEmpty → ℝ)) = 0
  exact map_zero _

end Erdos3.RankPreparationFamily

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedRelativePositivePassage
namespace OAI

section

namespace Erdos3.RankPreparationFamily

open Module Submodule VectorPolynomial

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)

theorem PreparedHeights.euclideanJetLayers_compact
    {p : ℝ} {R : ℕ} (hL : L.PreparedHeights p R)
    (hp : 0 ≤ p) (hR : 1 ≤ R) (O : Fin m → Type*) :
    CompactSpace (EuclideanJetLayers (fun j => (L j).space) O) := by
  let : ∀ j, CompactSpace (euclideanSubspace (L j).space ⧸
      (latticeSection (standardEuclideanLattice (L j).Coord)
        (euclideanSubspace (L j).space)).toAddSubgroup) :=
    hL.euclideanLayerTorus_compact L hp hR
  dsimp only [EuclideanJetLayers]
  infer_instance

end Erdos3.RankPreparationFamily

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

theorem preparedFiniteNestedSourceNative_literal_eq
    (m cutoff A Cdirect outerDepth innerDepth : ℕ) (constants : ℕ → ℕ)
    (G : Type) [Fintype G] (count nX : ℕ)
    (Bstruct pnum Qstride gainLog stageLog Plate : ℝ)
    (k : PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff) :
  let K := PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff
  let degree : K → ℕ := preparedFiniteNestedForwardAllDegreeDegree
  let Pdetect := preparedFiniteForwardDetectorPolynomial cutoff
  let Cdetect := fun k : K => sampledSupportedSlicedDetectionConstant (degree k) Pdetect
  let sourceU := fun k : K => preparedFiniteForwardPairedSourcePrecision A Cdirect constants
    (preparedFiniteNestedForwardAllDegreeStage k).val (preparedFiniteNestedForwardAllDegreeIsDirect k)
    (preparedFiniteNestedForwardAllDegreeSeed A constants Bstruct k) gainLog stageLog
  let modelLog := fun k : K => preparedFiniteForwardWork A constants
    (preparedFiniteNestedForwardAllDegreeStage k).val
    (preparedFiniteNestedForwardAllDegreeSeed A constants Bstruct k)
  let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
  let D := allocatedComparisonDimension m pnum
  let pDetect := fun k => allocatedModelTestLog (sourceU k) (modelLog k)
  let aDetect := fun k => 2 * sourceU k + 4 * modelLog k + 7
  let detectionGain := fun k : K => slicedDetectionGainLog (degree k) (Cdetect k) count
    (pDetect k) (pDetect k) (aDetect k)
  let Pk := fun k : K => scalarKernelLogarithmicBudget (Fin (degree k + 1)) G
    (detectionGain k + pDetect k + 4)
  let Pphysical := fun k : K => preparedFiniteScheduleLocalPhysical m nX count Qstride (Pk k)
  let target := fun k => detectionGain k + 40 + coefficientErrorSpatialLog (Pphysical k)
  let Eprofile := fun k : K => target k + D * ((m * 2 ^ (m + 1) : ℕ) * Pk k) + 5
  let Prho := fun k : K => 2 * affineProfileInputEnvelope D
    (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (Eprofile k) (pDetect k + 2) + 2
  let Pmaster := fun k : K => preparedFiniteScheduleLocalMaster Bstruct D pRadius Qstride
    (Pphysical k) (sourceU k) (modelLog k) (Prho k) (target k) (detectionGain k)
  (preparedModularGeneralDetectorResources
    (preparedModularGeneralDetectorConstants m (degree k))
    (degree k + 1) (Pmaster k) Plate).nativeBudget =
    preparedFiniteNestedSourceNative m G count nX (preparedFiniteForwardDetectorPolynomial cutoff)
      A Cdirect constants Bstruct pnum Qstride gainLog stageLog Plate k := by
  rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3
open VectorPolynomial Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal TensorProduct
attribute [local irreducible] preparedFiniteNestedSourceRequiredLog
  AllocatedExternalCandidateSampler.NativeDetection integerBox
  AllocatedExternalCandidateSampler.DegreeGlobalizationAt
  RankPreparationFamily.PreparedHeights.canonicalPaddedSamplerData

theorem exists_preparedRelativePatchPowerPassage_s2_oai
    (s n₀ stage childExponent : ℕ) (discount : ℝ)
    (hs : 1 ≤ s) (_hchildExponent : 2 ≤ childExponent)
    (hdiscount : 0 < discount) (hdiscountOne : discount ≤ 1)
    (ih : RelativePatchPowerInductionRule s n₀ stage discount childExponent) :
    ∃ requiredPower precisionPower : ℕ,
      ∀ preparationPower : ℕ, 2 ≤ preparationPower →
        ∃ passagePower : ℕ, 2 ≤ passagePower ∧
          PreparedRelativePatchPowerPassage s n₀ stage discount
            requiredPower precisionPower preparationPower passagePower := by
  classical
  obtain ⟨relativePower, hRelativePower, hStructure⟩ :=
    exists_preparedRelative_structural_input_power s
  obtain ⟨candidateBasePower, precisionPower, hCandidateBasePower, hPrecisionPower, hCandidate⟩ :=
    exists_preparedRelative_candidate_input_powers s relativePower childExponent
      (exists_relative_finite_returned_fiber_normalization.{0,0} s).choose
      (allocatedNormalizedShearObservableExponent s)
  obtain ⟨baseMin, hBaseMin, hUniversalConstants⟩ :=
    exists_preparedScalarStructuralBasePower s
  let basePower := max candidateBasePower baseMin
  have hBasePower : 2 ≤ basePower := hCandidateBasePower.trans (le_max_left _ _)
  let inputPower := preparedRelativePositiveInputExponent s
  let earlyPower := preparedRelativePositiveEarlyExponent s
  let extra := preparedRelativePositiveExtra s
  let primitive := preparedCommonRadiusPrimitiveExponent s
  let entropy := candidateNestedDegreeNetBound s 0
  let constants := AllocatedExternalCandidateSampler.degreeSourceCountConstants
  let outerDepth := 2 * s + 2
  let innerDepth := s + 1
  obtain ⟨requiredPower, hRequiredPower, hRequired⟩ :=
    exists_preparedFiniteNestedCanonicalRequired_power_budget_of_inputPower_s2
      s outerDepth innerDepth s entropy primitive 2 extra basePower inputPower
      constants (by dsimp only [innerDepth]; omega) (by omega)
  refine ⟨requiredPower, precisionPower, ?_⟩
  intro preparationPower hPreparationPower
  obtain ⟨extractionPower, hExtractionPower, hExtraction⟩ :=
    exists_preparedRelativeFinalExtraction_power s s basePower inputPower
      preparationPower requiredPower discount
  let passagePower := max requiredPower extractionPower
  refine ⟨passagePower, hRequiredPower.trans (le_max_left _ _), ?_⟩
  intro p a Λ d₀ hp ha haΛ hΛ habsolute nX hnX hX N hN f hf hfree
    D E m hD hm hms oldPatch F hrest hcomplexity hStage hscore
    L hsize hheight hRankSum hCoord hrank ip c err hip herrDegree hprepare herr
  have hp0 : 0 ≤ p := by linarith only [hp]
  have hDreal : (D : ℝ) ≤ p := by
    have hd := (relativePatchComplexity_rank_le oldPatch).trans hcomplexity
    simp only [Nat.cast_add] at hd
    linarith only [hd, Nat.cast_nonneg (α := ℝ) E]
  have hq : max m s = s := max_eq_right hms
  let M := preparationCoordinateCap (max m s) D (s * D)
  let Jalloc := modularInitialBlockCount (max m s) (nX + max m s * M)
  let dim := enlargedPreparedCommonSamplerDimension (max m s) M Jalloc
  let G := EnlargedPreparedCommonKernel (max m s) Jalloc
  let pRelative := (p + 2) ^ relativePower
  let childCost := (pRelative + 4) ^ childExponent
  let Bstruct := (p + 2) ^ basePower
  let Vars := LayerSamplerVariables G (PreparedSamplerContinuous (L.pad (max m s)))
    (preparedSamplerTransverse (L.pad (max m s)))
    (EnlargedPreparedCommonSamplerBlock (L.pad (max m s)) Jalloc)
  let vars := Fintype.card Vars
  have hStructOriginal := hStructure hp D nX hDreal hX
  have hStruct : p ≤ pRelative ∧ (s : ℝ) + 3 ≤ pRelative ∧
    (M : ℝ) ≤ pRelative ∧ (Jalloc : ℝ) ≤ pRelative ∧
    (dim : ℝ) ≤ pRelative ∧ allocatedUniformChartLog (M : ℝ) + 1 ≤ pRelative := by
    simpa only [M, Jalloc, dim, hq] using hStructOriginal
  have hOriginalCoord : ∀ j, Fintype.card (L j).Coord ≤ M := by
    intro j
    simpa only [M, hq] using
      (hCoord j).trans (preparationCoordinateCap_mono hms (Nat.mul_le_mul_right D hms))
  have hvars : (vars : ℝ) ≤ pRelative :=
    (preparedFiniteNestedSource_counts L nX M s hOriginalCoord hStruct.2.2.2.2.1).2.2.1
  have hCandidateBase : (p + 2) ^ candidateBasePower ≤ Bstruct :=
    pow_le_pow_right₀ (by linarith only [hp]) (le_max_left _ _)
  obtain ⟨hNorm₀, hRegularity₀, hMass₀, hChartCost₀, hEarly₀, hPrecision⟩ :=
    hCandidate hp0 (Nat.cast_nonneg (α := ℝ) vars) hvars
  have hNorm := hNorm₀.trans hCandidateBase
  have hRegularity := hRegularity₀.trans hCandidateBase
  have hMass := hMass₀.trans hCandidateBase
  have hChartCost := hChartCost₀.trans hCandidateBase
  have hEarly := hEarly₀.trans hCandidateBase
  obtain ⟨_, hProfile, hCutoff, _⟩ :=
    hUniversalConstants basePower (le_max_right _ _) p hp
  have hInput := preparedRelativeInitializer_scalarInputs oldPatch L hp hms hCoord hStructOriginal
    hPrecision hcomplexity ha habsolute
  have hB : 0 ≤ Bstruct := by dsimp only [Bstruct]; positivity
  have hBtwo : 2 ≤ Bstruct := by
    change 6 * pRelative + 35 ≤ Bstruct at hEarly
    linarith only [hEarly, hStruct.1, hp]
  have hpB : p ≤ Bstruct := by
    linarith only [hEarly, hStruct.1, hp]
  have hM : (M : ℝ) ≤ Bstruct := by
    linarith only [hEarly, hStruct.2.2.1, hStruct.1, hp]
  have hnum : (dim : ℝ) ≤ Bstruct := by
    linarith only [hEarly, hStruct.2.2.2.2.1, hStruct.1, hp]
  have hVars : (vars : ℝ) ≤ Bstruct := hvars.trans (by
    linarith only [hEarly, hStruct.1, hp])
  have hPadCoord := preparedRelativeInitializer_padded_coordinate_card_le L hms hCoord
  let Aexp := preparedFiniteNestedSourceExponent (max m s) s entropy primitive 2 extra
  have hAeq : Aexp = preparedRelativePositiveSourceExponent s := by
    dsimp only [Aexp]
    rw [hq]
    rfl
  have hA := preparedRelativePositiveSourceExponent_bounds s
  rw [← hAeq] at hA
  let t := preparedRelativeEndpointInputScale s earlyPower Bstruct
  let T := preparedRelativeEndpointGeometryScale s t
  let K := preparedRelativeEndpointUniformKnob s t
  have hKPower : K ≤ (Bstruct + 2) ^ inputPower :=
    (preparedRelativePositiveInputExponent_spec s).2 hB
  have hFinal := preparedRelativeFinalEnvelope_bounds s basePower inputPower preparationPower
    requiredPower discount hp0 hKPower
  have hExtractionBound := hExtraction p hp0
  have hExtractionFinal := preparedRelativeFinalExtraction_side_floor N hp0
    (Nat.le_max_right requiredPower extractionPower) hExtractionBound hN

  obtain ⟨hG, _, hVariables, hLayers⟩ := preparedFiniteNestedSource_counts L nX M s
    hOriginalCoord hnum
  have hEarlyData :=
    (exists_preparedFiniteNestedCanonicalEarlyPrimitive_budget s outerDepth innerDepth s
      entropy primitive 2 extra constants).choose_spec.2 m hms G vars nX M
      hB ⟨Nat.cast_nonneg dim, hnum⟩ ⟨le_rfl, hB⟩ ⟨hp0, hpB⟩ ⟨le_rfl, hB⟩
      hVars (hX.trans hpB) hG hM
  have hAcanonical : preparedFiniteNestedSourceExponent (max m s) s entropy primitive 2 extra = Aexp := rfl
  let seed := candidateNestedForwardSeed Aexp constants innerDepth outerDepth Bstruct
  let endpointParameter := preparedFiniteForwardParameter Aexp constants innerDepth seed
  let cost := endpointParameter + 1
  let u := preparedFiniteForwardModelPrecision Aexp constants innerDepth seed p 0
  let modelLog := preparedFiniteForwardWork Aexp constants innerDepth seed
  let anchor := preparedFiniteNestedForwardAllDegreeAnchor outerDepth innerDepth s
  let native := preparedFiniteNestedSourceNative (max m s) G vars nX
    (preparedFiniteForwardDetectorPolynomial s) Aexp 2 constants Bstruct dim 0 p 0 0 anchor
  let pRadius := allocatedCommonProductRadiusLog (max m s) Bstruct Bstruct
  let chartLog := allocatedUniformChartLog (M : ℝ)
  have hData : pRadius ∈ Set.Icc 0 ((Bstruct + 2) ^ earlyPower) ∧
      allocatedComparisonDimension s (dim : ℝ) ∈ Set.Icc 0 ((Bstruct + 2) ^ earlyPower) ∧
      ((nX + s * M : ℕ) : ℝ) ∈ Set.Icc 0 ((Bstruct + 2) ^ earlyPower) ∧
      endpointParameter ∈ Set.Icc 0 ((Bstruct + 2) ^ earlyPower) ∧
      u ∈ Set.Icc 0 ((Bstruct + 2) ^ earlyPower) ∧
      modelLog ∈ Set.Icc 0 ((Bstruct + 2) ^ earlyPower) ∧
      native ∈ Set.Icc 0 ((Bstruct + 2) ^ earlyPower) := by
    obtain ⟨hr, hd, hmod, hend, hslots⟩ := hEarlyData
    obtain ⟨_, _, hu, hw, hn, _⟩ := hslots anchor
    have hEarlyExponent :
        (exists_preparedFiniteNestedCanonicalEarlyPrimitive_budget s outerDepth innerDepth s
          entropy primitive 2 extra constants).choose = earlyPower := rfl
    rw [hEarlyExponent] at hr hd hmod hend hu hw hn
    exact ⟨hr,
      by simpa only [hq] using hd, by simpa only [hq] using hmod,
      by simpa only [hAcanonical] using hend,
      by simpa only [hAcanonical, anchor, preparedFiniteNestedForwardAllDegreeAnchor_stage,
        preparedFiniteNestedForwardAllDegreeAnchor_seed] using hu,
      by simpa only [hAcanonical, anchor, preparedFiniteNestedForwardAllDegreeAnchor_stage,
        preparedFiniteNestedForwardAllDegreeAnchor_seed] using hw,
      by simpa only [hAcanonical] using hn⟩
  have hBase := preparedRelativeEndpointInputBase_bounds earlyPower hB
  have hPowBase : (Bstruct + 2) ^ earlyPower ≤ preparedRelativeEndpointInputBase earlyPower Bstruct := by
    linarith only [hBase.2.2]
  have liftEarly {z : ℝ} (hz : z ∈ Set.Icc 0 ((Bstruct + 2) ^ earlyPower)) :
      z ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower Bstruct) :=
    ⟨hz.1, hz.2.trans hPowBase⟩
  have liftBase {z : ℝ} (hz : z ∈ Set.Icc 0 Bstruct) :
      z ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower Bstruct) :=
    ⟨hz.1, hz.2.trans hBase.2.1⟩
  have hChild0 : 0 ≤ childCost := by dsimp only [childCost, pRelative]; positivity
  have hChildB : childCost ≤ Bstruct := by linarith only [hChartCost]
  have hChartLog0 : 0 ≤ chartLog := by dsimp only [chartLog, allocatedUniformChartLog]; positivity
  have hChartLogB : chartLog ≤ Bstruct := by
    have hchart : chartLog + 1 ≤ pRelative := hStruct.2.2.2.2.2
    linarith only [hchart, hEarly, hStruct.1, hp]
  have hCostBase : cost ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower Bstruct) :=
    ⟨by dsimp only [cost]; linarith only [hData.2.2.2.1.1],
      (add_le_add hData.2.2.2.1.2 le_rfl).trans hBase.2.2⟩
  have hSeed0 : 0 ≤ seed := candidateNestedForwardSeed_nonneg Aexp constants innerDepth outerDepth hB
  have hSeedBase : seed ≤ preparedRelativeEndpointInputBase earlyPower Bstruct :=
    (le_preparedFiniteForwardParameter Aexp constants innerDepth hSeed0).trans
      (hData.2.2.2.1.2.trans hPowBase)
  have hNumData := preparedRelativeEndpoint_numerical_bounds s earlyPower M nX Jalloc hB
    (by simpa only [dim, hq] using hData.2.1.2.trans hPowBase)
    (hData.2.2.1.2.trans hPowBase)
    (liftBase ⟨hB, le_rfl⟩) hCostBase (liftEarly hData.1) (liftBase ⟨hp0, hpB⟩)
    (liftBase ⟨le_rfl, hB⟩) (liftBase ⟨hChartLog0, hChartLogB⟩)
    (liftBase ⟨hChartLog0, hChartLogB⟩) (liftBase ⟨hChild0, hChildB⟩)
    (liftEarly hData.2.2.2.2.1) (liftEarly hData.2.2.2.2.2.1)
    (liftEarly hData.2.2.2.2.2.2) hSeedBase
  let Eearly := 2 * u + 4 * modelLog + 12
  let nativeEarly := preparedConcreteSlicedForecastNativeLog s M nX Jalloc
    Bstruct cost pRadius p 0 chartLog chartLog childCost Eearly
  let massEarly := preparedConcreteSlicedForecastMassLog s M nX Jalloc
    Bstruct cost pRadius p 0 chartLog childCost Eearly
  let Ptest := preparedRelativeEndpointTestLog native nativeEarly
  let Ecompare := preparedRelativeEndpointComparisonLog native nativeEarly massEarly u modelLog cost
  let floorLog := (T + 10) ^ (2 * s + 20)
  let Lmin := preparedRelativeEndpointMinimumScale seed 0 childCost cost floorLog
  let Qgood := preparedRelativeEndpointGoodCutoff Ptest
  obtain ⟨hT, htT, hTK, hK, hTest, hCompare, hnEarly, hmEarly, hnLate, hmLate,
    hModelRequired, hNativeAmbient, hMin, hGood, hSigma, hCoarse, hAmbient, hFloor⟩ := hNumData
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hKbudget : K ∈ Set.Icc 0 ((Bstruct + 2) ^ inputPower) := ⟨hK0, hKPower⟩
  have hRreq := hRequired hp m hms G M vars nX ⟨Nat.cast_nonneg dim, hnum⟩
    ⟨le_rfl, hB⟩ ⟨hp0, hpB⟩ ⟨le_rfl, hB⟩ hM hVars (hX.trans hpB) hG
    hKbudget hKbudget hKbudget hKbudget hKbudget
  have hScale := preparedRelativeEndpointMinimumScale_bounds hSeed0 0 childCost cost floorLog
  have hGoodBounds := preparedRelativeEndpointGoodCutoff_bounds hTest.1
  have hLmin : (Lmin : ℝ) ≤ Real.exp K := hScale.2.2.1.trans (Real.exp_le_exp.mpr hMin)
  have hQgood : 1 ≤ Qgood := hGoodBounds.2.1
  have hQexp : (Qgood : ℝ) ≤ Real.exp K :=
    hGoodBounds.2.2.2.trans (Real.exp_le_exp.mpr hGood)

  let Rreq := preparedCanonicalRelativeSourceRequired L s outerDepth innerDepth
    entropy primitive 2 extra Bstruct p K
  have hRreqCanonical : Rreq ≤ (p + 2) ^ requiredPower := hRreq
  have hKnobRequired : K ≤ Rreq := preparedCanonicalRelativeSourceRequired_endpoint_le
    L s outerDepth innerDepth entropy primitive 2 extra K hB ⟨hp0, hpB⟩
  let pLate := preparedRelativeLateHeight Bstruct p preparationPower requiredPower
  obtain ⟨hpLate, hPadHeight, hPadSize, hLateCoord, hPadRankSum,
    hRoundedRank, hRankLate, hSourceRank, hSourceN, hPadSamplingRank,
    hPadDegree, hPadMem⟩ := preparedRelative_padded_input L (Nat.le_max_left m s)
      preparationPower requiredPower passagePower hp0 hB
      (by simpa only [M, hq] using hM) hheight hsize hRankSum
      N hrank hRreqCanonical (Nat.le_max_left _ _) hN
  have hKnobN : ∀ i, Real.exp K ≤ (N i : ℝ) := fun i =>
    (Real.exp_le_exp.mpr hKnobRequired).trans (hSourceN i)
  have hKnobRank : Real.exp K ≤ (preparedRoundedRank p requiredPower : ℝ) :=
    (Real.exp_le_exp.mpr hKnobRequired).trans hSourceRank
  have hCoordCanonical : ∀ j, Fintype.card (L.pad (max m s) j).Coord ≤ M :=
    fun j => (preparationCoordinateCap_bounds hPadSize (Nat.mul_le_mul_right D hms) j).1
  have hPrepLate : (p + 2) ^ preparationPower ≤ pLate :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hCapLate : (preparationCoordinateCap (max m s) D (s * D) : ℝ) ≤ pLate := by
    exact hM.trans (le_max_left _ _)
  let H := preparedSlicedForecastChildSize childCost
  have hHfloor : H ≤ Lmin := hScale.2.2.2.2.2.1
  have hHcut : Real.exp ((pRelative + 2 + 2) ^ childExponent) ≤ (H : ℝ) := by
    convert preparedSlicedForecastChildSize_lower childCost using 1
    dsimp only [childCost]
    congr 2
    ring
  have hHcost : (H : ℝ) ≤ Real.exp (childCost + 1) :=
    preparedSlicedForecastChildSize_upper hChild0

  have hEndpointDimensions := preparedNestedEndpointDimension_bounds s s le_rfl
    Aexp constants innerDepth outerDepth innerDepth hA.2.2.2.1
    (by dsimp only [outerDepth]; omega) hB
    (show (enlargedPreparedCommonSamplerDimension s M Jalloc : ℝ) ∈ Set.Icc 0 Bstruct from
      ⟨Nat.cast_nonneg _, by simpa only [dim, hq] using hnum⟩)
    nX M (hX.trans hpB) hM
  have hCap := preparedRelativeEndpointForecastCap_le_work s s Aexp le_rfl hA.2.2.1
    constants innerDepth outerDepth innerDepth M nX Jalloc hB
    ⟨hp0, hpB⟩ ⟨hChartLog0, hChartLogB⟩ ⟨hChild0, hChildB⟩
    hEndpointDimensions.1 hEndpointDimensions.2
  let Cslice := preparedFiniteNestedSourceSliceExponent (max m s) s primitive
  have hCsliceCanonical : preparedFiniteNestedSourceSliceExponent (max m s) s primitive = Cslice := rfl
  let sliceLog := (endpointParameter + Cslice) ^ Cslice
  have hBseed : Bstruct ≤ seed :=
    le_candidateNestedForwardSeed Aexp constants innerDepth outerDepth hA.1 hB
  obtain ⟨hModel0, hU0, hCost0, hSlice0, hCostSlice, hSliceWork, hChartSlice, hU⟩ :=
    preparedFiniteForward_endpoint_scalar_bounds Aexp Cslice constants innerDepth vars
      hA.1 (preparedFiniteNestedSourceSliceExponent_bounds (max m s) s primitive).1
      (by simpa only [Cslice, hq] using hA.2.2.2.2)
      hSeed0 hp0 (le_refl 0) (hVars.trans hBseed)
  have hSetupBounds := preparedRelativeEndpointInputScale_setup_bounds s earlyPower M nX Jalloc hB
    (by simpa only [dim, hq] using hData.2.1.2.trans hPowBase)
    (hData.2.2.1.2.trans hPowBase) (liftBase ⟨hB, le_rfl⟩) hCostBase
    (liftEarly hData.1) (liftBase ⟨hp0, hpB⟩) (liftBase ⟨le_rfl, hB⟩)
    (liftBase ⟨hChartLog0, hChartLogB⟩) (liftBase ⟨hChartLog0, hChartLogB⟩)
    (liftBase ⟨hChild0, hChildB⟩)
  obtain ⟨hSpatialLog, hBadLog, hPresLog, hTauLog, hRadiusLog, hDimensionLog,
    hPrimitiveCap, hLayerLog, hModularLog, hXLog, hScaleLog, hJacobianLog,
    hForwardLog, hChildLog⟩ := hSetupBounds
  have hInputBaseScale : preparedRelativeEndpointInputBase earlyPower Bstruct ≤ t :=
    (preparedRelativeEndpointInputScale_bounds s earlyPower hB).2.1
  have hModelK : modelLog ≤ K :=
    (liftEarly hData.2.2.2.2.2.1).2.trans (hInputBaseScale.trans (htT.trans hTK))
  have hCostK : cost ≤ K := hCostBase.2.trans (hInputBaseScale.trans (htT.trans hTK))
  have hFinalRequirements := preparedRelativeFinalEnvelope_ready_requirements s s D
    (nX + s * M) vars basePower inputPower preparationPower requiredPower discount
    hp0 hKPower hDreal (hModularLog.trans (htT.trans hTK)) hChildB hpLate le_rfl
    (by simpa only [add_assoc, show (2 : ℝ) + 2 = 4 by norm_num] using hNorm)
    (hCap.trans hModelK) (hnEarly.2.trans hTK) hCostK
  let lam := (1 - discount) ^ (stage + 1) * Λ
  have hlam : lam ∈ Set.Icc (0 : ℝ) 1 := by
    have hΛzero : 0 ≤ Λ := ((Real.exp_pos (-p)).le.trans ha).trans haΛ
    have hbasezero : 0 ≤ 1 - discount := sub_nonneg.mpr hdiscountOne
    have hbaseone : 1 - discount ≤ 1 := by linarith only [hdiscount]
    exact ⟨mul_nonneg (pow_nonneg hbasezero _) hΛzero,
      (mul_le_mul_of_nonneg_right (pow_le_one₀ hbasezero hbaseone) hΛzero).trans
        (by simpa only [one_mul] using hΛ)⟩

  have hSource := exists_preparedCanonicalInitializedRelativeSource_s2
    L oldPatch F outerDepth innerDepth entropy primitive 2 extra
    (initialCost := childCost + 1)
    hheight hsize hms hs hnX hp (by positivity) hRoundedRank
    hPrepLate hRankLate hCapLate
    ((by norm_num : 1 ≤ 2).trans (preparedCommonRadiusPrimitiveExponent_two_le s)) hK0
    hStructOriginal hEarly hPrecision hX hProfile hCutoff N hrank
    hSourceN hSourceRank ip hip c err hprepare herr ih ha haΛ hΛ habsolute
    hcomplexity hD hrest hStage f (fun x _ => hf x) hfree hscore
    ⟨hdiscount.le, hdiscountOne⟩
    (by simpa only [add_assoc, show (2 : ℝ) + 2 = 4 by norm_num] using hChild0)
    (by
      have hchild : (pRelative + 2 + 2) ^ childExponent = childCost := by
        dsimp only [childCost]; congr 1; ring
      rw [hchild]
      linarith)
    H Lmin Qgood hHfloor hHcut hHcost hLmin hQgood hQexp

  let data := hheight.canonicalPaddedSamplerData L Vars (Nat.le_max_left m s)
    (by positivity) hRoundedRank hPrepLate hRankLate hsize
    (Nat.mul_le_mul_right D hms) hCapLate
  let U := fun j => (L.pad (max m s) j).space
  let : ∀ j, DecidableEq (L.pad (max m s) j).Coord := fun _ => Classical.decEq _
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
  let : CompactSpace (EuclideanJetLayers U (fun _ => Unit)) :=
    hPadHeight.euclideanJetLayers_compact (L.pad (max m s)) hpLate hRoundedRank (fun _ => Unit)
  obtain ⟨hR, σ, hσ, S, hRadius0, hRadius, hσone, hσK, hσinv, hSmin, hSmax,
    hgap, hgeometry, hscalars, hDirectAvailable, hModels, hProductive,
    hmargin, Acandidate, hξone, hEnhanced⟩ := hSource
  obtain ⟨centerLift, hMeasurable, hCenterLift, sampleFn, readFn, hGlobal, hChoose⟩ := hEnhanced
  obtain ⟨center, productive, hReady, hProductiveMass, hProductivePoints, hInit⟩ :=
    hChoose (boundedPrimes Qgood) (boundedPrimes_prime Qgood)
      (fun p => Nat.log p Qgood) (boundedPrimes_log_prime_power_le Qgood)
  let A := Acandidate center
  have hSeedScale : Real.exp seed ≤ (S.value : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr (hScale.2.2.2.1.trans hSmin))
  have hPlateK := (preparedFiniteScheduleDirectCoarse_requested _ K).trans
    (hscalars anchor).coarse_late
  have hξK := Real.exp_le_exp.mpr (neg_le_neg hPlateK)
  let Plate : ℝ := (fun {a b : ℝ} (_ : a ≤ b) => b) hPlateK
  have nativeRule := degreeGlobalizationAt_of_preparedRelativePositiveSource_canonical
    (E := PreparedSamplerContinuous (L.pad (max m s))) A s hq Aexp hAeq
    (fun x => ((f x - (1 - discount) ^ (stage + 1) * Λ : ℝ) : ℂ))
    Bstruct dim 0 p 0 Plate hB ⟨Nat.cast_nonneg _, hnum⟩ ⟨le_rfl, hB⟩
    ⟨hp0, hpB⟩ ⟨le_rfl, hB⟩ hLayers hVariables
    (by simpa only [Fintype.card_fin] using hX.trans hpB) hG
    (by
      intro outerFront outerInner d hd hds pInput hpInput hpInner
      obtain ⟨profile, hx, hg, hu, hm, hn, hp, he, hc⟩ :=
        hReady.2 outerFront outerInner d hd hds pInput hpInput hpInner
      refine ⟨profile, hx, hg, hu, hm, ?_, hp, he, hc⟩
      simpa only [Fintype.card_fin] using hn.trans
        (preparedFiniteNestedSourceNative_literal_eq (max m s) s Aexp 2
          outerDepth innerDepth constants G vars nX Bstruct dim 0 p 0 Plate
          (outerFront, (0 : Fin (s + 1 + 1)), ⟨d, Nat.lt_succ_of_le hd⟩, false)))
    hSeedScale
  let Vtail : Fin (max m s) → ℝ≥0 := fun _ => ⟨Real.exp chartLog, (Real.exp_pos _).le⟩
  let rawCap := 4 * ∏ j, earlyConstantDensityCap
    (Fintype.card (PreparedSamplerContinuous (L.pad (max m s)) j))
    (preparedSamplerTransverse (L.pad (max m s)) j)
    (allocatedCommonProductRadius (max m s) Bstruct Bstruct) (Vtail j)
  let masters : PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth s → ℝ :=
    preparedFiniteNestedSourceMaster (max m s) G vars nX
      (preparedFiniteForwardDetectorPolynomial s) Aexp 2 constants Bstruct dim 0 p 0
  let projectionPrecision := preparedFiniteNestedSourceProjectionPrecision
    (outerDepth := outerDepth) (innerDepth := innerDepth) (cutoff := s)
    (max m s) G vars nX Aexp 2 constants Bstruct dim 0 p 0 Plate K
  let : Nonempty A.Site := A.site_nonempty
  have hDirectReady := hReady.1.1
  have hExcessReady :
      let _ : DecidableEq (Fin nX) := Classical.decEq _
      (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).excessMass
        (A.law.siteLaw (A.physicalBox hξone hmargin)) rawCap ≤
          6 * positiveProjectionAccuracy projectionPrecision := by
    exact hReady.1.2
  obtain ⟨_, _, hSigmaEndpoint, hXiEndpoint, hFloorEndpoint, hGridEndpoint⟩ :=
    preparedRelativeEndpoint_source_bounds_s2 (L.pad (max m s)) M nX Jalloc hCoordCanonical
      (fun _ => σ) _ S.value N hK0 hT
      (by simpa only [hq] using hLayerLog.trans htT)
      (by simpa only [hq] using hModularLog.trans htT)
      (by simpa only [hq] using hDimensionLog.2.trans htT)
      (by simpa only [hq] using hSpatialLog.2.trans htT)
      (hPrimitiveCap.2.trans htT)
      (by simpa only [hq] using hBadLog.2.trans htT)
      hCost0 (hPresLog.2.trans htT) hTest hCompare
      (hRadiusLog.2.trans htT) (hTauLog.2.trans htT)
      (by simpa only [hq] using hSigma)
      (by simpa only [hq] using hCoarse)
      (by simpa only [hq] using hFloor)
      (fun _ => hσ.le) (fun _ => hσK) hξK
      (by simpa only [hq] using hSmin) hKnobN
  have hMarginalCap := preparedRelativeEndpointMarginalCap_le_exp_work s Aexp hA.2.2.1
    (L.pad (max m s)) hq.le M Jalloc hCoordCanonical hB hnum Vtail
    (fun _ => Real.exp_le_exp.mpr hChartLogB) hProfile constants innerDepth outerDepth innerDepth
  obtain ⟨hCapOne, hCapExp, hForecastDetection, hForecastExcess⟩ :=
    preparedRelativePositiveForecastSource_s2 A s Aexp 2 Cslice constants Bstruct p 0 Plate masters
      hDirectReady
      hA.1 hB ⟨hp0, hpB⟩ ⟨le_rfl, hB⟩ hξone hξone hmargin hmargin K rawCap
      (preparedConcreteSlicedForecastCapLog (max m s) M nX Jalloc Bstruct cost pRadius p 0 chartLog childCost)
      hSliceWork ((le_max_right 1 rawCap).trans hMarginalCap)
      (by simpa only [pRadius, hq] using hCap)
      hExcessReady
  have hDetectorDecEq : (fun a b : Fin nX => Classical.propDecidable (a = b)) =
      instDecidableEqFin nX := Subsingleton.elim _ _
  rw [hDetectorDecEq] at hForecastDetection
  have hChildValue : ((fun r : ℝ => (r + 2) ^ childExponent)
      ((p + 2) ^ relativePower + 2)) = childCost := by
    dsimp only [childCost, pRelative]; congr 1; ring
  rw [hChildValue] at hInit
  let testLog := (preparedFiniteForwardDetectorPolynomial s).eval₂ (Nat.castRingHom ℝ)
    (allocatedModelTestLog
      (preparedFiniteForwardSourcePrecision Aexp constants innerDepth seed p 0) modelLog)
  have hTestTwo : 2 ≤ testLog := by
    have hsource0 : 0 ≤ preparedFiniteForwardSourcePrecision Aexp constants innerDepth seed p 0 := by
      simpa only [preparedFiniteForwardPairedSourcePrecision_model] using
        preparedFiniteForwardPairedSourcePrecision_nonneg Aexp 2 constants innerDepth false hSeed0
          ⟨hp0, hpB.trans hBseed⟩ ⟨le_rfl, hB.trans hBseed⟩
    dsimp only [testLog]
    rw [preparedFiniteForwardDetectorPolynomial_eval]
    unfold allocatedModelTestLog
    linarith only [hsource0, hModel0,
      Nat.cast_nonneg (α := ℝ) (preparedFiniteForwardDetectorOffset s)]
  let crtBudget := max 1 (max discount⁻¹ K)
  have hKcrt : K ≤ crtBudget := (le_max_right _ _).trans (le_max_right _ _)
  let finalBudget := preparedFinalScalarBudget s s
    (preparedRelativeFinalEnvelope s basePower inputPower preparationPower requiredPower discount p)
  obtain ⟨hBudgetOne, hBudgetRank, hBudgetDimension, hBudgetMatrix, hBudgetPatch,
    hBudgetCap, hBudgetNative, hBudgetCost⟩ := hFinalRequirements
  have hConclusion : RelativePatchSliceConclusion s N f ((1 - discount) * lam)
      (d₀ + s * (D + E)) (spatialPatchExtractionCost (recoveredKernelScalarBudget finalBudget)) :=
    relativePatchSliceConclusion_of_prepared_source_geometry_s2
    (A := A) (S := S) (M := M) (Jalloc := Jalloc)
    (degree := s) (originalRank := d₀) (D := D) (E := E)
    (pRadius := pRadius) (Pdim := Bstruct) (Qstride := 0)
    (PF := chartLog) (Pchart := chartLog) (childLog := childCost)
    (u := u) (p := modelLog) (pSlice := sliceLog) (pTest := testLog)
    (localBudget := native) (precision := K) (C := max 1 rawCap)
    (Ecompare := Ecompare) (Ptest := Ptest) (budget := finalBudget)
    (prep := L.pad (max m s)) (hprep := hPadHeight) (hpPrep := hpLate) (hRprep := hRoundedRank)
    (eSpatial := preparedSpatialKernelBlocks (max m s) M nX)
    (bW := data.bW) (ν := data.measures.layer) (f := f) (lam := lam)
    (hchild := hChild0) (hgain := le_rfl) (hReady := hProductiveMass)
    (hregularityBudget := by simpa only [add_assoc, show (2 : ℝ) + 2 = 4 by norm_num] using hRegularity)
    (hpGlobal := hB) (hchartGlobal := hChartCost)
    (hscoreGlobal := by simpa only [add_assoc, show (2 : ℝ) + 2 = 4 by norm_num] using hNorm)
    (hmassGlobal := by simpa only [add_assoc, show (2 : ℝ) + 2 = 4 by norm_num] using hMass)
    (hfGlobal := hf) (hlam := hlam) (rule := nativeRule)
    (by omega : 0 < max m s) hCoordCanonical
    hData.1.1 hp0 (le_refl 0) hChartLog0 hChartLog0 hCost0
    (fun j => (data.covolume_bound j).2) (fun j => (hRadius j).1)
    (fun j => (hRadius j).2) (fun _ => hσone)
    Vtail data.chart_bound (fun _ => le_rfl)
    (fun _ => Real.exp chartLog) (fun _ => (Real.exp_pos _).le)
    data.inverse_chart_bound (fun _ => Real.exp_le_exp.mpr hChartLogB)
    (hgeometry anchor) hChild0 (centerLift center) hInit hξone hmargin
    hU0 hModel0 hData.2.2.2.2.2.2.1 hSliceWork hCapOne hCapExp
    (by simpa only [pRadius, hq] using hCap)
    (by simpa only [hq] using hModelRequired.2.trans hTK)
    (by simpa only [native, preparedFiniteNestedSourceNative, anchor,
      preparedFiniteNestedForwardAllDegreeAnchor_degree] using hForecastDetection)
    hForecastExcess hSlice0 hCostSlice
    (hChartSlice (childCost + 1) (hChartCost.trans hBseed)) hTestTwo
    (Fintype.equivFin (L.pad (max m s)).PreparedCoordinate).symm
    (by linarith only [hU])
    (by
      simp only [hq, Ecompare, preparedRelativeEndpointComparisonLog,
        preparedRelativeEndpointTestLog, nativeEarly, massEarly]
      exact le_rfl)
    (by simpa only [nativeEarly, hq] using
      (show max native (3 * nativeEarly + 3) ≤ Ptest from le_rfl))
    hSigmaEndpoint
    (fun i => by
      simpa only [hq] using (Real.exp_le_exp.mpr (hNativeAmbient.2.trans hTK)).trans (hKnobN i))
    (by simpa only [hq] using
      (Real.exp_le_exp.mpr (hNativeAmbient.2.trans hTK)).trans hKnobRank)
    hPadSamplingRank (sampleFn center) (readFn center) (hGlobal center)
    (fun z hz => (hProductivePoints z hz).2.2.2.1)
    (by simpa only [Qgood, preparedRelativeEndpointGoodCutoff,
        modularInitialRankStrength_eq_forecast] using
      (fun z hz => (hProductivePoints z hz).2.2.2.2.1))
    (fun z hz => by simpa only [Fintype.card_fin] using
      (hProductivePoints z hz).2.2.2.2.2)
    hB (by simpa only [Fintype.card_fin] using hX.trans hpB) hVariables
    (by simpa only [Fintype.card_fin] using hnX) hpB
    (fun _ => by simp only [Nat.cast_one, Real.exp_zero]; exact le_rfl)
    hCompare.1 hFloorEndpoint hXiEndpoint hGridEndpoint hLateCoord data.integral_basis_bound
    hdiscount hdiscountOne (le_max_left _ _)
    ((le_max_left _ _).trans (le_max_right _ _))
    ⟨hTest.1, hTest.2.trans (hTK.trans hKcrt)⟩
    (by simpa only [hq] using
      (show preparedSlicedForecastBadLog s nX 0 p ∈ Set.Icc 0 crtBudget from
        ⟨hBadLog.1, hBadLog.2.trans (htT.trans (hTK.trans hKcrt))⟩))
    ⟨hPresLog.1, hPresLog.2.trans (htT.trans (hTK.trans hKcrt))⟩
    hq.le (hPadRankSum.trans (Nat.mul_le_mul_right D (Nat.le_max_left m s)))
    hBudgetOne hBudgetRank (by simpa only [hq, Nat.cast_add, Nat.cast_mul] using hBudgetDimension)
    (by simpa only [hq] using hBudgetMatrix) hBudgetPatch
    (by simpa only [pRadius, hq] using hBudgetCap) (by simpa only [hq] using hBudgetNative)
    hBudgetCost hExtractionFinal.2
  have hTarget : (1 - discount) * lam = (1 - discount) ^ (stage + 2) * Λ := by
    dsimp only [lam]
    rw [show stage + 2 = (stage + 1) + 1 by omega, pow_succ]
    ring
  rw [hTarget] at hConclusion
  exact hConclusion.mono le_rfl hExtractionFinal.1

end Erdos3

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.exists_preparedRelativePatchPowerPassage_s2_oai := @OAI.Erdos3.exists_preparedRelativePatchPowerPassage_s2_oai
