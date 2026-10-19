-- Prove2me | solution 1 for OAI.Erdos3.exists_comparableScalarSelectedBudget_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:58:23.29454+00:00
-- url     : https://prove2.me/submissions/f9970bfe-b323-4fc3-b347-f022776b8956

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B218
import Theorems.Thm_OAI_Erdos3_adaptiveAffineCutoff_reference_bounds_s2

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

theorem affineReferenceInput_le_envelope (epsilon : ℝ) {U : ℝ} (hU : 0 ≤ U) :
    affineReferenceInput epsilon U ≤ (20 * (U + 3)) ^ (affineReferencePower epsilon + 1) := by
  let B := 20 * (U + 3)
  have hB : 2 ≤ B := by dsimp only [B]; linarith
  have hk : 1 ≤ affineReferencePower epsilon := by unfold affineReferencePower; omega
  have hp := pow_le_pow_left₀ (by unfold affinePrimitiveLogBudget; positivity :
      0 ≤ affinePrimitiveLogBudget U + 2)
    (by dsimp only [B]; unfold affinePrimitiveLogBudget; linarith : affinePrimitiveLogBudget U + 2 ≤ B)
    (affineReferencePower epsilon)
  have hBpow : B ≤ B ^ affineReferencePower epsilon := by
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith : 1 ≤ B) hk
  have htail : affinePrimitiveLogBudget U + 3 * U + 10 ≤ B := by
    dsimp only [B]; unfold affinePrimitiveLogBudget; linarith
  have hn : 0 ≤ B ^ affineReferencePower epsilon := pow_nonneg (by linarith) _
  change _ ≤ B ^ (affineReferencePower epsilon + 1)
  rw [pow_succ]
  unfold affineReferenceInput
  nlinarith

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.OriginalParameterReferenceBudget
namespace OAI

section

namespace Erdos3

theorem affineReferenceInput_le_original_power (epsilon : ℝ) {U p : ℝ} {d : ℕ}
    (hp : 2 ≤ p) (hU : 0 ≤ U) (hUp : U ≤ (p + 2) ^ d) :
    affineReferenceInput epsilon U ≤ (p + 2) ^ ((d + 4) * (affineReferencePower epsilon + 1)) := by
  have hbase : 1 ≤ p + 2 := by linarith
  have hpow : 1 ≤ (p + 2) ^ d := one_le_pow₀ hbase
  have h80 : (80 : ℝ) ≤ (p + 2) ^ 4 := by
    calc
      80 ≤ (4 : ℝ) ^ 4 := by norm_num
      _ ≤ (p + 2) ^ 4 := pow_le_pow_left₀ (by norm_num) (by linarith) 4
  have hscale : 20 * (U + 3) ≤ (p + 2) ^ (d + 4) := by
    calc
      _ ≤ 80 * (p + 2) ^ d := by nlinarith
      _ ≤ (p + 2) ^ 4 * (p + 2) ^ d :=
        mul_le_mul_of_nonneg_right h80 (by positivity)
      _ = _ := by rw [pow_add]; ring
  calc
    _ ≤ (20 * (U + 3)) ^ (affineReferencePower epsilon + 1) :=
      affineReferenceInput_le_envelope epsilon hU
    _ ≤ ((p + 2) ^ (d + 4)) ^ (affineReferencePower epsilon + 1) :=
      pow_le_pow_left₀ (by positivity) hscale _
    _ = _ := by rw [pow_mul]

theorem affineCommonReferenceBudget_le_original_power (E : ℕ) (epsilon : ℝ) {U p : ℝ} {d : ℕ}
    (hp : 2 ≤ p) (hU : 0 ≤ U) (hUp : U ≤ (p + 2) ^ d) :
    affineCommonReferenceBudget E epsilon U ≤
      (p + 2) ^ (((d + 4) * (affineReferencePower epsilon + 1) + 1) * E + 1) := by
  let k := (d + 4) * (affineReferencePower epsilon + 1)
  have href : affineReferenceInput epsilon U ≤ (p + 2) ^ k :=
    affineReferenceInput_le_original_power epsilon hp hU hUp
  have hbase : 1 ≤ p + 2 := by linarith
  have hpow : 1 ≤ (p + 2) ^ k := one_le_pow₀ hbase
  have hsum : affineReferenceInput epsilon U + 2 ≤ (p + 2) ^ (k + 1) := by
    rw [pow_succ]
    nlinarith
  have hnonneg : 0 ≤ affineReferenceInput epsilon U + 2 := by
    linarith [(affineReferenceInput_bounds epsilon hU).1]
  change 2 * (affineReferenceInput epsilon U + 2) ^ E ≤ (p + 2) ^ ((k + 1) * E + 1)
  calc
    _ ≤ 2 * ((p + 2) ^ (k + 1)) ^ E :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnonneg hsum E) (by norm_num)
    _ = 2 * (p + 2) ^ ((k + 1) * E) := by rw [pow_mul]
    _ ≤ (p + 2) ^ ((k + 1) * E) * (p + 2) := by
      nlinarith [pow_nonneg (by linarith : 0 ≤ p + 2) ((k + 1) * E)]
    _ = _ := by rw [pow_succ]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.IndexedComparableScalarGeometryData
namespace OAI

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

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ScalarInitialPolynomialBudget
namespace OAI

section

namespace Erdos3

theorem scalarInitialReferenceInput_le_polynomial (m n d A : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (hm : (m : ℝ) ≤ (d + 1 : ℝ) * p) (hn : (n : ℝ) ≤ p) :
    scalarInitialReferenceInput m n d p ((A : ℝ) * (p + 1)) ≤
      (scalarInitialReferencePolynomial d A).eval₂ (Nat.castRingHom ℝ) p := by
  simp [scalarInitialReferenceInput, scalarInitialReferencePolynomial,
    replacementCommonInputLog, replacementCutoffInputLog, physicalReplacementInputLog,
    physicalPairCoefficientLog, smoothPairErrorLog, smoothPairRowErrorLog, scalarTransferTail]
  gcongr

theorem exists_scalarInitialReferenceInput_power_bound (d A : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (m n : ℕ) (p : ℝ), 0 ≤ p →
      (m : ℝ) ≤ (d + 1 : ℝ) * p → (n : ℝ) ≤ p →
      scalarInitialReferenceInput m n d p ((A : ℝ) * (p + 1)) ≤ (p + 2) ^ C := by
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_fixed_power_budget (scalarInitialReferencePolynomial d A)
  refine ⟨C, hC, ?_⟩
  intro m n p hp hm hn
  exact (scalarInitialReferenceInput_le_polynomial m n d A hp hm hn).trans (hbound p hp)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ScalarThresholdPolynomial
namespace OAI

section

namespace Erdos3

theorem scalarCombinedLogThreshold_le_polynomial (n d b : ℕ)
    {p P0 Z G U common refCost : ℝ} (hcommon : 0 ≤ common) (hZ : 0 ≤ Z)
    (hp : p ≤ common) (hP0 : P0 ≤ common) (hZC : Z ≤ common) (hG : G ≤ common) (hU : U ≤ common)
    (hn : (n : ℝ) ≤ common) (hd : (d : ℝ) ≤ common) (href : refCost ≤ common)
    (hb : (b : ℝ) ≤ 1024 * (common + 3) ^ 3) :
    scalarCombinedLogThreshold n d b p P0 Z G refCost
      (scalarTransferCellLog common b p Z U)
      (scalarMeshLog G (P0 + 1) (scalarTransferAccuracyLog b p Z)) ≤
      scalarThresholdPolynomial.eval₂ (Nat.castRingHom ℝ) common := by
  simp [scalarThresholdPolynomial, scalarCombinedLogThreshold, scalarTransferCellLog,
    scalarMeshLog, scalarTransferAccuracyLog, scalarTransferCapLog, scalarTransferTail,
    physicalReplacementThresholdLog, physicalPairCoefficientLog, physicalPairMeanLog,
    smoothPairErrorLog, smoothPairRowErrorLog, Polynomial.eval₂_pow]
  gcongr

theorem exists_scalarCombinedLogThreshold_common_power :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (n d b : ℕ) (p P0 Z G U common refCost : ℝ),
    0 ≤ common → 0 ≤ Z → p ≤ common → P0 ≤ common → Z ≤ common → G ≤ common → U ≤ common →
    (n : ℝ) ≤ common → (d : ℝ) ≤ common → refCost ≤ common →
    (b : ℝ) ≤ 1024 * (common + 3) ^ 3 →
    scalarCombinedLogThreshold n d b p P0 Z G refCost
      (scalarTransferCellLog common b p Z U)
      (scalarMeshLog G (P0 + 1) (scalarTransferAccuracyLog b p Z)) ≤ (common + 2) ^ C := by
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_fixed_power_budget scalarThresholdPolynomial
  refine ⟨C, hC, ?_⟩
  intro n d b p P0 Z G U common refCost hcommon hZ hp hP0 hZC hG hU hn hd href hb
  exact (scalarCombinedLogThreshold_le_polynomial n d b hcommon hZ hp hP0 hZC hG hU hn hd href hb).trans
    (hbound common hcommon)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScalarInitialThreshold
namespace OAI

section

namespace Erdos3

theorem exists_scalarInitialThreshold_power (E d A : ℕ) (hE : 2 ≤ E)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (m n : ℕ) (p : ℝ), 2 ≤ p →
      (m : ℝ) ≤ (d + 1 : ℝ) * p → (n : ℝ) ≤ p →
      epsilon⁻¹ ≤ Real.exp ((A : ℝ) * (p + 1)) →
      scalarInitialThreshold E m n d epsilon p ((A : ℝ) * (p + 1)) ≤ (p + 2) ^ C := by
  obtain ⟨C0, _, hUbound⟩ := exists_scalarInitialReferenceInput_power_bound d A
  obtain ⟨C1, hC1, hthreshold⟩ := exists_scalarCombinedLogThreshold_common_power
  let q := ((C0 + 4) * (affineReferencePower epsilon + 1) + 1) * E + 1
  refine ⟨(q + 2) * C1, by nlinarith [Nat.zero_le q], ?_⟩
  intro m n p hp hm hn heps
  let P0 := (A : ℝ) * (p + 1)
  let Z := replacementCommonInputLog m n d P0
  let G := 2 * physicalPairCoefficientLog n d Z + 2
  let U := scalarInitialReferenceInput m n d p P0
  let pref := affineReferenceInput epsilon U
  let common := affineCommonReferenceBudget E epsilon U
  let b := adaptiveAffineCutoff ⌈(pref + 2) ^ E⌉₊ m n epsilon p
    (scalarTransferTail (3 * p)) Z (scalarTransferBaseAccuracy (3 * p)) Z
  have hp0 : 0 ≤ p := by linarith
  have hP0 : 0 ≤ P0 := by dsimp only [P0]; positivity
  have hZ : 0 ≤ Z := (replacementCommonInputLog_bounds m n d hP0).1
  obtain ⟨hU, hZU, hGU, hP0U, hmU, hnU, hdU, hTU, hpU⟩ := scalarInitialReferenceInput_bounds m n d hp0 hP0
  have hGU' : G ≤ U := by linarith
  have hepsU : epsilon⁻¹ ≤ Real.exp U := heps.trans (Real.exp_le_exp.mpr hP0U)
  have hbase : 0 < scalarTransferBaseAccuracy (3 * p) := Real.exp_pos _
  have hbaseInv : (scalarTransferBaseAccuracy (3 * p))⁻¹ ≤ Real.exp U := by
    simp only [scalarTransferBaseAccuracy, Real.exp_neg, inv_inv]
    apply Real.exp_le_exp.mpr
    unfold scalarTransferTail at hTU
    linarith
  have hT : 0 ≤ scalarTransferTail (3 * p) := by unfold scalarTransferTail; positivity
  have hb := (adaptiveAffineCutoff_reference_bounds_s2 hE hepsilon hepsilon1 hU hp0 hT hZ hZ
    hpU hTU hZU hZU hmU hnU hepsU hbase hbaseInv).2
  have hc := affineCommonReferenceBudget_bounds hE epsilon hU
  have hcost : (pref + 2) ^ E ≤ common := by
    have hpref : 0 ≤ pref + 2 := by linarith [(affineReferenceInput_bounds epsilon hU).1]
    change (pref + 2) ^ E ≤ 2 * (pref + 2) ^ E
    nlinarith [pow_nonneg hpref E]
  have hthresholdCommon := hthreshold n d b p P0 Z G U common ((pref + 2) ^ E) hc.1 hZ
    (hpU.trans hc.2.1) (hP0U.trans hc.2.1) (hZU.trans hc.2.1) (hGU'.trans hc.2.1) hc.2.1
    (hnU.trans hc.2.1) (hdU.trans hc.2.1) hcost hb
  have hUoriginal : U ≤ (p + 2) ^ C0 := hUbound m n p hp0 hm hn
  have hcommonOriginal : common ≤ (p + 2) ^ q :=
    affineCommonReferenceBudget_le_original_power E epsilon hp hU hUoriginal
  exact polynomial_budget_comp hp0 hc.1 q C1 hcommonOriginal hthresholdCommon

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ComparableScalarSelectedBudget
namespace OAI

section

namespace Erdos3

theorem canonicalScalarTarget_dimension_bounds (d : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    let T := 8 * ((d : ℝ)+1) * (p+1)
    p ≤ T ∧ ∀ n : ℕ, (n : ℝ) ≤ p → 4 * ((d : ℝ)*n+1) ≤ T := by
  intro T
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hdp : 0 ≤ (d : ℝ)*p := mul_nonneg hd hp
  constructor
  · dsimp [T]
    nlinarith
  · intro n hn
    have hdn := mul_le_mul_of_nonneg_left hn hd
    dsimp [T]
    nlinarith

theorem exists_canonicalScalarFinalBudget (d A C : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {p : ℝ}, 0 ≤ p →
      let T := 8 * ((d : ℝ)+1) * (p+1)
      let P0 := (A : ℝ) * (T+1)
      let budget := (T+2)^C
      ((d : ℝ)+4) * (budget+P0+20) ≤ (p+D)^D ∧
        budget ≤ (p+D)^D := by
  let T : Polynomial ℕ := 8 * (Polynomial.C d + 1) * (Polynomial.X + 1)
  let Q : Polynomial ℕ := (Polynomial.C d + 4) *
    ((T+2)^C + Polynomial.C A * (T+1) + 20)
  obtain ⟨D, hD, hbound⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨D, hD, ?_⟩
  intro p hp target P0 budget
  have hcost : ((d : ℝ)+4) * (budget+P0+20) ≤ (p+D)^D := by
    simpa [Q, T, target, P0, budget, Polynomial.eval₂_pow] using hbound p hp
  have ht : 0 ≤ target := by dsimp [target]; positivity
  have hP : 0 ≤ P0 := by dsimp [P0]; positivity
  have hb : 0 ≤ budget := by dsimp [budget]; positivity
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  refine ⟨hcost, le_trans ?_ hcost⟩
  nlinarith [mul_nonneg hd (add_nonneg hb hP)]

end Erdos3

end

section

namespace Erdos3

theorem exists_canonicalScalarPrimitiveLogBudget (d marginFactor : ℕ)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ A : ℕ, 3 ≤ A ∧ ∀ {p σ : ℝ} {n : ℕ}, 2 ≤ p →
      (n : ℝ) ≤ p → 0 < σ → σ⁻¹ ≤ Real.exp p →
      let P0 := (A : ℝ) * (p + 1)
      let τ := σ / ((marginFactor : ℝ) * ((n : ℝ) + 1))
      0 ≤ P0 ∧ 3*p+10 ≤ P0 ∧ epsilon⁻¹ ≤ Real.exp P0 ∧
      (probabilityProfileLipschitz : ℝ) ≤ Real.exp P0 ∧
      (d : ℝ) ≤ Real.exp P0 ∧ 2 ≤ Real.exp P0 ∧
      τ⁻¹ ≤ Real.exp P0 ∧ 16 * (2*(d : ℝ)+1) / τ ≤ Real.exp P0 := by
  let M : ℝ := epsilon⁻¹ + (probabilityProfileLipschitz : ℝ) + d +
    marginFactor + 16*(2*(d : ℝ)+1)*marginFactor + 16
  let A : ℕ := ⌈M⌉₊ + 3
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hMA : M ≤ (A : ℝ) := by
    have hh := Nat.le_ceil M
    dsimp [A]
    push_cast
    linarith
  have hA : 3 ≤ A := by dsimp [A]; omega
  refine ⟨A, hA, ?_⟩
  intro p σ n hp hn hσ hσb P0 τ
  have hp0 : 0 ≤ p := by linarith
  have heps0 : 0 ≤ epsilon⁻¹ := inv_nonneg.mpr hepsilon.le
  have hprof0 : 0 ≤ (probabilityProfileLipschitz : ℝ) := probabilityProfileLipschitz.coe_nonneg
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hf0 : (0 : ℝ) ≤ marginFactor := Nat.cast_nonneg _
  have hconst0 : 0 ≤ 16*(2*(d : ℝ)+1)*(marginFactor : ℝ) := by positivity
  have hA16 : (16 : ℝ) ≤ A := by dsimp [M] at hMA; linarith
  have hP0 : 0 ≤ P0 := by dsimp [P0]; positivity
  have hAP0 : (A : ℝ) ≤ P0 := by dsimp [P0]; nlinarith
  have hexp : (A : ℝ) ≤ Real.exp P0 :=
    hAP0.trans (by linarith [Real.add_one_le_exp P0])
  have hscale : (A : ℝ) + 2*p ≤ P0 := by dsimp [P0]; nlinarith
  have hmul (c : ℝ) (hc0 : 0 ≤ c) (hc : c ≤ (A : ℝ)) :
      c * Real.exp (2*p) ≤ Real.exp P0 := by
    have hcExp : c ≤ Real.exp (A : ℝ) :=
      hc.trans (by linarith [Real.add_one_le_exp (A : ℝ)])
    calc
      _ ≤ Real.exp (A : ℝ) * Real.exp (2*p) :=
        mul_le_mul_of_nonneg_right hcExp (Real.exp_nonneg _)
      _ = Real.exp ((A : ℝ)+2*p) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hscale
  have hnexp : (n : ℝ)+1 ≤ Real.exp p := by linarith [Real.add_one_le_exp p]
  have hinv : τ⁻¹ = (marginFactor : ℝ) * ((n : ℝ)+1) * σ⁻¹ := by
    dsimp [τ]
    rw [inv_div, div_eq_mul_inv]
  have hτbound : τ⁻¹ ≤ (marginFactor : ℝ) * Real.exp (2*p) := by
    rw [hinv]
    calc
      _ ≤ (marginFactor : ℝ) * Real.exp p * Real.exp p := by gcongr
      _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  have hKbound : 16*(2*(d : ℝ)+1)/τ ≤
      (16*(2*(d : ℝ)+1)*(marginFactor : ℝ)) * Real.exp (2*p) := by
    rw [div_eq_mul_inv]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hτbound
      (show 0 ≤ 16*(2*(d : ℝ)+1) by positivity)
  refine ⟨hP0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [P0]
    nlinarith
  · apply le_trans _ hexp
    dsimp [M] at hMA
    linarith
  · apply le_trans _ hexp
    dsimp [M] at hMA
    linarith
  · apply le_trans _ hexp
    dsimp [M] at hMA
    linarith
  · linarith
  · apply hτbound.trans (hmul _ hf0 ?_)
    dsimp [M] at hMA
    linarith
  · apply hKbound.trans (hmul _ hconst0 ?_)
    dsimp [M] at hMA
    linarith

end Erdos3

end

section

namespace Erdos3

theorem exists_comparableScalarSelectedBudget_s2_oai (E d r : ℕ)
    (hE : 2 ≤ E) (hd : 2 ≤ d) (hr : 2 ≤ r)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    ∃ A C F : ℕ, 3 ≤ A ∧ 2 ≤ C ∧ 2 ≤ F ∧
    ∀ (n : ℕ) {p σ : ℝ}, 2 ≤ p → (n : ℝ) ≤ p →
      0 < σ → σ⁻¹ ≤ Real.exp p →
    let D := r * d
    let target := 8 * ((D : ℝ) + 1) * (p + 1)
    let P0 := (A : ℝ) * (target + 1)
    let budget := (target + 2) ^ C
    let τ := unconditionedSpatialTrimFraction n σ
    p ≤ target ∧ 2 ≤ target ∧ (n : ℝ) ≤ target ∧
      4 * ((d : ℝ) * n + 1) ≤ target ∧
      0 ≤ P0 ∧ 3 * target + 10 ≤ P0 ∧
      epsilon⁻¹ ≤ Real.exp P0 ∧
      (probabilityProfileLipschitz : ℝ) ≤ Real.exp P0 ∧
      (D : ℝ) ≤ Real.exp P0 ∧ (d : ℝ) ≤ Real.exp P0 ∧
      (r : ℝ) + 1 ≤ Real.exp P0 ∧ 2 ≤ Real.exp P0 ∧
      τ⁻¹ ≤ Real.exp P0 ∧ 16 * (2 * (D : ℝ) + 1) / τ ≤ Real.exp P0 ∧
      0 ≤ budget ∧
      scalarInitialThreshold E ((d + 1) * n) n d epsilon target P0 ≤ budget ∧
      ((D : ℝ) + 4) * (budget + P0 + 20) ≤ (p + F) ^ F ∧
      budget ≤ (p + F) ^ F := by
  obtain ⟨A, hA, hprimitive⟩ := exists_canonicalScalarPrimitiveLogBudget (r*d) 32 hepsilon
  obtain ⟨C, hC, hthreshold⟩ := exists_scalarInitialThreshold_power E d A hE hepsilon hepsilon1
  obtain ⟨F, hF, hfinal⟩ := exists_canonicalScalarFinalBudget (r*d) A C
  refine ⟨A, C, F, hA, hC, hF, ?_⟩
  intro n p σ hp hn hσ hσinv D target P0 budget τ
  have hp0 : 0 ≤ p := by linarith
  have hdD : d ≤ D := by
    have hh := Nat.mul_le_mul_right d hr
    dsimp [D]
    omega
  have hrD : r+1 ≤ D := by
    have hh := Nat.mul_le_mul_left r hd
    dsimp [D]
    omega
  have ht := canonicalScalarTarget_dimension_bounds D hp0
  have hpTarget : p ≤ target := ht.1
  have htarget : 2 ≤ target := hp.trans hpTarget
  have hnTarget : (n : ℝ) ≤ target := hn.trans hpTarget
  have hσTarget : σ⁻¹ ≤ Real.exp target := hσinv.trans (Real.exp_le_exp.mpr hpTarget)
  obtain ⟨hP0, htargetP0, hepsP0, hprofile, hDP0, htwoP0, hτP0, hKP0⟩ :=
    hprimitive htarget hnTarget hσ hσTarget
  have hdP0 : (d : ℝ) ≤ Real.exp P0 := (Nat.cast_le.mpr hdD).trans hDP0
  have hrP0 : (r : ℝ)+1 ≤ Real.exp P0 := by
    have hh : ((r+1 : ℕ) : ℝ) ≤ Real.exp P0 := (Nat.cast_le.mpr hrD).trans hDP0
    simpa only [Nat.cast_add, Nat.cast_one] using hh
  have hframe : 4 * ((d : ℝ)*n+1) ≤ target := by
    apply le_trans _ (ht.2 n hn)
    gcongr
  have hbudget0 : 0 ≤ budget := pow_nonneg (by linarith) _
  have hbudget : scalarInitialThreshold E ((d + 1) * n) n d epsilon target P0 ≤ budget := by
    apply hthreshold _ _ target htarget _ hnTarget hepsP0
    push_cast
    gcongr
  exact ⟨hpTarget, htarget, hnTarget, hframe, hP0, htargetP0, hepsP0, hprofile,
    hDP0, hdP0, hrP0, htwoP0, hτP0, hKP0, hbudget0, hbudget,
    (hfinal hp0).1, (hfinal hp0).2⟩

end Erdos3

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.exists_comparableScalarSelectedBudget_s2_oai := @OAI.Erdos3.exists_comparableScalarSelectedBudget_s2_oai
