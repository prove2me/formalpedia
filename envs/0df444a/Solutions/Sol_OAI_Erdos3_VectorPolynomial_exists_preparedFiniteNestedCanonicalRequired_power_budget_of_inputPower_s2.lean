-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.exists_preparedFiniteNestedCanonicalRequired_power_budget_of_inputPower_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T09:26:45.600988+00:00
-- url     : https://prove2.me/submissions/4bc59e88-ba85-49e1-ae12-d3c39f963650

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B294

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedShortAxis
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem allocatedScaleLog_nonneg {P : ℝ} (hP : 0 ≤ P) : 0 ≤ allocatedScaleLog P := by
  unfold allocatedScaleLog
  positivity

theorem le_allocatedScaleLog {P : ℝ} (hP : 0 ≤ P) : P ≤ allocatedScaleLog P := by
  have h : 0 ≤ P^2*(5*P+49) := by positivity
  unfold allocatedScaleLog
  nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteScheduleWitnessScalarPower
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem exists_preparedFiniteScheduleWitnessScalar_power_budget
    (stageCount inputPower : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {K : Type*} [Fintype K] {B Pscale Pmin Qw : ℝ} (lengths : K → ℝ),
        Fintype.card K ≤ stageCount → 0 ≤ B →
        Pscale ∈ Set.Icc 0 ((B + 2) ^ inputPower) →
        Pmin ∈ Set.Icc 0 ((B + 2) ^ inputPower) →
        Qw ∈ Set.Icc 0 ((B + 2) ^ inputPower) →
        (∀ k, lengths k ∈ Set.Icc 0 ((B + 2) ^ inputPower)) →
        let Pseed := allocatedScaleLog (Pscale + ∑ k, lengths k + Pmin + 1)
        Pseed ∈ Set.Icc 0 ((B + 2) ^ C) ∧
          allocatedWitnessScaleLog Pseed Qw ∈ Set.Icc 0 ((B + 2) ^ C) := by
  let T : Polynomial ℕ := (Polynomial.X + 2) ^ inputPower
  let Input : Polynomial ℕ := T + Polynomial.C stageCount * T + T + 1
  let Seed : Polynomial ℕ := (1 + Input ^ 2) * (5 * Input + 49)
  let Witness : Polynomial ℕ := (1 + Seed ^ 2) * (5 * Seed + 49) + Seed ^ 2 * T
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_fixed_power_budget (Seed + Witness)
  refine ⟨C, hC, ?_⟩
  intro K _ B Pscale Pmin Qw lengths hcard hB hscale hmin hQw hlengths Pseed
  let t : ℝ := (B + 2) ^ inputPower
  let inputBound : ℝ := t + (stageCount : ℝ) * t + t + 1
  let seedBound : ℝ := allocatedScaleLog inputBound
  let witnessBound : ℝ := allocatedWitnessScaleLog seedBound t
  have ht : 0 ≤ t := by dsimp only [t]; positivity
  have hsum0 : 0 ≤ ∑ k, lengths k := Finset.sum_nonneg (fun k _ => (hlengths k).1)
  have hsum : (∑ k, lengths k) ≤ (stageCount : ℝ) * t := by
    calc
      _ ≤ ∑ _k : K, t := Finset.sum_le_sum (fun k _ => (hlengths k).2)
      _ = (Fintype.card K : ℝ) * t := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) ht
  have hinput0 : 0 ≤ Pscale + ∑ k, lengths k + Pmin + 1 := by
    linarith only [hscale.1, hsum0, hmin.1]
  have hinput : Pscale + ∑ k, lengths k + Pmin + 1 ≤ inputBound := by
    dsimp only [inputBound]
    linarith only [hscale.2, hsum, hmin.2]
  have hseed0 : 0 ≤ Pseed := allocatedScaleLog_nonneg hinput0
  have hseed : Pseed ≤ seedBound := by
    dsimp only [Pseed, seedBound, allocatedScaleLog]
    gcongr
  have hwitness0 : 0 ≤ allocatedWitnessScaleLog Pseed Qw :=
    add_nonneg (allocatedScaleLog_nonneg hseed0) (mul_nonneg (sq_nonneg _) hQw.1)
  have hwitness : allocatedWitnessScaleLog Pseed Qw ≤ witnessBound := by
    have hscaleSeed : allocatedScaleLog Pseed ≤ allocatedScaleLog seedBound := by
      unfold allocatedScaleLog
      gcongr
    exact add_le_add hscaleSeed (mul_le_mul (pow_le_pow_left₀ hseed0 hseed 2)
      hQw.2 hQw.1 (sq_nonneg _))
  have hinputBound0 : 0 ≤ inputBound := by dsimp only [inputBound]; positivity
  have hseedBound0 : 0 ≤ seedBound := allocatedScaleLog_nonneg hinputBound0
  have hwitnessBound0 : 0 ≤ witnessBound :=
    add_nonneg (allocatedScaleLog_nonneg hseedBound0) (mul_nonneg (sq_nonneg _) ht)
  have hfinal : seedBound + witnessBound ≤ (B + 2) ^ C := by
    simpa [T, Input, Seed, Witness, t, inputBound, seedBound, witnessBound,
      allocatedScaleLog, allocatedWitnessScaleLog, Polynomial.eval₂_pow] using hbound B hB
  exact ⟨⟨hseed0, by linarith only [hseed, hfinal, hwitnessBound0]⟩,
    ⟨hwitness0, by linarith only [hwitness, hfinal, hseedBound0]⟩⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SpatialNumericEnvelopeFunctoriality
namespace OAI

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

section

namespace Erdos3

theorem spatialPrimitiveEnvelope_mono {p E l p' E' l' : ℝ}
    (hp : 0 ≤ p) (_hE : 0 ≤ E) (hl : 0 ≤ l)
    (hpp : p ≤ p') (hEE : E ≤ E') (hll : l ≤ l') :
    spatialPrimitiveEnvelope p E l ≤ spatialPrimitiveEnvelope p' E' l' := by
  have hp' : 0 ≤ p' := hp.trans hpp
  dsimp only [spatialPrimitiveEnvelope, spatialDisplacementEnvelope,
    spatialDiscretizationEnvelope, spatialLipschitzCostEnvelope,
    spatialThresholdEnvelope, spatialBoundaryEnvelope, spatialMovementEnvelope,
    spatialMeshEnvelope, spatialLipschitzEnvelope, spatialFixedProfileEnvelope,
    coefficientErrorVolumeLog, anisotropicSpatialCapLog]
  gcongr

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

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem exists_preparedFiniteNestedSourceRequired_power_budget
    (A : ℕ) (constants : ℕ → ℕ) (innerDepth outerDepth inputPower slotBound : ℕ)
    (hA : 2 ≤ A) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (Slot : Type*) [Fintype Slot],
      ∀ cutoff ≤ innerDepth, ∀ {x anchorGoodRequired conditionalRequired : ℝ},
      Fintype.card Slot ≤ slotBound → 0 ≤ x →
      anchorGoodRequired ≤ (x + 2) ^ inputPower →
      conditionalRequired ≤ (x + 2) ^ inputPower →
      ∀ (detectorRequired : Slot → ℝ),
      (∀ slot, detectorRequired slot ≤ (x + 2) ^ inputPower) →
      preparedFiniteNestedSourceRequired A constants innerDepth outerDepth cutoff x
        anchorGoodRequired conditionalRequired detectorRequired ≤ (x + 2) ^ C := by
  obtain ⟨D, _, hlocal⟩ :=
    exists_candidateNestedForwardLocal_budget A 0 constants innerDepth outerDepth hA
  let P : Polynomial ℕ := 1 + Polynomial.C (slotBound + 2) *
    (Polynomial.X + Polynomial.C 2) ^ inputPower +
    Polynomial.C ((outerDepth + 1) * (innerDepth + 1)) *
      (Polynomial.X + Polynomial.C 2) ^ D
  obtain ⟨C, hC, hP⟩ := exists_natPolynomial_fixed_power_budget P
  refine ⟨C, hC, ?_⟩
  intro Slot _ cutoff hcutoff x anchorGoodRequired conditionalRequired hcard hx
    hanchor hconditional detectorRequired hdetector
  classical
  have hinputNonneg : 0 ≤ (x + 2) ^ inputPower := pow_nonneg (by linarith) _
  have hlocalNonneg : 0 ≤ (x + 2) ^ D := pow_nonneg (by linarith) _
  have hanchor' : max 0 anchorGoodRequired ≤ (x + 2) ^ inputPower :=
    max_le hinputNonneg hanchor
  have hconditional' : max 0 conditionalRequired ≤ (x + 2) ^ inputPower :=
    max_le hinputNonneg hconditional
  have hdetectorSum : (∑ slot, max 0 (detectorRequired slot)) ≤
      (slotBound : ℝ) * (x + 2) ^ inputPower := by
    calc
      _ ≤ ∑ _slot : Slot, (x + 2) ^ inputPower :=
        Finset.sum_le_sum (fun slot _ => max_le hinputNonneg (hdetector slot))
      _ = (Fintype.card Slot : ℝ) * (x + 2) ^ inputPower := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) hinputNonneg
  have hcumulative (outer : Fin (outerDepth + 1)) (degree : Fin (cutoff + 1)) :
      max 0 (preparedFiniteForwardCumulative A constants degree.val
        (candidateNestedForwardSeed A constants innerDepth outer.val x)) ≤ (x + 2) ^ D := by
    have h := hlocal (gainLog := 0) (stageLog := 0) hx ⟨le_rfl, hx⟩ ⟨le_rfl, hx⟩
      outer.val (Nat.le_of_lt_succ outer.isLt) degree.val
      ((Nat.le_of_lt_succ degree.isLt).trans hcutoff)
    exact max_le hlocalNonneg h.2.2.2.1.2
  have hdegreeSum (outer : Fin (outerDepth + 1)) :
      (∑ degree : Fin (cutoff + 1),
        max 0 (preparedFiniteForwardCumulative A constants degree.val
          (candidateNestedForwardSeed A constants innerDepth outer.val x))) ≤
        ((innerDepth + 1 : ℕ) : ℝ) * (x + 2) ^ D := by
    calc
      _ ≤ ∑ _degree : Fin (cutoff + 1), (x + 2) ^ D :=
        Finset.sum_le_sum (fun degree _ => hcumulative outer degree)
      _ = ((cutoff + 1 : ℕ) : ℝ) * (x + 2) ^ D := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Nat.cast_le.mpr (Nat.succ_le_succ hcutoff)) hlocalNonneg
  have houterSum :
      (∑ outer : Fin (outerDepth + 1), ∑ degree : Fin (cutoff + 1),
        max 0 (preparedFiniteForwardCumulative A constants degree.val
          (candidateNestedForwardSeed A constants innerDepth outer.val x))) ≤
      (((outerDepth + 1) * (innerDepth + 1) : ℕ) : ℝ) * (x + 2) ^ D := by
    calc
      _ ≤ ∑ _outer : Fin (outerDepth + 1),
          ((innerDepth + 1 : ℕ) : ℝ) * (x + 2) ^ D :=
        Finset.sum_le_sum (fun outer _ => hdegreeSum outer)
      _ = _ := by simp [Nat.cast_mul, mul_assoc]
  have hpoly : 1 + ((slotBound + 2 : ℕ) : ℝ) * (x + 2) ^ inputPower +
      (((outerDepth + 1) * (innerDepth + 1) : ℕ) : ℝ) * (x + 2) ^ D ≤
      (x + 2) ^ C := by
    simpa [P, Polynomial.eval₂_pow] using hP x hx
  apply le_trans _ hpoly
  unfold preparedFiniteNestedSourceRequired
  have hmain := add_le_add
    (add_le_add (add_le_add (le_refl (1 : ℝ)) hanchor') hconditional') hdetectorSum
  have htotal := add_le_add hmain houterSum
  convert htotal using 1
  push_cast
  ring

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedFiniteScheduleGeometryBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem exists_preparedFiniteSchedulePowerBudget (m nStages : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {K : Type*} [Fintype K] {P D pRadius Qσ Pmin Qw : ℝ}
      {pDetect Ptail Prho Pk target Tmod : K → ℝ},
      Fintype.card K ≤ nStages → 0 ≤ P → D ∈ Set.Icc 0 P → pRadius ∈ Set.Icc 0 P →
      Qσ ∈ Set.Icc 0 P → Pmin ∈ Set.Icc 0 P → Qw ∈ Set.Icc 0 P →
      (∀ s, pDetect s ∈ Set.Icc 0 P) →
      (∀ s, Ptail s ∈ Set.Icc 0 P) → (∀ s, Prho s ∈ Set.Icc 0 P) →
      (∀ s, Pk s ∈ Set.Icc 0 P) → (∀ s, target s ∈ Set.Icc 0 P) →
      (∀ s, Tmod s ∈ Set.Icc 0 P) →
      let Pscale := preparedUniformDegreeScaleLog (D + pRadius) Ptail Qσ
      let lengthLogs := fun s => allocatedAffineLengthLog m D Pscale (Prho s) (Pk s)
        (target s) (pDetect s + 2) (Tmod s)
      let Pseed := allocatedScaleLog (Pscale + ∑ s, lengthLogs s + Pmin + 1)
      Pscale ∈ Set.Icc 0 ((P + C) ^ C) ∧
        (∑ s, lengthLogs s) ∈ Set.Icc 0 ((P + C) ^ C) ∧
        Pseed ∈ Set.Icc 0 ((P + C) ^ C) ∧
        allocatedWitnessScaleLog Pseed Qw ∈ Set.Icc 0 ((P + C) ^ C) := by
  obtain ⟨A, _, hA⟩ := exists_allocatedAffineScaleLog_bound m
  let X : Polynomial ℕ := Polynomial.X
  let pScale := Polynomial.C (nStages + 3) * X
  let pLength := (Polynomial.C (nStages + 9) * X + 2 + Polynomial.C A) ^ A
  let pInput := pScale + Polynomial.C nStages * pLength + X + 1
  let pSeed := (1 + pInput ^ 2) * (5 * pInput + 49)
  let pWitness := (1 + pSeed ^ 2) * (5 * pSeed + 49) + pSeed ^ 2 * X
  let poly := pScale + pSeed + pWitness
  obtain ⟨C, hC, hpoly⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨C, hC, ?_⟩
  intro K _ P D pRadius Qσ Pmin Qw pDetect Ptail Prho Pk target Tmod
    hCard hP hD hRadius hQσ hPmin hQw hDetect hTail hRho hPk hTarget hMod
    Pscale lengthLogs Pseed
  let scaleBound := ((nStages + 3 : ℕ) : ℝ) * P
  let lengthBound := (((nStages + 9 : ℕ) : ℝ) * P + 2 + A) ^ A
  let inputBound := scaleBound + (nStages : ℝ) * lengthBound + P + 1
  let seedBound := allocatedScaleLog inputBound
  let witnessBound := allocatedWitnessScaleLog seedBound P
  have hTailSum : (∑ s, Ptail s) ≤ (nStages : ℝ) * P := by
    calc
      _ ≤ ∑ _s : K, P := Finset.sum_le_sum (fun s _ => (hTail s).2)
      _ = (Fintype.card K : ℝ) * P := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hCard) hP
  have hTailSum0 : 0 ≤ ∑ s, Ptail s := Finset.sum_nonneg (fun s _ => (hTail s).1)
  have hScale0 : 0 ≤ Pscale := add_nonneg (add_nonneg (add_nonneg hD.1 hRadius.1) hTailSum0) hQσ.1
  have hScale : Pscale ≤ scaleBound := by
    calc
      _ ≤ P + P + (nStages : ℝ) * P + P :=
        add_le_add (add_le_add (add_le_add hD.2 hRadius.2) hTailSum) hQσ.2
      _ = _ := by dsimp only [scaleBound]; push_cast; ring
  have hF (s : K) : 0 ≤ pDetect s + 2 := by linarith only [(hDetect s).1]
  have hLogs0 (s) : 0 ≤ lengthLogs s :=
    (allocatedAffineLengthLog_bounds m hD.1 hScale0 (hRho s).1 (hPk s).1
      (hTarget s).1 (hF s) (hMod s).1).2.2.1
  have hLengths (s) : lengthLogs s ≤ lengthBound := by
    have hInput0 : 0 ≤ D + Pscale + lengthLogs s + 1 := by
      linarith only [hD.1, hScale0, hLogs0 s]
    have hLengthInput : lengthLogs s ≤ D + Pscale + lengthLogs s + 1 := by
      linarith only [hD.1, hScale0]
    apply (hLengthInput.trans (le_allocatedScaleLog hInput0)).trans
    apply (hA D Pscale (Prho s) (Pk s) (target s) (pDetect s + 2) (Tmod s)
      hD.1 hScale0 (hRho s).1 (hPk s).1 (hTarget s).1 (hF s) (hMod s).1).trans
    apply pow_le_pow_left₀ (by
      have hA0 : 0 ≤ (A : ℝ) := Nat.cast_nonneg A
      linarith only [hD.1, hScale0, (hRho s).1, (hPk s).1, (hTarget s).1,
        hF s, (hMod s).1, hA0])
    calc
      _ ≤ P + scaleBound + P + P + P + (P + 2) + P + A := by
        linarith only [hD.2, hScale, (hRho s).2, (hPk s).2,
          (hTarget s).2, (hDetect s).2, (hMod s).2]
      _ = _ := by dsimp only [scaleBound]; push_cast; ring
  have hLengthSum0 : 0 ≤ ∑ s, lengthLogs s := Finset.sum_nonneg (fun s _ => hLogs0 s)
  have hLengthBound0 : 0 ≤ lengthBound := by dsimp only [lengthBound]; positivity
  have hLengthSum : (∑ s, lengthLogs s) ≤ (nStages : ℝ) * lengthBound := by
    calc
      _ ≤ ∑ _s : K, lengthBound := Finset.sum_le_sum (fun s _ => hLengths s)
      _ = (Fintype.card K : ℝ) * lengthBound := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hCard) hLengthBound0
  have hInput0 : 0 ≤ Pscale + ∑ s, lengthLogs s + Pmin + 1 := by
    linarith only [hScale0, hLengthSum0, hPmin.1]
  have hInput : Pscale + ∑ s, lengthLogs s + Pmin + 1 ≤ inputBound := by
    dsimp only [inputBound]
    linarith only [hScale, hLengthSum, hPmin.2]
  have hSeed0 : 0 ≤ Pseed := allocatedScaleLog_nonneg hInput0
  have hSeed : Pseed ≤ seedBound := by
    dsimp only [Pseed, seedBound, allocatedScaleLog]
    gcongr
  have hWitness0 : 0 ≤ allocatedWitnessScaleLog Pseed Qw :=
    add_nonneg (allocatedScaleLog_nonneg hSeed0) (mul_nonneg (sq_nonneg _) hQw.1)
  have hWitness : allocatedWitnessScaleLog Pseed Qw ≤ witnessBound := by
    have hs : allocatedScaleLog Pseed ≤ allocatedScaleLog seedBound := by
      unfold allocatedScaleLog
      gcongr
    exact add_le_add hs (mul_le_mul (pow_le_pow_left₀ hSeed0 hSeed 2)
      hQw.2 hQw.1 (sq_nonneg _))
  have hScaleBound0 : 0 ≤ scaleBound := mul_nonneg (Nat.cast_nonneg _) hP
  have hInputBound0 : 0 ≤ inputBound := by dsimp only [inputBound]; positivity
  have hSeedBound0 : 0 ≤ seedBound := allocatedScaleLog_nonneg hInputBound0
  have hWitnessBound0 : 0 ≤ witnessBound :=
    add_nonneg (allocatedScaleLog_nonneg hSeedBound0) (mul_nonneg (sq_nonneg _) hP)
  have hEnvelope : scaleBound + seedBound + witnessBound ≤ (P + C) ^ C := by
    simpa [poly, pScale, pLength, pInput, pSeed, pWitness, X, scaleBound, lengthBound,
      inputBound, seedBound, witnessBound, allocatedScaleLog, allocatedWitnessScaleLog,
      Polynomial.eval₂_pow] using hpoly P hP
  have hSumSeed : (∑ s, lengthLogs s) ≤ seedBound := by
    apply le_trans (b := inputBound) _ (le_allocatedScaleLog hInputBound0)
    dsimp only [inputBound]
    linarith only [hLengthSum, hScaleBound0, hP]
  exact ⟨⟨hScale0, by linarith only [hScale, hEnvelope, hSeedBound0, hWitnessBound0]⟩,
    ⟨hLengthSum0, by linarith only [hSumSeed, hEnvelope, hScaleBound0, hWitnessBound0]⟩,
    ⟨hSeed0, by linarith only [hSeed, hEnvelope, hScaleBound0, hWitnessBound0]⟩,
    ⟨hWitness0, by linarith only [hWitness, hEnvelope, hScaleBound0, hSeedBound0]⟩⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

theorem exists_preparedFiniteScheduleGeometryBudget
    (m nStages Cmax : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {K : Type} [Fintype K] (degree Cdetect : K → ℕ)
      {G : Type} [Fintype G] {count nX : ℕ}
      {P Bstruct pnum Qstride Qσ Pmin Qw : ℝ}
      (pDetect aDetect target : K → ℝ),
      Fintype.card K ≤ nStages → (∀ k, degree k ≤ m) → (∀ k, Cdetect k ≤ Cmax) →
      0 ≤ P → Bstruct ∈ Set.Icc 0 P → pnum ∈ Set.Icc 0 P →
      (∀ k, pDetect k ∈ Set.Icc 0 P) → (∀ k, aDetect k ∈ Set.Icc 0 P) →
      Qstride ∈ Set.Icc 0 P → (∀ s, target s ∈ Set.Icc 0 P) →
      (count : ℝ) ≤ P → (nX : ℝ) ≤ P → (Fintype.card G : ℝ) ≤ P →
      Qσ ∈ Set.Icc 0 P → Pmin ∈ Set.Icc 0 P → Qw ∈ Set.Icc 0 P →
      let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
      let D := allocatedComparisonDimension m pnum
      let gainLog := fun s : K =>
        slicedDetectionGainLog (degree s) (Cdetect s) count (pDetect s) (pDetect s) (aDetect s)
      let Pk := fun s : K =>
        scalarKernelLogarithmicBudget (Fin ((degree s) + 1)) G (gainLog s + pDetect s + 4)
      let Tmod := fun s : K => ((m + 1 : ℕ) : ℝ) * Pk s + nX * Qstride
      let E := fun s : K => target s + D * ((m * 2 ^ (m + 1) : ℕ) * Pk s) + 5
      let Prho := fun s : K => 2 * affineProfileInputEnvelope D
        (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect s + 2) + 2
      let Ptail := fun s : K => affineProfileToleranceEnvelope m D
        (D * (D + 1) + D * D + D + 1)
        (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect s + 2)
      let Pscale := preparedUniformDegreeScaleLog (D + pRadius) Ptail Qσ
      let lengthLogs := fun s => allocatedAffineLengthLog m D Pscale (Prho s) (Pk s)
        (target s) (pDetect s + 2) (Tmod s)
      let Pseed := allocatedScaleLog (Pscale + ∑ s, lengthLogs s + Pmin + 1)
      let budget := (P + C) ^ C
      P ≤ budget ∧ pRadius ∈ Set.Icc 0 budget ∧ D ∈ Set.Icc 0 budget ∧
        (∀ s, gainLog s ∈ Set.Icc 0 budget ∧ Pk s ∈ Set.Icc 0 budget ∧
          Prho s ∈ Set.Icc 0 budget ∧ Ptail s ∈ Set.Icc 0 budget ∧
          Tmod s ∈ Set.Icc 0 budget) ∧
        Pscale ∈ Set.Icc 0 budget ∧ (∑ s, lengthLogs s) ∈ Set.Icc 0 budget ∧
        Pseed ∈ Set.Icc 0 budget ∧ allocatedWitnessScaleLog Pseed Qw ∈ Set.Icc 0 budget := by
  obtain ⟨A, _, hEarly⟩ := exists_preparedFiniteScheduleEarlyBudget m nStages Cmax
  obtain ⟨L, _, hLate⟩ := exists_preparedFiniteSchedulePowerBudget m nStages
  let X : Polynomial ℕ := Polynomial.X
  let earlyPoly := (X + Polynomial.C A) ^ A
  let latePoly := (earlyPoly + Polynomial.C L) ^ L
  obtain ⟨C, hC, hBound⟩ := exists_natPolynomial_eval_budget (earlyPoly + latePoly)
  refine ⟨C, hC, ?_⟩
  intro K _ degree Cdetect G _ count nX P Bstruct pnum Qstride Qσ Pmin Qw pDetect aDetect target
    hStages hdegree hCdetect hP hB hnum hp ha hQ htarget hcount hnX hG hQσ hPmin hQw
    pRadius D gainLog Pk Tmod E Prho Ptail Pscale lengthLogs Pseed budget
  let early := (P + A) ^ A
  let late := (early + L) ^ L
  have hEarly0 : 0 ≤ early := by dsimp only [early]; positivity
  have hLate0 : 0 ≤ late := by dsimp only [late]; positivity
  have hSum : early + late ≤ budget := by
    simpa [X, earlyPoly, latePoly, early, late, Polynomial.eval₂_pow] using hBound P hP
  have hEarlyCap : early ≤ budget := by linarith only [hSum, hLate0]
  have hLateCap : late ≤ budget := by linarith only [hSum, hEarly0]
  obtain ⟨hPEarly, hRadius, hD, hDegrees⟩ :=
    hEarly degree Cdetect (G := G) pDetect aDetect target
      hStages hdegree hCdetect hP hB hnum hp ha hQ htarget hcount hnX hG
  have lift {x : ℝ} (hx : x ∈ Set.Icc 0 P) : x ∈ Set.Icc 0 early :=
    ⟨hx.1, hx.2.trans hPEarly⟩
  obtain ⟨hScale, hLengths, hSeed, hWitness⟩ :=
    hLate hStages hEarly0 hD hRadius (lift hQσ) (lift hPmin) (lift hQw) (fun s => lift (hp s))
      (fun s => (hDegrees s).2.2.2.1) (fun s => (hDegrees s).2.2.1)
      (fun s => (hDegrees s).2.1) (fun s => lift (htarget s))
      (fun s => (hDegrees s).2.2.2.2)
  have earlyLift {x : ℝ} (hx : x ∈ Set.Icc 0 early) : x ∈ Set.Icc 0 budget :=
    ⟨hx.1, hx.2.trans hEarlyCap⟩
  have lateLift {x : ℝ} (hx : x ∈ Set.Icc 0 late) : x ∈ Set.Icc 0 budget :=
    ⟨hx.1, hx.2.trans hLateCap⟩
  refine ⟨hPEarly.trans hEarlyCap, earlyLift hRadius, earlyLift hD, ?_,
    lateLift hScale, lateLift hLengths, lateLift hSeed, lateLift hWitness⟩
  intro s
  exact ⟨earlyLift (hDegrees s).1, earlyLift (hDegrees s).2.1,
    earlyLift (hDegrees s).2.2.1, earlyLift (hDegrees s).2.2.2.1,
    earlyLift (hDegrees s).2.2.2.2⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedCenteredShortForecastGoodInterface
namespace OAI

section

namespace Erdos3

theorem preparedForecastGoodBudgets (Asp : ℕ) {baseB₀ Pchart Pwidth g V : ℝ}
    (hbase : 0 ≤ baseB₀) (hchart : 0 ≤ Pchart) (hwidth : 0 ≤ Pwidth)
    (hg : 0 ≤ g) (hV : 0 ≤ V) :
    let Bcert := preparedForecastGoodCertificateBudget baseB₀ Pchart Pwidth g V
    let Pgood := preparedForecastGoodAnalyticBudget Asp baseB₀ Pchart Pwidth g V
    0 ≤ Bcert ∧ baseB₀ ≤ Bcert ∧ Pchart ≤ Bcert ∧
      jointPhysicalBaseLog Pwidth (g + 8) V ≤ Bcert ∧
      0 ≤ Pgood ∧ Bcert ≤ Pgood ∧ Pwidth ≤ Pgood ∧
      (Pchart + Asp) ^ Asp ≤ Pgood ∧ g + 8 ≤ Pgood := by
  intro Bcert Pgood
  have hphysical : 0 ≤ jointPhysicalBaseLog Pwidth (g + 8) V := by
    unfold jointPhysicalBaseLog
    positivity
  have hcert : 0 ≤ Bcert := by
    dsimp only [Bcert, preparedForecastGoodCertificateBudget]
    positivity
  have hpower : 0 ≤ (Pchart + Asp) ^ Asp := by positivity
  have hgood : 0 ≤ Pgood := by
    change 0 ≤ Bcert + Pwidth + (Pchart + Asp) ^ Asp + g + 9
    positivity
  have hdef : Bcert = 1 + baseB₀ + Pchart + jointPhysicalBaseLog Pwidth (g + 8) V := rfl
  have hgdef : Pgood = Bcert + Pwidth + (Pchart + Asp) ^ Asp + g + 9 := rfl
  refine ⟨hcert, ?_, ?_, ?_, hgood, ?_, ?_, ?_, ?_⟩ <;>
    linarith only [hdef, hgdef, hbase, hchart, hwidth, hg, hphysical, hcert, hpower]

theorem exists_preparedForecastGoodBudgets_bound (Asp : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {P baseB₀ Pchart Pwidth g V : ℝ},
      0 ≤ P → baseB₀ ∈ Set.Icc 0 P → Pchart ∈ Set.Icc 0 P →
      Pwidth ∈ Set.Icc 0 P → g ∈ Set.Icc 0 P → V ∈ Set.Icc 0 P →
      preparedForecastGoodCertificateBudget baseB₀ Pchart Pwidth g V ∈
        Set.Icc 0 ((P + C) ^ C) ∧
      preparedForecastGoodAnalyticBudget Asp baseB₀ Pchart Pwidth g V ∈
        Set.Icc 0 ((P + C) ^ C) := by
  let poly : Polynomial ℕ :=
    15 * Polynomial.X + 160 + (Polynomial.X + Polynomial.C Asp) ^ Asp
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨C, hC, ?_⟩
  intro P baseB₀ Pchart Pwidth g V hP hbase hchart hwidth hg hV
  obtain ⟨hcert, _, _, _, hgood, hcertGood, _, _, _⟩ :=
    preparedForecastGoodBudgets Asp hbase.1 hchart.1 hwidth.1 hg.1 hV.1
  have hpow : (Pchart + Asp) ^ Asp ≤ (P + Asp) ^ Asp :=
    pow_le_pow_left₀ (add_nonneg hchart.1 (Nat.cast_nonneg _))
      (add_le_add hchart.2 (le_refl (Asp : ℝ))) Asp
  have hgoodUpper : preparedForecastGoodAnalyticBudget Asp baseB₀ Pchart Pwidth g V ≤
      15 * P + 160 + (P + Asp) ^ Asp := by
    unfold preparedForecastGoodAnalyticBudget preparedForecastGoodCertificateBudget jointPhysicalBaseLog
    linarith only [hbase.2, hchart.2, hwidth.2, hg.2, hV.2, hpow]
  have hpoly : 15 * P + 160 + (P + Asp) ^ Asp ≤ (P + C) ^ C := by
    simpa [poly, Polynomial.eval₂_pow] using hbound P hP
  exact ⟨⟨hcert, hcertGood.trans (hgoodUpper.trans hpoly)⟩,
    ⟨hgood, hgoodUpper.trans hpoly⟩⟩

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

theorem exists_preparedShortForecastRequired_power_budget (m inputPower : ℕ) :
    ∃ outputPower : ℕ, 2 ≤ outputPower ∧ ∀ p : ℝ, 2 ≤ p →
      ∀ Pmaster Plate E B0 Pgood Pprod : ℝ,
        0 ≤ Pmaster → Pmaster ≤ Plate → Plate ≤ (p + 2) ^ inputPower →
        E ∈ Set.Icc 0 ((p + 2) ^ inputPower) →
        B0 ∈ Set.Icc 0 ((p + 2) ^ inputPower) →
        Pgood ∈ Set.Icc 0 ((p + 2) ^ inputPower) →
        Pprod ∈ Set.Icc 0 ((p + 2) ^ inputPower) →
        preparedShortForecastProductiveRequired m Pmaster Plate E B0 Pgood Pprod ≤
          (p + 2) ^ outputPower := by
  obtain ⟨C, _, hresources⟩ := exists_preparedModularGeneralDetector_resource_budget
    (preparedModularGeneralDetectorConstants m 0) 1
  let Am := preparedCenteredMarginalExponent m
  let Ab := preparedBadProductSpatialExponent m
  let At := allocatedMaskedTiltedConstant m
  let Ag := preparedCenteredShortForecastGoodExponent m
  let Ap := preparedModularGeneralProductivityExponent m
  let U : Polynomial ℕ := (Polynomial.X + 2) ^ inputPower
  let B : Polynomial ℕ := (2 * U + Polynomial.C C) ^ C
  let Q : Polynomial ℕ := B + (B + U + Polynomial.C Am) ^ Am +
    ((U + Polynomial.C Ab) ^ Ab + Polynomial.C At) ^ At +
    (U + Polynomial.C Ag) ^ Ag + (U + Polynomial.C Ap) ^ Ap
  obtain ⟨outputPower, houtputPower, hQ⟩ := exists_natPolynomial_fixed_power_budget Q
  refine ⟨outputPower, houtputPower, ?_⟩
  intro p hp Pmaster Plate E B0 Pgood Pprod hMaster hLate hPlate hE hB0 hGood hProd
  let u := (p + 2) ^ inputPower
  let b := (2 * u + C) ^ C
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hmaster : Pmaster ≤ u := hLate.trans hPlate
  have hres := (hresources hMaster hLate).1
  have hresbound : (Pmaster + Plate + C) ^ C ≤ b :=
    pow_le_pow_left₀ (by have := hMaster.trans hLate; positivity)
      (by change Pmaster + Plate + C ≤ 2 * u + C; linarith) C
  have hrequired := hres.required.2.trans hresbound
  have hproj := hres.Pproj.2.trans hresbound
  let r := preparedModularGeneralDetectorResources
    (preparedModularGeneralDetectorConstants m 0) 1 Pmaster Plate
  have hmarg : (max r.Pproj E + Am) ^ Am ≤ (b + u + Am) ^ Am := by
    apply pow_le_pow_left₀
      (add_nonneg (hres.Pproj.1.trans (le_max_left _ _)) (Nat.cast_nonneg Am))
    exact add_le_add (max_le (by change r.Pproj ≤ b + u; linarith)
      (by change E ≤ b + u; have := hE.2; linarith)) le_rfl
  have hbad : ((B0 + Ab) ^ Ab + At) ^ At ≤ ((u + Ab) ^ Ab + At) ^ At := by
    apply pow_le_pow_left₀ (by have := hB0.1; positivity)
    exact add_le_add (pow_le_pow_left₀ (by have := hB0.1; positivity)
      (add_le_add hB0.2 le_rfl) Ab) le_rfl
  have hgood : (Pgood + Ag) ^ Ag ≤ (u + Ag) ^ Ag :=
    pow_le_pow_left₀ (by have := hGood.1; positivity) (add_le_add hGood.2 le_rfl) Ag
  have hprod : (Pprod + Ap) ^ Ap ≤ (u + Ap) ^ Ap :=
    pow_le_pow_left₀ (by have := hProd.1; positivity) (add_le_add hProd.2 le_rfl) Ap
  have hmarg0 : 0 ≤ (b + u + Am) ^ Am := by positivity
  have hbad0 : 0 ≤ ((u + Ab) ^ Ab + At) ^ At := by positivity
  have hgood0 : 0 ≤ (u + Ag) ^ Ag := by positivity
  have hprod0 : 0 ≤ (u + Ap) ^ Ap := by positivity
  have htotal : b + (b + u + Am) ^ Am + ((u + Ab) ^ Ab + At) ^ At +
      (u + Ag) ^ Ag + (u + Ap) ^ Ap ≤ (p + 2) ^ outputPower := by
    simpa [Q, B, U, b, u, Polynomial.eval₂_pow] using hQ p (by linarith : 0 ≤ p)
  change max (max r.required ((max r.Pproj E + Am) ^ Am))
    (max (max (((B0 + Ab) ^ Ab + At) ^ At) ((Pgood + Ag) ^ Ag))
      ((Pprod + Ap) ^ Ap)) ≤ _
  apply max_le
  · apply max_le
    · change r.required ≤ _
      linarith
    · linarith
  · apply max_le
    · exact max_le (by linarith) (by linarith)
    · linarith

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem exists_preparedShortForecastConstructedRequired_power_budget (m inputPower : ℕ) :
    ∃ outputPower : ℕ, 2 ≤ outputPower ∧ ∀ p : ℝ, 2 ≤ p →
      ∀ Pmaster Plate Eforecast baseB0 Pchart gainLog Vlog : ℝ,
        0 ≤ Pmaster → Pmaster ≤ Plate → Plate ≤ (p + 2) ^ inputPower →
        Eforecast ∈ Set.Icc 0 ((p + 2) ^ inputPower) →
        baseB0 ∈ Set.Icc 0 ((p + 2) ^ inputPower) →
        Pchart ∈ Set.Icc 0 ((p + 2) ^ inputPower) →
        gainLog ∈ Set.Icc 0 ((p + 2) ^ inputPower) →
        Vlog ∈ Set.Icc 0 ((p + 2) ^ inputPower) →
        let Pwidth := 4 * (Plate + 8)^2
        preparedShortForecastProductiveRequired m Pmaster Plate Eforecast
          (preparedForecastGoodCertificateBudget baseB0 Pchart Pwidth gainLog Vlog)
          (preparedForecastGoodAnalyticBudget (preparedCenteredShortForecastSpatialExponent m)
            baseB0 Pchart Pwidth gainLog Vlog) Pwidth ≤ (p + 2)^outputPower := by
  obtain ⟨C, _, hGoodBudgets⟩ :=
    exists_preparedForecastGoodBudgets_bound (preparedCenteredShortForecastSpatialExponent m)
  let U : Polynomial ℕ := (Polynomial.X + 2)^inputPower
  let W : Polynomial ℕ := U + 4 * (U + 8)^2
  let Q : Polynomial ℕ := W + (W + Polynomial.C C)^C
  obtain ⟨inflatedPower, _, hInflated⟩ := exists_natPolynomial_fixed_power_budget Q
  obtain ⟨outputPower, houtputPower, hRequired⟩ :=
    exists_preparedShortForecastRequired_power_budget m inflatedPower
  refine ⟨outputPower, houtputPower, ?_⟩
  intro p hp Pmaster Plate Eforecast baseB0 Pchart gainLog Vlog
    hMaster hLate hPlate hE hBase hChart hGain hV
  let u := (p + 2)^inputPower
  let w := u + 4 * (u + 8)^2
  let Pwidth := 4 * (Plate + 8)^2
  have hu : 0 ≤ u := by dsimp only [u]; positivity
  have huw : u ≤ w := by dsimp only [w]; nlinarith [sq_nonneg (u + 8)]
  have hw : 0 ≤ w := hu.trans huw
  have hwidth0 : 0 ≤ Pwidth := by dsimp only [Pwidth]; positivity
  have hLate0 : 0 ≤ Plate := hMaster.trans hLate
  have hwidth : Pwidth ≤ w := by
    have hsquare : (Plate + 8)^2 ≤ (u + 8)^2 :=
      pow_le_pow_left₀ (by linarith) (add_le_add hPlate le_rfl) 2
    dsimp only [Pwidth, w]
    nlinarith
  have hBcertGood := hGoodBudgets hw
    ⟨hBase.1, hBase.2.trans huw⟩ ⟨hChart.1, hChart.2.trans huw⟩
    ⟨hwidth0, hwidth⟩ ⟨hGain.1, hGain.2.trans huw⟩ ⟨hV.1, hV.2.trans huw⟩
  have hpower0 : 0 ≤ (w + C)^C := by positivity
  have hInflatedReal : w + (w + C)^C ≤ (p + 2)^inflatedPower := by
    simpa [Q, W, U, w, u, Polynomial.eval₂_pow] using hInflated p (by linarith : 0 ≤ p)
  have hwInflated : w ≤ (p + 2)^inflatedPower :=
    (le_add_of_nonneg_right hpower0).trans hInflatedReal
  have hpowerInflated : (w + C)^C ≤ (p + 2)^inflatedPower :=
    (le_add_of_nonneg_left hw).trans hInflatedReal
  exact hRequired p hp Pmaster Plate Eforecast
    (preparedForecastGoodCertificateBudget baseB0 Pchart Pwidth gainLog Vlog)
    (preparedForecastGoodAnalyticBudget (preparedCenteredShortForecastSpatialExponent m)
      baseB0 Pchart Pwidth gainLog Vlog) Pwidth hMaster hLate
    (hPlate.trans (huw.trans hwInflated))
    ⟨hE.1, hE.2.trans (huw.trans hwInflated)⟩
    ⟨hBcertGood.1.1, hBcertGood.1.2.trans hpowerInflated⟩
    ⟨hBcertGood.2.1, hBcertGood.2.2.trans hpowerInflated⟩
    ⟨hwidth0, hwidth.trans hwInflated⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedFiniteNestedSourceLatePowerBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem PreparedModularCanonicalDetectorResources.Bounds.mono
    {r : PreparedModularCanonicalDetectorResources ℝ} {B C : ℝ}
    (h : r.Bounds B) (hBC : B ≤ C) : r.Bounds C := by
  have lift {a : ℝ} (ha : a ∈ Set.Icc 0 B) : a ∈ Set.Icc 0 C :=
    ⟨ha.1, ha.2.trans hBC⟩
  cases h
  constructor <;> apply lift <;> assumption

theorem exists_preparedModularGeneral_cutoff_resource_budget (m cutoff : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {P L : ℝ}, 0 ≤ P → P ≤ L → ∀ degree : ℕ,
      degree ≤ cutoff →
      let r := preparedModularGeneralDetectorResources
        (preparedModularGeneralDetectorConstants m degree) (degree + 1) P L
      r.Bounds ((P + L + C) ^ C) := by
  let K (degree : Fin (cutoff + 1)) := preparedModularGeneralDetectorConstants m degree.val
  let A (degree : Fin (cutoff + 1)) := Classical.choose
    (exists_preparedModularGeneralDetector_resource_budget (K degree) (degree.val + 1))
  let poly : Polynomial ℕ := ∑ degree : Fin (cutoff + 1),
    (Polynomial.X + Polynomial.C (A degree)) ^ A degree
  obtain ⟨C, hC, hpoly⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨C, hC, ?_⟩
  intro P L hP hPL degree hdegree r
  let i : Fin (cutoff + 1) := ⟨degree, Nat.lt_succ_of_le hdegree⟩
  have hsum : (P + L + A i) ^ A i ≤
      ∑ j : Fin (cutoff + 1), (P + L + A j) ^ A j :=
    Finset.single_le_sum
      (f := fun j : Fin (cutoff + 1) => (P + L + (A j : ℝ)) ^ A j)
      (fun j _ => by have hL := hP.trans hPL; positivity) (Finset.mem_univ i)
  have hbound : (P + L + A i) ^ A i ≤ (P + L + C) ^ C := by
    apply hsum.trans
    simpa [poly, Polynomial.eval₂_finsetSum, Polynomial.eval₂_pow] using
      hpoly (P + L) (add_nonneg hP (hP.trans hPL))
  have hstage := ((Classical.choose_spec
    (exists_preparedModularGeneralDetector_resource_budget (K i) (i.val + 1))).2 hP hPL).1
  exact hstage.mono hbound

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

theorem PreparedEmptyLayerLocalScheduleBudget.mono
    {m : ℕ} {K G : Type} [Fintype K] [Fintype G]
    {degree Cdetect : K → ℕ} {nX count : ℕ}
    {Bstruct pnum Qstride Qσ requestedCoarse extraLate : ℝ}
    {u model : K → ℝ} {cap cap' : ℝ}
    (h : PreparedEmptyLayerLocalScheduleBudget (G := G) m degree Cdetect nX count
      Bstruct pnum Qstride Qσ requestedCoarse extraLate u model cap) (hcap : cap ≤ cap') :
    PreparedEmptyLayerLocalScheduleBudget (G := G) m degree Cdetect nX count
      Bstruct pnum Qstride Qσ requestedCoarse extraLate u model cap' := by
  unfold PreparedEmptyLayerLocalScheduleBudget at h ⊢
  dsimp only at h ⊢
  have lift {x : ℝ} (hx : x ∈ Set.Icc 0 cap) : x ∈ Set.Icc 0 cap' := ⟨hx.1, hx.2.trans hcap⟩
  refine ⟨lift h.1, lift h.2.1, lift h.2.2.1, lift h.2.2.2.1, lift h.2.2.2.2.1, ?_⟩
  intro k
  obtain ⟨hg, hk, hp, ht, hr, htail, hl, hm, hres⟩ := h.2.2.2.2.2 k
  exact ⟨lift hg, lift hk, lift hp, lift ht, lift hr, lift htail, lift hl, lift hm,
    hres.mono hcap⟩

theorem exists_preparedEmptyLayerLocalSchedule_budget (m nStages Cmax : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {K G : Type} [Fintype K] [Fintype G]
      (degree Cdetect : K → ℕ) {nX count : ℕ}
      {P Bstruct pnum Qstride Qσ requestedCoarse extraLate : ℝ}
      (u model : K → ℝ),
      Fintype.card K ≤ nStages → (∀ k, degree k ≤ m) → (∀ k, Cdetect k ≤ Cmax) →
      0 ≤ P → Bstruct ∈ Set.Icc 0 P → pnum ∈ Set.Icc 0 P →
      Qstride ∈ Set.Icc 0 P → Qσ ∈ Set.Icc 0 P →
      requestedCoarse ∈ Set.Icc 0 P → extraLate ∈ Set.Icc 0 P →
      (∀ k, u k ∈ Set.Icc 0 P) → (∀ k, model k ∈ Set.Icc 0 P) →
      (count : ℝ) ≤ P → (nX : ℝ) ≤ P → (Fintype.card G : ℝ) ≤ P →
      PreparedEmptyLayerLocalScheduleBudget (G := G) m degree Cdetect nX count
        Bstruct pnum Qstride Qσ requestedCoarse extraLate u model ((P + 2) ^ C) := by
  obtain ⟨A, _, hEarly⟩ := exists_preparedFiniteScheduleEarlyBudget m nStages Cmax
  obtain ⟨B, _, hGeom⟩ := exists_preparedFiniteScheduleGeometryBudget m nStages Cmax
  obtain ⟨R, _, hResources⟩ := exists_preparedModularGeneral_cutoff_resource_budget m m
  let X : Polynomial ℕ := Polynomial.X
  let rawPoly := 7 * X + 12
  let earlyPoly := (rawPoly + Polynomial.C A) ^ A
  let physicalPoly := Polynomial.C (m + 2) + 3 * X + earlyPoly
  let precisionPoly := rawPoly + earlyPoly + physicalPoly + 40 + coefficientErrorSpatialLog physicalPoly
  let geomPoly := (precisionPoly + Polynomial.C B) ^ B
  let masterPoly := 11 * geomPoly + 32
  let coarsePoly := Polynomial.C nStages * (geomPoly + 32) + X
  let spatialPoly := spatialPrimitiveEnvelope geomPoly coarsePoly 0
  let latePoly := masterPoly + geomPoly + coarsePoly +
    (2 * (spatialPoly + spatialTupleToleranceLog spatialPoly) + 4) + X
  let sumLatePoly := Polynomial.C nStages * latePoly
  let resourcesPoly := (masterPoly + sumLatePoly + Polynomial.C R) ^ R
  obtain ⟨C, hC, hPoly⟩ := exists_natPolynomial_fixed_power_budget
    (geomPoly + masterPoly + coarsePoly + sumLatePoly + resourcesPoly)
  refine ⟨C, hC, ?_⟩
  intro K G _ _ degree Cdetect nX count P Bstruct pnum Qstride Qσ requestedCoarse extraLate
    u model hCard hdegree hCdetect hP hB hnum hQ hQσ hCoarse hExtra hu hmodel hcount hnX hG
  unfold PreparedEmptyLayerLocalScheduleBudget
  intro pRadius D pDetect aDetect gain Pk physical target E rho tail scale tmod lengths master coarse late
  let raw : ℝ := 7 * P + 12
  let early : ℝ := (raw + A) ^ A
  let physicalBound : ℝ := ((m + 2 : ℕ) : ℝ) + 3 * P + early
  let precision : ℝ := raw + early + physicalBound + 40 + coefficientErrorSpatialLog physicalBound
  let geom : ℝ := (precision + B) ^ B
  let masterBound : ℝ := 11 * geom + 32
  let coarseBound : ℝ := (nStages : ℝ) * (geom + 32) + P
  let spatial : ℝ := spatialPrimitiveEnvelope geom coarseBound 0
  let lateBound : ℝ := masterBound + geom + coarseBound +
    (2 * (spatial + spatialTupleToleranceLog spatial) + 4) + P
  let sumLateBound : ℝ := (nStages : ℝ) * lateBound
  let resourceBound : ℝ := (masterBound + sumLateBound + R) ^ R
  have hraw0 : 0 ≤ raw := by dsimp [raw]; positivity
  have hPraw : P ≤ raw := by dsimp [raw]; linarith
  have liftRaw {x : ℝ} (hx : x ∈ Set.Icc 0 P) : x ∈ Set.Icc 0 raw :=
    ⟨hx.1, hx.2.trans hPraw⟩
  have hp (k) : pDetect k ∈ Set.Icc 0 raw := by
    dsimp only [pDetect, allocatedModelTestLog, raw]
    constructor <;> linarith only [(hu k).1, (hu k).2, (hmodel k).1, (hmodel k).2]
  have ha (k) : aDetect k ∈ Set.Icc 0 raw := by
    dsimp only [aDetect, raw]
    constructor <;> linarith only [(hu k).1, (hu k).2, (hmodel k).1, (hmodel k).2, hP]
  obtain ⟨hrawEarly, _, _, hStageEarly⟩ :=
    hEarly degree Cdetect (G := G) pDetect aDetect (fun _ => 0)
      hCard hdegree hCdetect hraw0 (liftRaw hB) (liftRaw hnum) hp ha (liftRaw hQ)
      (fun _ => ⟨le_rfl, hraw0⟩) (hcount.trans hPraw) (hnX.trans hPraw) (hG.trans hPraw)
  have hgain (k) : gain k ∈ Set.Icc 0 early := (hStageEarly k).1
  have hkernel (k) : Pk k ∈ Set.Icc 0 early := (hStageEarly k).2.1
  have hearly0 : 0 ≤ early := hraw0.trans hrawEarly
  have hphysicalBound0 : 0 ≤ physicalBound := by dsimp [physicalBound]; positivity
  have hphysical (k) : physical k ∈ Set.Icc 0 physicalBound := by
    dsimp only [physical, preparedFiniteScheduleLocalPhysical, physicalBound]
    constructor
    · have := hQ.1; have := (hkernel k).1; positivity
    · linarith only [hnX, hcount, hQ.2, (hkernel k).2]
  have hprecision0 : 0 ≤ precision := by
    have := coefficientErrorSpatialLog_nonneg hphysicalBound0
    dsimp only [precision]; positivity
  have hrawPrecision : raw ≤ precision := by
    have := coefficientErrorSpatialLog_nonneg hphysicalBound0
    dsimp only [precision]; linarith
  have hearlyPrecision : early ≤ precision := by
    have := coefficientErrorSpatialLog_nonneg hphysicalBound0
    dsimp only [precision]; linarith
  have htarget (k) : target k ∈ Set.Icc 0 precision := by
    have hsp : coefficientErrorSpatialLog (physical k) ≤ coefficientErrorSpatialLog physicalBound := by
      have := (hphysical k).1
      unfold coefficientErrorSpatialLog coefficientErrorVolumeLog anisotropicSpatialCapLog
      gcongr <;> exact (hphysical k).2
    constructor
    · have := (hgain k).1
      have := coefficientErrorSpatialLog_nonneg (hphysical k).1
      dsimp only [target]; positivity
    · dsimp only [target, precision]
      linarith only [(hgain k).2, hsp, hraw0, hphysicalBound0]
  have hPprecision : P ≤ precision := hPraw.trans hrawPrecision
  have liftPrecision {x : ℝ} (hx : x ∈ Set.Icc 0 P) : x ∈ Set.Icc 0 precision :=
    ⟨hx.1, hx.2.trans hPprecision⟩
  obtain ⟨hprecisionGeom, hradius, hD, hStage, hscale, hlengthSum, _, _⟩ :=
    hGeom degree Cdetect (G := G) pDetect aDetect target
      hCard hdegree hCdetect hprecision0 (liftPrecision hB) (liftPrecision hnum)
      (fun k => ⟨(hp k).1, (hp k).2.trans hrawPrecision⟩)
      (fun k => ⟨(ha k).1, (ha k).2.trans hrawPrecision⟩)
      (liftPrecision hQ) htarget (hcount.trans hPprecision) (hnX.trans hPprecision)
      (hG.trans hPprecision) (liftPrecision hQσ) ⟨le_rfl, hprecision0⟩ ⟨le_rfl, hprecision0⟩
  change precision ≤ geom at hprecisionGeom
  change pRadius ∈ Set.Icc 0 geom at hradius
  change D ∈ Set.Icc 0 geom at hD
  change (∀ k, gain k ∈ Set.Icc 0 geom ∧ Pk k ∈ Set.Icc 0 geom ∧
    rho k ∈ Set.Icc 0 geom ∧ tail k ∈ Set.Icc 0 geom ∧ tmod k ∈ Set.Icc 0 geom) at hStage
  change scale ∈ Set.Icc 0 geom at hscale
  change (∑ k, lengths k) ∈ Set.Icc 0 geom at hlengthSum
  have hgeom0 : 0 ≤ geom := hprecision0.trans hprecisionGeom
  have hPgeom : P ≤ geom := hPprecision.trans hprecisionGeom
  have hpGeom (k) : pDetect k ∈ Set.Icc 0 geom :=
    ⟨(hp k).1, (hp k).2.trans (hrawPrecision.trans hprecisionGeom)⟩
  have hphysicalGeom (k) : physical k ∈ Set.Icc 0 geom := by
    refine ⟨(hphysical k).1, ?_⟩
    have hbase : physicalBound ≤ precision := by
      have hspatial := coefficientErrorSpatialLog_nonneg hphysicalBound0
      dsimp only [precision]
      linarith only [hspatial, hraw0, hearly0]
    exact (hphysical k).2.trans (hbase.trans hprecisionGeom)
  have htargetGeom (k) : target k ∈ Set.Icc 0 geom :=
    ⟨(htarget k).1, (htarget k).2.trans hprecisionGeom⟩
  have hlength (k) : lengths k ∈ Set.Icc 0 geom := by
    have hnonneg (j) : 0 ≤ lengths j :=
      (allocatedAffineLengthLog_bounds m hD.1 hscale.1 (hStage j).2.2.1.1
        (hStage j).2.1.1 (htarget j).1 (by linarith only [(hp j).1])
        (hStage j).2.2.2.2.1).2.2.1
    exact ⟨hnonneg k, (Finset.single_le_sum (fun j _ => hnonneg j)
      (Finset.mem_univ k)).trans hlengthSum.2⟩
  have hmaster (k) : master k ∈ Set.Icc 0 masterBound := by
    change 0 ≤ Bstruct + D + pRadius + Qstride + physical k +
      (u k + model k + pDetect k + rho k + target k + gain k + 32) ∧ _
    constructor
    · have := hB.1; have := hD.1; have := hradius.1; have := hQ.1
      have := (hphysical k).1; have := (hu k).1; have := (hmodel k).1
      have := (hp k).1; have := (hStage k).2.2.1.1; have := (htarget k).1
      have := (hgain k).1; positivity
    · change Bstruct + D + pRadius + Qstride + physical k +
        (u k + model k + pDetect k + rho k + target k + gain k + 32) ≤ 11 * geom + 32
      linarith only [hB.2.trans hPgeom, hD.2, hradius.2, hQ.2.trans hPgeom,
        (hphysicalGeom k).2, (hu k).2.trans hPgeom, (hmodel k).2.trans hPgeom,
        (hpGeom k).2, (hStage k).2.2.1.2, (htargetGeom k).2, (hStage k).1.2]
  have hmasterBound0 : 0 ≤ masterBound := by dsimp [masterBound]; positivity
  have hcoarseBound0 : 0 ≤ coarseBound := by dsimp [coarseBound]; positivity
  have hcoarse : coarse ∈ Set.Icc 0 coarseBound := by
    have hsum : (∑ k, (gain k + 32)) ≤ (nStages : ℝ) * (geom + 32) := by
      calc
        _ ≤ ∑ _k : K, (geom + 32) := Finset.sum_le_sum (fun k _ => by linarith [(hStage k).1.2])
        _ = (Fintype.card K : ℝ) * (geom + 32) := by simp [mul_add]
        _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hCard) (by positivity)
    exact ⟨hCoarse.1.trans (le_max_right _ _), max_le
      (hsum.trans (le_add_of_nonneg_right hP))
      (hCoarse.2.trans (le_add_of_nonneg_left (by positivity)))⟩
  have hspatial0 : 0 ≤ spatial := (spatialPrimitiveEnvelope_bounds hgeom0 hcoarseBound0 (le_refl 0)).1
  have hlateBound0 : 0 ≤ lateBound := by
    have ht : 0 ≤ spatialTupleToleranceLog spatial := by unfold spatialTupleToleranceLog; positivity
    dsimp only [lateBound]; positivity
  have hsumLateBound0 : 0 ≤ sumLateBound := mul_nonneg (Nat.cast_nonneg _) hlateBound0
  have hlocalLate (k) : preparedUniformDegreeDirectLate (master k) scale (physical k) coarse extraLate
      ∈ Set.Icc 0 lateBound := by
    have hsp : spatialPrimitiveEnvelope (physical k) coarse 0 ≤ spatial :=
      spatialPrimitiveEnvelope_mono (hphysicalGeom k).1 hcoarse.1 (le_refl 0)
        (hphysicalGeom k).2 hcoarse.2 (le_refl 0)
    have hsp0 := (spatialPrimitiveEnvelope_bounds (hphysical k).1 hcoarse.1 (le_refl 0)).1
    have ht : spatialTupleToleranceLog (spatialPrimitiveEnvelope (physical k) coarse 0) ≤
        spatialTupleToleranceLog spatial := by unfold spatialTupleToleranceLog; gcongr
    have hxi : 2 * (spatialPrimitiveEnvelope (physical k) coarse 0 +
        spatialTupleToleranceLog (spatialPrimitiveEnvelope (physical k) coarse 0)) + 4 ≤
        2 * (spatial + spatialTupleToleranceLog spatial) + 4 := by linarith
    have hxi0 : 0 ≤ 2 * (spatial + spatialTupleToleranceLog spatial) + 4 := by
      unfold spatialTupleToleranceLog; positivity
    refine ⟨(hmaster k).1.trans (le_max_left _ _), ?_⟩
    unfold preparedUniformDegreeDirectLate
    apply max_le _ (max_le _ (max_le _ (max_le _ _))) <;>
      dsimp only [lateBound] <;>
      linarith only [(hmaster k).2, hscale.2, hcoarse.2, hxi, hExtra.2,
        hmasterBound0, hgeom0, hcoarseBound0, hxi0, hP]
  have hlate : late ∈ Set.Icc 0 sumLateBound := by
    refine ⟨Finset.sum_nonneg (fun k _ => (hlocalLate k).1), ?_⟩
    calc
      _ ≤ ∑ _k : K, lateBound := Finset.sum_le_sum (fun k _ => (hlocalLate k).2)
      _ = (Fintype.card K : ℝ) * lateBound := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hCard) hlateBound0
  have hmasterLate (k) : master k ≤ late :=
    (le_max_left _ _).trans (Finset.single_le_sum (fun j _ => (hlocalLate j).1) (Finset.mem_univ k))
  have hresourceBound0 : 0 ≤ resourceBound := by dsimp [resourceBound]; positivity
  let ev : Polynomial ℕ →+* ℝ := Polynomial.eval₂RingHom (Nat.castRingHom ℝ) P
  have heX : ev X = P := by simp [ev, X]
  have heC (n : ℕ) : ev (Polynomial.C n) = (n : ℝ) := by simp [ev]
  have heRaw : ev rawPoly = raw := by
    simp only [rawPoly, map_add, map_mul, map_ofNat, heX, raw]
  have heEarly : ev earlyPoly = early := by
    simp only [earlyPoly, map_pow, map_add, heRaw, heC, early]
  have hePhysical : ev physicalPoly = physicalBound := by
    simp only [physicalPoly, map_add, map_mul, heC, map_ofNat, heX, heEarly, physicalBound, Nat.cast_add, Nat.cast_ofNat]
  have hePrecision : ev precisionPoly = precision := by
    simp only [precisionPoly, map_add, map_ofNat, heRaw, heEarly, hePhysical,
      map_coefficientErrorSpatialLog, precision]
  have heGeom : ev geomPoly = geom := by
    simp only [geomPoly, map_pow, map_add, hePrecision, heC, geom]
  have heMaster : ev masterPoly = masterBound := by
    simp only [masterPoly, map_add, map_mul, map_ofNat, heGeom, masterBound]
  have heCoarse : ev coarsePoly = coarseBound := by
    simp only [coarsePoly, map_add, map_mul, map_ofNat, heGeom, heC, heX, coarseBound]
  have heSpatial : ev spatialPoly = spatial := by
    simp only [spatialPoly, map_spatialPrimitiveEnvelope, heGeom, heCoarse, map_zero, spatial]
  have heLate : ev latePoly = lateBound := by
    simp only [latePoly, map_add, map_mul, map_ofNat, heMaster, heGeom, heCoarse,
      heSpatial, map_spatialTupleToleranceLog, heX, lateBound]
  have heSumLate : ev sumLatePoly = sumLateBound := by
    simp only [sumLatePoly, map_mul, heC, heLate, sumLateBound]
  have heResource : ev resourcesPoly = resourceBound := by
    simp only [resourcesPoly, map_pow, map_add, heMaster, heSumLate, heC, resourceBound]
  have htotal := hPoly P hP
  change ev (geomPoly + masterPoly + coarsePoly + sumLatePoly + resourcesPoly) ≤ (P + 2) ^ C at htotal
  simp only [map_add, heGeom, heMaster, heCoarse, heSumLate, heResource] at htotal
  have hgeomCap : geom ≤ (P + 2) ^ C := by linarith only [htotal, hmasterBound0, hcoarseBound0, hsumLateBound0, hresourceBound0]
  have hmasterCap : masterBound ≤ (P + 2) ^ C := by linarith only [htotal, hgeom0, hcoarseBound0, hsumLateBound0, hresourceBound0]
  have hcoarseCap : coarseBound ≤ (P + 2) ^ C := by linarith only [htotal, hgeom0, hmasterBound0, hsumLateBound0, hresourceBound0]
  have hlateCap : sumLateBound ≤ (P + 2) ^ C := by linarith only [htotal, hgeom0, hmasterBound0, hcoarseBound0, hresourceBound0]
  have hresourceCap : resourceBound ≤ (P + 2) ^ C := by linarith only [htotal, hgeom0, hmasterBound0, hcoarseBound0, hsumLateBound0]
  have lift {x : ℝ} (hx : x ∈ Set.Icc 0 geom) : x ∈ Set.Icc 0 ((P + 2) ^ C) := ⟨hx.1, hx.2.trans hgeomCap⟩
  refine ⟨lift hradius, lift hD, lift hscale, ⟨hcoarse.1, hcoarse.2.trans hcoarseCap⟩,
    ⟨hlate.1, hlate.2.trans hlateCap⟩, ?_⟩
  intro k
  have hres := hResources (hmaster k).1 (hmasterLate k) (degree k) (hdegree k)
  have hresCap : (master k + late + R) ^ R ≤ (P + 2) ^ C := by
    apply le_trans _ hresourceCap
    apply pow_le_pow_left₀ (by have := (hmaster k).1; have := hlate.1; positivity)
    linarith only [(hmaster k).2, hlate.2]
  exact ⟨lift (hStage k).1, lift (hStage k).2.1, lift (hphysicalGeom k),
    lift (htargetGeom k), lift (hStage k).2.2.1, lift (hStage k).2.2.2.1,
    lift (hlength k), ⟨(hmaster k).1, (hmaster k).2.trans hmasterCap⟩, hres.mono hresCap⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

theorem exists_preparedFiniteScheduleWitnessLate_power_budget
    (m nStages Cmax inputPower : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {K G : Type} [Fintype K] [Fintype G]
        (degree Cdetect : K → ℕ) {nX count : ℕ}
        {B Bstruct pnum Qstride Qσ Pmin Qw requestedCoarse : ℝ}
        (u model : K → ℝ),
        Fintype.card K ≤ nStages → (∀ k, degree k ≤ m) → (∀ k, Cdetect k ≤ Cmax) →
        0 ≤ B → Bstruct ∈ Set.Icc 0 ((B + 2) ^ inputPower) →
        pnum ∈ Set.Icc 0 ((B + 2) ^ inputPower) →
        Qstride ∈ Set.Icc 0 ((B + 2) ^ inputPower) →
        Qσ ∈ Set.Icc 0 ((B + 2) ^ inputPower) →
        Pmin ∈ Set.Icc 0 ((B + 2) ^ inputPower) →
        Qw ∈ Set.Icc 0 ((B + 2) ^ inputPower) →
        requestedCoarse ∈ Set.Icc 0 ((B + 2) ^ inputPower) →
        (∀ k, u k ∈ Set.Icc 0 ((B + 2) ^ inputPower)) →
        (∀ k, model k ∈ Set.Icc 0 ((B + 2) ^ inputPower)) →
        (count : ℝ) ≤ (B + 2) ^ inputPower →
        (nX : ℝ) ≤ (B + 2) ^ inputPower →
        (Fintype.card G : ℝ) ≤ (B + 2) ^ inputPower →
        PreparedFiniteScheduleWitnessBudget (G := G) m degree Cdetect nX count
          Bstruct pnum Qstride Qσ Pmin Qw requestedCoarse u model ((B + 2) ^ C) := by
  obtain ⟨D0, _, hlocal⟩ := exists_preparedEmptyLayerLocalSchedule_budget m nStages Cmax
  let T : Polynomial ℕ := (Polynomial.X + 2) ^ inputPower
  obtain ⟨A, _, hfirstBound⟩ := exists_natPolynomial_fixed_power_budget
    (T + (T + 2) ^ D0)
  obtain ⟨W, _, hwitness⟩ := exists_preparedFiniteScheduleWitnessScalar_power_budget nStages A
  let nextPower := A + W
  let Final : Polynomial ℕ :=
    (Polynomial.X + 2) ^ W + ((Polynomial.X + 2) ^ nextPower + 2) ^ D0
  obtain ⟨C, hC, hfinalBound⟩ := exists_natPolynomial_fixed_power_budget Final
  refine ⟨C, hC, ?_⟩
  intro K G _ _ degree Cdetect nX count B Bstruct pnum Qstride Qσ Pmin Qw requestedCoarse
    u model hcard hdegree hdetect hB hstruct hnum hstride hσ hmin hQw hrequested
    hu hmodel hcount hnX hG
  let t : ℝ := (B + 2) ^ inputPower
  let first : ℝ := (t + 2) ^ D0
  let early : ℝ := (B + 2) ^ A
  let witnessCap : ℝ := (B + 2) ^ W
  let next : ℝ := (B + 2) ^ nextPower
  have ht : 0 ≤ t := by dsimp only [t]; positivity
  have hfirst0 : 0 ≤ first := by dsimp only [first]; positivity
  have hearly0 : 0 ≤ early := by dsimp only [early]; positivity
  have hwitness0 : 0 ≤ witnessCap := by dsimp only [witnessCap]; positivity
  have hnext0 : 0 ≤ next := by dsimp only [next]; positivity
  have hfirstSum : t + first ≤ early := by
    simpa [T, t, first, early, Polynomial.eval₂_pow] using hfirstBound B hB
  have htEarly : t ≤ early := by linarith only [hfirstSum, hfirst0]
  have hfirstEarly : first ≤ early := by linarith only [hfirstSum, ht]
  have liftEarly {x : ℝ} (hx : x ∈ Set.Icc 0 t) : x ∈ Set.Icc 0 early :=
    ⟨hx.1, hx.2.trans htEarly⟩
  have hinitial := hlocal (G := G) degree Cdetect u model hcard hdegree hdetect ht
    hstruct hnum hstride hσ hrequested (show (0 : ℝ) ∈ Set.Icc 0 t from ⟨le_rfl, ht⟩)
    hu hmodel hcount hnX hG
  let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
  let D := allocatedComparisonDimension m pnum
  let pDetect := fun k => allocatedModelTestLog (u k) (model k)
  let aDetect := fun k => 2 * u k + 4 * model k + 7
  let gain := fun k => slicedDetectionGainLog (degree k) (Cdetect k) count
    (pDetect k) (pDetect k) (aDetect k)
  let Pk := fun k => scalarKernelLogarithmicBudget (Fin (degree k + 1)) G
    (gain k + pDetect k + 4)
  let physical := fun k => preparedFiniteScheduleLocalPhysical m nX count Qstride (Pk k)
  let target := fun k => gain k + 40 + coefficientErrorSpatialLog (physical k)
  let E := fun k => target k + D * ((m * 2 ^ (m + 1) : ℕ) * Pk k) + 5
  let rho := fun k => 2 * affineProfileInputEnvelope D
    (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E k) (pDetect k + 2) + 2
  let tail := fun k => affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
    (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E k) (pDetect k + 2)
  let scale := preparedUniformDegreeScaleLog (D + pRadius) tail Qσ
  let tmod := fun k => ((m + 1 : ℕ) : ℝ) * Pk k + nX * Qstride
  let lengths := fun k => allocatedAffineLengthLog m D scale (rho k) (Pk k)
    (target k) (pDetect k + 2) (tmod k)
  let seed := allocatedScaleLog (scale + ∑ k, lengths k + Pmin + 1)
  have hscale : scale ∈ Set.Icc 0 first := hinitial.2.2.1
  have hlength (k : K) : lengths k ∈ Set.Icc 0 first := by
    obtain ⟨_, _, _, _, _, _, hl, _, _⟩ := hinitial.2.2.2.2.2 k
    exact hl
  have hseedWitness := hwitness (Pscale := scale) lengths hcard hB
    ⟨hscale.1, hscale.2.trans hfirstEarly⟩ (liftEarly hmin) (liftEarly hQw)
    (fun k => ⟨(hlength k).1, (hlength k).2.trans hfirstEarly⟩)
  change seed ∈ Set.Icc 0 witnessCap ∧
    allocatedWitnessScaleLog seed Qw ∈ Set.Icc 0 witnessCap at hseedWitness
  have hearlyNext : early ≤ next :=
    pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ B + 2) (Nat.le_add_right A W)
  have hwitnessNext : witnessCap ≤ next :=
    pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ B + 2) (Nat.le_add_left W A)
  have htNext : t ≤ next := htEarly.trans hearlyNext
  have liftNext {x : ℝ} (hx : x ∈ Set.Icc 0 t) : x ∈ Set.Icc 0 next :=
    ⟨hx.1, hx.2.trans htNext⟩
  have hactual := hlocal (G := G) degree Cdetect u model hcard hdegree hdetect hnext0
    (liftNext hstruct) (liftNext hnum) (liftNext hstride) (liftNext hσ)
    (liftNext hrequested) ⟨hseedWitness.2.1, hseedWitness.2.2.trans hwitnessNext⟩
    (fun k => liftNext (hu k)) (fun k => liftNext (hmodel k))
    (hcount.trans htNext) (hnX.trans htNext) (hG.trans htNext)
  have hfinalSum : witnessCap + (next + 2) ^ D0 ≤ (B + 2) ^ C := by
    simpa [Final, witnessCap, next, Polynomial.eval₂_pow] using hfinalBound B hB
  have hnextPower0 : 0 ≤ (next + 2) ^ D0 := by positivity
  have hwitnessFinal : witnessCap ≤ (B + 2) ^ C := by
    linarith only [hfinalSum, hnextPower0]
  have hactualFinal : (next + 2) ^ D0 ≤ (B + 2) ^ C := by
    linarith only [hfinalSum, hwitness0]
  change seed ∈ Set.Icc 0 ((B + 2) ^ C) ∧
    allocatedWitnessScaleLog seed Qw ∈ Set.Icc 0 ((B + 2) ^ C) ∧ _
  exact ⟨⟨hseedWitness.1.1, hseedWitness.1.2.trans hwitnessFinal⟩,
    ⟨hseedWitness.2.1, hseedWitness.2.2.trans hwitnessFinal⟩, hactual.mono hactualFinal⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

theorem exists_preparedFiniteNestedSourceLate_power_budget
    (m cutoff A Cdirect outerDepth innerDepth inputPower : ℕ)
    (constants : ℕ → ℕ) (hA : 2 ≤ A) (hcutoff : cutoff ≤ m) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (G : Type) [Fintype G] (count nX : ℕ)
      {Bstruct pnum Qstride gainLog stageLog Vlog Qσ Pmin requestedCoarse : ℝ},
      0 ≤ Bstruct → pnum ∈ Set.Icc 0 Bstruct → Qstride ∈ Set.Icc 0 Bstruct →
      gainLog ∈ Set.Icc 0 Bstruct → stageLog ∈ Set.Icc 0 Bstruct →
      (count : ℝ) ≤ Bstruct → (nX : ℝ) ≤ Bstruct → (Fintype.card G : ℝ) ≤ Bstruct →
      Vlog ∈ Set.Icc 0 ((Bstruct + 2) ^ inputPower) →
      Qσ ∈ Set.Icc 0 ((Bstruct + 2) ^ inputPower) →
      Pmin ∈ Set.Icc 0 ((Bstruct + 2) ^ inputPower) →
      requestedCoarse ∈ Set.Icc 0 ((Bstruct + 2) ^ inputPower) →
      let K := PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff
      let degree : K → ℕ := preparedFiniteNestedForwardAllDegreeDegree
      let Cdetect := fun k : K => sampledSupportedSlicedDetectionConstant (degree k)
        (preparedFiniteForwardDetectorPolynomial cutoff)
      let u := fun k : K => preparedFiniteForwardPairedSourcePrecision A Cdirect constants
        (preparedFiniteNestedForwardAllDegreeStage k).val (preparedFiniteNestedForwardAllDegreeIsDirect k)
        (preparedFiniteNestedForwardAllDegreeSeed A constants Bstruct k) gainLog stageLog
      let model := fun k : K => preparedFiniteForwardWork A constants
        (preparedFiniteNestedForwardAllDegreeStage k).val
        (preparedFiniteNestedForwardAllDegreeSeed A constants Bstruct k)
      let Qw := 2 * Bstruct + 2 * Vlog + 5 * (gainLog + 8) + 24
      PreparedFiniteScheduleWitnessBudget (G := G) m degree Cdetect nX count
        Bstruct pnum Qstride Qσ Pmin Qw requestedCoarse u model ((Bstruct + 2) ^ C) := by
  let K := PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff
  let Cmax := ∑ d : Fin (m + 1), sampledSupportedSlicedDetectionConstant d.val
    (preparedFiniteForwardDetectorPolynomial cutoff)
  obtain ⟨Clocal, _, hlocal⟩ :=
    exists_candidateNestedForwardLocal_budget A Cdirect constants innerDepth outerDepth hA
  let inputPoly : Polynomial ℕ := 8 * Polynomial.X + (Polynomial.X + 2) ^ Clocal +
    3 * (Polynomial.X + 2) ^ inputPower + 64
  obtain ⟨Cin, _, hinput⟩ := exists_natPolynomial_fixed_power_budget inputPoly
  obtain ⟨C, hC, hcore⟩ := exists_preparedFiniteScheduleWitnessLate_power_budget
    m (Fintype.card K) Cmax Cin
  refine ⟨C, hC, ?_⟩
  intro G _ count nX Bstruct pnum Qstride gainLog stageLog Vlog Qσ Pmin requestedCoarse
    hB hnum hstride hg hs hcount hnX hG hV hQσ hPmin hcoarse K' degree Cdetect u model Qw
  let localBound := (Bstruct + 2) ^ Clocal
  let primitiveBound := (Bstruct + 2) ^ inputPower
  let inputBound := (Bstruct + 2) ^ Cin
  have hl0 : 0 ≤ localBound := by dsimp only [localBound]; positivity
  have hp0 : 0 ≤ primitiveBound := by dsimp only [primitiveBound]; positivity
  have hbound : 8 * Bstruct + localBound + 3 * primitiveBound + 64 ≤ inputBound := by
    simpa [inputPoly, localBound, primitiveBound, inputBound, Polynomial.eval₂_pow] using hinput Bstruct hB
  have hBinput : Bstruct ≤ inputBound := by linarith only [hbound, hB, hl0, hp0]
  have hlocalInput : localBound ≤ inputBound := by linarith only [hbound, hB, hp0]
  have hprimitiveInput : primitiveBound ≤ inputBound := by linarith only [hbound, hB, hl0, hp0]
  have liftBase {x : ℝ} (hx : x ∈ Set.Icc 0 Bstruct) : x ∈ Set.Icc 0 inputBound :=
    ⟨hx.1, hx.2.trans hBinput⟩
  have liftPrimitive {x : ℝ} (hx : x ∈ Set.Icc 0 primitiveBound) : x ∈ Set.Icc 0 inputBound :=
    ⟨hx.1, hx.2.trans hprimitiveInput⟩
  have hQw : Qw ∈ Set.Icc 0 inputBound := by
    constructor
    · dsimp only [Qw]; have := hV.1; have := hg.1; positivity
    · dsimp only [Qw]
      linarith only [hbound, hV.2, hg.2, hB, hl0, hp0]
  have hstage (k : K') := hlocal hB hg hs k.1.val (Nat.le_of_lt_succ k.1.isLt)
    k.2.1.val (Nat.le_of_lt_succ k.2.1.isLt)
  have hu (k : K') : u k ∈ Set.Icc 0 inputBound := by
    have h := (hstage k).2.2.2.2.2 (preparedFiniteNestedForwardAllDegreeIsDirect k)
    exact ⟨h.1, h.2.trans hlocalInput⟩
  have hmodel (k : K') : model k ∈ Set.Icc 0 inputBound := by
    have h := (hstage k).2.2.1
    exact ⟨h.1, h.2.trans hlocalInput⟩
  have hdegree (k : K') : degree k ≤ m :=
    preparedFiniteNestedForwardAllDegreeDegree_le hcutoff k
  have hCdetect (k : K') : Cdetect k ≤ Cmax := by
    let d : Fin (m + 1) := ⟨degree k, Nat.lt_succ_of_le (hdegree k)⟩
    exact Finset.single_le_sum
      (f := fun d : Fin (m + 1) => sampledSupportedSlicedDetectionConstant d.val
        (preparedFiniteForwardDetectorPolynomial cutoff))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ d)
  exact hcore (G := G) degree Cdetect u model le_rfl hdegree hCdetect hB
    ⟨hB, hBinput⟩ (liftBase hnum) (liftBase hstride) (liftPrimitive hQσ)
    (liftPrimitive hPmin) hQw (liftPrimitive hcoarse) hu hmodel
    (hcount.trans hBinput) (hnX.trans hBinput) (hG.trans hBinput)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.PreparedFiniteNestedSourceProjectionBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem exists_preparedFiniteForwardFrontProjectionPrecision_budget (Cnative : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {t u p native : ℝ}, 0 ≤ t →
      u ∈ Set.Icc 0 t → p ∈ Set.Icc 0 t →
      native ∈ Set.Icc 0 ((t + Cnative) ^ Cnative) →
      preparedFiniteForwardFrontProjectionPrecision u p native ∈ Set.Icc 0 ((t + C) ^ C) := by
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C Cnative) ^ Cnative +
    9 * Polynomial.X + 55
  obtain ⟨C, hC, hpoly⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro t u p native ht hu hp hn
  let v : ℝ := (t + Cnative) ^ Cnative
  have hv : 0 ≤ v := by dsimp only [v]; positivity
  have hcommon : max native 3 ≤ v + 3 :=
    max_le (by linarith only [hn.2]) (by linarith only [hv])
  have hmax : max (max native 3) (2 * u + 4 * p + 20) ≤ v + 6 * t + 23 :=
    max_le (by linarith only [hcommon, ht]) (by linarith only [hu.2, hp.2, hv])
  have hbudget : v + 9 * t + 55 ≤ (t + C) ^ C := by
    simpa [Q, v, Polynomial.eval₂_pow] using hpoly t ht
  refine ⟨preparedFiniteForwardFrontProjectionPrecision_nonneg hu.1 hp.1, ?_⟩
  unfold preparedFiniteForwardFrontProjectionPrecision
  linarith only [hmax, hu.2, hp.2, hbudget]

theorem exists_preparedFiniteForwardFrontProjection_budget (Cnative : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (A Cdirect : ℕ) (stageCountConstant : ℕ → ℕ) (n : ℕ)
      {x gainLog stageLog native : ℝ}, 0 ≤ x →
      gainLog ∈ Set.Icc 0 x → stageLog ∈ Set.Icc 0 x →
      let u := preparedFiniteForwardModelPrecision A stageCountConstant n x gainLog stageLog
      let p := preparedFiniteForwardWork A stageCountConstant n x
      let t := preparedFiniteForwardPairedSourcePrecision A Cdirect stageCountConstant n false
        x gainLog stageLog + p
      native ∈ Set.Icc 0 ((t + Cnative) ^ Cnative) →
      preparedFiniteForwardFrontProjectionPrecision u p native ∈ Set.Icc 0 ((t + C) ^ C) := by
  obtain ⟨C, hC, hbound⟩ := exists_preparedFiniteForwardFrontProjectionPrecision_budget Cnative
  refine ⟨C, hC, ?_⟩
  intro A Cdirect stageCountConstant n x gainLog stageLog native hx hg hs u p t hn
  have hprecision := preparedFiniteForward_model_precision_bounds A stageCountConstant n hx hg hs
  have hu : 0 ≤ u := hprecision.1
  have hp : 0 ≤ p := preparedFiniteForwardWork_nonneg A stageCountConstant n hx
  have htEq : t = u + 3 * p + 1 := by
    dsimp only [t]
    rw [preparedFiniteForwardPairedSourcePrecision_model]
    have heq : preparedFiniteForwardSourcePrecision A stageCountConstant n x gainLog stageLog =
        u + 2 * p + 1 := hprecision.2.2.1
    rw [heq]
    ring
  have ht : 0 ≤ t := by linarith only [htEq, hu, hp]
  exact hbound ht ⟨hu, by linarith only [htEq, hp]⟩
    ⟨hp, by linarith only [htEq, hu, hp]⟩ hn

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem exists_preparedFiniteScheduleConditionalExcess_power_budget (m inputPower : ℕ) :
    ∃ extraPower : ℕ, 2 ≤ extraPower ∧
      ∀ {p Plate E : ℝ}, 2 ≤ p → 0 ≤ Plate →
      Plate ≤ (p + 2) ^ inputPower → E ≤ (p + 2) ^ inputPower →
      preparedConditionalExcessRequired m Plate E ≤ (p + 2) ^ extraPower := by
  let A := allocatedExternalConditionalExcessExponent m
  let U : Polynomial ℕ := (Polynomial.X + 2) ^ inputPower
  let Q : Polynomial ℕ := (4 * (U + 8) ^ 2 + U + Polynomial.C A) ^ A
  obtain ⟨extraPower, hpower, hQ⟩ := exists_natPolynomial_fixed_power_budget Q
  refine ⟨extraPower, hpower, ?_⟩
  intro p Plate E hp hPlate0 hPlate hE
  let u := (p + 2) ^ inputPower
  have hu : 0 ≤ u := by dsimp only [u]; positivity
  have hproj : 4 * (Plate + 8) ^ 2 ≤ 4 * (u + 8) ^ 2 := by
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by linarith : 0 ≤ Plate + 8)
        (add_le_add hPlate le_rfl) 2) (by norm_num)
  have hmax : max (4 * (Plate + 8) ^ 2) E ≤ 4 * (u + 8) ^ 2 + u := by
    exact max_le (hproj.trans (le_add_of_nonneg_right hu))
      (hE.trans (le_add_of_nonneg_left (by positivity)))
  have hbound : preparedConditionalExcessRequired m Plate E ≤
      (4 * (u + 8) ^ 2 + u + A) ^ A := by
    apply pow_le_pow_left₀
      (add_nonneg ((by positivity : 0 ≤ 4 * (Plate + 8) ^ 2).trans
        (le_max_left _ _)) (Nat.cast_nonneg A))
    exact add_le_add hmax le_rfl
  apply hbound.trans
  simpa [Q, U, u, Polynomial.eval₂_pow] using hQ p (by linarith : 0 ≤ p)

theorem exists_preparedFiniteScheduleUniformConditionalExcess_power_budget
    (s inputPower : ℕ) :
    ∃ extraPower : ℕ, 2 ≤ extraPower ∧
      ∀ m : ℕ, m ≤ s →
      ∀ {p Plate E : ℝ}, 2 ≤ p → 0 ≤ Plate →
      Plate ≤ (p + 2) ^ inputPower → E ≤ (p + 2) ^ inputPower →
      preparedConditionalExcessRequired m Plate E ≤ (p + 2) ^ extraPower := by
  let exponent (m : ℕ) :=
    (exists_preparedFiniteScheduleConditionalExcess_power_budget m inputPower).choose
  let extraPower := 2 + ∑ j ∈ Finset.range (s + 1), exponent j
  refine ⟨extraPower, by dsimp only [extraPower]; omega, ?_⟩
  intro m hm p Plate E hp hPlate0 hPlate hE
  have hexponent : exponent m ≤ extraPower := by
    have hsum : exponent m ≤ ∑ j ∈ Finset.range (s + 1), exponent j :=
      Finset.single_le_sum (f := exponent) (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))
    dsimp only [extraPower]
    omega
  have hlocal := (exists_preparedFiniteScheduleConditionalExcess_power_budget
    m inputPower).choose_spec.2 hp hPlate0 hPlate hE
  change preparedConditionalExcessRequired m Plate E ≤ (p + 2) ^ exponent m at hlocal
  exact hlocal.trans (pow_le_pow_right₀ (by linarith : 1 ≤ p + 2) hexponent)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem exists_preparedNestedFrontProjectionEnvelope_budget
    (A Cdirect Cnative : ℕ) (constants : ℕ → ℕ)
    (innerDepth outerDepth cardBound inputPower maxLayers : ℕ) (hA : 2 ≤ A) :
    ∃ projectionPower requiredPower : ℕ, 2 ≤ projectionPower ∧ 2 ≤ requiredPower ∧
      ∀ {K : Type*} [Fintype K] (outer inner : K → ℕ) (native : K → ℝ),
      Fintype.card K ≤ cardBound → (∀ k, outer k ≤ outerDepth) →
      (∀ k, inner k ≤ innerDepth) →
      ∀ {x gainLog stageLog endpoint Plate : ℝ}, 2 ≤ x →
      gainLog ∈ Set.Icc 0 x → stageLog ∈ Set.Icc 0 x →
      endpoint ∈ Set.Icc 0 ((x + 2) ^ inputPower) →
      Plate ∈ Set.Icc 0 ((x + 2) ^ inputPower) →
      (∀ k, native k ∈ Set.Icc 0
        ((preparedFiniteForwardPairedSourcePrecision A Cdirect constants (inner k) false
          (candidateNestedForwardSeed A constants innerDepth (outer k) x) gainLog stageLog +
          preparedFiniteForwardWork A constants (inner k)
            (candidateNestedForwardSeed A constants innerDepth (outer k) x) + Cnative) ^ Cnative)) →
      let E := preparedNestedFrontProjectionEnvelope A constants innerDepth
        outer inner native x gainLog stageLog endpoint
      E ∈ Set.Icc 0 ((x + 2) ^ projectionPower) ∧ endpoint ≤ E ∧
      (∀ k, preparedFiniteForwardFrontProjectionPrecision
        (preparedFiniteForwardModelPrecision A constants (inner k)
          (candidateNestedForwardSeed A constants innerDepth (outer k) x) gainLog stageLog)
        (preparedFiniteForwardWork A constants (inner k)
          (candidateNestedForwardSeed A constants innerDepth (outer k) x)) (native k) ≤ E) ∧
      ∀ m ≤ maxLayers,
        preparedConditionalExcessRequired m Plate E ≤ (x + 2) ^ requiredPower := by
  obtain ⟨D, _, hlocal⟩ := exists_candidateNestedForwardLocal_budget
    A Cdirect constants innerDepth outerDepth hA
  obtain ⟨C, _, hfront⟩ := exists_preparedFiniteForwardFrontProjection_budget Cnative
  let B : Polynomial ℕ := (Polynomial.X + 2) ^ D
  let Q : Polynomial ℕ := (Polynomial.X + 2) ^ inputPower + 1 +
    Polynomial.C cardBound * (2 * B + Polynomial.C C) ^ C
  obtain ⟨projectionPower, hpPower, hQ⟩ := exists_natPolynomial_fixed_power_budget Q
  obtain ⟨requiredPower, hrPower, hrequired⟩ :=
    exists_preparedFiniteScheduleUniformConditionalExcess_power_budget
      maxLayers (max inputPower projectionPower)
  refine ⟨projectionPower, requiredPower, hpPower, hrPower, ?_⟩
  intro K _ outer inner native hcard houter hinner x gainLog stageLog endpoint Plate
    hx hg hs hend hPlate hn E
  have hx0 : 0 ≤ x := (by norm_num : (0 : ℝ) ≤ 2).trans hx
  let bound : ℝ := (x + 2) ^ D
  have hb0 : 0 ≤ bound := by dsimp only [bound]; positivity
  let entry := fun k => preparedFiniteForwardFrontProjectionPrecision
    (preparedFiniteForwardModelPrecision A constants (inner k)
      (candidateNestedForwardSeed A constants innerDepth (outer k) x) gainLog stageLog)
    (preparedFiniteForwardWork A constants (inner k)
      (candidateNestedForwardSeed A constants innerDepth (outer k) x)) (native k)
  have hentry : ∀ k, entry k ∈ Set.Icc 0 ((2 * bound + C) ^ C) := by
    intro k
    let seed := candidateNestedForwardSeed A constants innerDepth (outer k) x
    have hseed : 0 ≤ seed := candidateNestedForwardSeed_nonneg A constants innerDepth (outer k) hx0
    have hxs : x ≤ seed := le_candidateNestedForwardSeed A constants innerDepth (outer k) hA hx0
    have hloc := hlocal hx0 hg hs (outer k) (houter k) (inner k) (hinner k)
    have hf := hfront A Cdirect constants (inner k) hseed
      ⟨hg.1, hg.2.trans hxs⟩ ⟨hs.1, hs.2.trans hxs⟩ (hn k)
    refine ⟨hf.1, hf.2.trans ?_⟩
    have hsource := hloc.2.2.2.2.2 false
    have hwork := hloc.2.2.1
    apply pow_le_pow_left₀
      (add_nonneg (add_nonneg hsource.1 hwork.1) (Nat.cast_nonneg C))
    dsimp only [bound] at hsource hwork ⊢
    linarith only [hsource.2, hwork.2]
  have hsum0 : 0 ≤ ∑ k, entry k := Finset.sum_nonneg (fun k _ => (hentry k).1)
  have hE0 : 0 ≤ E := by
    change 0 ≤ endpoint + 1 + ∑ k, entry k
    linarith only [hend.1, hsum0]
  have hsum : ∑ k, entry k ≤ (cardBound : ℝ) * (2 * bound + C) ^ C := by
    calc
      ∑ k, entry k ≤ ∑ _k : K, (2 * bound + C) ^ C :=
        Finset.sum_le_sum (fun k _ => (hentry k).2)
      _ = (Fintype.card K : ℝ) * (2 * bound + C) ^ C := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) (by positivity)
  have hE : E ≤ (x + 2) ^ projectionPower := by
    have htotal : (x + 2) ^ inputPower + 1 +
        (cardBound : ℝ) * (2 * bound + C) ^ C ≤ (x + 2) ^ projectionPower := by
      simpa [Q, B, bound, Polynomial.eval₂_pow] using hQ x hx0
    change endpoint + 1 + ∑ k, entry k ≤ _
    linarith only [hend.2, hsum, htotal]
  refine ⟨⟨hE0, hE⟩, ?_, ?_, ?_⟩
  · change endpoint ≤ endpoint + 1 + ∑ k, entry k
    linarith only [hsum0]
  · intro k
    have hk : entry k ≤ ∑ j, entry j :=
      Finset.single_le_sum (fun j _ => (hentry j).1) (Finset.mem_univ k)
    change entry k ≤ endpoint + 1 + ∑ j, entry j
    linarith only [hk, hend.1]
  · intro m hm
    exact hrequired m hm hx hPlate.1
      (hPlate.2.trans (pow_le_pow_right₀ (by linarith : 1 ≤ x + 2) (Nat.le_max_left _ _)))
      (hE.trans (pow_le_pow_right₀ (by linarith : 1 ≤ x + 2) (Nat.le_max_right _ _)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem exists_preparedFiniteNestedSourceProjection_budget
    (m cutoff A Cdirect outerDepth innerDepth inputPower : ℕ)
    (constants : ℕ → ℕ)
    (hA : 2 ≤ A) (hcutoff : cutoff ≤ m) :
    ∃ projectionPower requiredPower : ℕ, 2 ≤ projectionPower ∧ 2 ≤ requiredPower ∧
    ∀ (G : Type) [Fintype G] (count nX : ℕ)
      {Bstruct pnum Qstride gainLog stageLog Plate endpoint : ℝ},
      2 ≤ Bstruct → pnum ∈ Set.Icc 0 Bstruct → Qstride ∈ Set.Icc 0 Bstruct →
      gainLog ∈ Set.Icc 0 Bstruct → stageLog ∈ Set.Icc 0 Bstruct →
      (count : ℝ) ≤ Bstruct → (nX : ℝ) ≤ Bstruct → (Fintype.card G : ℝ) ≤ Bstruct →
      endpoint ∈ Set.Icc 0 ((Bstruct + 2) ^ inputPower) →
      Plate ∈ Set.Icc 0 ((Bstruct + 2) ^ inputPower) →
      let E := preparedFiniteNestedSourceProjectionPrecision
        (outerDepth := outerDepth) (innerDepth := innerDepth) (cutoff := cutoff)
        m G count nX A Cdirect constants Bstruct pnum Qstride gainLog stageLog Plate endpoint
      E ∈ Set.Icc 0 ((Bstruct + 2) ^ projectionPower) ∧ endpoint ≤ E ∧
        preparedConditionalExcessRequired m Plate E ≤ (Bstruct + 2) ^ requiredPower := by
  let K := PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff
  let Cnative := preparedFiniteNestedSourceNativeExponent m cutoff Cdirect
  obtain ⟨Cp, Cr, hCp, hCr, hbudget⟩ := exists_preparedNestedFrontProjectionEnvelope_budget
    A Cdirect Cnative constants innerDepth outerDepth (Fintype.card K) inputPower m hA
  refine ⟨Cp, Cr, hCp, hCr, ?_⟩
  intro G _ count nX Bstruct pnum Qstride gainLog stageLog Plate endpoint
    hB hnum hstride hg hs hcount hnX hG hend hPlate E
  let native : K → ℝ := preparedFiniteNestedSourceNative m G count nX
    (preparedFiniteForwardDetectorPolynomial cutoff) A Cdirect constants
    Bstruct pnum Qstride gainLog stageLog Plate
  have hnative (k : K) := preparedFiniteNestedSourceNative_budget m G count nX A Cdirect constants
    hcutoff hA ((by norm_num : (0 : ℝ) ≤ 2).trans hB) hnum hstride hg hs hcount hnX hG Plate k
  have h := hbudget (fun k : K => k.1.val) (fun k : K => k.2.1.val) native le_rfl
    (fun k => Nat.le_of_lt_succ k.1.isLt) (fun k => Nat.le_of_lt_succ k.2.1.isLt)
    hB hg hs hend hPlate (fun k => by
      simpa only [native, Cnative, preparedFiniteNestedForwardAllDegreeStage,
        preparedFiniteNestedForwardAllDegreeSeed, preparedFiniteNestedForwardAllDegreeOuter,
        preparedFiniteForwardPairedSourcePrecision_model] using hnative k)
  exact ⟨h.1, h.2.1, h.2.2.2 m le_rfl⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteNestedAnchorRequiredPower
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem exists_preparedFiniteNestedAnchorRequired_power_budget (q inputPower : ℕ) :
    ∃ outputPower : ℕ, 2 ≤ outputPower ∧ ∀ {B : ℝ}, 2 ≤ B →
      ∀ (M nX : ℕ) {pRadius Pscale Pseed Qw gainLog Vlog Pmaster Plate Econditional : ℝ},
      (M : ℝ) ≤ (B + 2) ^ inputPower →
      (nX : ℝ) ≤ (B + 2) ^ inputPower →
      pRadius ∈ Set.Icc 0 ((B + 2) ^ inputPower) →
      Pscale ∈ Set.Icc 0 ((B + 2) ^ inputPower) →
      Pseed ∈ Set.Icc 0 ((B + 2) ^ inputPower) →
      Qw ∈ Set.Icc 0 ((B + 2) ^ inputPower) →
      gainLog ∈ Set.Icc 0 ((B + 2) ^ inputPower) →
      Vlog ∈ Set.Icc 0 ((B + 2) ^ inputPower) →
      Econditional ∈ Set.Icc 0 ((B + 2) ^ inputPower) →
      0 ≤ Pmaster → Pmaster ≤ Plate → Plate ≤ (B + 2) ^ inputPower →
      let baseB0 := preparedUniformDegreeProductiveCertificateBudget
        M nX pRadius Pscale Pseed Qw (gainLog + 8) Vlog
      let Pwidth := 4 * (Plate + 8) ^ 2
      let Bcert := preparedForecastGoodCertificateBudget baseB0 B Pwidth gainLog Vlog
      let Pgood := preparedForecastGoodAnalyticBudget (preparedCenteredShortForecastSpatialExponent q)
        baseB0 B Pwidth gainLog Vlog
      preparedFiniteScheduleAnchorGoodRequired q Pmaster Plate Econditional Bcert Pgood Pwidth ≤
        (B + 2) ^ outputPower := by
  let envelope : Polynomial ℕ := Polynomial.X + 9 + 8 * (Polynomial.X + 2) ^ inputPower
  obtain ⟨inflatedPower, _, hEnvelope⟩ := exists_natPolynomial_fixed_power_budget envelope
  obtain ⟨outputPower, houtputPower, hRequired⟩ :=
    exists_preparedShortForecastConstructedRequired_power_budget q inflatedPower
  refine ⟨outputPower, houtputPower, ?_⟩
  intro B hB M nX pRadius Pscale Pseed Qw gainLog Vlog Pmaster Plate Econditional
    hM hnX hRadius hScale hSeed hQw hGain hV hE hMaster hLate hPlate
    baseB0 Pwidth Bcert Pgood
  let inputBound := (B + 2) ^ inputPower
  have hB0 : 0 ≤ B := (by norm_num : (0 : ℝ) ≤ 2).trans hB
  have hInput0 : 0 ≤ inputBound := pow_nonneg (by linarith only [hB0]) _
  have hEnvelopeReal : B + 9 + 8 * inputBound ≤ (B + 2) ^ inflatedPower := by
    simpa [envelope, inputBound, Polynomial.eval₂_pow] using hEnvelope B hB0
  have hInflated : inputBound ≤ (B + 2) ^ inflatedPower :=
    (by linarith only [hB0, hInput0] : inputBound ≤ B + 9 + 8 * inputBound).trans
      hEnvelopeReal
  have hChart : B ≤ (B + 2) ^ inflatedPower :=
    (by linarith only [hInput0] : B ≤ B + 9 + 8 * inputBound).trans hEnvelopeReal
  have hBase0 : 0 ≤ baseB0 := by
    dsimp only [baseB0, preparedUniformDegreeProductiveCertificateBudget]
    have := hRadius.1
    have := hScale.1
    have := hSeed.1
    have := hQw.1
    have := hGain.1
    have := hV.1
    positivity
  have hBase : baseB0 ≤ (B + 2) ^ inflatedPower := by
    apply le_trans _ hEnvelopeReal
    dsimp only [baseB0, preparedUniformDegreeProductiveCertificateBudget]
    change 1 + (M : ℝ) + nX + pRadius + Pscale + Pseed + Qw + (gainLog + 8) + Vlog ≤
      B + 9 + 8 * inputBound
    linarith only [hB0, hM, hnX, hRadius.2, hScale.2, hSeed.2, hQw.2, hGain.2, hV.2]
  exact hRequired B hB Pmaster Plate Econditional baseB0 B gainLog Vlog
    hMaster hLate (hPlate.trans hInflated)
    ⟨hE.1, hE.2.trans hInflated⟩ ⟨hBase0, hBase⟩ ⟨hB0, hChart⟩
    ⟨hGain.1, hGain.2.trans hInflated⟩ ⟨hV.1, hV.2.trans hInflated⟩

theorem exists_preparedFiniteNestedAnchorScalars_power_budget (q inputPower : ℕ) :
    ∃ outputPower : ℕ, 2 ≤ outputPower ∧ ∀ {B : ℝ}, 2 ≤ B →
      ∀ (M nX : ℕ) {pRadius Pscale Pseed Qw gainLog Vlog Pmaster Plate Econditional : ℝ},
      (M : ℝ) ≤ (B + 2) ^ inputPower →
      (nX : ℝ) ≤ (B + 2) ^ inputPower →
      pRadius ∈ Set.Icc 0 ((B + 2) ^ inputPower) →
      Pscale ∈ Set.Icc 0 ((B + 2) ^ inputPower) →
      Pseed ∈ Set.Icc 0 ((B + 2) ^ inputPower) →
      Qw ∈ Set.Icc 0 ((B + 2) ^ inputPower) →
      gainLog ∈ Set.Icc 0 ((B + 2) ^ inputPower) →
      Vlog ∈ Set.Icc 0 ((B + 2) ^ inputPower) →
      Econditional ∈ Set.Icc 0 ((B + 2) ^ inputPower) →
      0 ≤ Pmaster → Pmaster ≤ Plate → Plate ≤ (B + 2) ^ inputPower →
      let baseB0 := preparedUniformDegreeProductiveCertificateBudget
        M nX pRadius Pscale Pseed Qw (gainLog + 8) Vlog
      let Pwidth := 4 * (Plate + 8) ^ 2
      let Bcert := preparedForecastGoodCertificateBudget baseB0 B Pwidth gainLog Vlog
      let Pgood := preparedForecastGoodAnalyticBudget (preparedCenteredShortForecastSpatialExponent q)
        baseB0 B Pwidth gainLog Vlog
      baseB0 ∈ Set.Icc 0 ((B + 2) ^ outputPower) ∧
      Pwidth ∈ Set.Icc 0 ((B + 2) ^ outputPower) ∧
      Bcert ∈ Set.Icc 0 ((B + 2) ^ outputPower) ∧
      Pgood ∈ Set.Icc 0 ((B + 2) ^ outputPower) ∧
      preparedFiniteScheduleAnchorGoodRequired q Pmaster Plate Econditional Bcert Pgood Pwidth ≤
        (B + 2) ^ outputPower := by
  obtain ⟨goodPower, _, hGood⟩ :=
    exists_preparedForecastGoodBudgets_bound (preparedCenteredShortForecastSpatialExponent q)
  let U : Polynomial ℕ := (Polynomial.X + 2) ^ inputPower
  let T : Polynomial ℕ := Polynomial.X + 9 + 8 * U + 4 * (U + 8) ^ 2
  let envelope : Polynomial ℕ := T + (T + Polynomial.C goodPower) ^ goodPower
  obtain ⟨scalarPower, hscalarPower, hEnvelope⟩ := exists_natPolynomial_fixed_power_budget envelope
  obtain ⟨anchorPower, _, hAnchor⟩ := exists_preparedFiniteNestedAnchorRequired_power_budget q inputPower
  refine ⟨max scalarPower anchorPower, hscalarPower.trans (le_max_left _ _), ?_⟩
  intro B hB M nX pRadius Pscale Pseed Qw gainLog Vlog Pmaster Plate Econditional
    hM hnX hRadius hScale hSeed hQw hGain hV hE hMaster hLate hPlate
    baseB0 Pwidth Bcert Pgood
  let inputBound := (B + 2) ^ inputPower
  let commonBound := B + 9 + 8 * inputBound + 4 * (inputBound + 8) ^ 2
  have hB0 : 0 ≤ B := (by norm_num : (0 : ℝ) ≤ 2).trans hB
  have hInput0 : 0 ≤ inputBound := pow_nonneg (by linarith only [hB0]) _
  have hSquare0 : 0 ≤ 4 * (inputBound + 8) ^ 2 := by positivity
  have hInputCommon : inputBound ≤ commonBound := by
    dsimp only [commonBound]
    linarith only [hB0, hInput0, hSquare0]
  have hCommon0 : 0 ≤ commonBound := hInput0.trans hInputCommon
  have hChartCommon : B ≤ commonBound := by
    dsimp only [commonBound]
    linarith only [hInput0, hSquare0]
  have hBase0 : 0 ≤ baseB0 := by
    dsimp only [baseB0, preparedUniformDegreeProductiveCertificateBudget]
    have := hRadius.1
    have := hScale.1
    have := hSeed.1
    have := hQw.1
    have := hGain.1
    have := hV.1
    positivity
  have hBaseCommon : baseB0 ≤ commonBound := by
    dsimp only [baseB0, preparedUniformDegreeProductiveCertificateBudget, commonBound]
    linarith only [hB0, hSquare0, hM, hnX, hRadius.2, hScale.2, hSeed.2,
      hQw.2, hGain.2, hV.2]
  have hWidth0 : 0 ≤ Pwidth := by dsimp only [Pwidth]; positivity
  have hPlate0 : 0 ≤ Plate := hMaster.trans hLate
  have hWidthCommon : Pwidth ≤ commonBound := by
    have hWidthUpper : Pwidth ≤ 4 * (inputBound + 8) ^ 2 :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by linarith only [hPlate0]) (add_le_add hPlate le_rfl) 2)
        (by norm_num)
    apply hWidthUpper.trans
    dsimp only [commonBound]
    linarith only [hB0, hInput0]
  have hGoodBounds := hGood hCommon0 ⟨hBase0, hBaseCommon⟩ ⟨hB0, hChartCommon⟩
    ⟨hWidth0, hWidthCommon⟩ ⟨hGain.1, hGain.2.trans hInputCommon⟩
    ⟨hV.1, hV.2.trans hInputCommon⟩
  have hEnvelopeReal : commonBound + (commonBound + goodPower) ^ goodPower ≤
      (B + 2) ^ scalarPower := by
    simpa [envelope, T, U, commonBound, inputBound, Polynomial.eval₂_pow] using hEnvelope B hB0
  have hGoodPower0 : 0 ≤ (commonBound + goodPower) ^ goodPower := by positivity
  have hCommonBound : commonBound ≤ (B + 2) ^ scalarPower :=
    (le_add_of_nonneg_right hGoodPower0).trans hEnvelopeReal
  have hGoodPowerBound : (commonBound + goodPower) ^ goodPower ≤ (B + 2) ^ scalarPower :=
    (le_add_of_nonneg_left hCommon0).trans hEnvelopeReal
  have hScalarFinal : (B + 2) ^ scalarPower ≤ (B + 2) ^ max scalarPower anchorPower :=
    pow_le_pow_right₀ (by linarith only [hB]) (le_max_left _ _)
  have hAnchorFinal : (B + 2) ^ anchorPower ≤ (B + 2) ^ max scalarPower anchorPower :=
    pow_le_pow_right₀ (by linarith only [hB]) (le_max_right _ _)
  refine ⟨⟨hBase0, hBaseCommon.trans (hCommonBound.trans hScalarFinal)⟩,
    ⟨hWidth0, hWidthCommon.trans (hCommonBound.trans hScalarFinal)⟩,
    ⟨hGoodBounds.1.1, hGoodBounds.1.2.trans (hGoodPowerBound.trans hScalarFinal)⟩,
    ⟨hGoodBounds.2.1, hGoodBounds.2.2.trans (hGoodPowerBound.trans hScalarFinal)⟩, ?_⟩
  exact (hAnchor hB M nX hM hnX hRadius hScale hSeed hQw hGain hV hE hMaster hLate hPlate).trans
    hAnchorFinal

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedFiniteNestedSourcePowerBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

theorem exists_preparedFiniteNestedSource_power_budget
    (m cutoff A Cdirect outerDepth innerDepth inputPower : ℕ)
    (constants : ℕ → ℕ) (hA : 2 ≤ A) (hcutoff : cutoff ≤ m)
    (hworkDepth : cutoff ≤ innerDepth) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (G : Type) [Fintype G] (M count nX : ℕ)
      {Bstruct pnum Qstride gainLog stageLog Vlog Qσ Pmin requestedCoarse endpoint : ℝ},
      2 ≤ Bstruct → pnum ∈ Set.Icc 0 Bstruct → Qstride ∈ Set.Icc 0 Bstruct →
      gainLog ∈ Set.Icc 0 Bstruct → stageLog ∈ Set.Icc 0 Bstruct →
      (M : ℝ) ≤ Bstruct → (count : ℝ) ≤ Bstruct → (nX : ℝ) ≤ Bstruct →
      (Fintype.card G : ℝ) ≤ Bstruct →
      Vlog ∈ Set.Icc 0 ((Bstruct + 2) ^ inputPower) →
      Qσ ∈ Set.Icc 0 ((Bstruct + 2) ^ inputPower) →
      Pmin ∈ Set.Icc 0 ((Bstruct + 2) ^ inputPower) →
      requestedCoarse ∈ Set.Icc 0 ((Bstruct + 2) ^ inputPower) →
      endpoint ∈ Set.Icc 0 ((Bstruct + 2) ^ inputPower) →
      let K := PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff
      let degree : K → ℕ := preparedFiniteNestedForwardAllDegreeDegree
      let Pdetect := preparedFiniteForwardDetectorPolynomial cutoff
      let Cdetect := fun k : K => sampledSupportedSlicedDetectionConstant (degree k) Pdetect
      let kModel : K := preparedFiniteNestedForwardAllDegreeAnchor outerDepth innerDepth cutoff
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
      let Ptail := fun k : K => affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
        (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (Eprofile k) (pDetect k + 2)
      let Pscale := preparedUniformDegreeScaleLog (D + pRadius) Ptail Qσ
      let Tmod := fun k : K => ((m + 1 : ℕ) : ℝ) * Pk k + nX * Qstride
      let lengthLogs := fun k : K => allocatedAffineLengthLog m D Pscale (Prho k) (Pk k)
        (target k) (pDetect k + 2) (Tmod k)
      let Pseed := allocatedScaleLog (Pscale + ∑ k, lengthLogs k + Pmin + 1)
      let Qw := 2 * Bstruct + 2 * Vlog + 5 * (gainLog + 8) + 24
      let Pmaster := fun k : K => preparedFiniteScheduleLocalMaster Bstruct D pRadius Qstride
        (Pphysical k) (sourceU k) (modelLog k) (Prho k) (target k) (detectionGain k)
      let coarseTarget := preparedFiniteScheduleDirectCoarse detectionGain requestedCoarse
      let Plate := ∑ k : K, preparedUniformDegreeDirectLate (Pmaster k) Pscale
        (Pphysical k) coarseTarget (allocatedWitnessScaleLog Pseed Qw)
      let Econditional := preparedFiniteNestedSourceProjectionPrecision
        (outerDepth := outerDepth) (innerDepth := innerDepth) (cutoff := cutoff)
        m G count nX A Cdirect constants Bstruct pnum Qstride gainLog stageLog Plate endpoint
      let baseB0 := preparedUniformDegreeProductiveCertificateBudget
        M nX pRadius Pscale Pseed Qw (gainLog + 8) Vlog
      let Pwidth := 4 * (Plate + 8) ^ 2
      let Bcert := preparedForecastGoodCertificateBudget baseB0 Bstruct Pwidth gainLog Vlog
      let Pgood := preparedForecastGoodAnalyticBudget (preparedCenteredShortForecastSpatialExponent m)
        baseB0 Bstruct Pwidth gainLog Vlog
      let anchorRequired := preparedFiniteScheduleAnchorGoodRequired
        m (Pmaster kModel) Plate Econditional Bcert Pgood Pwidth
      let conditionalRequired := preparedConditionalExcessRequired m Plate Econditional
      let detectorRequired := fun k : K => (preparedModularGeneralDetectorResources
        (preparedModularGeneralDetectorConstants m (degree k)) (degree k + 1) (Pmaster k) Plate).required
      let Rreq := preparedFiniteNestedSourceRequired A constants innerDepth outerDepth cutoff Bstruct
        anchorRequired conditionalRequired detectorRequired
      let bound := (Bstruct + 2) ^ C
      pRadius ∈ Set.Icc 0 bound ∧ Pscale ∈ Set.Icc 0 bound ∧ Pseed ∈ Set.Icc 0 bound ∧
      Plate ∈ Set.Icc 0 bound ∧ Econditional ∈ Set.Icc 0 bound ∧ endpoint ≤ Econditional ∧
      baseB0 ∈ Set.Icc 0 bound ∧ Pwidth ∈ Set.Icc 0 bound ∧ Bcert ∈ Set.Icc 0 bound ∧
      Pgood ∈ Set.Icc 0 bound ∧ anchorRequired ≤ bound ∧ conditionalRequired ≤ bound ∧
      (∀ k, detectorRequired k ≤ bound) ∧ Rreq ≤ bound := by
  let K := PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff
  obtain ⟨Cgeom, hCgeom, hgeom⟩ := exists_preparedFiniteNestedSourceLate_power_budget
    m cutoff A Cdirect outerDepth innerDepth inputPower constants hA hcutoff
  let projectionInput := max Cgeom inputPower
  obtain ⟨Cproj, Cconditional, _, _, hprojection⟩ := exists_preparedFiniteNestedSourceProjection_budget
    m cutoff A Cdirect outerDepth innerDepth projectionInput constants hA hcutoff
  let primitivePoly : Polynomial ℕ := 8 * Polynomial.X + 3 * (Polynomial.X + 2) ^ inputPower + 64
  obtain ⟨Cprimitive, _, hprimitive⟩ := exists_natPolynomial_fixed_power_budget primitivePoly
  let anchorInput := max Cgeom (max Cproj Cprimitive)
  obtain ⟨Canchor, hCanchor, hanchor⟩ := exists_preparedFiniteNestedAnchorScalars_power_budget m anchorInput
  let componentPower := max Canchor (max Cconditional Cgeom)
  obtain ⟨Creq, _, hrequired⟩ := exists_preparedFiniteNestedSourceRequired_power_budget
    A constants innerDepth outerDepth componentPower (Fintype.card K) hA
  let C := max Creq (max Canchor (max Cgeom Cproj))
  refine ⟨C, hCanchor.trans ((le_max_left _ _).trans (le_max_right _ _)), ?_⟩
  intro G _ M count nX Bstruct pnum Qstride gainLog stageLog Vlog Qσ Pmin requestedCoarse endpoint
    hB hnum hstride hg hs hM hcount hnX hG hV hQσ hPmin hcoarse hend
    K' degree Pdetect Cdetect kModel sourceU modelLog pRadius D pDetect aDetect detectionGain Pk
    Pphysical target Eprofile Prho Ptail Pscale Tmod lengthLogs Pseed Qw Pmaster coarseTarget Plate
    Econditional baseB0 Pwidth Bcert Pgood anchorRequired conditionalRequired detectorRequired Rreq bound
  have hB0 : 0 ≤ Bstruct := (by norm_num : (0 : ℝ) ≤ 2).trans hB
  have hbase : 1 ≤ Bstruct + 2 := by linarith only [hB]
  have raise {a b : ℕ} (h : a ≤ b) : (Bstruct + 2) ^ a ≤ (Bstruct + 2) ^ b :=
    pow_le_pow_right₀ hbase h
  have lift {a b : ℕ} {x : ℝ} (h : a ≤ b) (hx : x ∈ Set.Icc 0 ((Bstruct + 2) ^ a)) :
      x ∈ Set.Icc 0 ((Bstruct + 2) ^ b) := ⟨hx.1, hx.2.trans (raise h)⟩
  have hgeometry := hgeom G count nX hB0 hnum hstride hg hs hcount hnX hG hV hQσ hPmin hcoarse
  obtain ⟨hSeed, _hWitness, hSchedule⟩ := hgeometry
  change Pseed ∈ Set.Icc 0 ((Bstruct + 2) ^ Cgeom) at hSeed
  obtain ⟨hRadius, _hD, hScale, _hCoarse, hPlate, hSlots⟩ := hSchedule
  have hMaster (k : K') : Pmaster k ∈ Set.Icc 0 ((Bstruct + 2) ^ Cgeom) :=
    (hSlots k).2.2.2.2.2.2.2.1
  have hDetector (k : K') : detectorRequired k ≤ (Bstruct + 2) ^ Cgeom :=
    (hSlots k).2.2.2.2.2.2.2.2.required.2
  have hMasterLate (k : K') : Pmaster k ≤ Plate := by
    apply (le_max_left _ _).trans
    exact Finset.single_le_sum
      (f := fun k => preparedUniformDegreeDirectLate (Pmaster k) Pscale (Pphysical k)
        coarseTarget (allocatedWitnessScaleLog Pseed Qw))
      (fun k _ => (hMaster k).1.trans (le_max_left _ _)) (Finset.mem_univ k)
  obtain ⟨hProjection, hEndpoint, hConditional⟩ := hprojection G count nX hB hnum hstride hg hs
    hcount hnX hG (lift (le_max_right _ _) hend) (lift (le_max_left _ _) hPlate)
  have hPrimitiveBound : 8 * Bstruct + 3 * (Bstruct + 2) ^ inputPower + 64 ≤
      (Bstruct + 2) ^ Cprimitive := by
    simpa [primitivePoly, Polynomial.eval₂_pow] using hprimitive Bstruct hB0
  have hInput0 : 0 ≤ (Bstruct + 2) ^ inputPower := by positivity
  have hBprimitive : Bstruct ≤ (Bstruct + 2) ^ Cprimitive := by
    linarith only [hPrimitiveBound, hB0, hInput0]
  have hVprimitive : Vlog ∈ Set.Icc 0 ((Bstruct + 2) ^ Cprimitive) := by
    exact ⟨hV.1, hV.2.trans (by linarith only [hPrimitiveBound, hB0, hInput0])⟩
  have hQwprimitive : Qw ∈ Set.Icc 0 ((Bstruct + 2) ^ Cprimitive) := by
    constructor
    · dsimp only [Qw]; have := hV.1; have := hg.1; positivity
    · dsimp only [Qw]
      linarith only [hPrimitiveBound, hg.2, hV.2, hB0, hInput0]
  have hPrimitiveAnchor : Cprimitive ≤ anchorInput := (le_max_right _ _).trans (le_max_right _ _)
  have hBanchor : Bstruct ≤ (Bstruct + 2) ^ anchorInput := hBprimitive.trans (raise hPrimitiveAnchor)
  obtain ⟨hBase, hWidth, hCertificate, hGood, hAnchor⟩ := hanchor hB M nX
    (hM.trans hBanchor) (hnX.trans hBanchor)
    (lift (le_max_left _ _) hRadius) (lift (le_max_left _ _) hScale)
    (lift (le_max_left _ _) hSeed) (lift hPrimitiveAnchor hQwprimitive)
    ⟨hg.1, hg.2.trans hBanchor⟩ (lift hPrimitiveAnchor hVprimitive)
    (lift ((le_max_left _ _).trans (le_max_right _ _)) hProjection)
    (hMaster kModel).1 (hMasterLate kModel) (hPlate.2.trans (raise (le_max_left _ _)))
  have hRreq : Rreq ≤ (Bstruct + 2) ^ Creq := hrequired K' cutoff hworkDepth le_rfl hB0
    (hAnchor.trans (raise (le_max_left _ _)))
    (hConditional.trans (raise ((le_max_left _ _).trans (le_max_right _ _))))
    detectorRequired (fun k => (hDetector k).trans
      (raise ((le_max_right _ _).trans (le_max_right _ _))))
  have hGeomFinal : Cgeom ≤ C := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hProjFinal : Cproj ≤ C := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hAnchorFinal : Canchor ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  refine ⟨lift hGeomFinal hRadius, lift hGeomFinal hScale, lift hGeomFinal hSeed,
    lift hGeomFinal hPlate, lift hProjFinal hProjection, hEndpoint,
    lift hAnchorFinal hBase, lift hAnchorFinal hWidth, lift hAnchorFinal hCertificate,
    lift hAnchorFinal hGood, hAnchor.trans (raise hAnchorFinal), ?_,
    fun k => (hDetector k).trans (raise hGeomFinal), hRreq.trans (raise (le_max_left _ _))⟩
  exact (conditionalRequired_le_preparedFiniteNestedSourceRequired A constants innerDepth outerDepth cutoff
    Bstruct anchorRequired conditionalRequired detectorRequired).trans
      (hRreq.trans (raise (le_max_left _ _)))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedCanonicalRelativeEndpointBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

theorem exists_preparedFiniteNestedSourceRequiredLog_power_budget
    (m cutoff A Cdirect outerDepth innerDepth inputPower : ℕ)
    (constants : ℕ → ℕ) (hA : 2 ≤ A) (hcutoff : cutoff ≤ m)
    (hworkDepth : cutoff ≤ innerDepth) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (G : Type) [Fintype G] (M count nX : ℕ)
      {Bstruct pnum Qstride gainLog stageLog Vlog Qσ Pmin requestedCoarse endpoint : ℝ},
      2 ≤ Bstruct → pnum ∈ Set.Icc 0 Bstruct → Qstride ∈ Set.Icc 0 Bstruct →
      gainLog ∈ Set.Icc 0 Bstruct → stageLog ∈ Set.Icc 0 Bstruct →
      (M : ℝ) ≤ Bstruct → (count : ℝ) ≤ Bstruct → (nX : ℝ) ≤ Bstruct →
      (Fintype.card G : ℝ) ≤ Bstruct →
      Vlog ∈ Set.Icc 0 ((Bstruct + 2) ^ inputPower) →
      Qσ ∈ Set.Icc 0 ((Bstruct + 2) ^ inputPower) →
      Pmin ∈ Set.Icc 0 ((Bstruct + 2) ^ inputPower) →
      requestedCoarse ∈ Set.Icc 0 ((Bstruct + 2) ^ inputPower) →
      endpoint ∈ Set.Icc 0 ((Bstruct + 2) ^ inputPower) →
      preparedFiniteNestedSourceRequiredLog m cutoff A Cdirect outerDepth innerDepth constants
        G M count nX Bstruct pnum Qstride gainLog stageLog Vlog Qσ Pmin requestedCoarse endpoint ≤
          (Bstruct + 2) ^ C := by
  obtain ⟨C, hC, hbound⟩ := exists_preparedFiniteNestedSource_power_budget
    m cutoff A Cdirect outerDepth innerDepth inputPower constants hA hcutoff hworkDepth
  refine ⟨C, hC, ?_⟩
  intro G _ M count nX Bstruct pnum Qstride gainLog stageLog Vlog Qσ Pmin requestedCoarse endpoint
    hB hnum hstride hg hs hM hcount hnX hG hV hQσ hPmin hcoarse hend
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hrequired⟩ :=
    hbound G M count nX hB hnum hstride hg hs hM hcount hnX hG hV hQσ hPmin hcoarse hend
  exact hrequired

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

theorem exists_preparedFiniteNestedCanonicalRequired_power_budget_of_inputPower_s2_oai
    (s outerDepth innerDepth cutoff e Cprimitive Cdirect extra earlybasePower inputPower : ℕ)
    (constants : ℕ → ℕ) (hworkDepth : cutoff ≤ innerDepth) (hbasePower : 1 ≤ earlybasePower) :
    ∃ requiredPower : ℕ, 2 ≤ requiredPower ∧ ∀ {p : ℝ}, 2 ≤ p →
      ∀ m ≤ s, ∀ (G : Type) [Fintype G] (M count nX : ℕ)
      {pnum Qstride gainLog stageLog Vlog Qσ Pmin requestedCoarse endpoint : ℝ},
      let q := max m cutoff
      let A := preparedFiniteNestedSourceExponent q cutoff e Cprimitive Cdirect extra
      let Bstruct := (p + 2) ^ earlybasePower
      pnum ∈ Set.Icc 0 Bstruct → Qstride ∈ Set.Icc 0 Bstruct →
      gainLog ∈ Set.Icc 0 Bstruct → stageLog ∈ Set.Icc 0 Bstruct →
      (M : ℝ) ≤ Bstruct → (count : ℝ) ≤ Bstruct → (nX : ℝ) ≤ Bstruct →
      (Fintype.card G : ℝ) ≤ Bstruct →
      Vlog ∈ Set.Icc 0 ((Bstruct + 2) ^ inputPower) →
      Qσ ∈ Set.Icc 0 ((Bstruct + 2) ^ inputPower) →
      Pmin ∈ Set.Icc 0 ((Bstruct + 2) ^ inputPower) →
      requestedCoarse ∈ Set.Icc 0 ((Bstruct + 2) ^ inputPower) →
      endpoint ∈ Set.Icc 0 ((Bstruct + 2) ^ inputPower) →
      preparedFiniteNestedSourceRequiredLog q cutoff A Cdirect outerDepth innerDepth constants
        G M count nX Bstruct pnum Qstride gainLog stageLog Vlog Qσ Pmin requestedCoarse endpoint ≤
          (p + 2) ^ requiredPower := by
  let q := fun i : Fin (s + 1) => max i.val cutoff
  let A := fun i : Fin (s + 1) =>
    preparedFiniteNestedSourceExponent (q i) cutoff e Cprimitive Cdirect extra
  have hA (i : Fin (s + 1)) : 2 ≤ A i :=
    (preparedFiniteNestedSourceExponent_bounds (q i) cutoff e Cprimitive Cdirect extra (A i) le_rfl).1
  let exponent := fun i : Fin (s + 1) => Classical.choose
    (exists_preparedFiniteNestedSourceRequiredLog_power_budget (q i) cutoff (A i) Cdirect
      outerDepth innerDepth inputPower constants (hA i) (Nat.le_max_right _ _) hworkDepth)
  let boundPoly : Polynomial ℕ := ∑ i : Fin (s + 1),
    ((Polynomial.X + 2) ^ earlybasePower + 2) ^ exponent i
  obtain ⟨requiredPower, hrequiredPower, hbound⟩ := exists_natPolynomial_fixed_power_budget boundPoly
  refine ⟨requiredPower, hrequiredPower, ?_⟩
  intro p hp m hm G _ M count nX pnum Qstride gainLog stageLog Vlog Qσ Pmin requestedCoarse endpoint
    q' A' Bstruct hnum hstride hg hs hM hcount hnX hG hV hQσ hPmin hcoarse hend
  let i : Fin (s + 1) := ⟨m, Nat.lt_succ_of_le hm⟩
  have hp0 : 0 ≤ p := (by norm_num : (0 : ℝ) ≤ 2).trans hp
  have hB : 2 ≤ Bstruct := by
    have hpower : p + 2 ≤ (p + 2) ^ earlybasePower := by
      simpa only [pow_one] using pow_le_pow_right₀
        (by linarith only [hp] : 1 ≤ p + 2) hbasePower
    exact (by linarith only [hp] : (2 : ℝ) ≤ p + 2).trans hpower
  have hlocal := (Classical.choose_spec
    (exists_preparedFiniteNestedSourceRequiredLog_power_budget (q i) cutoff (A i) Cdirect
      outerDepth innerDepth inputPower constants (hA i) (Nat.le_max_right _ _) hworkDepth)).2
    G M count nX hB hnum hstride hg hs hM hcount hnX hG
    hV hQσ hPmin hcoarse hend
  have hentry : (Bstruct + 2) ^ exponent i ≤ (p + 2) ^ requiredPower := by
    apply le_trans _ (hbound p hp0)
    rw [Polynomial.eval₂_finsetSum]
    have hsingle := Finset.single_le_sum
      (f := fun j : Fin (s + 1) =>
        (((Polynomial.X + 2) ^ earlybasePower + 2) ^ exponent j).eval₂ (Nat.castRingHom ℝ) p)
      (fun j _ => natPolynomial_eval_nonneg _ hp0) (Finset.mem_univ i)
    simpa [Bstruct, Polynomial.eval₂_pow] using hsingle
  exact hlocal.trans hentry

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.exists_preparedFiniteNestedCanonicalRequired_power_budget_of_inputPower_s2_oai := @OAI.Erdos3.VectorPolynomial.exists_preparedFiniteNestedCanonicalRequired_power_budget_of_inputPower_s2_oai
