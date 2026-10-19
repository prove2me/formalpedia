-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.exists_scalarNestedSourceDegreeGlobalization_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T09:35:21.764059+00:00
-- url     : https://prove2.me/submissions/736d2da1-2314-4b68-bc2a-565535e7b5ad

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B297
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_AllocatedExternalCandidateSampler_nativeDetection_of_preparedScalarNestedSchedule_s2

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CanonicalEmptyLayerGeometry
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {G X : Type*} {I J : Fin 0 → Type*} {n : Fin 0 → ℕ}
    (B : LayerSamplerAxis I n → Type*)

variable [Fintype G] [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    [∀ a, Fintype (B a)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin 0 → ℝ}

variable (S : LayerSamplerScale (G := G) B U b R σ)

theorem allocatedExternalCandidateRootBudget_zero_layers :
    allocatedExternalCandidateRootBudget B U b S =
      (Fintype.card G : ℝ) * S.value := by
  unfold allocatedExternalCandidateRootBudget
  rw [zeroLayerVariables_card]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem scalarNativeDimension_pos (s : ℕ) : 0 < scalarNativeDimension s := by
  unfold scalarNativeDimension
  positivity

end Erdos3.VectorPolynomial

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

section

namespace Erdos3.VectorPolynomial

theorem exists_preparedFiniteNestedSourceRequired_raised_power_budget
    (A : ℕ) (constants : ℕ → ℕ)
    (innerDepth outerDepth basePower lateExponent slotBound : ℕ)
    (hA : 2 ≤ A) (hBase : 1 ≤ basePower) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}, 2 ≤ p →
      ∀ (Slot : Type*) [Fintype Slot], ∀ cutoff ≤ innerDepth,
        Fintype.card Slot ≤ slotBound →
        ∀ detectorRequired : Slot → ℝ,
          (∀ slot, detectorRequired slot ≤ (p + 2) ^ lateExponent) →
          preparedFiniteNestedSourceRequired A constants innerDepth outerDepth cutoff
            ((p + 2) ^ basePower) 0 0 detectorRequired ≤ (p + 2) ^ C := by
  obtain ⟨D, _, hrequired⟩ := exists_preparedFiniteNestedSourceRequired_power_budget
    A constants innerDepth outerDepth lateExponent slotBound hA
  let bound : Polynomial ℕ := ((Polynomial.X + 2) ^ basePower + 2) ^ D
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_fixed_power_budget bound
  refine ⟨C, hC, ?_⟩
  intro p hp Slot _ cutoff hcutoff hcard detectorRequired hdetector
  have hp0 : 0 ≤ p := by linarith
  have hstruct0 : 0 ≤ (p + 2) ^ basePower := by positivity
  have hpStruct : p ≤ (p + 2) ^ basePower := le_power_budget hp0 hBase
  have hinput : (p + 2) ^ lateExponent ≤
      ((p + 2) ^ basePower + 2) ^ lateExponent :=
    pow_le_pow_left₀ (by linarith) (by linarith) lateExponent
  have hactual := hrequired Slot cutoff hcutoff
    (x := (p + 2) ^ basePower) (anchorGoodRequired := 0) (conditionalRequired := 0)
    hcard hstruct0 (by positivity) (by positivity) detectorRequired
    (fun slot => (hdetector slot).trans hinput)
  apply hactual.trans
  simpa [bound, Polynomial.eval₂_pow] using hbound p hp0

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

theorem PreparedEmptyLayerLocalScheduleBudget.tailWidthLog_le
    {m : ℕ} {K G : Type} [Fintype K] [Fintype G]
    {degree Cdetect : K → ℕ} {nX count : ℕ}
    {Bstruct pnum Qstride Qσ requestedCoarse extraLate : ℝ}
    {u model : K → ℝ} {cap : ℝ}
    (h : PreparedEmptyLayerLocalScheduleBudget (G := G) m degree Cdetect nX count
      Bstruct pnum Qstride Qσ requestedCoarse extraLate u model cap) :
    preparedEmptyLayerLocalTailWidthLog (G := G) m degree Cdetect nX count
      Bstruct pnum Qstride Qσ u model ≤
        (probabilityProfileLipschitz : ℝ) + 12 + 3 * cap := by
  unfold PreparedEmptyLayerLocalScheduleBudget at h
  dsimp only at h
  unfold preparedEmptyLayerLocalTailWidthLog
  dsimp only
  linarith only [h.1.2, h.2.1.2, h.2.2.1.2]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical BigOperators NNReal

theorem exists_preparedScalarFiniteSchedule_power_budget
    (s nStages inputPower : ℕ) (Pdetect : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}, 0 ≤ p →
      ∀ {nX : ℕ} {K : Type} [Fintype K]
        (degree : K → ℕ) (Bstruct extraLate : ℝ) (sourceU modelLog : K → ℝ),
        Fintype.card K ≤ nStages → (∀ k, degree k ≤ s) → (nX : ℝ) ≤ p →
        Bstruct ∈ Set.Icc 0 ((p + 2) ^ inputPower) →
        extraLate ∈ Set.Icc 0 ((p + 2) ^ inputPower) →
        (∀ k, sourceU k ∈ Set.Icc 0 ((p + 2) ^ inputPower)) →
        (∀ k, modelLog k ∈ Set.Icc 0 ((p + 2) ^ inputPower)) →
        let Cdetect := fun k => sampledSupportedSlicedDetectionConstant (degree k) Pdetect
        PreparedEmptyLayerLocalScheduleBudget (G := Fin (scalarNativeDimension s))
          (max s 1) degree Cdetect nX (scalarNativeDimension s)
          Bstruct (scalarNativeDimension s : ℝ) 0 0 0 extraLate sourceU modelLog
          ((p + 2) ^ C) ∧
        preparedEmptyLayerLocalTailWidthLog (G := Fin (scalarNativeDimension s))
          (max s 1) degree Cdetect nX (scalarNativeDimension s)
          Bstruct (scalarNativeDimension s : ℝ) 0 0 sourceU modelLog ≤ (p + 2) ^ C := by
  let Cmax := ∑ d : Fin (s + 1), sampledSupportedSlicedDetectionConstant d.val Pdetect
  obtain ⟨Cbase, hCbase, hbase⟩ :=
    exists_preparedEmptyLayerLocalSchedule_budget (max s 1) nStages Cmax
  let input : Polynomial ℕ := (Polynomial.X + 2) ^ inputPower + Polynomial.X +
    Polynomial.C (scalarNativeDimension s)
  let capPoly : Polynomial ℕ := (input + 2) ^ Cbase
  let bound : Polynomial ℕ :=
    Polynomial.C (⌈(probabilityProfileLipschitz : ℝ)⌉₊ + 12) + 4 * capPoly
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_fixed_power_budget bound
  refine ⟨C, hC, ?_⟩
  intro p hp nX K _ degree Bstruct extraLate sourceU modelLog
    hCard hdegree hnX hB hExtra hu hmodel Cdetect
  let P : ℝ := (p + 2) ^ inputPower + p + scalarNativeDimension s
  have ht : 0 ≤ (p + 2) ^ inputPower := by positivity
  have hd : (0 : ℝ) ≤ scalarNativeDimension s := Nat.cast_nonneg _
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have htP : (p + 2) ^ inputPower ≤ P := by dsimp only [P]; linarith
  have hpP : p ≤ P := by dsimp only [P]; linarith
  have hdP : (scalarNativeDimension s : ℝ) ≤ P := by dsimp only [P]; linarith
  have lift {x : ℝ} (hx : x ∈ Set.Icc 0 ((p + 2) ^ inputPower)) :
      x ∈ Set.Icc 0 P := ⟨hx.1, hx.2.trans htP⟩
  have hCdetect (k : K) : Cdetect k ≤ Cmax := by
    let d : Fin (s + 1) := ⟨degree k, Nat.lt_succ_of_le (hdegree k)⟩
    have hsum := Finset.single_le_sum
      (f := fun d : Fin (s + 1) => sampledSupportedSlicedDetectionConstant d.val Pdetect)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ d)
    exact hsum
  have hSchedule := hbase (G := Fin (scalarNativeDimension s)) degree Cdetect
    (nX := nX) (count := scalarNativeDimension s)
    (P := P) (Bstruct := Bstruct) (pnum := (scalarNativeDimension s : ℝ))
    (Qstride := 0) (Qσ := 0) (requestedCoarse := 0) (extraLate := extraLate)
    sourceU modelLog hCard (fun k => (hdegree k).trans (le_max_left s 1)) hCdetect
    hP (lift hB) ⟨hd, hdP⟩ ⟨le_rfl, hP⟩ ⟨le_rfl, hP⟩ ⟨le_rfl, hP⟩
    (lift hExtra) (fun k => lift (hu k)) (fun k => lift (hmodel k)) hdP
    (hnX.trans hpP) (by simpa only [Fintype.card_fin] using hdP)
  have hmajor : (⌈(probabilityProfileLipschitz : ℝ)⌉₊ : ℝ) + 12 +
      4 * (P + 2) ^ Cbase ≤ (p + 2) ^ C := by
    simpa [bound, capPoly, input, P, Polynomial.eval₂_pow] using hbound p hp
  have hcap0 : 0 ≤ (P + 2) ^ Cbase := by positivity
  have hceil0 : (0 : ℝ) ≤ ⌈(probabilityProfileLipschitz : ℝ)⌉₊ := Nat.cast_nonneg _
  have hcap : (P + 2) ^ Cbase ≤ (p + 2) ^ C := by
    linarith only [hmajor, hcap0, hceil0]
  refine ⟨hSchedule.mono hcap, ?_⟩
  have hwidth := hSchedule.tailWidthLog_le
  have hprofile := Nat.le_ceil (probabilityProfileLipschitz : ℝ)
  exact hwidth.trans (by linarith only [hmajor, hprofile, hcap0])

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.IndexedComparableScalarGeometryData
namespace OAI

section

namespace Erdos3

theorem unconditionedSpatialWidthCutoff_le_exp {P Q W τ : ℝ}
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hW : W ≤ Real.exp Q)
    (hτ : 0 < τ) (hτP : τ⁻¹ ≤ Real.exp P)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) :
    unconditionedSpatialWidthCutoff W τ 1 ≤ Real.exp (Q + 2 * P + 16) := by
  have heP : 1 ≤ Real.exp P := Real.one_le_exp_iff.mpr hP
  have heQ : 1 ≤ Real.exp Q := Real.one_le_exp_iff.mpr hQ
  have hfour : (4 : ℝ) ≤ Real.exp 16 := by linarith [Real.add_one_le_exp (16 : ℝ)]
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h128 : (128 : ℝ) ≤ Real.exp 16 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) htwo 7
    have hp' : (128 : ℝ) ≤ Real.exp 7 := by
      norm_num [← Real.exp_nat_mul] at hp
      exact hp
    exact hp'.trans (Real.exp_le_exp.mpr (by norm_num))
  have hmax : max (8 * (probabilityProfileLipschitz : ℝ)) 1 ≤ 8 * Real.exp P :=
    max_le (mul_le_mul_of_nonneg_left hprofile (by norm_num)) (by linarith)
  unfold unconditionedSpatialWidthCutoff
  apply max_le
  · calc
      4 / τ ≤ Real.exp 16 * Real.exp P := by
        rw [div_eq_mul_inv]
        exact mul_le_mul hfour hτP (inv_nonneg.mpr hτ.le) (Real.exp_nonneg _)
      _ = Real.exp (P + 16) := by rw [← Real.exp_add, add_comm]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  · calc
      8 * (1 + W) * max (8 * (probabilityProfileLipschitz : ℝ)) 1 / τ ≤
          8 * (2 * Real.exp Q) * (8 * Real.exp P) * Real.exp P := by
        rw [div_eq_mul_inv]
        gcongr
        linarith
      _ = 128 * Real.exp (Q + 2 * P) := by rw [Real.exp_add, two_mul P, Real.exp_add]; ring
      _ ≤ Real.exp 16 * Real.exp (Q + 2 * P) :=
        mul_le_mul_of_nonneg_right h128 (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring

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

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem preparedFiniteNestedResourceLayerSourceExponent_bounds
    (m q cutoff e Cprimitive Cdirect extra A : ℕ)
    (hA : preparedFiniteNestedResourceLayerSourceExponent
      m q cutoff e Cprimitive Cdirect extra ≤ A) :
    2 ≤ A ∧ extra ≤ A ∧ preparedFiniteForwardFrontProfileExponent e ≤ A ∧
    preparedFiniteNestedSourceSliceExponent m cutoff Cprimitive + 1 ≤ A ∧
    ∀ d ≤ cutoff, allocatedCandidateForwardScheduleExponent d m Cprimitive
      (preparedFiniteForwardInnerSourceExponent Cdirect
        (preparedFiniteForwardActualNativeBudgetExponent q
          (preparedFiniteForwardDetectorPolynomial cutoff))) 2 ≤ A := by
  have hfields : 2 ≤ A ∧ extra ≤ A ∧ preparedFiniteForwardFrontProfileExponent e ≤ A ∧
      preparedFiniteNestedSourceSliceExponent m cutoff Cprimitive + 1 ≤ A := by
    unfold preparedFiniteNestedResourceLayerSourceExponent at hA
    omega
  refine ⟨hfields.1, hfields.2.1, hfields.2.2.1, hfields.2.2.2, ?_⟩
  intro d hd
  have hsum := Finset.single_le_sum
    (f := fun i : Fin (cutoff + 1) => allocatedCandidateForwardScheduleExponent i.val m Cprimitive
      (preparedFiniteNestedSourceNativeExponent q cutoff Cdirect) 2)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ (⟨d, Nat.lt_succ_of_le hd⟩ : Fin (cutoff + 1)))
  change allocatedCandidateForwardScheduleExponent d m Cprimitive
    (preparedFiniteNestedSourceNativeExponent q cutoff Cdirect) 2 ≤ _ at hsum
  change allocatedCandidateForwardScheduleExponent d m Cprimitive
    (preparedFiniteNestedSourceNativeExponent q cutoff Cdirect) 2 ≤ A
  unfold preparedFiniteNestedResourceLayerSourceExponent at hA
  omega

theorem preparedFiniteNestedResourceLayerSourceSliceExponent_bounds
    (m cutoff Cprimitive : ℕ) :
    1 ≤ preparedFiniteNestedSourceSliceExponent m cutoff Cprimitive ∧
    ∀ d ≤ cutoff, allocatedCandidateStageSliceExponent d m Cprimitive ≤
      preparedFiniteNestedSourceSliceExponent m cutoff Cprimitive :=
  preparedFiniteNestedSourceSliceExponent_bounds m cutoff Cprimitive

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedScalarNestedPowerDetection
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

theorem PreparedEmptyLayerLocalScheduleBudget.lengthLog_mem
    {m : ℕ} {K G : Type} [Fintype K] [Fintype G]
    {degree Cdetect : K → ℕ} {nX count : ℕ}
    {Bstruct pnum Qstride Qσ requestedCoarse extraLate : ℝ}
    {u model : K → ℝ} {cap : ℝ}
    (h : PreparedEmptyLayerLocalScheduleBudget (G := G) m degree Cdetect nX count
      Bstruct pnum Qstride Qσ requestedCoarse extraLate u model cap) (k : K) :
    preparedEmptyLayerLocalLengthLog (G := G) m degree Cdetect nX count
      Bstruct pnum Qstride Qσ u model k ∈ Set.Icc 0 cap :=
  (h.2.2.2.2.2 k).2.2.2.2.2.2.1

theorem PreparedEmptyLayerLocalScheduleBudget.scaleFloor_le
    {m nStages : ℕ} {K G : Type} [Fintype K] [Fintype G]
    {degree Cdetect : K → ℕ} {nX count : ℕ}
    {Bstruct pnum Qstride Qσ requestedCoarse extraLate : ℝ}
    {u model : K → ℝ} {cap : ℝ}
    (h : PreparedEmptyLayerLocalScheduleBudget (G := G) m degree Cdetect nX count
      Bstruct pnum Qstride Qσ requestedCoarse extraLate u model cap)
    (hCard : Fintype.card K ≤ nStages) (hcap : 0 ≤ cap) :
    preparedEmptyLayerLocalScaleFloor (G := G) m degree Cdetect nX count
      Bstruct pnum Qstride Qσ u model ≤
      (probabilityProfileLipschitz : ℝ) + 12 + ((nStages : ℝ) + 3) * cap := by
  have hsum : (∑ k, max 0 (preparedEmptyLayerLocalLengthLog (G := G) m degree Cdetect nX count
      Bstruct pnum Qstride Qσ u model k)) ≤ (nStages : ℝ) * cap := by
    calc
      _ ≤ ∑ _k : K, cap := Finset.sum_le_sum (fun k _ => max_le hcap (h.lengthLog_mem k).2)
      _ = (Fintype.card K : ℝ) * cap := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hCard) hcap
  unfold preparedEmptyLayerLocalScaleFloor
  apply max_le
  · have hwidth := h.tailWidthLog_le
    have hprod : 0 ≤ (nStages : ℝ) * cap := mul_nonneg (Nat.cast_nonneg _) hcap
    nlinarith only [hwidth, hprod]
  · have hprofile := NNReal.coe_nonneg probabilityProfileLipschitz
    nlinarith only [hsum, hprofile, hcap]

theorem exists_preparedScalarFiniteSchedule_early_scale_power_budget
    (s nStages inputPower : ℕ) (Pdetect : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}, 0 ≤ p →
      ∀ {nX : ℕ} {K : Type} [Fintype K]
        (degree : K → ℕ) (Bstruct : ℝ) (sourceU modelLog : K → ℝ),
        Fintype.card K ≤ nStages → (∀ k, degree k ≤ s) → (nX : ℝ) ≤ p →
        Bstruct ∈ Set.Icc 0 ((p + 2) ^ inputPower) →
        (∀ k, sourceU k ∈ Set.Icc 0 ((p + 2) ^ inputPower)) →
        (∀ k, modelLog k ∈ Set.Icc 0 ((p + 2) ^ inputPower)) →
        let Cdetect := fun k => sampledSupportedSlicedDetectionConstant (degree k) Pdetect
        PreparedEmptyLayerLocalScheduleBudget (G := Fin (scalarNativeDimension s))
          (max s 1) degree Cdetect nX (scalarNativeDimension s)
          Bstruct (scalarNativeDimension s : ℝ) 0 0 0 0 sourceU modelLog ((p + 2) ^ C) ∧
        preparedEmptyLayerLocalScaleFloor (G := Fin (scalarNativeDimension s))
          (max s 1) degree Cdetect nX (scalarNativeDimension s)
          Bstruct (scalarNativeDimension s : ℝ) 0 0 sourceU modelLog ≤ (p + 2) ^ C := by
  obtain ⟨A, _, hCore⟩ := exists_preparedScalarFiniteSchedule_power_budget s nStages inputPower Pdetect
  let poly : Polynomial ℕ := Polynomial.C (⌈(probabilityProfileLipschitz : ℝ)⌉₊ + 12) +
    Polynomial.C (nStages + 4) * (Polynomial.X + 2) ^ A
  obtain ⟨C, hC, hPoly⟩ := exists_natPolynomial_fixed_power_budget poly
  refine ⟨C, hC, ?_⟩
  intro p hp nX K _ degree Bstruct sourceU modelLog hCard hdegree hnX hB hu hmodel Cdetect
  obtain ⟨hSchedule, _⟩ := hCore hp degree Bstruct 0 sourceU modelLog
    hCard hdegree hnX hB ⟨le_rfl, by positivity⟩ hu hmodel
  have hcap : 0 ≤ (p + 2) ^ A := by positivity
  have hmajor : (⌈(probabilityProfileLipschitz : ℝ)⌉₊ : ℝ) + 12 +
      ((nStages : ℝ) + 4) * (p + 2) ^ A ≤ (p + 2) ^ C := by
    simpa [poly, Polynomial.eval₂_pow] using hPoly p hp
  have hceil0 : (0 : ℝ) ≤ ⌈(probabilityProfileLipschitz : ℝ)⌉₊ := Nat.cast_nonneg _
  have hprod : 0 ≤ (nStages : ℝ) * (p + 2) ^ A := mul_nonneg (Nat.cast_nonneg _) hcap
  have hcapUp : (p + 2) ^ A ≤ (p + 2) ^ C := by nlinarith only [hmajor, hceil0, hprod, hcap]
  refine ⟨hSchedule.mono hcapUp, ?_⟩
  have hfloor := hSchedule.scaleFloor_le hCard hcap
  have hprofile := Nat.le_ceil (probabilityProfileLipschitz : ℝ)
  exact hfloor.trans (by nlinarith only [hmajor, hprofile, hcap])

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical

theorem exists_preparedScalarNestedInput_power_budget
    (outerDepth innerDepth cutoff exponent Cdirect basePower : ℕ)
    (constants : ℕ → ℕ) (hA : 2 ≤ exponent) :
    ∃ inputPower : ℕ, 2 ≤ inputPower ∧ ∀ {p : ℝ}, 0 ≤ p →
      let B := (p + 2) ^ basePower
      B ∈ Set.Icc 0 ((p + 2) ^ inputPower) ∧
      ∀ k : PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff,
        preparedFiniteForwardPairedSourcePrecision exponent Cdirect constants
          (preparedFiniteNestedForwardAllDegreeStage k).val
          (preparedFiniteNestedForwardAllDegreeIsDirect k)
          (preparedFiniteNestedForwardAllDegreeSeed exponent constants B k) B B ∈
            Set.Icc 0 ((p + 2) ^ inputPower) ∧
        preparedFiniteForwardWork exponent constants
          (preparedFiniteNestedForwardAllDegreeStage k).val
          (preparedFiniteNestedForwardAllDegreeSeed exponent constants B k) ∈
            Set.Icc 0 ((p + 2) ^ inputPower) := by
  obtain ⟨D, _, hlocal⟩ := exists_candidateNestedForwardLocal_budget
    exponent Cdirect constants innerDepth outerDepth hA
  let Q : Polynomial ℕ := (Polynomial.X + 2) ^ basePower +
    ((Polynomial.X + 2) ^ basePower + 2) ^ D
  obtain ⟨inputPower, hInput, hQ⟩ := exists_natPolynomial_fixed_power_budget Q
  refine ⟨inputPower, hInput, ?_⟩
  intro p hp B
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hmajor : B + (B + 2) ^ D ≤ (p + 2) ^ inputPower := by
    simpa [Q, B, Polynomial.eval₂_pow] using hQ p hp
  have hnonneg : 0 ≤ (B + 2) ^ D := by positivity
  have hcap : (B + 2) ^ D ≤ (p + 2) ^ inputPower := by
    linarith only [hmajor, hB]
  refine ⟨⟨hB, by linarith only [hmajor, hnonneg]⟩, ?_⟩
  intro k
  have h := hlocal (gainLog := B) (stageLog := B) hB ⟨hB, le_rfl⟩ ⟨hB, le_rfl⟩
    k.1.val (Nat.le_of_lt_succ k.1.isLt) k.2.1.val (Nat.le_of_lt_succ k.2.1.isLt)
  have hu := h.2.2.2.2.2 k.2.2.2
  have hw := h.2.2.1
  exact ⟨⟨hu.1, hu.2.trans hcap⟩, ⟨hw.1, hw.2.trans hcap⟩⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

theorem exists_preparedScalarNestedSchedule_power_detection
    (s outerDepth innerDepth exponent Cslice Cdirect : ℕ) (constants : ℕ → ℕ)
    (hA : 3 ≤ exponent) (hSlice : Cslice + 1 ≤ exponent) (hcutoff : s ≤ innerDepth) :
    ∃ baseMin : ℕ, 1 ≤ baseMin ∧ ∀ basePower : ℕ, baseMin ≤ basePower →
      ∃ earlyExponent : ℕ, 2 ≤ earlyExponent ∧ ∀ latePower : ℕ,
        ∃ sizeExponent : ℕ, 2 ≤ sizeExponent ∧
          PreparedScalarNestedPowerDetection s outerDepth innerDepth exponent Cslice Cdirect
            constants basePower earlyExponent latePower sizeExponent := by
  obtain ⟨baseMin, hBaseMin, hstruct⟩ := exists_preparedScalarStructuralBasePower s
  refine ⟨baseMin, hBaseMin, ?_⟩
  intro basePower hBasePower
  have hBase : 1 ≤ basePower := hBaseMin.trans hBasePower
  have hA2 : 2 ≤ exponent := by omega
  let K := PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth s
  let nStages := Fintype.card K
  let Pdetect := preparedFiniteForwardDetectorPolynomial s
  obtain ⟨inputPower, _, hinput⟩ := exists_preparedScalarNestedInput_power_budget
    outerDepth innerDepth s exponent Cdirect basePower constants hA2
  obtain ⟨earlyExponent, hEarly, hearly⟩ :=
    exists_preparedScalarFiniteSchedule_early_scale_power_budget s nStages inputPower Pdetect
  refine ⟨earlyExponent, hEarly, ?_⟩
  intro latePower
  obtain ⟨lateExponent, _, hlate⟩ :=
    exists_preparedScalarFiniteSchedule_power_budget s nStages (max inputPower latePower) Pdetect
  obtain ⟨sizeExponent, hSize, hrequired⟩ :=
    exists_preparedFiniteNestedSourceRequired_raised_power_budget exponent constants
      innerDepth outerDepth basePower lateExponent nStages hA2 hBase
  refine ⟨sizeExponent, hSize, ?_⟩
  intro nX p hp hX I₀ J₀ _ _ n₀ B₀ _ U₀ b₀ R₀ σ₀ S₀ hb₀ o₀ hR₀ hσ₀
    N poly₀ hmem₀ τ ξ₀ center₀ _ A₀ htrim hscale hSupper hsize
  let Bstruct : ℝ := (p + 2) ^ basePower
  let degree : K → ℕ := preparedFiniteNestedForwardAllDegreeDegree
  let stage : K → ℕ := fun k => (preparedFiniteNestedForwardAllDegreeStage k).val
  let seed : K → ℝ := preparedFiniteNestedForwardAllDegreeSeed exponent constants Bstruct
  let sourceU := fun k : K => preparedFiniteForwardPairedSourcePrecision exponent Cdirect
    constants (stage k) (preparedFiniteNestedForwardAllDegreeIsDirect k) (seed k) Bstruct Bstruct
  let modelLog := fun k : K => preparedFiniteForwardWork exponent constants (stage k) (seed k)
  let Cdetect := fun k : K => sampledSupportedSlicedDetectionConstant (degree k) Pdetect
  have hp0 : 0 ≤ p := by linarith
  have hB : 0 ≤ Bstruct := by dsimp [Bstruct]; positivity
  have hstructData := hstruct basePower hBasePower p hp
  have hinputData := hinput hp0
  have hcard : Fintype.card K ≤ nStages := le_rfl
  have hdegree (k : K) : degree k ≤ s :=
    preparedFiniteNestedForwardAllDegreeDegree_le (Nat.le_refl s) k
  have hu (k : K) : sourceU k ∈ Set.Icc 0 ((p + 2) ^ inputPower) := (hinputData.2 k).1
  have hm (k : K) : modelLog k ∈ Set.Icc 0 ((p + 2) ^ inputPower) := (hinputData.2 k).2
  have hEarlyData := hearly hp0 degree Bstruct sourceU modelLog hcard hdegree hX hinputData.1 hu hm
  have hbase : 1 ≤ p + 2 := by linarith
  have hInputLift : (p + 2) ^ inputPower ≤ (p + 2) ^ max inputPower latePower :=
    pow_le_pow_right₀ hbase (le_max_left inputPower latePower)
  have hLateLift : (p + 2) ^ latePower ≤ (p + 2) ^ max inputPower latePower :=
    pow_le_pow_right₀ hbase (le_max_right inputPower latePower)
  have lift {x : ℝ} (hx : x ∈ Set.Icc 0 ((p + 2) ^ inputPower)) :
      x ∈ Set.Icc 0 ((p + 2) ^ max inputPower latePower) := ⟨hx.1, hx.2.trans hInputLift⟩
  have hLateData := (hlate hp0 degree Bstruct ((p + 2) ^ latePower) sourceU modelLog
    hcard hdegree hX (lift hinputData.1) ⟨by positivity, hLateLift⟩
    (fun k => lift (hu k)) (fun k => lift (hm k))).1
  have hActual := A₀.nativeDetection_of_preparedScalarNestedSchedule_s2
    outerDepth innerDepth exponent Cslice Cdirect constants Bstruct Bstruct Bstruct
    ((p + 2) ^ latePower) p hA hSlice hstructData.1 ⟨hB, le_rfl⟩ ⟨hB, le_rfl⟩
    hstructData.2.1 hstructData.2.2.1 hp hX hstructData.2.2.2 htrim
  refine ⟨_, hLateData.2.2.2.2.1.1, ?_, ?_⟩
  · apply hActual
    · exact (Real.exp_le_exp.mpr hEarlyData.2).trans hscale
    · exact hSupper
    · intro i
      apply (Real.exp_le_exp.mpr (hrequired hp K s hcutoff hcard _ ?_)).trans (hsize i)
      intro k
      exact (hLateData.2.2.2.2.2 k).2.2.2.2.2.2.2.2.required.2
  · intro outer degree i
    exact (Real.exp_le_exp.mpr ((cumulative_le_preparedFiniteNestedSourceRequired
      exponent constants innerDepth outerDepth s Bstruct 0 0 (fun _ : K => 0) outer degree).trans
      (hrequired hp K s hcutoff hcard (fun _ : K => 0) (fun _ => by positivity)))).trans (hsize i)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PreparedScalarSpatialWidthPower
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem exists_preparedScalarSpatialWidthPower (s latePower : ℕ) :
    ∃ widthExponent : ℕ, 2 ≤ widthExponent ∧
      ∀ p : ℝ, 2 ≤ p → ∀ nX : ℕ, (nX : ℝ) ≤ p →
        ∀ S : ℕ, (S : ℝ) ≤ Real.exp ((p + 2) ^ latePower) →
          unconditionedSpatialWidthCutoff ((scalarNativeDimension s : ℝ) * S)
            (unconditionedSpatialTrimFraction nX (Real.exp (-p))) 1 ≤
              Real.exp ((p + 2) ^ widthExponent) := by
  obtain ⟨c, hc⟩ := exists_nat_ge (probabilityProfileLipschitz : ℝ)
  let Q : Polynomial ℕ := Polynomial.C (scalarNativeDimension s) +
    (Polynomial.X + 2) ^ latePower +
      2 * (2 * Polynomial.X + 33 + Polynomial.C c) + 16
  obtain ⟨widthExponent, hwidthExponent, hbudget⟩ :=
    exists_natPolynomial_fixed_power_budget Q
  refine ⟨widthExponent, hwidthExponent, ?_⟩
  intro p hp nX hnX S hS
  let t := (p + 2) ^ latePower
  let P : ℝ := 2 * p + 33 + c
  have hp0 : 0 ≤ p := by linarith
  have ht : 0 ≤ t := by dsimp only [t]; positivity
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hdim : (scalarNativeDimension s : ℝ) ≤
      Real.exp (scalarNativeDimension s : ℝ) :=
    le_trans (by linarith) (Real.add_one_le_exp _)
  have hW : (scalarNativeDimension s : ℝ) * S ≤
      Real.exp ((scalarNativeDimension s : ℝ) + t) := by
    calc
      _ ≤ Real.exp (scalarNativeDimension s : ℝ) * Real.exp t :=
        mul_le_mul hdim hS (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = _ := (Real.exp_add _ _).symm
  have hτ : 0 < unconditionedSpatialTrimFraction nX (Real.exp (-p)) := by
    unfold unconditionedSpatialTrimFraction
    positivity
  have hτP : (unconditionedSpatialTrimFraction nX (Real.exp (-p)))⁻¹ ≤
      Real.exp P := by
    have h32 : (32 : ℝ) ≤ Real.exp 32 := by
      linarith [Real.add_one_le_exp (32 : ℝ)]
    have hnExp : (nX : ℝ) + 1 ≤ Real.exp (p + 1) := by
      linarith [Real.add_one_le_exp (p + 1)]
    calc
      _ = 32 * ((nX : ℝ) + 1) * Real.exp p := by
        simp [unconditionedSpatialTrimFraction, Real.exp_neg]
      _ ≤ Real.exp 32 * Real.exp (p + 1) * Real.exp p := by gcongr
      _ = Real.exp (2 * p + 33) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp P := Real.exp_le_exp.mpr
        (by dsimp only [P]; linarith [Nat.cast_nonneg (α := ℝ) c])
  have hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P := by
    have hcExp : (c : ℝ) ≤ Real.exp c :=
      le_trans (by linarith) (Real.add_one_le_exp _)
    exact (hc.trans hcExp).trans
      (Real.exp_le_exp.mpr (by dsimp only [P]; linarith))
  apply (unconditionedSpatialWidthCutoff_le_exp hP
    (show 0 ≤ (scalarNativeDimension s : ℝ) + t by positivity)
    hW hτ hτP hprofile).trans
  apply Real.exp_le_exp.mpr
  simpa [Q, P, t, Polynomial.eval₂_pow] using hbudget p hp0

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ScalarNestedSourceDegreeGlobalization
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin 0 → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin 0 → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin 0 → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

namespace AllocatedExternalCandidateSampler

variable (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

local notation "countConstants" => degreeSourceCountConstants

local instance zeroLayerNestedDegreeScalarsSiteNonempty_r6fc1e9_1 : Nonempty A.Site := A.site_nonempty
variable (q outerDepth innerDepth cutoff exponent Cprimitive Cslice Cdirect : ℕ)
    (Bstruct gainLog stageLog Qstride Plate : ℝ)
local notation "Slots" => PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff
local notation "count" => Fintype.card (LayerSamplerVariables G I n B)
local notation "pnum" => (Fintype.card G : ℝ)
local notation "seed" => candidateNestedForwardSeed exponent countConstants innerDepth
local notation "native" => preparedFiniteNestedSourceNative q G count (Fintype.card X)
    (preparedFiniteForwardDetectorPolynomial cutoff) exponent Cdirect countConstants
    Bstruct pnum Qstride gainLog stageLog Plate
local notation "slotSeed" => preparedFiniteNestedForwardAllDegreeSeed exponent countConstants Bstruct
local notation "slotStage" => preparedFiniteNestedForwardAllDegreeStage
local notation "slotDegree" => preparedFiniteNestedForwardAllDegreeDegree
attribute [local irreducible] AllocatedExternalCandidateSampler.NativeDetection

theorem exists_zeroLayerNestedDegreeSourceProfile_scalars
    (outerFront outerInner : Fin (outerDepth + 1)) {degree e : ℕ} {p : ℝ}
    (hdegree : degree ≤ cutoff) (hcutoff : cutoff ≤ q) (hdepth : degree ≤ innerDepth)
    (hFrontExponent : preparedFiniteForwardFrontProfileExponent e ≤ exponent)
    (hInnerExponent : allocatedCandidateForwardScheduleExponent degree 0 Cprimitive
      (preparedFiniteForwardInnerSourceExponent Cdirect
        (preparedFiniteForwardActualNativeBudgetExponent q
          (preparedFiniteForwardDetectorPolynomial cutoff))) 2 ≤ exponent)
    (hCslice : 1 ≤ Cslice) (hSliceExponent : Cslice + 1 ≤ exponent)
    (hInnerSlice : allocatedCandidateStageSliceExponent degree 0 Cprimitive ≤ Cslice)
    (hprimitive : 1 ≤ Cprimitive)
    (hBstruct : 0 ≤ Bstruct) (hg : gainLog ∈ Set.Icc 0 Bstruct)
    (hs : stageLog ∈ Set.Icc 0 Bstruct) (hQstride : Qstride ∈ Set.Icc 0 Bstruct)
    (hG : (Fintype.card G : ℝ) ≤ Bstruct)
    (hX : (Fintype.card X : ℝ) ≤ Bstruct)
    (hpFront : p ∈ Set.Icc 0 (seed outerFront.val Bstruct))
    (hpInner : p ≤ seed outerInner.val Bstruct)
    (hξ : ξ ≤ 1)
    {surplus L : ℝ} (hsurplus : 0 < surplus) (hsurplus1 : surplus ≤ 1)
    (htrim : τ = unconditionedSpatialTrimFraction (Fintype.card X) surplus)
    (hN : ∀ i, unconditionedSpatialWidthCutoff
      (allocatedExternalCandidateRootBudget B U b S) τ L ≤ (N i : ℝ))
    (hNative : ∀ k : Slots, A.NativeDetection (slotDegree k)
      ((preparedFiniteForwardParameter exponent countConstants (slotStage k).val (slotSeed k) + Cslice) ^ Cslice)
      ((preparedFiniteForwardDetectorPolynomial cutoff).eval₂ (Nat.castRingHom ℝ)
        (allocatedModelTestLog
          (preparedFiniteForwardPairedSourcePrecision exponent Cdirect countConstants
            (slotStage k).val (preparedFiniteNestedForwardAllDegreeIsDirect k)
            (slotSeed k) gainLog stageLog)
          (preparedFiniteForwardWork exponent countConstants (slotStage k).val (slotSeed k))))
      (native k)
      (preparedFiniteNestedForwardFixedCenterThreshold exponent countConstants Bstruct gainLog stageLog k))
    (hsize : ∀ i, Real.exp (preparedFiniteForwardCumulative exponent countConstants degree
      (seed outerInner.val Bstruct)) ≤ (N i : ℝ)) :
    ∃ P : A.DegreeSourceProfile degree p e,
      P.inner.x = seed outerInner.val Bstruct ∧
      P.inner.gainLog = seed outerInner.val Bstruct ∧
      P.front.u = preparedFiniteForwardModelPrecision exponent countConstants 0
        (seed outerFront.val Bstruct) gainLog stageLog ∧
      P.front.pModel = preparedFiniteForwardWork exponent countConstants 0
        (seed outerFront.val Bstruct) ∧
      P.front.nativeBudget = native
        ((outerFront, 0, ⟨degree, Nat.lt_succ_of_le hdegree⟩, false) : Slots) := by
  let P := A.zeroLayerNestedDegreeSourceProfile q outerDepth innerDepth cutoff exponent Cprimitive
    Cslice Cdirect Bstruct gainLog stageLog Qstride Plate outerFront outerInner
    hdegree hcutoff hdepth hFrontExponent hInnerExponent hCslice hSliceExponent hInnerSlice
    hprimitive hBstruct hg hs hQstride hG hX hpFront hpInner hξ hsurplus hsurplus1 htrim hN
    hNative hsize
  refine ⟨P, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [P, zeroLayerNestedDegreeSourceProfile, zeroLayerDegreeSourceProfile,
    zeroLayerForwardFrontSourceProfile, preparedFiniteForwardFrontSourceProfile,
    preparedFixedCenterFrontSourceProfile, InnerSourceProfile.with_gain_detection,
    InnerSourceProfile.raise_gain, preparedFiniteForwardActualResourceLayerInnerSourceProfile,
    preparedFiniteForwardResourceLayerInnerSourceProfile,
    preparedFiniteNestedSourceNative, preparedFiniteNestedForwardAllDegreeDegree_slot,
    preparedFiniteNestedSourceMaster_front]

theorem exists_zeroLayerNestedDegreeSourceProfile_of_exponent_scalars
    (extra : ℕ) (outerFront outerInner : Fin (outerDepth + 1)) {degree e : ℕ} {p : ℝ}
    (hdegree : degree ≤ cutoff) (hcutoff : cutoff ≤ q) (hdepth : degree ≤ innerDepth)
    (hExponent : preparedFiniteNestedResourceLayerSourceExponent 0 q cutoff e
      Cprimitive Cdirect extra ≤ exponent)
    (hprimitive : 1 ≤ Cprimitive)
    (hBstruct : 0 ≤ Bstruct) (hg : gainLog ∈ Set.Icc 0 Bstruct)
    (hs : stageLog ∈ Set.Icc 0 Bstruct) (hQstride : Qstride ∈ Set.Icc 0 Bstruct)
    (hG : (Fintype.card G : ℝ) ≤ Bstruct)
    (hX : (Fintype.card X : ℝ) ≤ Bstruct)
    (hpFront : p ∈ Set.Icc 0 (seed outerFront.val Bstruct))
    (hpInner : p ≤ seed outerInner.val Bstruct)
    (hξ : ξ ≤ 1)
    {surplus L : ℝ} (hsurplus : 0 < surplus) (hsurplus1 : surplus ≤ 1)
    (htrim : τ = unconditionedSpatialTrimFraction (Fintype.card X) surplus)
    (hN : ∀ i, unconditionedSpatialWidthCutoff
      (allocatedExternalCandidateRootBudget B U b S) τ L ≤ (N i : ℝ))
    (hNative : ∀ k : Slots, A.NativeDetection (slotDegree k)
      ((preparedFiniteForwardParameter exponent countConstants (slotStage k).val (slotSeed k) + (preparedFiniteNestedSourceSliceExponent 0 cutoff Cprimitive)) ^
        (preparedFiniteNestedSourceSliceExponent 0 cutoff Cprimitive))
      ((preparedFiniteForwardDetectorPolynomial cutoff).eval₂ (Nat.castRingHom ℝ)
        (allocatedModelTestLog
          (preparedFiniteForwardPairedSourcePrecision exponent Cdirect countConstants
            (slotStage k).val (preparedFiniteNestedForwardAllDegreeIsDirect k)
            (slotSeed k) gainLog stageLog)
          (preparedFiniteForwardWork exponent countConstants (slotStage k).val (slotSeed k))))
      (native k)
      (preparedFiniteNestedForwardFixedCenterThreshold exponent countConstants Bstruct gainLog stageLog k))
    (hsize : ∀ i, Real.exp (preparedFiniteForwardCumulative exponent countConstants degree
      (seed outerInner.val Bstruct)) ≤ (N i : ℝ)) :
    ∃ P : A.DegreeSourceProfile degree p e,
      P.inner.x = seed outerInner.val Bstruct ∧
      P.inner.gainLog = seed outerInner.val Bstruct ∧
      P.front.u = preparedFiniteForwardModelPrecision exponent countConstants 0
        (seed outerFront.val Bstruct) gainLog stageLog ∧
      P.front.pModel = preparedFiniteForwardWork exponent countConstants 0
        (seed outerFront.val Bstruct) ∧
      P.front.nativeBudget = native
        ((outerFront, 0, ⟨degree, Nat.lt_succ_of_le hdegree⟩, false) : Slots) := by
  have he := preparedFiniteNestedResourceLayerSourceExponent_bounds 0 q cutoff e
    Cprimitive Cdirect extra exponent hExponent
  have hc := preparedFiniteNestedResourceLayerSourceSliceExponent_bounds 0 cutoff Cprimitive
  exact A.exists_zeroLayerNestedDegreeSourceProfile_scalars q outerDepth innerDepth cutoff exponent
    Cprimitive (preparedFiniteNestedSourceSliceExponent 0 cutoff Cprimitive) Cdirect
    Bstruct gainLog stageLog Qstride Plate outerFront outerInner
    hdegree hcutoff hdepth he.2.2.1 (he.2.2.2.2 degree hdegree)
    hc.1 he.2.2.2.1 (hc.2 degree hdegree)
    hprimitive hBstruct hg hs hQstride hG hX hpFront hpInner hξ hsurplus hsurplus1 htrim hN
    hNative hsize

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin 0 → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin 0 → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin 0 → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

namespace AllocatedExternalCandidateSampler

variable (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

local notation "countConstants" => degreeSourceCountConstants

local instance zeroLayerNestedDegreeFullScalarsSiteNonempty_r6fc1e9_1 : Nonempty A.Site := A.site_nonempty
variable (q outerDepth innerDepth cutoff exponent Cprimitive Cslice Cdirect : ℕ)
    (Bstruct gainLog stageLog Qstride Plate : ℝ)
local notation "Slots" => PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff
local notation "count" => Fintype.card (LayerSamplerVariables G I n B)
local notation "pnum" => (Fintype.card G : ℝ)
local notation "seed" => candidateNestedForwardSeed exponent countConstants innerDepth
local notation "native" => preparedFiniteNestedSourceNative q G count (Fintype.card X)
    (preparedFiniteForwardDetectorPolynomial cutoff) exponent Cdirect countConstants
    Bstruct pnum Qstride gainLog stageLog Plate
local notation "slotSeed" => preparedFiniteNestedForwardAllDegreeSeed exponent countConstants Bstruct
local notation "slotStage" => preparedFiniteNestedForwardAllDegreeStage
local notation "slotDegree" => preparedFiniteNestedForwardAllDegreeDegree
attribute [local irreducible] AllocatedExternalCandidateSampler.NativeDetection

theorem exists_zeroLayerNestedDegreeSourceProfile_full_scalars
    (outerFront outerInner : Fin (outerDepth + 1)) {degree e : ℕ} {p : ℝ}
    (hdegree : degree ≤ cutoff) (hcutoff : cutoff ≤ q) (hdepth : degree ≤ innerDepth)
    (hFrontExponent : preparedFiniteForwardFrontProfileExponent e ≤ exponent)
    (hInnerExponent : allocatedCandidateForwardScheduleExponent degree 0 Cprimitive
      (preparedFiniteForwardInnerSourceExponent Cdirect
        (preparedFiniteForwardActualNativeBudgetExponent q
          (preparedFiniteForwardDetectorPolynomial cutoff))) 2 ≤ exponent)
    (hCslice : 1 ≤ Cslice) (hSliceExponent : Cslice + 1 ≤ exponent)
    (hInnerSlice : allocatedCandidateStageSliceExponent degree 0 Cprimitive ≤ Cslice)
    (hprimitive : 1 ≤ Cprimitive)
    (hBstruct : 0 ≤ Bstruct) (hg : gainLog ∈ Set.Icc 0 Bstruct)
    (hs : stageLog ∈ Set.Icc 0 Bstruct) (hQstride : Qstride ∈ Set.Icc 0 Bstruct)
    (hG : (Fintype.card G : ℝ) ≤ Bstruct)
    (hX : (Fintype.card X : ℝ) ≤ Bstruct)
    (hpFront : p ∈ Set.Icc 0 (seed outerFront.val Bstruct))
    (hpInner : p ≤ seed outerInner.val Bstruct)
    (hξ : ξ ≤ 1)
    {surplus L : ℝ} (hsurplus : 0 < surplus) (hsurplus1 : surplus ≤ 1)
    (htrim : τ = unconditionedSpatialTrimFraction (Fintype.card X) surplus)
    (hN : ∀ i, unconditionedSpatialWidthCutoff
      (allocatedExternalCandidateRootBudget B U b S) τ L ≤ (N i : ℝ))
    (hNative : ∀ k : Slots, A.NativeDetection (slotDegree k)
      ((preparedFiniteForwardParameter exponent countConstants (slotStage k).val (slotSeed k) + Cslice) ^ Cslice)
      ((preparedFiniteForwardDetectorPolynomial cutoff).eval₂ (Nat.castRingHom ℝ)
        (allocatedModelTestLog
          (preparedFiniteForwardPairedSourcePrecision exponent Cdirect countConstants
            (slotStage k).val (preparedFiniteNestedForwardAllDegreeIsDirect k)
            (slotSeed k) gainLog stageLog)
          (preparedFiniteForwardWork exponent countConstants (slotStage k).val (slotSeed k))))
      (native k)
      (preparedFiniteNestedForwardFixedCenterThreshold exponent countConstants Bstruct gainLog stageLog k))
    (hsize : ∀ i, Real.exp (preparedFiniteForwardCumulative exponent countConstants degree
      (seed outerInner.val Bstruct)) ≤ (N i : ℝ)) :
    ∃ P : A.DegreeSourceProfile degree p e,
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
      P.inner.Csource = preparedFiniteForwardInnerSourceExponent Cdirect
        (preparedFiniteForwardActualNativeBudgetExponent q
          (preparedFiniteForwardDetectorPolynomial cutoff)) := by
  let P := A.zeroLayerNestedDegreeSourceProfile q outerDepth innerDepth cutoff exponent Cprimitive
    Cslice Cdirect Bstruct gainLog stageLog Qstride Plate outerFront outerInner
    hdegree hcutoff hdepth hFrontExponent hInnerExponent hCslice hSliceExponent hInnerSlice
    hprimitive hBstruct hg hs hQstride hG hX hpFront hpInner hξ hsurplus hsurplus1 htrim hN
    hNative hsize
  refine ⟨P, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [P, zeroLayerNestedDegreeSourceProfile, zeroLayerDegreeSourceProfile,
    zeroLayerForwardFrontSourceProfile, preparedFiniteForwardFrontSourceProfile,
    preparedFixedCenterFrontSourceProfile, InnerSourceProfile.with_gain_detection,
    InnerSourceProfile.raise_gain, preparedFiniteForwardActualResourceLayerInnerSourceProfile,
    preparedFiniteForwardResourceLayerInnerSourceProfile,
    preparedFiniteNestedSourceNative, preparedFiniteNestedForwardAllDegreeDegree_slot,
    preparedFiniteNestedSourceMaster_front]

theorem exists_zeroLayerNestedDegreeSourceProfile_of_exponent_full_scalars
    (extra : ℕ) (outerFront outerInner : Fin (outerDepth + 1)) {degree e : ℕ} {p : ℝ}
    (hdegree : degree ≤ cutoff) (hcutoff : cutoff ≤ q) (hdepth : degree ≤ innerDepth)
    (hExponent : preparedFiniteNestedResourceLayerSourceExponent 0 q cutoff e
      Cprimitive Cdirect extra ≤ exponent)
    (hprimitive : 1 ≤ Cprimitive)
    (hBstruct : 0 ≤ Bstruct) (hg : gainLog ∈ Set.Icc 0 Bstruct)
    (hs : stageLog ∈ Set.Icc 0 Bstruct) (hQstride : Qstride ∈ Set.Icc 0 Bstruct)
    (hG : (Fintype.card G : ℝ) ≤ Bstruct)
    (hX : (Fintype.card X : ℝ) ≤ Bstruct)
    (hpFront : p ∈ Set.Icc 0 (seed outerFront.val Bstruct))
    (hpInner : p ≤ seed outerInner.val Bstruct)
    (hξ : ξ ≤ 1)
    {surplus L : ℝ} (hsurplus : 0 < surplus) (hsurplus1 : surplus ≤ 1)
    (htrim : τ = unconditionedSpatialTrimFraction (Fintype.card X) surplus)
    (hN : ∀ i, unconditionedSpatialWidthCutoff
      (allocatedExternalCandidateRootBudget B U b S) τ L ≤ (N i : ℝ))
    (hNative : ∀ k : Slots, A.NativeDetection (slotDegree k)
      ((preparedFiniteForwardParameter exponent countConstants (slotStage k).val (slotSeed k) + (preparedFiniteNestedSourceSliceExponent 0 cutoff Cprimitive)) ^
        (preparedFiniteNestedSourceSliceExponent 0 cutoff Cprimitive))
      ((preparedFiniteForwardDetectorPolynomial cutoff).eval₂ (Nat.castRingHom ℝ)
        (allocatedModelTestLog
          (preparedFiniteForwardPairedSourcePrecision exponent Cdirect countConstants
            (slotStage k).val (preparedFiniteNestedForwardAllDegreeIsDirect k)
            (slotSeed k) gainLog stageLog)
          (preparedFiniteForwardWork exponent countConstants (slotStage k).val (slotSeed k))))
      (native k)
      (preparedFiniteNestedForwardFixedCenterThreshold exponent countConstants Bstruct gainLog stageLog k))
    (hsize : ∀ i, Real.exp (preparedFiniteForwardCumulative exponent countConstants degree
      (seed outerInner.val Bstruct)) ≤ (N i : ℝ)) :
    ∃ P : A.DegreeSourceProfile degree p e,
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
      P.inner.Csource = preparedFiniteForwardInnerSourceExponent Cdirect
        (preparedFiniteForwardActualNativeBudgetExponent q
          (preparedFiniteForwardDetectorPolynomial cutoff)) := by
  have he := preparedFiniteNestedResourceLayerSourceExponent_bounds 0 q cutoff e
    Cprimitive Cdirect extra exponent hExponent
  have hc := preparedFiniteNestedResourceLayerSourceSliceExponent_bounds 0 cutoff Cprimitive
  exact A.exists_zeroLayerNestedDegreeSourceProfile_full_scalars q outerDepth innerDepth cutoff exponent
    Cprimitive (preparedFiniteNestedSourceSliceExponent 0 cutoff Cprimitive) Cdirect
    Bstruct gainLog stageLog Qstride Plate outerFront outerInner
    hdegree hcutoff hdepth he.2.2.1 (he.2.2.2.2 degree hdegree)
    hc.1 he.2.2.2.1 (hc.2 degree hdegree)
    hprimitive hBstruct hg hs hQstride hG hX hpFront hpInner hξ hsurplus hsurplus1 htrim hN
    hNative hsize

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel AllocatedExternalCandidateSampler
open scoped Classical BigOperators NNReal TensorProduct

theorem exists_preparedScalarNestedPowerDegreeProfiles_of_exponent
    (s outerDepth innerDepth exponent Cprimitive Cdirect extra baseFloor : ℕ)
    (entropies : Fin (s + 1) → ℕ)
    (hA : 3 ≤ exponent) (hprimitive : 1 ≤ Cprimitive) (hdepth : s ≤ innerDepth)
    (hExponent : ∀ j, preparedFiniteNestedResourceLayerSourceExponent 0 (max s 1) s
      (entropies j) Cprimitive Cdirect extra ≤ exponent) :
    ∃ baseMin : ℕ, baseFloor ≤ baseMin ∧ 1 ≤ baseMin ∧
      ∀ basePower : ℕ, baseMin ≤ basePower →
      ∃ earlyExponent : ℕ, 2 ≤ earlyExponent ∧ ∀ latePower : ℕ,
        ∃ sizeExponent : ℕ, 2 ≤ sizeExponent ∧
          PreparedScalarNestedPowerDegreeProfiles s outerDepth innerDepth exponent Cprimitive Cdirect
            entropies basePower earlyExponent latePower sizeExponent := by
  let Cslice := preparedFiniteNestedSourceSliceExponent 0 s Cprimitive
  have he := preparedFiniteNestedResourceLayerSourceExponent_bounds
    0 (max s 1) s (entropies 0) Cprimitive Cdirect extra exponent (hExponent 0)
  obtain ⟨baseMin, hBaseMin, hPower⟩ := exists_preparedScalarNestedSchedule_power_detection
    s outerDepth innerDepth exponent Cslice Cdirect degreeSourceCountConstants hA he.2.2.2.1 hdepth
  obtain ⟨structMin, hStructMin, hstruct⟩ := exists_preparedScalarStructuralBasePower s
  let fullMin := max baseFloor (max baseMin structMin)
  refine ⟨fullMin, le_max_left _ _, hBaseMin.trans ((le_max_left _ _).trans (le_max_right _ _)), ?_⟩
  intro basePower hBasePower
  have hBase : baseMin ≤ basePower :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hBasePower
  have hStruct : structMin ≤ basePower :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hBasePower
  obtain ⟨earlyExponent, hEarly, hLate⟩ := hPower basePower hBase
  refine ⟨earlyExponent, hEarly, ?_⟩
  intro latePower
  obtain ⟨detectSize, hDetectSize, hDetection⟩ := hLate latePower
  obtain ⟨widthSize, _, hWidth⟩ := exists_preparedScalarSpatialWidthPower s latePower
  let sizeExponent := max detectSize widthSize
  refine ⟨sizeExponent, hDetectSize.trans (le_max_left _ _), ?_⟩
  intro nX p hp hX I₀ J₀ _ _ n₀ B₀ _ U₀ b₀ R₀ σ₀ S₀ hb₀ o₀ hR₀ hσ₀
    N poly₀ hmem₀ τ ξ₀ center₀ _ A₀ hξ htrim hscale hSupper hsize
  let Bstruct : ℝ := (p + 2) ^ basePower
  have hp0 : 0 ≤ p := by linarith
  have hB : 0 ≤ Bstruct := by dsimp [Bstruct]; positivity
  have hbase : 1 ≤ p + 2 := by linarith
  have hsizeDetect (i : Fin nX) : Real.exp ((p + 2) ^ detectSize) ≤ (N i : ℝ) :=
    (Real.exp_le_exp.mpr (pow_le_pow_right₀ hbase (le_max_left _ _))).trans (hsize i)
  obtain ⟨Plate, hPlate, hNative, hCumulative⟩ :=
    hDetection hp hX A₀ htrim hscale hSupper hsizeDetect
  have hN (i : Fin nX) : unconditionedSpatialWidthCutoff
      (allocatedExternalCandidateRootBudget B₀ U₀ b₀ S₀) τ 1 ≤ (N i : ℝ) := by
    rw [allocatedExternalCandidateRootBudget_zero_layers, Fintype.card_fin, htrim]
    exact (hWidth p hp nX hX S₀.value hSupper).trans
      ((Real.exp_le_exp.mpr (pow_le_pow_right₀ hbase (le_max_right _ _))).trans (hsize i))
  have hstructData := hstruct basePower hStruct p hp
  refine ⟨Plate, hPlate, hNative, hCumulative, ?_⟩
  intro entropySlot outerFront outerInner horder d hd pNorm hpNorm
  have hA2 : 2 ≤ exponent := by omega
  have hpInner : pNorm ≤ candidateNestedForwardSeed exponent degreeSourceCountConstants
      innerDepth outerInner.val Bstruct :=
    hpNorm.2.trans (candidateNestedForwardSeed_monotone exponent degreeSourceCountConstants
      innerDepth hA2 hB horder)
  have hG : (Fintype.card (Fin (scalarNativeDimension s)) : ℝ) ≤ Bstruct := by
    simpa only [Fintype.card_fin] using hstructData.1
  have hXstruct : (Fintype.card (Fin nX) : ℝ) ≤ Bstruct := by
    simpa only [Fintype.card_fin] using hX.trans hstructData.2.2.2
  have hsurplus1 : Real.exp (-p) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have htrim' : τ = unconditionedSpatialTrimFraction (Fintype.card (Fin nX)) (Real.exp (-p)) := by
    simpa only [Fintype.card_fin] using htrim
  have hdec : instDecidableEqFin nX = (fun a b : Fin nX => Classical.propDecidable (a = b)) :=
    Subsingleton.elim _ _
  rw [hdec] at hNative
  have hprofile := A₀.exists_zeroLayerNestedDegreeSourceProfile_of_exponent_scalars
    (max s 1) outerDepth innerDepth s exponent Cprimitive Cdirect Bstruct Bstruct Bstruct 0 Plate
    extra outerFront outerInner hd (le_max_left s 1) (hd.trans hdepth) (hExponent entropySlot)
    hprimitive hB ⟨hB, le_rfl⟩ ⟨hB, le_rfl⟩ ⟨le_rfl, hB⟩ hG hXstruct hpNorm hpInner
    hξ (Real.exp_pos (-p)) hsurplus1 htrim' hN
    (by simpa only [zeroLayerVariables_card, Fintype.card_fin] using hNative)
    (hCumulative outerInner ⟨d, Nat.lt_succ_of_le hd⟩)
  simpa only [zeroLayerVariables_card, Fintype.card_fin] using hprofile

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel AllocatedExternalCandidateSampler
open scoped Classical BigOperators NNReal TensorProduct

theorem exists_preparedScalarNestedPowerDegreeProfiles_full_of_exponent
    (s outerDepth innerDepth exponent Cprimitive Cdirect extra baseFloor : ℕ)
    (entropies : Fin (s + 1) → ℕ)
    (hA : 3 ≤ exponent) (hprimitive : 1 ≤ Cprimitive) (hdepth : s ≤ innerDepth)
    (hExponent : ∀ j, preparedFiniteNestedResourceLayerSourceExponent 0 (max s 1) s
      (entropies j) Cprimitive Cdirect extra ≤ exponent) :
    ∃ baseMin : ℕ, baseFloor ≤ baseMin ∧ 1 ≤ baseMin ∧
      ∀ basePower : ℕ, baseMin ≤ basePower →
      ∃ earlyExponent : ℕ, 2 ≤ earlyExponent ∧ ∀ latePower : ℕ,
        ∃ sizeExponent : ℕ, 2 ≤ sizeExponent ∧
          PreparedScalarNestedPowerDegreeProfilesFull s outerDepth innerDepth exponent Cprimitive Cdirect
            entropies basePower earlyExponent latePower sizeExponent := by
  obtain ⟨baseMin, _, hBaseMin, hPower⟩ := exists_preparedScalarNestedPowerDegreeProfiles_of_exponent
    s outerDepth innerDepth exponent Cprimitive Cdirect extra baseFloor entropies
    hA hprimitive hdepth hExponent
  obtain ⟨structMin, hStructMin, hstruct⟩ := exists_preparedScalarStructuralBasePower s
  let fullMin := max baseFloor (max baseMin structMin)
  refine ⟨fullMin, le_max_left _ _, hBaseMin.trans ((le_max_left _ _).trans (le_max_right _ _)), ?_⟩
  intro basePower hBasePower
  have hBase : baseMin ≤ basePower :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hBasePower
  have hStruct : structMin ≤ basePower :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hBasePower
  obtain ⟨earlyExponent, hEarly, hLate⟩ := hPower basePower hBase
  refine ⟨earlyExponent, hEarly, ?_⟩
  intro latePower
  obtain ⟨detectSize, hDetectSize, hDetection⟩ := hLate latePower
  obtain ⟨widthSize, _, hWidth⟩ := exists_preparedScalarSpatialWidthPower s latePower
  let sizeExponent := max detectSize widthSize
  refine ⟨sizeExponent, hDetectSize.trans (le_max_left _ _), ?_⟩
  intro nX p hp hX I₀ J₀ _ _ n₀ B₀ _ U₀ b₀ R₀ σ₀ S₀ hb₀ o₀ hR₀ hσ₀
    N poly₀ hmem₀ τ ξ₀ center₀ _ A₀ hξ htrim hscale hSupper hsize
  let Bstruct : ℝ := (p + 2) ^ basePower
  have hp0 : 0 ≤ p := by linarith
  have hB : 0 ≤ Bstruct := by dsimp [Bstruct]; positivity
  have hbase : 1 ≤ p + 2 := by linarith
  have hsizeDetect (i : Fin nX) : Real.exp ((p + 2) ^ detectSize) ≤ (N i : ℝ) :=
    (Real.exp_le_exp.mpr (pow_le_pow_right₀ hbase (le_max_left _ _))).trans (hsize i)
  obtain ⟨Plate, hPlate, hNative, hCumulative, _⟩ :=
    hDetection hp hX A₀ hξ htrim hscale hSupper hsizeDetect
  have hN (i : Fin nX) : unconditionedSpatialWidthCutoff
      (allocatedExternalCandidateRootBudget B₀ U₀ b₀ S₀) τ 1 ≤ (N i : ℝ) := by
    rw [allocatedExternalCandidateRootBudget_zero_layers, Fintype.card_fin, htrim]
    exact (hWidth p hp nX hX S₀.value hSupper).trans
      ((Real.exp_le_exp.mpr (pow_le_pow_right₀ hbase (le_max_right _ _))).trans (hsize i))
  have hstructData := hstruct basePower hStruct p hp
  refine ⟨Plate, hPlate, hNative, hCumulative, ?_⟩
  intro entropySlot outerFront outerInner horder d hd pNorm hpNorm
  have hA2 : 2 ≤ exponent := by omega
  have hpInner : pNorm ≤ candidateNestedForwardSeed exponent degreeSourceCountConstants
      innerDepth outerInner.val Bstruct :=
    hpNorm.2.trans (candidateNestedForwardSeed_monotone exponent degreeSourceCountConstants
      innerDepth hA2 hB horder)
  have hG : (Fintype.card (Fin (scalarNativeDimension s)) : ℝ) ≤ Bstruct := by
    simpa only [Fintype.card_fin] using hstructData.1
  have hXstruct : (Fintype.card (Fin nX) : ℝ) ≤ Bstruct := by
    simpa only [Fintype.card_fin] using hX.trans hstructData.2.2.2
  have hsurplus1 : Real.exp (-p) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have htrim' : τ = unconditionedSpatialTrimFraction (Fintype.card (Fin nX)) (Real.exp (-p)) := by
    simpa only [Fintype.card_fin] using htrim
  have hdec : instDecidableEqFin nX = (fun a b : Fin nX => Classical.propDecidable (a = b)) :=
    Subsingleton.elim _ _
  rw [hdec] at hNative
  have hprofile := A₀.exists_zeroLayerNestedDegreeSourceProfile_of_exponent_full_scalars
    (max s 1) outerDepth innerDepth s exponent Cprimitive Cdirect Bstruct Bstruct Bstruct 0 Plate
    extra outerFront outerInner hd (le_max_left s 1) (hd.trans hdepth) (hExponent entropySlot)
    hprimitive hB ⟨hB, le_rfl⟩ ⟨hB, le_rfl⟩ ⟨le_rfl, hB⟩ hG hXstruct hpNorm hpInner
    hξ (Real.exp_pos (-p)) hsurplus1 htrim' hN
    (by simpa only [zeroLayerVariables_card, Fintype.card_fin] using hNative)
    (hCumulative outerInner ⟨d, Nat.lt_succ_of_le hd⟩)
  simpa only [zeroLayerVariables_card, Fintype.card_fin] using hprofile

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel AllocatedExternalCandidateSampler
open scoped Classical BigOperators NNReal TensorProduct
attribute [local irreducible] AllocatedExternalCandidateSampler.DegreeGlobalizationAt

theorem exists_scalarNestedSourceDegreeGlobalization_s2_oai
    (s initial extra baseFloor : ℕ) :
    ∃ exponent : ℕ, 3 ≤ exponent ∧
      ∃ baseMin : ℕ, baseFloor ≤ baseMin ∧ 1 ≤ baseMin ∧
        ∀ basePower : ℕ, baseMin ≤ basePower →
        ∃ earlyExponent : ℕ, 2 ≤ earlyExponent ∧ ∀ latePower : ℕ,
          ∃ sizeExponent : ℕ, 2 ≤ sizeExponent ∧
            ScalarNestedSourceDegreeGlobalization s initial exponent basePower
              earlyExponent latePower sizeExponent := by
  classical
  obtain ⟨Cstep, hCstep, hglobal⟩ := exists_degreeGlobalizationAt_of_nested_source_profiles s
  let eMax := candidateNestedDegreeNetBound s initial
  let Pdetect := preparedFiniteForwardDetectorPolynomial s
  let Csource := preparedFiniteNestedResourceLayerSourceExponent 0 (max s 1) s eMax 1 1 extra
  let Cfront := preparedFiniteNestedFrontFitExponent (max s 1) Pdetect Cstep
  let Crec := candidateSourceRecursiveUniformExponent s 1
  let exponent := 3 + Csource + Cfront + Crec
  have hA : 3 ≤ exponent := by dsimp [exponent]; omega
  have hsource : Csource ≤ exponent := by dsimp [exponent]; omega
  have hfront : Cfront ≤ exponent := by dsimp [exponent]; omega
  have hrec : Crec ≤ exponent := by dsimp [exponent]; omega
  obtain ⟨sourceMin, hSourceFloor, hSourceMin, hSources⟩ :=
    exists_preparedScalarNestedPowerDegreeProfiles_full_of_exponent
      s (2 * s) (s + 1) exponent 1 1 extra baseFloor (fun _ => eMax)
      hA (by omega) (by omega) (fun _ => hsource)
  obtain ⟨structMin, hStructMin, hstruct⟩ := exists_preparedScalarStructuralBasePower s
  refine ⟨exponent, hA, max sourceMin structMin,
    hSourceFloor.trans (le_max_left _ _), hSourceMin.trans (le_max_left _ _), ?_⟩
  intro basePower hBase
  have hBaseSource := (le_max_left sourceMin structMin).trans hBase
  have hBaseStruct := (le_max_right sourceMin structMin).trans hBase
  obtain ⟨earlyExponent, hEarly, hLate⟩ := hSources basePower hBaseSource
  refine ⟨earlyExponent, hEarly, ?_⟩
  intro latePower
  obtain ⟨sizeExponent, hSize, hFull⟩ := hLate latePower
  refine ⟨sizeExponent, hSize, ?_⟩
  intro nX p hp hnX I₀ E₀ J₀ _ _ n₀ B₀ _ U₀ b₀ R₀ σ₀ S₀ hb₀ o₀ hR₀ hσ₀
    N poly₀ hmem₀ τ ξ₀ center₀ _ A₀ hξ htrim hS hSupper hN Bstruct finalSeed hFinal weight
  let : Nonempty (Fin (scalarNativeDimension s)) :=
    ⟨⟨0, scalarNativeDimension_pos s⟩⟩
  have hB : 0 ≤ Bstruct := by dsimp [Bstruct]; positivity
  have hA2 : 2 ≤ exponent := by omega
  have hstructData := hstruct basePower hBaseStruct p hp
  have hG : (Fintype.card (Fin (scalarNativeDimension s)) : ℝ) ≤ Bstruct := by
    simpa only [Fintype.card_fin] using hstructData.1
  have hX : (Fintype.card (Fin nX) : ℝ) ≤ Bstruct := by
    simpa only [Fintype.card_fin] using hnX.trans hstructData.2.2.2
  have hVars : (Fintype.card (LayerSamplerVariables
      (Fin (scalarNativeDimension s)) I₀ n₀ B₀) : ℝ) ≤ Bstruct := by
    simpa only [zeroLayerVariables_card] using hG
  obtain ⟨Plate, hPlate, hNative, hCumulative, hProfiles⟩ :=
    hFull hp hnX A₀ hξ htrim hS hSupper hN
  let seed := candidateNestedForwardSeed exponent degreeSourceCountConstants (s + 1)
  have hSeed (r : ℕ) : 0 ≤ seed r Bstruct :=
    candidateNestedForwardSeed_nonneg exponent degreeSourceCountConstants (s + 1) r hB
  have profiles (j : Fin s) := hProfiles (0 : Fin (s + 1))
    ⟨2 * j.val, by omega⟩ ⟨2 * j.val + 1, by omega⟩ (by simp only [Fin.le_def]; omega)
    (s - (j.val + 1) + 1) (by omega) (seed (2 * j.val) Bstruct) ⟨hSeed _, le_rfl⟩
  choose P hP using profiles
  let source (j : Fin s) := (P j).mono_netExponent (hSeed _)
    (candidateNestedDegreeNetExponent_le_bound s initial (Nat.le_of_lt j.isLt))
  have hinner (j : Fin s) : (source j).inner.x = seed (2 * j.val + 1) Bstruct :=
    (hP j).1
  have hgain (j : Fin s) : (source j).inner.x ≤ (source j).inner.gainLog := by
    change (P j).inner.x ≤ (P j).inner.gainLog
    rw [(hP j).1, (hP j).2.1]
  have hfit (j : Fin s) : ((source j).front.familyParameter + 2) ^ Cstep ≤
      (source j).inner.x := by
    rw [hinner j]
    exact (source j).front.familyParameter_pow_le_next_seed (max s 1) Pdetect Cstep
      exponent 1 degreeSourceCountConstants (2 * s) (s + 1) s
      ⟨2 * j.val, by omega⟩ Bstruct (scalarNativeDimension s) 0 Bstruct Bstruct Plate
      hfront (by omega) hB (by omega) (by omega)
      ⟨Nat.cast_nonneg _, by simpa only [Fintype.card_fin] using hG⟩
      ⟨le_rfl, hB⟩ ⟨hB, le_rfl⟩ ⟨hB, le_rfl⟩ (by simpa only [Nat.cast_zero] using hB)
      hVars hX hG ⟨hSeed _, le_rfl⟩ (hP j).2.2.1 (hP j).2.2.2.1
      (by simpa only [zeroLayerVariables_card, Fintype.card_fin, source,
        DegreeSourceProfile.mono_netExponent, FrontSourceProfile.mono_netExponent,
        Pdetect, Bstruct] using (hP j).2.2.2.2.1)
  have hrecursive (j : Fin s) : (source j).inner.recursiveParameter ≤
      seed (2 * (j.val + 1)) Bstruct :=
    (source j).inner.recursiveParameter_le_next_degree_seed_of_uniform
      1 exponent (s + 1) s j.val (by omega) hrec le_rfl hB
      (hP j).2.2.2.2.2.1 (hP j).2.2.2.2.2.2.1 (hinner j)
  exact hglobal (E := E₀) A₀ weight initial exponent (s + 1) Bstruct source
    hA2 hB hVars hinner hfit hgain hFinal hrecursive

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.exists_scalarNestedSourceDegreeGlobalization_s2_oai := @OAI.Erdos3.VectorPolynomial.exists_scalarNestedSourceDegreeGlobalization_s2_oai
