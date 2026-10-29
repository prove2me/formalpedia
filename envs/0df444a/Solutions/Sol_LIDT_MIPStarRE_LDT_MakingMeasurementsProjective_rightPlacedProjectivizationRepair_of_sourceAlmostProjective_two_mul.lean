-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.rightPlacedProjectivizationRepair_of_sourceAlmostProjective_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T15:23:02.283265+00:00
-- url     : https://prove2.me/submissions/2e483954-5fa9-49f3-80cc-01284f5b024e

-- Generated proof for MIPStarRE.LDT.MakingMeasurementsProjective.rightPlacedProjectivizationRepair_of_sourceAlmostProjective_two_mul.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_MeasurementLift
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFUniformAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_LocalityPreservingRepair
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Projectivization
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_LayerAlgebra
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_PositiveGram_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_PositiveGram_Rows
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_PositiveGram_Sigma
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_ProjectorApprox
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_AlmostProjective
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_QCompleteness
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_RankReduction_LowRank
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_RankReduction_Sigma
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_TruncationCombinatorics
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_SpectralTruncation_Conversion
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_SpectralTruncation_ProjectiveNonMeasurement
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Local
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CompletionTransfer
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_ApproxDelta
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteHilbert
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_LIDT_MIPStarRE_Quantum_ProjectorONB
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Theorems.Thm_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_qSDD_rightPlaced_zeroProjSubMeas_le_one
import Theorems.Thm_LIDT_MIPStarRE_LDT_rightTensor_sub

namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

namespace LIDT

/- Source helpers from MIPStarRE/LDT/MakingMeasurementsProjective/LocalityPreservingRepair.lean. -/
/-!
# Section 5 — Locality-preserving projectivization repair

This file proves the locality-preserving repair route for the late Section 5
`Q/X/XHat/P` argument.

## Scope

The **spectral-truncation stage** (the first part of the proof of rounding
to projectors) is already proved by
`spectralTruncationStatement_of_sourceAlmostProjective` in
`MakingMeasurementsProjective/SpectralTruncation/ProjectiveNonMeasurement.lean`,
which is fully proved via
`projectiveNonMeasurement_of_sourceAlmostProjective_full`. Proofs that
require the spectral truncation statement should call that declaration directly.

The main result recorded here:

- **`leftLiftedProjectivizationRepair`** — paper origin
  `references/ldt-paper/orthonormalization.tex` lines 534–860 (rank
  reduction and the `Q`/`√Q` completeness setup) and 862–1194 (the
  `X`/`X̂`/`P` algebra producing the lifted projective sub-measurement,
  including the final triangle-inequality assembly).  The formal proof below
  follows that local `Q/X/XHat/P` route by passing to the left marginal state,
  constructing the local projective family there, and transporting the final
  estimate back to left lifts.

The theorem proved here is the direct output of that route under a normalized
bipartite state and the source almost-projective estimate for the left-lifted
measurement. It is stated directly in terms of this estimate, rather than in
terms of a separate repair-input assumption, and provides the unconditional
repair step used by the orthonormalization theorem.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

noncomputable section



























private lemma trace_mul_rightTensor_eq_sum_trace_rightDiagBlock
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (M : MIPStarRE.Quantum.Op (ιA × ιB)) (X : MIPStarRE.Quantum.Op ιB) :
    Matrix.trace (M * rightTensor (ι₁ := ιA) X) =
      ∑ a : ιA, Matrix.trace (rightDiagBlock M a * X) := by
  classical
  let e : ((ιA × ιB) × ιB) ≃ (ιA × (ιB × ιB)) :=
    { toFun := fun x => (x.1.1, (x.1.2, x.2))
      invFun := fun x => ((x.1, x.2.1), x.2.2)
      left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
      right_inv := fun ⟨_, ⟨_, _⟩⟩ => rfl }
  simpa [rightDiagBlock, Matrix.trace, Matrix.mul_apply, rightTensor, Matrix.one_apply,
    Fintype.sum_prod_type, Finset.sum_sigma', e] using
    (e.sum_comp (fun y : ιA × (ιB × ιB) =>
      M (y.1, y.2.1) (y.1, y.2.2) * X y.2.2 y.2.1))

private lemma normalizedTrace_rightMarginalDensity_mul_eq
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Nonempty ιA]
    (ρ : MIPStarRE.Quantum.Op (ιA × ιB)) (X : MIPStarRE.Quantum.Op ιB) :
    MIPStarRE.Quantum.normalizedTrace (rightMarginalDensity ρ * X) =
      MIPStarRE.Quantum.normalizedTrace (ρ * rightTensor (ι₁ := ιA) X) := by
  have hcard : ((Fintype.card ιA : Error) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold MIPStarRE.Quantum.normalizedTrace rightMarginalDensity
  rw [smul_mul_assoc, Matrix.trace_smul, Matrix.sum_mul, Matrix.trace_sum]
  rw [trace_mul_rightTensor_eq_sum_trace_rightDiagBlock]
  simp [Fintype.card_prod]
  ring

private lemma rightMarginalState_isNormalized {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Nonempty ιA]
    {ψ : QuantumState (ιA × ιB)} (hψ : ψ.IsNormalized) :
    (rightMarginalState ψ).IsNormalized := by
  unfold QuantumState.IsNormalized
  have hnorm :
      MIPStarRE.Quantum.normalizedTrace (rightMarginalDensity ψ.density) =
        MIPStarRE.Quantum.normalizedTrace ψ.density := by
    simpa [rightTensor_one] using
      normalizedTrace_rightMarginalDensity_mul_eq (ρ := ψ.density)
        (X := (1 : MIPStarRE.Quantum.Op ιB))
  simpa [rightMarginalState] using hnorm.trans hψ

private lemma rightMarginal_ev_eq {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Nonempty ιA]
    (ψ : QuantumState (ιA × ιB)) (X : MIPStarRE.Quantum.Op ιB) :
    ev ψ (rightTensor (ι₁ := ιA) X) = ev (rightMarginalState ψ) X := by
  unfold ev
  rw [← Complex.ofReal_inj]
  simp [normalizedTrace_rightMarginalDensity_mul_eq (ρ := ψ.density) (X := X),
    rightMarginalState]











private lemma sddOpRel_rightPlaced_of_ev_eq
    {Question Outcome : Type*} {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB)) (φ : QuantumState ιB)
    (𝒟 : Distribution Question)
    (A B : IdxOpFamily Question Outcome ιB) (δ : Error)
    (hev : ∀ X : MIPStarRE.Quantum.Op ιB,
      ev ψ (rightTensor (ι₁ := ιA) X) = ev φ X) :
    SDDOpRel φ 𝒟 A B δ →
    SDDOpRel ψ 𝒟
      (fun q => OpFamily.rightPlacedOpFamily (ιA := ιA) (A q))
      (fun q => OpFamily.rightPlacedOpFamily (ιA := ιA) (B q)) δ := by
  intro ⟨hAB⟩
  constructor
  unfold sddErrorOp at *
  calc
    avgOver 𝒟
        (fun q =>
          qSDDOp ψ
            (OpFamily.rightPlacedOpFamily (ιA := ιA) (A q))
            (OpFamily.rightPlacedOpFamily (ιA := ιA) (B q)))
      = avgOver 𝒟 (fun q => qSDDOp φ (A q) (B q)) := by
          refine avgOver_congr 𝒟 _ _ ?_
          intro q
          unfold qSDDOp qSDDCore
          refine Finset.sum_congr rfl ?_
          intro a _
          simp [OpFamily.rightPlacedOpFamily, rightTensor_sub,
            rightTensor_mul_rightTensor, hev]
    _ ≤ δ := hAB

private lemma sddRel_of_rightPlaced_sddOpRel {Outcome : Type*}
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    {ψ : QuantumState (ιA × ιB)} {B : Measurement Outcome ιB}
    {R : OpFamily Outcome ιB}
    {P : ProjSubMeas Outcome ιB}
    {δ : Error}
    (hR : ∀ a : Outcome, R.outcome a = P.outcome a)
    (hclose :
      SDDOpRel ψ (uniformDistribution Unit)
        (fun _ => OpFamily.rightPlacedOpFamily (ιA := ιA) (B.toSubMeas : OpFamily Outcome ιB))
        (fun _ => OpFamily.rightPlacedOpFamily (ιA := ιA) R)
        δ) :
    SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) B.toSubMeas))
      (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) P.toSubMeas))
      δ := by
  refine ⟨?_⟩
  have herror :
      sddError ψ (uniformDistribution Unit)
          (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) B.toSubMeas))
          (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) P.toSubMeas)) =
        sddErrorOp ψ (uniformDistribution Unit)
          (fun _ => OpFamily.rightPlacedOpFamily (ιA := ιA) (B.toSubMeas : OpFamily Outcome ιB))
          (fun _ => OpFamily.rightPlacedOpFamily (ιA := ιA) R) := by
    unfold sddError sddErrorOp
    refine avgOver_congr (uniformDistribution Unit) _ _ ?_
    intro u
    unfold qSDD qSDDOp qSDDCore
    refine Finset.sum_congr rfl ?_
    intro a _
    simp [constSubMeasFamily, rightPlacedSubMeas, SubMeas.toOpFamily,
      OpFamily.rightPlacedOpFamily, hR a]
  rw [herror]
  exact hclose.squaredDistanceBound









end

end MIPStarRE.LDT.MakingMeasurementsProjective

end

end LIDT

open LIDT
/-!
# Section 5 — Locality-preserving projectivization repair

This file proves the locality-preserving repair route for the late Section 5
`Q/X/XHat/P` argument.

## Scope

The **spectral-truncation stage** (the first part of the proof of rounding
to projectors) is already proved by
`spectralTruncationStatement_of_sourceAlmostProjective` in
`MakingMeasurementsProjective/SpectralTruncation/ProjectiveNonMeasurement.lean`,
which is fully proved via
`projectiveNonMeasurement_of_sourceAlmostProjective_full`. Proofs that
require the spectral truncation statement should call that declaration directly.

The main result recorded here:

- **`leftLiftedProjectivizationRepair`** — paper origin
  `references/ldt-paper/orthonormalization.tex` lines 534–860 (rank
  reduction and the `Q`/`√Q` completeness setup) and 862–1194 (the
  `X`/`X̂`/`P` algebra producing the lifted projective sub-measurement,
  including the final triangle-inequality assembly).  The formal proof below
  follows that local `Q/X/XHat/P` route by passing to the left marginal state,
  constructing the local projective family there, and transporting the final
  estimate back to left lifts.

The theorem proved here is the direct output of that route under a normalized
bipartite state and the source almost-projective estimate for the left-lifted
measurement. It is stated directly in terms of this estimate, rather than in
terms of a separate repair-input assumption, and provides the unconditional
repair step used by the orthonormalization theorem.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

noncomputable section

theorem solution
    {Outcome : Type*} {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState (ιA × ιB)) (hψ : ψ.IsNormalized)
    (B : _root_.LIDT.MIPStarRE.LDT.Measurement Outcome ιB) (ζ : _root_.LIDT.MIPStarRE.LDT.Error) (hζ : 0 ≤ ζ)
    (hsource :
      ∑ a, _root_.LIDT.MIPStarRE.LDT.ev ψ
        ((_root_.LIDT.MIPStarRE.LDT.rightLiftedMeasurement (ιA := ιA) B).outcome a -
          (_root_.LIDT.MIPStarRE.LDT.rightLiftedMeasurement (ιA := ιA) B).outcome a *
            (_root_.LIDT.MIPStarRE.LDT.rightLiftedMeasurement (ιA := ιA) B).outcome a) ≤ 2 * ζ) :
    ∃ P : _root_.LIDT.MIPStarRE.LDT.ProjSubMeas Outcome ιB,
      _root_.LIDT.MIPStarRE.LDT.SDDRel ψ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
        (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily (_root_.LIDT.MIPStarRE.LDT.rightPlacedSubMeas (ιA := ιA) B.toSubMeas))
        (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily (_root_.LIDT.MIPStarRE.LDT.rightPlacedSubMeas (ιA := ιA) P.toSubMeas))
        (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.orthonormalizationMainLemmaError ζ) := by
  classical
  let : DecidableEq Outcome := Classical.decEq Outcome
  rcases _root_.LIDT.MIPStarRE.LDT.QuantumState.IsNormalized.nonempty (ι := ιA × ιB) hψ with ⟨⟨i, j⟩⟩
  let : Nonempty ιA := ⟨i⟩
  let : Nonempty ιB := ⟨j⟩
  let φ : _root_.LIDT.MIPStarRE.LDT.QuantumState ιB := rightMarginalState ψ
  have hφ : φ.IsNormalized := rightMarginalState_isNormalized hψ
  have hterm : ∀ a : Outcome,
      _root_.LIDT.MIPStarRE.LDT.ev ψ
        ((_root_.LIDT.MIPStarRE.LDT.rightLiftedMeasurement (ιA := ιA) B).outcome a -
          (_root_.LIDT.MIPStarRE.LDT.rightLiftedMeasurement (ιA := ιA) B).outcome a *
            (_root_.LIDT.MIPStarRE.LDT.rightLiftedMeasurement (ιA := ιA) B).outcome a) =
      _root_.LIDT.MIPStarRE.LDT.ev φ (B.outcome a - B.outcome a * B.outcome a) := by
    intro a
    simpa [φ, _root_.LIDT.MIPStarRE.LDT.rightLiftedMeasurement, _root_.LIDT.MIPStarRE.LDT.rightPlacedSubMeas, _root_.LIDT.MIPStarRE.LDT.rightTensor_sub,
      _root_.LIDT.MIPStarRE.LDT.rightTensor_mul_rightTensor] using
      (rightMarginal_ev_eq (ψ := ψ) (X := B.outcome a - B.outcome a * B.outcome a))
  have hsourceLocal :
      ∑ a, _root_.LIDT.MIPStarRE.LDT.ev φ (B.outcome a - B.outcome a * B.outcome a) ≤ 2 * ζ := by
    simpa [hterm] using hsource
  by_cases hζ_small : ζ ≤ 1 / (4 : _root_.LIDT.MIPStarRE.LDT.Error)
  · have hprojective : _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.projectiveNonMeasurement φ B ζ :=
      _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.projectiveNonMeasurement_of_sourceAlmostProjective_two_mul_full
        φ B ζ hφ hsourceLocal
    obtain ⟨R, hR⟩ := hprojective
    have hSpectralLocal : _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.SpectralTruncationStatement φ B ζ :=
      _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.spectralTruncationStatement_of_witness φ B ζ R hR
    obtain ⟨qLayer, hRank⟩ :=
      _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.projectiveLowRankSum_of_spectralTruncationStatement φ B ζ hφ hζ
        hζ_small hSpectralLocal hsourceLocal
    by_cases hsigma : Nonempty (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.FiniteHilbertSpace.sigmaFinCarrier
        (fun a : Outcome => (qLayer.q.outcome a).rank))
    · let := hsigma
      obtain ⟨_xHat, _hxHat_coisometry, _hxHat_mixed, data, hq, _hx, _hxHat, hQP⟩ :=
        _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.pQApprox_ofRankReductionSigmaRangePositiveGram φ B ζ hRank hφ hζ hζ_small
      have hBQ :
          _root_.LIDT.MIPStarRE.LDT.SDDOpRel φ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
            (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.constOpFamily (B.toSubMeas : _root_.LIDT.MIPStarRE.LDT.OpFamily Outcome ιB))
            (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.constOpFamily data.qLayer.q) (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.roundingToProjectiveError ζ) := by
        simpa [hq, _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.sigmaRangeQLayer] using hRank.closeness
      have hBP_local :
          _root_.LIDT.MIPStarRE.LDT.SDDOpRel φ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
            (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.constOpFamily (B.toSubMeas : _root_.LIDT.MIPStarRE.LDT.OpFamily Outcome ιB))
            (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.constOpFamily (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.PFamily data)) (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.orthonormalizationMainLemmaError ζ) := by
        exact _root_.LIDT.MIPStarRE.LDT.Preliminaries.sddOpRel_mono φ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
          (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.constOpFamily (B.toSubMeas : _root_.LIDT.MIPStarRE.LDT.OpFamily Outcome ιB))
          (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.constOpFamily (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.PFamily data))
          (2 * (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.roundingToProjectiveError ζ + 30 * _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.zetaQuarterRoot ζ))
          (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.orthonormalizationMainLemmaError ζ)
          (_root_.LIDT.MIPStarRE.LDT.Preliminaries.sddOpRel_triangle φ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
            (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.constOpFamily (B.toSubMeas : _root_.LIDT.MIPStarRE.LDT.OpFamily Outcome ιB))
            (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.constOpFamily data.qLayer.q)
            (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.constOpFamily (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.PFamily data))
            (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.roundingToProjectiveError ζ) (30 * _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.zetaQuarterRoot ζ) hBQ hQP)
          (projectivizationRepair_small_error_bound hζ hζ_small)
      have hLifted :
          _root_.LIDT.MIPStarRE.LDT.SDDOpRel ψ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
            (fun _ => _root_.LIDT.MIPStarRE.LDT.OpFamily.rightPlacedOpFamily (ιA := ιA) (B.toSubMeas : _root_.LIDT.MIPStarRE.LDT.OpFamily Outcome ιB))
            (fun _ => _root_.LIDT.MIPStarRE.LDT.OpFamily.rightPlacedOpFamily (ιA := ιA) (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.PFamily data))
            (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.orthonormalizationMainLemmaError ζ) := by
        refine sddOpRel_rightPlaced_of_ev_eq
          (ιA := ιA) (ιB := ιB) ψ φ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
          (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.constOpFamily (B.toSubMeas : _root_.LIDT.MIPStarRE.LDT.OpFamily Outcome ιB))
          (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.constOpFamily (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.PFamily data))
          (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.orthonormalizationMainLemmaError ζ) ?_ hBP_local
        intro X
        exact rightMarginal_ev_eq ψ X
      exact ⟨_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.qxpProjSubMeas data,
        sddRel_of_rightPlaced_sddOpRel
          (R := _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.PFamily data) (P := _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.qxpProjSubMeas data)
          (fun a => by
            rw [_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.qxpProjSubMeas_outcome]
            rfl)
          hLifted⟩
    · have hQzero_rank : ∀ a : Outcome, (qLayer.q.outcome a).rank = 0 := by
        intro a
        by_contra hrank
        have hpos : 0 < (qLayer.q.outcome a).rank := Nat.pos_of_ne_zero hrank
        have : Nonempty (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.FiniteHilbertSpace.sigmaFinCarrier
            (fun a : Outcome => (qLayer.q.outcome a).rank)) := by
          refine ⟨⟨Fintype.equivFin Outcome a, ⟨0, ?_⟩⟩⟩
          simpa [Fintype.equivFin] using hpos
        exact hsigma this
      have hQzero : ∀ a : Outcome, qLayer.q.outcome a = 0 := by
        intro a
        exact matrix_eq_zero_of_rank_eq_zero (qLayer.q.outcome a) (hQzero_rank a)
      have hQ_lifted :
          _root_.LIDT.MIPStarRE.LDT.SDDOpRel ψ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
            (fun _ => _root_.LIDT.MIPStarRE.LDT.OpFamily.rightPlacedOpFamily (ιA := ιA) (B.toSubMeas : _root_.LIDT.MIPStarRE.LDT.OpFamily Outcome ιB))
            (fun _ => _root_.LIDT.MIPStarRE.LDT.OpFamily.rightPlacedOpFamily (ιA := ιA) qLayer.q)
            (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.roundingToProjectiveError ζ) := by
        refine sddOpRel_rightPlaced_of_ev_eq
          (ιA := ιA) (ιB := ιB) ψ φ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
          (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.constOpFamily (B.toSubMeas : _root_.LIDT.MIPStarRE.LDT.OpFamily Outcome ιB))
          (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.constOpFamily qLayer.q) (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.roundingToProjectiveError ζ) ?_ hRank.closeness
        intro X
        exact rightMarginal_ev_eq ψ X
      exact ⟨_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.zeroProjSubMeas (Outcome := Outcome) (ι := ιB),
        ⟨le_trans
          (sddRel_of_rightPlaced_sddOpRel
            (R := qLayer.q) (P := _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.zeroProjSubMeas (Outcome := Outcome) (ι := ιB))
            hQzero hQ_lifted).squaredDistanceBound
          (roundingToProjectiveError_le_orthonormalizationMainLemmaError
            hζ hζ_small)⟩⟩
  · refine ⟨_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.zeroProjSubMeas (Outcome := Outcome) (ι := ιB), ?_⟩
    have hzero :
        _root_.LIDT.MIPStarRE.LDT.qSDD ψ (_root_.LIDT.MIPStarRE.LDT.rightPlacedSubMeas (ιA := ιA) B.toSubMeas)
          (_root_.LIDT.MIPStarRE.LDT.rightPlacedSubMeas (ιA := ιA)
            (_root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.zeroProjSubMeas (Outcome := Outcome) (ι := ιB)).toSubMeas) ≤ 1 :=
      _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.qSDD_rightPlaced_zeroProjSubMeas_le_one ψ hψ B.toSubMeas
    have hbound : 1 ≤ _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.orthonormalizationMainLemmaError ζ :=
      one_le_orthonormalizationMainLemmaError_of_quarter_lt (lt_of_not_ge hζ_small)
    constructor
    simpa [_root_.LIDT.MIPStarRE.LDT.sddError, _root_.LIDT.MIPStarRE.LDT.avgOver, _root_.LIDT.MIPStarRE.LDT.uniformDistribution, _root_.LIDT.MIPStarRE.LDT.constSubMeasFamily]
      using (le_trans hzero hbound)
