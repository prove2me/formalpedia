-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.ProjStrat.qBipartiteMatchMass_roleRegisterProjMeas_arbitrary_eq_average
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:57:38.590907+00:00
-- url     : https://prove2.me/submissions/154341d2-6403-4103-9e9b-72b1f5d5f8e0

-- Generated proof for MIPStarRE.LDT.ProjStrat.qBipartiteMatchMass_roleRegisterProjMeas_arbitrary_eq_average.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyBiProjUnsymmetrization
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyBiProj_DirectSum
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyBiProj_Measurements
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyFailures
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Algebra
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Core
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.ProjStrat
end LIDT.MIPStarRE.LDT.ProjStrat

namespace LIDT

/- Source helpers from MIPStarRE/LDT/Test/StrategyBiProjUnsymmetrization.lean. -/
/-!
# Heterogeneous role-register measurement extraction

This file contains the principal-block extraction used to unsymmetrize a
measurement on the heterogeneous role-register space
`Role × (ιA ⊕ ιB)`.  The Alice extraction is the block indexed by
`(Role.A, Sum.inl _)`; the Bob extraction is the block indexed by
`(Role.B, Sum.inr _)`.

These are the two-space analogues of the same-space extractions in
`MIPStarRE.LDT.Test.Unsymmetrization`.  They preserve POVM completeness, but
they do not assert that arbitrary principal blocks of a projective measurement
remain projective.  As in the paper proof, projectivity is restored later by
the projectivization step.

## References

* `references/ldt-paper/inductive_step.tex`, lines 84--109.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT

namespace ProjStrat

/-! ### Principal blocks of heterogeneous role-register operators -/













































end ProjStrat

namespace SubMeas

















end SubMeas

namespace Measurement













end Measurement

namespace ProjStrat

/-! ### Extraction on the constructed role-register measurements -/

/-! ### Trace compression for occupied role-register sectors -/

private lemma trace_single_tensor_mul_eq_trace_submatrix {β α : Type*}
    [Fintype β] [DecidableEq β] [Fintype α] [DecidableEq α]
    (b : β) (X : MIPStarRE.Quantum.Op α)
    (Y : MIPStarRE.Quantum.Op (β × α)) :
    Matrix.trace (opTensor (Matrix.single b b (1 : ℂ)) X * Y) =
      Matrix.trace (X * Y.submatrix (fun i : α => (b, i)) (fun i : α => (b, i))) := by
  classical
  unfold Matrix.trace
  simp only [Matrix.diag_apply, Matrix.mul_apply]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  calc
    ∑ x : β, ∑ y : α, ∑ x_1 : β, ∑ y_1 : α,
        Matrix.single b b (1 : ℂ) x x_1 * X y y_1 * Y (x_1, y_1) (x, y)
      = ∑ x : β, ∑ y : α, ∑ y_1 : α,
        Matrix.single b b (1 : ℂ) x b * X y y_1 * Y (b, y_1) (x, y) := by
          refine Finset.sum_congr rfl ?_
          intro x _
          refine Finset.sum_congr rfl ?_
          intro y _
          rw [Fintype.sum_eq_single b (by
            intro x_1 hx
            have hx' : b ≠ x_1 := fun h => hx h.symm
            simp [Matrix.single, hx'])]
    _ = ∑ y : α, ∑ y_1 : α, X y y_1 * Y (b, y_1) (b, y) := by
          rw [Fintype.sum_eq_single b (by
            intro x hx
            have hx' : b ≠ x := fun h => hx h.symm
            simp [Matrix.single, hx'])]
          simp [Matrix.single]
    _ = ∑ y : α, ∑ y_1 : α, X y y_1 * Y (b, y_1) (b, y) := rfl

private lemma rolePairProj_eq_single_pair (rL rR : Role) :
    rolePairProj rL rR = Matrix.single (rL, rR) (rL, rR) (1 : ℂ) := by
  ext p q
  rcases p with ⟨pL, pR⟩
  rcases q with ⟨qL, qR⟩
  cases rL <;> cases rR <;> cases pL <;> cases pR <;> cases qL <;> cases qR <;>
    simp [rolePairProj, roleProj, opTensor]









private lemma trace_rolePairDirectSumCond_mul {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (rL rR : Role)
    (X : MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB))
    (Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB × RoleRegisterLocal ιA ιB)) :
    Matrix.trace (rolePairDirectSumCond rL rR X * Y) =
      Matrix.trace (X * Y.submatrix
        (rolePairSectorEmbedding rL rR) (rolePairSectorEmbedding rL rR)) := by
  classical
  let e := roleRegisterPairLocalEquiv ιA ιB
  let Y' : MIPStarRE.Quantum.Op
      ((Role × Role) × (LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB)) :=
    Matrix.reindex e.symm e.symm Y
  have hY : Y = Matrix.reindex e e Y' := by
    ext x y
    simp [Y', e]
  rw [hY]
  unfold rolePairDirectSumCond
  change Matrix.trace ((Matrix.reindexAlgEquiv ℂ ℂ e) (opTensor (rolePairProj rL rR) X) *
      (Matrix.reindexAlgEquiv ℂ ℂ e) Y') = _
  rw [← map_mul (Matrix.reindexAlgEquiv ℂ ℂ e)]
  simp only [Matrix.coe_reindexAlgEquiv]
  rw [Matrix.trace_reindex]
  rw [rolePairProj_eq_single_pair]
  rw [trace_single_tensor_mul_eq_trace_submatrix]
  rfl

private lemma trace_localPairABBlock_mul_arbitrary {ιA ιB : Type*}
    [Fintype ιA] [Fintype ιB]
    (X : MIPStarRE.Quantum.Op (ιA × ιB))
    (Y : MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB)) :
    Matrix.trace (localPairABBlock X * Y) =
      Matrix.trace (X * Y.submatrix
        localPairABEmbedding localPairABEmbedding) := by
  unfold Matrix.trace
  rw [Fintype.sum_prod_type]
  simp only [Matrix.diag_apply, Matrix.mul_apply]
  simp_rw [Fintype.sum_prod_type]
  simp [localPairABBlock, localPairABEmbedding]

private lemma trace_localPairBABlock_mul_arbitrary {ιA ιB : Type*}
    [Fintype ιA] [Fintype ιB]
    (X : MIPStarRE.Quantum.Op (ιB × ιA))
    (Y : MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB)) :
    Matrix.trace (localPairBABlock X * Y) =
      Matrix.trace (X * Y.submatrix
        localPairBAEmbedding localPairBAEmbedding) := by
  unfold Matrix.trace
  rw [Fintype.sum_prod_type]
  simp only [Matrix.diag_apply, Matrix.mul_apply]
  simp_rw [Fintype.sum_prod_type]
  simp [localPairBABlock, localPairBAEmbedding]



private lemma opTensor_localDirectSum_roleLocalBlock_AB_submatrix
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : MIPStarRE.Quantum.Op ιA) (Bfill : MIPStarRE.Quantum.Op ιB)
    (Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) :
    (opTensor (localDirectSumBlock A Bfill) (roleRegisterRoleLocalBlock Role.B Y)).submatrix
      localPairABEmbedding localPairABEmbedding =
    opTensor A (extractRoleRegisterBobBlock Y) := by
  ext z w
  simp [localPairABEmbedding, roleRegisterRoleLocalBlock,
    extractRoleRegisterBobBlock, opTensor]

private lemma opTensor_localDirectSum_roleLocalBlock_BA_submatrix
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (Afill : MIPStarRE.Quantum.Op ιA) (B : MIPStarRE.Quantum.Op ιB)
    (Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) :
    (opTensor (localDirectSumBlock Afill B) (roleRegisterRoleLocalBlock Role.A Y)).submatrix
      localPairBAEmbedding localPairBAEmbedding =
    opTensor B (extractRoleRegisterAliceBlock Y) := by
  ext z w
  simp [localPairBAEmbedding, roleRegisterRoleLocalBlock,
    extractRoleRegisterAliceBlock, opTensor]

private lemma opTensor_roleBlock_roleRegister_AB_submatrix
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A Afill : MIPStarRE.Quantum.Op ιA) (B Bfill : MIPStarRE.Quantum.Op ιB)
    (Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) :
    (opTensor
        (roleBlock (localDirectSumBlock A Bfill) (localDirectSumBlock Afill B))
        Y).submatrix
      (rolePairSectorEmbedding Role.A Role.B) (rolePairSectorEmbedding Role.A Role.B) =
      opTensor (localDirectSumBlock A Bfill) (roleRegisterRoleLocalBlock Role.B Y) := by
  ext z w
  simp [rolePairSectorEmbedding, roleRegisterRoleLocalBlock, opTensor]

private lemma opTensor_roleBlock_roleRegister_BA_submatrix
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A Afill : MIPStarRE.Quantum.Op ιA) (B Bfill : MIPStarRE.Quantum.Op ιB)
    (Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) :
    (opTensor
        (roleBlock (localDirectSumBlock A Bfill) (localDirectSumBlock Afill B))
        Y).submatrix
      (rolePairSectorEmbedding Role.B Role.A) (rolePairSectorEmbedding Role.B Role.A) =
      opTensor (localDirectSumBlock Afill B) (roleRegisterRoleLocalBlock Role.A Y) := by
  ext z w
  simp [rolePairSectorEmbedding, roleRegisterRoleLocalBlock, opTensor]

private lemma trace_heterogeneousSwapDensity_mul_opTensor {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (X : MIPStarRE.Quantum.Op (ιA × ιB))
    (A : MIPStarRE.Quantum.Op ιA) (B : MIPStarRE.Quantum.Op ιB) :
    Matrix.trace (heterogeneousSwapDensity X * opTensor B A) =
      Matrix.trace (X * opTensor A B) := by
  rw [← heterogeneousSwapDensity_opTensor]
  rw [← heterogeneousSwapDensity_mul]
  unfold heterogeneousSwapDensity
  rw [Matrix.trace_reindex]

private lemma ev_roleRegisterSymmState_roleBlock_arbitrary
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB))
    (A Afill : MIPStarRE.Quantum.Op ιA) (B Bfill : MIPStarRE.Quantum.Op ιB)
    (Y : MIPStarRE.Quantum.Op (RoleRegisterLocal ιA ιB)) :
    ev (roleRegisterSymmState ψ)
        (opTensor
          (roleBlock (localDirectSumBlock A Bfill) (localDirectSumBlock Afill B))
          Y) =
      (1 / 2 : Error) * ev ψ (opTensor A (extractRoleRegisterBobBlock Y)) +
        (1 / 2 : Error) * ev ψ (opTensor (extractRoleRegisterAliceBlock Y) B) := by
  unfold ev roleRegisterSymmState
  change Complex.re (MIPStarRE.Quantum.normalizedTrace
      (((roleRegisterDensityScale ιA ιB : ℂ) •
      rolePairDirectSumCond Role.A Role.B (localPairABBlock ψ.density) +
      (roleRegisterDensityScale ιA ιB : ℂ) •
        rolePairDirectSumCond Role.B Role.A
          (localPairBABlock (heterogeneousSwapDensity ψ.density))) *
        opTensor
          (roleBlock (localDirectSumBlock A Bfill) (localDirectSumBlock Afill B))
          Y)) =
    (1 / 2 : Error) * ev ψ (opTensor A (extractRoleRegisterBobBlock Y)) +
      (1 / 2 : Error) * ev ψ (opTensor (extractRoleRegisterAliceBlock Y) B)
  rw [Matrix.add_mul, MIPStarRE.Quantum.normalizedTrace_add]
  rw [smul_mul_assoc, smul_mul_assoc]
  rw [MIPStarRE.Quantum.normalizedTrace_smul, MIPStarRE.Quantum.normalizedTrace_smul]
  unfold MIPStarRE.Quantum.normalizedTrace
  rw [trace_rolePairDirectSumCond_mul]
  rw [opTensor_roleBlock_roleRegister_AB_submatrix]
  rw [trace_localPairABBlock_mul_arbitrary]
  rw [opTensor_localDirectSum_roleLocalBlock_AB_submatrix]
  rw [trace_rolePairDirectSumCond_mul]
  rw [opTensor_roleBlock_roleRegister_BA_submatrix]
  rw [trace_localPairBABlock_mul_arbitrary]
  rw [opTensor_localDirectSum_roleLocalBlock_BA_submatrix]
  rw [trace_heterogeneousSwapDensity_mul_opTensor]
  let T₁ : ℂ :=
    Matrix.trace (ψ.density * opTensor A (extractRoleRegisterBobBlock Y)) /
      ((Fintype.card ιA : ℂ) * (Fintype.card ιB : ℂ))
  let T₂ : ℂ :=
    Matrix.trace (ψ.density * opTensor (extractRoleRegisterAliceBlock Y) B) /
      ((Fintype.card ιA : ℂ) * (Fintype.card ιB : ℂ))
  have hA : (Fintype.card ιA : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hB : (Fintype.card ιB : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hS : (Fintype.card (LocalCarrierSum ιA ιB) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hscale (T : ℂ) :
      (roleRegisterDensityScale ιA ιB : ℂ) *
          (T / (Fintype.card (RoleRegisterLocal ιA ιB × RoleRegisterLocal ιA ιB) : ℂ)) =
        (1 / 2 : ℂ) *
          (T / ((Fintype.card ιA : ℂ) * (Fintype.card ιB : ℂ))) := by
    unfold roleRegisterDensityScale RoleRegisterLocal
    rw [Fintype.card_prod, Fintype.card_prod]
    have hRole : Fintype.card Role = 2 := by decide
    rw [hRole]
    field_simp [hA, hB, hS, Nat.cast_pow, Nat.cast_mul]
    norm_num [Nat.cast_pow, Nat.cast_mul]
    field_simp [hA, hB]
  rw [show ev ψ (opTensor A (extractRoleRegisterBobBlock Y)) = Complex.re T₁ by
    unfold ev MIPStarRE.Quantum.normalizedTrace
    rw [Fintype.card_prod]
    norm_num [Nat.cast_mul]
    rfl]
  rw [show ev ψ (opTensor (extractRoleRegisterAliceBlock Y) B) = Complex.re T₂ by
    unfold ev MIPStarRE.Quantum.normalizedTrace
    rw [Fintype.card_prod]
    norm_num [Nat.cast_mul]
    rfl]
  rw [show (roleRegisterDensityScale ιA ιB : ℂ) *
        (Matrix.trace (ψ.density * opTensor A (extractRoleRegisterBobBlock Y)) /
          (Fintype.card (RoleRegisterLocal ιA ιB × RoleRegisterLocal ιA ιB) : ℂ)) =
      (1 / 2 : ℂ) * T₁ by
    subst T₁
    exact hscale (Matrix.trace (ψ.density * opTensor A (extractRoleRegisterBobBlock Y)))]
  rw [show (roleRegisterDensityScale ιA ιB : ℂ) *
        (Matrix.trace (ψ.density * opTensor (extractRoleRegisterAliceBlock Y) B) /
          (Fintype.card (RoleRegisterLocal ιA ιB × RoleRegisterLocal ιA ιB) : ℂ)) =
      (1 / 2 : ℂ) * T₂ by
    subst T₂
    exact hscale (Matrix.trace (ψ.density * opTensor (extractRoleRegisterAliceBlock Y) B))]
  norm_num [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]

private lemma ev_roleRegisterSymmState_roleRegisterProjMeas_arbitrary_outcome
    {Outcome ιA ιB : Type*}
    [Inhabited Outcome] [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB))
    (MA : ProjMeas Outcome ιA) (MB : ProjMeas Outcome ιB)
    (G : Measurement Outcome (RoleRegisterLocal ιA ιB)) (a : Outcome) :
    ev (roleRegisterSymmState ψ)
        (opTensor ((roleRegisterProjMeas MA MB).outcome a) (G.outcome a)) =
      (1 / 2 : Error) *
          ev ψ (opTensor (MA.outcome a) ((G.extractRoleRegisterBob).outcome a)) +
        (1 / 2 : Error) *
          ev ψ (opTensor ((G.extractRoleRegisterAlice).outcome a) (MB.outcome a)) := by
  let fillerA : ProjMeas Outcome ιA := ProjMeas.trivialDistinguishedOutcome default
  let fillerB : ProjMeas Outcome ιB := ProjMeas.trivialDistinguishedOutcome default
  change ev (roleRegisterSymmState ψ)
      (opTensor
        (roleBlock
          (localDirectSumBlock (MA.outcome a) (fillerB.outcome a))
          (localDirectSumBlock (fillerA.outcome a) (MB.outcome a)))
        (G.outcome a)) =
    (1 / 2 : Error) *
        ev ψ (opTensor (MA.outcome a) (extractRoleRegisterBobBlock (G.outcome a))) +
      (1 / 2 : Error) *
        ev ψ (opTensor (extractRoleRegisterAliceBlock (G.outcome a)) (MB.outcome a))
  exact ev_roleRegisterSymmState_roleBlock_arbitrary ψ
    (MA.outcome a) (fillerA.outcome a) (MB.outcome a) (fillerB.outcome a) (G.outcome a)

















end ProjStrat

end MIPStarRE.LDT

end

end LIDT

open LIDT
/-!
# Heterogeneous role-register measurement extraction

This file contains the principal-block extraction used to unsymmetrize a
measurement on the heterogeneous role-register space
`Role × (ιA ⊕ ιB)`.  The Alice extraction is the block indexed by
`(Role.A, Sum.inl _)`; the Bob extraction is the block indexed by
`(Role.B, Sum.inr _)`.

These are the two-space analogues of the same-space extractions in
`MIPStarRE.LDT.Test.Unsymmetrization`.  They preserve POVM completeness, but
they do not assert that arbitrary principal blocks of a projective measurement
remain projective.  As in the paper proof, projectivity is restored later by
the projectivization step.

## References

* `references/ldt-paper/inductive_step.tex`, lines 84--109.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.LDT




open LIDT.MIPStarRE.LDT.ProjStrat

/-! ### Extraction on the constructed role-register measurements -/

/-! ### Trace compression for occupied role-register sectors -/

theorem solution
    {Outcome ιA ιB : Type*}
    [Inhabited Outcome] [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState (ιA × ιB))
    (MA : _root_.LIDT.MIPStarRE.LDT.ProjMeas Outcome ιA) (MB : _root_.LIDT.MIPStarRE.LDT.ProjMeas Outcome ιB)
    (G : _root_.LIDT.MIPStarRE.LDT.Measurement Outcome (_root_.LIDT.MIPStarRE.LDT.ProjStrat.RoleRegisterLocal ιA ιB)) :
    _root_.LIDT.MIPStarRE.LDT.qBipartiteMatchMass (_root_.LIDT.MIPStarRE.LDT.ProjStrat.roleRegisterSymmState ψ)
        (_root_.LIDT.MIPStarRE.LDT.ProjStrat.roleRegisterProjMeas MA MB).toSubMeas G.toSubMeas =
      (_root_.LIDT.MIPStarRE.LDT.qBipartiteMatchMass ψ MA.toSubMeas (G.extractRoleRegisterBob).toSubMeas +
        _root_.LIDT.MIPStarRE.LDT.qBipartiteMatchMass ψ (G.extractRoleRegisterAlice).toSubMeas MB.toSubMeas) / 2 := by
  unfold _root_.LIDT.MIPStarRE.LDT.qBipartiteMatchMass
  calc
    ∑ a : Outcome,
        _root_.LIDT.MIPStarRE.LDT.ev (_root_.LIDT.MIPStarRE.LDT.ProjStrat.roleRegisterSymmState ψ)
          (_root_.LIDT.MIPStarRE.LDT.opTensor ((_root_.LIDT.MIPStarRE.LDT.ProjStrat.roleRegisterProjMeas MA MB).outcome a) (G.outcome a))
      = ∑ a : Outcome,
          ((1 / 2 : _root_.LIDT.MIPStarRE.LDT.Error) *
              _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.opTensor (MA.outcome a) ((G.extractRoleRegisterBob).outcome a)) +
            (1 / 2 : _root_.LIDT.MIPStarRE.LDT.Error) *
              _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.opTensor ((G.extractRoleRegisterAlice).outcome a) (MB.outcome a))) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          exact ev_roleRegisterSymmState_roleRegisterProjMeas_arbitrary_outcome ψ MA MB G a
    _ = (1 / 2 : _root_.LIDT.MIPStarRE.LDT.Error) * ∑ a : Outcome,
          _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.opTensor (MA.outcome a) ((G.extractRoleRegisterBob).outcome a)) +
        (1 / 2 : _root_.LIDT.MIPStarRE.LDT.Error) * ∑ a : Outcome,
          _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.opTensor ((G.extractRoleRegisterAlice).outcome a) (MB.outcome a)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = (∑ a : Outcome,
            _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.opTensor (MA.outcome a) ((G.extractRoleRegisterBob).outcome a)) +
          ∑ a : Outcome,
            _root_.LIDT.MIPStarRE.LDT.ev ψ (_root_.LIDT.MIPStarRE.LDT.opTensor ((G.extractRoleRegisterAlice).outcome a) (MB.outcome a))) / 2 := by
          ring
