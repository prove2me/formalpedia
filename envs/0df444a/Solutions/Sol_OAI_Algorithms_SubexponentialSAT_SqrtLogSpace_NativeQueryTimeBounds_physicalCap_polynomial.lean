-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryTimeBounds.physicalCap_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:36:28.136392+00:00
-- url     : https://prove2.me/submissions/9ef1ba76-bc79-49e4-9d4d-835e0b010861

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ081S099
import Definitions.Def_OAIQ081S100

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorTableBudgets
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed polynomial bounds for the actual factor-table service. The scalar
allowance includes physical signed-word lengths; it never bounds the integer
value of an exponential modulus or numerator in unary. All ambient source
rows and every specialized incidence record are included. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableBudgets
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SubexpLiftRing
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.Polynomial
open OAI.Algorithms.SubexponentialSAT.Subexp
open FactorTableNative

private theorem scalar_allowance_ordinary :
    Ordinary (fun S => LayoutSourceValuesProgram.Native.scalarAllowance S S S S S) := by
  unfold LayoutSourceValuesProgram.Native.scalarAllowance
    LayoutProgramScalar.FromCounts.binomialCost LayoutProgramScalar.numeratorPrepareCost
    LayoutProgramScalar.numeratorFoldCost LayoutProgramScalar.termGrowth
  exact (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 14) ordinary_id) (ordinary_mul (ordinary_const 7) ordinary_id)) (ordinary_const 15)) (ordinary_add (ordinary_mul (ordinary_const 3) ordinary_id) (ordinary_const 4))) (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 12) ordinary_id) (ordinary_mul (ordinary_mul (ordinary_mul (ordinary_const 400) (ordinary_add ordinary_id (ordinary_const 1))) (ordinary_add ordinary_id (ordinary_const 1))) (ordinary_add ordinary_id (ordinary_const 5)))) (ordinary_mul (ordinary_mul (ordinary_const 110) (ordinary_add ordinary_id (ordinary_const 1))) (ordinary_add (ordinary_add ordinary_id (ordinary_add ordinary_id (ordinary_const 1))) (ordinary_const 4)))) (ordinary_const 32))) (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 9) ordinary_id) (ordinary_mul (ordinary_const 3) ordinary_id)) (ordinary_mul ordinary_id (ordinary_add (ordinary_add (ordinary_add (ordinary_mul ordinary_id (ordinary_add (ordinary_mul (ordinary_const 28) ordinary_id) (ordinary_const 34))) (ordinary_mul (ordinary_const 140) ordinary_id)) (ordinary_mul (ordinary_const 18) ordinary_id)) (ordinary_const 222)))) (ordinary_mul (ordinary_const 3) (ordinary_mul ordinary_id (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 8) ordinary_id) (ordinary_mul (ordinary_const 2) ordinary_id)) (ordinary_const 9))))) (ordinary_const 24)) (ordinary_add (ordinary_mul (ordinary_mul (ordinary_const 200000000) (ordinary_add ordinary_id (ordinary_const 1))) (ordinary_pow (ordinary_add (ordinary_add (ordinary_mul ordinary_id (ordinary_add (ordinary_mul (ordinary_const 14) (ordinary_add (ordinary_mul (ordinary_const 2) ordinary_id) ordinary_id)) (ordinary_const 52))) (ordinary_add (ordinary_mul (ordinary_const 2) ordinary_id) ordinary_id)) (ordinary_const 4)) 2)) (ordinary_const 1))) (ordinary_const 1))) (ordinary_mul (ordinary_const 4) (ordinary_mul ordinary_id ordinary_id))) (ordinary_const 6)) (ordinary_const 1))

private theorem numerator_allowance_ordinary :
    Ordinary (fun S => LayoutSourceValuesProgram.Native.numeratorAllowance S S S S S S) := by
  unfold LayoutSourceValuesProgram.Native.numeratorAllowance
    MatrixExtendedEntryProgram.guardStageCost MatrixEntryProgram.scanStageCost
    CollisionProgram.typeWidth
  exact (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 36) (ordinary_mul (ordinary_mul (ordinary_const 2) ordinary_id) ordinary_id)) (ordinary_mul (ordinary_const 4) (ordinary_add (ordinary_mul (ordinary_const 14) (ordinary_mul ordinary_id ordinary_id)) (ordinary_const 17)))) (ordinary_mul (ordinary_const 203) (ordinary_mul ordinary_id ordinary_id))) (ordinary_const 265)) (ordinary_add (ordinary_mul (ordinary_const 4) (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 9) (ordinary_mul ordinary_id ordinary_id)) (ordinary_mul ordinary_id (ordinary_add (ordinary_mul (ordinary_const 14) ordinary_id) (ordinary_const 17)))) (ordinary_mul (ordinary_const 30) ordinary_id)) (ordinary_const 43))) (ordinary_const 1))) (ordinary_add (ordinary_mul (ordinary_const 81) ordinary_id) (ordinary_const 107))) (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 8) (ordinary_mul ordinary_id ordinary_id)) (ordinary_mul (ordinary_const 8) ordinary_id)) (ordinary_const 24))) (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 7) ordinary_id) (ordinary_const 5)) (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 36) (ordinary_mul (ordinary_mul (ordinary_const 2) ordinary_id) ordinary_id)) (ordinary_mul (ordinary_const 4) (ordinary_add (ordinary_mul (ordinary_const 14) (ordinary_mul ordinary_id ordinary_id)) (ordinary_const 17)))) (ordinary_mul (ordinary_const 203) (ordinary_mul ordinary_id ordinary_id))) (ordinary_const 265))) (ordinary_add (ordinary_mul ordinary_id (ordinary_add (ordinary_mul (ordinary_const 208) ordinary_id) (ordinary_const 149))) (ordinary_const 3)))) (ordinary_mul (ordinary_const 7) ordinary_id)) scalar_allowance_ordinary) (ordinary_const 20))

private theorem value_table_ordinary :
    Ordinary (fun S => LayoutSourceValuesProgram.Native.polynomialBudget S S S S S S S S) := by
  unfold LayoutSourceValuesProgram.Native.polynomialBudget
    LayoutSourceValuesProgram.Native.callbackBudget
    LayoutSourceValuesProgram.Native.integerBits IntegerRingLiftProgram.polynomialBudget
    LayoutProgramScalar.termGrowth
  simp only [RingProgram.ternary_baseWidth]
  exact (ordinary_add (ordinary_mul ordinary_id (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul ordinary_id numerator_allowance_ordinary) (ordinary_const 1)) (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_mul ordinary_id (ordinary_add (ordinary_mul (ordinary_const 14) (ordinary_add (ordinary_mul (ordinary_const 2) ordinary_id) ordinary_id)) (ordinary_const 52))) (ordinary_add (ordinary_add (ordinary_mul (ordinary_mul (ordinary_const 100000) (ordinary_pow (ordinary_add ordinary_id (ordinary_const 1)) 3)) (ordinary_pow (ordinary_add (ordinary_mul (ordinary_const 2) ordinary_id) (ordinary_const 1)) 2)) (ordinary_mul (ordinary_mul (ordinary_const 80) ordinary_id) (ordinary_mul (ordinary_const 2) ordinary_id))) (ordinary_const 110))) (ordinary_mul (ordinary_mul (ordinary_const 200000) (ordinary_pow (ordinary_add ordinary_id (ordinary_const 1)) 3)) (ordinary_pow (ordinary_add (ordinary_mul (ordinary_const 2) ordinary_id) (ordinary_const 1)) 2))) (ordinary_mul (ordinary_mul (ordinary_const 203) ordinary_id) (ordinary_mul (ordinary_const 2) ordinary_id))) (ordinary_const 251))) (ordinary_mul (ordinary_const 2) (ordinary_mul ordinary_id (ordinary_add (ordinary_mul (ordinary_const 14) (ordinary_add (ordinary_mul (ordinary_const 2) ordinary_id) ordinary_id)) (ordinary_const 52))))) (ordinary_const 6)) (ordinary_mul (ordinary_const 6) (ordinary_mul ordinary_id (ordinary_mul (ordinary_const 2) ordinary_id)))) (ordinary_const 16))) (ordinary_const 14))

private theorem source_bound_ordinary {f : ℕ → ℕ} (hf : Ordinary f) :
    Ordinary (fun S => UniversalRowSourceBound.sourceBound (f S)) := by
  unfold UniversalRowSourceBound.sourceBound UniversalRowSourceBound.dataBound
    UniversalRowSourceBound.outerLoopBound UniversalRowSourceBound.termBound
    UniversalRowSourceBound.factorLoopBound UniversalRowSourceBound.factorCallbackBound
    UniversalRowSourceBound.inputBound UniversalRowSourceBound.rowBytes
    UniversalRowSourceBound.termBytes UniversalRowSourceBound.factorsBytes
    UniversalRowSourceBound.factorBytes UniversalRowSourceBound.indicesBound
  exact (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 10) (ordinary_add (ordinary_const 1) (ordinary_mul (ordinary_add (ordinary_mul (ordinary_const 2) hf) (ordinary_const 2)) hf))) (ordinary_mul (ordinary_const 13) hf)) (ordinary_mul (ordinary_const 6) hf)) (ordinary_const 40)) (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 7) (ordinary_add (ordinary_const 1) (ordinary_mul (ordinary_add (ordinary_mul (ordinary_const 2) hf) (ordinary_const 2)) hf))) (ordinary_const 8)) (ordinary_mul hf (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 6) hf) (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul hf (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 28) hf) (ordinary_mul (ordinary_const 14) hf)) (ordinary_const 51))) (ordinary_mul (ordinary_const 30) hf)) (ordinary_mul (ordinary_const 15) hf)) (ordinary_const 63)) (ordinary_mul (ordinary_const 7) (ordinary_add (ordinary_const 1) (ordinary_mul (ordinary_add (ordinary_mul (ordinary_const 2) hf) (ordinary_const 2)) hf)))) (ordinary_mul hf (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 6) hf) (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_add (ordinary_mul (ordinary_const 28) hf) (ordinary_const 60)) hf) (ordinary_mul (ordinary_const 9) hf)) (ordinary_mul (ordinary_const 80) hf)) (ordinary_const 140))) (ordinary_const 7)))) (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 24) (ordinary_add hf hf)) (ordinary_mul (ordinary_const 8) (ordinary_add (ordinary_const 1) (ordinary_mul (ordinary_add (ordinary_mul (ordinary_const 2) (ordinary_add (ordinary_mul (ordinary_const 4) hf) (ordinary_const 2))) (ordinary_const 2)) hf)))) (ordinary_const 42))) (ordinary_mul (ordinary_const 2) hf)) (ordinary_mul (ordinary_const 2) hf)) (ordinary_const 20))) (ordinary_const 7))))) (ordinary_mul (ordinary_const 8) hf)) (ordinary_const 11)) (ordinary_mul (ordinary_const 2048) (ordinary_pow (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 2) hf) (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 2) hf) (ordinary_const 2)) (ordinary_mul (ordinary_add (ordinary_mul (ordinary_const 2) (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 4) hf) (ordinary_const 2)) (ordinary_add (ordinary_const 1) (ordinary_mul (ordinary_add (ordinary_mul (ordinary_const 2) (ordinary_add (ordinary_mul (ordinary_const 4) hf) (ordinary_const 2))) (ordinary_const 2)) hf)))) (ordinary_const 2)) hf))) (ordinary_const 1)) 2))) (ordinary_const 4))

private theorem source_length_ordinary : Ordinary UniversalRowSourceBound.sourceLengthBound := by
  unfold UniversalRowSourceBound.sourceLengthBound UniversalRowSourceBound.inputBound
    UniversalRowSourceBound.rowBytes UniversalRowSourceBound.termBytes
    UniversalRowSourceBound.factorsBytes UniversalRowSourceBound.factorBytes
  exact (ordinary_mul (ordinary_const 300) (ordinary_pow (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 2) ordinary_id) (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 2) ordinary_id) (ordinary_const 2)) (ordinary_mul (ordinary_add (ordinary_mul (ordinary_const 2) (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 4) ordinary_id) (ordinary_const 2)) (ordinary_add (ordinary_const 1) (ordinary_mul (ordinary_add (ordinary_mul (ordinary_const 2) (ordinary_add (ordinary_mul (ordinary_const 4) ordinary_id) (ordinary_const 2))) (ordinary_const 2)) ordinary_id)))) (ordinary_const 2)) ordinary_id))) (ordinary_const 1)) 2))

private theorem workspace_ordinary : Ordinary workspaceEnvelope := by
  unfold workspaceEnvelope UniversalRowSourceBound.indicesBound
  exact (ordinary_add (ordinary_add ordinary_id (ordinary_mul ordinary_id (ordinary_mul ordinary_id (ordinary_mul (ordinary_const 2) ordinary_id)))) (ordinary_add (ordinary_const 1) (ordinary_mul (ordinary_add (ordinary_mul (ordinary_const 2) ordinary_id) (ordinary_const 2)) ordinary_id)))

private theorem uniform_ordinary : Ordinary uniformEnvelope := by
  unfold uniformEnvelope UniversalRowMismatchTypes.extractBudget
    UniversalRowMismatchBound.mismatchBound CollisionProgram.typeWidth
  simp only [Fin.val_zero, Nat.zero_add]
  exact (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add value_table_ordinary (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 36) (ordinary_mul (ordinary_mul (ordinary_const 2) ordinary_id) ordinary_id)) (ordinary_mul (ordinary_const 4) (ordinary_add (ordinary_mul (ordinary_const 14) (ordinary_mul ordinary_id ordinary_id)) (ordinary_const 17)))) (ordinary_mul (ordinary_const 203) (ordinary_mul ordinary_id ordinary_id))) (ordinary_const 265)) (ordinary_mul (ordinary_const 400) (ordinary_pow (ordinary_add ordinary_id (ordinary_const 1)) 3))) (ordinary_mul (ordinary_const 8) (ordinary_mul ordinary_id ordinary_id))) (ordinary_const 13))) (ordinary_mul (ordinary_const 14) ordinary_id)) (ordinary_mul (ordinary_const 224) workspace_ordinary)) (source_bound_ordinary workspace_ordinary)) (ordinary_const 281))

private theorem source_envelope_ordinary : Ordinary sourceEnvelope := by
  unfold sourceEnvelope LayoutSourceRowsProgramInitialize.budget rowBudgetPolynomial
  exact (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_mul (ordinary_const 240) (ordinary_add (ordinary_add ordinary_id (ordinary_const 1)) (ordinary_const 1))) (ordinary_add (ordinary_mul ordinary_id (ordinary_mul (ordinary_const 2) ordinary_id)) (ordinary_const 1))) (ordinary_mul (ordinary_const 1000) (ordinary_pow (ordinary_add (ordinary_mul (ordinary_const 4) ordinary_id) (ordinary_const 1)) 2))) (ordinary_mul ordinary_id (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 1000) (ordinary_pow (ordinary_add (ordinary_mul (ordinary_const 2) ordinary_id) (ordinary_const 1)) 2)) (ordinary_mul ordinary_id (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 800) (ordinary_pow (ordinary_add (ordinary_mul (ordinary_const 2) ordinary_id) (ordinary_const 1)) 2)) uniform_ordinary) (ordinary_mul (ordinary_const 200) ordinary_id)) (ordinary_const 302)) (ordinary_mul (ordinary_const 12) ordinary_id)) (ordinary_const 12)) (ordinary_mul (ordinary_const 5) ordinary_id)) (ordinary_mul (ordinary_const 3) source_length_ordinary)) (ordinary_const 15)))) (ordinary_mul (ordinary_mul (ordinary_mul (ordinary_mul (ordinary_const 300000) (ordinary_add (ordinary_add (ordinary_const 2) (ordinary_mul ordinary_id (ordinary_add source_length_ordinary (ordinary_const 2)))) (ordinary_const 1))) (ordinary_pow (ordinary_add (ordinary_add ordinary_id (ordinary_const 1)) (ordinary_const 1)) 3)) (ordinary_pow (ordinary_add ordinary_id (ordinary_const 1)) 3)) (ordinary_pow (ordinary_add (ordinary_mul (ordinary_const 2) ordinary_id) (ordinary_const 1)) 2))) (ordinary_mul (ordinary_const 18) (ordinary_mul (ordinary_add ordinary_id (ordinary_const 1)) (ordinary_mul ordinary_id (ordinary_mul (ordinary_const 2) ordinary_id))))) (ordinary_mul (ordinary_const 12) ordinary_id)) (ordinary_mul (ordinary_const 3) (ordinary_add (ordinary_const 2) (ordinary_mul ordinary_id (ordinary_add source_length_ordinary (ordinary_const 2)))))) (ordinary_const 67)) (ordinary_mul (ordinary_const 45) (ordinary_mul (ordinary_add ordinary_id (ordinary_const 1)) (ordinary_mul ordinary_id (ordinary_mul (ordinary_const 2) ordinary_id))))) (ordinary_const 83)))) (ordinary_mul (ordinary_const 2) ordinary_id)) (ordinary_const 23)) (ordinary_mul (ordinary_const 1000000000000) (ordinary_add (ordinary_add ordinary_id (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 67108864) ordinary_id) (ordinary_const 1)) (ordinary_mul (ordinary_add ordinary_id (ordinary_const 1)) (ordinary_mul ordinary_id (ordinary_mul (ordinary_const 2) ordinary_id)))) (ordinary_add ordinary_id (ordinary_const 1))) (ordinary_mul ordinary_id (ordinary_add (ordinary_mul (ordinary_const 2) (ordinary_mul (ordinary_add ordinary_id (ordinary_const 1)) (ordinary_mul ordinary_id (ordinary_mul (ordinary_const 2) ordinary_id)))) (ordinary_const 2)))) (ordinary_const 1))) (ordinary_const 1))))

private theorem payload_ordinary : Ordinary payloadEnvelope := by
  unfold payloadEnvelope
  exact (ordinary_mul (ordinary_mul ordinary_id ordinary_id) (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 2) (ordinary_add (ordinary_add ordinary_id ordinary_id) ordinary_id)) (ordinary_mul (ordinary_mul (ordinary_const 2) ordinary_id) (ordinary_mul (ordinary_const 2) ordinary_id))) (ordinary_const 2)))

private theorem specialization_ordinary : Ordinary specializationEnvelope := by
  unfold specializationEnvelope
  exact (ordinary_mul (ordinary_const (3200000*(1000000000*3^10+64)^10)) (ordinary_pow (ordinary_mul (ordinary_const 10) (ordinary_add ordinary_id (ordinary_const 1))) 100))

private theorem literal_ordinary : Ordinary literalEnvelope := by
  unfold literalEnvelope
  exact (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 7) ordinary_id) (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 10) ordinary_id) (ordinary_mul (ordinary_const 9) ordinary_id)) (ordinary_const 18)) (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 10) ordinary_id) (ordinary_mul (ordinary_const 42) ordinary_id)) (ordinary_mul (ordinary_const 29) (ordinary_mul ordinary_id (ordinary_mul (ordinary_const 2) ordinary_id)))) (ordinary_const 109))) (ordinary_add (ordinary_add source_envelope_ordinary (ordinary_const 1)) (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 7) ordinary_id) (ordinary_const 5)) specialization_ordinary)))) (ordinary_mul (ordinary_const 22) (ordinary_add ordinary_id (ordinary_const 1)))) (ordinary_mul (ordinary_const 19) payload_ordinary)) (ordinary_mul (ordinary_const 2) (ordinary_add (ordinary_mul ordinary_id (ordinary_add (ordinary_mul (ordinary_const 2) (ordinary_mul (ordinary_add ordinary_id (ordinary_const 1)) (ordinary_mul ordinary_id (ordinary_mul (ordinary_const 2) ordinary_id)))) (ordinary_const 2))) (ordinary_const 1)))) (ordinary_const 54))

private theorem table_ordinary : Ordinary tableEnvelope := by
  unfold tableEnvelope
  exact (ordinary_mul (ordinary_const 1000000) (ordinary_pow (ordinary_add (ordinary_add (ordinary_add (ordinary_add ordinary_id ordinary_id) literal_ordinary) payload_ordinary) (ordinary_const 1)) 2))

/-- Public fixed-polynomial certificates for composing physical caps. -/
theorem payloadEnvelope_polynomial : Ordinary payloadEnvelope := payload_ordinary

theorem tableEnvelope_polynomial : Ordinary tableEnvelope := table_ordinary

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableBudgets
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadSumBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Explicit compact boundary, source and arithmetic caps for the actual head
sum. Their fixed polynomial certificates depend on source dimensions and
physical word lengths, independently of the number of head assignments. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumBudgets
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram OAI.Algorithms.SubexponentialSAT.SubexpLiftRing
open OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.Polynomial
open FactorTableBudgets

private theorem ordinary_comp {f g : ℕ → ℕ} (hf : Ordinary f) (hg : Ordinary g) :
    Ordinary (fun A => g (f A)) := by
  obtain ⟨C,e,hf⟩ := hf
  obtain ⟨K,d,hg⟩ := hg
  refine ⟨K*(C+1)^d,e*d,?_⟩
  intro A
  have h1 : 1 ≤ (A+1)^e := Nat.one_le_pow _ _ (by omega)
  have hb : f A+1 ≤ (C+1)*(A+1)^e := by
    have := hf A
    nlinarith
  calc
    _ ≤ K*(f A+1)^d := hg (f A)
    _ ≤ K*((C+1)*(A+1)^e)^d := by gcongr
    _ = _ := by rw [mul_pow,pow_mul]; ring

private theorem compact_ordinary : Ordinary compactCap := by
  unfold compactCap
  exact (ordinary_add (ordinary_add (ordinary_add ordinary_id (ordinary_mul (ordinary_const 4) ordinary_id)) (ordinary_const 6)) payloadEnvelope_polynomial)

private theorem source_ordinary : Ordinary sourceCap := by
  unfold sourceCap FactorTableProgram.literalRecordBound
  exact (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 1029) compact_ordinary) (ordinary_const 99)) ordinary_id) (ordinary_mul ordinary_id (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 2) ordinary_id) (ordinary_mul (ordinary_const 2) payloadEnvelope_polynomial)) (ordinary_const 4)))) (ordinary_const 1))

private theorem arithmetic_ordinary : Ordinary arithmeticCap := by
  unfold arithmeticCap FactorEvaluationSpace.inputScale
  exact (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_const 1) compact_ordinary) ordinary_id) (ordinary_mul (ordinary_mul (ordinary_const 2) ordinary_id) ordinary_id)) (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 2) ordinary_id) ordinary_id) ordinary_id) ordinary_id) ordinary_id) (ordinary_mul ordinary_id ordinary_id)) ordinary_id) ordinary_id) ordinary_id) (ordinary_const 1)))

private theorem table_scalar_ordinary : Ordinary tableScalarCap := by
  unfold tableScalarCap
  exact (ordinary_add (ordinary_add (ordinary_add ordinary_id source_ordinary) (ordinary_mul (ordinary_const 1029) compact_ordinary)) (ordinary_const 99))

private theorem callback_ordinary : Ordinary callbackEnvelope := by
  unfold callbackEnvelope
  exact (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const FactorAssignmentProgram.callbackScratch.length) (ordinary_add (ordinary_mul (ordinary_const 2) compact_ordinary) (ordinary_const 3))) (ordinary_mul (ordinary_const 128) compact_ordinary)) (ordinary_const 200)) (ordinary_comp table_scalar_ordinary tableEnvelope_polynomial)) (ordinary_mul (ordinary_const 2000) (ordinary_pow arithmetic_ordinary 3))) (ordinary_mul (ordinary_const 14000000) (ordinary_pow arithmetic_ordinary 9)))

private theorem body_ordinary : Ordinary bodyEnvelope := by
  unfold bodyEnvelope
  exact (ordinary_mul (ordinary_const 3040000) (ordinary_pow (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_const FactorAssignmentProgram.entryScratch.length) ordinary_id) (ordinary_mul (ordinary_const 2) ordinary_id)) ordinary_id) ordinary_id) ordinary_id) compact_ordinary) callback_ordinary) (ordinary_const 1)) 10))

private theorem prefix_ordinary : Ordinary prefixCap := by
  unfold prefixCap
  exact (ordinary_add (ordinary_add body_ordinary (ordinary_mul (ordinary_const 9) (ordinary_add ordinary_id (ordinary_const 1)))) (ordinary_const 8))

private theorem iteration_ordinary : Ordinary iterationEnvelope := by
  unfold iterationEnvelope
  exact (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 2) body_ordinary) (ordinary_mul (ordinary_const 126) prefix_ordinary)) (ordinary_mul (ordinary_const 54) ordinary_id)) (ordinary_const 286))

/-- All chosen capacities and the per-assignment time coefficient have fixed
polynomial growth. The constants precede the physical input cap. -/
theorem caps_polynomial : ∃ C e : ℕ, ∀ A,
    compactCap A ≤ C*(A+1)^e ∧ sourceCap A ≤ C*(A+1)^e ∧
    arithmeticCap A ≤ C*(A+1)^e ∧ prefixCap A ≤ C*(A+1)^e ∧
    iterationEnvelope A ≤ C*(A+1)^e := by
  obtain ⟨C,e,h⟩ := ordinary_add (ordinary_add (ordinary_add
    (ordinary_add compact_ordinary source_ordinary) arithmetic_ordinary) prefix_ordinary)
      iteration_ordinary
  refine ⟨C,e,fun A => ?_⟩
  have hs := h A
  dsimp only at hs
  exact ⟨by omega,by omega,by omega,by omega,by omega⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumBudgets
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeQueryInputBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed input-length bounds for the literal trial and accepted query
preparations. The common bound is produced before the greedy loop; none of
these caps contains a suspended caller word or a repeated-node scratch cap. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryInputBounds

open BitProgram StructuredCalls SqrtLog DisjointReuse HighFrontendSources
open HashGreedyCode LeafParametersProgram CostAssembly.Polynomial
open NativeQueryPreparation

private theorem sourceCap_mono (Cn dn Cl dl N k L U : ℕ) (h : L ≤ U) :
    sourceCap Cn dn Cl dl N L k ≤ sourceCap Cn dn Cl dl N U k := by
  unfold sourceCap
  gcongr

private theorem frontendCap_mono (Cf df k L U : ℕ) (h : L ≤ U) :
    frontendCap Cf df L k ≤ frontendCap Cf df U k := by
  unfold frontendCap
  gcongr

private theorem preparedCap_mono (Cp dp Cn dn Cl dl Cf df N k L U : ℕ) (h : L ≤ U) :
    preparedCap Cp dp Cn dn Cl dl Cf df N L k ≤
      preparedCap Cp dp Cn dn Cl dl Cf df N U k := by
  have hs := sourceCap_mono Cn dn Cl dl N k L U h
  have hf := frontendCap_mono Cf df k L U h
  dsimp only [preparedCap, HighQuerySetup.localBound]
  have ha := Nat.add_le_add hs hf
  exact Nat.add_le_add_right (Nat.add_le_add ha
    (Nat.mul_le_mul_left Cp (Nat.pow_le_pow_left (Nat.add_le_add_right ha 1) dp))) 1

/-- Substitution uses a fixed polynomial for the genuinely produced common
bound. The degree is independent of all later states, candidates and nodes. -/
theorem cap_polynomial (Cp dp Cn dn Cl dl Cf df C0 d0 k : ℕ) :
    ∃ C d : ℕ, ∀ N L : ℕ, L ≤ C0 * (N + 1) ^ d0 →
      sourceCap Cn dn Cl dl N L k + frontendCap Cf df L k +
        preparedCap Cp dp Cn dn Cl dl Cf df N L k + 4*N + 6 ≤ C * (N + 1) ^ d := by
  let U := fun N => C0 * (N+1)^d0
  have hU : Ordinary U := ordinary_mul (ordinary_const C0)
    (ordinary_pow (ordinary_add ordinary_id (ordinary_const 1)) d0)
  have hK := ordinary_add (ordinary_add hU (ordinary_const k)) (ordinary_const 1)
  have hS : Ordinary (fun N => sourceCap Cn dn Cl dl N (U N) k) :=
    ordinary_add (ordinary_add (ordinary_add
      (ordinary_mul (ordinary_const 3) hU) (ordinary_const 2))
      (ordinary_mul (ordinary_const Cn) (ordinary_pow
        (ordinary_add ordinary_id (ordinary_const 1)) dn)))
      (ordinary_mul (ordinary_const Cl) (ordinary_pow hK dl))
  have hF : Ordinary (fun N => frontendCap Cf df (U N) k) :=
    ordinary_add (ordinary_add
      (ordinary_mul (ordinary_const 10) (ordinary_add hU (ordinary_const 1)))
      (ordinary_mul (ordinary_const Cf) (ordinary_pow hK df))) (ordinary_const 12)
  have hA := ordinary_add hS hF
  have hP : Ordinary (fun N => preparedCap Cp dp Cn dn Cl dl Cf df N (U N) k) :=
    ordinary_add (ordinary_add hA (ordinary_mul (ordinary_const Cp)
      (ordinary_pow (ordinary_add hA (ordinary_const 1)) dp))) (ordinary_const 1)
  obtain ⟨C,d,hC⟩ := ordinary_add (ordinary_add (ordinary_add (ordinary_add hS hF) hP)
    (ordinary_mul (ordinary_const 4) ordinary_id)) (ordinary_const 6)
  refine ⟨C,d,?_⟩
  intro N L hL
  have hs := sourceCap_mono Cn dn Cl dl N k L (U N) hL
  have hf := frontendCap_mono Cf df k L (U N) hL
  have hp := preparedCap_mono Cp dp Cn dn Cl dl Cf df N k L (U N) hL
  exact (by omega : sourceCap Cn dn Cl dl N L k + frontendCap Cf df L k +
    preparedCap Cp dp Cn dn Cl dl Cf df N L k + 4*N+6 ≤
      sourceCap Cn dn Cl dl N (U N) k + frontendCap Cf df (U N) k +
        preparedCap Cp dp Cn dn Cl dl Cf df N (U N) k +4*N+6).trans (hC N)


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryInputBounds
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryHeadBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! A concrete numerical HeadBounds certificate for the actual visitor.
Source columns are bounded from its stored native input, all incidence rows
remain present, and the compact endpoint cap is separate from transient space. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets
open OAI BitProgram StructuredCalls SubexpSetupStorage SubexpLiftRing
open SqrtLog SqrtLog.LeafProgram SqrtLog.LeafHeadSetupProgram
open HeadSumBudgets FactorTableBudgets
open OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.Polynomial

private theorem scalar_ordinary : OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.Polynomial.Ordinary scalarCap := by
  unfold scalarCap sourceSize
  exact (ordinary_mul (ordinary_const 1000100) (ordinary_pow (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_add ordinary_id (ordinary_const 1)) (ordinary_add (ordinary_mul (ordinary_const 100) (ordinary_pow (ordinary_add ordinary_id (ordinary_const 2)) 2)) (ordinary_const 2))) ordinary_id) (ordinary_const 1)) (ordinary_const 1)) 10))

/-- Constants are fixed before the original physical/scalar allowance. All
four actual capacities and the sharp per-head exponential coefficient use
this same ordinary polynomial; the factor2^h remains separate. -/
theorem caps_polynomial : ∃ C e : ℕ, ∀ A,
    compact A ≤ C*(A+1)^e ∧ source A ≤ C*(A+1)^e ∧
    arithmetic A ≤ C*(A+1)^e ∧ transient A ≤ C*(A+1)^e ∧
    HeadSumBudgets.iterationEnvelope (scalarCap A) ≤ C*(A+1)^e := by
  obtain ⟨K,f,hscalar⟩ := scalar_ordinary
  obtain ⟨C,e,hcaps⟩ := HeadSumBudgets.caps_polynomial
  refine ⟨C*(K+1)^e,f*e,fun A => ?_⟩
  have h1 : 1 ≤ (A+1)^f := Nat.one_le_pow _ _ (by omega)
  have hb : scalarCap A+1 ≤ (K+1)*(A+1)^f := by
    have := hscalar A
    nlinarith
  have hpoly : C*(scalarCap A+1)^e ≤ (C*(K+1)^e)*(A+1)^(f*e) := by
    calc
      _ ≤ C*((K+1)*(A+1)^f)^e := by gcongr
      _ = _ := by rw [mul_pow,pow_mul]; ring
  obtain ⟨hp,hs,hz,hb,ht⟩ := hcaps (scalarCap A)
  exact ⟨hp.trans hpoly,hs.trans hpoly,hz.trans hpoly,hb.trans hpoly,ht.trans hpoly⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeQueryTimeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Time bounds for the same actual source/prepared caps used by the literal
query provider. The resource record supplies the combinatorial exponent;
its ordinary fields are not asserted to measure the actual physical phases.
Frontend, preparation, seed and return work are paid separately below. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryTimeBounds

open SqrtLog SqrtLog.Statement CostAssembly.Polynomial NativeQueryInputBounds

/-- The cap is polynomial in the original input independently of all later
candidates, marks, nodes, or preserved caller words. -/
theorem physicalCap_polynomial_oai (Cp dp Cn dn Cl dl Cf df C0 d0 k : ℕ) :
    ∃ C e : ℕ, ∀ N L : ℕ, L ≤ C0*(N+1)^d0 →
      physicalCap Cp dp Cn dn Cl dl Cf df N L k ≤ C*(N+1)^e := by
  obtain ⟨Cw,ew,hw⟩ := cap_polynomial Cp dp Cn dn Cl dl Cf df C0 d0 k
  obtain ⟨Cc,ec,hc⟩ := QueryHeadBudgets.caps_polynomial
  let V := fun N => Cw*(N+1)^ew
  have hV : Ordinary V := ordinary_mul (ordinary_const Cw)
    (ordinary_pow (ordinary_add ordinary_id (ordinary_const 1)) ew)
  obtain ⟨C,e,hpoly⟩ := ordinary_add
    (ordinary_mul (ordinary_const 30) (ordinary_add hV (ordinary_const 1)))
    (ordinary_mul (ordinary_const Cc) (ordinary_pow
      (ordinary_add (ordinary_mul (ordinary_const 12) hV) (ordinary_const 1)) ec))
  refine ⟨C,e,?_⟩
  intro N L hL
  let S := sourceCap Cn dn Cl dl N L k
  let F := frontendCap Cf df L k
  let P := preparedCap Cp dp Cn dn Cl dl Cf df N L k
  have hW : S+F+P+4*N+6 ≤ V N := hw N L hL
  have hA : 12*P+4*N+6 ≤ 12*V N := by omega
  have hcompact := (hc (12*P+4*N+6)).1.trans
    (Nat.mul_le_mul_left Cc (Nat.pow_le_pow_left (Nat.add_le_add_right hA 1) ec))
  have hraw : physicalCap Cp dp Cn dn Cl dl Cf df N L k ≤
      30*(V N+1)+Cc*(12*V N+1)^ec := by
    change 30*(S+F+P+4*N+6+1)+QueryHeadBudgets.compact (12*P+4*N+6) ≤ _
    omega
  exact hraw.trans (hpoly N)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryTimeBounds
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryTimeBounds.physicalCap_polynomial_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryTimeBounds.physicalCap_polynomial_oai
