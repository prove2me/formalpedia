-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamBudgets.high_loop_budget_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:27:41.038319+00:00
-- url     : https://prove2.me/submissions/60995605-ec5a-4fce-8976-15123e6389a1

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ081S183

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_TruncatedRingProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Native arithmetic after immediate Boolean specialization

The existing finite sparse-product program is used with empty formal support.
Its keys still carry the ambient input coordinate type; this does not compress
the declared variables. There are at most `u * J` retained entries, including
zero cutoffs. Polynomial local time therefore bounds all its source prefixes,
including the table, inputs, output, normalization copies and arithmetic scratch.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram

open scoped BigOperators
open OAI OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open MomentsProgram BitProgram

/- The two fields coincide with LeafProgram.NativeSemantics.Good. The
arithmetic layer states them transparently to avoid importing the factor
interpreter. Conversion in either direction supplies `valid` and `nodup`.
The proof bodies below are the original finite-program validity arguments. -/

variable {V R : Type*} [DecidableEq V] [CommRing R]

/-- Additive readout has a fixed degree-six bound. -/
theorem readoutBudget_polynomial (n B d u J : ℕ) :
 MomentsReadoutProgram.uniformReadoutBudget B d n u J (n+u+J) (u*J) ≤30000*(n+B+d+u+J+1)^6 := by
 let a := n+B+d+u+J+1
 have ha : 1≤a := by dsimp [a]; omega
 have hm : MomentsReadoutProgram.uniformReadoutBudget B d n u J (n+u+J) (u*J) ≤MomentsReadoutProgram.uniformReadoutBudget a a a a a (a+a+a) (a*a) := by
  have hn : n≤a := by dsimp [a]; omega
  have hB : B≤a := by dsimp [a]; omega
  have hd : d≤a := by dsimp [a]; omega
  have hu : u≤a := by dsimp [a]; omega
  have hJ : J≤a := by dsimp [a]; omega
  dsimp [MomentsReadoutProgram.uniformReadoutBudget,
    MomentsReadoutProgram.uniformSlotBudget, Dictionary.codeBranchBudget]
  gcongr
 refine hm.trans ?_
 change MomentsReadoutProgram.uniformReadoutBudget a a a a a (a+a+a) (a*a) ≤30000*a^6
 have h0 : 1≤a^6 := Nat.one_le_pow 6 a ha
 have h1 : a≤a^6 := by simpa using pow_le_pow_right' ha (show 1≤6 by decide)
 have h2 : a^2≤a^6 := pow_le_pow_right' ha (by decide)
 have h3 : a^3≤a^6 := pow_le_pow_right' ha (by decide)
 have h4 : a^4≤a^6 := pow_le_pow_right' ha (by decide)
 have h5 : a^5≤a^6 := pow_le_pow_right' ha (by decide)
 dsimp [MomentsReadoutProgram.uniformReadoutBudget,
    MomentsReadoutProgram.uniformSlotBudget, Dictionary.codeBranchBudget]
 ring_nf
 omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram
end

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NodeReadoutSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual node-array readout after all finite-difference pairs. The fixed
cleanup pays for transient lower words and clears the old output. Preserved
masters supply the coefficient zero vector and both truncation bounds. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeReadoutSpace

open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open MomentsProgram TruncatedRingProgram

theorem budget_polynomial (n B d u J incoming : ℕ) :
    budget n B d u J incoming ≤
      41 * (2 * incoming + 3) + 30000 * (n + B + d + u + J + 1) ^ 6 + 1 := by
  exact Nat.add_le_add_right
    (Nat.add_le_add_left (TruncatedRingProgram.readoutBudget_polynomial n B d u J) _) 1

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeReadoutSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NodeAppendSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeAppendSpace
open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open MomentsProgram TruncatedRingProgram

theorem budget_polynomial (n B d u J incoming : ℕ) :
    budget n B d u J incoming ≤ 29 * incoming + 27 +
      (41 * (2 * incoming + 3) + 30000 * (n + B + d + u + J + 1) ^ 6 + 1) +
      6 * (incoming + J * (d * B)) + 9 := by
  exact Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add_left (NodeReadoutSpace.budget_polynomial n B d u J incoming) _) _) _


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeAppendSpace
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

private theorem compact_ordinary : Ordinary compact := by
  obtain ⟨C,e,h⟩ := caps_polynomial
  exact ⟨C,e,fun A => (h A).1⟩

private theorem transient_ordinary : Ordinary transient := by
  obtain ⟨C,e,h⟩ := caps_polynomial
  exact ⟨C,e,fun A => (h A).2.2.2.1⟩

private theorem iteration_ordinary :
    Ordinary (fun A => HeadSumBudgets.iterationEnvelope (scalarCap A)) := by
  obtain ⟨C,e,h⟩ := caps_polynomial
  exact ⟨C,e,fun A => (h A).2.2.2.2⟩

private theorem multiply_ordinary : Ordinary multiplyEnvelope := by
  unfold multiplyEnvelope
  exact (ordinary_add (ordinary_mul (ordinary_const 51000) (ordinary_add compact_ordinary (ordinary_const 1))) (ordinary_mul (ordinary_const 4000000) (ordinary_pow (ordinary_add (ordinary_mul (ordinary_const 6) ordinary_id) (ordinary_const 1)) 10)))

/-- The complete actual one-head visitor has fixed polynomial overhead.
It is multiplied by the proved head-size exponent only after this theorem. -/
theorem visitor_polynomial : ∃ C e : ℕ, ∀ A, visitorEnvelope A ≤ C*(A+1)^e := by
  change Ordinary visitorEnvelope
  unfold visitorEnvelope QueryVisitorLoad.runEnvelope
  exact (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const (1000*(10000000000000000*HeadLoaderBudgets.sizeCoefficient^8+3))) (ordinary_pow (ordinary_add (ordinary_add compact_ordinary ordinary_id) (ordinary_const 2)) 64)) (ordinary_mul (ordinary_const 100) compact_ordinary)) (ordinary_const 200)) iteration_ordinary) multiply_ordinary) (ordinary_mul (ordinary_const 996) compact_ordinary)) (ordinary_const 200)) transient_ordinary) (ordinary_mul (ordinary_const 896) compact_ordinary))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryNodeFinish
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual node readout and loop continuation. The emitted coefficient stream
retains its order. Node temporaries are physically reclaimed before refreshing
the outer guard, and every completed node restores one fixed boundary bound. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeFinish

open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open MomentsProgram TruncatedRingProgram

theorem budget_polynomial (n wordWidth d u J incoming : ℕ) :
    budget n wordWidth d u J incoming ≤
      29 * incoming + 27 +
      (41 * (2 * incoming + 3) + 30000 * (n + wordWidth + d + u + J + 1) ^ 6 + 1) +
      6 * (incoming + J * (d * wordWidth)) + 9 + 4 * incoming + 10 :=
  Nat.add_le_add_right
    (Nat.add_le_add_right (NodeAppendSpace.budget_polynomial n wordWidth d u J incoming) _) _

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeFinish
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_ReconstructionNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! One concrete lower-workspace recovery tail: native Hermite reconstruction,
canonical complete binary readback, and paid cache reclamation. All retained
caller stacks enter its local prefix bound; the endpoint changes only count323.
The physical jet and semantic target hypotheses must be produced by the query. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionNative

open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing OAI.Algorithms.SubexponentialSAT.SqrtLog
open DensePolynomialProgram
open LeafProgram.Count

/-- The recovery degree is fixed before every input. -/
theorem budget_polynomial (S : ℕ) :
    budget S ≤ (2400*(ReconstructionProgram.Native.costConstant+1)^4+39608)*(S+1)^96 := by
  have hpositive : 0 < S+1 := Nat.succ_pos S
  have hone : 1 ≤ (S+1)^2 := Nat.one_le_pow _ _ hpositive
  have hfour : (S+1)^4 ≤ (S+1)^96 := Nat.pow_le_pow_right hpositive (by decide)
  have hlinear : S+1 ≤ (S+1)^96 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hpositive (show 1 ≤ 96 by decide)
  have hsquare : (2*(S+1)^2+1)^2 ≤ 9*(S+1)^4 := by
    have h := Nat.pow_le_pow_left (show 2*(S+1)^2+1 ≤ 3*(S+1)^2 by omega) 2
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hread : 4400*(2*(S+1)^2+1)^2 ≤ 39600*(S+1)^96 := by
    calc
      _ ≤ 4400*(9*(S+1)^4) := Nat.mul_le_mul_left 4400 hsquare
      _ = 39600*(S+1)^4 := by ring
      _ ≤ 39600*(S+1)^96 := Nat.mul_le_mul_left 39600 hfour
  have hrest : 4*S+8 ≤ 8*(S+1)^96 := by omega
  unfold budget
  calc
    _ ≤ 2400*(ReconstructionProgram.Native.costConstant+1)^4*(S+1)^96 +
        39600*(S+1)^96 + 8*(S+1)^96 := by omega
    _ = _ := by ring

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionNative
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryReconstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual streamed-jet handoff, scratch preparation, and canonical count
reconstruction. Readiness is derived from the produced ring masters. The target
and jets are mathematical properties of the actual query output; no evaluator
or readiness service is accepted by the produced-input theorem. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstruction

open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing OAI.Algorithms.SubexponentialSAT.SqrtLog
open DensePolynomialProgram LeafProgram
open LeafParametersProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

/-- All exponents are fixed before the input and before the produced jets. -/
theorem budget_polynomial (B S : ℕ) :
    budget B S ≤ (2400*(ReconstructionProgram.Native.costConstant+1)^4+
      5*Count.Prepare.ports.length+39628)*(B+S+1)^96 := by
  have hp : 0 < B+S+1 := by omega
  have hlinear : B+1 ≤ (B+S+1)^96 := by
    have h := Nat.pow_le_pow_right hp (show 1 ≤ 96 by decide)
    simp only [pow_one] at h
    omega
  have hrec := ReconstructionNative.budget_polynomial S
  have hpow : (S+1)^96 ≤ (B+S+1)^96 := Nat.pow_le_pow_left (by omega) 96
  have hrec' := hrec.trans (Nat.mul_le_mul_left
    (2400*(ReconstructionProgram.Native.costConstant+1)^4+39608) hpow)
  have hprep : 8*B+10+prepareBudget B ≤
      (5*Count.Prepare.ports.length+20)*(B+1) := by
    unfold prepareBudget
    nlinarith only [Nat.zero_le (Count.Prepare.ports.length*B)]
  have hprep' := hprep.trans (Nat.mul_le_mul_left
    (5*Count.Prepare.ports.length+20) hlinear)
  unfold budget coreBudget
  calc
    _ = (8*B+10+prepareBudget B)+ReconstructionNative.budget S := by omega
    _ ≤ (5*Count.Prepare.ports.length+20)*(B+S+1)^96 +
        (2400*(ReconstructionProgram.Native.costConstant+1)^4+39608)*(B+S+1)^96 :=
      Nat.add_le_add hprep' hrec'
    _ = _ := by
      rw [← Nat.add_mul]
      apply congrArg (fun x : ℕ => x*(B+S+1)^96)
      omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstruction
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryVisitorBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Polynomial overhead and prefix space for the complete actual tuple
visitor. The number of heads and the proved maximum head-size exponent stay
explicit; the empty-head/empty-tuple term is retained. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorBudgets
open OAI SqrtLog SubexpLiftRing SubexpSetupStorage
open SignatureTupleSource LeafHeadSetupProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.Polynomial

private theorem compact_ordinary : Ordinary QueryHeadBudgets.compact := by
  obtain ⟨C,e,h⟩ := QueryHeadBudgets.caps_polynomial
  exact ⟨C,e,fun A => (h A).1⟩

private theorem tail_ordinary : Ordinary tailEnvelope := by
  unfold tailEnvelope
  exact (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 75) compact_ordinary) (ordinary_const 97)) (ordinary_mul (ordinary_const 3000000) (ordinary_pow (ordinary_add (ordinary_mul (ordinary_const 6) ordinary_id) (ordinary_const 1)) 10)))

private theorem baseline_ordinary : Ordinary baselineEnvelope := by
  unfold baselineEnvelope QueryVisitorLoad.runEnvelope
  exact (ordinary_add (ordinary_add (ordinary_mul (ordinary_const (1000*(10000000000000000*HeadLoaderBudgets.sizeCoefficient^8+3))) (ordinary_pow (ordinary_add (ordinary_add compact_ordinary ordinary_id) (ordinary_const 2)) 64)) (ordinary_mul (ordinary_const 90) compact_ordinary)) (ordinary_const 89))

theorem envelope_polynomial : ∃ C e : ℕ, ∀ A, envelope A ≤ C*(A+1)^e := by
  change Ordinary envelope
  unfold envelope
  exact (ordinary_add (ordinary_add (ordinary_add (ordinary_add tail_ordinary (ordinary_mul (ordinary_const 2400) (ordinary_add compact_ordinary (ordinary_const 1)))) baseline_ordinary) QueryHeadBudgets.visitor_polynomial) (ordinary_const 20))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorBudgets
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_TupleRunBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The same compact endpoint cap supports the actual tuple controller and
its visitor. Transient scanner/reload work is bounded separately; none of it
is fed back into the retained frame cap between pairs. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TupleRunBudgets
open OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.Polynomial
open SignatureTupleSource SignatureTupleComplete SignatureTupleLoader

private theorem compact_ordinary : Ordinary QueryHeadBudgets.compact := by
  obtain ⟨C,e,h⟩ := QueryHeadBudgets.caps_polynomial
  exact ⟨C,e,fun A => (h A).1⟩

private theorem scanner_ordinary : Ordinary scannerEnvelope := by
  unfold scannerEnvelope
  exact ordinary_mul (ordinary_const 100000) (ordinary_pow
    (ordinary_mul (ordinary_const 20000)
      (ordinary_pow (ordinary_add ordinary_id (ordinary_const 2)) 6)) 6)

private theorem run_ordinary : Ordinary (fun A =>
    SignatureTupleLoader.runEnvelope A (QueryHeadBudgets.compact A)) := by
  unfold SignatureTupleLoader.runEnvelope
  exact ordinary_mul (ordinary_const
    (1000*(10000000000000000*HeadLoaderBudgets.sizeCoefficient^8+3)))
    (ordinary_pow (ordinary_add (ordinary_add compact_ordinary ordinary_id) (ordinary_const 2)) 64)

theorem event_polynomial : ∃ C e : ℕ, ∀ A, eventEnvelope A ≤ C*(A+1)^e := by
  change Ordinary eventEnvelope
  unfold eventEnvelope
  exact ordinary_add (ordinary_add (ordinary_add (ordinary_add scanner_ordinary run_ordinary)
    (ordinary_mul (ordinary_const 4000) (ordinary_add compact_ordinary (ordinary_const 1))))
    (ordinary_mul (ordinary_const 200) compact_ordinary)) (ordinary_const 200)

theorem envelope_polynomial : ∃ C e : ℕ, ∀ A, envelope A ≤ C*(A+1)^e := by
  change Ordinary envelope
  unfold envelope
  exact ordinary_add event_polynomial QueryVisitorBudgets.envelope_polynomial

theorem runCoefficient_polynomial : ∃ C e : ℕ, ∀ A, runCoefficient A ≤ C*(A+1)^e := by
  change Ordinary runCoefficient
  unfold runCoefficient
  have ht : Ordinary QueryVisitorBudgets.tailEnvelope := by
    obtain ⟨C,e,h⟩ := QueryVisitorBudgets.envelope_polynomial
    refine ⟨C,e,fun A => le_trans ?_ (h A)⟩
    unfold QueryVisitorBudgets.envelope
    omega
  exact ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 5) envelope_polynomial)
    (ordinary_mul (ordinary_const 2496) compact_ordinary)) ht) (ordinary_const 1602)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TupleRunBudgets
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_ResourceBudgets
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed-degree numerical closure for measured streaming costs. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

open SqrtLog.Statement

/-- Fixed polynomial local budgets compose without allowing the exponent
to depend on the runtime input or the number of streamed iterations. -/
theorem polynomialBudget_substitute (work size inputBits C d K e : ℕ)
    (hwork : work ≤ C * (size + 1) ^ d)
    (hsize : size ≤ K * (inputBits + 1) ^ e) :
    work ≤ C * (K + 1) ^ d * (inputBits + 1) ^ (e * d) := by
  have hbase : 1 ≤ (inputBits + 1) ^ e := Nat.one_le_pow' _ _
  have hs : size + 1 ≤ (K + 1) * (inputBits + 1) ^ e := by nlinarith
  calc
    _ ≤ C * ((K + 1) * (inputBits + 1) ^ e) ^ d :=
      hwork.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hs d))
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_StreamedQueryMeasuredCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The measured callback pays native mask setup, the complete attained-tuple
run (including ascent), and the signed commit. Its finite-difference iterator
is compared to the original explicit resource record with one fixed power. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamedQueryMeasuredCost

open OAI SqrtLog SubexpLiftRing SubexpQuarticRing
open SignatureTupleSource SignatureTupleTraversal SignatureTupleDFS
open CostAssembly.Polynomial
open scoped BigOperators

private theorem compact_ordinary : Ordinary QueryHeadBudgets.compact := by
  obtain ⟨C,e,h⟩ := QueryHeadBudgets.caps_polynomial
  exact ⟨C,e,fun A => (h A).1⟩

theorem coefficient_polynomial : ∃ C e : ℕ, ∀ A, coefficient A ≤ C*(A+1)^e := by
  change Ordinary coefficient
  have hstart : Ordinary (fun A => QueryPairEvaluation.startBudget A (QueryHeadBudgets.compact A)) := by
    unfold QueryPairEvaluation.startBudget
    exact ordinary_add (ordinary_add
      (ordinary_mul (ordinary_const 300)
        (ordinary_add (ordinary_add compact_ordinary ordinary_id) (ordinary_const 1)))
      (ordinary_mul (ordinary_const 2) compact_ordinary)) (ordinary_const 5)
  have hbytes : Ordinary (fun A => A*A*(2*(A+A+A)+2*(A*(2*A))+2)) :=
    ordinary_mul (ordinary_mul ordinary_id ordinary_id)
      (ordinary_add (ordinary_add
        (ordinary_mul (ordinary_const 2) (ordinary_add (ordinary_add ordinary_id ordinary_id) ordinary_id))
        (ordinary_mul (ordinary_const 2) (ordinary_mul ordinary_id (ordinary_mul (ordinary_const 2) ordinary_id))))
        (ordinary_const 2))
  have hcommit : Ordinary commitEnvelope := by
    unfold commitEnvelope
    exact ordinary_add (ordinary_add (ordinary_add (ordinary_add
      (ordinary_mul (ordinary_const 51000) (ordinary_add compact_ordinary (ordinary_const 1)))
      (ordinary_mul (ordinary_const 20) ordinary_id))
      (ordinary_mul (ordinary_const 6000000)
        (ordinary_pow (ordinary_add (ordinary_mul (ordinary_const 6) ordinary_id) (ordinary_const 1)) 10)))
      (ordinary_mul (ordinary_const 6) hbytes)) (ordinary_const 30)
  exact ordinary_add (ordinary_add hstart hcommit) TupleRunBudgets.runCoefficient_polynomial

theorem pairCoefficient_polynomial : ∃ C e : ℕ, ∀ A, pairCoefficient A ≤ C*(A+1)^e := by
  change Ordinary pairCoefficient
  exact ordinary_mul
    (ordinary_mul (ordinary_add coefficient_polynomial (ordinary_const 46))
      (ordinary_add ordinary_id (ordinary_const 1)))
    (ordinary_add (ordinary_mul (ordinary_const 3) ordinary_id) (ordinary_const 1))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamedQueryMeasuredCost
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryStreamBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed polynomial time envelopes for the actual conditioned stream. The
same original assembled resource pays the support/tuple work; all remaining
scalars and retained words enter only fixed polynomial coefficients. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamBudgets
open SqrtLog SubexpLiftRing SubexpQuarticRing
open CostAssembly.Polynomial QueryStreamCorrect

private theorem finishEnvelope_polynomial : Ordinary finishEnvelope := by
  have htwo := ordinary_mul (ordinary_const 2) ordinary_id
  have hbase := ordinary_add (ordinary_add (ordinary_add (ordinary_add
    (ordinary_add ordinary_id htwo) ordinary_id) ordinary_id) ordinary_id) (ordinary_const 1)
  have hmain := ordinary_add (ordinary_add
    (ordinary_mul (ordinary_const 41) (ordinary_add htwo (ordinary_const 3)))
    (ordinary_mul (ordinary_const 30000) (ordinary_pow hbase 6))) (ordinary_const 1)
  have hcubic := ordinary_mul (ordinary_const 6)
    (ordinary_add ordinary_id (ordinary_mul ordinary_id (ordinary_mul ordinary_id htwo)))
  exact ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add
    (ordinary_add (ordinary_mul (ordinary_const 29) ordinary_id) (ordinary_const 27))
    hmain) hcubic) (ordinary_const 9))
    (ordinary_mul (ordinary_const 4) ordinary_id)) (ordinary_const 10)

private theorem scalarPolynomial (R : ℕ) : Ordinary (fun X =>
    18*X+65*X+67+23*X+
      X*(20000*(X+1)^4+300*(X+1)+X+10+finishEnvelope X+1)+32+
      R*(2*X+1)^96) := by
  have hbase := ordinary_add ordinary_id (ordinary_const 1)
  have hprepare := ordinary_add (ordinary_mul (ordinary_const 20000) (ordinary_pow hbase 4))
    (ordinary_mul (ordinary_const 300) hbase)
  have hnode := ordinary_add (ordinary_add (ordinary_add
    (ordinary_add hprepare ordinary_id) (ordinary_const 10)) finishEnvelope_polynomial)
    (ordinary_const 1)
  have hprefix := ordinary_add (ordinary_add (ordinary_add
    (ordinary_mul (ordinary_const 18) ordinary_id)
    (ordinary_mul (ordinary_const 65) ordinary_id)) (ordinary_const 67))
    (ordinary_mul (ordinary_const 23) ordinary_id)
  have hrec := ordinary_mul (ordinary_const R) (ordinary_pow
    (ordinary_add (ordinary_mul (ordinary_const 2) ordinary_id) (ordinary_const 1)) 96)
  exact ordinary_add (ordinary_add (ordinary_add hprefix
    (ordinary_mul ordinary_id hnode)) (ordinary_const 32)) hrec

private theorem scalarEnvelope_polynomial : Ordinary scalarEnvelope :=
  scalarPolynomial reconstructionCoefficient

private theorem finish_le (n t d J A X : ℕ)
    (hn : n ≤ X) (ht : t ≤ X) (hd : d ≤ X) (hJ : J ≤ X)
    (hF : QueryHeadBudgets.compact A ≤ X) :
    finishBudget n t d J A ≤ finishEnvelope X := by
  have h := QueryNodeFinish.budget_polynomial n (baseWidth 3 t) d t J
    (QueryHeadBudgets.compact A)
  apply h.trans
  simp only [RingProgram.ternary_baseWidth]
  unfold finishEnvelope
  gcongr

private theorem budget_le_scalar (n t d Q J A S work X : ℕ)
    (hn : n ≤ X) (ht : t ≤ X) (hd : d ≤ X) (hQ : Q ≤ X) (hJ : J ≤ X)
    (hS : S ≤ X) (hF : QueryHeadBudgets.compact A ≤ X)
    (hpair : StreamedQueryMeasuredCost.pairCoefficient A ≤ X) :
    budget n t d Q J A S work ≤ scalarEnvelope X*(work+1)^2 := by
  have hfinish := finish_le n t d J A X hn ht hd hJ hF
  have hrec := QueryReconstruction.budget_polynomial (QueryHeadBudgets.compact A) S
  have hrec' : QueryReconstruction.budget (QueryHeadBudgets.compact A) S ≤
      reconstructionCoefficient*(2*X+1)^96 := hrec.trans
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 96))
  have hraw : budget n t d Q J A S work ≤
      18*X+65*X+67+23*X+
      X*(20000*(X+1)^4+300*(X+1)+X*work^2+10+finishEnvelope X+1)+32+
      reconstructionCoefficient*(2*X+1)^96 := by
    unfold budget nodeBudget prepareBudget
    gcongr
  let rest := 18*X+65*X+67+23*X+
    X*(20000*(X+1)^4+300*(X+1)+10+finishEnvelope X+1)+32+
    reconstructionCoefficient*(2*X+1)^96
  have hone : 1 ≤ (work+1)^2 := Nat.one_le_pow' _ _
  have hpow : work^2 ≤ (work+1)^2 := Nat.pow_le_pow_left (by omega) 2
  have hrest := Nat.mul_le_mul_left rest hone
  have hp := Nat.mul_le_mul_left (X*X) hpow
  apply hraw.trans
  change _ ≤ scalarEnvelope X*(work+1)^2
  unfold scalarEnvelope
  dsimp [rest] at hrest
  nlinarith only [hrest,hp]

/-- All coefficients and degrees precede every query, node and physical cap.
The exponential term is exactly the square of the same original work value. -/
theorem budget_polynomial : ∃ C e : ℕ, ∀ n t d Q J A S work U : ℕ,
    n ≤ U → t ≤ U → d ≤ U → Q ≤ U → J ≤ U → A ≤ U → S ≤ U →
    budget n t d Q J A S work ≤ C*(U+1)^e*(work+1)^2 := by
  obtain ⟨Cc,dc,hc⟩ := QueryHeadBudgets.caps_polynomial
  obtain ⟨Cp,dp,hp⟩ := StreamedQueryMeasuredCost.pairCoefficient_polynomial
  obtain ⟨Ce,de,he⟩ := scalarEnvelope_polynomial
  let degree := dc+dp+1
  let coefficient := Cc+Cp+1
  refine ⟨Ce*(coefficient+1)^de,degree*de,?_⟩
  intro n t d Q J A S work U hn ht hd hQ hJ hA hS
  let X := coefficient*(U+1)^degree
  have hbase : 1 ≤ U+1 := by omega
  have hlinear : U ≤ X := by
    have h := Nat.le_self_pow (show degree ≠ 0 by dsimp [degree]; omega) (U+1)
    have hm := Nat.le_mul_of_pos_left ((U+1)^degree)
      (show 0 < coefficient by dsimp [coefficient]; omega)
    omega
  have hcompact : QueryHeadBudgets.compact A ≤ X := by
    have h0 := (hc A).1
    have hpow : (A+1)^dc ≤ (U+1)^degree :=
      (Nat.pow_le_pow_left (by omega) dc).trans (Nat.pow_le_pow_right hbase (by dsimp [degree]; omega))
    exact h0.trans (Nat.mul_le_mul (by dsimp [coefficient]; omega) hpow)
  have hpair : StreamedQueryMeasuredCost.pairCoefficient A ≤ X := by
    have hpow : (A+1)^dp ≤ (U+1)^degree :=
      (Nat.pow_le_pow_left (by omega) dp).trans (Nat.pow_le_pow_right hbase (by dsimp [degree]; omega))
    exact (hp A).trans (Nat.mul_le_mul (by dsimp [coefficient]; omega) hpow)
  have h := budget_le_scalar n t d Q J A S work X
    (hn.trans hlinear) (ht.trans hlinear) (hd.trans hlinear) (hQ.trans hlinear)
    (hJ.trans hlinear) (hS.trans hlinear) hcompact hpair
  have hs := polynomialBudget_substitute (scalarEnvelope X) X U Ce de coefficient degree
    (he X) le_rfl
  exact h.trans (Nat.mul_le_mul_right _ hs)

private theorem high_loop_le (stream L n H U : ℕ)
    (hL : L ≤ U) (hn : n ≤ U) (hH : H ≤ U) :
    2^H*(stream+11*L+16*(n+2)+28*H+27)+3 ≤
      100*2^H*(stream+U+1) := by
  have hp : 1 ≤ 2^H := Nat.one_le_pow _ _ (by decide)
  have hb : stream+11*L+16*(n+2)+28*H+27+3 ≤ 100*(stream+U+1) := by omega
  have hm := Nat.mul_le_mul_left (2^H) hb
  nlinarith only [hm,hp]

/-- This is the actual high-loop expression, including copy/control/terminal
work. The high-variable factor stays separate from the retained-space cap. -/
theorem high_loop_budget_polynomial_oai : ∃ C e : ℕ,
    ∀ n t d Q J A S work U L H : ℕ,
    n ≤ U → t ≤ U → d ≤ U → Q ≤ U → J ≤ U → A ≤ U → S ≤ U →
    L ≤ U → H ≤ U →
    2^H*(budget n t d Q J A S work+11*L+16*(n+2)+28*H+27)+3 ≤
      C*(U+1)^e*(work+1)^2*2^H := by
  obtain ⟨C,e,h⟩ := budget_polynomial
  refine ⟨100*(C+1),e+1,?_⟩
  intro n t d Q J A S work U L H hn ht hd hQ hJ hA hS hL hH
  have hb := h n t d Q J A S work U hn ht hd hQ hJ hA hS
  have hbase : 1 ≤ U+1 := by omega
  have hp : (U+1)^e ≤ (U+1)^(e+1) := Nat.pow_le_pow_right hbase (by omega)
  have hlin : U+1 ≤ (U+1)^(e+1)*(work+1)^2 :=
    (Nat.le_self_pow (by omega) _).trans
      (Nat.le_mul_of_pos_right _ (Nat.one_le_pow' _ _))
  have hb' := hb.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left C hp))
  have hsum : budget n t d Q J A S work+U+1 ≤
      (C+1)*(U+1)^(e+1)*(work+1)^2 := by nlinarith only [hb',hlin]
  calc
    _ ≤ 100*2^H*(budget n t d Q J A S work+U+1) := high_loop_le _ L n H U hL hn hH
    _ ≤ 100*2^H*((C+1)*(U+1)^(e+1)*(work+1)^2) := Nat.mul_le_mul_left _ hsum
    _ = _ := by ring


open SqrtLog SqrtLog.Statement



open Filter SqrtLog SqrtLog.Statement


open SqrtLog SqrtLog.Statement

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamBudgets
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamBudgets.high_loop_budget_polynomial_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamBudgets.high_loop_budget_polynomial_oai
