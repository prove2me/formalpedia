-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets.loader_caps
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:49:29.233955+00:00
-- url     : https://prove2.me/submissions/d7e1011e-04f8-482b-b5e3-c33d7c1e4530

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S175
import Definitions.Def_OAIQ081S179

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_NodeTimeSource
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The native integer-entry and column costs are polynomials in actual
retained source-word lengths, with the full incidence count preserved. -/
namespace SubexponentialSAT.SqrtLog.NodeTime
open SubexponentialSAT Subexp SubexpLiftRing
open SubexponentialSAT.MulticolorTypes LayoutProgram LeafHeadSetupProgram
open LeafHeadSetupProgram.Bounds

private theorem integer_diagonal (X : ℕ) :
    EntryBank.integerBudget X X X X X X X ≤ 10000000000000*(X+1)^5 := by
  have hp (j : ℕ) (hj : j ≤ 5) : X^j ≤ (X+1)^5 :=
    (Nat.pow_le_pow_left (Nat.le_succ X) j).trans (Nat.pow_le_pow_right (by omega) hj)
  have h0 : 1 ≤ (X+1)^5 := by simpa using hp 0 (by decide)
  have h1 : X ≤ (X+1)^5 := by simpa using hp 1 (by decide)
  have h2 := hp 2 (by decide)
  have h3 := hp 3 (by decide)
  have h4 := hp 4 (by decide)
  have h5 := hp 5 (by decide)
  dsimp only [EntryBank.integerBudget,LayoutProgramScalar.termGrowth,
    LayoutSourceValuesProgram.Native.numeratorAllowance,LayoutSourceValuesProgram.Native.scalarAllowance,
    MatrixExtendedEntryProgram.guardStageCost,MatrixEntryProgram.scanStageCost,CollisionProgram.typeWidth,
    LayoutProgramScalar.FromCounts.binomialCost,LayoutProgramScalar.numeratorPrepareCost,
    LayoutProgramScalar.numeratorFoldCost,UniversalRowMismatchTypes.extractBudget]
  norm_num only [Fin.val_zero]
  conv_lhs => ring_nf
  omega

theorem integerBudget_le (r Q A R W P D X : ℕ)
    (hr : r ≤ X) (hQ : Q ≤ X) (hA : A ≤ X) (hR : R ≤ X)
    (hW : W ≤ X) (hP : P ≤ X) (hD : D ≤ X) :
    EntryBank.integerBudget r Q A R W P D ≤ 10000000000000*(X+1)^5 := by
  apply le_trans _ (integer_diagonal X)
  dsimp only [EntryBank.integerBudget, LayoutProgramScalar.termGrowth,
    LayoutSourceValuesProgram.Native.numeratorAllowance, LayoutSourceValuesProgram.Native.scalarAllowance,
    MatrixExtendedEntryProgram.guardStageCost, MatrixEntryProgram.scanStageCost, CollisionProgram.typeWidth,
    LayoutProgramScalar.FromCounts.binomialCost, LayoutProgramScalar.numeratorPrepareCost,
    LayoutProgramScalar.numeratorFoldCost, UniversalRowMismatchTypes.extractBudget, LayoutProgramScalar.termGrowth]
  gcongr

/-- The diagonal uses the encoded width, not the coefficient magnitude. -/
theorem integerLength_le (R W P D X : ℕ) (hR : R ≤ X) (hW : W ≤ X) (hP : P ≤ X) (hD : D ≤ X) :
    EntryBank.integerLength R W P D ≤ 100*(X+1)^2 := by
  unfold EntryBank.integerLength LayoutProgramScalar.termGrowth
  nlinarith [Nat.mul_le_mul hR (Nat.add_le_add (Nat.mul_le_mul_left 28 hW) (Nat.mul_le_mul_left 14 hP))]

end SubexponentialSAT.SqrtLog.NodeTime

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_NodeTimeColumns
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.NodeTime
open SubexponentialSAT Subexp SubexpLiftRing SubexpSetupStorage
open LeafHeadSetupProgram LeafHeadSetupProgram.Bounds
open LayoutProgram RowSelectionProgram

theorem inputBounds (s : Native.Inputs) (a : LeafHeadSetupProgram.Data)
    (h : Native.Ready s a) (B : ℕ) (hb : WordBound B a) : InputBounds s B := by
  have hp : (LayoutOwnerFiberProgram.stream s.plans).length ≤ B := by simpa only [h.plans] using hb 136
  have hc := Encoding.length_encodeList_lower (fun p : ℕ×ℕ => LayoutOwnerFiberProgram.pairPayload p.1 p.2) s.plans
  have hd : s.D ≤ B := by
    change s.plans.length+1 ≤ (LayoutOwnerFiberProgram.stream s.plans).length at hc
    rw [s.plans_length] at hc
    omega
  exact ⟨by simpa [h.ambient,unary] using hb 128,hd,
    by simpa [h.colors,unary] using hb 130,by simpa [h.nodes,unary] using hb 131,
    by simpa [h.order,unary] using hb 138,by simpa only [h.width] using hb 140,
    by simpa only [h.height] using hb 139,by simpa only [h.metadata] using hb 135,hp,
    by simpa [h.wordWidth,unary] using hb 132⟩

theorem columns_le {s : Native.Inputs} {B : ℕ} (h : InputBounds s B) :
    s.columnTime ≤ columnEnvelope (B+1) ∧ s.columnLength ≤ (B+1)*(100*(B+2)^2+2) := by
  let X := B+1
  have hx : B ≤ X := by dsimp [X]; omega
  have hn := h.n.trans hx
  have hd := h.D.trans hx
  have hr := h.r.trans hx
  have hq := h.Q.trans hx
  have ho := h.R.trans hx
  have hw := h.width.trans hx
  have hh := h.height.trans hx
  have hm := h.metadata.trans hx
  have hp := h.plans.trans hx
  have hqr := h.Qr.trans hx
  have hpower : s.power.1.length ≤ X := by
    simp only [Native.Inputs.power,IntegerCache.denominatorWord,List.length_append,
      List.length_replicate,List.length_singleton]
    dsimp [X]
    omega
  have hpair : pairLength s.power ≤ X := by
    simpa only [pairLength,Native.Inputs.power,List.length_nil,Nat.add_zero] using hpower
  have hlen : s.entryLength ≤ 100*(X+1)^2 := integerLength_le _ _ _ _ X ho hw hpair hpower
  have hib := integerBudget_le _ _ _ _ _ _ _ X hr hq hh ho hw hpair hpower
  have hs : s.size ≤ X*X+11*X+1 := by
    unfold Native.Inputs.size
    have hm := Nat.mul_le_mul ho hw
    omega
  have he : s.entryTime ≤ entryEnvelope X := by
    unfold Native.Inputs.entryTime Native.Inputs.lookupTime LayoutFiberSumProgram.nativeTime entryEnvelope
    have hu : 800*(s.metadata.length+s.D+1)^2+1 ≤ 800*(2*X+1)^2+1 := by gcongr ; omega
    dsimp only [Native.Inputs.entryLength] at hlen
    omega
  constructor
  · change s.columnTime ≤ columnEnvelope X
    unfold Native.Inputs.columnTime columnEnvelope
    gcongr ; omega
  · change s.D*(s.entryLength+2) ≤ X*(100*(X+1)^2+2)
    gcongr

end SubexponentialSAT.SqrtLog.NodeTime

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryVisitorLoadBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Source-parameter bounds for the full key produced from an actual shifted
incidence matrix. Every incidence row and every retained coefficient is charged. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoadBounds

open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport

theorem matrixBound_le_monomial {n D B L U : ℕ}
    (hU : 1 ≤ U) (hn : n ≤ U) (hD : D ≤ U) (hB : B ≤ U) (hL : L ≤ U) :
    matrixBound n D B L ≤ 31*U^3 := by
  have h12 : 1 ≤ U^2 := by simpa using (Nat.pow_le_pow_left hU 2)
  have h2 : U ≤ U^2 := Nat.le_self_pow (by decide) U
  calc
    _ ≤ U*(12*U*(U+U)+6*U+1) := by unfold matrixBound; gcongr
    _ ≤ U*(31*U^2) := by gcongr; nlinarith
    _ = 31*U^3 := by ring

theorem keySpaceBound_le_monomial {n D B L U : ℕ}
    (hU : 1 ≤ U) (hn : n ≤ U) (hD : D ≤ U) (hB : B ≤ U) (hL : L ≤ U) :
    keySpaceBound n D B L ≤ 1000000*U^10 := by
  let R := matrixBound n D B L
  let W := List.replicate L false
  have hR : R ≤ 31*U^3 := matrixBound_le_monomial hU hn hD hB hL
  have hp (k : ℕ) : 1 ≤ U^k := by simpa using (Nat.pow_le_pow_left hU k)
  have h13 : U ≤ U^3 := Nat.le_self_pow (by decide) U
  have h19 : U ≤ U^9 := Nat.le_self_pow (by decide) U
  have h49 : U^4 ≤ U^9 := Nat.pow_le_pow_right hU (by decide)
  have h310 : U^3 ≤ U^10 := Nat.pow_le_pow_right hU (by decide)
  have h110 : U ≤ U^10 := Nat.le_self_pow (by decide) U
  have hw : BucketProgram.widthBound W n R ≤ 34*U^4 := by
    calc
      _ = 1+n*(L+1+R) := by simp [W,BucketProgram.widthBound]
      _ ≤ 1+U*(U+1+31*U^3) := by gcongr
      _ ≤ 1+U*(33*U^3) := by gcongr; have := hp 3; omega
      _ = 1+33*U^4 := by ring
      _ ≤ 34*U^4 := by have := hp 4; omega
  have hrow : BucketProgram.rowCostBound W n R ≤ 519000*U^9 := by
    calc
      _ ≤ (2*U)*(200*(36*U^4)^2+34)+9*(34*U^4)+22 := by
        unfold BucketProgram.rowCostBound
        gcongr <;> have := hp 4 <;> omega
      _ = 518400*U^9+68*U+306*U^4+22 := by ring
      _ ≤ 519000*U^9 := by have := hp 9; omega
  have hfirst : 9*(n*(2*R+1)) ≤ 567*U^4 := by
    calc
      _ ≤ 9*(U*(63*U^3)) := by gcongr; have := hp 3; omega
      _ = 567*U^4 := by ring
  have hsig : BucketProgram.signatureRowBound W n R ≤ 520000*U^9 := by
    unfold BucketProgram.signatureRowBound
    have := hp 9
    omega
  have hprod : D*(BucketProgram.signatureRowBound W n R+2) ≤ 520002*U^10 := by
    calc
      _ ≤ U*(520002*U^9) := by gcongr; have := hp 9; omega
      _ = 520002*U^10 := by ring
  change 16*(L+n+R)+(7*R+D*(BucketProgram.signatureRowBound W n R+2)+8)+1 ≤ _
  have := hp 10
  omega

theorem matrixEnvelope_le_monomial (s : LeafHeadSetupProgram.Native.Inputs) {L U : ℕ}
    (hU : 1 ≤ U) (hn : s.n ≤ U) (hD : s.D ≤ U) (hB : s.columnLength ≤ U) (hL : L ≤ U) :
    matrixEnvelope s L ≤ 31*U^3 :=
  matrixBound_le_monomial hU hn hD hB hL

theorem keyEnvelope_le_monomial (s : LeafHeadSetupProgram.Native.Inputs) {L U : ℕ}
    (hU : 1 ≤ U) (hn : s.n ≤ U) (hD : s.D ≤ U) (hB : s.columnLength ≤ U) (hL : L ≤ U) :
    keyEnvelope s L ≤ 1000000*U^10 := by
  have h := keySpaceBound_le_monomial hU hn hD hB hL
  dsimp only [keyEnvelope,matrixEnvelope,keySpaceBound,keyCostBound] at h ⊢
  omega


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoadBounds
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

private theorem sourceSize_large (A : ℕ) : A+1 ≤ sourceSize A := by
  unfold sourceSize
  omega

private theorem load_envelope_le {n N D C L U : ℕ} (hU : 1 ≤ U)
    (hn : n ≤ U) (hN : N ≤ U) (hD : D ≤ U) (hC : C ≤ U) (hL : L ≤ U) :
    SignatureHeadLoader.retainedOutputBound n N D C L ≤ 41*U^3 := by
  have hm := QueryVisitorLoadBounds.matrixBound_le_monomial hU hn hD hC hL
  have h2 : U ≤ U^2 := Nat.le_self_pow (by decide) _
  have h3 : U^2 ≤ U^3 := Nat.pow_le_pow_right hU (by decide)
  have h13 : 1 ≤ U^3 := Nat.one_le_pow _ _ hU
  have hleft : n*(2*n+2) ≤ 4*U^2 := by
    calc
      _ ≤ U*(2*U+2) := by gcongr
      _ ≤ _ := by nlinarith
  have hright : (2*N+2)*N ≤ 4*U^2 := by
    calc
      _ ≤ (2*U+2)*U := by gcongr
      _ ≤ _ := by nlinarith
  unfold SignatureHeadLoader.retainedOutputBound
  change n*(2*n+2)+2+(2*N+2)*N+QueryVisitorLoadBounds.matrixBound n D C L ≤ _
  omega

/-- Physical master words derive the column, full matrix, full key and loader
output bounds. No column evaluator or successful layout run is assumed. -/
theorem loader_caps_oai (s : Native.Inputs) (a : Data) (A L : ℕ)
    (ha : Native.Ready s a) (hbound : WordBound A a) (hL : L ≤ A) :
    SignatureHeadLoader.retainedOutputBound s.n s.N s.D s.columnLength L ≤ scalarCap A ∧
    QueryVisitorLoadBounds.matrixEnvelope s L ≤ scalarCap A ∧
    QueryVisitorLoadBounds.keyEnvelope s L ≤ scalarCap A ∧
    11*s.n+6 ≤ scalarCap A := by
  have hi := NodeTime.inputBounds s a ha A hbound
  have hc := (NodeTime.columns_le hi).2
  have hN : s.N ≤ A := by simpa [ha.factors,unary] using hbound 129
  let U := sourceSize A+1
  have hAU : A+1 ≤ U := by dsimp [U]; have := sourceSize_large A; omega
  have hU : 1 ≤ U := by omega
  have hn : s.n ≤ U := by have := hi.n; omega
  have hN' : s.N ≤ U := by omega
  have hD : s.D ≤ U := by have := hi.D; omega
  have hC : s.columnLength ≤ U := by dsimp [U,sourceSize]; omega
  have hL' : L ≤ U := by omega
  have hl := load_envelope_le hU hn hN' hD hC hL'
  have hm := QueryVisitorLoadBounds.matrixEnvelope_le_monomial s hU hn hD hC hL'
  have hk := QueryVisitorLoadBounds.keyEnvelope_le_monomial s hU hn hD hC hL'
  have h3 : U^3 ≤ U^10 := Nat.pow_le_pow_right hU (by decide)
  have h1 : U ≤ U^10 := Nat.le_self_pow (by decide) _
  have h0 : 1 ≤ U^10 := Nat.one_le_pow _ _ hU
  change _ ≤ 1000100*U^10 ∧ _ ≤ 1000100*U^10 ∧ _ ≤ 1000100*U^10 ∧ _ ≤ 1000100*U^10
  exact ⟨by omega,by omega,by omega,by omega⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets.loader_caps_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets.loader_caps_oai
