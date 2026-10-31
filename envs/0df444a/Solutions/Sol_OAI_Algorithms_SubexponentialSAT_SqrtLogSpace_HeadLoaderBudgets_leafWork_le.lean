-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadLoaderBudgets.leafWork_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:40:02.482585+00:00
-- url     : https://prove2.me/submissions/0d89a472-ee14-4ed6-b3c7-97c4ea44dac0

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S179

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutMatrixProgramCompatibility
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact serialization and state projection at the all-row bucket boundary. -/
namespace SubexponentialSAT.SqrtLog.LayoutMatrixProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem ids_length_le (js : List ℕ) (n : ℕ) (h : ∀ v ∈ js, v ≤ n) :
    (ids js).length ≤ 1+(2*n+2)*js.length := by
  unfold ids
  have hh := ProgramEncoding.encodeRecords_length_le
    (js.map fun j => List.replicate j true) n (by
      intro word hw
      obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
      simpa using h v hv)
  simpa using hh

theorem commandCost_le_explicit (T B D n : ℕ) (js : List ℕ) (h : ∀ v ∈ js, v ≤ n) :
    commandCost T B D n js ≤
      19*(1+(2*n+2)*js.length)+12+
        D*(9*D+7*(1+(2*n+2)*js.length)+js.length*(T+24*B+8*n+45)+27) := by
  have hh := ids_length_le js n h
  unfold commandCost rowBodyCost
  calc
    _ ≤ 19*(1+(2*n+2)*js.length)+12+
        D*(9*D+7*(1+(2*n+2)*js.length)+js.length*(T+24*B+8*n+45)+25+2) := by
      gcongr
    _ = _ := by ring

end SubexponentialSAT.SqrtLog.LayoutMatrixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadIdentifierProgramSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadIdentifierProgram
open SubexponentialSAT BitProgram StructuredCalls

theorem count_le (p : ℕ → Bool) (n : ℕ) : count p n ≤ n := by
  simpa [count,chosenIds] using List.length_filter_le p (List.range n)

end SubexponentialSAT.SqrtLog.HeadIdentifierProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramBoundsPrepare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed polynomial cost of actual head-ID, support-mask, and factor-ID
preparation. Bounds include the real isolated-bank copy/cleanup costs. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Bounds
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage

 theorem selectedHeads_length (n : ℕ) (rows : List (List Bool)) (low : List Bool) (z : ℕ) :
    (selectedHeads n rows low z).length ≤ n :=
  HeadIdentifierProgram.count_le _ _

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Bounds

end
end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureHeadLoader
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The concrete head-loader is specialized to actual node bootstrap data.
All physical entry contracts are discharged by the native cache producer. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

private theorem matrixCost_polynomial (T B D n U : ℕ) (js : List ℕ)
    (hjs : ∀ v∈js,v ≤ n) (hT : T ≤ U) (hB : B ≤ U) (hD : D ≤ U)
    (hn : n ≤ U) (hh : js.length ≤ U) (hU : 1 ≤ U) :
    LayoutMatrixProgram.commandCost T B D n js+1 ≤ 1001*U^3 := by
  have hc := LayoutMatrixProgram.commandCost_le_explicit T B D n js hjs
  have hpoly : LayoutMatrixProgram.commandCost T B D n js ≤ 1000*U^3 := by
    apply hc.trans
    calc
      _ ≤ 19*(1+(2*U+2)*U)+12+
        U*(9*U+7*(1+(2*U+2)*U)+U*(U+24*U+8*U+45)+27) := by gcongr
      _ ≤ 1000*U^3 := by
        have h12 : U ≤ U^2 := by nlinarith only [hU]
        have h23 : U^2 ≤ U^3 := pow_le_pow_right₀ hU (by decide)
        nlinarith only [hU,h12,h23]
  have h1 : 1 ≤ U^3 := one_le_pow₀ hU
  omega

private theorem loaderArithmetic_bound (A size matrix B D n U : ℕ)
    (hU : 1 ≤ U) (hA : A ≤ U) (hS : size ≤ U) (hB : B ≤ U)
    (hD : D ≤ U) (hn : n ≤ U) (hm : matrix ≤ 1001*U^3) :
    let live := A+5*size^2+matrix
    let shift := 10000*(D+1)*(n+1)*(live+B+1)^2
    100000*(A+size^3+1)+(matrix+1878*(live+1))+
      (shift+147*(live+shift+1))+(2*(live+shift)+3) ≤ 100000000000000*U^8 := by
  let live := A+5*size^2+matrix
  let shift := 10000*(D+1)*(n+1)*(live+B+1)^2
  have h13 : U ≤ U^3 := by simpa only [pow_one] using pow_le_pow_right₀ hU (by decide : 1 ≤ 3)
  have h23 : U^2 ≤ U^3 := pow_le_pow_right₀ hU (by decide)
  have h38 : U^3 ≤ U^8 := pow_le_pow_right₀ hU (by decide)
  have h18 : 1 ≤ U^8 := one_le_pow₀ hU
  have hs2 : size^2 ≤ U^2 := Nat.pow_le_pow_left hS 2
  have hs3 : size^3 ≤ U^3 := Nat.pow_le_pow_left hS 3
  have hlive : live ≤ 1007*U^3 := by dsimp [live]; omega
  have hw : live+B+1 ≤ 1009*U^3 := by omega
  have hshift : shift ≤ 40723240000*U^8 := by
    calc
      _ ≤ 10000*(2*U)*(2*U)*(1009*U^3)^2 := by
        dsimp only [shift]
        gcongr <;> omega
      _ = 40723240000*U^8 := by ring
  change 100000*(A+size^3+1)+(matrix+1878*(live+1))+
    (shift+147*(live+shift+1))+(2*(live+shift)+3) ≤ 100000000000000*U^8
  omega

/-- One fixed power bounds every concrete preparation, matrix, shift, and
cleanup cost. No input-dependent exponent is introduced. -/
theorem localWork_le_monomial (s : Native.Inputs) (z A : ℕ) :
    localWork s z A ≤ 100000000000000*(workSize s z A)^8 := by
  let U := workSize s z A
  let size := Bounds.preparationSize s.n s.N s.rows s.low (s.Q*s.r) z
  let matrix := LayoutMatrixProgram.commandCost s.columnTime s.columnLength s.D s.n
    (selectedHeads s.n s.rows s.low z)+1
  have hU : 1 ≤ U := by dsimp [U,workSize]; omega
  have hA : A ≤ U := by dsimp [U,workSize]; omega
  have hS : size ≤ U := by dsimp [U,workSize,size]; omega
  have hT : s.columnTime ≤ U := by dsimp [U,workSize]; omega
  have hB : s.columnLength ≤ U := by dsimp [U,workSize]; omega
  have hD : s.D ≤ U := by dsimp [U,workSize]; omega
  have hn : s.n ≤ U := by dsimp [U,workSize]; omega
  have hm : matrix ≤ 1001*U^3 := matrixCost_polynomial _ _ _ _ _ _
    (fun v hv => (HeadIdentifierProgram.chosenIds_bound _ _ v hv).le)
    hT hB hD hn ((Bounds.selectedHeads_length s.n s.rows s.low z).trans hn) hU
  exact loaderArithmetic_bound A size matrix s.columnLength s.D s.n U hU hA hS hB hD hn hm

/-- The paid address/import/export ABI has the same fixed-degree envelope. -/
theorem leafWork_le_monomial (s : Native.Inputs) (z A : ℕ) :
    36*A+22*(localWork s z A+1)+35 ≤ 10000000000000000*(workSize s z A)^8 := by
  have h := localWork_le_monomial s z A
  have hA : A ≤ workSize s z A := by unfold workSize; omega
  have hU : 1 ≤ workSize s z A := by unfold workSize; omega
  have hpow : workSize s z A ≤ (workSize s z A)^8 := by
    simpa only [pow_one] using pow_le_pow_right₀ hU (by decide : 1 ≤ 8)
  have h1 : 1 ≤ (workSize s z A)^8 := one_le_pow₀ hU
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
end
end

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

/-- One deliberately coarse fixed polynomial pays both native column costs. -/
theorem columnEnvelope_le (X : ℕ) : columnEnvelope X ≤ 10000000000000000*(X+1)^8 := by
  have hp (j : ℕ) (hj : j ≤ 8) : X^j ≤ (X+1)^8 :=
    (Nat.pow_le_pow_left (Nat.le_succ X) j).trans (Nat.pow_le_pow_right (by omega) hj)
  have h0 : 1 ≤ (X+1)^8 := by simpa using hp 0 (by decide)
  have h1 : X ≤ (X+1)^8 := by simpa using hp 1 (by decide)
  have h2 := hp 2 (by decide)
  have h3 := hp 3 (by decide)
  have h4 := hp 4 (by decide)
  have h5 := hp 5 (by decide)
  have h6 := hp 6 (by decide)
  have h7 := hp 7 (by decide)
  have h8 := hp 8 (by decide)
  dsimp only [columnEnvelope,entryEnvelope]
  conv_lhs => ring_nf
  omega

end SubexponentialSAT.SqrtLog.NodeTime

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadLoaderBudgets
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed polynomial bounds for the actual head loader from its retained
source words. Column time is derived from the native integer-entry program;
the outer loop's address is charged by its actual unary word length. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadLoaderBudgets

open OAI BitProgram StructuredCalls SqrtLog SubexpSetupStorage
open SqrtLog.LeafHeadSetupProgram

private theorem columnLength_polynomial (B X : ℕ) (hBX : B+2 ≤ X) :
    (B+1)*(100*(B+2)^2+2) ≤ 102*X^8 := by
  have hX : 1 ≤ X := by omega
  have hX2 : 1 ≤ X^2 := one_le_pow₀ hX
  have h38 : X^3 ≤ X^8 := pow_le_pow_right₀ hX (by decide)
  calc
    _ ≤ X*(100*X^2+2) := by gcongr; omega
    _ ≤ X*(102*X^2) := by gcongr; omega
    _ = 102*X^3 := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ h38

/-- The source bank includes the ambient/factor counters, the complete row
word, low mask, native metadata and the integer-arithmetic widths. -/
theorem preparationSize_le (s : Native.Inputs) (a : Data) (B A z : ℕ)
    (ha : Native.Ready s a) (hB : WordBound B a)
    (hrows : s.rows.length = s.n+s.N) (hz : z ≤ A) :
    Bounds.preparationSize s.n s.N s.rows s.low (s.Q*s.r) z ≤ 7*B+A+2 := by
  have hn : s.n ≤ B := by simpa [ha.ambient,unary] using hB 128
  have hN : s.N ≤ B := by simpa [ha.factors,unary] using hB 129
  have hw : s.Q*s.r ≤ B := by simpa [ha.wordWidth,unary] using hB 132
  have hf : s.rows.flatten.length ≤ B := by simpa only [ha.words] using hB 133
  have hl : s.low.length ≤ B := by simpa only [ha.low] using hB 134
  unfold Bounds.preparationSize
  omega

/-- No column evaluator or successful running-time witness is assumed.
The actual native column budget follows from the physically stored inputs. -/
theorem workSize_le (s : Native.Inputs) (a : Data) (B A z : ℕ)
    (ha : Native.Ready s a) (hB : WordBound B a)
    (hrows : s.rows.length = s.n+s.N) (hz : z ≤ A) :
    SignatureHeadLoader.workSize s z A ≤ sizeCoefficient*(A+B+2)^8 := by
  let X := A+B+2
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hBX : B+2 ≤ X := by dsimp [X]; omega
  have hpow : X ≤ X^8 := by
    simpa only [pow_one] using pow_le_pow_right₀ hX (by decide : 1 ≤ 8)
  have h1 : 1 ≤ X^8 := one_le_pow₀ hX
  have hA : A ≤ X^8 := (show A ≤ X by dsimp [X]; omega).trans hpow
  have hBs : B ≤ X^8 := (show B ≤ X by dsimp [X]; omega).trans hpow
  have hi := NodeTime.inputBounds s a ha B hB
  have hc := NodeTime.columns_le hi
  have ht : s.columnTime ≤ 10000000000000000*X^8 :=
    hc.1.trans ((NodeTime.columnEnvelope_le (B+1)).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hBX 8)))
  have hl : s.columnLength ≤ 102*X^8 :=
    hc.2.trans (columnLength_polynomial B X hBX)
  have hp := preparationSize_le s a B A z ha hB hrows hz
  have hn := hi.n
  have hd := hi.D
  change SignatureHeadLoader.workSize s z A ≤ sizeCoefficient*X^8
  unfold SignatureHeadLoader.workSize sizeCoefficient
  omega

/-- Paid address staging, import, export and cleanup have the same degree64
envelope. The resource use of the outer repeated run remains a separate bound. -/
theorem leafWork_le_oai (s : Native.Inputs) (a : Data) (B A z : ℕ)
    (ha : Native.Ready s a) (hB : WordBound B a)
    (hrows : s.rows.length = s.n+s.N) (hz : z ≤ A) :
    36*A+22*(SignatureHeadLoader.localWork s z A+1)+35 ≤
      (10000000000000000*sizeCoefficient^8)*(A+B+2)^64 := by
  apply (SignatureHeadLoader.leafWork_le_monomial s z A).trans
  calc
    _ ≤ 10000000000000000*(sizeCoefficient*(A+B+2)^8)^8 := by
      gcongr
      exact workSize_le s a B A z ha hB hrows hz
    _ = _ := by simp only [mul_pow, ← pow_mul, show 8*8=64 from rfl, mul_assoc]


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadLoaderBudgets
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadLoaderBudgets.leafWork_le_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadLoaderBudgets.leafWork_le_oai
