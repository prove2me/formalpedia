-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeSourceBounds.retainedCap
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:26:28.163962+00:00
-- url     : https://prove2.me/submissions/742489a6-b986-4302-b738-c61ca3306271

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S185

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleLoader
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete head reloads for the attained-signature DFS.  The matrix comes
from the fixed native integer-entry machine, and each reload restores one
fixed retained-word bound before the next candidate scan. -/

noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open SignatureTupleProgram SignatureTupleNative SignatureTupleRefinement
open LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage


/-- The retained output cap itself is a fixed input polynomial, independent
of the caller's current storage bound and of the number of head reloads. -/
theorem retained_output_polynomial (s : Native.Inputs) (a : Data) (B : ℕ)
    (ha : Native.Ready s a) (hB : WordBound B a) :
    SignatureHeadLoader.retainedOutputBound s.n s.N s.D s.columnLength B≤10000*(B+2)^6 := by
  let X := B+2
  have hX : 1≤X := by dsimp [X]; omega
  have hX2 : 1≤X^2 := one_le_pow₀ hX
  have h16 : X≤X^6 := by simpa only [pow_one] using pow_le_pow_right₀ hX (by decide : 1≤6)
  have h26 : X^2≤X^6 := pow_le_pow_right₀ hX (by decide)
  have h56 : X^5≤X^6 := pow_le_pow_right₀ hX (by decide)
  have h06 : 1≤X^6 := one_le_pow₀ hX
  have h13 : X≤X^3 := by simpa only [pow_one] using pow_le_pow_right₀ hX (by decide : 1≤3)
  have hi := NodeTime.inputBounds s a ha B hB
  have hc := (NodeTime.columns_le hi).2
  have hn : s.n≤X := hi.n.trans (by dsimp [X]; omega)
  have hN : s.N≤X := by
    have hb : s.N≤B := by simpa [ha.factors,unary] using hB 129
    dsimp [X]; omega
  have hD : s.D≤X := hi.D.trans (by dsimp [X]; omega)
  have hb : B≤X := by dsimp [X]; omega
  have hcol : s.columnLength≤102*X^3 := by
    apply hc.trans
    calc
      _≤X*(100*X^2+2) := by dsimp [X]; gcongr; omega
      _≤X*(102*X^2) := by gcongr; omega
      _=102*X^3 := by ring
  have hcB : s.columnLength+B≤103*X^3 := by omega
  calc
    _≤X*(2*X+2)+2+(2*X+2)*X+X*(12*X*(103*X^3)+6*X+1) := by
      unfold SignatureHeadLoader.retainedOutputBound
      gcongr
    _=1236*X^5+10*X^2+5*X+2 := by ring
    _≤10000*X^6 := by omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleComplete
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete cursor invariants for the fixed attained-signature controller.
The integer head matrices come from native source words.  Each boundary uses
one retained cap; reload and predecessor-scan prefix bounds remain transient.
-/

noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete

open Classical
open OAI.Algorithms.SubexponentialSAT.SubexpLiftRing
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage
open SignatureTupleDFS SignatureTupleTraversal SignatureTupleProgram
open SignatureTupleNative SignatureTupleRefinement SignatureTupleLoader SignatureTupleSource

theorem retainedEnvelope_cap (s : ProducedSource) (A : ℕ) : RetainedCap s (retainedEnvelope s.bound A) := by
  have hi := NodeTime.inputBounds s.input s.source s.ready s.bound s.bounded
  have hn := hi.n
  have hr := hi.r
  have hnode : s.input.node.val ≤ s.bound := by
    simpa only [s.ready.node,unary,List.length_replicate] using s.bounded 307
  have hbase : s.base ≤ s.bound*s.bound := Nat.mul_le_mul hnode hr
  have hframes : 6*s.input.r*(s.input.n+1) ≤ 6*s.bound*(s.bound+1) := by gcongr
  have hout := retained_output_polynomial s.input s.source s.bound s.ready s.bounded
  constructor <;> unfold retainedEnvelope <;> omega

/-- The retained cap has fixed degree36. No input-dependent exponent is
introduced by the depth, assignment counter or repeated head reconstruction. -/
theorem retainedEnvelope_polynomial (B A : ℕ) :
    retainedEnvelope B A ≤ (100000*20000^6+10050)*(A+B+2)^36 := by
  let X := A+B+2
  change retainedEnvelope B A ≤ (100000*20000^6+10050)*X^36
  have hX : 1 ≤ X := by dsimp [X]; omega
  have h1 : X ≤ X^36 := by simpa only [pow_one] using pow_le_pow_right₀ hX (by decide : 1 ≤ 36)
  have h2 : X^2 ≤ X^36 := pow_le_pow_right₀ hX (by decide)
  have h6 : X^6 ≤ X^36 := pow_le_pow_right₀ hX (by decide)
  have h0 : 1 ≤ X^36 := one_le_pow₀ hX
  have hb : B ≤ X := by dsimp [X]; omega
  have hb1 : B+1 ≤ X := by dsimp [X]; omega
  have hb2 : B+2 ≤ X := by dsimp [X]; omega
  have ha : A ≤ X := by dsimp [X]; omega
  have hscan : scannerEnvelope B ≤ (100000*20000^6)*X^36 := by
    unfold scannerEnvelope
    rw [mul_pow,←pow_mul]
    change 100000*(20000^6*(B+2)^36) ≤ _
    calc
      _ ≤ 100000*(20000^6*X^36) := by gcongr
      _=_ := (Nat.mul_assoc _ _ _).symm
  have ho : 10000*(B+2)^6 ≤ 10000*X^36 := Nat.mul_le_mul_left 10000 ((Nat.pow_le_pow_left hb2 6).trans h6)
  have hf : 6*B*(B+1) ≤ 6*X^36 := by
    calc
      _ ≤ 6*X*X := by gcongr
      _=6*X^2 := by rw [pow_two,Nat.mul_assoc]
      _ ≤ 6*X^36 := Nat.mul_le_mul_left 6 h2
  have hs : B*B ≤ X^36 := (Nat.mul_le_mul hb hb).trans (by simpa only [pow_two] using h2)
  have hA := ha.trans h1
  have hB := hb.trans h1
  have hB1 := hb1.trans h1
  unfold retainedEnvelope
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete
end
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

private theorem square_le_compact (T : ℕ) : T^2 ≤ HeadSumBudgets.compactCap T := by
  have hp : T*T ≤ FactorTableBudgets.payloadEnvelope T := by
    unfold FactorTableBudgets.payloadEnvelope
    calc
      T*T = T*T*1 := (Nat.mul_one _).symm
      _ ≤ T*T*(2*(T+T+T)+2*T*(2*T)+2) := Nat.mul_le_mul_left _ (by omega)
  unfold HeadSumBudgets.compactCap
  rw [pow_two]
  omega

/-- The fixed degree36 scanner and both persistent frame banks fit the
already chosen compact head cap, including at ambient size zero. -/
theorem retained_le_compact (B A : ℕ) (hB : B ≤ A) :
    retainedEnvelope B 0 ≤ QueryHeadBudgets.compact A := by
  have hsource : 100*(A+2)^2 ≤ QueryHeadBudgets.sourceSize A+1 := by
    have h := Nat.mul_le_mul_right (100*(A+2)^2+2) (show 1 ≤ A+1 by omega)
    unfold QueryHeadBudgets.sourceSize
    omega
  have hpower : (A+2)^36 ≤ (A+2)^40 := Nat.pow_le_pow_right (by omega) (by decide)
  have hscalar : (QueryHeadBudgets.sourceSize A+1)^20 ≤ (QueryHeadBudgets.scalarCap A)^2 := by
    unfold QueryHeadBudgets.scalarCap
    rw [mul_pow,←pow_mul]
    norm_num
  calc
    retainedEnvelope B 0 ≤ (100000*20000^6+10050)*(B+2)^36 := by
      simpa only [Nat.zero_add] using retainedEnvelope_polynomial B 0
    _ ≤ (100000*20000^6+10050)*(A+2)^36 := by gcongr
    _ ≤ 100^20*(A+2)^40 := Nat.mul_le_mul (by norm_num) hpower
    _ = (100*(A+2)^2)^20 := by rw [mul_pow,←pow_mul]
    _ ≤ (QueryHeadBudgets.sourceSize A+1)^20 := Nat.pow_le_pow_left hsource 20
    _ ≤ (QueryHeadBudgets.scalarCap A)^2 := hscalar
    _ ≤ QueryHeadBudgets.compact A := square_le_compact _

/-- Native ready words already supply the numeric source dimensions; no
additional layout, scanner or successful-run premise is required. -/
theorem retainedCap (s : ProducedSource) (A : ℕ) (hs : s.bound ≤ A) :
    RetainedCap s (QueryHeadBudgets.compact A) := by
  have h := retainedEnvelope_cap s 0
  have hle := retained_le_compact s.bound A hs
  exact ⟨h.positive.trans hle,h.cursor.trans hle,h.frames.trans hle,
    h.output.trans hle,h.scanner.trans hle⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TupleRunBudgets
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryNodeSourceBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete capacities for the actual addressed node source. Its reference
snapshot is bounded only by retained query words, independently of caller
scratch, node index and the actual bootstrap cache witness. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeSourceBounds
open OAI BitProgram StructuredCalls SqrtLog SubexpSetupStorage
open LeafHeadSetupProgram LeafParametersProgram LeafProgram
open QueryNodeEvaluation


variable (query : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (query.input k))
  (first : MulticolorTypes.Word (LeafProgram.Query.packingProblem query k hg).r
    (LeafProgram.Query.packingProblem query k hg).Q)
  (tail : List (MulticolorTypes.Word (LeafProgram.Query.packingProblem query k hg).r
    (LeafProgram.Query.packingProblem query k hg).Q))
  (node : Fin (LeafProgram.Query.packingProblem query k hg).Q)
variable (a : QueryNodeEvaluation.Data) (bits : List Bool) (remaining : List (List Bool)) (A : ℕ)
  (hbank : NativeLayoutLoad.SourceBank (Native.queryInputsAddressed query k hg first tail node) a)
  (hparked : ∀ j : Fin 14,
    (a.stacks (NativeLayoutLoad.stackMap (LayoutMasters.high j))).length≤A)
  (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
  (hc : CacheCorrect (Native.queryInputsAddressed query k hg first tail node).height
    (unary (Native.queryInputsAddressed query k hg first tail node).R)
    (Native.queryInputsAddressed query k hg first tail node).width words)


local notation "src" => nodeSource query k hg first tail node a bits remaining A hbank hparked ra rd rc words hc

/-- The actual restricted source supplies the SAME compact cursor/frame/key
cap on every node, without using its prior transient scratch. -/
theorem retainedCap_oai : SignatureTupleComplete.RetainedCap src (QueryHeadBudgets.compact A) :=
  TupleRunBudgets.retainedCap src A (Nat.le_refl A)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeSourceBounds
end
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeSourceBounds.retainedCap_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeSourceBounds.retainedCap_oai
