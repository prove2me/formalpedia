-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.entryAt
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:18:34.057878+00:00
-- url     : https://prove2.me/submissions/b6d3f662-b265-46d1-b7e8-9d1caa063cb3

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S174
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_EntryBank_command_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixEntryScalar
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A scalar generating polynomial for the actual matrix entries

The coefficient of degree j equals 2^j times the j-th elementary projector
kernel. Consequently normalized coefficients need only scalar polynomial
arithmetic, with no enumeration of subsets in the eventual implementation.
-/

/-! The scalar kernel has only three nonzero local factors: 1, -X, and 1+X. -/

/-!
# Exact binomial formula for the implemented multicolor matrix

This connects scalar additions and sign changes to the very same matrix
used in the support and rank proofs. The only normalization hypothesis is
that the field has characteristic different from two.
-/

namespace SubexponentialSAT.Subexp.MatrixEntryKernel

open SubexponentialSAT.MulticolorTypes
open scoped BigOperators

variable {r Q Δ : ℕ} {K : Type*} [Field K]

theorem same_not_swap_iff (i : Fin Δ) (u y : UniversalType r Q Δ) (l : Fin Q) :
    (pair i u l = pair i y l ∧ (u.slot i l, u.head l) ≠ pair i y l) ↔
      (u.head l ≠ u.slot i l ∧ pair i u l = pair i y l) := by
  constructor
  · rintro ⟨hs, ht⟩
    refine ⟨?_, hs⟩
    intro hf
    apply ht
    have he : (u.slot i l, u.head l) = pair i u l := by simp [pair, hf]
    exact he.trans hs
  · rintro ⟨hf, hs⟩
    refine ⟨hs, ?_⟩
    intro ht
    exact hf (congrArg Prod.fst (hs.trans ht.symm))

theorem swap_not_same_iff (i : Fin Δ) (u y : UniversalType r Q Δ) (l : Fin Q) :
    ((u.slot i l, u.head l) = pair i y l ∧ pair i u l ≠ pair i y l) ↔
      (u.head l ≠ u.slot i l ∧ (u.slot i l, u.head l) = pair i y l) := by
  constructor
  · rintro ⟨ht, hs⟩
    refine ⟨?_, ht⟩
    intro hf
    apply hs
    have he : pair i u l = (u.slot i l, u.head l) := by simp [pair, hf]
    exact he.trans ht
  · rintro ⟨hf, ht⟩
    refine ⟨ht, ?_⟩
    intro hs
    exact hf (congrArg Prod.fst (hs.trans ht.symm))

end SubexponentialSAT.Subexp.MatrixEntryKernel

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixScanSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.allCompatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Arithmetic meaning of the two physical unary counters and the
compatibility register, including the one-hot color encoding boundary. -/

namespace SubexponentialSAT.Subexp.MatrixScanProgram

open BitProgram StructuredCalls StackRoutines

theorem encodeColor_injective {r : ℕ} : Function.Injective (@encodeColor r) := by
  intro c d h
  have he := congrFun (List.ofFn_injective h) c
  simp only [decide_true] at he
  exact (of_decide_eq_true he.symm).symm

@[simp] theorem encodeColor_eq_iff {r : ℕ} (c d : Fin r) :
    encodeColor c = encodeColor d ↔ c = d := encodeColor_injective.eq_iff

theorem encodeColor_pair_eq {r : ℕ} (a b c d : Fin r) :
    encodeColor a ++ encodeColor b = encodeColor c ++ encodeColor d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
    exact ⟨encodeColor_injective h1, encodeColor_injective h2⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem same_typedRow {r Q Δ : ℕ} (i : Fin Δ)
    (u y : MulticolorTypes.UniversalType r Q Δ) (l : Fin Q) :
    same (typedRow i u y l) = decide (u.head l = y.head l ∧ u.slot i l = y.slot i l) := by
  simp [same, typedRow, encodeColor_pair_eq]

theorem swapped_typedRow {r Q Δ : ℕ} (i : Fin Δ)
    (u y : MulticolorTypes.UniversalType r Q Δ) (l : Fin Q) :
    swapped (typedRow i u y l) = decide (u.slot i l = y.head l ∧ u.head l = y.slot i l) := by
  simp [swapped, typedRow, encodeColor_pair_eq]

end SubexponentialSAT.Subexp.MatrixScanProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixEntryEvaluation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Connect the concrete scan counters and adjacent-add value to the actual
joint matrix. These are refinement lemmas for the physical component programs,
not alternative definitions of their runtime instructions. -/

namespace SubexponentialSAT.Subexp.MatrixEntryEvaluation

open MulticolorTypes MatrixScanProgram
open scoped BigOperators

variable {r Q Δ : ℕ}

theorem unchangedCount_sum (ws : List ColorRow) :
    unchangedCount ws = (ws.map (fun w => if same w && !swapped w then 1 else 0)).sum := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [unchangedCount, ih, Nat.add_comm]

theorem transposedCount_sum (ws : List ColorRow) :
    transposedCount ws = (ws.map (fun w => if swapped w && !same w then 1 else 0)).sum := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [transposedCount, ih, Nat.add_comm]

theorem same_pair (i : Fin Δ) (u y : UniversalType r Q Δ) (l : Fin Q) :
    same (typedRow i u y l) = decide (MatrixEntryKernel.pair i u l = MatrixEntryKernel.pair i y l) := by
  simpa [MatrixEntryKernel.pair, Prod.mk.injEq] using same_typedRow i u y l

theorem swapped_pair (i : Fin Δ) (u y : UniversalType r Q Δ) (l : Fin Q) :
    swapped (typedRow i u y l) = decide ((u.slot i l, u.head l) = MatrixEntryKernel.pair i y l) := by
  simpa [MatrixEntryKernel.pair, Prod.mk.injEq] using swapped_typedRow i u y l

theorem unchanged_test (i : Fin Δ) (u y : UniversalType r Q Δ) (l : Fin Q) :
    (same (typedRow i u y l) && !swapped (typedRow i u y l)) =
      decide (u.head l ≠ u.slot i l ∧ MatrixEntryKernel.pair i u l = MatrixEntryKernel.pair i y l) := by
  apply Bool.eq_iff_iff.mpr
  simpa [same_pair, swapped_pair] using MatrixEntryKernel.same_not_swap_iff i u y l

theorem transposed_test (i : Fin Δ) (u y : UniversalType r Q Δ) (l : Fin Q) :
    (swapped (typedRow i u y l) && !same (typedRow i u y l)) =
      decide (u.head l ≠ u.slot i l ∧ (u.slot i l, u.head l) = MatrixEntryKernel.pair i y l) := by
  apply Bool.eq_iff_iff.mpr
  simpa [same_pair, swapped_pair] using MatrixEntryKernel.swap_not_same_iff i u y l

theorem unchangedCount_rows (i : Fin Δ) (u y : UniversalType r Q Δ) :
    unchangedCount (rows i u y) = (MatrixEntryKernel.allUnchanged i u y).card := by
  rw [unchangedCount_sum]
  simp only [rows, List.map_ofFn, List.sum_ofFn, Function.comp_def, unchanged_test, decide_eq_true_eq]
  simp [MatrixEntryKernel.allUnchanged]

theorem transposedCount_rows (i : Fin Δ) (u y : UniversalType r Q Δ) :
    transposedCount (rows i u y) = (MatrixEntryKernel.allTransposed i u y).card := by
  rw [transposedCount_sum]
  simp only [rows, List.map_ofFn, List.sum_ofFn, Function.comp_def, transposed_test, decide_eq_true_eq]
  simp [MatrixEntryKernel.allTransposed]

theorem unchangedCount_le (i : Fin Δ) (u y : UniversalType r Q Δ) :
    unchangedCount (rows i u y) ≤ Q := by
  rw [unchangedCount_rows]
  have h := Finset.card_le_card (Finset.filter_subset
    (fun l : Fin Q => u.head l ≠ u.slot i l ∧
      MatrixEntryKernel.pair i u l = MatrixEntryKernel.pair i y l) Finset.univ)
  simpa [MatrixEntryKernel.allUnchanged] using h

theorem transposedCount_le (i : Fin Δ) (u y : UniversalType r Q Δ) :
    transposedCount (rows i u y) ≤ Q := by
  rw [transposedCount_rows]
  have h := Finset.card_le_card (Finset.filter_subset
    (fun l : Fin Q => u.head l ≠ u.slot i l ∧
      (u.slot i l, u.head l) = MatrixEntryKernel.pair i y l) Finset.univ)
  simpa [MatrixEntryKernel.allTransposed] using h

end SubexponentialSAT.Subexp.MatrixEntryEvaluation

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceValuesProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! The scalar callback calls the actual integer numerator program, then the
actual binary-to-ring scaler. Its integer result is never supplied as input. -/


/-! Closed correction-table construction from type metadata and integer/ring
caches. No correction-scalar table is supplied to the program or theorem. -/


/-! Uniform polynomial accounting and per-index observation of generated
correction tables. All parameters describe actual bytes and runtime counts. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open MulticolorTypes IntegerRingLiftProgram
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram (WordPair pairValue pairLength)
open scoped BigOperators

theorem scalar_cost_le (A R Q W P n h : ℕ) (hn : n ≤ Q) (hh : h ≤ Q) :
    LayoutProgramScalar.FromCounts.totalCost A R n h W P ≤ scalarAllowance A R Q W P := by
  unfold LayoutProgramScalar.FromCounts.totalCost scalarAllowance
    LayoutProgramScalar.FromCounts.binomialCost LayoutProgramScalar.numeratorPrepareCost
    LayoutProgramScalar.numeratorFoldCost
  gcongr <;> omega

theorem numerator_cost_le {r Q : ℕ} (A R W P : ℕ) (node : Fin Q)
    (u y : UniversalType r Q 1) :
    LayoutProgram.Numerator.budget A R W P node u y ≤ numeratorAllowance r Q A R W P := by
  have hu := Subexp.MatrixEntryEvaluation.unchangedCount_le (0 : Fin 1) u y
  have hh := Subexp.MatrixEntryEvaluation.transposedCount_le (0 : Fin 1) u y
  have hs := scalar_cost_le A R Q W P
    (Subexp.MatrixScanProgram.unchangedCount (Subexp.MatrixEntryEvaluation.rows 0 u y)-1)
    (Subexp.MatrixScanProgram.transposedCount (Subexp.MatrixEntryEvaluation.rows 0 u y))
    (by omega) hh
  have hg : Subexp.MatrixExtendedEntryProgram.guardStageCost r Q 1 0 node.val ≤
      Subexp.MatrixExtendedEntryProgram.guardStageCost r Q 1 0 Q := by
    unfold Subexp.MatrixExtendedEntryProgram.guardStageCost
    gcongr
    exact node.isLt.le
  unfold LayoutProgram.Numerator.budget numeratorAllowance
  omega

end SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramEntryBankCost
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Uniform numerical bounds for the concrete entry program. The universal
type words affect the result, but no type-dependent search is charged here. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

open SubexponentialSAT.BitProgram SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes RowSelectionProgram

variable {r Q : ℕ}

theorem integerLength_bound (R W P D : ℕ) (u y : UniversalType r Q 1) :
    IntegerEntry.lengthBound R W P u y+D+1 ≤ integerLength R W P D := by
  unfold IntegerEntry.lengthBound integerLength
  gcongr
  exact Nat.sub_le _ _

theorem integerLength_one (R W P D : ℕ) : 1 ≤ integerLength R W P D := by
  unfold integerLength
  omega

theorem integerBudget_bound (A R W P D : ℕ) (t : Fin Q)
    (u y : UniversalType r Q 1) :
    IntegerEntry.budget A R W P D t u y ≤ integerBudget r Q A R W P D := by
  have hn := LayoutSourceValuesProgram.Native.numerator_cost_le A R W P t u y
  have hg : MatrixExtendedEntryProgram.guardStageCost r Q 1 0 t.val ≤
      MatrixExtendedEntryProgram.guardStageCost r Q 1 0 Q := by
    unfold MatrixExtendedEntryProgram.guardStageCost
    gcongr
    exact t.isLt.le
  have hl : IntegerEntry.lengthBound R W P u y ≤ R*LayoutProgramScalar.termGrowth (2*W+P) := by
    unfold IntegerEntry.lengthBound
    exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  unfold IntegerEntry.budget integerBudget
  gcongr

end SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutFiberSumProgramNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Discharge the fiber loop's callback by the concrete integer-entry machine.
All remaining assumptions describe its actual caches and numerical bounds. -/
namespace SubexponentialSAT.SqrtLog.LayoutFiberSumProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.Subexp.ConstructivePacking RowSelectionProgram

theorem data_low_frame (base : Data) (regs : Fin 16 → Bool)
    (queue column : List Bool) (acc next : WordPair)
    (i : Fin 256) (hi : i.val < 212) :
    (data base regs queue column acc next).stacks i=base.stacks i := by
  have h212 : i≠212 := by
    intro h
    have he : i.val=212 := congrArg Fin.val h
    omega
  have h213 : i≠213 := by
    intro h
    have he : i.val=213 := congrArg Fin.val h
    omega
  have h214 : i≠214 := by
    intro h
    have he : i.val=214 := congrArg Fin.val h
    omega
  have h253 : i≠253 := by
    intro h
    have he : i.val=253 := congrArg Fin.val h
    omega
  have h254 : i≠254 := by
    intro h
    have he : i.val=254 := congrArg Fin.val h
    omega
  have h255 : i≠255 := by
    intro h
    have he : i.val=255 := congrArg Fin.val h
    omega
  simp [data,bank,h212,h213,h214,h253,h254,h255]

theorem data_cached {r Q : ℕ} (base : Data) (c : LayoutProgram.Numerator.Saved)
    (t : Fin Q) (hc : LayoutProgram.EntryBank.CacheWords (r:=r) base c t)
    (regs : Fin 16 → Bool) (queue column : List Bool) (acc next : WordPair) :
    LayoutProgram.EntryBank.CacheWords (r:=r) (data base regs queue column acc next) c t := by
  constructor
  · simpa [data,bank] using hc.hp
  · simpa [data,bank] using hc.hn
  · simpa [data,bank] using hc.hw
  · simpa [data,bank] using hc.hpos
  · exact hc.hneg
  · simpa [data,bank] using hc.hr
  · simpa [data,bank] using hc.ha
  · simpa [data,bank] using hc.colors
  · simpa [data,bank] using hc.nodes
  · simpa [data,bank] using hc.node
  · simpa [data,bank] using hc.typeWidth

theorem finish_data (base : Data) (hwork : ∀ i : Fin 256, i.val < 200 → base.stacks i=[])
    (regs rf : Fin 16 → Bool) (queue column : List Bool) (acc result : WordPair) :
    LayoutProgram.EntryBank.finish (data base regs queue column acc ([],[])) rf result=
      data base rf queue column acc result := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    by_cases hi : i.val < 200
    · have h212 : i ≠ 212 := by intro h; have := congrArg Fin.val h; omega
      have h213 : i ≠ 213 := by intro h; have := congrArg Fin.val h; omega
      have h214 : i ≠ 214 := by intro h; have := congrArg Fin.val h; omega
      have h253 : i ≠ 253 := by intro h; have := congrArg Fin.val h; omega
      have h254 : i ≠ 254 := by intro h; have := congrArg Fin.val h; omega
      have h255 : i ≠ 255 := by intro h; have := congrArg Fin.val h; omega
      simpa [LayoutProgram.EntryBank.finish,data,bank,hi,h212,h213,h214,h253,h254,h255]
        using hwork i hi
    · by_cases h254 : i=254
      · subst i; simp [bank]
      by_cases h255 : i=255
      · subst i; simp [bank]
      simp [data,bank,hi,h254,h255]

/-- The concrete metadata lookup and universal integer-entry program fulfills
the native fiber callback, even with arbitrary accumulator/queue contents.
`U` bounds actual metadata lookup time; it is not a program-service premise. -/
theorem entryAt_oai {r Q D : ℕ} (P : PackingData (Fin D) (UniversalType r Q 1))
    (Hwords : List (List Bool)) (width : List Bool) (power : WordPair)
    (aWord : List Bool) (R : ℕ) (t : Fin Q) (row col : Fin D)
    (base : Data) (S U : ℕ)
    (hlen : Hwords.length=R) (hwords : ∀ x∈Hwords,x.length=width.length)
    (hvalues : Hwords.map BinaryArithmetic.toNat=(List.range R).map (LayoutCoefficientRecurrence.H aWord.length))
    (hp : pairValue power=(2:ℤ)^(R-1)) (hpt : LayoutProgramScalar.wordTotal power=2^(R-1))
    (hpos : BinaryArithmetic.toNat power.1=2^(R-1))
    (hwidth : Q+1 ≤ width.length) (hAQ : aWord.length ≤ Q) (hQ : 1 ≤ Q)
    (hc : LayoutProgram.EntryBank.CacheWords (r:=r) base
      (LayoutProgramScalar.FromCounts.unsignedSaved Hwords width power R aWord) t)
    (hwork : ∀ i : Fin 256, i.val < 200 → base.stacks i=[])
    (hmeta : base.stacks 200=SelectorProgram.rawRecords (LayoutProgram.EntryBank.metadataRecords P))
    (hrow : base.stacks 252=List.replicate row.val true)
    (hsize : ∀ i : Fin 256, i.val < 212 → (base.stacks i).length ≤ S)
    (hrs : row.val ≤ S) (hcs : col.val ≤ S)
    (hmetadata : ∀ v, LayoutProgram.EntryBank.MetadataBound
      (PackingMetadata.value P CollisionProgram.encodeType v) S)
    (hlookup : LayoutProgram.EntryBank.lookupBudget P row col ≤ U) :
    EntryAt LayoutProgram.EntryBank.command base (incidenceValue P aWord.length R t row)
      (nativeTime r Q R width power aWord S U) (nativeLength R width power)
      (LayoutProgram.constraintMassBound Q R) col.val := by
  intro regs queue acc
  let a := data base regs queue (unary col.val) acc ([],[])
  have hready : LayoutProgram.EntryBank.BaseReady a := by
    refine ⟨?_,by simp [a,data,bank],by simp [a,data,bank]⟩
    intro i hi
    rw [data_low_frame base regs queue (unary col.val) acc ([],[]) i (by omega)]
    exact hwork i hi
  obtain ⟨n,hn,rf,result,he,hv,hm,hl⟩ := LayoutProgram.EntryBank.command_eval
    P Hwords width power aWord R t row col a S
    (LayoutProgram.EntryBank.integerBudget r Q aWord.length R width.length (pairLength power) power.1.length)
    (nativeLength R width power) hlen hwords hvalues hp hpt hpos hwidth hAQ hQ
    (data_cached base _ t hc regs queue (unary col.val) acc ([],[])) hready
    (by simpa [a,data,bank] using hmeta) (by simpa [a,data,bank] using hrow)
    (by simp [a,data,bank,unary])
    (by
      intro i hi
      rw [data_low_frame base regs queue (unary col.val) acc ([],[]) i hi]
      exact hsize i hi) hrs hcs hmetadata
    (fun u y => LayoutProgram.EntryBank.integerBudget_bound _ _ _ _ _ t u y)
    (fun u y => LayoutProgram.EntryBank.integerLength_bound _ _ _ _ u y)
    (LayoutProgram.EntryBank.integerLength_one _ _ _ _)
  have hf := finish_data base hwork regs rf queue (unary col.val) acc result
  change LayoutProgram.EntryBank.finish a rf result=_ at hf
  rw [hf] at he
  refine ⟨n,?_,rf,result,he,?_,hl,hm⟩
  · unfold nativeTime
    omega
  · simpa [incidenceValue] using hv

end SubexponentialSAT.SqrtLog.LayoutFiberSumProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.entryAt_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.entryAt_oai
