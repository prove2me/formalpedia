-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.universal_generated
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:42:07.403024+00:00
-- url     : https://prove2.me/submissions/a98926cf-6077-404d-9161-5a160aad0fe8

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S186
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_SourceBank_native_universal_cleanup_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_SourceCache_native_difference
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_SourceCache_native_inverse
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_SourceWitness_universal

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingNodeProgramModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The physical radix generator emits precisely the coefficient encoding of
nodes in the actual supplied-polynomial unramified ring. -/
namespace SubexponentialSAT.SqrtLog.RingNodeProgram

open SubexponentialSAT BinaryArithmetic SubexpLiftRing SubexpQuarticRing
open RingProgram

theorem nodeCode_value (t d n : ℕ) (ht : 0 < t) (j : Fin d) :
    BinaryArithmetic.toNat (nodeCode t d n j).val = n / 3^j.val % 3 := by
  apply toNat_fixedBits_of_lt
  have hc : 2^2 ≤ 2^(2*t) := Nat.pow_le_pow_right (by decide) (by omega)
  rw [ternary_baseWidth]
  have hm := Nat.mod_lt (n / 3^j.val) (by decide : 0 < 3)
  norm_num at hc
  omega

theorem residueNode_coordinate {d : ℕ} (a : RingModel.Data d) (Q : ℕ)
    (hQ : Q < 3^d) (i : Fin Q) (j : Fin d) :
    (a.fieldCoordinates (a.residueNode Q hQ i) j).val = (i.val+1) / 3^j.val % 3 := by
  let index : Fin (3^d) := ⟨i.val+1, by omega⟩
  let v : Fin d → ZMod 3 := fun j =>
    ZMod.finEquiv 3 ((finFunctionFinEquiv.symm index) j)
  change (a.fieldCoordinates (a.fieldCoordinates.symm v) j).val = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- The physical words decode to the same nodes used by interpolation. -/
theorem nodeCode_decode (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : ScalarCache 3 t) (Q : ℕ) (hQ : Q < 3^d) (i : Fin Q) :
    (modelRing t ht hd a M cache).decode (nodeCode t d (i.val+1)) =
      a.node t Q ht hQ i := by
  rw [modelRing_decode]
  unfold RingModel.Data.node RingModel.Data.sectionValue
  congr 1
  funext j
  unfold wordValue
  rw [nodeCode_value t d (i.val+1) ht j, residueNode_coordinate]

end SubexponentialSAT.SqrtLog.RingNodeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_InterpolationCacheProgramModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Values computed by the physical interpolation-cache producer. Every
entry is a typed output of an executable ring program. The uniform inverse
routine has an explicit zero-diagonal interpretation. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram

open SubexponentialSAT
open scoped BigOperators

theorem negativeValue_decode (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (minusOne x : Coeff t d)
    (hm : (RingProgram.modelRing t ht hd a M cache).decode minusOne = -1) :
    (RingProgram.modelRing t ht hd a M cache).decode (negativeValue t a M cache minusOne x) =
      -(RingProgram.modelRing t ht hd a M cache).decode x := by
  let ops := RingProgram.modelRing t ht hd a M cache
  change ops.decode (ops.mulRun x minusOne).1 = -ops.decode x
  rw [ops.mul_correct,hm]
  exact mul_neg_one (ops.decode x)

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowTableSource
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Indexed cache tables and the represented interpolation row

The physical producer reads natural-number indexed lists. This adapter
identifies those reads with the finite-indexed row specification, including
the mismatch filter and the cardinality guard. Its premises concern only
individual input cache entries, the delta word, and the limit's length.
-/

namespace SubexponentialSAT.Subexp.UniversalRowTableSource

open SubexpSymbolicCost SubexpRepresentedRows SubexpRowInterpolation
open UniversalRowSource
open UniversalRowProgram (Row rowExpression)

variable {C E A B : Type*} {Q : ℕ}

theorem positions_mismatch {V G : Type*} [DecidableEq G]
    (head : V → Fin Q → G) (σ : Fin Q → G) (y : V) :
    positions (mismatchPositions head σ y) =
      ((List.finRange Q).filter (fun i => decide (head y i ≠ σ i))).map Fin.val := by
  simp [positions, UniversalRowSource.selected]

end SubexponentialSAT.Subexp.UniversalRowTableSource

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceValuesProgramPorts
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed port maps and the persistent ring-cache frame for source-table
callbacks. These lemmas are independent of the integer numerator evaluator. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open IntegerRingLiftProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem numeratorPorts_injective : Function.Injective numeratorPorts := by
  intro i j h
  have hv := congrArg Fin.val h
  apply Fin.ext
  dsimp only [numeratorPorts] at hv
  split_ifs at hv <;> simp_all <;> omega

/-- Ring service invariants depend only on their own high registers. -/
theorem cachedReady_frame (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (zero one minusOne : ModelCode t d) (base s : Store)
    (h : CachedReady t a M cache zero one minusOne base)
    (hf : ∀ i : Fin 256, 120 ≤ i.val → i ≠ 253 → i ≠ 254 → s i = base i) :
    CachedReady t a M cache zero one minusOne s := by
  have he (i : Fin 256) (hi : 120 ≤ i.val) (h253 : i ≠ 253) (h254 : i ≠ 254) :=
    hf i hi h253 h254
  have h120 := he 120 (by decide) (by decide) (by decide)
  have h194 := he 194 (by decide) (by decide) (by decide)
  have h201 := he 201 (by decide) (by decide) (by decide)
  have h202 := he 202 (by decide) (by decide) (by decide)
  have h203 := he 203 (by decide) (by decide) (by decide)
  have h204 := he 204 (by decide) (by decide) (by decide)
  have hn : HornerProgram.Services.NativeReady 3 t M cache (modelTable t a M cache) s := by
    refine ⟨⟨h120.trans h.native.workspace.1,?_⟩,h194.trans h.native.modulus,
      ?_,h203.trans h.native.zero,h201.trans h.native.table,?_⟩
    · intro i
      have hp := hf (ReconstructionProgram.RingAdapter.ports i)
        (by fin_cases i <;> decide) (by fin_cases i <;> decide) (by fin_cases i <;> decide)
      rw [hp]
      simpa only [ReconstructionProgram.RingAdapter.finalNative,h194,h201,h202,h203]
        using h.native.workspace.2 i
    · simpa only [h202] using h.native.width
    · simpa only [h204] using h.native.degree
  refine ⟨hn,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rcases h.clean with ⟨h1,h2,h3,h4,h5⟩
    exact ⟨h120.trans h1,(he 240 (by decide) (by decide) (by decide)).trans h2,
      (he 241 (by decide) (by decide) (by decide)).trans h3,
      (he 244 (by decide) (by decide) (by decide)).trans h4,
      (he 245 (by decide) (by decide) (by decide)).trans h5⟩
  · exact (he 249 (by decide) (by decide) (by decide)).trans h.zero
  · exact (he 250 (by decide) (by decide) (by decide)).trans h.one
  · exact (he 251 (by decide) (by decide) (by decide)).trans h.minusOne
  · exact (he 246 (by decide) (by decide) (by decide)).trans h.bits
  · exact (he 247 (by decide) (by decide) (by decide)).trans h.accumulator
  · exact (he 248 (by decide) (by decide) (by decide)).trans h.place
  · exact (he 255 (by decide) (by decide) (by decide)).trans h.output

end SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceBankFrameCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Measured staging and exact caller-store frames for the fixed source bank. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem stageTypes_stacks (a : Data) (h23 : a.stacks 23=[]) (h24 : a.stacks 24=[]) :
    (Staging.result 0 1 stageTypesOps a).stacks=
      Function.update (Function.update a.stacks 23 (a.stacks 289)) 24 (a.stacks 292) := by
  simp [stageTypesOps,Staging.result,Staging.actionResult,StackRoutines.copyStacks,h23,h24]

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceBankFrameCalls
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem vectorPorts_inj : Function.Injective vectorPorts := Fin.castAdd_injective _ _

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceBankFrameNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Bind the actual integer-to-ring vector producer to the actual source-row
program. The coefficient table is obtained from its execution, not supplied
as an expanded table premise. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open IntegerRingLiftProgram
open RowSelectionProgram (WordPair pairValue pairLength)

theorem nativePositions_eq {r Q : ℕ} (u y : UniversalType r Q 1) :
    nativePositions u y=UniversalRowTableSource.positions
      (SubexpRowInterpolation.mismatchPositions (fun v => v.head) (u.slot 0) y) := by
  symm
  exact UniversalRowTableSource.positions_mismatch (fun v => v.head) (u.slot 0) y

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceBankFrameReady
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete pre-state invariants for source dispatch. Metadata lookup and
whole-store comparisons preserve these low-bank arithmetic inputs. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open IntegerRingLiftProgram

theorem stageTypes_lowStore (a : Data) (h23 : a.stacks 23=[]) (h24 : a.stacks 24=[])
    (j : Fin 256) (hj23 : j≠23) (hj24 : j≠24) :
    lowStore (Staging.result 0 1 stageTypesOps a) j=lowStore a j := by
  have hn23 : vectorPorts j≠23 := by
    intro h; apply hj23; apply vectorPorts_inj; exact h
  have hn24 : vectorPorts j≠24 := by
    intro h; apply hj24; apply vectorPorts_inj; exact h
  simp [lowStore,projectState,stageTypes_stacks a h23 h24,hn23,hn24]

theorem inputFields_stage {r Q : ℕ} (a : Data) (c : Numerator.Saved) (start : Fin Q)
    (u y : UniversalType r Q 1) (h : InputFields a c start u y)
    (h23 : a.stacks 23=[]) (h24 : a.stacks 24=[])
    (hu : a.stacks 289=CollisionProgram.encodeType u)
    (hy : a.stacks 292=CollisionProgram.encodeType y) :
    ∀ i : Fin 64,
      lowStore (Staging.result 0 1 stageTypesOps a) (LayoutSourceValuesProgram.Native.numeratorPorts i)=
        (Numerator.state c (fun _=>false) start u y [] [] ([],[])).stacks i := by
  intro i
  by_cases hi23 : i=23
  · subst i
    simp [lowStore,projectState,stageTypes_stacks a h23 h24,vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,MatrixEntryProgram.input,hu]
  by_cases hi24 : i=24
  · subst i
    simp [lowStore,projectState,stageTypes_stacks a h23 h24,vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,MatrixEntryProgram.input,hy]
  have hn23 : LayoutSourceValuesProgram.Native.numeratorPorts i≠23 := by
    intro hh; apply hi23
    apply LayoutSourceValuesProgram.Native.numeratorPorts_injective
    exact hh
  have hn24 : LayoutSourceValuesProgram.Native.numeratorPorts i≠24 := by
    intro hh; apply hi24
    apply LayoutSourceValuesProgram.Native.numeratorPorts_injective
    exact hh
  rw [stageTypes_lowStore a h23 h24 _ hn23 hn24]
  exact h i hi23 hi24

theorem cachedReady_stage (t : ℕ) {d : ℕ} (model : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (zero one minusOne : ModelCode t d) (a : Data)
    (h : CachedReady t model M cache zero one minusOne (lowStore a))
    (h23 : a.stacks 23=[]) (h24 : a.stacks 24=[]) :
    CachedReady t model M cache zero one minusOne (lowStore (Staging.result 0 1 stageTypesOps a)) := by
  apply LayoutSourceValuesProgram.Native.cachedReady_frame t model M cache zero one minusOne
    (lowStore a) _ h
  intro i hi _ _
  apply stageTypes_lowStore a h23 h24
  · intro he; subst i; norm_num at hi
  · intro he; subst i; norm_num at hi

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceBankState
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Cache and workspace invariants for the actual metadata dispatch. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem WorkReady.emitter {a : Data} (h : WorkReady a) : EmitterClean a := by
  intro j hj hk hn
  by_cases h287 : j=287
  · subst j; exact h.output
  have hm : j∈cleanupPorts := by
    have hr : j∈List.ofFn (fun i : Fin 31 => (⟨256+i.val,by omega⟩ : Fin 320)) := by
      apply List.mem_ofFn.mpr
      refine ⟨⟨j.val-256,by omega⟩,?_⟩
      apply Fin.ext; simp; omega
    simp only [cleanupPorts,List.mem_append]
    exact Or.inl (Or.inl (Or.inr hr))
  exact h.work j hm (Or.inl (by omega))

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceCache
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The native interpolation-cache values implement the exact node units used
by the universal source semantics. No field inverse is assumed in O. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceCache

open SubexponentialSAT.SubexpRepresentedRows SubexponentialSAT.SubexpRowInterpolation
open InterpolationCacheProgram

variable {d Q : ℕ}

theorem native_node (t : ℕ) (ht : 0 < t) (hd : 0 < d) (a : RingModel.Data d)
    (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (minusOne : Coeff t d) (hQ : Q < 3^d) (i : Fin Q) :
    (RingProgram.modelRing t ht hd a M cache).decode ((native t a M cache minusOne).node i)=
      a.node t Q ht hQ i :=
  RingNodeProgram.nodeCode_decode t ht hd a M cache Q hQ i

theorem native_negative (t : ℕ) (ht : 0 < t) (hd : 0 < d) (a : RingModel.Data d)
    (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (minusOne : Coeff t d) (hm : (RingProgram.modelRing t ht hd a M cache).decode minusOne = -1)
    (i : Fin Q) :
    (RingProgram.modelRing t ht hd a M cache).decode
      (negativeValue t a M cache minusOne ((native t a M cache minusOne).node i))=
    (RingProgram.modelRing t ht hd a M cache).decode
      (((RingProgram.modelRing t ht hd a M cache).negRun ((native t a M cache minusOne).node i)).1) := by
  rw [(RingProgram.modelRing t ht hd a M cache).neg_correct]
  exact negativeValue_decode t ht hd a M cache minusOne _ hm

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceCache

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceBankUniversal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The universal branch has a concrete trace and a typed polynomial witness.
The only table used below is returned by the actual native vector program. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open IntegerRingLiftProgram RowSelectionProgram

variable {r Q d : ℕ}

theorem universal_generated_oai (p : Parameters r Q d) (a : Data) (ha : Ready p a)
    (u y : UniversalType r Q 1)
    (hu : a.stacks 289=CollisionProgram.encodeType u)
    (hy : a.stacks 292=CollisionProgram.encodeType y)
    (S : ℕ) (hS : ∀ j,(a.stacks j).length ≤ S)
    (hQ : Q ≤ S) (hR : p.R ≤ S)
    (hW : p.ringWidth.length ≤ S) (hRW : p.rowWidth.length ≤ S) :
    ∃ codes : Fin Q → ModelCode p.t d, ∃ n ≤ nativeBudget p S a codes u y,
      ∃ b : Data, ∃ bytes : List Bool,
        Eval (.seq universal cleanup) n a b ∧
        b.stacks=Function.update (clearedStacks a) 287 bytes ∧
        SourceWitness.Generated p.ops p.R (UniversalRowSourceBound.sourceLengthBound S)
          (p.rows u y) bytes := by
  have h23 : a.stacks 23=[] := ha.work.work 23 (by decide) (Or.inl (by decide))
  have h24 : a.stacks 24=[] := ha.work.work 24 (by decide) (Or.inl (by decide))
  have h67 : a.stacks 67=[] := ha.work.work 67 (by decide) (Or.inl (by decide))
  have h71 : a.stacks 71=[] := ha.work.work 71 (by decide) (Or.inl (by decide))
  have h274 : a.stacks 274=[] := ha.work.work 274 (by decide) (Or.inl (by decide))
  have hready := cachedReady_stage p.t p.model p.modulus p.cache _ _ _ a ha.ring h23 h24
  have hinv : (projectState id vectorPorts (Staging.result 0 1 stageTypesOps a)).stacks 252=
      RingProgram.flat p.invDenom := by
    change lowStore (Staging.result 0 1 stageTypesOps a) 252=_
    rw [stageTypes_lowStore a h23 h24 252 (by decide) (by decide)]
    exact ha.inverseDenominator
  obtain ⟨codes,hcodes,n,hn,b,he,hbs⟩ := native_universal_cleanup_eval
    p.hwords p.width p.power p.aWord p.R p.start u y p.hlen p.hwidths p.hvalues
    p.hp p.hpt p.hwidth p.hAQ p.hQ p.t p.ht p.hd p.model p.modulus p.cache p.hz
    p.ops.zeroRun.1 p.ops.oneRun.1 p.minusOne p.invDenom
    p.ops.zero_correct p.ops.one_correct p.hminus p.integerWord p.hinteger a
    ha.work.temp h23 h24 hready hinv
    (inputFields_stage a p.saved p.start u y (ha.input u y) h23 h24 hu hy)
    ha.nodes ha.work.count ha.work.tableCount ha.work.tableAccum h67 h71
    ha.work.emitter h274 (ha.work.low 0 (by decide)) (ha.work.low 1 (by decide))
    (ha.work.low 2 (by decide)) (ha.work.low 3 (by decide))
    p.inverse p.negative p.difference p.ringWidth p.rowWidth p.hringWidth p.hrowWidth
    ha.inverses ha.negatives ha.differences ha.ringWidth ha.rowWidth S hS
  let delta : ModelCode p.t d := if u=y then p.ops.oneRun.1 else p.ops.zeroRun.1
  let bytes := UniversalRowProgram.rowCode (RingProgram.flat p.ops.zeroRun.1)
    (RingProgram.flat p.ops.oneRun.1) (RingProgram.flat p.ops.zeroRun.1++RingProgram.flat p.ops.oneRun.1)
    (UniversalRowDataProgram.row (SourceTyped.tables RingProgram.flat codes p.inverse p.negative p.difference)
      (UniversalRowTableSource.positions (SubexpRowInterpolation.mismatchPositions (fun v=>v.head) (u.slot 0) y))
      (RingProgram.flat delta) (a.stacks 47))
  have hb : b.stacks=Function.update (clearedStacks a) 287 bytes := by
    by_cases heq : u=y <;>
      simpa [bytes,delta,ha.zero,ha.one,hu,hy,nativePositions_eq,heq] using hbs
  have hbase : 0 < SubexpLiftRing.baseWidth 3 p.t := by
    rw [RingProgram.ternary_baseWidth]
    have := p.ht
    omega
  have hg := SourceWitness.universal p.ops hbase p.nodeCache p.integerWord p.hinteger
    p.denom p.invDenom p.hinv (p.model.nodeUnits p.t Q p.ht p.hfield)
    (SourceCache.native_node p.t p.ht p.hd p.model p.modulus p.cache p.minusOne p.hfield)
    (SourceCache.native_inverse p.t p.ht p.hd p.model p.modulus p.cache p.minusOne p.hminus p.hfield)
    (SourceCache.native_difference p.t p.ht p.hd p.model p.modulus p.cache p.minusOne p.hminus p.hfield)
    codes p.inverse p.negative p.difference p.aWord.length p.R u y delta (a.stacks 47)
    hcodes (fun _=>rfl)
    (SourceCache.native_negative p.t p.ht p.hd p.model p.modulus p.cache p.minusOne p.hminus)
    (fun _ _=>rfl) (by rfl) ha.limit p.ringWidth p.rowWidth p.hringWidth p.hrowWidth
    S hQ hW hRW hR
  exact ⟨codes,n,hn,b,bytes,he,hb,hg⟩

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.universal_generated_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.universal_generated_oai
