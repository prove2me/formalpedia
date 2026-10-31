-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceReady.Input.bank_ready
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:32:16.015646+00:00
-- url     : https://prove2.me/submissions/09a180d7-c3d4-4352-badf-a3c3821ab1b6

import Mathlib
import Definitions.Def_OAIQ081S170
import Definitions.Def_OAIQ081S174

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramSourceStaging
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Protect the target-jet caches while the source-polynomial initializer
uses the same private local ports. Source length and target jet order are
independent runtime values. These are actual copy and clear programs. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.SourceStaging

open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage

theorem saved_empty (a : Data) (i : Fin 768) (hi : i∈cachePorts) :
    (saved a).stacks i=[] := by
  simp [saved,clearMany_stacks,hi]

end SubexponentialSAT.SqrtLog.LeafProgram.SourceStaging

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramSourceControls
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid source-control copies into the isolated 340-stack worker. All inputs
come from runtime layout/ring masters; no source polynomial is supplied. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.SourceControls
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage

theorem delta_stacks (a : Data) :
    (deltaState a).stacks = Function.update a.stacks 365 (true :: a.stacks 365) := by
  rfl

end SubexponentialSAT.SqrtLog.LeafProgram.SourceControls

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramSourceReadyCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Byte-level value and frame rules for source preparation. These rules
concern the actual paid copy/clear state transformer, not assumed source
execution or a supplied readiness certificate. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.SourceReady
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage

theorem saved_frame (a : Data) (i : Fin 768)
    (hc : i ∉ SourceStaging.cachePorts) (hb : i ∉ SourceStaging.backupPorts) :
    (SourceStaging.saved a).stacks i = a.stacks i := by
  rw [SourceStaging.saved,clearMany_stacks,ite_eq_right hc]
  apply copyMany_frame
  intro p hp he
  have hm : p.2 ∈ SourceStaging.backupPorts := by
    simp only [SourceStaging.savePairs,List.mem_cons,List.mem_nil_iff,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl <;> decide
  exact hb (he.symm ▸ hm)

theorem prepared_frame (a : Data) (i : Fin 768)
    (h365 : i ≠ 365) (hp : ∀ p ∈ SourceControls.pairs,i ≠ p.2)
    (hc : i ∉ SourceStaging.cachePorts) (hb : i ∉ SourceStaging.backupPorts) :
    (prepared a).stacks i = a.stacks i := by
  unfold prepared SourceControls.prepared
  rw [SourceControls.delta_stacks,Function.update_of_ne h365,copyMany_frame _ _ _ hp]
  exact saved_frame a i hc hb

theorem prepared_copy (a : Data)
    (he : ∀ p ∈ SourceControls.pairs,a.stacks p.2=[])
    (p : Fin 768 × Fin 768) (hp : p ∈ SourceControls.pairs) :
    (prepared a).stacks p.2 = a.stacks p.1 := by
  have hs : ∀ q ∈ SourceControls.pairs,
      q.1 ∉ SourceStaging.cachePorts ∧ q.1 ∉ SourceStaging.backupPorts ∧
      q.2 ∉ SourceStaging.cachePorts ∧ q.2 ∉ SourceStaging.backupPorts ∧ q.2 ≠ 365 := by
    simp [SourceControls.pairs,SourceStaging.cachePorts,SourceStaging.backupPorts]
  have hz : ∀ q ∈ SourceControls.pairs,(SourceStaging.saved a).stacks q.2=[] := by
    intro q hq
    rw [saved_frame a q.2 (hs q hq).2.2.1 (hs q hq).2.2.2.1]
    exact he q hq
  unfold prepared SourceControls.prepared
  rw [SourceControls.delta_stacks,Function.update_of_ne (hs p hp).2.2.2.2]
  rw [copyMany_value SourceControls.pairs (SourceStaging.saved a)
    (by decide) hz (by simp [SourceControls.pairs]) p hp]
  exact saved_frame a p.1 (hs p hp).1 (hs p hp).2.1

theorem prepared_cache (a : Data) (i : Fin 768) (hi : i ∈ SourceStaging.cachePorts) :
    (prepared a).stacks i=[] := by
  have h365 : i ≠ 365 := by
    simp only [SourceStaging.cachePorts,List.mem_cons,List.mem_nil_iff,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl <;> decide
  have hp : ∀ p ∈ SourceControls.pairs,i ≠ p.2 := by
    simp only [SourceStaging.cachePorts,List.mem_cons,List.mem_nil_iff,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl <;> simp [SourceControls.pairs]
  unfold prepared SourceControls.prepared
  rw [SourceControls.delta_stacks,Function.update_of_ne h365,copyMany_frame _ _ _ hp]
  exact SourceStaging.saved_empty a i hi

theorem prepared_delta (a : Data) (he : a.stacks 365=[]) :
    (prepared a).stacks 365=[true] := by
  unfold prepared SourceControls.prepared
  rw [SourceControls.delta_stacks,Function.update_same,
    copyMany_frame SourceControls.pairs _ 365 (by simp [SourceControls.pairs]),
    saved_frame a 365 (by decide) (by decide),he]

private theorem localPort_ne_delta (i : Fin 340) (hi : i ∉ changedLocal) :
    localPort i ≠ 365 := by
  intro h
  have hv := congrArg Fin.val h
  simp [localPort] at hv
  simp [changedLocal] at hi
  omega

private theorem localPort_not_cache (i : Fin 340) (hi : i ∉ changedLocal) :
    localPort i ∉ SourceStaging.cachePorts := by
  intro h
  simp [SourceStaging.cachePorts] at h
  rcases h with h | h | h | h <;>
    have hv := congrArg Fin.val h <;>
    simp [localPort] at hv <;>
    simp [changedLocal] at hi <;>
    omega

private theorem localPort_not_backup (i : Fin 340) :
    localPort i ∉ SourceStaging.backupPorts := by
  intro h
  simp [SourceStaging.backupPorts] at h
  rcases h with h | h | h | h <;>
    have hv := congrArg Fin.val h <;>
    simp [localPort] at hv <;>
    omega

theorem local_frame (a : Data) (i : Fin 340) (hi : i ∉ changedLocal) :
    localStore a i = a.stacks (localPort i) := by
  apply prepared_frame
  · exact localPort_ne_delta i hi
  · intro p hp
    simp only [SourceControls.pairs,List.mem_cons,List.mem_nil_iff,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals
      intro h
      have hv := congrArg Fin.val h
      simp [localPort] at hv
      simp [changedLocal] at hi
      omega
  · exact localPort_not_cache i hi
  · exact localPort_not_backup i

theorem local_copy (a : Data)
    (he : ∀ p ∈ SourceControls.pairs,a.stacks p.2=[])
    (src : Fin 768) (dst : Fin 340) (hp : (src,localPort dst) ∈ SourceControls.pairs) :
    localStore a dst = a.stacks src := prepared_copy a he _ hp

theorem local_cache (a : Data) (i : Fin 340)
    (hi : i ∈ ([192,193,242,243] : List (Fin 340))) : localStore a i=[] := by
  apply prepared_cache
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl <;>
    simp [localPort, SourceStaging.cachePorts]

end SubexponentialSAT.SqrtLog.LeafProgram.SourceReady

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyInputReady
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Recover the native arithmetic invariants from the actual staged cache
words and an otherwise empty low workspace. No execution premise is used. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl DensePolynomialProgram
open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
attribute [local simp] Fin.coe_ofNat_eq_mod

variable {t d : ℕ} {a : RingModel.Data d}
  {M : SubexpPreparedQuartic.Modulus 3 t} {cache : RingProgram.ScalarCache 3 t} {s : Store}

theorem ArithmeticInput.scalarReady (h : ArithmeticInput t a M cache s) :
    HornerProgram.Services.NativeReady 3 t M cache (HornerProgram.modelTable t a M cache) s := by
  refine ⟨⟨h.clean 120 (by decide) (by decide),?_⟩,h.modulus,h.width,h.zero,h.table,h.degree⟩
  intro i
  fin_cases i <;>
    simp [ReconstructionProgram.RingAdapter.ports,ReconstructionProgram.RingAdapter.finalNative,
      ReconstructionProgram.RingAdapter.nativeStacks]
  all_goals exact h.clean _ (by decide) (by decide)

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramSourceReadyArithmetic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The arithmetic half of physical source readiness is preserved by source
control copies. The source-count initializer uses R+1, independently of J. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.SourceReady
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl DensePolynomialProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open LayoutSourceRowsProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem arithmetic_frame (a : Data) (i : Fin 256) (hi : arithmeticPort i) :
    localStore a (executorPorts i)=rawLow a i := by
  apply local_frame
  intro hm
  simp only [changedLocal, List.mem_cons, List.mem_nil_iff, or_false] at hm
  rcases hi with ⟨hi, h192, h193⟩
  rcases hm with hm|hm|hm|hm|hm|hm|hm|hm|hm|hm|hm|hm|hm|hm|hm|hm|hm|hm|
    hm|hm|hm|hm|hm|hm|hm|hm|hm
  all_goals
    have hv := congrArg Fin.val hm
    simp [executorPorts] at hv
    rcases hi with hi | hi | hi
    · omega
    · subst i
      norm_num at hv
    · omega

end SubexponentialSAT.SqrtLog.LeafProgram.SourceReady

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramSourceReadyInput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A physical caller contract. All hypotheses are bytes in retained masters,
blank work tapes, or explicit length bounds. In particular no native source
readiness or execution is assumed. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.SourceReady
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl DensePolynomialProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.Subexp SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open LayoutSourceRowsProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

variable {r Q d : ℕ} {p : SourceBank.Parameters r Q d}
  {ps : List (ℕ × ℕ)} {P : PackingData (Fin ps.length) (UniversalType r Q 1)}
  {a : Data} {v N f S : ℕ}

theorem Input.controls_empty (h : Input p ps P a v N f S) :
    ∀ q ∈ SourceControls.pairs,a.stacks q.2=[] := by
  intro q hq
  simp only [SourceControls.pairs,List.mem_cons,List.mem_nil_iff,or_false] at hq
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact h.clean 21 (by decide)
  · exact h.clean 22 (by decide)
  · exact h.clean 26 (by decide)
  · exact h.clean 42 (by decide)
  · exact h.clean 43 (by decide)
  · exact h.clean 44 (by decide)
  · exact h.clean 45 (by decide)
  · exact h.clean 47 (by decide)
  · exact h.clean 48 (by decide)
  · exact h.clean 306 (by decide)
  · exact h.clean 308 (by decide)
  · exact h.clean 309 (by decide)
  · exact h.clean 310 (by decide)
  · exact h.clean 311 (by decide)
  · exact h.clean 312 (by decide)
  · exact h.clean 313 (by decide)
  · exact h.clean 314 (by decide)
  · exact h.clean 337 (by decide)
  · exact h.clean 249 (by decide)
  · exact h.clean 250 (by decide)
  · exact h.clean 251 (by decide)
  · exact h.clean 252 (by decide)

theorem Input.empty (h : Input p ps P a v N f S) (i : Fin 340) (hi : localBlank i) :
    localStore a i=[] := by
  rcases hi with hi|hi
  · exact (local_frame a i hi.2).trans (h.clean i hi.1)
  · exact local_cache a i hi

theorem Input.copied (h : Input p ps P a v N f S) (src : Fin 768) (dst : Fin 340)
    (hp : (src,localPort dst) ∈ SourceControls.pairs) :
    localStore a dst=a.stacks src := local_copy a h.controls_empty src dst hp

theorem Input.delta (h : Input p ps P a v N f S) : localStore a 25=[true] :=
  prepared_delta a (h.clean 25 (by decide))

theorem base_frame (a : Data) (D W : ℕ) (ps : List (ℕ × ℕ)) (v N f : ℕ)
    (i : Fin 340) (hi : i ∉ ([192,193,242,243,304] : List (Fin 340))) :
    sourceBase a D W ps v N f i=localStore a i := by
  simp only [List.mem_cons,List.mem_nil_iff,or_false,not_or] at hi
  simp [sourceBase,preparedSourceStore,initializeFinish,hi.1,hi.2.1,hi.2.2.1,hi.2.2.2.1,hi.2.2.2.2]

theorem bank_frame (a : Data) (D W : ℕ) (ps : List (ℕ × ℕ)) (v N f : ℕ)
    (i : Fin 320) (hi : i ∉ ([5,10,192,193,242,243,304] : List (Fin 320))) :
    (bank a D W ps v N f).stacks i=localStore a (sourcePorts i) := by
  have hh : sourcePorts i ∉ ([192,193,242,243,304] : List (Fin 340)) := by
    simpa [sourcePorts,Fin.ext_iff] using (by
      simp only [List.mem_cons,List.mem_nil_iff,or_false,not_or] at hi ⊢
      exact hi.2.2 : i ∉ ([192,193,242,243,304] : List (Fin 320)))
  have h5 : sourcePorts i≠5 := by
    intro he; have hh : i=5 := Fin.ext (congrArg (fun j : Fin 340 => j.val) he)
    exact hi (by simp [hh])
  have h10 : sourcePorts i≠10 := by
    intro he; have hh : i=10 := Fin.ext (congrArg (fun j : Fin 340 => j.val) he)
    exact hi (by simp [hh])
  simp only [bank,Function.comp_apply,clearedSourceStore,Function.update_of_ne h5,
    Function.update_of_ne h10]
  exact base_frame a D W ps v N f _ hh

theorem Input.bank_empty (h : Input p ps P a v N f S) (D W : ℕ) (i : Fin 320)
    (hi : bankBlank i) : (bank a D W ps v N f).stacks i=[] := by
  rcases hi with rfl|rfl|hi
  · simp [bank,clearedSourceStore,sourcePorts]
  · simp [bank,clearedSourceStore,sourcePorts]
  · by_cases h5 : i=5
    · subst i; simp [bank,clearedSourceStore,sourcePorts]
    by_cases h10 : i=10
    · subst i; simp [bank,clearedSourceStore,sourcePorts]
    rw [bank_frame a D W ps v N f i (by simpa [h5,h10] using hi.2)]
    exact h.empty _ hi.1

end SubexponentialSAT.SqrtLog.LeafProgram.SourceReady

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramSourceReadyBank
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Derivation of the source-bank invariant from its paid master copies.
The source numerator sees empty 5/10 only inside the checked staging wrapper. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.SourceReady
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl DensePolynomialProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.Subexp SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open LayoutSourceRowsProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

variable {r Q d : ℕ} {p : SourceBank.Parameters r Q d}
  {ps : List (ℕ × ℕ)} {P : PackingData (Fin ps.length) (UniversalType r Q 1)}
  {a : Data} {v N f S : ℕ}

theorem Input.bank_fields (h : Input p ps P a v N f S) (D W : ℕ) :
    BankFields p (bank a D W ps v N f).stacks := by
  have cp (src : Fin 768) (dst : Fin 320)
      (hp : (src,localPort (sourcePorts dst)) ∈ SourceControls.pairs)
      (hi : dst ∉ ([5,10,192,193,242,243,304] : List (Fin 320))) :
      (bank a D W ps v N f).stacks dst=a.stacks src :=
    (bank_frame a D W ps v N f dst hi).trans (h.copied src _ hp)
  exact ⟨(cp 130 21 (by decide) (by decide)).trans h.colors,
    (cp 131 22 (by decide) (by decide)).trans h.nodes,
    (bank_frame a D W ps v N f 25 (by decide)).trans h.delta,
    (cp 132 26 (by decide) (by decide)).trans h.typeWidth,
    (cp 710 42 (by decide) (by decide)).trans h.positive,
    (cp 711 43 (by decide) (by decide)).trans h.negative,
    (cp 140 44 (by decide) (by decide)).trans h.scalarWidth,
    (cp 712 45 (by decide) (by decide)).trans h.power,
    (cp 138 47 (by decide) (by decide)).trans h.radius,
    (cp 139 48 (by decide) (by decide)).trans h.offset,
    (cp 280 249 (by decide) (by decide)).trans h.zero,
    (cp 207 250 (by decide) (by decide)).trans h.one,
    (cp 211 251 (by decide) (by decide)).trans h.minusOne,
    (cp 728 252 (by decide) (by decide)).trans h.inverseDenominator,
    (cp 713 308 (by decide) (by decide)).trans h.inverses,
    (cp 714 309 (by decide) (by decide)).trans h.negatives,
    (cp 715 310 (by decide) (by decide)).trans h.differences,
    (cp 717 311 (by decide) (by decide)).trans h.ringWidth,
    (cp 716 312 (by decide) (by decide)).trans h.rowWidth,
    (cp 280 313 (by decide) (by decide)).trans h.zero,
    (cp 207 314 (by decide) (by decide)).trans h.one⟩

theorem Input.bank_input (h : Input p ps P a v N f S) (D W : ℕ)
    (u y : UniversalType r Q 1) :
    SourceBank.InputFields (bank a D W ps v N f) p.saved p.start u y := by
  have F := h.bank_fields D W
  have E := h.bank_empty D W
  intro i hi hj
  fin_cases i
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 0 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 1 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 2 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 3 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 4 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 5 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 6 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 7 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 8 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 9 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 10 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 11 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 12 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 13 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 14 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 15 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 16 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 17 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 18 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 19 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 20 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using F.colors
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using F.nodes
  · exact False.elim (hi rfl)
  · exact False.elim (hj rfl)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using F.index
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using F.typeWidth
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 27 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 28 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 29 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 30 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 31 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 32 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 33 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 34 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 35 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 36 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 37 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 38 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 39 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 40 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 41 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using F.positive
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using F.negative
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using F.scalarWidth
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using F.power
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 46 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using F.radius
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using F.offset
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 49 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 253 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 254 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 52 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 53 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 54 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 55 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 56 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 57 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 58 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 59 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 60 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 61 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 62 (by decide)
  · simpa +decide [SourceBank.lowStore,projectState,SourceBank.vectorPorts,
      LayoutSourceValuesProgram.Native.numeratorPorts,Numerator.state,Numerator.baseStacks,
      Guard.guardInput,Scan.scanInput,SubexponentialSAT.Subexp.MatrixEntryProgram.input,
      SourceBank.Parameters.start,SourceBank.Parameters.saved,
      LayoutProgramScalar.FromCounts.unsignedSaved,h.powerNegative] using E 63 (by decide)

theorem Input.bank_work (h : Input p ps P a v N f S) (D W : ℕ) :
    SourceBank.WorkReady (bank a D W ps v N f) := by
  have E := h.bank_empty D W
  refine ⟨?_,E 319 (by decide),E 287 (by decide),E 37 (by decide),
    E 64 (by decide),E 65 (by decide),?_⟩
  · intro j hj _
    apply E
    simp only [SourceBank.cleanupPorts, List.mem_append] at hj
    rcases hj with ((hj | hj) | hj) | hj
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hj
      rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp [bankBlank, localBlank, physicalLive, changedLocal,
          LayoutSourceRowsProgram.sourcePorts]
    · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hj
      fin_cases k <;> simp [bankBlank, localBlank, physicalLive, changedLocal,
        LayoutSourceRowsProgram.sourcePorts]
    · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hj
      fin_cases k <;> simp [bankBlank, localBlank, physicalLive, changedLocal,
        LayoutSourceRowsProgram.sourcePorts]
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hj
      rcases hj with rfl|rfl|rfl <;>
        simp [bankBlank, localBlank, physicalLive, changedLocal,
          LayoutSourceRowsProgram.sourcePorts]
  · intro j hj
    apply E
    have hv : j.val=0 ∨ j.val=1 ∨ j.val=2 ∨ j.val=3 := by omega
    rcases hv with hv|hv|hv|hv
    · have he : j=(0 : Fin 320) := Fin.ext hv
      subst j
      simp [bankBlank, localBlank, physicalLive, changedLocal,
        LayoutSourceRowsProgram.sourcePorts]
    · have he : j=(1 : Fin 320) := Fin.ext hv
      subst j
      simp [bankBlank, localBlank, physicalLive, changedLocal,
        LayoutSourceRowsProgram.sourcePorts]
    · have he : j=(2 : Fin 320) := Fin.ext hv
      subst j
      simp [bankBlank, localBlank, physicalLive, changedLocal,
        LayoutSourceRowsProgram.sourcePorts]
    · have he : j=(3 : Fin 320) := Fin.ext hv
      subst j
      simp [bankBlank, localBlank, physicalLive, changedLocal,
        LayoutSourceRowsProgram.sourcePorts]

theorem Input.bank_ring (h : Input p ps P a v N f S) (D W : ℕ) :
    IntegerRingLiftProgram.CachedReady p.t p.model p.modulus p.cache
      p.ops.zeroRun.1 p.ops.oneRun.1 p.minusOne (SourceBank.lowStore (bank a D W ps v N f)) := by
  let b := bank a D W ps v N f
  have F := h.bank_fields D W
  have E := h.bank_empty D W
  have H := h.arithmetic.scalarReady
  have hf (i : Fin 256) (hlo : 120 ≤ i.val) (hhi : i.val ≤ 204)
      (h192 : i≠192) (h193 : i≠193) :
      SourceBank.lowStore b i=rawLow a i := by
    have hx : SourceBank.vectorPorts i ∉ ([5,10,192,193,242,243,304] : List (Fin 320)) := by
      simp only [List.mem_cons,List.mem_nil_iff,or_false,not_or]
      repeat' constructor
      all_goals intro he; have hh := congrArg Fin.val he
      all_goals simp only [SourceBank.vectorPorts,Fin.val_castAdd] at hh
      all_goals omega
    change b.stacks (SourceBank.vectorPorts i)=_
    rw [bank_frame a D W ps v N f _ hx]
    exact arithmetic_frame a i ⟨Or.inr (Or.inr ⟨by omega,hhi⟩),h192,h193⟩
  have hn : HornerProgram.Services.NativeReady 3 p.t p.modulus p.cache
      (HornerProgram.modelTable p.t p.model p.modulus p.cache) (SourceBank.lowStore b) := by
    refine ⟨⟨?_,?_⟩,?_,?_,?_,?_,?_⟩
    · rw [hf 120 (by decide) (by decide) (by decide) (by decide)]; exact H.workspace.1
    · intro i
      have hv := hf (ReconstructionProgram.RingAdapter.ports i)
        (by fin_cases i <;> decide) (by fin_cases i <;> decide)
        (by fin_cases i <;> decide) (by fin_cases i <;> decide)
      rw [hv]
      simpa only [ReconstructionProgram.RingAdapter.finalNative,
        hf 194 (by decide) (by decide) (by decide) (by decide),
        hf 201 (by decide) (by decide) (by decide) (by decide),
        hf 202 (by decide) (by decide) (by decide) (by decide),
        hf 203 (by decide) (by decide) (by decide) (by decide)] using H.workspace.2 i
    · rw [hf 194 (by decide) (by decide) (by decide) (by decide)]; exact H.modulus
    · rw [hf 202 (by decide) (by decide) (by decide) (by decide)]; exact H.width
    · rw [hf 203 (by decide) (by decide) (by decide) (by decide)]; exact H.zero
    · rw [hf 201 (by decide) (by decide) (by decide) (by decide)]; exact H.table
    · rw [hf 204 (by decide) (by decide) (by decide) (by decide)]; exact H.degree
  exact ⟨hn,⟨E 120 (by decide),E 240 (by decide),E 241 (by decide),E 244 (by decide),
    E 245 (by decide)⟩,F.zeroCache,F.oneCache,F.minusCache,
    E 246 (by decide),E 247 (by decide),E 248 (by decide),E 255 (by decide)⟩

theorem Input.bank_ready_oai (h : Input p ps P a v N f S) (D W : ℕ) :
    SourceBank.Ready p (bank a D W ps v N f) := by
  have F := h.bank_fields D W
  exact ⟨h.bank_work D W,h.bank_input D W,h.bank_ring D W,F.inverseDenominator,
    by simp [F.nodes],by simp [F.radius],F.inverses,F.negatives,F.differences,
    F.ringWidth,F.rowWidth,F.zero,F.one⟩

end SubexponentialSAT.SqrtLog.LeafProgram.SourceReady

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceReady.Input.bank_ready_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceReady.Input.bank_ready_oai
