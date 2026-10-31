-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceReady.Input.native
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:03:54.27278+00:00
-- url     : https://prove2.me/submissions/94d63e57-6adb-49c5-b549-263237c1a3ba

import Mathlib
import Definitions.Def_OAIQ081S182
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafProgram_SourceReady_Input_bank_ready
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafProgram_SourceReady_Input_base_bound

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

theorem lowClear_iff (i : Fin 768) :
    i∈lowClearPorts ↔ ∃j : Fin 205, j∉retainedLow ∧ lowPort j=i := by
  simp [lowClearPorts,List.mem_map,List.mem_filter]

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

theorem mem_extraPorts (i : Fin 768) : i ∈ extraPorts ↔
    (589 ≤ i.val ∧ i.val < 593) ∨ (596 ≤ i.val ∧ i.val < 680) := by
  have hr : i ∈ (List.finRange 84).map
      (fun j => (⟨596+j.val,by omega⟩ : Fin 768)) ↔ 596 ≤ i.val ∧ i.val < 680 := by
    simp only [List.mem_map,List.mem_finRange,true_and]
    constructor
    · rintro ⟨j,hj⟩
      have hv := congrArg Fin.val hj
      change 596+j.val=i.val at hv
      omega
    · intro hi
      refine ⟨⟨i.val-596,by omega⟩,?_⟩
      apply Fin.ext
      change 596+(i.val-596)=i.val
      omega
  have hc : i ∈ ([589,590,591,592] : List (Fin 768)) ↔ 589 ≤ i.val ∧ i.val < 593 := by
    simp only [List.mem_cons,List.mem_nil_iff,or_false]
    constructor
    · intro h
      rcases h with rfl|rfl|rfl|rfl <;> decide
    · intro h
      have hv : i.val=589 ∨ i.val=590 ∨ i.val=591 ∨ i.val=592 := by omega
      rcases hv with h|h|h|h
      · left; exact Fin.ext h
      · right; left; exact Fin.ext h
      · right; right; left; exact Fin.ext h
      · right; right; right; exact Fin.ext h
  simp only [extraPorts,List.mem_append,hc,hr]

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
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

theorem ArithmeticInput.pairReady (h : ArithmeticInput t a M cache s) :
    PairSpec.BaseReady 3 t M cache (HornerProgram.modelTable t a M cache) s (s 10) (fun _=>[]) := by
  constructor
  · intro j h8 h9
    fin_cases j <;>
      simp_all [RingCall.ports,RingCall.port,RingScan.serviceState,RingScan.serviceWorkState,
        RingScan.serviceTapes,h.modulus,h.lowWidth,h.zero,h.table]
    all_goals exact h.clean _ (by decide) (by decide)
  · intro i
    fin_cases i <;>
      simp [SubexpConvolutionPair.lowPort,SubexpJetCellProgram.scalarPorts,
        DensePolynomialLoop.ready,DensePolynomialLoop.state,DensePolynomialLoop.stackArray,Fin.addCases,
        h.lowModulus,h.modulus,h.lowWidth]
    all_goals first
      | exact h.lowModulus.trans h.modulus
      | exact h.lowWidth
      | (apply h.clean <;> decide)

  · simp [h.fullZero]
  · simpa only [h.lowWidth] using h.width
  · exact h.degree
  · exact h.clean 120 (by decide) (by decide)
  · intro j hlo hhi
    apply h.clean j (by omega)
    intro hj
    simp only [arithmeticCachePorts,List.mem_cons,List.mem_nil_iff,or_false] at hj
    rcases hj with hj|hj|hj|hj|hj|hj|hj|hj|hj|hj <;> subst j <;> omega

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

theorem arithmetic_ready {t d : ℕ} (model : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (a : Data) (h : PerturbationAssembly.ArithmeticInput t model M cache (rawLow a)) :
    PairSpec.BaseReady 3 t M cache (HornerProgram.modelTable t model M cache)
      (localStore a ∘ executorPorts) (rawLow a 10) (fun _ => []) := by
  have H := h.pairReady
  constructor
  · intro i hi hj
    rw [Function.comp_apply,arithmetic_frame a _
      ((by decide : ∀ j : Fin 32,arithmeticPort (RingCall.ports j)) i)]
    exact H.high i hi hj
  · intro i
    rw [Function.comp_apply,arithmetic_frame a _
      ((by decide : ∀ j : Fin 20,arithmeticPort
        (SubexpConvolutionPair.lowPort (SubexpJetCellProgram.scalarPorts j))) i)]
    exact H.low i
  · rw [Function.comp_apply,arithmetic_frame a 104 (by decide)]; exact H.width
  · exact H.scalarWidthLength
  · rw [Function.comp_apply,arithmetic_frame a 204 (by decide)]; exact H.degreeLength
  · rw [Function.comp_apply,arithmetic_frame a 120 (by decide)]; exact H.scratch
  · intro i hlo hhi
    rw [Function.comp_apply,arithmetic_frame a i (by
      unfold arithmeticPort; constructor
      · exact Or.inr (Or.inr ⟨hlo,by omega⟩)
      · constructor <;> intro he <;> subst i <;> norm_num at hhi)]
    exact H.work i hlo hhi

theorem initialized_ready {t d : ℕ} (model : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (a : Data) (D : ℕ)
    (h : PerturbationAssembly.ArithmeticInput t model M cache (rawLow a))
    (hD : a.stacks (localPort 210)=List.replicate D true)
    (h245 : a.stacks (localPort 245)=[]) :
    LayoutSourceRowsProgramInitialize.Ready (localStore a ∘ initializationPorts)
      D (d*baseWidth 3 t) := by
  have hc (i : Fin 256) (hi : i ∈ ([100,101,102,107,108,120] : List (Fin 256))) :
      localStore a (initializationPorts i)=[] := by
    rw [local_frame a _ (by
      intro hm
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;>
        (norm_num [initializationPorts, changedLocal] at hm <;> first | omega | (revert hm; decide)))]
    apply h.clean
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num
    · intro hm
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;>
        (norm_num [PerturbationAssembly.arithmeticCachePorts] at hm <;> first | omega | (revert hm; decide))
  refine ⟨?_,?_,hc 100 (by decide),hc 101 (by decide),hc 102 (by decide),
    hc 107 (by decide),hc 108 (by decide),hc 120 (by decide),?_,?_,?_,?_,?_⟩
  · exact (local_frame a 210 (by decide)).trans hD
  · exact (local_frame a 104 (by decide)).trans h.fullZero
  · exact local_cache a 192 (by decide)
  · exact local_cache a 193 (by decide)
  · exact local_cache a 242 (by decide)
  · exact local_cache a 243 (by decide)
  · exact (local_frame a 245 (by decide)).trans h245

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

theorem base_frame (a : Data) (D W : ℕ) (ps : List (ℕ × ℕ)) (v N f : ℕ)
    (i : Fin 340) (hi : i ∉ ([192,193,242,243,304] : List (Fin 340))) :
    sourceBase a D W ps v N f i=localStore a i := by
  simp only [List.mem_cons,List.mem_nil_iff,or_false,not_or] at hi
  simp [sourceBase,preparedSourceStore,initializeFinish,hi.1,hi.2.1,hi.2.2.1,hi.2.2.2.1,hi.2.2.2.2]

end SubexponentialSAT.SqrtLog.LeafProgram.SourceReady

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramSourceReady
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical master words and ordinary scratch cleanliness imply every native
source precondition. The numerator uses the cleared 5/10 view; the executor
keeps the original arithmetic words. No source execution is a hypothesis. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.SourceReady
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl DensePolynomialProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.Subexp SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open LayoutSourceRowsProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

variable {r Q d : ℕ} {p : SourceBank.Parameters r Q d}
  {ps : List (ℕ × ℕ)} {P : PackingData (Fin ps.length) (UniversalType r Q 1)}
  {a : Data} {v N f S : ℕ}

theorem Input.low_empty (h : Input p ps P a v N f S) :
    ∀ i ∈ SourceStaging.lowClearPorts,a.stacks i=[] := by
  intro i hi
  obtain ⟨j,hj,hji⟩ := (SourceStaging.lowClear_iff i).mp hi
  rw [← hji]
  exact h.clean (Fin.castAdd 135 j) (by
    intro hp
    simp only [physicalLive, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|
      hp|hp|hp|hp|hp|hp|hp
    all_goals have hv := congrArg Fin.val hp
    all_goals simp at hv
    all_goals try omega
    all_goals apply hj
    all_goals simp [SourceStaging.retainedLow, Fin.ext_iff]
    all_goals omega)

theorem Input.extra_empty (h : Input p ps P a v N f S) :
    ∀ i ∈ SourceControls.extraPorts,a.stacks i=[] := by
  intro i hi
  have hb := (SourceControls.mem_extraPorts i).mp hi
  have hlo : 589 ≤ i.val := by omega
  have hhi : i.val < 680 := by omega
  let j : Fin 340 := ⟨i.val-340,by omega⟩
  have hj : 249 ≤ j.val := by dsimp [j]; omega
  have he : localPort j=i := by apply Fin.ext; dsimp [localPort,j]; omega
  rw [← he]
  apply h.clean
  intro hp
  simp [physicalLive] at hp
  omega

theorem Input.base_empty (h : Input p ps P a v N f S) (D W : ℕ) (i : Fin 340)
    (hb : localBlank i) (hi : i ∉ ([192,193,242,243,304] : List (Fin 340))) :
    sourceBase a D W ps v N f i=[] :=
  (base_frame a D W ps v N f i hi).trans (h.empty i hb)

theorem Input.native_oai (h : Input p ps P a v N f S) :
    Source.NativeInput p ps P a v N f S (rawLow a 10) (fun _ => []) := by
  have E := h.empty
  have BE := h.base_empty (p.R+1) (d*baseWidth 3 p.t)
  have IE (i : Fin 340) (hb : localBlank i)
      (hi : i ∉ ([192,193,242,243] : List (Fin 340))) :
      initializeFinish (localStore a) (p.R+1) (d*baseWidth 3 p.t) i=[] := by
    simp only [List.mem_cons,List.mem_nil_iff,or_false,not_or] at hi
    simpa only [initializeFinish,Function.update_of_ne hi.1,
      Function.update_of_ne hi.2.1,Function.update_of_ne hi.2.2.1,
      Function.update_of_ne hi.2.2.2] using E i hb
  refine {
    tmp := h.tmp
    low := h.low_empty
    extra := h.extra_empty
    backups := h.backups
    init := initialized_ready p.model p.modulus p.cache a (p.R+1) h.arithmetic
      h.dimension (h.clean 245 (by decide))
    literal := (local_frame a 233 (by decide)).trans h.literal
    ambient := (local_frame a 212 (by decide)).trans h.ambient
    factor := (local_frame a 216 (by decide)).trans h.factor
    plans := (h.copied 136 337 (by decide)).trans h.plans
    lookup := ?_
    rowsClean := ?_
    workClean := ?_
    owner := ?_
    arithmetic := arithmetic_ready p.model p.modulus p.cache a h.arithmetic
    empty := ?_
    source := h.bank_ready (p.R+1) (d*baseWidth 3 p.t)
    sourceClean := ?_
    metadata := (h.copied 135 306 (by decide)).trans h.metadata
    size := ?_
    metadataSize := h.metadataSize
    incidenceBound := h.incidenceBound
    nodesBound := ?_
    radiusBound := Nat.le_trans (Nat.le_succ _) h.countSize
    ringWidthBound := ?_
    rowWidthBound := ?_
  }
  · intro i hi
    have hb : localBlank i := by
      simp only [List.mem_cons,List.mem_nil_iff,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp [localBlank, physicalLive, changedLocal]
    have hn : i ∉ ([192,193,242,243] : List (Fin 340)) := by
      simp only [List.mem_cons,List.mem_nil_iff,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp
    exact IE i hb hn
  · intro i hi
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      apply BE <;> simp [localBlank, physicalLive, changedLocal]
  · intro i hi
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      apply BE <;> simp [localBlank, physicalLive, changedLocal]
  · intro i hi
    fin_cases i <;> norm_num at hi
    all_goals apply BE <;> simp [ownerStacks, localBlank, physicalLive, changedLocal]
  · exact ⟨E 99 (by decide),E 121 (by decide),E 122 (by decide),E 240 (by decide),
      E 241 (by decide),E 244 (by decide),E 245 (by decide),fun i => by
        fin_cases i <;> apply E <;>
          simp [bufferPorts, executorPorts, localBlank, physicalLive, changedLocal]⟩
  · intro i hi
    simp only [SourceBank.cleanupPorts, List.mem_append] at hi
    rcases hi with ((hi | hi) | hi) | hi
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        apply BE <;> simp [sourcePorts, localBlank, physicalLive, changedLocal]
    · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hi
      fin_cases k <;> apply BE <;>
        simp [sourcePorts, localBlank, physicalLive, changedLocal]
    · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hi
      fin_cases k <;> apply BE <;>
        simp [sourcePorts, localBlank, physicalLive, changedLocal]
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
      rcases hi with rfl|rfl|rfl <;>
        apply BE <;> simp [sourcePorts, localBlank, physicalLive, changedLocal]
  · intro i; exact h.base_bound (sourcePorts i)
  · simpa only [h.nodes,List.length_replicate] using h.size 131
  · simpa only [h.ringWidth] using h.size 717
  · simpa only [h.rowWidth] using h.size 716

end SubexponentialSAT.SqrtLog.LeafProgram.SourceReady

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceReady.Input.native_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceReady.Input.native_oai
