-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceReady.Input.base_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:57:43.693721+00:00
-- url     : https://prove2.me/submissions/b45d20a7-d708-417c-978b-ba1a289c77f1

import Mathlib
import Definitions.Def_OAIQ081S170

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

theorem prepared_delta (a : Data) (he : a.stacks 365=[]) :
    (prepared a).stacks 365=[true] := by
  unfold prepared SourceControls.prepared
  rw [SourceControls.delta_stacks,Function.update_same,
    copyMany_frame SourceControls.pairs _ 365 (by simp [SourceControls.pairs]),
    saved_frame a 365 (by decide) (by decide),he]

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

end SubexponentialSAT.SqrtLog.LeafProgram.SourceReady

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramSourceReadySize
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Word bounds for the actual source preparation and full source initializer.
The bound explicitly includes the full (R+1)-coefficient zero array. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.SourceReady
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.Subexp SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open LayoutSourceRowsProgram

variable {r Q d : ℕ} {p : SourceBank.Parameters r Q d}
  {ps : List (ℕ × ℕ)} {P : PackingData (Fin ps.length) (UniversalType r Q 1)}
  {a : Data} {v N f S : ℕ}

theorem Input.prepared_bound (h : Input p ps P a v N f S) : WordBound S (prepared a) := by
  have hsave : WordBound S (SourceStaging.saved a) := by
    apply clearMany_wordBound
    exact copyMany_wordBound SourceStaging.savePairs a S (by decide)
      (by intro q hq
          simp only [SourceStaging.savePairs,List.mem_cons,List.mem_nil_iff,or_false] at hq
          rcases hq with rfl|rfl|rfl|rfl <;> exact h.backups _ (by decide))
      (by simp [SourceStaging.savePairs]) h.size
  have hs : ∀ q ∈ SourceControls.pairs,
      q.2 ∉ SourceStaging.cachePorts ∧ q.2 ∉ SourceStaging.backupPorts := by
    simp [SourceControls.pairs,SourceStaging.cachePorts,SourceStaging.backupPorts]
  have hcopy : WordBound S (copyManyState SourceControls.pairs (SourceStaging.saved a)) :=
    copyMany_wordBound SourceControls.pairs (SourceStaging.saved a) S (by decide)
      (by intro q hq
          rw [saved_frame a q.2 (hs q hq).1 (hs q hq).2]
          exact h.controls_empty q hq)
      (by simp [SourceControls.pairs]) hsave
  intro i
  by_cases hi : i=365
  · subst i
    rw [prepared_delta a (h.clean 25 (by decide))]
    simp only [List.length_cons,List.length_nil]
    have := h.countSize
    omega
  · simpa only [prepared,SourceControls.prepared,SourceControls.delta_stacks,
      Function.update_of_ne hi] using hcopy i

theorem Input.local_bound (h : Input p ps P a v N f S) (i : Fin 340) :
    (localStore a i).length ≤ S := h.prepared_bound (localPort i)

theorem Input.base_bound_oai (h : Input p ps P a v N f S) (i : Fin 340) :
    (sourceBase a (p.R+1) (d*baseWidth 3 p.t) ps v N f i).length ≤ S := by
  have upd (s : Fin 340 → List Bool) (hs : ∀ j,(s j).length ≤ S)
      (j : Fin 340) (b : List Bool) (hb : b.length ≤ S) :
      ∀ i,(Function.update s j b i).length ≤ S := by
    intro i
    by_cases hi : i=j
    · subst i; simpa using hb
    · simpa only [Function.update_of_ne hi] using hs i
  have hc : (List.replicate (p.R+1) true).length ≤ S := by simpa using h.countSize
  have hz : (List.replicate ((p.R+1)*(d*baseWidth 3 p.t)) false).length ≤ S := by
    simpa using h.arraySize
  have h1 := upd (localStore a) h.local_bound 243 _ hc
  have h2 := upd _ h1 242 _ hz
  have h3 := upd _ h2 192 _ hz
  have h4 := upd _ h3 193 _ hc
  have hidx : (LayoutSourcePlanLookup.unary (ps.idxOf (v,N+f))).length ≤ S := by
    simpa only [LayoutSourcePlanLookup.unary,List.length_replicate,List.idxOf,beq_eq_decide] using
      (List.idxOf_le_length (a := (v,N+f)) (l := ps)).trans h.incidenceBound
  exact upd _ h4 304 _ hidx i

end SubexponentialSAT.SqrtLog.LeafProgram.SourceReady

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceReady.Input.base_bound_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceReady.Input.base_bound_oai
