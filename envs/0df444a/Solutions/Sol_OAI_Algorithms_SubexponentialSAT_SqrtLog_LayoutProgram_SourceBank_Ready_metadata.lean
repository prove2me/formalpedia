-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Ready.metadata
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:24:51.828733+00:00
-- url     : https://prove2.me/submissions/ade5af12-542c-4868-bcc8-ce6cad3eabdb

import Mathlib
import Definitions.Def_OAIQ081S174

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

theorem lowStore_metadata (a : Data) (mr mc : GlobalBasisMetadata.Metadata)
    (rf : Fin 16 → Bool) : lowStore (⟨rf,metadataStacks a mr mc⟩ : Data)=lowStore a := by
  funext i
  have hb : (vectorPorts i).val < 256 := i.isLt
  have hn (j : Fin 320) (hj : 256 ≤ j.val) : vectorPorts i≠j := by
    intro h; have := congrArg Fin.val h; omega
  simp [lowStore,projectState,metadataStacks,
    hn 288 (by decide),hn 289 (by decide),hn 290 (by decide),
    hn 291 (by decide),hn 292 (by decide),hn 293 (by decide)]

theorem inputFields_frame {r Q : ℕ} (a b : Data) (c : Numerator.Saved) (start : Fin Q)
    (u y : UniversalType r Q 1) (h : InputFields a c start u y)
    (hf : lowStore b=lowStore a) : InputFields b c start u y := by
  intro i hi hj
  rw [hf]
  exact h i hi hj

theorem cachedReady_metadata (t : ℕ) {d : ℕ} (model : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (zero one minusOne : ModelCode t d) (a : Data)
    (mr mc : GlobalBasisMetadata.Metadata) (rf : Fin 16 → Bool)
    (h : CachedReady t model M cache zero one minusOne (lowStore a)) :
    CachedReady t model M cache zero one minusOne (lowStore (⟨rf,metadataStacks a mr mc⟩ : Data)) := by
  rw [lowStore_metadata]
  exact h

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

theorem metadata_frame (a : Data) (mr mc : GlobalBasisMetadata.Metadata)
    (j : Fin 320) (hj : j.val < 288 ∨ 293 < j.val) :
    metadataStacks a mr mc j=a.stacks j := by
  have h288 : j≠288 := by intro h; subst j; norm_num at hj
  have h289 : j≠289 := by intro h; subst j; norm_num at hj
  have h290 : j≠290 := by intro h; subst j; norm_num at hj
  have h291 : j≠291 := by intro h; subst j; norm_num at hj
  have h292 : j≠292 := by intro h; subst j; norm_num at hj
  have h293 : j≠293 := by intro h; subst j; norm_num at hj
  simp [metadataStacks,h288,h289,h290,h291,h292,h293]

theorem WorkReady.metadata {a b : Data} (h : WorkReady a)
    (mr mc : GlobalBasisMetadata.Metadata) (hb : b.stacks=metadataStacks a mr mc) : WorkReady b := by
  constructor
  · intro j hj hk; rw [hb,metadata_frame a mr mc j hk]; exact h.work j hj hk
  · rw [hb,metadata_frame a mr mc 319 (Or.inr (by decide))]; exact h.temp
  · rw [hb,metadata_frame a mr mc 287 (Or.inl (by decide))]; exact h.output
  · rw [hb,metadata_frame a mr mc 37 (Or.inl (by decide))]; exact h.count
  · rw [hb,metadata_frame a mr mc 64 (Or.inl (by decide))]; exact h.tableCount
  · rw [hb,metadata_frame a mr mc 65 (Or.inl (by decide))]; exact h.tableAccum
  · intro j hj; rw [hb,metadata_frame a mr mc j (Or.inl (by omega))]; exact h.low j hj

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceConfiguration
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete numerical and cache inputs to the source bank. The state predicate
contains byte representations only; it contains no program-service premise. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open IntegerRingLiftProgram RowSelectionProgram

variable {r Q d : ℕ}

theorem Ready.metadata_oai {p : Parameters r Q d} {a b : Data} (h : Ready p a)
    (mr mc : GlobalBasisMetadata.Metadata) (hb : b.stacks=metadataStacks a mr mc) : Ready p b := by
  have hf (j : Fin 320) (hj : j.val < 288 ∨ 293 < j.val) : b.stacks j=a.stacks j := by
    rw [hb,metadata_frame a mr mc j hj]
  constructor
  · exact h.work.metadata mr mc hb
  · intro u y
    apply inputFields_frame a b p.saved p.start u y (h.input u y)
    have hh := lowStore_metadata a mr mc b.regs
    simpa only [lowStore,projectState,hb] using hh
  · have hh := cachedReady_metadata p.t p.model p.modulus p.cache _ _ _ a mr mc b.regs h.ring
    simpa only [lowStore,projectState,hb] using hh
  · exact (hf 252 (Or.inl (by decide))).trans h.inverseDenominator
  · rw [hf 22 (Or.inl (by decide))]; exact h.nodes
  · rw [hf 47 (Or.inl (by decide))]; exact h.limit
  · exact (hf 308 (Or.inr (by decide))).trans h.inverses
  · exact (hf 309 (Or.inr (by decide))).trans h.negatives
  · exact (hf 310 (Or.inr (by decide))).trans h.differences
  · exact (hf 311 (Or.inr (by decide))).trans h.ringWidth
  · exact (hf 312 (Or.inr (by decide))).trans h.rowWidth
  · exact (hf 313 (Or.inr (by decide))).trans h.zero
  · exact (hf 314 (Or.inr (by decide))).trans h.one

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Ready.metadata_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Ready.metadata_oai
