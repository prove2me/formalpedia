-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCorrect.prepared_product_eval_correct
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T11:37:53.096494+00:00
-- url     : https://prove2.me/submissions/dfb8fc24-8d7d-4721-aa87-b7e87d394d1d

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S191
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_FactorAssignmentCallback_callbackBudget_le
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_FactorAssignmentCallback_callback_eval_correct

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeSparse
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Computable normalized sparse coefficient lists. Zero coefficients may stay
in the list; keys are unique, so this does not enlarge the finite index bound.
No equality decision for coefficients or full ambient Boolean table is used. -/

namespace SubexponentialSAT.SqrtLog.Squarefree.Sparse

open scoped BigOperators

variable {K R A : Type*} [DecidableEq K] [AddCommMonoid R]

omit [AddCommMonoid R] in
theorem length_le_card (l : Data K R) (s : Finset K) (hn : (keys l).Nodup)
    (hs : ∀ k ∈ keys l, k ∈ s) : l.length ≤ s.card := by
  have hsub : (keys l).toFinset ⊆ s := by
    intro k hk
    exact hs k (List.mem_toFinset.mp hk)
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hn] at hcard
  simpa only [keys, List.length_map] using hcard

end SubexponentialSAT.SqrtLog.Squarefree.Sparse

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramNormalize
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms



namespace SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable {K C R A : Type*} [DecidableEq K] [CommRing R] [AddCommMonoid A]

omit [DecidableEq K] [CommRing R] in
theorem denoteTable_keys (f : C → R) (entries : List (K × C)) :
    Squarefree.Sparse.keys (denoteTable f entries) = Squarefree.Sparse.keys entries := by
  simp [denoteTable,Squarefree.Sparse.keys,List.map_map,Function.comp_def]

end SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary


namespace SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary

 theorem rawEntries_length_le (entries : List (List Bool × List Bool)) (W C : ℕ)
    (hk : ∀ a ∈ entries, a.1.length ≤ W) (hc : ∀ a ∈ entries, a.2.length ≤ C) :
    (Squarefree.Program.rawEntries entries).length ≤ entries.length * (2*W+2*C+2) := by
  induction entries with
  | nil => simp [Squarefree.Program.rawEntries]
  | cons a entries ih =>
    have h1 := hk a (by simp)
    have h2 := hc a (by simp)
    have h3 := ih (fun b hb => hk b (by simp [hb])) (fun b hb => hc b (by simp [hb]))
    simp only [Squarefree.Program.rawEntries,List.length_append,Encoding.length_frame,List.length_cons]
    nlinarith

end SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeIndexEncoding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A self-delimiting encoding of sparse keys: two unary numeric fields,
followed by exactly n support bits. The encoding works without precision
assumptions; the precision assumptions only bound its length. -/

namespace SubexponentialSAT.SqrtLog.Squarefree

theorem encodeIndex_length_le {n t J : ℕ} (a : Index (Fin n))
    (h : a.Kept t J) : (encodeIndex a).length ≤ t + J + n := by
  rw [encodeIndex_length]
  obtain ⟨hu, hz⟩ := h
  omega

end SubexponentialSAT.SqrtLog.Squarefree

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeSparseBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Squarefree

open scoped BigOperators

namespace Sparse

variable {V R : Type*} [DecidableEq V] [CommSemiring R]

theorem mem_indexUniverse (vars : Finset V) (t J : ℕ) (a : Index V) :
    a ∈ indexUniverse vars t J ↔ a.Kept t J ∧ a.vars ⊆ vars ∧ a.vars.card < J := by
  rcases a with ⟨u, z, s⟩
  simp [indexUniverse, supportUniverse, Index.Kept, Finset.mem_image]

theorem indexUniverse_card_le (vars : Finset V) (t J : ℕ) :
    (indexUniverse vars t J).card ≤ t * J * (supportUniverse vars J).card := by
  exact (Finset.card_image_le).trans (by simp)

omit [CommSemiring R] in
theorem ValidData.in_universe {vars : Finset V} {t J : ℕ} {l : Data (Index V) R}
    (h : ValidData vars t J l) : ∀ a ∈ keys l, a ∈ indexUniverse vars t J := by
  intro a ha
  rcases h a ha with ⟨hk, hv, hs⟩
  exact (mem_indexUniverse vars t J a).mpr ⟨hk, hs, hv.trans_lt hk.2⟩

omit [CommSemiring R] in
theorem ValidData.length_le {vars : Finset V} {t J : ℕ} {l : Data (Index V) R}
    (h : ValidData vars t J l) (hn : (keys l).Nodup) :
    l.length ≤ t * J * (supportUniverse vars J).card :=
  (length_le_card l _ hn h.in_universe).trans (indexUniverse_card_le vars t J)

end Sparse
end SubexponentialSAT.SqrtLog.Squarefree

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashInputProgramLoopFinal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Public raw-input ABI and the uniform paid execution theorem. All control
tables are fixed independently of source size, raw tuple length and ring width.
Repeated source references and zero coefficients remain separate records. -/
namespace SubexponentialSAT.SqrtLog.HashInputProgram.Loop
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem original_payload_length_le (clauses : List (List Bool)) (p : List Bool)
    (hp : p∈clauses) : p.length ≤ (Encoding.encodeList id clauses).length := by
  induction clauses with
  | nil => simp at hp
  | cons q qs ih =>
      have hq := Encoding.length_frame q
      simp only [Encoding.encodeList,id_eq,Encoding.length_frame,List.length_cons,List.length_append] at *
      rcases List.mem_cons.mp hp with rfl | hp
      · omega
      · have hh := ih hp
        omega

end SubexponentialSAT.SqrtLog.HashInputProgram.Loop

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramIncidence
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The selected-factor incidence service with a concrete source generator.
All ring/layout inputs are copied from persistent masters, and the complete
private worker is reclaimed after exporting the actual lookup table. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Incidence
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage

theorem mem_workerPorts (i : Fin 768) : i ∈ workerPorts ↔ 340 ≤ i.val ∧ i.val < 680 := by
  simp only [workerPorts,List.mem_map,List.mem_finRange,true_and]
  constructor
  · rintro ⟨j,hj⟩
    have hv := congrArg Fin.val hj
    change 340+j.val=i.val at hv
    omega
  · intro hi
    refine ⟨⟨i.val-340,by omega⟩,?_⟩
    apply Fin.ext
    change 340+(i.val-340)=i.val
    omega

end SubexponentialSAT.SqrtLog.LeafProgram.Incidence

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramProductBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsProgram.Product
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem bytes_length_le {n B d : ℕ} (entries : List (Entry n B d)) (W : ℕ)
    (h : Normalize.KeyBound Squarefree.encodeIndex W entries) :
    (bytes entries).length ≤ entries.length*(2*W+2*(d*B)+2) := by
  have hh := Dictionary.rawEntries_length_le
    (Squarefree.Program.encodeDictionary Squarefree.encodeIndex RingProgram.flat entries) W (d*B)
    (by intro a ha; obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha; exact h b hb)
    (by intro a ha; obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha; exact le_of_eq (RingProgram.flat_length b.2))
  simpa [bytes,Normalize.bytes,Squarefree.Program.encodeDictionary] using hh

end SubexponentialSAT.SqrtLog.MomentsProgram.Product

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramValidity
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

namespace Product

theorem decoded_valid {R : Type*} [CommRing R] {n B d : ℕ}
    (f : RingProgram.Code (Word B) d → R) (vars : Finset (Fin n)) (u J : ℕ)
    (entries : List (Entry n B d)) (h : ∀ a ∈ entries, ValidKey vars u J a.1) :
    Squarefree.Sparse.ValidData vars u J (Dictionary.denoteTable f entries) := by
  intro k hk
  simp only [Squarefree.Sparse.keys,Dictionary.denoteTable,List.map_map,Function.comp_def] at hk
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hk
  exact h a ha

end Product
end SubexponentialSAT.SqrtLog.MomentsProgram

end OAI.Algorithms
end

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
section NativeValidity

namespace Good

variable {n B d u J : ℕ} {vars : Finset (Fin n)}

theorem decoded_valid {R : Type*} [CommRing R]
    {a : List (Product.Entry n B d)} (h : Good vars u J a)
    (f : RingProgram.Code (Word B) d → R) :
    Squarefree.Sparse.ValidData vars u J (Dictionary.denoteTable f a) :=
  Product.decoded_valid f vars u J a h.valid

theorem length_le {a : List (Product.Entry n B d)} (h : Good vars u J a) :
    a.length ≤ u*J*(Squarefree.Sparse.supportUniverse vars J).card := by
  have hv := h.decoded_valid (fun _ => (0 : ℤ))
  have hn : (Squarefree.Sparse.keys (Dictionary.denoteTable (fun _ => (0 : ℤ)) a)).Nodup := by
    simpa only [Dictionary.denoteTable_keys] using h.nodup
  simpa only [Dictionary.denoteTable,List.length_map] using hv.length_le hn

end Good


end NativeValidity

variable {V R : Type*} [DecidableEq V] [CommRing R]

omit [DecidableEq V] in
/-- Empty formal support has at most one possible support, also when `J = 0`. -/
theorem empty_support_card_le (J : ℕ) :
    (Squarefree.Sparse.supportUniverse (∅ : Finset V) J).card ≤ 1 := by
  calc
    _ ≤ ((∅ : Finset V).powerset).card := Finset.card_filter_le _ _
    _ = 1 := by simp

theorem empty_length_le {n B d u J : ℕ} {a : List (Product.Entry n B d)}
    (ha : Good ∅ u J a) : a.length ≤ u * J := by
  exact ha.length_le.trans (by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (u * J)
      (empty_support_card_le (V := Fin n) J))

theorem empty_bytes_length_le {n B d u J : ℕ} {a : List (Product.Entry n B d)}
    (ha : Good ∅ u J a) :
    (Product.bytes a).length ≤ u * J * (2 * (u + J + n) + 2 * (d * B) + 2) := by
  exact (Product.bytes_length_le a (u + J + n)
    (fun x hx => Squarefree.encodeIndex_length_le x.1 (ha.valid x hx).1)).trans
      (Nat.mul_le_mul_right _ (empty_length_le ha))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorTableProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual selected-factor table runs over ambient variable IDs. Each low
payload is specialized immediately before its framed table entry is retained.
The source scratch embedding excludes persistent layout masters. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI BitProgram StructuredCalls SubexpConvolutionControl SubexpScanPrimitives
open SubexpPolynomialConstructor PerturbationAssembly OAI.Algorithms.SubexponentialSAT.SubexpLiftRing

attribute [local simp] Fin.coe_ofNat_eq_mod

theorem basePort_protected (i : Fin 768) :
    basePort i ≠ 640 ∧ basePort i ≠ 641 ∧ basePort i ≠ 642 ∧ basePort i ≠ 647 ∧
      basePort i ≠ 650 ∧ basePort i ≠ 651 ∧ basePort i ≠ 670 ∧ basePort i ≠ 671 := by
  simp only [basePort]
  split_ifs <;> simp_all [Fin.ext_iff, Fin.coe_ofNat_eq_mod]

theorem basePort_high (i : Fin 768) :
    (basePort i).val < 768 ∨ (885 ≤ (basePort i).val ∧ (basePort i).val ≤ 892) := by
  simp only [basePort]
  split_ifs <;> simp_all only [Fin.val_castAdd, Fin.coe_ofNat_eq_mod] <;> omega

theorem basePort_outside (i : Fin 896)
    (hi : i ∈ protectedPorts ∨ (768 ≤ i.val ∧ (i.val < 885 ∨ 892 < i.val))) :
    ¬ ∃ j, basePort j = i := by
  rintro ⟨j, hj⟩
  rcases hi with hi | hi
  · simp only [protectedPorts, List.mem_cons, List.mem_nil_iff, or_false] at hi
    have hp := basePort_protected j
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hp.1 hj
    · exact hp.2.1 hj
    · exact hp.2.2.1 hj
    · exact hp.2.2.2.1 hj
    · exact hp.2.2.2.2.1 hj
    · exact hp.2.2.2.2.2.1 hj
    · exact hp.2.2.2.2.2.2.1 hj
    · exact hp.2.2.2.2.2.2.2 hj
  · have hm := basePort_high j
    rw [hj] at hm
    omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorAssignmentProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The accepted-assignment factor product uses the original finite-ring
indicator and clause programs after the concrete specialized table producer.
Every cache is rebuilt from persistent source words by paid native copies;
neutral factor IDs leave the running multiplicative identity unchanged. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram

open OAI BitProgram StructuredCalls SubexpSetupStorage
open SqrtLog SqrtLog.LeafProgram
noncomputable section

theorem move_eval (a : Data) (src dst : Fin 896)
    (hsd : src ≠ dst) (hst : src ≠ 159) (htd : (159 : Fin 896) ≠ dst)
    (htmp : a.stacks 159 = []) :
    Eval (move src dst) (9 * (a.stacks src).length + 8) a (moved a src dst) := by
  have hcopy := SubexpScanPrimitives.copy_eval a src dst 159 0 1 hsd hst htd (by decide) htmp
  let b := SubexpScanPrimitives.afterCopy a src dst 0 1
  have hclear : Eval (clear src) (2 * (b.stacks src).length + 3) b
      ⟨readRegs b.regs 0 1 none, Function.update b.stacks src []⟩ :=
    Eval.call _ (ListRegisterProgram.clear_run src (0 : Fin 40) 1 b.regs b.stacks)
  have hlen : b.stacks src = a.stacks src := by
    simp [b, SubexpScanPrimitives.afterCopy, StackRoutines.copyStacks, hsd]
  have hout : (⟨readRegs b.regs 0 1 none, Function.update b.stacks src []⟩ : Data) =
      moved a src dst := by
    apply congrArg₂ StructuredProgram.State.mk
    · simp [b, SubexpScanPrimitives.afterCopy, StackRoutines.readRegs_reset]
    · rfl
  rw [hout] at hclear
  have he := hcopy.seq hclear
  simpa only [move, copy, hlen, show 7 * (a.stacks src).length + 5 +
    (2 * (a.stacks src).length + 3) = 9 * (a.stacks src).length + 8 by omega] using he

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorTableSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Space for one actual ambient-coordinate table construction. Its unary
traversal has only n iterations, so its polynomial local time bounds every
source prefix. No outer signature or finite-difference iteration count occurs
in this estimate. The concrete literal and staging traces are instantiated by
the factor-table producer, rather than supplied to a final counting endpoint. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableSpace

open SqrtLog

open BitProgram StructuredCalls FactorTableProgram

/-- The protected caller regions include every low node port except the
export62, all eight layout masters, and high ports outside the private bank. -/
theorem caller_port_not_written (i : Fin 896)
    (hi : (i.val < 340 ∧ i ≠ 62) ∨ i ∈ protectedPorts ∨
      (768 ≤ i.val ∧ i ≠ 881 ∧ i ≠ 882 ∧ (i.val < 885 ∨ 892 < i.val))) :
    i ∉ writtenPorts := by
  intro hm
  rcases List.mem_append.mp hm with hm | hm
  · obtain ⟨j, hj, hji⟩ := List.mem_map.mp hm
    rcases hi with hi | hi | hi
    · have hw := (LeafProgram.Incidence.mem_workerPorts j).mp hj
      have hb : 340 ≤ (basePort j).val := by
        simp only [basePort]
        split_ifs <;> simp_all only [Fin.coe_ofNat_eq_mod, Fin.val_castAdd] <;> omega
      have hv := congrArg Fin.val hji
      omega
    · exact basePort_outside i (Or.inl hi) ⟨j, hji⟩
    · exact basePort_outside i (Or.inr ⟨hi.1, hi.2.2.2⟩) ⟨j, hji⟩
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      norm_num [protectedPorts, Fin.ext_iff, Fin.coe_ofNat_eq_mod] at hi

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorAssignmentLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Relational execution of the fixed specialized factor-record loop. This
adapts the original FactorLoop reader/while proof to the shared 896-stack ABI
and empty-support dictionaries. The explicit callback premise must be proved
for the actual callback before this component can close an algorithm endpoint. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentLoop
attribute [local simp] Fin.coe_ofNat_eq_mod
open OAI BitProgram StructuredCalls SqrtLog SqrtLog.LeafProgram MomentsProgram

theorem recordState_eq {n B d : ℕ} (base : Fin 896 → List Bool)
    (regs : Fin 40 → Bool) (seed : Raw n B d) (v pr f : Bool) (source payload : List Bool) :
    recordState base regs seed v pr f source payload =
      state base (recordState base regs seed v pr f source payload).regs seed source payload := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    by_cases h149 : i=149 <;> by_cases h150 : i=150 <;>
      simp [FactorAssignmentProgram.ports, state, Function.update_apply, h149, h150]

theorem recordState_self {n B d : ℕ} (base : Fin 896 → List Bool)
    (regs : Fin 40 → Bool) (seed : Raw n B d) (v pr f : Bool) (source payload : List Bool)
    (h13 : regs 13=v) (h14 : regs 14=pr) (h15 : regs 15=f) :
    recordState base regs seed v pr f source payload = state base regs seed source payload := by
  rw [recordState_eq]
  congr 1
  funext i
  by_cases h1 : i=13 <;> by_cases h2 : i=14 <;> by_cases h3 : i=15 <;>
    simp_all [recordState, RecordPrograms.state, FactorAssignmentProgram.ports, state]

theorem inner_eval {n B d : ℕ} (u J : ℕ)
    (step : Raw n B d → ℕ → Raw n B d → Prop)
    (ready : (Fin 896 → List Bool) → Prop) (eligible : ℕ → Prop) (T C : ℕ)
    (contract : ∀ base, ready base → ∀ id seed tail regs, eligible id →
      NativeSemantics.Good ∅ u J seed → tail.length ≤ T →
      ∃ out, NativeSemantics.Good ∅ u J out ∧ step seed id out ∧
        ∃ k ≤ C, ∃ rr,
          Eval FactorAssignmentProgram.callback k
            (state base regs seed tail (Encoding.encodeNat id).reverse)
            (state base rr out tail []) ∧ rr 13 = false ∧ rr 14 = true ∧ rr 15 = false)
    (base : Fin 896 → List Bool) (hb : ready base)
    (ids : List ℕ) (seed : Raw n B d) (regs : Fin 40 → Bool)
    (hg : NativeSemantics.Good ∅ u J seed) (hids : ∀ id ∈ ids, eligible id)
    (hlen : (ProgramEncoding.encodeRecords (records ids)).length ≤ T) :
    ∃ out, NativeSemantics.Good ∅ u J out ∧ MomentsAssembly.Relational.FoldRel step ids seed out ∧
      ∃ k ≤ 1+RecordPrograms.budget (fun _ => C) (records ids), ∃ rr,
        Eval (RecordPrograms.loop FactorAssignmentProgram.ports FactorAssignmentProgram.callback) k
          (RecordPrograms.afterTag FactorAssignmentProgram.ports (state base regs seed [] []) (records ids) [])
          (recordState base rr out false true false [] []) := by
  induction ids generalizing seed regs with
  | nil =>
    refine ⟨seed,hg,.nil seed,1,by simp [records,RecordPrograms.budget],regs,?_⟩
    apply Eval.while_false
    simp [RecordPrograms.afterTag,records,FactorAssignmentProgram.ports,RecordPrograms.state]
  | cons fid ids ih =>
    let bits := Encoding.encodeNat fid
    let tail := Encoding.encodeList id (records ids) ++ []
    let parsed := recordState base regs seed false true false tail bits.reverse
    obtain ⟨next,hnext,hstep,k,hk,rr,hcall,h13,h14,h15⟩ :=
      contract base hb fid seed tail parsed.regs (hids fid (by simp)) hg (by
        have hh : (ProgramEncoding.encodeRecords (records ids)).length ≤ T := by
          simp only [ProgramEncoding.encodeRecords,records,List.map_cons,Encoding.encodeList,
            List.length_cons,List.length_append] at hlen ⊢
          omega
        simpa [tail,ProgramEncoding.encodeRecords] using hh)
    have hcall' : Eval FactorAssignmentProgram.callback k parsed
        (recordState base rr next false true false tail []) := by
      rw [recordState_self base rr next false true false tail [] h13 h14 h15]
      have hp : parsed = state base parsed.regs seed tail bits.reverse :=
        recordState_eq base regs seed false true false tail bits.reverse
      rw [hp]
      exact hcall
    have hreader : Eval (RecordPrograms.reader FactorAssignmentProgram.ports) (6*bits.length+4)
        (RecordPrograms.afterTag FactorAssignmentProgram.ports (state base regs seed [] []) (records (fid::ids)) [])
        parsed := by
      simpa [parsed,recordState,records,RecordPrograms.afterTag,bits,tail] using
        RecordPrograms.reader_eval FactorAssignmentProgram.ports (state base regs seed [] []) bits tail [] true true false
    have hbranch : Eval
        (.ite FactorAssignmentProgram.ports.found (RecordPrograms.atom (.set FactorAssignmentProgram.ports.tag false))
          (RecordPrograms.atom (.pop FactorAssignmentProgram.ports.source FactorAssignmentProgram.ports.tag FactorAssignmentProgram.ports.present))) 2
        (recordState base rr next false true false tail [])
        (RecordPrograms.afterTag FactorAssignmentProgram.ports (state base rr next [] []) (records ids) []) := by
      apply Eval.ite_false (by simp [recordState])
      exact RecordPrograms.pop_list_eval FactorAssignmentProgram.ports (state base rr next [] []) (records ids) [] false true
    obtain ⟨out,hout,hrel,m,hm,rf,hrest⟩ := ih next rr hnext (fun id hi => hids id (by simp [hi])) (by
      simp only [ProgramEncoding.encodeRecords,records,List.map_cons,Encoding.encodeList,
        List.length_cons,List.length_append] at hlen ⊢
      omega)
    have hguard :
        (RecordPrograms.afterTag FactorAssignmentProgram.ports (state base regs seed [] []) (records (fid::ids)) []).regs
          FactorAssignmentProgram.ports.tag=true := by simp [RecordPrograms.afterTag,records]
    refine ⟨out,hout,.cons hstep hrel,(6*bits.length+4+(k+2))+m+1,?_,rf,?_⟩
    · simp only [records,List.map_cons,RecordPrograms.budget] at hm ⊢
      dsimp [bits]
      omega
    · exact Eval.while_true hguard (hreader.seq (hcall'.seq hbranch)) hrest

theorem loop_eval {n B d : ℕ} (u J : ℕ)
    (step : Raw n B d → ℕ → Raw n B d → Prop)
    (ready : (Fin 896 → List Bool) → Prop) (eligible : ℕ → Prop) (T C : ℕ)
    (contract : ∀ base, ready base → ∀ id seed tail regs, eligible id →
      NativeSemantics.Good ∅ u J seed → tail.length ≤ T →
      ∃ out, NativeSemantics.Good ∅ u J out ∧ step seed id out ∧
        ∃ k ≤ C, ∃ rr,
          Eval FactorAssignmentProgram.callback k
            (state base regs seed tail (Encoding.encodeNat id).reverse)
            (state base rr out tail []) ∧ rr 13 = false ∧ rr 14 = true ∧ rr 15 = false)
    (base : Fin 896 → List Bool) (hb : ready base)
    (ids : List ℕ) (seed : Raw n B d) (regs : Fin 40 → Bool)
    (hg : NativeSemantics.Good ∅ u J seed) (hids : ∀ id ∈ ids, eligible id)
    (hlen : (ProgramEncoding.encodeRecords (records ids)).length ≤ T) :
    ∃ out, NativeSemantics.Good ∅ u J out ∧ MomentsAssembly.Relational.FoldRel step ids seed out ∧
      ∃ k ≤ loopBudget C ids, ∃ rr,
        Eval FactorAssignmentProgram.loop k
          (state base regs seed (ProgramEncoding.encodeRecords (records ids)) [])
          (state base rr out [] []) := by
  obtain ⟨out,hout,hr,k,hk,rr,he⟩ := inner_eval u J step ready eligible T C contract base hb ids seed regs hg hids hlen
  let initial := state base regs seed (ProgramEncoding.encodeRecords (records ids)) []
  have hstart : recordState base regs seed (regs 13) (regs 14) (regs 15)
      (Encoding.encodeList id (records ids) ++ []) [] = initial := by
    rw [recordState_self base regs seed _ _ _ _ _ rfl rfl rfl]
    simp [initial,ProgramEncoding.encodeRecords]
  have hset := RecordPrograms.set_found_eval FactorAssignmentProgram.ports (state base regs seed [] [])
    (regs 13) (regs 14) (regs 15) false (Encoding.encodeList id (records ids) ++ []) []
  have hpop := RecordPrograms.pop_list_eval FactorAssignmentProgram.ports (state base regs seed [] [])
    (records ids) [] (regs 13) (regs 14)
  have hrun := hset.seq (hpop.seq he)
  change Eval FactorAssignmentProgram.loop (1+(1+k))
    (recordState base regs seed (regs 13) (regs 14) (regs 15) _ [])
    (recordState base rr out false true false [] []) at hrun
  rw [hstart,recordState_eq] at hrun
  exact ⟨out,hout,hr,1+(1+k),by dsimp [loopBudget]; omega,_,hrun⟩

theorem loopBudget_le (C : ℕ) (ids : List ℕ) :
    loopBudget C ids ≤ (C+17)*((ProgramEncoding.encodeRecords (records ids)).length+1) := by
  have h := RecordPrograms.program_budget_le_input (fun _ => C) (records ids) 0 C (by simp)
  simp only [Nat.zero_add] at h
  dsimp [loopBudget]
  omega

theorem product_eval {n B d : ℕ} (u J : ℕ)
    (step : Raw n B d → ℕ → Raw n B d → Prop)
    (ready : (Fin 896 → List Bool) → Prop) (eligible : ℕ → Prop) (T C : ℕ)
    (contract : ∀ base, ready base → ∀ id seed tail regs, eligible id →
      NativeSemantics.Good ∅ u J seed → tail.length ≤ T →
      ∃ out, NativeSemantics.Good ∅ u J out ∧ step seed id out ∧
        ∃ k ≤ C, ∃ rr,
          Eval FactorAssignmentProgram.callback k
            (state base regs seed tail (Encoding.encodeNat id).reverse)
            (state base rr out tail []) ∧ rr 13 = false ∧ rr 14 = true ∧ rr 15 = false)
    (a : FactorAssignmentProgram.Data) (ha : ready a.stacks) (ids : List ℕ) (one : Raw n B d)
    (hg : NativeSemantics.Good ∅ u J one) (hids : ∀ id ∈ ids, eligible id)
    (hlen : (ProgramEncoding.encodeRecords (records ids)).length ≤ T)
    (h175 : a.stacks 175=ProgramEncoding.encodeRecords (records ids))
    (h69 : a.stacks 69=Product.bytes one)
    (h149 : a.stacks 149=[]) (h150 : a.stacks 150=[]) (h151 : a.stacks 151=[])
    (h854 : a.stacks 854=[]) (h159 : a.stacks 159=[]) :
    ∃ out, NativeSemantics.Good ∅ u J out ∧ MomentsAssembly.Relational.FoldRel step ids one out ∧
      ∃ k ≤ productBudget n B d u J C ids, ∃ rr,
        Eval FactorAssignmentProgram.product k a ⟨rr,Function.update a.stacks 854 (Product.bytes out)⟩ := by
  let a1 := SubexpScanPrimitives.afterCopy a 175 150 0 1
  let a2 := SubexpScanPrimitives.afterCopy a1 69 151 0 1
  have h1 : Eval (FactorAssignmentProgram.copy 175 150) (7*(a.stacks 175).length+5) a a1 :=
    SubexpScanPrimitives.copy_eval a 175 150 159 0 1 (by decide) (by decide) (by decide) (by decide) h159
  have h2 : Eval (FactorAssignmentProgram.copy 69 151) (7*(a1.stacks 69).length+5) a1 a2 :=
    SubexpScanPrimitives.copy_eval a1 69 151 159 0 1 (by decide) (by decide) (by decide) (by decide)
      (by simpa [a1,SubexpScanPrimitives.afterCopy,StackRoutines.copyStacks] using h159)
  have hinput : a2=state a.stacks a2.regs one (ProgramEncoding.encodeRecords (records ids)) [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      by_cases h1 : i=149 <;> by_cases h2 : i=150 <;> by_cases h3 : i=151 <;>
        simp_all [a2, a1, SubexpScanPrimitives.afterCopy, StackRoutines.copyStacks, state]
  obtain ⟨out,ho,hr,nl,hl,rr,he⟩ := loop_eval u J step ready eligible T C contract a.stacks ha ids one
    a2.regs hg hids hlen
  rw [← hinput] at he
  let b := state a.stacks rr out [] []
  have h3 := FactorAssignmentProgram.move_eval b 151 854 (by decide) (by decide) (by decide)
    (by simpa [b,state] using h159)
  have hout : FactorAssignmentProgram.moved b 151 854 =
      ⟨(FactorAssignmentProgram.moved b 151 854).regs,Function.update a.stacks 854 (Product.bytes out)⟩ := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      by_cases h1 : i=149 <;> by_cases h2 : i=150 <;> by_cases h3 : i=151 <;>
        by_cases h4 : i=854 <;>
        simp [b, state, h1, h2, h3, h4, h149, h150, h151, h854]
  rw [hout] at h3
  have honeBound := TruncatedRingProgram.empty_bytes_length_le (a:=one) ⟨hg.valid, hg.nodup⟩
  have houtBound := TruncatedRingProgram.empty_bytes_length_le (a:=out) ⟨ho.valid, ho.nodup⟩
  refine ⟨out,ho,hr,(7*(a.stacks 175).length+5)+((7*(a1.stacks 69).length+5)+
    (nl+(9*(b.stacks 151).length+8))),?_,_,h1.seq (h2.seq (he.seq h3))⟩
  dsimp [productBudget,byteBound]
  simp only [h175] at *
  have h69' : a1.stacks 69=Product.bytes one := by
    simpa [a1,SubexpScanPrimitives.afterCopy,StackRoutines.copyStacks] using h69
  simp only [h69']
  have hb151 : b.stacks 151=Product.bytes out := by simp [b,state]
  rw [hb151]
  omega

/-- The specialized record fold multiplies in the coefficient ring before any
additive shared-variable readout. Its empty list contributes the stored identity. -/
theorem foldRel_mul {n B d : ℕ} {R : Type*} [Monoid R]
    (decode : Raw n B d → R) (value : ℕ → R)
    (step : Raw n B d → ℕ → Raw n B d → Prop)
    (hstep : ∀ a id b, step a id b → decode b = decode a * value id)
    {ids : List ℕ} {seed out : Raw n B d}
    (hr : MomentsAssembly.Relational.FoldRel step ids seed out) :
    decode out = decode seed * (ids.map value).prod := by
  induction hr with
  | nil => simp
  | @cons id ids a b c hab hbc ih =>
    rw [ih, hstep a id b hab]
    simp only [List.map_cons, List.prod_cons, mul_assoc]

/-- This identity includes unused-factor groups and the empty product. -/
theorem foldRel_product {n B d : ℕ} {R : Type*} [Monoid R]
    (decode : Raw n B d → R) (value : ℕ → R)
    (step : Raw n B d → ℕ → Raw n B d → Prop)
    (hstep : ∀ a id b, step a id b → decode b = decode a * value id)
    {ids : List ℕ} {one out : Raw n B d}
    (hr : MomentsAssembly.Relational.FoldRel step ids one out)
    (hone : decode one = 1) : decode out = (ids.map value).prod := by
  rw [foldRel_mul decode value step hstep hr, hone, one_mul]

theorem productBudget_le (n B d u J T C : ℕ) (ids : List ℕ)
    (h : (ProgramEncoding.encodeRecords (records ids)).length ≤ T) :
    productBudget n B d u J C ids ≤ uniformProductBudget n B d u J T C := by
  have hl := loopBudget_le C ids
  have hm := Nat.mul_le_mul_left (C + 17) (Nat.add_le_add_right h 1)
  have hs := Nat.mul_le_mul_left 7 h
  dsimp [productBudget, uniformProductBudget]
  omega

/-- Good-empty-support restores the same structural boundary after the whole
factor product. The proof uses the exact output-tape update from product_eval,
so retained caller words never inherit the transient prefix bound. -/
theorem product_return_bound {n B d u J P : ℕ}
    (a b : FactorAssignmentProgram.Data) (out : Raw n B d)
    (hframe : b.stacks = Function.update a.stacks 854 (Product.bytes out))
    (ha : ∀ i, (a.stacks i).length ≤ P)
    (hout : NativeSemantics.Good ∅ u J out)
    (hcapacity : byteBound n B d u J ≤ P) :
    ∀ i, (b.stacks i).length ≤ P := by
  have hbytes : (Product.bytes out).length ≤ byteBound n B d u J :=
    TruncatedRingProgram.empty_bytes_length_le (a := out) ⟨hout.valid, hout.nodup⟩
  intro i
  rw [hframe]
  by_cases hi : i = 854
  · subst i
    simpa only [Function.update_self] using hbytes.trans hcapacity
  · simpa only [Function.update_of_ne hi] using ha i

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentLoop
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorAssignmentCallback
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual specialized callback dispatches one stored original factor ID.
The general dispatch theorem fixes its physical payload, flags and exact frame;
hash and marked branch correctness is supplied by their concrete native proofs. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback

open OAI BitProgram StructuredCalls
open SqrtLog SqrtLog.LeafProgram MomentsProgram FactorAssignmentProgram

noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

/-- Exact callback byte restoration supplies the state expected by the
record-fold theorem, while allowing the accumulator encoding to change. -/
theorem result_eq_state {n B d : ℕ} (base : Fin 896 → List Bool)
    (regs : Fin 40 → Bool) (seed out : FactorAssignmentLoop.Raw n B d)
    (tail payload : List Bool) (b : FactorAssignmentProgram.Data)
    (hb : b.stacks = Function.update
      (Function.update (FactorAssignmentLoop.state base regs seed tail payload).stacks 149 [])
      151 (Product.bytes out)) :
    b = FactorAssignmentLoop.state base b.regs out tail [] := by
  cases b with
  | mk rb sb =>
    apply congrArg (StructuredProgram.State.mk rb)
    funext i
    have hi := congrFun hb i
    by_cases h149 : i = 149 <;> by_cases h150 : i = 150 <;> by_cases h151 : i = 151
    all_goals simpa [FactorAssignmentLoop.state, Function.update_apply, h149, h150, h151] using hi

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorJet
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The incidence meaning depends only on the merged assignment and the
fixed-high context. Parser and accumulator contents do not enter it. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Factor
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open PerturbationAssembly DensePolynomialProgram

theorem factorJet_frame {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (n f j : ℕ) (theta : Coeff (baseWidth 3 p.t) d) (a b : Fin 768 → List Bool)
    (h145 : a 145=b 145) (h702 : a 702=b 702) (h703 : a 703=b 703) :
    factorJet p ps P n f j theta a=factorJet p ps P n f j theta b := by
  unfold factorJet sourceIncidenceJet
  simp only [choiceStore,show (574:Fin 768)≠546 by decide,show (575:Fin 768)≠546 by decide,
    show (575:Fin 768)≠574 by decide,ite_false,ite_true, if_true]
  rw [h145,h702,h703]

end SubexponentialSAT.SqrtLog.LeafProgram.Factor

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorAssignmentBoundary
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The real initializer and paid cache setup establish the physical boundary
for the actual stored-ID fold. Bounds are fixed before that fold; the current
Good-empty-support seed is serialized on151, the unread suffix on150 and the
reversed original ID on149. No execution service is a field below. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBoundary
open OAI BitProgram StructuredCalls SubexpSetupStorage
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps MomentsProgram NativeSemantics
open OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open FactorAssignmentProgram

noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem scalar_frame {t d J R n : ℕ} {model : RingModel.Data d}
    {M : SubexpPreparedQuartic.Modulus 3 t} {cache : RingProgram.ScalarCache 3 t}
    {theta : DensePolynomialProgram.Coeff (baseWidth 3 t) d}
    {a b : State 16 768}
    (h : FactorTableNative.ScalarMasters t model M cache J R theta a n)
    (hf : ∀ i ∈ scalarPorts, b.stacks i = a.stacks i) :
    FactorTableNative.ScalarMasters t model M cache J R theta b n := by
  refine ⟨h.widthPositive,h.zeroCanonical,h.zeroBits,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hf 194 (by decide)]; exact h.modulus
  · rw [hf 202 (by decide)]; exact h.width
  · rw [hf 203 (by decide)]; exact h.zero
  · rw [hf 201 (by decide)]; exact h.table
  · rw [hf 204 (by decide)]; exact h.degree
  · rw [hf 145 (by decide)]; exact h.choicesLength
  · rw [hf 280 (by decide)]; exact h.zeroWord
  · rw [hf 207 (by decide)]; exact h.oneWord
  · rw [hf 78 (by decide)]; exact h.thetaWord
  · rw [hf 128 (by decide)]; exact h.ambientCount
  · rw [hf 243 (by decide)]; exact h.targetCount
  · rw [hf 138 (by decide)]; exact h.radius
  · rw [hf 703 (by decide)]; exact h.highLength

theorem source_frame {r Q d : ℕ} {p : LayoutProgram.SourceBank.Parameters r Q d}
    {ps : List (ℕ × ℕ)}
    {P : OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking.PackingData (Fin ps.length)
      (OAI.Algorithms.SubexponentialSAT.MulticolorTypes.UniversalType r Q 1)} {a b : State 16 768}
    (h : FactorTableNative.SourceMasters p ps P a)
    (hf : ∀ i ∈ sourcePorts, b.stacks i = a.stacks i) :
    FactorTableNative.SourceMasters p ps P b := by
  constructor
  · rw [hf 130 (by decide)]; exact h.colors
  · rw [hf 131 (by decide)]; exact h.nodes
  · rw [hf 132 (by decide)]; exact h.typeWidth
  · rw [hf 710 (by decide)]; exact h.positive
  · rw [hf 711 (by decide)]; exact h.negative
  · rw [hf 140 (by decide)]; exact h.scalarWidth
  · rw [hf 712 (by decide)]; exact h.power
  · exact h.powerNegative
  · rw [hf 138 (by decide)]; exact h.radius
  · rw [hf 139 (by decide)]; exact h.offset
  · rw [hf 135 (by decide)]; exact h.metadata
  · rw [hf 136 (by decide)]; exact h.plans
  · rw [hf 713 (by decide)]; exact h.inverses
  · rw [hf 714 (by decide)]; exact h.negatives
  · rw [hf 715 (by decide)]; exact h.differences
  · rw [hf 717 (by decide)]; exact h.ringWidth
  · rw [hf 716 (by decide)]; exact h.rowWidth
  · rw [hf 280 (by decide)]; exact h.zero
  · rw [hf 207 (by decide)]; exact h.one
  · rw [hf 211 (by decide)]; exact h.minusOne
  · rw [hf 728 (by decide)]; exact h.inverseDenominator

/-- Updates of the three actual loop ports preserve every other stack. -/
theorem loop_state_frame {n B d : ℕ} (base : Fin 896 → List Bool)
    (regs : Fin 40 → Bool) (seed : FactorAssignmentLoop.Raw n B d)
    (tail payload : List Bool) (i : Fin 896)
    (h149 : i ≠ 149) (h150 : i ≠ 150) (h151 : i ≠ 151) :
    (FactorAssignmentLoop.state base regs seed tail payload).stacks i = base i := by
  simp only [FactorAssignmentLoop.state, Function.update_of_ne h149,
    Function.update_of_ne h150, Function.update_of_ne h151]

/-- Every parsed record has the same chosen structural bound, independently
of the prior prefix's transient workspace. -/
theorem loop_state_bound {n B d u J P : ℕ} (a : FactorAssignmentProgram.Data)
    (regs : Fin 40 → Bool) (seed : FactorAssignmentLoop.Raw n B d)
    (tail : List Bool) (f : ℕ) (ha : WordBound P a)
    (hseed : NativeSemantics.Good ∅ u J seed)
    (hcapacity : FactorAssignmentLoop.byteBound n B d u J ≤ P)
    (htail : tail.length ≤ P) (hf : f+1 ≤ P) :
    WordBound P (FactorAssignmentLoop.state a.stacks regs seed tail
      (Encoding.encodeNat f).reverse) := by
  have hs : (Product.bytes seed).length ≤ P :=
    (TruncatedRingProgram.empty_bytes_length_le (a := seed) ⟨hseed.valid,hseed.nodup⟩).trans hcapacity
  intro i
  by_cases hi149 : i = 149
  · subst i
    simpa only [FactorAssignmentLoop.state, Function.update_self, List.length_reverse,
      Encoding.length_encodeNat] using hf
  by_cases hi150 : i = 150
  · subst i
    simpa only [FactorAssignmentLoop.state, Function.update_of_ne (by decide : (150 : Fin 896) ≠ 149),
      Function.update_self] using htail
  by_cases hi151 : i = 151
  · subst i
    simpa only [FactorAssignmentLoop.state, Function.update_of_ne (by decide : (151 : Fin 896) ≠ 149),
      Function.update_of_ne (by decide : (151 : Fin 896) ≠ 150), Function.update_self] using hs
  rw [loop_state_frame _ _ _ _ _ i hi149 hi150 hi151]
  exact ha i

variable {r Q n d P M S : ℕ} {q : Factor.Spec r Q n d}
  {one : FactorAssignmentLoop.Raw n (baseWidth 3 q.p.t) d}
  {a : FactorAssignmentProgram.Data}

theorem Ready.input (h : Ready q P S one a)
    (regs : Fin 40 → Bool) (seed : FactorAssignmentLoop.Raw n (baseWidth 3 q.p.t) d)
    (tail : List Bool) (f : ℕ) (hseed : NativeSemantics.Good ∅ q.u q.J seed)
    (htail : tail.length ≤ P) (hf : f+1 ≤ P) :
    FactorAssignmentCallback.Input q P S one seed
      (FactorAssignmentLoop.state a.stacks regs seed tail (Encoding.encodeNat f).reverse) f := by
  let b := FactorAssignmentLoop.state a.stacks regs seed tail (Encoding.encodeNat f).reverse
  have frame (i : Fin 896) (h149 : i ≠ 149) (h150 : i ≠ 150) (h151 : i ≠ 151) :
      b.stacks i = a.stacks i := loop_state_frame _ _ _ _ _ i h149 h150 h151
  have localFrame (i : Fin 768)
      (hi : i ∈ scalarPorts ∨ i ∈ sourcePorts) :
      (projectState localRegister FactorTableProgram.basePort b).stacks i =
        (projectState localRegister FactorTableProgram.basePort a).stacks i := by
    have hn := (List.forall_iff_forall_mem.mp (by decide) : ∀ i ∈ scalarPorts ++ sourcePorts,
      FactorTableProgram.basePort i ≠ 149 ∧ FactorTableProgram.basePort i ≠ 150 ∧
      FactorTableProgram.basePort i ≠ 151) i (List.mem_append.mpr hi)
    exact frame _ hn.1 hn.2.1 hn.2.2
  refine ⟨scalar_frame h.scalar (fun i hi => localFrame i (Or.inl hi)),
    source_frame h.masters (fun i hi => localFrame i (Or.inr hi)),
    loop_state_bound a regs seed tail f h.incoming hseed h.seedFits htail hf,
    h.size,h.radius,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (frame 701 (by decide) (by decide) (by decide)).trans h.rows
  · exact (frame 700 (by decide) (by decide) (by decide)).trans h.clauses
  · exact (frame 704 (by decide) (by decide) (by decide)).trans h.count
  · exact (frame 705 (by decide) (by decide) (by decide)).trans h.mark
  · exact (frame 706 (by decide) (by decide) (by decide)).trans h.flag
  · simp only [FactorAssignmentLoop.state, Function.update_self]
  · simp only [FactorAssignmentLoop.state,
      Function.update_of_ne (by decide : (151 : Fin 896) ≠ 149),
      Function.update_of_ne (by decide : (151 : Fin 896) ≠ 150), Function.update_self]
  · intro i hi
    have hn := (List.forall_iff_forall_mem.mp (by decide) : ∀ i ∈ callbackScratch,
      lowStack i ≠ 149 ∧ lowStack i ≠ 150 ∧ lowStack i ≠ 151) i hi
    exact (frame _ hn.1 hn.2.1 hn.2.2).trans (h.blank i hi)
  · intro i hi h62 h556
    have ne (j : Fin 896) (hj : j.val < 340 ∧ j ≠ 62) : i ≠ j := by
      intro he
      subst i
      exact FactorTableSpace.caller_port_not_written j (Or.inl hj) hi
    exact (frame i (ne 149 (by decide)) (ne 150 (by decide))
      (ne 151 (by decide))).trans (h.tableBlank i hi h62 h556)
  · rw [frame 857 (by decide) (by decide) (by decide)]; exact h.correction
  · rw [frame 708 (by decide) (by decide) (by decide)]; exact h.hashWidth
  · rw [frame 707 (by decide) (by decide) (by decide)]; exact h.hashModulus
  · rw [frame 280 (by decide) (by decide) (by decide)]; exact h.ringShape
  · intro i
    have hn : lowStack (Factor.nativeStacks (Memory.lowPort i)) ≠ 149 ∧
        lowStack (Factor.nativeStacks (Memory.lowPort i)) ≠ 150 ∧
        lowStack (Factor.nativeStacks (Memory.lowPort i)) ≠ 151 := by
      have hi := i.isLt
      have hv : (lowStack (Factor.nativeStacks (Memory.lowPort i))).val = i.val := rfl
      constructor
      · intro he
        have hh := congrArg Fin.val he
        rw [hv] at hh
        norm_num at hh
        omega
      constructor
      · intro he
        have hh := congrArg Fin.val he
        rw [hv] at hh
        norm_num at hh
        omega
      · intro he
        have hh := congrArg Fin.val he
        rw [hv] at hh
        norm_num at hh
        omega
    exact (frame _ hn.1 hn.2.1 hn.2.2).trans (h.low i)
  · exact (frame 69 (by decide) (by decide) (by decide)).trans h.oneBytes
  · exact (frame 76 (by decide) (by decide) (by decide)).trans h.minusBytes
  · exact (frame 143 (by decide) (by decide) (by decide)).trans h.tape
  · rw [frame 88 (by decide) (by decide) (by decide)]; exact h.shape
  · exact (frame 63 (by decide) (by decide) (by decide)).trans h.clauseOutput
  · intro i hi
    have hn := (List.forall_iff_forall_mem.mp (by decide) : ∀ i ∈ FactorServices.clauseScratch,
      lowStack (Clause.callerStacks i) ≠ 149 ∧ lowStack (Clause.callerStacks i) ≠ 150 ∧
      lowStack (Clause.callerStacks i) ≠ 151) i hi
    exact (frame _ hn.1 hn.2.1 hn.2.2).trans (h.clauseWork i hi)


/-- The running record ports are disjoint from all three assignment masters.
Thus every factor value is read from the same actual accepted assignment. -/
theorem loop_value (a : FactorAssignmentProgram.Data) (regs : Fin 40 → Bool)
    (seed : FactorAssignmentLoop.Raw n (baseWidth 3 q.p.t) d)
    (tail payload : List Bool) (f : ℕ) :
    q.value ((FactorAssignmentLoop.state a.stacks regs seed tail payload).stacks ∘ lowStack) f =
      q.value (a.stacks ∘ lowStack) f := by
  have hj (j : ℕ) : Factor.factorJet q.p q.ps q.packing n f j q.theta
      ((FactorAssignmentLoop.state a.stacks regs seed tail payload).stacks ∘ lowStack) =
      Factor.factorJet q.p q.ps q.packing n f j q.theta (a.stacks ∘ lowStack) := by
    apply Factor.factorJet_frame
    all_goals exact loop_state_frame _ _ _ _ _ _ (by decide) (by decide) (by decide)
  unfold Factor.Spec.value Factor.Semantics.hashValue Factor.Semantics.markedValue
  simp_rw [hj]

/-- The actual prepared store instantiates the callback used by the record
fold. The output witness, polynomial cost, exact frame and semantic product
all refer to this one fixed callback run. -/
theorem Ready.callback_eval (h : Ready q P S one a)
    (hone : NativeSemantics.Good ∅ q.u q.J one)
    (honeval : TruncatedRingProgram.rawDenote q.p.ops.decode one =
      Squarefree.canonical q.u q.J 1)
    (regs : Fin 40 → Bool) (seed : FactorAssignmentLoop.Raw n (baseWidth 3 q.p.t) d)
    (tail : List Bool) (f width Z : ℕ)
    (hseed : NativeSemantics.Good ∅ q.u q.J seed)
    (htail : tail.length ≤ P) (hf : f+1 ≤ P)
    (hwidth : ∀ hi : f < q.rows.length,
      ∀ w ∈ HashInputProgram.Expansion.weightedRow q.p.t d q.source q.rows[f],
        w.literals.length ≤ width)
    (hZ : 1 ≤ Z) (hP : P ≤ Z) (hbit : q.bitWidth ≤ Z)
    (hshape : d*baseWidth 3 q.p.t ≤ Z)
    (hhashScale : ∀ hi : f < q.rows.length,
      FactorEvaluationSpace.inputScale (baseWidth 3 q.p.t) d n q.u q.J
        width q.rows[f].length q.digits.length ≤ Z)
    (hmarkScale : FactorEvaluationSpace.inputScale (baseWidth 3 q.p.t) d n q.u q.J
      q.markedClause.length 0 0 ≤ Z) :
    ∃ out : FactorAssignmentLoop.Raw n (baseWidth 3 q.p.t) d,
      NativeSemantics.Good ∅ q.u q.J out ∧
      TruncatedRingProgram.rawValue q.u q.J q.p.ops.decode out =
        TruncatedRingProgram.rawValue q.u q.J q.p.ops.decode seed *
          QueryEvaluation.specializeDense q.u q.J
            (fun v => decide (v ∈ Squarefree.decodeMask n (a.stacks 857)))
            (q.value (a.stacks ∘ lowStack) f) ∧
      ∃ steps ≤ FactorAssignmentCallback.uniformCallbackBudget q P S Z, ∃ rr,
        Eval FactorAssignmentProgram.callback steps
          (FactorAssignmentLoop.state a.stacks regs seed tail (Encoding.encodeNat f).reverse)
          (FactorAssignmentLoop.state a.stacks rr out tail []) ∧
        rr 13 = false ∧ rr 14 = true ∧ rr 15 = false := by
  let b := FactorAssignmentLoop.state a.stacks regs seed tail (Encoding.encodeNat f).reverse
  have hi := h.input regs seed tail f hseed htail hf
  obtain ⟨out,rf,steps,z,hout,hvalue,hsteps,he,hframe,h13,h14,h15⟩ :=
    FactorAssignmentCallback.callback_eval_correct hi hone hseed honeval width hwidth
  have hcost := FactorAssignmentCallback.callbackBudget_le hi width Z hZ hP hbit
    hshape hhashScale hmarkScale rf
  have heq := FactorAssignmentCallback.result_eq_state a.stacks regs seed out tail
    (Encoding.encodeNat f).reverse z hframe
  refine ⟨out,hout,?_,steps,hsteps.trans hcost,z.regs,?_,h13,h14,h15⟩
  · have hmask : b.stacks 857 = a.stacks 857 :=
      loop_state_frame _ _ _ _ _ 857 (by decide) (by decide) (by decide)
    have hvalueFrame : q.value (b.stacks ∘ lowStack) f = q.value (a.stacks ∘ lowStack) f :=
      loop_value a regs seed tail (Encoding.encodeNat f).reverse f
    calc
      TruncatedRingProgram.rawValue q.u q.J q.p.ops.decode out =
          TruncatedRingProgram.rawValue q.u q.J q.p.ops.decode seed *
            QueryEvaluation.specializeDense q.u q.J
              (fun v => decide (v ∈ Squarefree.decodeMask n (b.stacks 857)))
              (q.value (b.stacks ∘ lowStack) f) := hvalue
      _ = TruncatedRingProgram.rawValue q.u q.J q.p.ops.decode seed *
            QueryEvaluation.specializeDense q.u q.J
              (fun v => decide (v ∈ Squarefree.decodeMask n (a.stacks 857)))
              (q.value (a.stacks ∘ lowStack) f) := by rw [hmask, hvalueFrame]
  · rw [heq] at he
    exact he

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBoundary
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorAssignmentCorrect
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual initializer, source-context cache, dispatcher, specialized
incidence producer and factor arithmetic instantiate the stored-ID fold.
The output is the entire specialized coefficient-ring product on stack854.
Every resource assertion below concerns this same fixed command. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCorrect

open OAI BitProgram StructuredCalls SubexpSetupStorage
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram MomentsProgram
open OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open FactorAssignmentProgram FactorAssignmentBoundary FactorAssignmentLoop

noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

variable {r Q n d P M S : ℕ} {q : Factor.Spec r Q n d}

/-- The prepared machine runs the concrete factor callback for every stored
ID. Neutral IDs and the empty list retain the actual stored identity. -/
theorem prepared_product_eval_correct_oai
    {a : FactorAssignmentProgram.Data}
    {one : Raw n (baseWidth 3 q.p.t) d}
    (h : Ready q P S one a) (ids : List ℕ)
    (hone : NativeSemantics.Good ∅ q.u q.J one)
    (honeval : TruncatedRingProgram.rawDenote q.p.ops.decode one =
      Squarefree.canonical q.u q.J 1)
    (honedense : TruncatedRingProgram.rawValue q.u q.J q.p.ops.decode one = 1)
    (hids : a.stacks 175 = ProgramEncoding.encodeRecords (records ids))
    (hblank : ∀ i ∈ ([149,150,151,159,854] : List (Fin 896)), a.stacks i = [])
    (width Z : ℕ)
    (hwidth : ∀ f (hf : f < q.rows.length),
      ∀ w ∈ HashInputProgram.Expansion.weightedRow q.p.t d q.source q.rows[f],
        w.literals.length ≤ width)
    (hZ : 1 ≤ Z) (hP : P ≤ Z) (hbit : q.bitWidth ≤ Z)
    (hshape : d * baseWidth 3 q.p.t ≤ Z)
    (hhashScale : ∀ f (hf : f < q.rows.length),
      FactorEvaluationSpace.inputScale (baseWidth 3 q.p.t) d n q.u q.J
        width q.rows[f].length q.digits.length ≤ Z)
    (hmarkScale : FactorEvaluationSpace.inputScale (baseWidth 3 q.p.t) d n q.u q.J
      q.markedClause.length 0 0 ≤ Z) :
    ∃ (out : Raw n (baseWidth 3 q.p.t) d) (steps : ℕ) (b : FactorAssignmentProgram.Data), NativeSemantics.Good ∅ q.u q.J out ∧
      TruncatedRingProgram.rawValue q.u q.J q.p.ops.decode out =
        (ids.map (fun f => QueryEvaluation.specializeDense q.u q.J
          (fun v => decide (v ∈ Squarefree.decodeMask n (a.stacks 857)))
          (q.value (a.stacks ∘ lowStack) f))).prod ∧
      steps ≤ uniformProductBudget n (baseWidth 3 q.p.t) d q.u q.J P
        (FactorAssignmentCallback.uniformCallbackBudget q P S Z) ∧
      Eval product steps a b ∧
      b.stacks = Function.update a.stacks 854 (Product.bytes out) ∧
      WordBound P b := by
  let value := fun f => QueryEvaluation.specializeDense q.u q.J
    (fun v => decide (v ∈ Squarefree.decodeMask n (a.stacks 857)))
    (q.value (a.stacks ∘ lowStack) f)
  let decode := TruncatedRingProgram.rawValue (n := n) q.u q.J q.p.ops.decode
  let step := fun seed f out => decode out = decode seed * value f
  have hlen : (ProgramEncoding.encodeRecords (records ids)).length ≤ P := by
    rw [← hids]
    exact h.incoming 175
  have hidLength (f : ℕ) (hf : f ∈ ids) : f + 1 ≤ P := by
    have hb := HashInputProgram.Loop.original_payload_length_le (records ids)
      (Encoding.encodeNat f) (List.mem_map.mpr ⟨f,hf,rfl⟩)
    simpa only [Encoding.length_encodeNat] using hb.trans hlen
  obtain ⟨out,hout,hfold,k,hk,rr,he⟩ := product_eval q.u q.J step
    (fun base => base = a.stacks) (fun f => f ∈ ids) P
    (FactorAssignmentCallback.uniformCallbackBudget q P S Z)
    (by
      intro base hb f seed tail regs hf hseed htail
      subst base
      exact h.callback_eval hone honeval regs seed tail f width Z hseed htail
        (hidLength f hf) (hwidth f) hZ hP hbit hshape (hhashScale f) hmarkScale)
    a rfl ids one hone (fun _ hi => hi) hlen hids h.oneBytes
    (hblank 149 (by decide)) (hblank 150 (by decide)) (hblank 151 (by decide))
    (hblank 854 (by decide)) (hblank 159 (by decide))
  refine ⟨out,k,⟨rr,Function.update a.stacks 854 (Product.bytes out)⟩,hout,?_,
    hk.trans (productBudget_le _ _ _ _ _ _ _ ids hlen),he,rfl,?_⟩
  · exact foldRel_product decode value step (fun _ _ _ hs => hs) hfold honedense
  · exact product_return_bound a _ out rfl h.incoming hout h.seedFits

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCorrect
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCorrect.prepared_product_eval_correct_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCorrect.prepared_product_eval_correct_oai
