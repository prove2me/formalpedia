-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.specializeCall_run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T11:04:35.968984+00:00
-- url     : https://prove2.me/submissions/b3fed2d7-0373-4376-8df2-944c4eff254a

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S188
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryProducerSpace_low_run_space
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryProducerSpace_run_space
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_StructuredSpace_local_stack_bound

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryProducerSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Immediate Boolean specialization followed by the actual additive dictionary
normalizer. The input is a polynomial-size origin/singleton incidence stream;
no multivariate product is materialized before specialization. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open MomentsProgram TruncatedRingProgram
open scoped BigOperators

theorem escaped_append (a b : List Bool) : escaped (a ++ b) = escaped a ++ escaped b := by
  induction a with
  | nil => rfl
  | cons bit bits ih => simp [escaped, ih]

theorem escaped_frame (bits : List Bool) : escaped bits ++ [false] = Encoding.frame bits := by
  induction bits with
  | nil => rfl
  | cons bit bits ih => simp [escaped, Encoding.frame, ih]

theorem frameBody_eval (regs : Fin 8 → Bool)
    (modulus width degree output : List Bool) (bit : Bool) (bits : List Bool) :
    ∃ rr, StructuredProgram.Eval frameBody 5
      (frameData regs modulus width degree (bit :: bits) output)
      (frameReady rr modulus width degree bits (true :: bit :: output)) := by
  let a := frameData regs modulus width degree (bit :: bits) output
  let b := (StructuredProgram.Atom.pop 35 0 1).eval a
  let c := (StructuredProgram.Atom.push 28 0).eval b
  let d := (StructuredProgram.Atom.set 0 true).eval c
  let e := (StructuredProgram.Atom.push 28 0).eval d
  have he := (StructuredProgram.Eval.atom (.pop 35 0 1) a).seq
    ((StructuredProgram.Eval.atom (.push 28 0) b).seq
    ((StructuredProgram.Eval.atom (.set 0 true) c).seq
    ((StructuredProgram.Eval.atom (.push 28 0) d).seq
      (StructuredProgram.Eval.atom (.peek 35 0 1) e))))
  refine ⟨e.regs, ?_⟩
  unfold frameBody
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  apply SubexpScanPrimitives.state_ext
  · rfl
  · funext i
    fin_cases i <;> rfl

theorem frameLoop_eval (bits output : List Bool) (regs : Fin 8 → Bool)
    (modulus width degree : List Bool) :
    ∃ rr, StructuredProgram.Eval frameLoop (6 * bits.length + 1)
      (frameReady regs modulus width degree bits output)
      (frameData rr modulus width degree [] (escaped bits.reverse ++ output)) := by
  induction bits generalizing output regs with
  | nil =>
    refine ⟨readRegs regs 0 1 none, ?_⟩
    exact StructuredProgram.Eval.while_false (by simp [frameReady, frameData, state, readRegs])
  | cons bit bits ih =>
    obtain ⟨rb, hb⟩ := frameBody_eval (readRegs regs 0 1 (some bit))
      modulus width degree output bit bits
    obtain ⟨rr, hr⟩ := ih (true :: bit :: output) rb
    have he := StructuredProgram.Eval.while_true (body := frameBody)
      (by simp [frameReady, frameData, state, readRegs] :
        (frameReady regs modulus width degree (bit :: bits) output).regs 1 = true) hb hr
    refine ⟨rr, ?_⟩
    unfold frameLoop
    convert he using 1
    · simp only [List.length_cons]
      omega
    · simp [escaped_append, escaped, List.append_assoc]

theorem framer_eval (bits output : List Bool) (regs : Fin 8 → Bool)
    (modulus width degree : List Bool) :
    ∃ rr, StructuredProgram.Eval framer (6 * bits.length + 4)
      (frameData regs modulus width degree bits output)
      (frameData rr modulus width degree [] (Encoding.frame bits.reverse ++ output)) := by
  let a := frameData regs modulus width degree bits output
  let b := (StructuredProgram.Atom.set 0 false).eval a
  let c := (StructuredProgram.Atom.push 28 0).eval b
  have hp := StructuredProgram.Eval.atom (.peek 35 0 1) c
  have hc : (StructuredProgram.Atom.peek 35 0 1).eval c =
      frameReady c.regs modulus width degree bits (false :: output) := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · funext i
      fin_cases i <;> rfl
  rw [hc] at hp
  obtain ⟨rr, hr⟩ := frameLoop_eval bits (false :: output) c.regs modulus width degree
  have he := (StructuredProgram.Eval.atom (.set 0 false) a).seq
    ((StructuredProgram.Eval.atom (.push 28 0) b).seq (hp.seq hr))
  refine ⟨rr, ?_⟩
  unfold framer
  convert he using 1
  · omega
  · rw [← escaped_frame]
    simp [frameData, List.append_assoc]

theorem prepare_eval (regs : Fin 8 → Bool) (modulus width degree mask raw : List Bool) :
    ∃ rr, Eval prepare (9 * mask.length + 7)
      (state regs modulus width degree [] [] {input := raw, target := mask})
      (state rr modulus width degree [] [] {input := Encoding.frame mask ++ raw}) := by
  let a := state regs modulus width degree [] [] {input := raw, target := mask}
  have ht := SubexpScanPrimitives.transfer_eval a 29 35 0 1 (by decide) (by decide)
  have hb : SubexpScanPrimitives.afterTransfer a 29 35 0 1 =
      frameData (readRegs regs 0 1 none) modulus width degree mask.reverse raw := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · funext i
      fin_cases i <;> first | rfl |
        simp [SubexpScanPrimitives.afterTransfer, StackRoutines.transferStacks, a,
          frameData, state, MomentsProjectionProgram.tapes, Fin.addCases, Fin.coe_ofNat_eq_mod]
  rw [hb] at ht
  obtain ⟨rr, hr⟩ := framer_eval mask.reverse raw (readRegs regs 0 1 none)
    modulus width degree
  refine ⟨rr, ?_⟩
  have he := ht.seq (Eval.base hr)
  unfold prepare
  convert he using 1
  · change 9 * mask.length + 7 = 3 * mask.length + 3 + (6 * mask.reverse.length + 4)
    simp only [List.length_reverse]
    omega
  · unfold frameData
    simp only [List.reverse_reverse]

/-- No serialized correction prefix is assumed: its bytes are produced on this
same run from the separate ambient mask, and all framing steps are charged. -/
theorem prepared_run_space (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d u J N : ℕ} (U : Finset (Fin n))
    (source : List (Product.Entry n (baseWidth p t) d))
    (hsource : ∀ a ∈ source, Product.ValidKey Finset.univ u J a.1)
    (hN : source.length ≤ N) (regs : Fin 8 → Bool) (width degree : List Bool)
    (hd : degree.length = d) (hw : width.length = baseWidth p t) :
    let result := Normalize.run p t M cache (HeadEvaluation.specializeEntries U source) []
    let start := state regs M.bits width degree [] []
      {input := Product.bytes source, target := Squarefree.encodeMask U}
    ∃ steps rr, steps ≤ preparedBudget n (baseWidth p t) d u J N (Product.bytes source).length ∧
      Trace preparedProgram steps (start.withPC (some preparedProgram.entry))
        ((state rr M.bits width degree (Product.bytes result) []
          {target := (Squarefree.encodeMask U).reverse}).withPC none) ∧
      Good ∅ u J result ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace preparedProgram prefixSteps (start.withPC (some preparedProgram.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ stackBits start.stacks +
          preparedBudget n (baseWidth p t) d u J N (Product.bytes source).length := by
  dsimp only
  obtain ⟨readyRegs, hprepare⟩ := prepare_eval regs M.bits width degree
    (Squarefree.encodeMask U) (Product.bytes source)
  obtain ⟨steps, rr, hsteps, hrun, hgood, _⟩ := run_space p t M cache U source
    hsource hN readyRegs width degree hd hw
  have he := hprepare.seq (Eval.call program hrun)
  have hbound : 9 * (Squarefree.encodeMask U).length + 7 + steps + 1 ≤
      preparedBudget n (baseWidth p t) d u J N (Product.bytes source).length := by
    simp only [Squarefree.encodeMask_length]
    unfold preparedBudget
    omega
  refine ⟨_, rr, hbound, ?_, hgood, ?_⟩
  · exact compiled_halt_trace he 28 15
  · intro prefixSteps intermediate hp ht i
    exact StructuredSpace.local_stack_bound preparedProgram
      (steps := preparedBudget n (baseWidth p t) d u J N (Product.bytes source).length)
      (by rfl) prefixSteps intermediate (hp.trans hbound) ht i

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryIncidenceCommand
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed native incidence command and its physical port ABI. The definitions
are extracted unchanged from the same emitter-specializer composition. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace
open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog MomentsProgram
open SubexpScanPrimitives SubexpSetupStorage

namespace Native

theorem lowPorts_injective : Function.Injective lowPorts := Fin.castAdd_injective _ _

theorem producerPorts_injective : Function.Injective producerPorts := by
  intro i j h
  exact Fin.ext (Nat.add_left_cancel (congrArg Fin.val h))

theorem producerRegisters_injective : Function.Injective producerRegisters :=
  Fin.castAdd_injective _ _

end Native
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace
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

theorem joinedPort_injective : Function.Injective joinedPort := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [joinedPort] at this
  omega

theorem emptyHigh_update (mask : List Bool) :
    QueryProducerSpace.Native.emptyHigh mask =
      Function.update (QueryProducerSpace.Native.emptyHigh []) 29 mask := by
  first | done | (funext i; fin_cases i <;> rfl)

theorem joinedState_update_mask (regs : Fin 16 → Bool) (low : Fin 256 → List Bool)
    (mask : List Bool) :
    (QueryProducerSpace.Native.joinedState regs low
      (QueryProducerSpace.Native.emptyHigh mask)).stacks =
      Function.update (QueryProducerSpace.Native.joinedState regs low
        (QueryProducerSpace.Native.emptyHigh [])).stacks 285 mask := by
  funext i
  refine Fin.addCases (m := 256) (n := 38) (fun j => ?_) (fun j => ?_) i
  · have hn : (j.castAdd 38 : Fin 294) ≠ 285 := by
      intro h
      have hv := congrArg Fin.val h
      have hj := j.isLt
      simp only [Fin.val_castAdd, Fin.coe_ofNat_eq_mod] at hv
      omega
    simp [QueryProducerSpace.Native.joinedState, hn]
  · rw [emptyHigh_update]
    by_cases hj : j = 29
    · subst j
      change (QueryProducerSpace.Native.joinedState regs low
        (Function.update (QueryProducerSpace.Native.emptyHigh []) 29 mask)).stacks
        (QueryProducerSpace.Native.producerPorts 29) = mask
      rw [QueryProducerSpace.Native.joinedState_high, Function.update_self]
    · have hn : (Fin.natAdd 256 j : Fin 294) ≠ 285 := by
        intro h
        have hv := congrArg Fin.val h
        simp only [Fin.val_natAdd, Fin.coe_ofNat_eq_mod] at hv
        apply hj
        apply Fin.ext
        simp only [Fin.coe_ofNat_eq_mod]
        omega
      simp [QueryProducerSpace.Native.joinedState, hj, hn]

theorem copied_joined_shape (a : OuterData) (low : Fin 256 → List Bool)
    (hs : ∀ i, a.stacks (joinedPort i) =
      (QueryProducerSpace.Native.joinedState a.regs low
        (QueryProducerSpace.Native.emptyHigh [])).stacks i) :
    projectState id joinedPort (SubexpSetupStorage.copyState 857 625 a) =
      QueryProducerSpace.Native.joinedState
        (SubexpSetupStorage.copyState 857 625 a).regs low
        (QueryProducerSpace.Native.emptyHigh (a.stacks 857)) := by
  apply state_ext
  · rfl
  · rw [joinedState_update_mask]
    funext i
    by_cases hi : i = 285
    · subst i
      have hz : a.stacks 625 = [] := hs 285
      simp [projectState, SubexpSetupStorage.copyState, StackRoutines.copyStacks, joinedPort, Fin.coe_ofNat_eq_mod, hz]
    · have hn : joinedPort i ≠ 625 := by
        intro h
        apply hi
        apply joinedPort_injective
        exact h
      simp only [projectState, SubexpSetupStorage.copyState, StackRoutines.copyStacks,
        Function.comp_apply, Function.update_of_ne hn, Function.update_of_ne hi]
      exact hs i

theorem joinedState_update_low (regs : Fin 16 → Bool) (low : Fin 256 → List Bool)
    (high : Fin 38 → List Bool) (word : List Bool) :
    (QueryProducerSpace.Native.joinedState regs (Function.update low 217 word) high).stacks =
      Function.update (QueryProducerSpace.Native.joinedState regs low high).stacks 217 word := by
  funext i
  refine Fin.addCases (m := 256) (n := 38) (fun j => ?_) (fun j => ?_) i
  · by_cases hj : j = 217
    · subst j; rfl
    · have hn : (j.castAdd 38 : Fin 294) ≠ 217 := by
        intro h
        apply hj
        have hv := congrArg (fun x : Fin 294 => x.val) h
        exact Fin.ext hv
      simp [QueryProducerSpace.Native.joinedState, hj, hn]
  · have hn : (Fin.natAdd 256 j : Fin 294) ≠ 217 := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_natAdd, Fin.coe_ofNat_eq_mod] at hv
      omega
    simp [QueryProducerSpace.Native.joinedState, hn]

/-- The producer reclaims its copied mask and all high scratch. Exactly its
specialized low output replaces caller557; every other caller word returns. -/
theorem specialized_joined_output (a : OuterData) (low : Fin 256 → List Bool)
    (rr : Fin 16 → Bool) (word : List Bool)
    (hs : ∀ i, a.stacks (joinedPort i) =
      (QueryProducerSpace.Native.joinedState a.regs low
        (QueryProducerSpace.Native.emptyHigh [])).stacks i) :
    embedState id joinedPort (SubexpSetupStorage.copyState 857 625 a)
      (QueryProducerSpace.Native.joinedState rr (Function.update low 217 word)
        (QueryProducerSpace.Native.emptyHigh [])) =
      (⟨rr, Function.update a.stacks 557 word⟩ : OuterData) := by
  apply embedState_eq_of_ports id joinedPort _ _ _ Function.injective_id joinedPort_injective
  · intro i; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i
    change Function.update a.stacks 557 word (joinedPort i) = _
    rw [joinedState_update_low]
    by_cases hi : i = 217
    · subst i; rfl
    · have hn : joinedPort i ≠ 557 := by
        intro h
        apply hi
        apply joinedPort_injective
        exact h
      simp only [Function.update_of_ne hn, Function.update_of_ne hi]
      exact hs i
  · intro i hi
    have h557 : i ≠ 557 := by
      intro h
      subst i
      exact hi ⟨217, rfl⟩
    have h625 : i ≠ 625 := by
      intro h
      subst i
      exact hi ⟨285, rfl⟩
    simp [SubexpSetupStorage.copyState, StackRoutines.copyStacks, h557, h625]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryIncidenceSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open MomentsProgram TruncatedRingProgram
open scoped BigOperators

noncomputable section
variable {R : Type*} [CommRing R]

/-- Each emitted incidence stream has only one constant record and one row of
positive Taylor coefficients per ambient coordinate. This is polynomial storage
before specialization, independently of the support-universe cardinality. -/
theorem incidence_entries_length {n B d : ℕ}
    (ops : SubexpSymbolicCost.RingProgram (RingProgram.Code (Word B) d))
    (J : ℕ) (theta beta : RingProgram.Code (Word B) d)
    (rows : Fin n → List (RingProgram.Code (Word B) d)) :
    (PerturbationAssembly.outputWords ops J theta beta rows).length =
      1 + n * (J - 1) := by
  have htail (v : Fin n) :
      (PerturbationAssembly.shiftedValue ops J theta (rows v)).val.tail.length = J - 1 := by
    rw [List.length_tail, (PerturbationAssembly.shiftedValue ops J theta (rows v)).property]
  simp [PerturbationAssembly.outputWords, PerturbationAssembly.rawWords,
    List.length_flatten, List.map_ofFn, List.sum_ofFn, htail, Nat.add_comm]


/-- The emitted dictionary has the same bounded keys as its decoded source;
this premise is obtained from the actual incidence constructor. -/
theorem incidence_valid {n B d : ℕ}
    (ops : SubexpSymbolicCost.RepresentedRing (RingProgram.Code (Word B) d) R)
    (u J : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (theta beta : RingProgram.Code (Word B) d)
    (rows : Fin n → List (RingProgram.Code (Word B) d)) :
    ∀ a ∈ PerturbationAssembly.outputWords ops.program J theta beta rows,
      Product.ValidKey Finset.univ u J a.1 := by
  intro a ha
  apply PerturbationAssembly.outputWords_valid ops u J hu hJ theta beta rows a.1
  simp only [Squarefree.Sparse.keys, PerturbationProgram.decodeRecords,
    List.map_map, Function.comp_def]
  exact List.mem_map.mpr ⟨a, ha, rfl⟩

end


namespace Native

open SubexpScanPrimitives SubexpSetupStorage

theorem loadPairs_valid : ∀ p ∈ loadPairs,
    p.1 ≠ p.2 ∧ p.1 ≠ 292 ∧ (292 : Fin 294) ≠ p.2 := by
  intro p hp
  simp only [loadPairs, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> decide

theorem load_eval (regs : Fin 16 → Bool) (low : Fin 256 → List Bool) (mask : List Bool) :
    Eval loadCommand (7 * ((low 194).length + (low 202).length + (low 204).length) +
      6 * (low 217).length + 21)
      (joinedState regs low (emptyHigh mask)) (loaded (joinedState regs low (emptyHigh mask))) := by
  let a := joinedState regs low (emptyHigh mask)
  let b := copyManyState loadPairs a
  let c := afterTransfer b 217 292 0 1
  have hcopy := copyMany_eval 292 loadPairs a loadPairs_valid (by rfl)
  have hfirst := SubexpScanPrimitives.transfer_eval b 217 292 0 1 (by decide) (by decide)
  have hsecond := SubexpScanPrimitives.transfer_eval c 292 284 0 1 (by decide) (by decide)
  have he := hcopy.seq (hfirst.seq hsecond)
  unfold loadCommand loaded
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  change 7 * ((low 194).length + (low 202).length + (low 204).length) +
      6 * (low 217).length + 21 =
    (7 * (low 194).length + 5 + (7 * (low 202).length + 5 +
      (7 * (low 204).length + 5 + 0))) +
      (3 * (low 217).length + 3 + (3 * ((low 217).reverse ++ []).length + 3))
  simp only [List.length_append, List.length_reverse, List.length_nil]
  omega

theorem loaded_high (regs : Fin 16 → Bool) (low : Fin 256 → List Bool) (mask : List Bool)
    (i : Fin 38) :
    (loaded (joinedState regs low (emptyHigh mask))).stacks (producerPorts i) =
      (state (fun _ => false) (low 194) (low 202) (low 204) [] []
        {input := low 217, target := mask}).stacks i := by
  fin_cases i <;> first
    | rfl
    | (change low 194 ++ [] = low 194; exact List.append_nil _)
    | (change low 202 ++ [] = low 202; exact List.append_nil _)
    | (change low 204 ++ [] = low 204; exact List.append_nil _)
    | (change ((low 217).reverse ++ []).reverse ++ [] = low 217; simp)

theorem loaded_low (regs : Fin 16 → Bool) (low : Fin 256 → List Bool) (mask : List Bool)
    (i : Fin 256) :
    (loaded (joinedState regs low (emptyHigh mask))).stacks (lowPorts i) =
      (Function.update low 217 []) i := by
  have hi : (lowPorts i).val < 256 := i.isLt
  have h261 : lowPorts i ≠ 261 := by intro h; have := congrArg Fin.val h; omega
  have h268 : lowPorts i ≠ 268 := by intro h; have := congrArg Fin.val h; omega
  have h280 : lowPorts i ≠ 280 := by intro h; have := congrArg Fin.val h; omega
  have h284 : lowPorts i ≠ 284 := by intro h; have := congrArg Fin.val h; omega
  have h292 : lowPorts i ≠ 292 := by intro h; have := congrArg Fin.val h; omega
  by_cases h217 : i = 217
  · subst i
    rfl
  · have h217' : lowPorts i ≠ 217 := by
      intro h
      apply h217
      apply Fin.ext
      have hv := congrArg Fin.val h
      simpa [lowPorts] using hv
    simp [loaded, loadPairs, copyManyState, copyState, afterTransfer,
      StackRoutines.copyStacks, StackRoutines.transferStacks,
      h261, h268, h280, h284, h292, h217', h217]

theorem embed_low (regs rr : Fin 16 → Bool) (low low' : Fin 256 → List Bool)
    (high : Fin 38 → List Bool) :
    embedState id lowPorts (joinedState regs low high) ⟨rr, low'⟩ = joinedState rr low' high := by
  apply SubexpScanPrimitives.embedState_eq _ _ Function.injective_id lowPorts_injective
  · intro i; rfl
  · intro i; simp [joinedState, lowPorts]
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i hi
    have hge : 256 ≤ i.val := by
      by_contra h
      apply hi
      exact ⟨⟨i.val, by omega⟩, Fin.ext rfl⟩
    let j : Fin 38 := ⟨i.val - 256, by omega⟩
    have hj : producerPorts j = i := by
      apply Fin.ext
      simp only [producerPorts, Fin.val_natAdd, j]
      omega
    rw [← hj]
    simp [joinedState, producerPorts]


theorem embed_loaded (regs : Fin 16 → Bool) (low : Fin 256 → List Bool) (mask : List Bool) :
    let a := loaded (joinedState regs low (emptyHigh mask))
    embedState producerRegisters producerPorts a
      (state (a.regs ∘ producerRegisters) (low 194) (low 202) (low 204) [] []
        {input := low 217, target := mask}) = a := by
  dsimp only
  apply SubexpScanPrimitives.embedState_eq _ _ producerRegisters_injective producerPorts_injective
  · intro i; rfl
  · exact loaded_high regs low mask
  · intro i hi; rfl
  · intro i hi; rfl

theorem highPorts_mem (i : Fin 294) : i ∈ highPorts ↔ 256 ≤ i.val := by
  simp only [highPorts, List.mem_map, List.mem_finRange, true_and]
  constructor
  · rintro ⟨j, rfl⟩
    simp [producerPorts]
  · intro hi
    refine ⟨⟨i.val - 256, by omega⟩, ?_⟩
    apply Fin.ext
    simp only [producerPorts, Fin.val_natAdd]
    omega

theorem finish_eval (a : State 16 294) (hscratch : a.stacks 292 = []) :
    Eval finishCommand (6 * (a.stacks 271).length + 6 + clearManyCost highPorts (movedOutput a))
      a (finished a) := by
  have h1 := SubexpScanPrimitives.transfer_eval a 271 292 0 1 (by decide) (by decide)
  have h2 := SubexpScanPrimitives.transfer_eval (afterTransfer a 271 292 0 1)
    292 217 0 1 (by decide) (by decide)
  have ho : Eval outputMove (6 * (a.stacks 271).length + 6) a (movedOutput a) := by
    unfold outputMove movedOutput
    convert h1.seq h2 using 1
    all_goals try with_reducible_and_instances rfl
    simp [afterTransfer, StackRoutines.transferStacks, hscratch]
    omega
  exact ho.seq (clearMany_eval highPorts (movedOutput a))

theorem finished_high (a : State 16 294) (i : Fin 38) :
    (finished a).stacks (producerPorts i) = [] := by
  rw [finished, clearMany_stacks, ite_eq_left]
  exact (highPorts_mem _).mpr (by simp [producerPorts])

theorem finished_low (a : State 16 294) (hscratch : a.stacks 292 = [])
    (hempty : a.stacks 217 = []) (i : Fin 256) :
    (finished a).stacks (lowPorts i) =
      (Function.update (fun j => a.stacks (lowPorts j)) 217 (a.stacks 271)) i := by
  have hi : (lowPorts i).val < 256 := i.isLt
  rw [finished, clearMany_stacks, ite_eq_right ((highPorts_mem _).not.mpr (by omega))]
  have h271 : lowPorts i ≠ 271 := by intro h; have := congrArg Fin.val h; omega
  have h292 : lowPorts i ≠ 292 := by intro h; have := congrArg Fin.val h; omega
  by_cases h217 : i = 217
  · subst i
    simp [movedOutput, afterTransfer, StackRoutines.transferStacks, lowPorts, hscratch, hempty]
  · have h217' : lowPorts i ≠ 217 := by
      intro h
      apply h217
      apply Fin.ext
      have hv := congrArg Fin.val h
      simpa [lowPorts] using hv
    simp [movedOutput, afterTransfer, StackRoutines.transferStacks,
      h271, h292, h217', h217]


theorem emptyHigh_nil (i : Fin 38) : emptyHigh [] i = [] := by
  fin_cases i <;> rfl

theorem embed_producer_low (regs : Fin 16 → Bool) (low : Fin 256 → List Bool)
    (mask : List Bool) (out : State 8 38) (i : Fin 256) :
    (embedState producerRegisters producerPorts
      (loaded (joinedState regs low (emptyHigh mask))) out).stacks (lowPorts i) =
        (Function.update low 217 []) i := by
  rw [embedState_stack_frame _ _ _ _ _]
  · exact loaded_low regs low mask i
  · rintro ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    have hi := i.isLt
    simp only [producerPorts, lowPorts, Fin.val_natAdd, Fin.val_castAdd] at hv
    omega

theorem finished_producer_shape (regs : Fin 16 → Bool) (low : Fin 256 → List Bool)
    (mask : List Bool) (rr : Fin 8 → Bool) (modulus width degree bits : List Bool) :
    let out := state rr modulus width degree bits [] {target := mask.reverse}
    let embedded := embedState producerRegisters producerPorts
      (loaded (joinedState regs low (emptyHigh mask))) out
    finished embedded = joinedState (finished embedded).regs
      (Function.update low 217 bits) (emptyHigh []) := by
  dsimp only
  let out := state rr modulus width degree bits [] {target := mask.reverse}
  let embedded := embedState producerRegisters producerPorts
    (loaded (joinedState regs low (emptyHigh mask))) out
  have hscratch : embedded.stacks 292 = [] := by
    change embedded.stacks (producerPorts 36) = []
    rw [embedState_stack _ _ _ _ producerPorts_injective]
    rfl
  have hempty : embedded.stacks 217 = [] := by
    change embedded.stacks (lowPorts 217) = []
    rw [embed_producer_low]
    rfl
  have hword : embedded.stacks 271 = bits := by
    change embedded.stacks (producerPorts 15) = bits
    rw [embedState_stack _ _ _ _ producerPorts_injective]
    rfl
  apply SubexpScanPrimitives.state_ext
  · rfl
  · funext i
    by_cases hi : i.val < 256
    · let j : Fin 256 := ⟨i.val, hi⟩
      have hj : lowPorts j = i := Fin.ext rfl
      rw [← hj, joinedState_low]
      change (finished embedded).stacks (lowPorts j) = (Function.update low 217 bits) j
      rw [finished_low embedded hscratch hempty j, hword]
      have hh : (fun k => embedded.stacks (lowPorts k)) = Function.update low 217 [] := by
        funext k
        exact embed_producer_low regs low mask out k
      rw [hh, Function.update_idem]
    · let j : Fin 38 := ⟨i.val - 256, by omega⟩
      have hj : producerPorts j = i := by
        apply Fin.ext
        simp only [producerPorts, Fin.val_natAdd, j]
        omega
      rw [← hj, joinedState_high]
      change (finished embedded).stacks (producerPorts j) = emptyHigh [] j
      rw [finished_high, emptyHigh_nil]


theorem clearManyCost_le_on (ps : List (Fin 294)) (a : State 16 294) (B : ℕ)
    (ha : ∀ i ∈ ps, (a.stacks i).length ≤ B) :
    clearManyCost ps a ≤ ps.length * (2 * B + 3) := by
  induction ps generalizing a with
  | nil => simp [clearManyCost]
  | cons p ps ih =>
    have hb : ∀ i ∈ ps, ((clearState p a).stacks i).length ≤ B := by
      intro i hi
      by_cases h : i = p
      · subst i; simp [clearState]
      · simpa [clearState, h] using ha i (by simp [hi])
    have hc := ih (clearState p a) hb
    have hp := ha p (by simp)
    simp only [clearManyCost, List.length_cons]
    nlinarith

theorem core_words_le (regs : Fin 8 → Bool) (modulus width degree bits mask : List Bool)
    (B : ℕ) (hm : modulus.length ≤ B) (hw : width.length ≤ B) (hd : degree.length ≤ B)
    (ho : bits.length ≤ B) (hmask : mask.length ≤ B) (i : Fin 38) :
    ((state regs modulus width degree bits [] {target := mask}).stacks i).length ≤ B := by
  fin_cases i <;> first | exact hm | exact hw | exact hd | exact ho | exact hmask | exact Nat.zero_le _

theorem finish_cost_le (regs : Fin 16 → Bool) (low : Fin 256 → List Bool)
    (mask : List Bool) (rr : Fin 8 → Bool) (modulus width degree bits : List Bool) :
    let out := state rr modulus width degree bits [] {target := mask.reverse}
    let embedded := embedState producerRegisters producerPorts
      (loaded (joinedState regs low (emptyHigh mask))) out
    clearManyCost highPorts (movedOutput embedded) ≤
      38 * (2 * (modulus.length + width.length + degree.length + mask.length + bits.length) + 3) := by
  dsimp only
  let out := state rr modulus width degree bits [] {target := mask.reverse}
  let a := embedState producerRegisters producerPorts
    (loaded (joinedState regs low (emptyHigh mask))) out
  have hbound := clearManyCost_le_on highPorts (movedOutput a)
    (modulus.length + width.length + degree.length + mask.length + bits.length)
  simp only [highPorts, List.length_map, List.length_finRange] at hbound
  apply hbound
  intro i hi
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
  have h217 : producerPorts j ≠ 217 := by
    intro h
    have hv := congrArg Fin.val h
    simp only [producerPorts, Fin.val_natAdd] at hv
    omega
  by_cases h271 : producerPorts j = 271
  · simp [movedOutput, afterTransfer, StackRoutines.transferStacks, h271]
  by_cases h292 : producerPorts j = 292
  · simp [movedOutput, afterTransfer, StackRoutines.transferStacks, h292]
  simp only [movedOutput, afterTransfer, StackRoutines.transferStacks, Function.update_apply,
    ite_eq_right h217, ite_eq_right h292, ite_eq_right h271]
  rw [embedState_stack _ _ _ _ producerPorts_injective]
  exact core_words_le rr modulus width degree bits mask.reverse _
    (by omega) (by omega) (by omega) (by omega) (by simp; omega) j

/-- The original native emitter, immediate correction substitution, additive
normalization and cleanup execute on one fixed source machine. Every incoming
word assertion describes the concrete scalar caches or row serialization. -/
theorem run_space (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d) (model : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (u J N : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (theta : DensePolynomialProgram.Coeff (baseWidth 3 t) d)
    (rows : List (DensePolynomialProgram.Fixed.Array (baseWidth 3 t) d N × Bool))
    (low : SubexpConvolutionControl.Store)
    (hinput : PerturbationAssembly.LowInput t model M cache J N theta rows low)
    (hout : low 217 = []) (regs : Fin 16 → Bool) (U : Finset (Fin rows.length)) :
    let source := emittedSource t model M cache J N theta rows
    let result := Normalize.run 3 t M cache (HeadEvaluation.specializeEntries U source) []
    let start := joinedState regs low (emptyHigh (Squarefree.encodeMask U))
    let bound := combinedBudget
      (PerturbationAssembly.lowWorkPolynomial rows.length N J t d
        ((low 192).length + (low 193).length + (low 243).length))
      ((low 194).length + (low 202).length + (low 204).length)
      (Product.bytes source).length rows.length (baseWidth 3 t) d u J (1 + rows.length * (J - 1))
    ∃ steps rr, steps ≤ bound ∧
      Trace program steps (start.withPC (some program.entry))
        ((joinedState rr (Function.update low 217 (Product.bytes result)) (emptyHigh [])).withPC none) ∧
      Good ∅ u J result ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace program prefixSteps (start.withPC (some program.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ stackBits start.stacks + bound := by
  dsimp only
  let source := emittedSource t model M cache J N theta rows
  let result := Normalize.run 3 t M cache (HeadEvaluation.specializeEntries U source) []
  let mask := Squarefree.encodeMask U
  let emitted := Function.update low 217 (Product.bytes source)
  have hvalid : ∀ a ∈ source, Product.ValidKey Finset.univ u J a.1 :=
    incidence_valid (RingProgram.modelRing t ht hd model M cache) u J hu hJ theta _ _
  have hlength : source.length ≤ 1 + rows.length * (J - 1) := by
    exact le_of_eq (incidence_entries_length _ J theta _ _)
  obtain ⟨lowSteps, lowRegs, hlowSteps, hlow, _⟩ :=
    low_run_space t model M cache J N theta rows low hinput hout regs
  have hlowCall := eval_call_lifted lowProgram id lowPorts
    (joinedState regs low (emptyHigh mask)) Function.injective_id lowPorts_injective hlow
  rw [embed_low, embed_low] at hlowCall
  have hload := load_eval lowRegs emitted mask
  let loadedState := loaded (joinedState lowRegs emitted (emptyHigh mask))
  let coreRegs := loadedState.regs ∘ producerRegisters
  obtain ⟨coreSteps, rr, hcoreSteps, hcore, hgood, _⟩ :=
    prepared_run_space 3 t M cache U source hvalid hlength coreRegs (low 202) (low 204)
      hinput.scalarReady.degree hinput.scalarReady.width
  have hcoreCall := eval_call_lifted preparedProgram producerRegisters producerPorts
    loadedState producerRegisters_injective producerPorts_injective hcore
  have hstart : embedState producerRegisters producerPorts loadedState
      (state coreRegs M.bits (low 202) (low 204) [] []
        {input := Product.bytes source, target := mask}) = loadedState := by
    simpa only [emitted, Function.update_of_ne (by decide : (194 : Fin 256) ≠ 217),
      Function.update_of_ne (by decide : (202 : Fin 256) ≠ 217),
      Function.update_of_ne (by decide : (204 : Fin 256) ≠ 217), Function.update_self,
      hinput.scalarReady.modulus] using embed_loaded lowRegs emitted mask
  rw [hstart] at hcoreCall
  let coreOut := state rr M.bits (low 202) (low 204) (Product.bytes result) []
    {target := mask.reverse}
  let finalCore := embedState producerRegisters producerPorts loadedState coreOut
  have hscratch : finalCore.stacks 292 = [] := by
    change finalCore.stacks (producerPorts 36) = []
    rw [embedState_stack _ _ _ _ producerPorts_injective]
    rfl
  have hword : finalCore.stacks 271 = Product.bytes result := by
    change finalCore.stacks (producerPorts 15) = Product.bytes result
    rw [embedState_stack _ _ _ _ producerPorts_injective]
    rfl
  have hfinish := finish_eval finalCore hscratch
  have hfinished : finished finalCore = joinedState (finished finalCore).regs
      (Function.update low 217 (Product.bytes result)) (emptyHigh []) := by
    simpa only [emitted, Function.update_idem] using
      finished_producer_shape lowRegs emitted mask rr M.bits (low 202) (low 204) (Product.bytes result)
  rw [hfinished] at hfinish
  have he := hlowCall.seq (hload.seq (hcoreCall.seq hfinish))
  have houtput := TruncatedRingProgram.empty_bytes_length_le hgood
  change (Product.bytes result).length ≤ _ at houtput
  have hclear := finish_cost_le lowRegs emitted mask rr M.bits (low 202) (low 204)
    (Product.bytes result)
  have hbound : lowSteps +
      (7 * ((emitted 194).length + (emitted 202).length + (emitted 204).length) +
        6 * (emitted 217).length + 21 +
        (coreSteps + (6 * (finalCore.stacks 271).length + 6 +
          clearManyCost highPorts (movedOutput finalCore)))) + 1 ≤
      combinedBudget
        (PerturbationAssembly.lowWorkPolynomial rows.length N J t d
          ((low 192).length + (low 193).length + (low 243).length))
        ((low 194).length + (low 202).length + (low 204).length)
        (Product.bytes source).length rows.length (baseWidth 3 t) d u J (1 + rows.length * (J - 1)) := by
    have hmask : mask.length = rows.length := Squarefree.encodeMask_length U
    have hmod : M.bits.length = (low 194).length := congrArg List.length hinput.scalarReady.modulus.symm
    simp only [emitted, Function.update_of_ne (by decide : (194 : Fin 256) ≠ 217),
      Function.update_of_ne (by decide : (202 : Fin 256) ≠ 217),
      Function.update_of_ne (by decide : (204 : Fin 256) ≠ 217), Function.update_self, hword]
    dsimp only [combinedBudget]
    change clearManyCost highPorts (movedOutput finalCore) ≤ _ at hclear
    rw [hmask, hmod] at hclear
    omega
  refine ⟨_, (finished finalCore).regs, hbound, ?_, hgood, ?_⟩
  · exact compiled_halt_trace he 205 217
  · intro prefixSteps intermediate hp htrace i
    exact StructuredSpace.local_stack_bound program (by rfl) prefixSteps intermediate
      (hp.trans hbound) htrace i

end Native

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorTableSpecialization
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Proof-side correctness of the unchanged immediately specialized incidence
call. Operational command definitions remain in FactorTableProgram. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI BitProgram StructuredCalls SubexpConvolutionControl SubexpScanPrimitives
open SubexpPolynomialConstructor PerturbationAssembly OAI.Algorithms.SubexponentialSAT.SubexpLiftRing

attribute [local simp] Fin.coe_ofNat_eq_mod

/-- Input words alone instantiate the concrete emitter/specializer. The result
has empty correction support before its bytes enter the outer lookup table. -/
theorem specializeCall_run_oai (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (model : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (u J N : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (theta : DensePolynomialProgram.Coeff (baseWidth 3 t) d)
    (rows : List (DensePolynomialProgram.Fixed.Array (baseWidth 3 t) d N × Bool))
    (a : OuterData) (low : Fin 256 → List Bool)
    (hinput : PerturbationAssembly.LowInput t model M cache J N theta rows low)
    (hout : low 217 = []) (U : Finset (Fin rows.length))
    (hmask : a.stacks 857 = Squarefree.encodeMask U) (htmp : a.stacks 881 = [])
    (hs : ∀ i, a.stacks (joinedPort i) =
      (QueryProducerSpace.Native.joinedState a.regs low
        (QueryProducerSpace.Native.emptyHigh [])).stacks i) :
    let source := QueryProducerSpace.emittedSource t model M cache J N theta rows
    let result := MomentsProgram.Normalize.run 3 t M cache
      (HeadEvaluation.specializeEntries U source) []
    ∃ k rf, k ≤ 7*(a.stacks 857).length+5+
      specializeBudget t d u J N rows.length (1+rows.length*(J-1))
        (MomentsProgram.Product.bytes source).length low ∧
      TruncatedRingProgram.Good ∅ u J result ∧
      Eval specializeCall k a
        (⟨rf, Function.update a.stacks 557 (MomentsProgram.Product.bytes result)⟩ : OuterData) := by
  dsimp only
  let copied := SubexpSetupStorage.copyState 857 625 a
  let source := QueryProducerSpace.emittedSource t model M cache J N theta rows
  let result := MomentsProgram.Normalize.run 3 t M cache
    (HeadEvaluation.specializeEntries U source) []
  obtain ⟨steps, rr, hsteps, hrun, hgood, _⟩ :=
    QueryProducerSpace.Native.run_space t ht hd model M cache u J N hu hJ theta rows
      low hinput hout copied.regs U
  have hshape := copied_joined_shape a low hs
  rw [hmask] at hshape
  have htrace : Trace QueryProducerSpace.Native.program steps
      ((projectState id joinedPort copied).withPC
        (some QueryProducerSpace.Native.program.entry))
      ((QueryProducerSpace.Native.joinedState rr
        (Function.update low 217 (MomentsProgram.Product.bytes result))
        (QueryProducerSpace.Native.emptyHigh [])).withPC none) := by
    rw [hshape]
    exact hrun
  have hp := eval_call_from_state QueryProducerSpace.Native.program id joinedPort copied
    Function.injective_id joinedPort_injective htrace
  have ho := specialized_joined_output a low rr (MomentsProgram.Product.bytes result) hs
  rw [ho] at hp
  have hc := SubexpSetupStorage.copy_eval 857 625 881 a
    (by decide) (by decide) (by decide) htmp
  refine ⟨7*(a.stacks 857).length+5+steps, rr, ?_, hgood, hc.seq hp⟩
  exact Nat.add_le_add_left hsteps _

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.specializeCall_run_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.specializeCall_run_oai
