-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.native_literal
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T11:27:27.356946+00:00
-- url     : https://prove2.me/submissions/d6510128-75dd-40af-8956-3bf30de3c997

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S189
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_PerturbationEmitProgram_emit_run
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_FactorTableNative_lowPayload_native_run
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_FactorTableProgram_literalPayload_rel

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

 theorem nil : Good (B := B) (d := d) vars u J [] :=
  ⟨by simp, by simp [Squarefree.Sparse.keys]⟩

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

/-- The native constant keeps its origin record exactly at positive cutoffs. -/
theorem constant_good {n B d : ℕ} (u J : ℕ)
    (c : RingProgram.Code (Word B) d) :
    Good (n := n) ∅ u J (Squarefree.Sparse.constant u J c) := by
  by_cases h : 0 < u ∧ 0 < J
  · constructor
    · intro a ha
      simp only [Squarefree.Sparse.constant, ite_eq_left h, List.mem_singleton] at ha
      subst a
      simp [Product.ValidKey, Squarefree.Index.Kept, Squarefree.Index.Valid,
        Squarefree.Index.origin, h.1, h.2]
    · simp [Squarefree.Sparse.constant, h, Squarefree.Sparse.keys]
  · simpa only [Squarefree.Sparse.constant, ite_eq_right h] using
      (Good.nil (n := n) (B := B) (d := d) (vars := ∅) (u := u) (J := J))


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

private theorem localBudget_mono (n B d u J N a : ℕ)
    (hn : n ≤ a) (hB : B ≤ a) (hd : d ≤ a) (hu : u ≤ a) (hJ : J ≤ a) (hN : N ≤ a) :
    localBudget n B d u J N ≤ localBudget a a a a a a := by
  dsimp [localBudget, normalizationBudget, additionBudget, scalingBudget, productBudget,
    Product.stepEnvelope, MomentsReadoutProgram.uniformReadoutBudget,
    MomentsReadoutProgram.uniformSlotBudget, Dictionary.codeBranchBudget]
  gcongr

/-- The degree and constant are fixed before every runtime dimension. -/
theorem localBudget_le (n B d u J N : ℕ) :
    localBudget n B d u J N ≤ 3000000 * (n + B + d + u + J + N + 1) ^ 10 := by
  let a := n + B + d + u + J + N + 1
  have ha : 1 ≤ a := by dsimp [a]; omega
  refine (localBudget_mono n B d u J N a (by dsimp [a]; omega) (by dsimp [a]; omega)
    (by dsimp [a]; omega) (by dsimp [a]; omega) (by dsimp [a]; omega)
    (by dsimp [a]; omega)).trans ?_
  change localBudget a a a a a a ≤ 3000000 * a ^ 10
  have h0 : 1 ≤ a ^ 10 := Nat.one_le_pow 10 a ha
  have h1 : a ≤ a ^ 10 := by simpa using pow_le_pow_right' ha (show 1 ≤ 10 by decide)
  have h2 : a ^ 2 ≤ a ^ 10 := pow_le_pow_right' ha (by decide)
  have h3 : a ^ 3 ≤ a ^ 10 := pow_le_pow_right' ha (by decide)
  have h4 : a ^ 4 ≤ a ^ 10 := pow_le_pow_right' ha (by decide)
  have h5 : a ^ 5 ≤ a ^ 10 := pow_le_pow_right' ha (by decide)
  have h6 : a ^ 6 ≤ a ^ 10 := pow_le_pow_right' ha (by decide)
  have h7 : a ^ 7 ≤ a ^ 10 := pow_le_pow_right' ha (by decide)
  have h8 : a ^ 8 ≤ a ^ 10 := pow_le_pow_right' ha (by decide)
  have h9 : a ^ 9 ≤ a ^ 10 := pow_le_pow_right' ha (by decide)
  dsimp [localBudget, normalizationBudget, additionBudget, scalingBudget, productBudget,
    Product.stepEnvelope, MomentsReadoutProgram.uniformReadoutBudget,
    MomentsReadoutProgram.uniformSlotBudget, Dictionary.codeBranchBudget]
  ring_nf
  omega

theorem normalizationBudget_le_local (n B d u J N : ℕ) :
    normalizationBudget n B d u J N ≤ localBudget n B d u J N := by
  unfold localBudget
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryProducerSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

/-- A fixed exponent covers framing, scanning, handoff and normalization. -/
theorem preparedBudget_polynomial (n B d u J N L : ℕ) :
    preparedBudget n B d u J N L ≤
      3100000 * (n + B + d + u + J + N + L + 1) ^ 10 := by
  let a := n + B + d + u + J + N + L + 1
  have ha : 1 ≤ a := by dsimp [a]; omega
  have hn : n ≤ a := by dsimp [a]; omega
  have hL : L ≤ a := by dsimp [a]; omega
  have hsum : n + B + d + u + J + N + 1 ≤ a := by dsimp [a]; omega
  have hnorm := (TruncatedRingProgram.normalizationBudget_le_local n B d u J N).trans
    (TruncatedRingProgram.localBudget_le n B d u J N)
  have hnorm' : TruncatedRingProgram.normalizationBudget n B d u J N ≤
      3000000 * a ^ 10 := hnorm.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsum 10))
  have hscan : 200 * (L + 1) * (n + 2) ≤ 200 * (a + 1) * (a + 2) := by gcongr
  have h0 : 1 ≤ a ^ 10 := Nat.one_le_pow 10 a ha
  have h1 : a ≤ a ^ 10 := by simpa using pow_le_pow_right' ha (show 1 ≤ 10 by decide)
  have h2 : a ^ 2 ≤ a ^ 10 := pow_le_pow_right' ha (by decide)
  change preparedBudget n B d u J N L ≤ 3100000 * a ^ 10
  unfold preparedBudget budget
  have hexpand : 200 * (a + 1) * (a + 2) = 200 * a ^ 2 + 600 * a + 400 := by ring
  rw [hexpand] at hscan
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpPolynomialConstructor
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Reusable physical construction of a padded polynomial from two scalar
cells and a cached unary dimension. The native constructor buffers are
cleared on return; an order-preserving move writes the chosen cache slot. -/

namespace SubexponentialSAT.SubexpPolynomialConstructor

open BitProgram StructuredCalls SubexpConvolutionControl
open SubexpPolynomialServiceControl (transfer transfer_run)

theorem move_run (s : Store) (src dst : Fin 256)
    (hs : src ≠ 245) (hd : dst ≠ 245) (hsd : src ≠ dst)
    (htmp : s 245 = []) (hout : s dst = []) :
    ExecutesIn (move src dst) (6 * (s src).length + 6) s
      (Function.update (Function.update s src []) dst (s src)) := by
  let middle := Function.update (Function.update s src []) 245 (s src).reverse
  have h₁ : ExecutesIn (transfer src 245) (3 * (s src).length + 3) s middle := by
    simpa [middle, htmp] using transfer_run src 245 s hs
  have he : Function.update (Function.update middle 245 []) dst
      ((middle 245).reverse ++ middle dst) =
      Function.update (Function.update s src []) dst (s src) := by
    funext j
    by_cases hj : j = 245 <;>
      simp [middle, Function.update_apply, hd, Ne.symm hs, Ne.symm hd, Ne.symm hsd, htmp, hout, hj]
  have h₂ : ExecutesIn (transfer 245 dst) (3 * (s src).length + 3) middle
      (Function.update (Function.update s src []) dst (s src)) := by
    have h := transfer_run 245 dst middle (Ne.symm hd)
    rw [he] at h
    simpa [middle] using h
  have h := h₁.seq h₂
  have hcost : (3 * (s src).length + 3) + (3 * (s src).length + 3) =
      6 * (s src).length + 6 := by omega
  simpa only [move, hcost] using h

end SubexponentialSAT.SubexpPolynomialConstructor

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyEntry
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Frame an actual completed incidence dictionary under its original variable
ID. The table accumulator is229; all coefficient-emitter work ports are free. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpConvolutionControl
open SubexpPolynomialConstructor

theorem emitTable_run (s : Store) (key payload : List Bool)
    (hk : s 222=key.reverse) (hp : s 228=payload.reverse) :
    ExecutesIn emitTable (4*key.length+4*payload.length+14) s
      (Function.update (Function.update (Function.update s 222 []) 228 [])
        229 (Encoding.frame key++Encoding.frame payload++s 229)) := by
  intro regs
  have h := PerturbationEmitProgram.emit_run (s ∘ tableMap) key payload
    (by
      change s (tableMap 222) = key.reverse
      rw [show tableMap 222 = 222 by decide]
      exact hk)
    (by
      change s (tableMap 228) = payload.reverse
      rw [show tableMap 228 = 228 by decide]
      exact hp)
  obtain ⟨n,rf,hn,he⟩ := h regs
  have hl := eval_liftCommand_from_state PerturbationEmitProgram.emitCommand
    0 0 id tableMap (⟨regs,s⟩ : Data) Function.injective_id tableMap.injective he
  let out := Function.update (Function.update (Function.update s 222 []) 228 [])
    229 (Encoding.frame key++Encoding.frame payload++s 229)
  have hext : Function.extend tableMap (s ∘ tableMap) s=s := by
    exact congrArg StructuredProgram.State.stacks
      (embedState_project id tableMap (⟨regs,s⟩ : Data) Function.injective_id tableMap.injective)
  have hout : embedState id tableMap (⟨regs,s⟩ : Data)
      (⟨rf,Function.update (Function.update (Function.update (s ∘ tableMap) 222 []) 228 [])
        217 (Encoding.frame key++Encoding.frame payload++(s ∘ tableMap) 217)⟩ : Data) =
      (⟨rf,out⟩ : Data) := by
    apply state_ext
    · simp [embedState]
    · change Function.extend tableMap _ s=out
      rw [ProgramLinking.extend_update tableMap.injective,
        ProgramLinking.extend_update tableMap.injective,
        ProgramLinking.extend_update tableMap.injective,hext]
      have h222 : tableMap 222=222 := by decide
      have h228 : tableMap 228=228 := by decide
      have h217 : tableMap 217=229 := by decide
      simp only [h222,h228,h217,Function.comp_apply]
      rfl
  change Eval emitTable (n+1) (⟨regs,s⟩ : Data) _ at hl
  rw [hout] at hl
  exact ⟨n+1,rf,by omega,hl⟩

theorem entry_run (s : Store) (he : ∀ i ∈ entryScratch, s i=[]) :
    ExecutesIn entry (20*(s 215).length+19*(s 217).length+39) s
      (Function.update (Function.update s 217 []) 229
        (Encoding.frame (s 215)++Encoding.frame (s 217)++s 229)) := by
  let s1 := Function.update s 222 (s 215)
  let s2 := Function.update s 222 (s 215).reverse
  let s3 := Function.update (Function.update s2 217 []) 228 (s 217)
  let s4 := Function.update (Function.update s2 217 []) 228 (s 217).reverse
  have h1 : ExecutesIn (copy 215 222) (7*(s 215).length+5) s s1 := by
    simpa [s1,he 222 (by simp [entryScratch])] using
      copy_run 215 222 s (by decide) (by decide) (by decide)
        (he 120 (by simp [entryScratch]))
  have h2 : ExecutesIn (.call (StackRoutines.reverseProgram 222 223 224 (0 : Fin 16) 1))
      (9*(s 215).length+7) s1 s2 := by
    intro regs
    have h := reverse_eval (⟨regs,s1⟩ : Data) 222 223 224 0 1
      (by decide) (by decide) (by decide) (by decide)
      (by simpa [s1] using he 223 (by simp [entryScratch]))
      (by simpa [s1] using he 224 (by simp [entryScratch]))
    exact ⟨9*(s 215).length+7,_,le_rfl,by simpa [s1,s2,afterReverse,StackRoutines.reverseStacks] using h⟩
  have h3 : ExecutesIn (move 217 228) (6*(s 217).length+6) s2 s3 := by
    simpa [s3,s2] using move_run s2 217 228 (by decide) (by decide) (by decide)
      (by simpa [s2] using he 245 (by simp [entryScratch]))
      (by simpa [s2] using he 228 (by simp [entryScratch]))
  have h4 : ExecutesIn (.call (StackRoutines.reverseProgram 228 226 227 (0 : Fin 16) 1))
      (9*(s 217).length+7) s3 s4 := by
    intro regs
    have h := reverse_eval (⟨regs,s3⟩ : Data) 228 226 227 0 1
      (by decide) (by decide) (by decide) (by decide)
      (by simpa [s3,s2] using he 226 (by simp [entryScratch]))
      (by simpa [s3,s2] using he 227 (by simp [entryScratch]))
    exact ⟨9*(s 217).length+7,_,le_rfl,by simpa [s4,s3,afterReverse,StackRoutines.reverseStacks] using h⟩
  have hout : Function.update (Function.update (Function.update s4 222 []) 228 [])
      229 (Encoding.frame (s 215)++Encoding.frame (s 217)++s4 229) =
      Function.update (Function.update s 217 []) 229
        (Encoding.frame (s 215)++Encoding.frame (s 217)++s 229) := by
    funext i
    by_cases h217 : i=217 <;> by_cases h222 : i=222 <;>
      by_cases h228 : i=228 <;> by_cases h229 : i=229 <;>
      simp [s4,s2,h217,h222,h228,h229,
        he 222 (by simp [entryScratch]),he 228 (by simp [entryScratch])]
  have h5 := emitTable_run s4 (s 215) (s 217)
    (by simp [s4,s2]) (by simp [s4])
  rw [hout] at h5
  have h := (h1.seq (h2.seq (h3.seq h4))).seq h5
  convert h using 1 <;> first | rfl | ring

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramAdd
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native addition of dense polynomial arrays whose coefficients have an
arbitrary runtime extension degree. The fixed scanner visits base words;
there is no quartet assumption and no generated instruction table. -/

namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.DensePolynomialLoop
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem encode_eq_flatten_words {B d : ℕ} (P : List (Coeff B d)) :
    encode P = flatten (words P) := by
  induction P with
  | nil => rfl
  | cons a P ih =>
      simp [encode, words, flatten, RingProgram.flat, List.map_ofFn, Function.comp_def,
        show (P.map RingProgram.flat).flatten = flatten (words P) from ih]

@[simp] theorem encode_length {B d : ℕ} (P : List (Coeff B d)) :
    (encode P).length = P.length * (d * B) := by
  rw [encode_eq_flatten_words, flatten_length, words_length, Nat.mul_assoc]

end SubexponentialSAT.SqrtLog.DensePolynomialProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramFixedBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact-length dense arrays and their polynomial meanings, independent of
native service composition. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed
@[simp] theorem encode_length {B degree J : ℕ} (P : Array B degree J) :
    (encode P).length = J*(degree*B) := by simp [encode,P.2]

end SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyLiteral
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual literal table entry construction and branch dispatch. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl SubexpScanPrimitives

attribute [local simp] Fin.coe_ofNat_eq_mod

theorem makeLiteralKey_run (s : Store) (j : ℕ) (hj : s 233=List.replicate j true)
    (h215 : s 215=[]) (h120 : s 120=[]) :
    ExecutesIn makeLiteralKey (7*j+7) s (Function.update s 215 (Encoding.encodeNat j)) := by
  let a := Function.update s 215 [false]
  have hp : ExecutesIn (Subexp.TupleProgram.pushConst 215 0 false) 2 s a := by
    intro regs
    refine ⟨2,Function.update regs 0 false,by omega,?_⟩
    simpa [a,h215,Subexp.TupleProgram.pushedState] using
      Subexp.TupleProgram.pushConst_eval (215 : Fin 256) (0 : Fin 16) false (⟨regs,s⟩ : Data)
  have hc : ExecutesIn (copy 233 215) (7*j+5) a
      (Function.update s 215 (Encoding.encodeNat j)) := by
    simpa [a,hj,Encoding.encodeNat] using copy_run 233 215 a
      (by decide) (by decide) (by decide) (by simp [a,h120])
  convert hp.seq hc using 1 <;> first | rfl | omega


theorem finishLiteral_run (s : Store) (he : ∀ i∈entryScratch,s i=[]) :
    ExecutesIn finishLiteral
      (22*(s 215).length+19*(s 217).length+2*(s 205).length+45) s
      (Function.update (Function.update (Function.update (Function.update s 217 [])
        229 (Encoding.frame (s 215)++Encoding.frame (s 217)++s 229)) 215 []) 205 []) := by
  have h1 := entry_run s he
  let a := Function.update (Function.update s 217 []) 229
    (Encoding.frame (s 215)++Encoding.frame (s 217)++s 229)
  have h2 := clear_run 215 a
  have h3 := clear_run 205 (Function.update a 215 [])
  have h := h1.seq (h2.seq h3)
  convert h using 1
  · rfl
  · simp only [a,Function.update_of_ne (by decide : (215:Fin 256)≠229),
      Function.update_of_ne (by decide : (215:Fin 256)≠217),
      Function.update_of_ne (by decide : (205:Fin 256)≠215),
      Function.update_of_ne (by decide : (205:Fin 256)≠229),
      Function.update_of_ne (by decide : (205:Fin 256)≠217)]
    omega

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
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

theorem innerPort_injective : Function.Injective innerPort := by
  intro a b h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [innerPort] at this
  omega

theorem basePort_low (i : Fin 768) (hi : i.val < 640) : basePort i = i.castAdd 128 := by
  have hn (j : Fin 768) (hj : 640 ≤ j.val) : i ≠ j := by
    intro h
    subst j
    omega
  simp only [basePort, ite_eq_right (hn 640 (by decide)),
    ite_eq_right (hn 641 (by decide)), ite_eq_right (hn 642 (by decide)),
    ite_eq_right (hn 647 (by decide)), ite_eq_right (hn 650 (by decide)),
    ite_eq_right (hn 651 (by decide)), ite_eq_right (hn 670 (by decide)),
    ite_eq_right (hn 671 (by decide))]

theorem basePort_inner (i : Fin 256) :
    basePort (PerturbationAssembly.innerPort i) = innerPort i := by
  rw [basePort_low _ (by change 340+i.val<640; omega)]
  rfl

theorem replaceInner_project (s : OuterStore) : replaceInner s (projectInner s)=s := by
  have h := embedState_project id innerPort (⟨fun _=>false,s⟩ : OuterData)
    Function.injective_id innerPort_injective
  exact congrArg StructuredProgram.State.stacks h

theorem replaceInner_update (s : OuterStore) (u : Store) (i : Fin 256) (bits : List Bool) :
    replaceInner s (Function.update u i bits)=Function.update (replaceInner s u) (innerPort i) bits :=
  ProgramLinking.extend_update innerPort_injective _ _ _ _

theorem liftInner_run (s : OuterStore) (code : Code) (K : ℕ) (u : Store)
    (h : ExecutesIn code K (projectInner s) u) :
    ExecutesOuter (liftInner code) (K+1) s (replaceInner s u) := by
  constructor
  intro regs
  obtain ⟨k,rf,hk,he⟩ := h regs
  have hl := eval_liftCommand_from_state code 0 0 id innerPort (⟨regs,s⟩ : OuterData)
    Function.injective_id innerPort_injective he
  refine ⟨k+1,rf,by omega,?_⟩
  unfold liftInner
  convert hl using 1
  all_goals try with_reducible_and_instances rfl
  apply state_ext
  · simp [embedState]
  · rfl

/-- A common single-result service remains a single-result service after
relocation, with the exact one-step compiled-call overhead. -/
theorem liftInner_update_run (s : OuterStore) (code : Code) (K : ℕ)
    (i : Fin 256) (bits : List Bool)
    (h : ExecutesIn code K (projectInner s) (Function.update (projectInner s) i bits)) :
    ExecutesOuter (liftInner code) (K+1) s (Function.update s (innerPort i) bits) := by
  have hh := liftInner_run s code K _ h
  simpa only [replaceInner_update,replaceInner_project] using hh

theorem literalIteration_rel (s : OuterStore) (j K Lrows Lpayload : ℕ)
    (Good : List Bool → Prop)
    (hj : s 573=List.replicate j true)
    (h545 : s 545=[]) (h555 : s 555=[]) (h557 : s 557=[])
    (he : ∀ i∈entryScratch,s (innerPort i)=[])
    (hpayload : ∀ regs : Fin 16 → Bool, ∃ words payload k rf,
      k≤K ∧ words.length≤Lrows ∧ payload.length≤Lpayload ∧ Good payload ∧
      Eval literalPayload k
        (⟨regs,Function.update s 555 (Encoding.encodeNat j)⟩ : OuterData)
        (⟨rf,Function.update (Function.update (Function.update s 555 (Encoding.encodeNat j))
          545 words) 557 payload⟩ : OuterData))
    (regs : Fin 16 → Bool) :
    ∃ payload k rf,k≤7*j+K+22*(j+1)+19*Lpayload+2*Lrows+54 ∧
      payload.length≤Lpayload ∧ Good payload ∧
      Eval literalIteration k (⟨regs,s⟩ : OuterData)
        (⟨rf,Function.update s 569 (Encoding.frame (Encoding.encodeNat j)++
          Encoding.frame payload++s 569)⟩ : OuterData) := by
  let key := Encoding.encodeNat j
  let a := Function.update s 555 key
  have hkey : ExecutesOuter (liftInner makeLiteralKey) (7*j+8) s a := by
    have h := liftInner_update_run s makeLiteralKey (7*j+7) 215 key
      (makeLiteralKey_run (projectInner s) j
        (by simpa [projectInner,Function.comp_def,innerPort] using hj)
        (by simpa [projectInner,Function.comp_def,innerPort] using h555)
        (by simpa [projectInner,Function.comp_def,innerPort] using he 120 (by simp [entryScratch])))
    simpa [a,innerPort] using h
  obtain ⟨nk,rk,hnk,hek⟩ := hkey.run regs
  obtain ⟨words,payload,np,rp,hnp,hw,hp,hgood,hep⟩ := hpayload rk
  let b := Function.update (Function.update a 545 words) 557 payload
  have hb : ∀ i∈entryScratch,(projectInner b) i=[] := by
    intro i hi
    have hn : innerPort i≠555 ∧ innerPort i≠545 ∧ innerPort i≠557 := by
      simp only [entryScratch, List.mem_cons, List.mem_nil_iff, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa [b,a,projectInner,Function.comp_def,Function.update_apply,hn.1,hn.2.1,hn.2.2] using he i hi
  have hend := liftInner_run b finishLiteral
    (22*key.length+19*payload.length+2*words.length+45)
    (Function.update (Function.update (Function.update (Function.update (projectInner b) 217 [])
      229 (Encoding.frame ((projectInner b) 215)++Encoding.frame ((projectInner b) 217)++
        (projectInner b) 229)) 215 []) 205 [])
    (by simpa [projectInner,Function.comp_def,innerPort,b,a] using finishLiteral_run (projectInner b) hb)
  rw [replaceInner_update,replaceInner_update,replaceInner_update,replaceInner_update,
    replaceInner_project] at hend
  have hout : Function.update (Function.update (Function.update (Function.update b
      (innerPort 217) []) (innerPort 229)
      (Encoding.frame ((projectInner b) 215)++Encoding.frame ((projectInner b) 217)++(projectInner b) 229))
      (innerPort 215) []) (innerPort 205) []=
      Function.update s 569 (Encoding.frame key++Encoding.frame payload++s 569) := by
    funext i
    by_cases h545' : i=545
    · subst i; simp [innerPort,h545]
    by_cases h555' : i=555
    · subst i; simp [innerPort,h555]
    by_cases h557' : i=557
    · subst i; simp [innerPort,h557]
    by_cases h569' : i=569
    · subst i; simp [innerPort, projectInner, b, a]
    simp [innerPort, projectInner, b, a, h545', h555', h557', h569']
  rw [hout] at hend
  obtain ⟨nf,rf,hnf,hef⟩ := hend.run rp
  refine ⟨payload,nk+(np+nf),rf,?_,hp,hgood,hek.seq (hep.seq hef)⟩
  simp only [key,Encoding.encodeNat,List.length_append,List.length_replicate,List.length_singleton] at hnf
  omega


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyStoredLow
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual low-variable worker's byte output, including its internally
computed beta, is the unnormalized Stored incidence dictionary. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT
open DensePolynomialProgram _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree PerturbationProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem originKey_eq_encodeIndex (n : ℕ) :
    originKey n = encodeIndex (Index.origin : Index (Fin n)) := by
  simp [originKey,PerturbationEmitProgram.keyBits,PerturbationProgram.Key.bits,
    encodeIndex,Index.origin,encodeMask,Encoding.encodeNat]

theorem origin_dictionary {B d : ℕ} (n : ℕ) (beta : Coeff B d) :
    Encoding.frame (originKey n) ++ Encoding.frame (RingProgram.flat beta) =
      dictionaryBits [((Index.origin : Index (Fin n)),beta)] := by
  simp [dictionaryBits,originKey_eq_encodeIndex]

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
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

/-- Source storage before specialization is polynomial even though later
multivariate products would have exponentially many potential supports. -/
theorem incidence_bytes_length {n B d : ℕ}
    (ops : SubexpSymbolicCost.RepresentedRing (RingProgram.Code (Word B) d) R)
    (u J : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (theta beta : RingProgram.Code (Word B) d)
    (rows : Fin n → List (RingProgram.Code (Word B) d)) :
    (Product.bytes (PerturbationAssembly.outputWords ops.program J theta beta rows)).length ≤
      (1 + n * (J - 1)) * (2 * (u + J + n) + 2 * (d * B) + 2) := by
  have h := Product.bytes_length_le
    (PerturbationAssembly.outputWords ops.program J theta beta rows) (u + J + n)
    (fun a ha => Squarefree.encodeIndex_length_le a.1
      (incidence_valid ops u J hu hJ theta beta rows a ha).1)
  rwa [incidence_entries_length] at h

end


/-- The byte ABI of the native incidence emitter is the product dictionary ABI. -/
theorem dictionaryBits_productBytes {n B d : ℕ} (source : List (Product.Entry n B d)) :
    PerturbationProgram.dictionaryBits source = Product.bytes source := by
  induction source with
  | nil => rfl
  | cons a source ih =>
    simpa only [PerturbationProgram.dictionaryBits_cons, Product.bytes, Normalize.bytes,
      Squarefree.Program.encodeDictionary, List.map_cons, Squarefree.Program.rawEntries] using
      congrArg (fun bits => Encoding.frame (Squarefree.encodeIndex a.1) ++
        Encoding.frame (RingProgram.flat a.2) ++ bits) ih

namespace Native

open SubexpScanPrimitives SubexpSetupStorage



/-- The full local join retains a fixed polynomial degree, including cleanup. -/
theorem combinedBudget_polynomial (lowWork cacheLength rawLength n B d u J count : ℕ) :
    combinedBudget lowWork cacheLength rawLength n B d u J count ≤
      3200000 * (lowWork + cacheLength + rawLength + n + B + d + u + J + count + 1) ^ 10 := by
  let a := lowWork + cacheLength + rawLength + n + B + d + u + J + count + 1
  have ha : 1 ≤ a := by dsimp [a]; omega
  have hl : lowWork ≤ a := by dsimp [a]; omega
  have hc : cacheLength ≤ a := by dsimp [a]; omega
  have hr : rawLength ≤ a := by dsimp [a]; omega
  have hn : n ≤ a := by dsimp [a]; omega
  have hB : B ≤ a := by dsimp [a]; omega
  have hd : d ≤ a := by dsimp [a]; omega
  have hu : u ≤ a := by dsimp [a]; omega
  have hJ : J ≤ a := by dsimp [a]; omega
  have hp := preparedBudget_polynomial n B d u J count rawLength
  have hsum : n + B + d + u + J + count + rawLength + 1 ≤ a := by dsimp [a]; omega
  have hp' : preparedBudget n B d u J count rawLength ≤ 3100000 * a ^ 10 :=
    hp.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsum 10))
  have ho : u * J * (2 * (u + J + n) + 2 * (d * B) + 2) ≤
      a * a * (2 * (a + a + a) + 2 * (a * a) + 2) := by gcongr
  have he : a * a * (2 * (a + a + a) + 2 * (a * a) + 2) =
      2 * a ^ 4 + 6 * a ^ 3 + 2 * a ^ 2 := by ring
  rw [he] at ho
  have h0 : 1 ≤ a ^ 10 := Nat.one_le_pow 10 a ha
  have h1 : a ≤ a ^ 10 := by simpa using pow_le_pow_right' ha (show 1 ≤ 10 by decide)
  have h2 : a ^ 2 ≤ a ^ 10 := pow_le_pow_right' ha (by decide)
  have h3 : a ^ 3 ≤ a ^ 10 := pow_le_pow_right' ha (by decide)
  have h4 : a ^ 4 ≤ a ^ 10 := pow_le_pow_right' ha (by decide)
  change combinedBudget lowWork cacheLength rawLength n B d u J count ≤ 3200000 * a ^ 10
  dsimp only [combinedBudget]
  omega

end Native

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyRelInput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Common physical input invariant, independent of whichever exact source
arrays are returned by the next native source execution. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls DensePolynomialProgram SubexpConvolutionControl
open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem pairChoice_rows {B d N : ℕ} (xs : List (Fixed.Array B d N)) (choice : List Bool)
    (h : xs.length=choice.length) : (pairChoice xs choice).map Prod.fst=xs := by
  rw [←List.unzip_fst]
  exact congrArg Prod.fst (List.unzip_zip h)

variable {t d : ℕ} {a : RingModel.Data d}
  {M : SubexpPreparedQuartic.Modulus 3 t} {cache : RingProgram.ScalarCache 3 t}
  {J N : ℕ} {theta : Coeff (baseWidth 3 t) d} {s : OuterStore} {n : ℕ}

theorem StagedInput.scratch (h : StagedInput t a M cache J N theta s n)
    (i : Fin 256) (hi : i∈lowScratch) : s (innerPort i)=[] := by
  by_cases hlo : i.val < 205
  · apply h.arithmetic.clean i hlo
    intro ha
    simp [lowScratch, PerturbationBetaProgram.workPorts, originScratch, targetScratch,
      coordinateLoadScratch, shiftScratch, coordinateEmitScratch] at hi
    simp [arithmeticCachePorts] at ha
    omega
  · exact h.workEmpty i hi (by omega)

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyOutputBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Polynomial storage bounds for the actual emitted, unnormalized output. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT DensePolynomialProgram
open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem sourceWords_length {B d N : ℕ} (rows : List (Fixed.Array B d N × Bool)) :
    (sourceWords rows).length=rows.length*(2*(N*(d*B))+2)+1 := by
  induction rows with
  | nil => simp [sourceWords]
  | cons row rows ih =>
      simp only [sourceWords,List.map_cons,Encoding.length_encodeList_cons,Fixed.encode_length] at *
      rw [ih]
      simp only [List.length_cons]
      ring

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
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

/-- The native high-variable branch already has empty correction support.
Both cutoff positivity facts are provided by the actual parameter choice. -/
theorem high_payload_good {n B d : ℕ} (u J : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (c : RingProgram.Code (OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing.Word B) d) :
    ∃ entries : List (MomentsProgram.Product.Entry n B d),
      TruncatedRingProgram.Good ∅ u J entries ∧
      Encoding.frame (originKey n) ++ Encoding.frame (RingProgram.flat c) =
        MomentsProgram.Product.bytes entries := by
  refine ⟨Squarefree.Sparse.constant u J c, TruncatedRingProgram.constant_good u J c, ?_⟩
  have h := PerturbationAssembly.origin_dictionary n c
  rw [QueryProducerSpace.dictionaryBits_productBytes] at h
  simpa [Squarefree.Sparse.constant, hu, hJ] using h

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorTableNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Physical source preparation for the specialized factor table. The old
master-word argument is generalized to the actually selected unary factor,
then transported through the fixed protected-port embedding. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative
open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram
open PerturbationAssembly LayoutProgram SubexpSetupStorage DensePolynomialProgram
open OAI.Algorithms.SubexponentialSAT.Subexp OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking OAI.Algorithms.SubexponentialSAT.MulticolorTypes
attribute [local simp] Fin.coe_ofNat_eq_mod

variable {r Q d n J S f : ℕ} {p : SourceBank.Parameters r Q d}
    {ps : List (ℕ × ℕ)} {P : PackingData (Fin ps.length) (UniversalType r Q 1)}
    {a : SourceReady.Data} {theta : DensePolynomialProgram.Coeff (baseWidth 3 p.t) d}


/-- Source output545 replaces only local205; scalar/cache words used by the
immediate producer retain the size bound of the actual source input. -/
theorem source_output_cache_bound (a : FactorTableProgram.OuterData) (words : List Bool)
    (S : ℕ) (hb : ∀ i, ((projectState id FactorTableProgram.basePort a).stacks i).length ≤ S)
    (i : Fin 256) (hi : i ≠ 205) :
    ((FactorTableProgram.projectInner (Function.update a.stacks 545 words)) i).length ≤ S := by
  have hn : FactorTableProgram.innerPort i ≠ 545 := by
    intro h
    apply hi
    exact FactorTableProgram.innerPort_injective h
  have hh := hb (PerturbationAssembly.innerPort i)
  change (a.stacks (FactorTableProgram.basePort (PerturbationAssembly.innerPort i))).length ≤ S at hh
  rw [FactorTableProgram.basePort_inner] at hh
  simpa only [FactorTableProgram.projectInner, Function.comp_apply, Function.update_of_ne hn] using hh

theorem good_bytes_transport {m n B d u J : ℕ} (hm : m = n)
    (entries : List (MomentsProgram.Product.Entry m B d))
    (hgood : TruncatedRingProgram.Good ∅ u J entries) :
    ∃ result : List (MomentsProgram.Product.Entry n B d),
      TruncatedRingProgram.Good ∅ u J result ∧
      MomentsProgram.Product.bytes entries = MomentsProgram.Product.bytes result := by
  subst n
  exact ⟨entries, hgood, rfl⟩

theorem lowWorkPolynomial_mono_size (n N J t d E F : ℕ) (h : E ≤ F) :
    lowWorkPolynomial n N J t d E ≤ lowWorkPolynomial n N J t d F := by
  dsimp only [lowWorkPolynomial]
  omega

/-- All source and normalizer costs use one fixed polynomial degree. -/
theorem specializeBudget_le (t d u J N n S rawLength : ℕ)
    (low : Fin 256 → List Bool)
    (h192 : (low 192).length ≤ S) (h193 : (low 193).length ≤ S)
    (h243 : (low 243).length ≤ S) (h194 : (low 194).length ≤ S)
    (h202 : (low 202).length ≤ S) (h204 : (low 204).length ≤ S)
    (hraw : rawLength ≤ specializedRawBound n u J (baseWidth 3 t) d) :
    FactorTableProgram.specializeBudget t d u J N n (1+n*(J-1)) rawLength low ≤
      specializedWorkPolynomial t d u J N n S := by
  have he : (low 192).length+(low 193).length+(low 243).length ≤ 3*S := by omega
  have hp := lowWorkPolynomial_mono_size n N J t d _ _ he
  have hb := QueryProducerSpace.Native.combinedBudget_polynomial
    (lowWorkPolynomial n N J t d ((low 192).length+(low 193).length+(low 243).length))
    ((low 194).length+(low 202).length+(low 204).length)
    rawLength n (baseWidth 3 t) d u J (1+n*(J-1))
  apply hb.trans
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  omega

/-- The emitted origin/singleton dictionary is polynomial before immediate
specialization, regardless of how many correction supports exist globally. -/
theorem emittedSource_bytes_bound (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (model : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (u J N : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (theta : Coeff (baseWidth 3 t) d)
    (rows : List (DensePolynomialProgram.Fixed.Array (baseWidth 3 t) d N × Bool)) :
    (MomentsProgram.Product.bytes
      (QueryProducerSpace.emittedSource t model M cache J N theta rows)).length ≤
      specializedRawBound rows.length u J (baseWidth 3 t) d := by
  exact QueryProducerSpace.incidence_bytes_length
    (RingProgram.modelRing t ht hd model M cache) u J hu hJ theta
    (PerturbationBetaProgram.runValue t model M cache theta (pairedRows rows))
    (fun v : Fin rows.length => rows[v].1.val)


/-- The exact generated dictionary fits an ambient-typed Goodempty witness
and one fixed polynomial budget, uniformly over the source's actual row bytes. -/
theorem lowPayload_native_bounded {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (u J n f S j : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (theta : Coeff (baseWidth 3 p.t) d)
    (s : FactorTableProgram.OuterStore) (acc : List Bool) (regs : Fin 16 → Bool)
    (hcommon : StagedInput p.t p.model p.modulus p.cache J (p.R+1) theta
      (FactorTableProgram.projectBase s) n)
    (hsource : SourceReady.Input p ps P
      (projectState id FactorTableProgram.basePort (sourceCallData s j acc regs)) j n f S)
    (hj : j < n) (hn : n ≤ S) (hf : f ≤ S)
    (hplans : (LayoutOwnerFiberProgram.stream ps).length ≤ S)
    (hmask : (s 857).length = n) (htmp : s 881 = []) :
    ∃ (xs : List (DensePolynomialProgram.Fixed.Array (baseWidth 3 p.t) d (p.R+1)))
      (k : ℕ) (rf : Fin 16 → Bool),
      xs.length = n ∧
      LayoutSourceRowsProgram.RowProperty DensePolynomialProgram.Fixed.encode
        (fun z out => PolynomialExecutorProgram.meaning p.ops out.val =
          LayoutSourceRowsProgram.sourceRowFamily ps n f j
            (LayoutSourceRowsProgram.totalPackedSource p P) z)
        ((p.R+1)*(d*baseWidth 3 p.t)) 0 xs ∧
      let payload := specializedRowPayload p.t p.model p.modulus p.cache J (p.R+1)
        theta (pairChoice xs (s 546)) (s 857)
      (∃ entries : List (MomentsProgram.Product.Entry n (baseWidth 3 p.t) d),
        TruncatedRingProgram.Good ∅ u J entries ∧ payload = MomentsProgram.Product.bytes entries) ∧
      payload.length ≤ specializedPayloadBound n u J (baseWidth 3 p.t) d ∧
      k ≤ Source.nativeSourceWorkPolynomial p S + 1 +
        (7*n+5+specializedWorkPolynomial p.t d u J (p.R+1) n S) ∧
      Eval FactorTableProgram.lowPayload k (sourceCallData s j acc regs)
        (⟨rf,Function.update
          (Function.update (sourceCallData s j acc regs).stacks 545
            (Encoding.encodeList DensePolynomialProgram.Fixed.encode xs))
          557 payload⟩ : FactorTableProgram.OuterData) := by
  obtain ⟨xs,hxs,hrows,k,rf,hk,hgood,he⟩ := lowPayload_native_run p ps P u J n f S j hu hJ
    theta s acc regs hcommon hsource hj hn hf hplans hmask htmp
  let pairs := pairChoice xs (s 546)
  have hchoices : (s 546).length = n := hcommon.choicesLength
  have hpairs : pairs.length = n :=
    (pairChoice_length xs (s 546) (hxs.trans hchoices.symm)).trans hxs
  let words := Encoding.encodeList DensePolynomialProgram.Fixed.encode xs
  let low := FactorTableProgram.projectInner
    (Function.update (sourceCallData s j acc regs).stacks 545 words)
  have hb (i : Fin 256) (hi : i ≠ 205) : (low i).length ≤ S :=
    source_output_cache_bound (sourceCallData s j acc regs) words S hsource.size i hi
  have hraw := emittedSource_bytes_bound p.t p.ht p.hd p.model p.modulus p.cache
    u J (p.R+1) hu hJ theta pairs
  have hbudget := specializeBudget_le p.t d u J (p.R+1) pairs.length S _ low
    (hb 192 (by decide)) (hb 193 (by decide)) (hb 243 (by decide))
    (hb 194 (by decide)) (hb 202 (by decide)) (hb 204 (by decide)) hraw
  have hbudget' := hbudget.trans_eq
    (congrArg (fun m => specializedWorkPolynomial p.t d u J (p.R+1) m S) hpairs)
  have hlen := TruncatedRingProgram.empty_bytes_length_le hgood
  have hlen' := hlen.trans_eq (congrArg
    (fun m => u*J*(2*(u+J+m)+2*(d*baseWidth 3 p.t)+2)) hpairs)
  refine ⟨xs,k,rf,hxs,hrows,?_,hlen',?_,he⟩
  · exact good_bytes_transport hpairs _ hgood
  · exact hk.trans (Nat.add_le_add_left (Nat.add_le_add_left hbudget' _) _)


/-- Every literal branch is discharged by the actual fixed source and
immediate normalizer. Its source assumption contains physical words only. -/
theorem native_literal_oai {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (u J n f S j : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (theta : Coeff (baseWidth 3 p.t) d)
    (s : FactorTableProgram.OuterStore) (acc : List Bool)
    (h : StagedInput p.t p.model p.modulus p.cache J (p.R+1) theta
      (FactorTableProgram.projectBase s) n)
    (hsource : ∀ regs : Fin 16 → Bool, SourceReady.Input p ps P
      (projectState id FactorTableProgram.basePort (sourceCallData s j acc regs)) j n f S)
    (hj : j < n) (hn : n ≤ S) (hf : f ≤ S)
    (hplans : (LayoutOwnerFiberProgram.stream ps).length ≤ S)
    (h545 : s 545 = []) (h555 : s 555 = []) (h557 : s 557 = [])
    (hm : (s 575).length = n) (hmask : (s 857).length = n) (htmp : s 881 = [])
    (regs : Fin 16 → Bool) :
    ∃ payload k rf, k ≤ specializedLiteralWork p u J n S (s 574).length ∧
      payload.length ≤ specializedPayloadBound n u J (baseWidth 3 p.t) d ∧
      PayloadMeaning p ps P u J n f theta s j payload ∧
      Eval FactorTableProgram.literalIteration k
        (⟨regs,FactorTableProgram.literalReady s (List.replicate j true) acc⟩ : FactorTableProgram.OuterData)
        (⟨rf,FactorTableProgram.literalReady s (List.replicate j true)
          (Encoding.frame (Encoding.encodeNat j)++Encoding.frame payload++acc)⟩ : FactorTableProgram.OuterData) := by
  let current := FactorTableProgram.literalReady s (List.replicate j true) acc
  let keyed := Function.update current 555 (Encoding.encodeNat j)
  let W := d*baseWidth 3 p.t
  let Lrows := n*(2*((p.R+1)*W)+2)+1
  let Lpayload := specializedPayloadBound n u J (baseWidth 3 p.t) d
  let Klow := Source.nativeSourceWorkPolynomial p S+1+
    (7*n+5+specializedWorkPolynomial p.t d u J (p.R+1) n S)
  let Kpayload := 10*j+9*(s 574).length+18+(10*j+42*n+29*W+109)+Klow
  have scratch (i : Fin 256) (hi : i ∈ lowScratch) :
      s (FactorTableProgram.innerPort i) = [] := by
    have hh := h.scratch i hi
    change s (FactorTableProgram.basePort (PerturbationAssembly.innerPort i)) = [] at hh
    rwa [FactorTableProgram.basePort_inner] at hh
  have he : ∀ i∈entryScratch,current (FactorTableProgram.innerPort i)=[] := by
    intro i hi
    have hni : FactorTableProgram.innerPort i≠573 ∧ FactorTableProgram.innerPort i≠569 := by
      simp only [entryScratch, List.mem_cons, List.mem_nil_iff, or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    have hilow : i ∈ lowScratch := by
      simp only [entryScratch, List.mem_cons, List.mem_nil_iff, or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    simpa [current,FactorTableProgram.literalReady,Function.update_apply,hni.1,hni.2] using
      scratch i hilow
  have ho : ∀ i∈originScratch,keyed (FactorTableProgram.innerPort i)=[] := by
    intro i hi
    have hni : FactorTableProgram.innerPort i≠573 ∧ FactorTableProgram.innerPort i≠569 ∧
        FactorTableProgram.innerPort i≠555 := by
      simp only [originScratch, List.mem_cons, List.mem_nil_iff, or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    have hilow : i ∈ lowScratch := by
      simp only [originScratch, List.mem_cons, List.mem_nil_iff, or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    simpa [keyed,current,FactorTableProgram.literalReady,Function.update_apply,hni.1,hni.2.1,hni.2.2] using
      scratch i hilow
  have h220 : keyed 560=[] := by
    simpa [keyed,current,FactorTableProgram.literalReady,FactorTableProgram.innerPort] using scratch 220 (by decide)
  have hz : (keyed 547).length=W := by
    simpa [keyed,current,FactorTableProgram.literalReady,W,FactorTableProgram.projectBase,
      FactorTableProgram.basePort] using congrArg List.length h.zeroWord
  have h1 : (keyed 548).length=W := by
    simpa [keyed,current,FactorTableProgram.literalReady,W,FactorTableProgram.projectBase,
      FactorTableProgram.basePort] using congrArg List.length h.oneWord
  have hprogram : p.ops.program =
      RingProgram.modelProgram p.t p.model p.modulus p.cache := by
    exact RingProgram.modelRing_program p.t p.ht p.hd p.model p.modulus p.cache
  have hzeroRun := congrArg (fun q => q.zeroRun) hprogram
  have honeRun := congrArg (fun q => q.oneRun) hprogram
  have hzeroRun' : p.ops.zeroRun =
      (RingProgram.modelProgram p.t p.model p.modulus p.cache).zeroRun := by
    simpa only [SubexpSymbolicCost.RepresentedRing.program] using hzeroRun
  have honeRun' : p.ops.oneRun =
      (RingProgram.modelProgram p.t p.model p.modulus p.cache).oneRun := by
    simpa only [SubexpSymbolicCost.RepresentedRing.program] using honeRun
  have hzWord : keyed 547=RingProgram.flat p.ops.zeroRun.1 := by
    rw [hzeroRun']
    simpa [keyed,current,FactorTableProgram.literalReady,FactorTableProgram.projectBase,
      FactorTableProgram.basePort] using h.zeroWord
  have h1Word : keyed 548=RingProgram.flat p.ops.oneRun.1 := by
    rw [honeRun']
    simpa [keyed,current,FactorTableProgram.literalReady,FactorTableProgram.projectBase,
      FactorTableProgram.basePort] using h.oneWord
  have hhighGood : ∃ entries : List (MomentsProgram.Product.Entry n (baseWidth 3 p.t) d),
      TruncatedRingProgram.Good ∅ u J entries ∧
      Encoding.frame (originKey n) ++
        Encoding.frame (if (keyed 575).getD (keyed 573).length false then keyed 548 else keyed 547) =
        MomentsProgram.Product.bytes entries := by
    cases hb : (keyed 575).getD (keyed 573).length false
    · simp only [Bool.false_eq_true, ite_false, hzWord]
      exact FactorTableProgram.high_payload_good (n:=n) u J hu hJ p.ops.zeroRun.1
    · simp only [ite_true, if_true, h1Word]
      exact FactorTableProgram.high_payload_good (n:=n) u J hu hJ p.ops.oneRun.1
  have hp : ∀ rs : Fin 16 → Bool, ∃ words payload k rf, k≤Kpayload ∧
      words.length≤Lrows ∧ payload.length≤Lpayload ∧
      PayloadMeaning p ps P u J n f theta s j payload ∧
      Eval FactorTableProgram.literalPayload k (⟨rs,keyed⟩ : FactorTableProgram.OuterData)
        (⟨rf,Function.update (Function.update keyed 545 words) 557 payload⟩ : FactorTableProgram.OuterData) := by
    intro rs
    suffices hs : ∃ words payload k rf,
        k≤10*(keyed 573).length+9*(keyed 574).length+18+
          (10*(keyed 573).length+42*n+29*W+109)+Klow ∧
        words.length≤Lrows ∧ payload.length≤Lpayload ∧
        PayloadMeaning p ps P u J n f theta s j payload ∧
        Eval FactorTableProgram.literalPayload k (⟨rs,keyed⟩ : FactorTableProgram.OuterData)
          (⟨rf,Function.update (Function.update keyed 545 words) 557 payload⟩ : FactorTableProgram.OuterData) by
      simpa [Kpayload,keyed,current,FactorTableProgram.literalReady] using hs
    refine FactorTableProgram.literalPayload_rel keyed n W Klow Lrows Lpayload
      (PayloadMeaning p ps P u J n f theta s j)
      (by simpa [keyed,current,FactorTableProgram.literalReady,FactorTableProgram.projectBase,
        FactorTableProgram.basePort] using congrArg List.length h.ambientCount)
      (by simpa [keyed,current,FactorTableProgram.literalReady] using hm) hz h1
      (by simpa [keyed,current,FactorTableProgram.literalReady] using h545)
      (by simpa [keyed,current,FactorTableProgram.literalReady] using h557) h220 ho ?_ ?_ ?_ rs
    · intro hb rs'
      have hb' : (s 574).getD j false=false := by
        simpa [keyed,current,FactorTableProgram.literalReady] using hb
      obtain ⟨xs,k,rf,hxs,hrows,hgood,hlen,hk,hev⟩ :=
        lowPayload_native_bounded p ps P u J n f S j hu hJ theta s acc rs' h
          (hsource rs') hj hn hf hplans hmask htmp
      refine ⟨Encoding.encodeList DensePolynomialProgram.Fixed.encode xs,
        specializedRowPayload p.t p.model p.modulus p.cache J (p.R+1) theta
          (pairChoice xs (s 546)) (s 857),k,rf,hk,?_,hlen,⟨hgood,?_⟩,hev⟩
      · have hl := sourceWords_length (pairChoice xs (s 546))
        have hc : xs.length=(s 546).length := hxs.trans h.choicesLength.symm
        simpa [sourceWords,pairChoice_rows xs (s 546) hc,pairChoice_length xs (s 546) hc,
          hxs,Lrows,W] using hl.le
      · simp only [hb',Bool.false_eq_true,ite_false]
        exact ⟨xs,hxs,hrows,rfl⟩
    · intro hb
      refine ⟨hhighGood,?_⟩
      have hb' : (s 574).getD j false=true := by
        simpa [keyed,current,FactorTableProgram.literalReady] using hb
      simp only [hb',ite_true, if_true]
      simp [keyed,current,FactorTableProgram.literalReady]
    · obtain ⟨entries,hgood,hbytes⟩ := hhighGood
      rw [hbytes]
      exact TruncatedRingProgram.empty_bytes_length_le hgood
  obtain ⟨payload,k,rf,hk,hlen,hmeaning,heval⟩ := FactorTableProgram.literalIteration_rel current j
    Kpayload Lrows Lpayload (PayloadMeaning p ps P u J n f theta s j)
    (by simp [current,FactorTableProgram.literalReady])
    (by simpa [current,FactorTableProgram.literalReady] using h545)
    (by simpa [current,FactorTableProgram.literalReady] using h555)
    (by simpa [current,FactorTableProgram.literalReady] using h557) he hp regs
  refine ⟨payload,k,rf,?_,hlen,hmeaning,?_⟩
  · dsimp only [Kpayload,Klow,Lpayload,Lrows,W] at hk
    unfold specializedLiteralWork
    omega
  · simpa [current,FactorTableProgram.literalReady,List.append_assoc] using heval


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.native_literal_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.native_literal_oai
