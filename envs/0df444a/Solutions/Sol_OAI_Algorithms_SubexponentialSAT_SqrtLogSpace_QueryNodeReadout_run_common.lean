-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeReadout.run_common
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:24:50.823093+00:00
-- url     : https://prove2.me/submissions/73236089-bf07-4466-85a9-1675eb5fee64

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S185
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryNodeFinish_command_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_StructuredSpace_local_stack_bound

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramLookup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed primitive dictionary lookup. Dictionary normalization guarantees
unique keys. All key and coefficient bits are scanned by the existing finite
record program; key width, coefficient width and dictionary length are runtime
data and do not affect the instruction table. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpRecordScan

variable {K C : Type*} [DecidableEq K]

section Semantic
variable [AddCommMonoid C]

private theorem fetch_zero_of_not_mem (entries : Sparse.Data K C) (k : K)
    (h : k ∉ Sparse.keys entries) : Sparse.fetch k entries = 0 := by
  induction entries with
  | nil => rfl
  | cons a entries ih =>
    rcases a with ⟨j,c⟩
    have hj : j ≠ k := by intro he; subst j; exact h (by simp [Sparse.keys])
    have ht : k ∉ Sparse.keys entries := by
      intro he; exact h (by simp only [Sparse.keys, List.map_cons, List.mem_cons]; exact Or.inr he)
    simp [Sparse.fetch, hj, ih ht]

/-- On a normalized dictionary, mathematical additive fetch is first-match lookup. -/
theorem fetch_eq_lookup (entries : Sparse.Data K C) (k : K)
    (hn : (Sparse.keys entries).Nodup) :
    Sparse.fetch k entries = (entries.lookup k).getD 0 := by
  induction entries with
  | nil => rfl
  | cons a entries ih =>
    rcases a with ⟨j,c⟩
    have hh : j ∉ Sparse.keys entries ∧ (Sparse.keys entries).Nodup := by
      simpa [Sparse.keys] using hn
    by_cases h : j = k
    · subst j
      simp [Sparse.fetch, fetch_zero_of_not_mem entries k hh.1]
    · simp [Sparse.fetch, h, List.lookup_cons, beq_false_of_ne (Ne.symm h), ih hh.2]
end Semantic

end SubexponentialSAT.SqrtLog.Squarefree.Program

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

omit [CommRing R] in
theorem denoteTable_lookup (f : C → R) (entries : List (K × C)) (k : K) :
    (denoteTable f entries).lookup k = (entries.lookup k).map f := by
  induction entries with
  | nil => rfl
  | cons a entries ih =>
    rcases a with ⟨j,c⟩
    by_cases h : j=k
    · subst j; simp [denoteTable]
    · simp only [denoteTable,List.map_cons,List.lookup_cons] at ih ⊢
      simp [beq_false_of_ne (Ne.symm h),ih]

end SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeSparseOps
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Squarefree

namespace Sparse

variable {V R : Type*} [DecidableEq V] [CommSemiring R]

theorem jetCoeff_atom (a b : Index V) (c : R) :
    jetCoeff a (atom b c) = if b = a then c else 0 := by
  rcases a with ⟨u, z, s⟩
  rcases b with ⟨v, w, t⟩
  by_cases hu : v = u <;> by_cases hz : w = z <;> by_cases hs : t = s <;>
    simp [jetCoeff, atom, Polynomial.coeff_monomial, coeff_monomial, hu, hz, hs]

theorem jetCoeff_denote (a : Index V) (l : Data (Index V) R) :
    jetCoeff a (denote l) = fetch a l := by
  induction l with
  | nil => simp [denote, decode, jetCoeff, fetch]
  | cons b l ih =>
      change jetCoeff a (atom b.1 b.2 + denote l) = _
      simp only [jetCoeff, Polynomial.coeff_add, coeff_add]
      change jetCoeff a (atom b.1 b.2) + jetCoeff a (denote l) = _
      rw [jetCoeff_atom, ih]
      rfl

end Sparse

end SubexponentialSAT.SqrtLog.Squarefree

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsOutput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A concrete dense Z-output list for CRT reconstruction. Its entries are
obtained only by sparse coefficient scans and a finite sum over retained U. -/

namespace SubexponentialSAT.SqrtLog.Moments

open scoped BigOperators
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree

variable {R V : Type*} [CommSemiring R] [DecidableEq V]

theorem coeff_tabulate (n : ℕ) (f : ℕ → R) (j : ℕ) :
    PolynomialAlgorithm.coeff (tabulate n f) j = if j < n then f j else 0 := by
  induction n generalizing f j with
  | zero => simp [tabulate, PolynomialAlgorithm.coeff]
  | succ n ih =>
      cases j with
      | zero => simp [tabulate, PolynomialAlgorithm.coeff]
      | succ j => simpa [tabulate, PolynomialAlgorithm.coeff] using ih (fun j => f (j+1)) j

end SubexponentialSAT.SqrtLog.Moments

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsReadoutProgramSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Identification of the physically computed coefficient list with the
sparse moment readout. The only lookup premise is normalized distinct keys. -/
namespace SubexponentialSAT.SqrtLog.MomentsReadoutProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram.Dictionary
open scoped BigOperators

variable {R : Type*} [CommRing R]

theorem addFetched_denote {K : Type*} [DecidableEq K]
    (p e : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p e)
    (cache : RingProgram.ScalarCache p e) (scalar : ZMod (p^e) →+* R)
    {d : ℕ} (basis : Fin d → R)
    (entries : List (K × RingProgram.Code (Word (baseWidth p e)) d)) (k : K)
    (acc : RingProgram.Code (Word (baseWidth p e)) d)
    (hn : (Squarefree.Sparse.keys entries).Nodup) :
    let f := RingProgram.denote (RingProgram.scalarRing p e M cache) scalar basis
    f (addFetched p e M cache entries k acc) =
      f acc + Squarefree.Sparse.fetch k (denoteTable f entries) := by
  dsimp only
  let f := RingProgram.denote (RingProgram.scalarRing p e M cache) scalar basis
  have hf := Squarefree.Program.fetch_eq_lookup (denoteTable f entries) k
    (by simpa only [denoteTable_keys] using hn)
  rw [denoteTable_lookup] at hf
  change f (addFetched p e M cache entries k acc) =
    f acc + Squarefree.Sparse.fetch k (denoteTable f entries)
  cases he : entries.lookup k with
  | none =>
      have hz : Squarefree.Sparse.fetch k (denoteTable f entries)=0 := by simpa [he] using hf
      simp [addFetched,he,hz]
  | some x =>
      have hx : Squarefree.Sparse.fetch k (denoteTable f entries)=f x := by simpa [he] using hf
      simpa only [addFetched,he,hx,RingProgram.scalarRing_program] using
        RingProgram.denote_add (RingProgram.scalarRing p e M cache) scalar basis acc x

theorem foldU_denote {n d : ℕ} (p e : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p e) (cache : RingProgram.ScalarCache p e)
    (scalar : ZMod (p^e) →+* R) (basis : Fin d → R)
    (entries : List (Squarefree.Index (Fin n) × RingProgram.Code (Word (baseWidth p e)) d))
    (z u k : ℕ) (acc : RingProgram.Code (Word (baseWidth p e)) d)
    (hn : (Squarefree.Sparse.keys entries).Nodup) :
    let f := RingProgram.denote (RingProgram.scalarRing p e M cache) scalar basis
    f (foldU p e M cache entries z u k acc) = f acc+
      ∑ i ∈ Finset.range k, Squarefree.Sparse.fetch ⟨u+i,z,∅⟩ (denoteTable f entries) := by
  dsimp only
  induction k generalizing u acc with
  | zero => simp [foldU]
  | succ k ih =>
      rw [foldU,ih,addFetched_denote p e M cache scalar basis entries _ _ hn]
      simp [Finset.sum_range_succ',
        add_assoc,add_comm,add_left_comm]

theorem outputCodes_denote_shift {n d : ℕ} (p e : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p e) (cache : RingProgram.ScalarCache p e)
    (scalar : ZMod (p^e) →+* R) (basis : Fin d → R)
    (entries : List (Squarefree.Index (Fin n) × RingProgram.Code (Word (baseWidth p e)) d))
    (t : ℕ) (zero : RingProgram.Code (Word (baseWidth p e)) d) (z J : ℕ)
    (hn : (Squarefree.Sparse.keys entries).Nodup)
    (hz : RingProgram.denote (RingProgram.scalarRing p e M cache) scalar basis zero=0) :
    let f := RingProgram.denote (RingProgram.scalarRing p e M cache) scalar basis
    (outputCodes p e M cache entries t zero z J).map f =
      Moments.tabulate J (fun j => ∑ u ∈ Finset.range t,
        Squarefree.Sparse.fetch ⟨u,z+j,∅⟩ (denoteTable f entries)) := by
  dsimp only
  induction J generalizing z with
  | zero => rfl
  | succ J ih =>
      simp only [outputCodes,List.map_cons,Moments.tabulate]
      rw [foldU_denote p e M cache scalar basis entries z 0 t zero hn,ih,hz]
      simp [Nat.add_comm,Nat.add_left_comm]

theorem outputCodes_denote {n d : ℕ} (p e : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p e) (cache : RingProgram.ScalarCache p e)
    (scalar : ZMod (p^e) →+* R) (basis : Fin d → R)
    (entries : List (Squarefree.Index (Fin n) × RingProgram.Code (Word (baseWidth p e)) d))
    (t J : ℕ) (zero : RingProgram.Code (Word (baseWidth p e)) d)
    (hn : (Squarefree.Sparse.keys entries).Nodup)
    (hz : RingProgram.denote (RingProgram.scalarRing p e M cache) scalar basis zero=0) :
    let f := RingProgram.denote (RingProgram.scalarRing p e M cache) scalar basis
    (outputCodes p e M cache entries t zero 0 J).map f =
      Moments.outputCoefficients t J (denoteTable f entries) := by
  simpa [Moments.outputCoefficients] using
    outputCodes_denote_shift p e M cache scalar basis entries t zero 0 J hn hz

end SubexponentialSAT.SqrtLog.MomentsReadoutProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_TruncatedRingProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
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

variable {V R : Type*} [DecidableEq V] [CommRing R]

noncomputable section

theorem eval_zero_eq_coeff (P : Squarefree.Poly V R) :
    Squarefree.evalHom (fun _ => 0) (by simp) P = Squarefree.coeff ∅ P := by
  classical
  rw [← MonoidAlgebra.sum_coeff_single P]
  generalize P.coeff = q
  induction q using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb =>
      rw [Finsupp.sum_add_index (by simp) (by simp)]
      simp only [map_add, ha, hb, Squarefree.coeff_add]
  | single s c =>
      rw [Finsupp.sum_single_index (by simp)]
      change Squarefree.evalHom (fun _ => 0) (by simp) (Squarefree.monomial s.vars c) =
        Squarefree.coeff ∅ (Squarefree.monomial s.vars c)
      rw [Squarefree.eval_monomial, Squarefree.coeff_monomial]
      by_cases hs : s.vars = ∅
      · simp [Squarefree.weight, hs]
      · obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hs
        have hz : Squarefree.weight (fun _ : V => (0 : R)) s.vars = 0 :=
          Finset.prod_eq_zero hv rfl
        simp [hz, hs]

theorem rawValue_coeff {n B d u J : ℕ}
    (f : RingProgram.Code (Word B) d → R) (a : List (Product.Entry n B d))
    (i : Fin u) (j : Fin J) :
    ((rawValue u J f a).coeff i).coeff j =
      Squarefree.Sparse.fetch ⟨i.val, j.val, ∅⟩ (Dictionary.denoteTable f a) := by
  simp only [rawValue, jetProjection, RingHom.comp_apply, Dense.coeff_ofPolynomial,
    Squarefree.coeff_evalJet, eval_zero_eq_coeff]
  exact Squarefree.Sparse.jetCoeff_denote ⟨i.val, j.val, ∅⟩ _

/-- The existing native additive readout is exactly the dense marker sum. -/
theorem readout_codes_dense (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d : ℕ} (scalar : ZMod (p ^ t) →+* R) (basis : Fin d → R)
    (u J : ℕ) (entries : List (Product.Entry n (baseWidth p t) d))
    (zero : RingProgram.Code (Word (baseWidth p t)) d)
    (hn : (Squarefree.Sparse.keys entries).Nodup)
    (hz : RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis zero = 0) :
    let f := RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis
    Truncated.ofPolynomial J (PolynomialAlgorithm.denote
      ((MomentsReadoutProgram.outputCodes p t M cache entries u zero 0 J).map f)) =
      Dense.readout (rawValue u J f entries) := by
  dsimp only
  rw [MomentsReadoutProgram.outputCodes_denote p t M cache scalar basis entries u J zero hn hz]
  ext z
  rw [Truncated.coeff_ofPolynomial, PolynomialAlgorithm.coeff_denote,
    Moments.outputCoefficients, Moments.coeff_tabulate, ite_eq_left z.isLt,
    Dense.coeff_readout]
  simp only [rawValue_coeff]
  exact (Fin.sum_univ_eq_sum_range
    (fun i => Squarefree.Sparse.fetch ⟨i, z.val, ∅⟩
      (Dictionary.denoteTable
        (RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis) entries)) u).symm

end

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NodeReadoutSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual node-array readout after all finite-difference pairs. The fixed
cleanup pays for transient lower words and clears the old output. Preserved
masters supply the coefficient zero vector and both truncation bounds. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeReadoutSpace

open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open MomentsProgram TruncatedRingProgram

theorem registers_injective : Function.Injective registers := Fin.castAdd_injective _ _

private theorem portIndex_ports (i : Fin 40) : portIndex (ports i).val = i.val := by
  fin_cases i <;> rfl

theorem ports_injective : Function.Injective ports := by
  intro i j h
  apply Fin.ext
  have hv := congrArg (fun k : Fin 896 => portIndex k.val) h
  simpa only [portIndex_ports] using hv

theorem mem_scratchIndices (i : Fin 40) : i ∈ scratchIndices ↔
    i ≠ 0 ∧ i ≠ 5 ∧ i ≠ 12 ∧ i ≠ 15 ∧ i ≠ 24 ∧ i ≠ 27 ∧
      i ≠ 28 ∧ i ≠ 29 ∧ i ≠ 36 := by
  simp only [scratchIndices, List.mem_filter, List.mem_ofFn, exists_eq,
    decide_eq_true_eq, true_and]

theorem scratchPorts_low {i : Fin 896} (hi : i ∈ scratchPorts) :
    88 ≤ i.val ∧ i.val < 128 := by
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
  obtain ⟨h0,h5,h12,h15,h24,h27,h28,h29,h36⟩ := (mem_scratchIndices j).mp hj
  simp only [ports, h0, h5, h12, h15, h24, h27, h28, h29, h36, ite_false]
  omega

theorem localState_stack (rr : Fin 8 → Bool)
    (modulus width degree dictionary zero marker taylor shape output : List Bool) (i : Fin 40) :
    (localState rr modulus width degree dictionary zero marker taylor shape output).stacks i =
      if i = 0 then output else if i = 5 then modulus else if i = 12 then width
      else if i = 15 then dictionary else if i = 24 then degree else if i = 27 then zero
      else if i = 28 then marker else if i = 29 then taylor else if i = 36 then shape else [] := by
  fin_cases i <;> rfl

theorem clearedMany_frame (a : Data) (i : Fin 896) (hi : i ∉ clearPorts) :
    (clearedMany clearPorts a).stacks i = a.stacks i := by
  rw [clearedMany_stack, ite_eq_right hi]

theorem prepared_eq (a : Data)
    (modulus width degree dictionary zero marker taylor shape : List Bool)
    (h : Ready a modulus width degree dictionary zero marker taylor shape) :
    let b := clearedMany clearPorts a
    embedState registers ports b
      (localState (fun i => b.regs (registers i))
        modulus width degree dictionary zero marker taylor shape []) = b := by
  dsimp only
  apply embedState_eq_of_ports _ _ _ _ _ registers_injective ports_injective
  · intro i; rfl
  · intros; rfl
  · intro i
    rw [localState_stack]
    by_cases h0 : i = 0
    · subst i
      simp [ports, clearedMany_stack,
        show (862 : Fin 896) ∈ clearPorts from List.mem_cons_self]
    by_cases h5 : i = 5
    · subst i
      simpa [ports, clearedMany_frame a 5 (by decide)] using h.modulus
    by_cases h12 : i = 12
    · subst i
      simpa [ports, clearedMany_frame a 12 (by decide)] using h.width
    by_cases h15 : i = 15
    · subst i
      simpa [ports, clearedMany_frame a 850 (by decide)] using h.dictionary
    by_cases h24 : i = 24
    · subst i
      simpa [ports, clearedMany_frame a 39 (by decide)] using h.degree
    by_cases h27 : i = 27
    · subst i
      simpa [ports, clearedMany_frame a 280 (by decide)] using h.zero
    by_cases h28 : i = 28
    · subst i
      simpa [ports, clearedMany_frame a 212 (by decide)] using h.marker
    by_cases h29 : i = 29
    · subst i
      simpa [ports, clearedMany_frame a 243 (by decide)] using h.taylor
    by_cases h36 : i = 36
    · subst i
      simpa [ports, clearedMany_frame a 128 (by decide)] using h.shape
    have hm : ports i ∈ scratchPorts := List.mem_map.mpr
      ⟨i, (mem_scratchIndices i).mpr ⟨h0,h5,h12,h15,h24,h27,h28,h29,h36⟩, rfl⟩
    have hmc : ports i ∈ clearPorts := List.mem_cons_of_mem 862 hm
    rw [clearedMany_stack, ite_eq_left hmc]
    simp only [h0, h5, h12, h15, h24, h27, h28, h29, h36, ite_false]
  · intros; rfl

theorem result_output (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree dictionary zero marker taylor shape bits : List Bool) :
    (result a rr modulus width degree dictionary zero marker taylor shape bits).stacks 862 = bits := by
  change (embedState registers ports _ _).stacks (ports 0) = bits
  rw [embedState_stack _ _ _ _ ports_injective]
  rfl

theorem result_stack (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree dictionary zero marker taylor shape bits : List Bool)
    (hr : Ready a modulus width degree dictionary zero marker taylor shape)
    (i : Fin 896) :
    (result a rr modulus width degree dictionary zero marker taylor shape bits).stacks i =
      if i = 862 then bits else (clearedMany clearPorts a).stacks i := by
  by_cases hi : ∃ j, ports j = i
  · obtain ⟨j, rfl⟩ := hi
    change (embedState registers ports _ _).stacks (ports j) = _
    rw [embedState_stack _ _ _ _ ports_injective]
    by_cases hj : j = 0
    · subst j
      simp only [localState_stack, ports, ↓reduceIte]
    have hn : ports j ≠ 862 := fun h => hj (ports_injective (show ports j = ports 0 from h))
    rw [ite_eq_right hn]
    have hp := congrArg (fun d : Data => d.stacks (ports j))
      (prepared_eq a modulus width degree dictionary zero marker taylor shape hr)
    rw [embedState_stack _ _ _ _ ports_injective] at hp
    rw [← hp]
    simp only [localState_stack, hj, ite_false]
  · have hn : i ≠ 862 := fun h => hi ⟨0, (show ports 0 = 862 from rfl).trans h.symm⟩
    change (embedState registers ports _ _).stacks i = _
    rw [embedState_stack_frame _ _ _ _ i hi, ite_eq_right hn]

/-- All input masters and other high query buffers survive exactly. -/
theorem result_frame (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree dictionary zero marker taylor shape bits : List Bool)
    (hr : Ready a modulus width degree dictionary zero marker taylor shape)
    (i : Fin 896) (ho : i ≠ 862) (hs : i ∉ scratchPorts) :
    (result a rr modulus width degree dictionary zero marker taylor shape bits).stacks i =
      a.stacks i := by
  rw [result_stack a rr _ _ _ _ _ _ _ _ _ hr i, ite_eq_right ho, clearedMany_stack]
  exact ite_eq_right (by simpa only [clearPorts, List.mem_cons, not_or] using And.intro ho hs)

theorem result_scratch (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree dictionary zero marker taylor shape bits : List Bool)
    (hr : Ready a modulus width degree dictionary zero marker taylor shape)
    (i : Fin 896) (hs : i ∈ scratchPorts) :
    (result a rr modulus width degree dictionary zero marker taylor shape bits).stacks i = [] := by
  have ho : i ≠ 862 := by
    have := scratchPorts_low hs
    intro h
    subst i
    change 88 ≤ 862 ∧ 862 < 128 at this
    omega
  rw [result_stack a rr _ _ _ _ _ _ _ _ _ hr i, ite_eq_right ho, clearedMany_stack]
  exact ite_eq_left (List.mem_cons_of_mem 862 hs)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeReadoutSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NodeAppendSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeAppendSpace
open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open MomentsProgram TruncatedRingProgram

theorem appendResult_stacks (a : Data) (hs : a.stacks 89 = []) :
    (appendResult a).stacks = Function.update (Function.update
      (Function.update a.stacks 863 (a.stacks 863 ++ a.stacks 862)) 862 []) 89 [] := by
  funext i
  by_cases h863 : i = 863
  · subst i
    simp [appendResult, transferred, StackRoutines.transferStacks, hs]
  by_cases h862 : i = 862
  · subst i
    simp [appendResult, transferred, StackRoutines.transferStacks, hs]
  by_cases h89 : i = 89
  · subst i
    simp [appendResult, transferred, StackRoutines.transferStacks, hs]
  simp [appendResult, transferred, StackRoutines.transferStacks, h863, h862, h89]

theorem prepared_stacks (a : Data) (i : Fin 896) :
    (prepared a).stacks i = if i = 5 then a.stacks 194 else if i = 12 then a.stacks 202
      else if i = 39 then a.stacks 204 else if i = 89 then [] else a.stacks i := by
  by_cases h5 : i = 5
  · subst i; simp [prepared, copied, StackRoutines.copyStacks, NodeReadoutSpace.clearedMany_stack]
  by_cases h12 : i = 12
  · subst i; simp [prepared, copied, StackRoutines.copyStacks, NodeReadoutSpace.clearedMany_stack]
  by_cases h39 : i = 39
  · subst i; simp [prepared, copied, StackRoutines.copyStacks, NodeReadoutSpace.clearedMany_stack]
  by_cases h89 : i = 89
  · subst i; simp [prepared, copied, StackRoutines.copyStacks, NodeReadoutSpace.clearedMany_stack]
  simp [prepared, copied, StackRoutines.copyStacks, NodeReadoutSpace.clearedMany_stack,
    h5, h12, h39, h89]

theorem prepared_ready (a : Data)
    (modulus width degree dictionary zero marker taylor shape : List Bool)
    (hr : MasterReady a modulus width degree dictionary zero marker taylor shape) :
    NodeReadoutSpace.Ready (prepared a) modulus width degree dictionary zero marker taylor shape := by
  constructor
  · simpa [prepared_stacks] using hr.modulus
  · simpa [prepared_stacks] using hr.width
  · simpa [prepared_stacks] using hr.degree
  · simpa [prepared_stacks] using hr.dictionary
  · simpa [prepared_stacks] using hr.zero
  · simpa [prepared_stacks] using hr.marker
  · simpa [prepared_stacks] using hr.taylor
  · simpa [prepared_stacks] using hr.shape



theorem readout_scratch (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree dictionary zero marker taylor shape bits : List Bool)
    (hr : MasterReady a modulus width degree dictionary zero marker taylor shape) :
    (NodeReadoutSpace.result (prepared a) rr modulus width degree dictionary zero
      marker taylor shape bits).stacks 89 = [] :=
  NodeReadoutSpace.result_scratch _ rr _ _ _ _ _ _ _ _ _
    (prepared_ready a _ _ _ _ _ _ _ _ hr) 89 (by decide)

theorem readout_stream (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree dictionary zero marker taylor shape bits : List Bool)
    (hr : MasterReady a modulus width degree dictionary zero marker taylor shape) :
    (NodeReadoutSpace.result (prepared a) rr modulus width degree dictionary zero
      marker taylor shape bits).stacks 863 = a.stacks 863 := by
  rw [NodeReadoutSpace.result_frame _ rr _ _ _ _ _ _ _ _ _
    (prepared_ready a _ _ _ _ _ _ _ _ hr) 863 (by decide) (by decide)]
  simp [prepared_stacks]

theorem result_output (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree dictionary zero marker taylor shape bits : List Bool)
    (hr : MasterReady a modulus width degree dictionary zero marker taylor shape) :
    (result a rr modulus width degree dictionary zero marker taylor shape bits).stacks 863 =
      a.stacks 863 ++ bits := by
  unfold result
  rw [appendResult_stacks _ (readout_scratch a rr _ _ _ _ _ _ _ _ _ hr)]
  simp only [Function.update_of_ne (show (863 : Fin 896) ≠ 89 from by decide),
    Function.update_of_ne (show (863 : Fin 896) ≠ 862 from by decide), Function.update_self]
  rw [readout_stream a rr _ _ _ _ _ _ _ _ _ hr, NodeReadoutSpace.result_output]

theorem result_frame (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree dictionary zero marker taylor shape bits : List Bool)
    (hr : MasterReady a modulus width degree dictionary zero marker taylor shape)
    (i : Fin 896) (h5 : i ≠ 5) (h12 : i ≠ 12) (h39 : i ≠ 39)
    (h862 : i ≠ 862) (h863 : i ≠ 863) (hs : i ∉ NodeReadoutSpace.scratchPorts) :
    (result a rr modulus width degree dictionary zero marker taylor shape bits).stacks i =
      a.stacks i := by
  have h89 : i ≠ 89 := by
    intro hi
    subst i
    exact hs (by decide)
  unfold result
  rw [appendResult_stacks _ (readout_scratch a rr _ _ _ _ _ _ _ _ _ hr)]
  simp only [Function.update_of_ne h89, Function.update_of_ne h862, Function.update_of_ne h863]
  rw [NodeReadoutSpace.result_frame _ rr _ _ _ _ _ _ _ _ _
    (prepared_ready a _ _ _ _ _ _ _ _ hr) i h862 hs]
  simp only [prepared_stacks, h5, h12, h39, h89, ite_false]

theorem result_empty (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree dictionary zero marker taylor shape bits : List Bool)
    (hr : MasterReady a modulus width degree dictionary zero marker taylor shape)
    (i : Fin 896) (hi : i = 862 ∨ i ∈ NodeReadoutSpace.scratchPorts) :
    (result a rr modulus width degree dictionary zero marker taylor shape bits).stacks i = [] := by
  unfold result
  rw [appendResult_stacks _ (readout_scratch a rr _ _ _ _ _ _ _ _ _ hr)]
  by_cases h89 : i = 89
  · subst i; simp
  by_cases h862 : i = 862
  · subst i; simp
  have hs := hi.resolve_left h862
  have h863 : i ≠ 863 := by
    have hl := NodeReadoutSpace.scratchPorts_low hs
    intro he
    subst i
    change 88 ≤ 863 ∧ 863 < 128 at hl
    omega
  simp only [Function.update_of_ne h89, Function.update_of_ne h862, Function.update_of_ne h863]
  exact NodeReadoutSpace.result_scratch _ rr _ _ _ _ _ _ _ _ _
    (prepared_ready a _ _ _ _ _ _ _ _ hr) i hs

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeAppendSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_StreamResources
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Uniform storage rules for concrete streaming loops. A local runtime bound
is used only for one invocation whose entire initial storage is uniformly
bounded; neither bound depends on the number of loop iterations. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamResources

open BitProgram

/-- Summing the port bounds counts every simultaneously live buffer. -/
theorem dataBits_le_mul {r s l bound : ℕ} (c : Cfg r s l)
    (h : ∀ i, (c.stacks i).length ≤ bound) : dataBits c ≤ s * bound := by
  simpa [dataBits, stackBits] using Finset.sum_le_card_nsmul Finset.univ
    (fun i => (c.stacks i).length) bound (fun i _ => h i)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamResources
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryNodeFinish
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual node readout and loop continuation. The emitted coefficient stream
retains its order. Node temporaries are physically reclaimed before refreshing
the outer guard, and every completed node restores one fixed boundary bound. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeFinish

open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open MomentsProgram TruncatedRingProgram

theorem guarded_test (a : Data) (nodes : List (List Bool))
    (hc : a.stacks 301=Encoding.encodeList id nodes) :
    (guarded a).regs 37 = !nodes.isEmpty ∧ (guarded a).regs 38=true := by
  cases nodes <;> simp [guarded,readRegs,hc,Encoding.encodeList]

theorem finished_stacks (a : Data) : (finished a).stacks =
    Function.update (Function.update (Function.update a.stacks 78 []) 850 [])
      307 (true::a.stacks 307) := by
  funext i
  by_cases h307 : i=307
  · subst i
    simp [finished,guarded,advanced,NodeReadoutSpace.clearedMany_stack]
  by_cases h850 : i=850
  · subst i
    simp [finished,guarded,advanced,NodeReadoutSpace.clearedMany_stack]
  by_cases h78 : i=78
  · subst i
    simp [finished,guarded,advanced,NodeReadoutSpace.clearedMany_stack]
  simp [finished,guarded,advanced,NodeReadoutSpace.clearedMany_stack,h307,h850,h78]

theorem finished_index (a : Data) (index : ℕ) (hi : a.stacks 307=List.replicate index true) :
    (finished a).stacks 307=List.replicate (index+1) true := by
  simp [finished_stacks,hi,List.replicate_succ]

theorem finished_frame (a : Data) (i : Fin 896)
    (h78 : i≠78) (h850 : i≠850) (h307 : i≠307) :
    (finished a).stacks i=a.stacks i := by
  simp [finished_stacks,h78,h850,h307]

theorem finished_guard (a : Data) (nodes : List (List Bool))
    (hc : a.stacks 301=Encoding.encodeList id nodes) :
    (finished a).regs 37 = !nodes.isEmpty ∧ (finished a).regs 38=true := by
  apply guarded_test
  simpa [advanced,NodeReadoutSpace.clearedMany_stack] using hc

theorem result_frame (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree dictionary zero marker taylor shape bits : List Bool)
    (hr : NodeAppendSpace.MasterReady a modulus width degree dictionary zero marker taylor shape)
    (i : Fin 896) (hi : i ∉ touchedPorts) :
    (result a rr modulus width degree dictionary zero marker taylor shape bits).stacks i =
      a.stacks i := by
  simp only [touchedPorts, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, not_or] at hi
  rw [result, finished_frame _ i hi.1.2.2.2.1 hi.1.2.2.2.2.2.1 hi.1.2.2.2.2.1]
  exact NodeAppendSpace.result_frame a rr _ _ _ _ _ _ _ _ _ hr i
    hi.1.1 hi.1.2.1 hi.1.2.2.1 hi.1.2.2.2.2.2.2.1 hi.1.2.2.2.2.2.2.2 hi.2

theorem result_output (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree dictionary zero marker taylor shape bits : List Bool)
    (hr : NodeAppendSpace.MasterReady a modulus width degree dictionary zero marker taylor shape) :
    (result a rr modulus width degree dictionary zero marker taylor shape bits).stacks 863 =
      a.stacks 863 ++ bits := by
  rw [result, finished_frame _ 863 (by decide) (by decide) (by decide)]
  exact NodeAppendSpace.result_output a rr _ _ _ _ _ _ _ _ _ hr

theorem result_index (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree dictionary zero marker taylor shape bits : List Bool)
    (hr : NodeAppendSpace.MasterReady a modulus width degree dictionary zero marker taylor shape)
    (index : ℕ) (hi : a.stacks 307 = List.replicate index true) :
    (result a rr modulus width degree dictionary zero marker taylor shape bits).stacks 307 =
      List.replicate (index + 1) true := by
  apply finished_index
  exact (NodeAppendSpace.result_frame a rr _ _ _ _ _ _ _ _ _ hr 307
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hi

theorem result_guard (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree dictionary zero marker taylor shape bits : List Bool)
    (hr : NodeAppendSpace.MasterReady a modulus width degree dictionary zero marker taylor shape)
    (nodes : List (List Bool)) (hc : a.stacks 301 = Encoding.encodeList id nodes) :
    (result a rr modulus width degree dictionary zero marker taylor shape bits).regs 37 =
      !nodes.isEmpty ∧
    (result a rr modulus width degree dictionary zero marker taylor shape bits).regs 38 = true := by
  apply finished_guard
  exact (NodeAppendSpace.result_frame a rr _ _ _ _ _ _ _ _ _ hr 301
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hc

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeFinish
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryNodeReadout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual node dictionary is read into increasing Taylor coefficients,
appended to the interpolation stream, and reclaimed before the next node.
The dictionary witness, encoded result and resource trace are shared. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeReadout

open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog SubexpLiftRing SubexpQuarticRing
open LeafProgram MomentsProgram LayoutProgram TruncatedRingProgram QueryTupleState
open QueryPairCommit QueryReadyConstruction

private theorem coeff_getElem {R : Type*} [Semiring R] (xs : List R)
    (i : ℕ) (hi : i < xs.length) : PolynomialAlgorithm.coeff xs i = xs[i] := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i (by simpa using hi)

/-- Equal truncated coefficients identify the complete fixed-length list,
including retained zero coefficients. -/
theorem list_of_readout {R : Type*} [CommRing R] {J : ℕ}
    (xs : List R) (value : Truncated R J) (hl : xs.length=J)
    (hv : Truncated.ofPolynomial J (PolynomialAlgorithm.denote xs)=value) :
    xs=List.ofFn value.coeff := by
  apply List.ext_getElem (by simp [hl])
  intro i hi hj
  have hJ : i < J := by simpa [hl] using hi
  have hc := congrArg (fun v : Truncated R J => v.coeff ⟨i,hJ⟩) hv
  change (PolynomialAlgorithm.denote xs).coeff i=value.coeff ⟨i,hJ⟩ at hc
  rw [PolynomialAlgorithm.coeff_denote,coeff_getElem xs i hi] at hc
  simpa using hc

/-- Every readout cache comes from the actual retained query words. -/
theorem master_common {r Q n d : ℕ} {q : Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool}
    {P : ℕ} {a : Data}
    (h : CommonReady q node H high P a)
    (entries : List (Product.Entry n (baseWidth 3 q.p.t) d))
    (he : a.stacks 850=Product.bytes entries) :
    NodeAppendSpace.MasterReady a q.p.modulus.bits q.width (List.replicate d true)
      (Product.bytes entries) (RingProgram.flat q.p.ops.zeroRun.1)
      (List.replicate q.p.t true) (List.replicate q.J true) (List.replicate n true) :=
  ⟨h.modulus,h.width,h.degree,he,h.zero,h.precision,h.order,h.ambient⟩

/-- The produced native coefficient words represent exactly the node's
additive shared-marker readout, in increasing Taylor order. -/
theorem codes_value {r Q n d : ℕ} (q : Factor.Spec r Q n d)
    (entries : List (Product.Entry n (baseWidth 3 q.p.t) d))
    (hg : Good ∅ q.p.t q.J entries)
    (value : Truncated (q.p.model.O q.p.t) q.J)
    (hv : Dense.readout (rawValue q.p.t q.J q.p.ops.decode entries)=value) :
    let codes := MomentsReadoutProgram.outputCodes 3 q.p.t q.p.modulus q.p.cache
      entries q.p.t q.p.ops.zeroRun.1 0 q.J
    codes.length=q.J ∧ codes.map q.p.ops.decode=List.ofFn value.coeff := by
  dsimp only
  have hlist := MomentsReadoutProgram.outputCodes_denote 3 q.p.t q.p.modulus q.p.cache
    (LiftRing.of (q.p.model.F q.p.t)) (RingBasis.basis (q.p.model.F q.p.t))
    entries q.p.t q.J q.p.ops.zeroRun.1 hg.nodup q.p.ops.zero_correct
  have hlen := congrArg List.length hlist
  simp only [List.length_map,Moments.outputCoefficients_length] at hlen
  refine ⟨hlen,list_of_readout _ value (by simpa using hlen) ?_⟩
  have hread := readout_codes_dense 3 q.p.t q.p.modulus q.p.cache
    (LiftRing.of (q.p.model.F q.p.t)) (RingBasis.basis (q.p.model.F q.p.t))
    q.p.t q.J entries q.p.ops.zeroRun.1 hg.nodup q.p.ops.zero_correct
  exact hread.trans hv

/-- Read, serialize, append and finish one completed interpolation node.
All zero Taylor slots remain in the actual stream; the next node index and
cursor guard are updated by paid native instructions. -/
theorem run_common_oai {r Q n d : ℕ} (q : Factor.Spec r Q n d) (node : Fin Q)
    (H : Finset (Fin n)) (high : H → Bool)
    (P B index : ℕ) (a : Data)
    (hready : CommonReady q node H high P a)
    (value : Truncated (q.p.model.O q.p.t) q.J)
    (hvalue : NodeAccumulatorMeaning q value a)
    (remaining : List (List Bool))
    (hcursor : a.stacks 301=Encoding.encodeList id remaining)
    (hindex : a.stacks 307=List.replicate index true)
    (hb : ∀ i, (a.stacks i).length ≤ B)
    (hout : (a.stacks 863).length + q.J * (d * baseWidth 3 q.p.t) ≤ B)
    (hnext : index + 1 ≤ B) :
    ∃ steps b, ∃ codes : List (RingProgram.Code (Word (baseWidth 3 q.p.t)) d),
      Eval QueryNodeFinish.command steps a b ∧ codes.length=q.J ∧
      codes.map q.p.ops.decode=List.ofFn value.coeff ∧
      b.stacks 863=a.stacks 863++(codes.map RingProgram.flat).flatten ∧
      b.stacks 78=[] ∧ b.stacks 850=[] ∧ b.stacks 862=[] ∧
      (∀ i∈NodeReadoutSpace.scratchPorts,b.stacks i=[]) ∧
      b.stacks 307=List.replicate (index+1) true ∧
      b.regs 37= !remaining.isEmpty ∧ b.regs 38=true ∧
      (∀ i,i∉QueryNodeFinish.touchedPorts → b.stacks i=a.stacks i) ∧
      (∀ i, (b.stacks i).length ≤ B) ∧
      steps + 1 ≤ QueryNodeFinish.budget n (baseWidth 3 q.p.t) d q.p.t q.J B ∧
      Trace QueryNodeFinish.program (steps + 1)
        (a.withPC (some QueryNodeFinish.program.entry)) (b.withPC none) ∧
      ∀ (prefixSteps : ℕ) intermediate, prefixSteps ≤ steps + 1 →
        Trace QueryNodeFinish.program prefixSteps
          (a.withPC (some QueryNodeFinish.program.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          896 * B + QueryNodeFinish.budget n (baseWidth 3 q.p.t) d q.p.t q.J B := by
  obtain ⟨entries,h850,hgood,hmeaning⟩ := hvalue.entries
  have hr := master_common hready entries h850
  have hx : (a.stacks 307).length + 1 ≤ B := by simpa [hindex] using hnext
  obtain ⟨steps,rr,ht,he,hbits,hbound⟩ := QueryNodeFinish.command_eval
    3 q.p.t q.p.modulus q.p.cache entries hgood q.p.ops.zeroRun.1
    q.width (List.replicate d true) (List.replicate q.p.t true)
    (List.replicate q.J true) (List.replicate n true)
    (List.length_replicate ..) q.widthLength (List.length_replicate ..)
    (List.length_replicate ..) (List.length_replicate ..) a B hb hr hout hx
  let codes := MomentsReadoutProgram.outputCodes 3 q.p.t q.p.modulus q.p.cache
    entries q.p.t q.p.ops.zeroRun.1 0 q.J
  let bits := (codes.map RingProgram.flat).flatten
  let b := QueryNodeFinish.result a rr q.p.modulus.bits q.width (List.replicate d true)
    (Product.bytes entries) (RingProgram.flat q.p.ops.zeroRun.1)
    (List.replicate q.p.t true) (List.replicate q.J true) (List.replicate n true) bits
  have hc := codes_value q entries hgood value hmeaning
  have h78 : b.stacks 78=[] := by
    simp [b,QueryNodeFinish.result,QueryNodeFinish.finished_stacks]
  have hnode : b.stacks 850=[] := by
    simp [b,QueryNodeFinish.result,QueryNodeFinish.finished_stacks]
  have hempty (i : Fin 896) (hi : i=862 ∨ i∈NodeReadoutSpace.scratchPorts) :
      b.stacks i=[] := by
    have h78 : i≠78 := by
      rcases hi with rfl|hi
      · decide
      · have hh := NodeReadoutSpace.scratchPorts_low hi
        intro heq
        subst i
        change 88≤78 ∧ 78<128 at hh
        omega
    have h850 : i≠850 := by
      rcases hi with rfl|hi
      · decide
      · have hh := NodeReadoutSpace.scratchPorts_low hi
        intro heq
        subst i
        change 88≤850 ∧ 850<128 at hh
        omega
    have h307 : i≠307 := by
      rcases hi with rfl|hi
      · decide
      · have hh := NodeReadoutSpace.scratchPorts_low hi
        intro heq
        subst i
        change 88≤307 ∧ 307<128 at hh
        omega
    rw [show b.stacks i=(NodeAppendSpace.result a rr q.p.modulus.bits q.width
      (List.replicate d true) (Product.bytes entries) (RingProgram.flat q.p.ops.zeroRun.1)
      (List.replicate q.p.t true) (List.replicate q.J true) (List.replicate n true) bits).stacks i
      from QueryNodeFinish.finished_frame _ i h78 h850 h307]
    exact NodeAppendSpace.result_empty a rr _ _ _ _ _ _ _ _ _ hr i hi
  have hguard := QueryNodeFinish.result_guard a rr _ _ _ _ _ _ _ _ bits hr remaining hcursor
  refine ⟨steps,b,codes,he,hc.1,hc.2,
    QueryNodeFinish.result_output a rr _ _ _ _ _ _ _ _ _ hr,h78,hnode,
    hempty 862 (Or.inl rfl),fun i hi => hempty i (Or.inr hi),
    QueryNodeFinish.result_index a rr _ _ _ _ _ _ _ _ _ hr index hindex,
    hguard.1,hguard.2,QueryNodeFinish.result_frame a rr _ _ _ _ _ _ _ _ _ hr,
    hbound,ht,compiled_halt_trace he 850 863,?_⟩
  intro prefixSteps intermediate hle htrace i
  exact StructuredSpace.local_stack_bound QueryNodeFinish.program
    (StreamResources.dataBits_le_mul _ hb) prefixSteps intermediate (hle.trans ht) htrace i

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeReadout
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeReadout.run_common_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeReadout.run_common_oai
