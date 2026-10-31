-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.marked_step_value
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:14:36.963742+00:00
-- url     : https://prove2.me/submissions/db5b8044-2a32-47b5-b07b-9c7b7af8d8b6

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S181
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafProgram_AssignmentSemantics_selectedFactor_denote_at
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafProgram_AssignmentSemantics_selectedFactor_good
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_TruncatedRingProgram_product_dense

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramNormalize
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms



namespace SubexponentialSAT.SqrtLog.MomentsProgram.Normalize
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable {K R A : Type*} [DecidableEq K] [CommRing R] [AddCommMonoid A]

theorem insertCode_nodup (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ} (k : K)
    (x : RingProgram.Code (Word (baseWidth p t)) d)
    (seed : List (K × RingProgram.Code (Word (baseWidth p t)) d))
    (hn : (Squarefree.Sparse.keys seed).Nodup) :
    (Squarefree.Sparse.keys (Dictionary.insertCode p t M cache k x seed)).Nodup := by
  unfold Dictionary.insertCode
  have heq : Squarefree.Sparse.keys (Squarefree.Sparse.erase k seed) =
      (Squarefree.Sparse.keys seed).filter (fun j => decide (j ≠ k)) := by
    clear hn
    induction seed with
    | nil => rfl
    | cons a seed ih =>
      by_cases h : a.1=k <;> simpa [Squarefree.Sparse.erase,Squarefree.Sparse.keys,h] using ih
  have he : (Squarefree.Sparse.keys (Squarefree.Sparse.erase k seed)).Nodup := by
    rw [heq]
    exact hn.filter _
  have hnot : k ∉ Squarefree.Sparse.keys (Squarefree.Sparse.erase k seed) := by
    rw [heq]
    simp
  simp only [Squarefree.Sparse.keys,List.map_cons,List.map_reverse]
  exact List.nodup_cons.mpr ⟨by simpa [Squarefree.Sparse.keys] using hnot,
    by simpa [Squarefree.Sparse.keys] using he⟩

theorem run_nodup (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ}
    (source seed : List (K × RingProgram.Code (Word (baseWidth p t)) d))
    (hn : (Squarefree.Sparse.keys seed).Nodup) :
    (Squarefree.Sparse.keys (run p t M cache source seed)).Nodup := by
  induction source generalizing seed with
  | nil => exact hn
  | cons a source ih => exact ih _ (insertCode_nodup p t M cache a.1 a.2 seed hn)

end SubexponentialSAT.SqrtLog.MomentsProgram.Normalize


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeSparseProduct
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Squarefree

open scoped BigOperators

namespace Index

variable {V : Type*} [DecidableEq V]

theorem Valid.join {a b : Index V} (ha : a.Valid) (hb : b.Valid) : (a.join b).Valid :=
  (Finset.card_union_le _ _).trans (Nat.add_le_add ha hb)

end Index

end SubexponentialSAT.SqrtLog.Squarefree

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramHash
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Sparse clause-circuit evaluation for one hash row

The input is a list of supplied nonzero coefficients and width-k clause lists.
The evaluator visits those lists directly; it never builds a truth table on the
union of the clause scopes. Counters include measured variable lookup and ring
callbacks. Their primitive realization is a separate obligation, not inferred
from these counters. `Algebra` also admits canonical truncated operations, whose
decoder need not be a homomorphism into the untruncated polynomial ring.
-/

namespace SubexponentialSAT.SqrtLog.LeafProgram

open SubexponentialSAT.SubexpSymbolicCost

variable {V C A : Type*}

section PolynomialSemantics

variable {R : Type*} [CommRing R]

theorem clauseValue_eq_eval (value : V → R) (ls : List (SAT.Literal V)) :
    clauseValue (ringAlgebra R) value ls = MvPolynomial.eval value (clausePolynomial ls) := by
  induction ls with
  | nil => simp [clauseValue, clausePolynomial, ringAlgebra]
  | cons l ls ih =>
      change literalValue (ringAlgebra R) value l * clauseValue (ringAlgebra R) value ls = _
      simp only [clausePolynomial, List.map_cons, List.prod_cons, map_mul]
      rw [ih]
      congr 1
      cases hp : l.positive <;>
        simp [literalValue, ringAlgebra, HashInput.falsifyingLiteral, hp, sub_eq_add_neg]

theorem rowValue_eq_eval (decode : C → R) (value : V → R) (terms : SparseRow V C) :
    rowValue (ringAlgebra R) decode value terms =
      MvPolynomial.eval value (rowPolynomial decode terms) := by
  induction terms with
  | nil => simp [rowValue, rowPolynomial, ringAlgebra]
  | cons term terms ih =>
      rcases term with ⟨c, ls⟩
      change decode c * clauseValue (ringAlgebra R) value ls +
        rowValue (ringAlgebra R) decode value terms = _
      rw [clauseValue_eq_eval, ih]
      simp [rowPolynomial]

end PolynomialSemantics
end SubexponentialSAT.SqrtLog.LeafProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramLift
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Integer representative lifting of the ternary selector coefficients.
Only reduction is a ring homomorphism. The lift itself is a finite choice of
0, 1, or 2, and no ring homomorphism from `ZMod 3` into the thickened ring is
assumed. All statements use the supplied irreducible polynomial. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram

section Naturality
variable {V C R S : Type*} [CommRing R] [CommRing S]

theorem map_literalValue (rho : R →+* S) (value : V → R) (l : SAT.Literal V) :
    rho (literalValue (ringAlgebra R) value l) =
      literalValue (ringAlgebra S) (fun v => rho (value v)) l := by
  cases hp : l.positive <;> simp [literalValue, ringAlgebra, hp]

theorem map_clauseValue (rho : R →+* S) (value : V → R) (ls : List (SAT.Literal V)) :
    rho (clauseValue (ringAlgebra R) value ls) =
      clauseValue (ringAlgebra S) (fun v => rho (value v)) ls := by
  induction ls with
  | nil => simp [clauseValue, ringAlgebra]
  | cons l ls ih =>
      change rho (literalValue (ringAlgebra R) value l * clauseValue (ringAlgebra R) value ls) =
        literalValue (ringAlgebra S) (fun v => rho (value v)) l *
          clauseValue (ringAlgebra S) (fun v => rho (value v)) ls
      rw [map_mul, map_literalValue, ih]

theorem map_rowValue (rho : R →+* S) (decode : C → R) (value : V → R)
    (terms : SparseRow V C) :
    rho (rowValue (ringAlgebra R) decode value terms) =
      rowValue (ringAlgebra S) (fun c => rho (decode c)) (fun v => rho (value v)) terms := by
  induction terms with
  | nil => simp [rowValue, ringAlgebra]
  | cons term rest ih =>
      rcases term with ⟨c, ls⟩
      change rho (decode c * clauseValue (ringAlgebra R) value ls +
        rowValue (ringAlgebra R) decode value rest) =
        rho (decode c) * clauseValue (ringAlgebra S) (fun v => rho (value v)) ls +
          rowValue (ringAlgebra S) (fun c => rho (decode c)) (fun v => rho (value v)) rest
      rw [map_add, map_mul, map_clauseValue, ih]

end Naturality

end SubexponentialSAT.SqrtLog.LeafProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsSparse
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Executable support extraction for the normalized sparse squarefree jets.
Projection erases X after extracting one requested support, leaving U and Z.
All operations preserve the same bounded sparse representation. -/

namespace SubexponentialSAT.SqrtLog.Moments

open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree
open scoped BigOperators

variable {V R : Type*} [DecidableEq V] [CommSemiring R]

theorem ringScalar_eq_atom (c : R) :
    ringScalar (V := V) c = Sparse.atom Index.origin c := by
  simp [ringScalar, Sparse.atom, Index.origin]

end SubexponentialSAT.SqrtLog.Moments

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramProductSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsProgram.Product
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open scoped BigOperators

variable {R : Type*} [CommRing R]

theorem run_nodup (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {n d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (u J : ℕ)
    (left right seed : List (Entry n (baseWidth p t) d))
    (hn : (Squarefree.Sparse.keys seed).Nodup) :
    (Squarefree.Sparse.keys (run p t M cache table u J left right seed)).Nodup := by
  induction left generalizing seed with
  | nil => exact hn
  | cons a left ih =>
    exact ih _ (Normalize.run_nodup p t M cache _ seed hn)

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

namespace Normalize
variable {K : Type*} [DecidableEq K]

theorem insertCode_preserves_keys (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ} (P : K → Prop) (k : K)
    (x : RingProgram.Code (Word (baseWidth p t)) d)
    (seed : List (K × RingProgram.Code (Word (baseWidth p t)) d))
    (hk : P k) (hs : ∀ a ∈ seed, P a.1) :
    ∀ a ∈ Dictionary.insertCode p t M cache k x seed, P a.1 := by
  intro a ha
  simp only [Dictionary.insertCode,List.mem_cons,List.mem_reverse] at ha
  rcases ha with rfl|ha
  · exact hk
  · exact hs a (List.mem_filter.mp ha).1

theorem run_preserves_keys (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ} (P : K → Prop)
    (source seed : List (K × RingProgram.Code (Word (baseWidth p t)) d))
    (hs : ∀ a ∈ source, P a.1) (hi : ∀ a ∈ seed, P a.1) :
    ∀ a ∈ run p t M cache source seed, P a.1 := by
  induction source generalizing seed with
  | nil => exact hi
  | cons a source ih =>
    apply ih _ (fun b hb => hs b (by simp [hb]))
    exact insertCode_preserves_keys p t M cache P a.1 a.2 seed (hs a (by simp)) hi
end Normalize

namespace Product

theorem keptJoin_valid {n B d : ℕ} (vars : Finset (Fin n)) (u J : ℕ)
    (a : Squarefree.Index (Fin n)) (entries : List (Entry n B d))
    (ha : a.Valid ∧ a.vars ⊆ vars) (he : ∀ b ∈ entries, ValidKey vars u J b.1) :
    ∀ b ∈ keptJoin a u J entries, ValidKey vars u J b.1 := by
  induction entries with
  | nil => intro b hb; simp [keptJoin] at hb
  | cons b entries ih =>
    intro c hc
    have hb := he b (by simp)
    have ht := ih (fun c hc => he c (by simp [hc]))
    by_cases h : (a.join b.1).Kept u J
    · simp only [keptJoin,h,ite_true, if_true,List.mem_cons] at hc
      rcases hc with rfl|hc
      · exact ⟨h,ha.1.join hb.2.1,Finset.union_subset ha.2 hb.2.2⟩
      · exact ht c hc
    · simp only [keptJoin,h,ite_false] at hc
      exact ht c hc

theorem block_valid (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {n d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (vars : Finset (Fin n)) (u J : ℕ)
    (a : Entry n (baseWidth p t) d) (right : List (Entry n (baseWidth p t) d))
    (ha : ValidKey vars u J a.1) (hr : ∀ b ∈ right, ValidKey vars u J b.1) :
    ∀ b ∈ block p t M cache table u J a right, ValidKey vars u J b.1 := by
  intro b hb
  have h := keptJoin_valid vars u J a.1
    (Squarefree.ScaleProgram.scaled p t M cache table a.2 right) ha.2
    (by intro c hc; obtain ⟨e,he,rfl⟩ := List.mem_map.mp hc; exact hr e he)
  exact h b (by simpa [block] using hb)

theorem run_valid (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {n d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (vars : Finset (Fin n)) (u J : ℕ)
    (left right seed : List (Entry n (baseWidth p t) d))
    (hl : ∀ a ∈ left, ValidKey vars u J a.1)
    (hr : ∀ b ∈ right, ValidKey vars u J b.1) (hi : ∀ b ∈ seed, ValidKey vars u J b.1) :
    ∀ b ∈ run p t M cache table u J left right seed, ValidKey vars u J b.1 := by
  induction left generalizing seed with
  | nil => exact hi
  | cons a left ih =>
    apply ih _ (fun b hb => hl b (by simp [hb]))
    exact Normalize.run_preserves_keys p t M cache (ValidKey vars u J) _ seed
      (block_valid p t M cache table vars u J a right (hl a (by simp)) hr) hi

end Product
end SubexponentialSAT.SqrtLog.MomentsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ResidualEmbeddingSource
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Original literal identifiers may differ from the residual formal-variable
type. High-variable literals are branch constants, and the sparse row circuit
commutes with padding the remaining formal supports into ambient masks. -/
namespace SubexponentialSAT.SqrtLog.ResidualEmbedding

open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree LeafProgram
noncomputable section

variable {I V W R : Type*} [DecidableEq V] [DecidableEq W] [CommRing R]

theorem scalarJet_eq_ringScalar (c : R) :
    scalarJet (V := V) c = Moments.ringScalar c :=
  (Moments.ringScalar_eq_atom c).symm

end
end SubexponentialSAT.SqrtLog.ResidualEmbedding

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNativeSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Validity and storage bounds for the actual raw dictionaries produced by
native hash-row execution. No canonical-output premise is used. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram
open HashCircuitProgram
open HashCircuitProgram.Native

variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
variable (cache : RingProgram.ScalarCache p t) {n d : ℕ}
variable (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
variable (vars : Finset (Fin n)) (u J : ℕ)

theorem product_good (left right : List (Product.Entry n (baseWidth p t) d))
    (hl : Good vars u J left) (hr : Good vars u J right) :
    Good vars u J (Product.run p t M cache table u J left right []) :=
  ⟨Product.run_valid p t M cache table vars u J left right [] hl.valid hr.valid (by simp),
    Product.run_nodup p t M cache table u J left right [] (by simp [Squarefree.Sparse.keys])⟩

end SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics


/-! Denotation of the concrete raw row recurrence used by the native program. -/


/-! Instantiation at the actual supplied-polynomial unramified ring. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram
open HashCircuitProgram
open HashCircuitProgram.Native
open scoped BigOperators

theorem model_table_correct (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (i j : Fin d) :
    RingBasis.basis (a.F t) i * RingBasis.basis (a.F t) j =
      ∑ k, SubexponentialSAT.LiftRing.of (a.F t) (wordValue 3 t (modelTable t a M cache i j k)) *
        RingBasis.basis (a.F t) k := by
  let _ : Fact (1 < 3^t) := ⟨Nat.one_lt_pow (Nat.ne_of_gt ht) (by decide)⟩
  rw [RingBasis.basis_mul (a.F t) (a.F_monic t ht) (a.F_degree t ht) i j]
  apply Finset.sum_congr rfl
  intro k _
  have hc : wordValue 3 t (modelTable t a M cache i j k) =
      RingBasis.structureConstant (a.F t) i j k := by
    change (RingProgram.scalarRing 3 t M cache).decode
      ((RingProgram.structureTableRun (RingProgram.scalarRing 3 t M cache).program
        (RingProgram.liftCoefficientsRun t a.coefficients).1).1 i j k) = _
    rw [RingProgram.structureTableRun_remainder (RingProgram.scalarRing 3 t M cache) hd]
    change (Polynomial.X ^ (i.val+j.val) %ₘ RingProgram.quotientPolynomial
      (RingProgram.scalarRing 3 t M cache) (RingProgram.liftCoefficientsRun t a.coefficients).1).coeff k = _
    rw [RingProgram.modelPolynomial t ht a M cache]
    all_goals rfl
  rw [hc]

end SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics


/-! Original literal identifiers remain unchanged when the native dictionaries
carry padded jets from the free coordinates of a branch. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsFinite
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Bridge from explicit head-assignment/support lists to finite-sum semantics.
The only enumeration requirements are no duplicates and exact membership.
The lists may be supplied by the primitive mask and bucket enumerators. -/

namespace SubexponentialSAT.SqrtLog.Moments

open scoped BigOperators
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree

variable {V G R : Type*} [DecidableEq V] [CommSemiring R]
  [Fintype G] [DecidableEq G] {X : G → Type*}
  [∀ g, Fintype (X g)] [∀ g, DecidableEq (X g)]
  {vars : Finset V} {t J : ℕ}

theorem ringScalar_constant (c : R) :
    ringScalar (V := V) c = jetScalar (jetConstant c) := by
  simp [ringScalar, jetScalar, jetConstant]

end SubexponentialSAT.SqrtLog.Moments

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeSemanticsFactors
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Polynomial naturality for the actual H-adic indicator expression. U
remains formal throughout; only its final retained coefficient sum is read. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics
open scoped BigOperators
open Polynomial
noncomputable section

variable {R : Type*} [CommRing R] {V : Type*} [DecidableEq V]

theorem jetEval_ringScalar (x : V → R) (hx : ∀ v, x v*x v=x v) (c : R) :
    Moments.jetEval x hx (Moments.ringScalar c) = Polynomial.C (Polynomial.C c) := by
  simp [Moments.jetEval,Moments.ringScalar,Squarefree.weight]

end
end SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeSemanticsCode
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The code-dependent expressions emitted by the actual assignment fold
are connected to the scalar U-expansion, without evaluating U at one. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics
open scoped BigOperators
open Polynomial
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open IdempotentApplyProgram.Steps (Context)
open AssignmentSemantics
noncomputable section

variable {p t n d : ℕ} [Fact p.Prime] {R : Type*} [CommRing R]

theorem indicatorPolynomial_eq (ctx : Context p t n d) (scalar : ZMod (p^t) →+* R)
    (code : RingProgram.Code (RingProgram.ScalarCode p t) (3*t))
    (H : Squarefree.Jet (Fin n) R) :
    AssignmentSemantics.indicatorPolynomial ctx scalar code H =
      indicatorJet t (codeDigits ctx scalar code) H := by
  have hu : Squarefree.Sparse.atom (IdempotentApplyProgram.Multiplier.uKey n) (1:R) =
      (Polynomial.X : Squarefree.Jet (Fin n) R) := by
    simp [Squarefree.Sparse.atom,IdempotentApplyProgram.Multiplier.uKey,
      show Squarefree.monomial (V:=Fin n) ∅ (1:R) = 1 from rfl,
      ← Polynomial.C_mul_X_pow_eq_monomial]
  simp only [AssignmentSemantics.indicatorPolynomial,indicatorJet,hu,codeDigits,
    Polynomial.eval₂_map]

end
end SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryJetSelected
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Exact dense semantics of the native selected-factor run after immediate
Boolean specialization. The common lifting marker remains through products. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryJetSemantics

open scoped BigOperators
open Polynomial OAI OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open LeafProgram LeafProgram.NodeSemantics
open IdempotentApplyProgram.Steps (Context)



section SpecializedNativeFactors

variable {R A : Type*} [CommRing R] [CommRing A]
  {p t n d : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
/-- The indicator only uses its scalar coefficients, shared marker, and input.
Thus two coefficient-ring maps agreeing on those data give the same value. -/
theorem indicatorJet_eval_congr
    (F G : Squarefree.Jet (Fin n) R →+* A)
    (hs : F.comp Moments.ringScalar = G.comp Moments.ringScalar)
    (hX : F Polynomial.X = G Polynomial.X)
    (t : ℕ) (digits : Fin t → R[X]) (a b : Squarefree.Jet (Fin n) R)
    (hab : F a = G b) : F (indicatorJet t digits a) = G (indicatorJet t digits b) := by
  unfold indicatorJet
  simp only [map_sum, map_mul, map_pow, Polynomial.hom_eval₂, hs, hX, hab,
    IdempotentProgram.hValue, map_sub, map_one, map_ofNat]

/-- Naturality of the actual selected expression, including marked violations
and neutral IDs, under maps that retain the common lifting marker. -/
theorem selectedValue_eval_congr (ctx : Context p t n d)
    (scalar : ZMod (p ^ t) →+* R) (basis : Fin d → R)
    (code : RingProgram.Code (RingProgram.ScalarCode p t) (3 * t))
    (F G : Squarefree.Jet (Fin n) R →+* A)
    (hs : ∀ c, F (Moments.ringScalar c) = G (Moments.ringScalar c))
    (hX : F Polynomial.X = G Polynomial.X)
    (left right : ℕ → Fin n → Squarefree.Jet (Fin n) R)
    (hjet : ∀ id v, F (left id v) = G (right id v))
    (hashes : List (List (HashCircuitProgram.Native.Row.WeightedClause n (baseWidth p t) d)))
    (marked : Bool) (clause : List (SAT.Literal (Fin n))) (id : ℕ) :
    F (AssignmentSemantics.selectedValue ctx scalar basis code left hashes marked clause id) =
      G (AssignmentSemantics.selectedValue ctx scalar basis code right hashes marked clause id) := by
  unfold AssignmentSemantics.selectedValue
  by_cases hi : id < hashes.length
  · simp only [dite_eq_left hi, indicatorPolynomial_eq]
    apply indicatorJet_eval_congr F G (RingHom.ext hs) hX
    rw [← rowValue_eq_eval (R := Squarefree.Jet (Fin n) R) scalarJet (left id),
      ← rowValue_eq_eval (R := Squarefree.Jet (Fin n) R) scalarJet (right id),
      LeafProgram.map_rowValue F scalarJet (left id),
      LeafProgram.map_rowValue G scalarJet (right id)]
    simp only [ResidualEmbedding.scalarJet_eq_ringScalar, hs, hjet]
  · simp only [dite_eq_right hi]
    split
    · rw [← clauseValue_eq_eval (R := Squarefree.Jet (Fin n) R) (left id),
        ← clauseValue_eq_eval (R := Squarefree.Jet (Fin n) R) (right id),
        LeafProgram.map_clauseValue F (left id), LeafProgram.map_clauseValue G (right id)]
      simp only [hjet]
    · simp only [map_one]

/-- The actual source expression computed from already-specialized incidence
jets has exactly the bounded dense value of the unspecialized expression. -/
theorem selectedValue_specialized_dense (ctx : Context p t n d)
    (scalar : ZMod (p ^ t) →+* R) (basis : Fin d → R)
    (code : RingProgram.Code (RingProgram.ScalarCode p t) (3 * t))
    (U : Fin n → Bool) (jet : ℕ → Fin n → Squarefree.Jet (Fin n) R)
    (hashes : List (List (HashCircuitProgram.Native.Row.WeightedClause n (baseWidth p t) d)))
    (marked : Bool) (clause : List (SAT.Literal (Fin n))) (id u J : ℕ) :
    TruncatedRingProgram.jetProjection u J
      (AssignmentSemantics.selectedValue ctx scalar basis code
        (fun id v => Moments.jetScalar (Moments.jetEval (Squarefree.boolValue U)
          (Squarefree.boolValue_idempotent U) (jet id v))) hashes marked clause id) =
      QueryEvaluation.specializeDense u J U
        (AssignmentSemantics.selectedValue ctx scalar basis code jet hashes marked clause id) := by
  apply selectedValue_eval_congr ctx scalar basis code
  · intro c
    change TruncatedRingProgram.jetProjection u J (Moments.ringScalar c) =
      Dense.ofPolynomial u J (Moments.jetEval (Squarefree.boolValue U)
        (Squarefree.boolValue_idempotent U) (Moments.ringScalar c))
    rw [jetEval_ringScalar]
    rw [Moments.ringScalar_constant, TruncatedRingProgram.jetProjection_jetScalar]
    rfl
  · simp [TruncatedRingProgram.jetProjection, QueryEvaluation.specializeDense,
      Squarefree.evalJet]
  · intro id v
    exact TruncatedRingProgram.jetProjection_jetScalar u J _

/-- One actual selected-factor multiplication extends an arbitrary valid
empty-support accumulator. Both the resulting validity and its dense value
refer to the same native product output. -/
theorem selectedFactor_step_specialized_dense (ctx : Context p t n d)
    (scalar : ZMod (p ^ t) →+* R) (basis : Fin d → R)
    (htable : ∀ i j, basis i * basis j =
      ∑ k, scalar (wordValue p t (ctx.table i j k)) * basis k)
    (hd : 0 < d) (hb : basis ⟨0, hd⟩ = 1) (hu : 0 < ctx.u) (hJ : 0 < ctx.J)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (one seed : AssignmentSemantics.Raw (p := p) (t := t) (n := n) (d := d))
    (incidence : ℕ → Fin n → AssignmentSemantics.Raw (p := p) (t := t) (n := n) (d := d))
    (hone : NativeSemantics.Good ∅ ctx.u ctx.J one)
    (hseed : NativeSemantics.Good ∅ ctx.u ctx.J seed)
    (hi : ∀ id v, NativeSemantics.Good ∅ ctx.u ctx.J (incidence id v))
    (hminus : RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache)
      scalar basis minus = -1)
    (honeval : NativeSemantics.rawDenote
      (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache) scalar basis)
      one = Squarefree.canonical ctx.u ctx.J 1)
    (U : Fin n → Bool) (jet : ℕ → Fin n → Squarefree.Jet (Fin n) R)
    (hashes : List (List (HashCircuitProgram.Native.Row.WeightedClause n (baseWidth p t) d)))
    (marked : Bool) (clause : List (SAT.Literal (Fin n))) (id : ℕ)
    (hhash : ∀ (h : id < hashes.length), ∀ w ∈ hashes[id], ∀ l ∈ w.literals,
      NativeSemantics.rawDenote
        (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache) scalar basis)
        (incidence id l.variable) = Squarefree.canonical ctx.u ctx.J
          (Moments.jetScalar (Moments.jetEval (Squarefree.boolValue U)
            (Squarefree.boolValue_idempotent U) (jet id l.variable))))
    (hmark : marked = true → id = hashes.length → ∀ l ∈ clause,
      NativeSemantics.rawDenote
        (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache) scalar basis)
        (incidence id l.variable) = Squarefree.canonical ctx.u ctx.J
          (Moments.jetScalar (Moments.jetEval (Squarefree.boolValue U)
            (Squarefree.boolValue_idempotent U) (jet id l.variable))))
    (code : RingProgram.Code (RingProgram.ScalarCode p t) (3 * t))
    (factor : AssignmentSemantics.Raw (p := p) (t := t) (n := n) (d := d))
    (hfactor : AssignmentSemantics.selectedFactor ctx minus one incidence hashes marked clause
      (List.ofFn (IdempotentApplyProgram.coefficientTriple t code)) id = some factor) :
    let output := MomentsProgram.Product.run p t ctx.modulus ctx.cache ctx.table
      ctx.u ctx.J seed factor []
    NativeSemantics.Good ∅ ctx.u ctx.J output ∧
      TruncatedRingProgram.rawValue ctx.u ctx.J
        (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache) scalar basis) output =
      TruncatedRingProgram.rawValue ctx.u ctx.J
        (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache) scalar basis) seed *
      QueryEvaluation.specializeDense ctx.u ctx.J U
        (AssignmentSemantics.selectedValue ctx scalar basis code jet hashes marked clause id) := by
  dsimp only
  have hg := AssignmentSemantics.selectedFactor_good ctx ∅ hu hJ minus one incidence hone hi
    hashes marked clause _ id factor hfactor
  refine ⟨NativeSemantics.product_good p t ctx.modulus ctx.cache ctx.table ∅ ctx.u ctx.J
    seed factor hseed hg, ?_⟩
  rw [TruncatedRingProgram.product_dense p t ctx.modulus ctx.cache scalar basis
    ctx.table htable ctx.u ctx.J seed factor]
  apply congrArg (fun value => TruncatedRingProgram.rawValue ctx.u ctx.J
    (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache) scalar basis) seed * value)
  have hv := AssignmentSemantics.selectedFactor_denote_at ctx scalar basis htable hd hb hu hJ
    ∅ minus one incidence hone hi hminus honeval
    (fun id v => Moments.jetScalar (Moments.jetEval (Squarefree.boolValue U)
      (Squarefree.boolValue_idempotent U) (jet id v)))
    hashes marked clause id hhash hmark code factor hfactor
  change TruncatedRingProgram.jetProjection ctx.u ctx.J (NativeSemantics.rawDenote _ factor) = _
  rw [hv, TruncatedRingProgram.jetProjection_canonical]
  exact selectedValue_specialized_dense ctx scalar basis code U jet hashes marked clause
    id ctx.u ctx.J

end SpecializedNativeFactors

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryJetSemantics
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One executed factor step, specialized to the actual source ring, its
computed multiplication table, and the three physical assignment masters. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Factor.Semantics
open SubexponentialSAT SubexpLiftRing SubexpQuarticRing
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open HashCircuitProgram HashCircuitProgram.Native
open LeafProgram.NativeSemantics LeafProgram.AssignmentSemantics
open scoped BigOperators

variable {r Q d n : ℕ}

theorem context_table_correct (p : SourceBank.Parameters r Q d) (u J : ℕ)
    (width : List Bool) (hw : width.length=baseWidth 3 p.t) (i j : Fin d) :
    RingBasis.basis (p.model.F p.t) i * RingBasis.basis (p.model.F p.t) j =
      ∑ k, LiftRing.of (p.model.F p.t)
        (wordValue 3 p.t ((sourceContext p n u J width hw).table i j k)) *
        RingBasis.basis (p.model.F p.t) k :=
  model_table_correct p.t p.ht p.hd p.model p.modulus p.cache i j

theorem basis_zero (p : SourceBank.Parameters r Q d) :
    RingBasis.basis (p.model.F p.t) (⟨0,p.hd⟩ : Fin d) = 1 := by
  simp [RingBasis.basis]

end SubexponentialSAT.SqrtLog.LeafProgram.Factor.Semantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramAssignmentConcrete
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The relational, actually executed assignment fold has the same value as
the selected-factor expression used by the node proof.  This bridge chooses
no raw representative and retains the shared U and T truncations. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.AssignmentConcrete

open SubexponentialSAT SubexpLiftRing SubexpQuarticRing MomentsProgram MomentsAssembly
open HashCircuitProgram HashCircuitProgram.Native
open scoped BigOperators

variable {r Q n d : ℕ}

/-- Dispatch agrees also on the marked ID and on every neutral ID.  Raw
tuple multiplicity is preserved in weightedHashes. -/
theorem value_eq_selectedValue (q : Factor.Spec r Q n d)
    (s : Fin 768 → List Bool) (id : ℕ) :
    q.value s id = AssignmentSemantics.selectedValue q.ctx
      (LiftRing.of (q.p.model.F q.p.t)) (RingBasis.basis (q.p.model.F q.p.t))
      q.code (sourceJets q s) (weightedHashes q) q.marked q.markedClause id := by
  unfold Factor.Spec.value AssignmentSemantics.selectedValue weightedHashes
  simp only [List.length_map]
  by_cases h : id < q.rows.length
  · simp only [dite_eq_left h, List.getElem_map]
    rfl
  · simp only [dite_eq_right h]
    split <;> rfl

end SubexponentialSAT.SqrtLog.LeafProgram.AssignmentConcrete

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorAssignmentCallbackNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete physical inputs for the streamed factor callback. The source
context is the actual q.ctx, and the dispatcher determines every selected row
and clause. These predicates contain stored words and finite size bounds only.
Their construction from the actual loader/cache run remains an integration step. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback
open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open SqrtLog SqrtLog.LeafProgram HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps MomentsProgram NativeSemantics
open FactorAssignmentProgram
open Subexp.ConstructivePacking MulticolorTypes LayoutProgram DensePolynomialProgram

noncomputable section

variable {r Q n d A S : ℕ} {q : Factor.Spec r Q n d}
  {one seed : FactorAssignmentLoop.Raw n (baseWidth 3 q.p.t) d}
  {a : FactorAssignmentProgram.Data} {f : ℕ}

/-- Dense multiplication for the same selected native factor. The source jet
uses all original factor IDs, but the concrete incidence family is the one
just produced for f; no table for other IDs is constructed or assumed. -/
theorem selected_step_value
    (s : Fin 768 → List Bool) (mask : List Bool)
    (incidence : Fin n → FactorAssignmentLoop.Raw n (baseWidth 3 q.p.t) d)
    (hone : NativeSemantics.Good ∅ q.u q.J one)
    (hseed : NativeSemantics.Good ∅ q.u q.J seed)
    (honeval : NativeSemantics.rawDenote q.p.ops.decode one =
      Squarefree.canonical q.u q.J 1)
    (hi : ∀ v, TruncatedRingProgram.Good ∅ q.u q.J (incidence v))
    (hinc : ∀ v, TruncatedRingProgram.rawDenote q.p.ops.decode (incidence v) =
      FactorTableDenotation.specializedJet q.u q.J mask
        (Factor.factorJet q.p q.ps q.packing n f v.val q.theta s))
    (factor : FactorAssignmentLoop.Raw n (baseWidth 3 q.p.t) d)
    (hfactor : AssignmentSemantics.selectedFactor q.ctx q.minus one (fun _ => incidence)
      (AssignmentConcrete.weightedHashes q) q.marked q.markedClause q.digits f = some factor) :
    let result := Product.run 3 q.p.t q.ctx.modulus q.ctx.cache q.ctx.table q.u q.J seed factor []
    NativeSemantics.Good ∅ q.u q.J result ∧
      TruncatedRingProgram.rawValue q.u q.J q.p.ops.decode result =
        TruncatedRingProgram.rawValue q.u q.J q.p.ops.decode seed *
          QueryEvaluation.specializeDense q.u q.J
            (fun v => decide (v ∈ Squarefree.decodeMask n mask)) (q.value s f) := by
  have scalarize {R : Type} [CommRing R] {m : ℕ} (u J : ℕ) (mask : List Bool)
      (jet : Squarefree.Jet (Fin m) R) :
      FactorTableDenotation.specializedJet u J mask jet =
        Squarefree.canonical u J (Moments.jetScalar (Moments.jetEval
          (Squarefree.boolValue (fun v => decide (v ∈ Squarefree.decodeMask m mask)))
          (Squarefree.boolValue_idempotent _) jet)) := by
    have hvalue : (fun v : Fin m => if v ∈ Squarefree.decodeMask m mask then (1 : R) else 0) =
        Squarefree.boolValue (fun v => decide (v ∈ Squarefree.decodeMask m mask)) := by
      funext v
      simp [Squarefree.boolValue]
    simp only [FactorTableDenotation.specializedJet, hvalue]
  have rawEq {R : Type} [CommRing R] {m B e : ℕ}
      (decode : RingProgram.Code (Word B) e → R) (entries : List (Product.Entry m B e)) :
      NativeSemantics.rawDenote decode entries = TruncatedRingProgram.rawDenote decode entries := rfl
  let U : Fin n → Bool := fun v => decide (v ∈ Squarefree.decodeMask n mask)
  have hjet (v : Fin n) : NativeSemantics.rawDenote q.p.ops.decode (incidence v) =
      Squarefree.canonical q.u q.J
        (Moments.jetScalar (Moments.jetEval (Squarefree.boolValue U)
          (Squarefree.boolValue_idempotent U)
          (AssignmentConcrete.sourceJets q s f v))) := by
    unfold AssignmentConcrete.sourceJets
    exact (rawEq (R := q.p.model.O q.p.t) q.p.ops.decode (incidence v)).trans ((hinc v).trans
      (scalarize (R := q.p.model.O q.p.t) (m := n) q.u q.J mask
        (Factor.factorJet q.p q.ps q.packing n f v.val q.theta s)))
  have hh := QueryJetSemantics.selectedFactor_step_specialized_dense q.ctx
    (LiftRing.of (q.p.model.F q.p.t)) (RingBasis.basis (q.p.model.F q.p.t))
    (Factor.Semantics.context_table_correct q.p q.u q.J q.width q.widthLength)
    q.p.hd (Factor.Semantics.basis_zero q.p) q.hu q.hJ q.minus one seed
    (fun _ => incidence) hone hseed (fun _ v => ⟨(hi v).valid, (hi v).nodup⟩)
    q.minusValue honeval U (AssignmentConcrete.sourceJets q s)
    (AssignmentConcrete.weightedHashes q) q.marked q.markedClause f
    (fun _ _ _ l _ => hjet l.variable) (fun _ _ l _ => hjet l.variable)
    q.code factor hfactor
  refine ⟨hh.1, hh.2.trans ?_⟩
  exact congrArg (fun value => TruncatedRingProgram.rawValue q.u q.J
    q.p.ops.decode seed * QueryEvaluation.specializeDense q.u q.J U value)
    (AssignmentConcrete.value_eq_selectedValue q s f).symm

/-- The marked branch retains the source clause's violation polynomial and
multiplies it into the same current seed. -/
theorem marked_step_value_oai
    (s : Fin 768 → List Bool) (mask : List Bool)
    (incidence : Fin n → FactorAssignmentLoop.Raw n (baseWidth 3 q.p.t) d)
    (hone : NativeSemantics.Good ∅ q.u q.J one)
    (hseed : NativeSemantics.Good ∅ q.u q.J seed)
    (honeval : NativeSemantics.rawDenote q.p.ops.decode one =
      Squarefree.canonical q.u q.J 1)
    (hi : ∀ v, TruncatedRingProgram.Good ∅ q.u q.J (incidence v))
    (hinc : ∀ v, TruncatedRingProgram.rawDenote q.p.ops.decode (incidence v) =
      FactorTableDenotation.specializedJet q.u q.J mask
        (Factor.factorJet q.p q.ps q.packing n f v.val q.theta s))
    (hm : q.marked = true) (hf : f = q.rows.length) :
    let factor := FactorServices.clauseResult q.ctx q.minus one incidence q.markedClause
    TruncatedRingProgram.rawValue q.u q.J q.p.ops.decode
      (Product.run 3 q.p.t q.ctx.modulus q.ctx.cache q.ctx.table q.u q.J seed factor []) =
      TruncatedRingProgram.rawValue q.u q.J q.p.ops.decode seed *
        QueryEvaluation.specializeDense q.u q.J
          (fun v => decide (v ∈ Squarefree.decodeMask n mask)) (q.value s f) := by
  apply (selected_step_value s mask incidence hone hseed honeval hi hinc _ ?_).2
  simp [AssignmentSemantics.selectedFactor, AssignmentConcrete.weightedHashes, hf, hm,
    FactorServices.clauseResult]

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.marked_step_value_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.marked_step_value_oai
