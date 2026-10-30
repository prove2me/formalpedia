-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.localScan_localFactor
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T03:41:20.92393+00:00
-- url     : https://prove2.me/submissions/cf434c81-6b2c-456a-964b-3602d51c4dc0

import Mathlib
import Definitions.Def_OAIQ081S022
import Definitions.Def_OAIQ081S063

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_TruncatedInverse
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Explicit finite geometric inversion and local CRT factors

The inverses in this file are finite polynomial expressions. Scalar inverses are
input data with multiplication certificates; no Bézout coefficients are chosen.
-/

noncomputable section

namespace SubexponentialSAT.TruncatedInverse

open Polynomial
open scoped BigOperators

variable {A : Type*} [CommRing A]

theorem trunc_degree_lt (D : ℕ) (f : A[X]) :
    (Truncation.trunc D f).degree < (D : ℕ) := by
  apply (degree_lt_iff_coeff_zero _ _).2
  intro n hn
  simp [Truncation.coeff_trunc, Nat.not_lt.mpr hn]

theorem X_pow_dvd_sub_trunc (D : ℕ) (f : A[X]) :
    (X : A[X]) ^ D ∣ f - Truncation.trunc D f := by
  rw [X_pow_dvd_iff]
  intro n hn
  simp [Truncation.coeff_trunc, hn]

/-- Coefficient truncation and monic remainder are the same operation. -/
theorem trunc_eq_modByMonic (D : ℕ) (f : A[X]) :
    Truncation.trunc D f = f %ₘ (X ^ D) := by
  nontriviality A
  have hself : Truncation.trunc D f %ₘ (X ^ D) = Truncation.trunc D f := by
    apply (modByMonic_eq_self_iff (monic_X.pow D)).2
    rw [degree_X_pow]
    exact trunc_degree_lt D f
  exact ((modByMonic_eq_of_dvd_sub (monic_X.pow D)
    (X_pow_dvd_sub_trunc D f)).trans hself).symm

end SubexponentialSAT.TruncatedInverse

end
end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpTruncatedGeometric
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Keeping every geometric-inverse intermediate below degree D preserves
the existing inverse formula. The loop itself is the already executable
`TruncatedInverse.geometricLoop`; these are its semantic invariants. -/

namespace SubexponentialSAT.SubexpTruncatedGeometric

open Polynomial
open scoped BigOperators

variable {R : Type*} [CommRing R]

theorem trunc_mul_trunc (D : ℕ) (P Q : Polynomial R) :
    Truncation.trunc D (Truncation.trunc D P * Truncation.trunc D Q) =
      Truncation.trunc D (P * Q) := by
  have h₁ := dvd_mul_of_dvd_right (TruncatedInverse.X_pow_dvd_sub_trunc D P) Q
  have h₂ := dvd_mul_of_dvd_right (TruncatedInverse.X_pow_dvd_sub_trunc D Q)
    (Truncation.trunc D P)
  have h : (X : Polynomial R) ^ D ∣ P * Q - Truncation.trunc D P * Truncation.trunc D Q := by
    convert dvd_add h₁ h₂ using 1
    all_goals try with_reducible_and_instances rfl
    ring
  rw [TruncatedInverse.trunc_eq_modByMonic D (Truncation.trunc D P * Truncation.trunc D Q),
    TruncatedInverse.trunc_eq_modByMonic D (P * Q)]
  exact (Polynomial.modByMonic_eq_of_dvd_sub (monic_X.pow D) h).symm

end SubexponentialSAT.SubexpTruncatedGeometric

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpLocalFactorAlgebra
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Algebraic interfaces for constructing a local CRT factor from node
differences and inverting its constant coefficient. -/

namespace SubexponentialSAT.SubexpLocalFactorAlgebra

open Polynomial
open scoped BigOperators

variable {A ι : Type*} [CommRing A] [Fintype ι] [DecidableEq ι]

theorem localFactor_eq_product (θ : ι → A) (D : ℕ) (i : ι) :
    TruncatedInverse.localFactor θ D i =
      ∏ j ∈ Finset.univ.erase i, (X + C (θ i - θ j)) ^ D := by
  simp [TruncatedInverse.localFactor, JetCRT.cofactor, JetCRT.nodePower,
    prod_comp, pow_comp, sub_eq_add_neg, add_assoc]

end SubexponentialSAT.SubexpLocalFactorAlgebra

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramCorrectionAlgebra
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The jet loop runs J times independently of the scalar precision t. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open Polynomial
open scoped BigOperators
open SubexponentialSAT.SubexpTruncatedGeometric

theorem truncatedPower_denote {S R : Type*} [CommRing R]
    (J : ℕ) (denote : S → R[X]) (mulOp : S → S → S)
    (hm : ∀ a b, denote (mulOp a b) = Truncation.trunc J (denote a * denote b))
    (factor seed : S) (F P : R[X])
    (hf : denote factor = Truncation.trunc J F)
    (hs : denote seed = Truncation.trunc J P) (n : ℕ) :
    denote ((fun a => mulOp a factor)^[n] seed) = Truncation.trunc J (P * F^n) := by
  induction n with
  | zero => simpa using hs
  | succ n ih =>
      rw [Function.iterate_succ_apply', hm, ih, hf, trunc_mul_trunc]
      simp only [pow_succ, mul_assoc]

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramDifference
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A physical inverse builder for a difference of two supplied nodes. The
residue exponent and nilpotence precision are the independent runtime inputs
209 and 212; no loop enumerates the lifted ring. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

theorem differenceValue_decode {C A : Type*} [Ring A]
    (decode : C → A) (mulOp addOp : C → C → C)
    (hm : ∀ a b, decode (mulOp a b) = decode a * decode b)
    (ha : ∀ a b, decode (addOp a b) = decode a + decode b)
    (theta other minusOne : C) (hn : decode minusOne = -1) :
    decode (differenceValue mulOp addOp theta other minusOne) = decode theta - decode other := by
  simp [differenceValue, ha, hm, hn, sub_eq_add_neg]

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNodeScanControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed traversal of flat node cells, skipping one unary-indexed node.
The included-node service is an actual command with an actual execution
contract. This file accounts for all reads, guards, index pops, and cleanup.
-/

namespace SubexponentialSAT.SubexpNodeScanControl

open BitProgram StructuredCalls SubexpConvolutionControl

variable {A C : Type*}

theorem run_after_skip (f : A → C → A) (cs : List C) (a : A) :
    (run f cs ⟨a, [], false⟩).value = cs.foldl f a := by
  induction cs generalizing a with
  | nil => rfl
  | cons c cs ih => simpa [run, next] using ih (f a c)

/-- The physical index/marker traversal includes exactly all nodes except the
indexed one. An out-of-range index simply includes all nodes. -/
theorem run_skip_index (f : A → C → A) (cs : List C) (skip : List Bool) (a : A) :
    (run f cs ⟨a, skip, true⟩).value = (cs.eraseIdx skip.length).foldl f a := by
  induction cs generalizing skip a with
  | nil => simp [run]
  | cons c cs ih =>
    cases skip with
    | nil => simpa [run, next] using run_after_skip f cs a
    | cons bit rest => simpa [run, next] using ih rest (f a c)

end SubexponentialSAT.SubexpNodeScanControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpLocalProductAlgebra
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The exact value schedule of the physical node/power loops gives the
same local cofactor as the general-ring CRT reconstruction theorem. -/

namespace SubexponentialSAT.SubexpLocalProductAlgebra

open Polynomial
open scoped BigOperators

theorem get_mul_prod_eraseIdx {M : Type*} [CommMonoid M]
    (xs : List M) (i : ℕ) (hi : i < xs.length) :
    xs[i] * (xs.eraseIdx i).prod = xs.prod := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
      cases i with
      | zero => rfl
      | succ i =>
          have hi' : i < xs.length := by simpa using hi
          change xs[i] * (a * (xs.eraseIdx i).prod) = a * xs.prod
          rw [mul_left_comm, ih i hi']

/-- Deleting the indexed node from the physical list yields exactly the
Finset cofactor product. Cancellation uses the coefficient shift by X^D,
which is injective over every commutative ring, including rings with zero
divisors. -/
theorem product_excluding_node {R : Type*} [CommRing R] {Q : ℕ}
    (theta : Fin Q → R) (D : ℕ) (i : Fin Q) :
    (((List.ofFn theta).eraseIdx i.val).map
      (fun x => (X + C (theta i - x)) ^ D)).prod =
      TruncatedInverse.localFactor theta D i := by
  classical
  let G : R → R[X] := fun x => (X + C (theta i - x)) ^ D
  have hi : i.val < ((List.ofFn theta).map G).length := by simp
  have hs := get_mul_prod_eraseIdx ((List.ofFn theta).map G) i.val hi
  have hget : ((List.ofFn theta).map G)[i.val] = (X : R[X]) ^ D := by
    simp [G]
  have htotal : ((List.ofFn theta).map G).prod = ∏ j, G (theta j) := by
    rw [List.map_ofFn, List.prod_ofFn]
    rfl
  rw [hget, List.eraseIdx_map, htotal] at hs
  have ht : (X : R[X]) ^ D * (∏ j ∈ Finset.univ.erase i, G (theta j)) = ∏ j, G (theta j) := by
    simpa [G] using Finset.mul_prod_erase Finset.univ (fun j => G (theta j)) (Finset.mem_univ i)
  rw [SubexpLocalFactorAlgebra.localFactor_eq_product]
  change (((List.ofFn theta).eraseIdx i.val).map G).prod = ∏ j ∈ Finset.univ.erase i, G (theta j)
  ext k
  have hc := congrArg (fun p : R[X] => p.coeff (k + D)) (hs.trans ht.symm)
  simpa only [coeff_X_pow_mul] using hc

end SubexponentialSAT.SubexpLocalProductAlgebra

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramScanAlgebra
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open Polynomial
open scoped BigOperators

section
variable {CodeC S R : Type*} [CommRing R]
variable (decode : CodeC → R) (denote : S → R[X]) (cm ca : CodeC → CodeC → CodeC) (pm : S → S → S)
variable (hm : ∀ a b, decode (cm a b) = decode a * decode b)
variable (ha : ∀ a b, decode (ca a b) = decode a + decode b)
variable (J : ℕ) (linear : CodeC → S)
variable (hp : ∀ a b, denote (pm a b) = Truncation.trunc J (denote a * denote b))
variable (hl : ∀ a, denote (linear a) = Truncation.trunc J (X + C (decode a)))
variable (theta minusOne : CodeC) (hn : decode minusOne = -1)
include hm ha hp hl hn

theorem localUpdate_denote (acc : S) (P : R[X])
    (hacc : denote acc = Truncation.trunc J P) (c : CodeC) :
    denote (localUpdate cm ca pm linear theta minusOne J acc c) =
      Truncation.trunc J (P * (X + C (decode theta - decode c))^J) := by
  apply truncatedPower_denote J denote pm hp _ acc _ P _ hacc J
  rw [hl, differenceValue_decode decode cm ca hm ha theta c minusOne hn]

theorem localFold_denote (cs : List CodeC) (acc : S) (P : R[X])
    (hacc : denote acc = Truncation.trunc J P) :
    denote (cs.foldl (localUpdate cm ca pm linear theta minusOne J) acc) =
      Truncation.trunc J (P * (cs.map (fun c => (X + C (decode theta - decode c))^J)).prod) := by
  induction cs generalizing acc P with
  | nil => simpa using hacc
  | cons c cs ih =>
      rw [List.foldl_cons]
      have hnext := localUpdate_denote decode denote cm ca pm hm ha J linear hp hl
        theta minusOne hn acc P hacc c
      rw [ih _ _ hnext]
      simp only [List.map_cons, List.prod_cons, mul_assoc]

theorem localScan_denote (cs : List CodeC) (skip : List Bool) (one : S)
    (hone : denote one = Truncation.trunc J 1) :
    denote (SubexpNodeScanControl.run (localUpdate cm ca pm linear theta minusOne J)
      cs ⟨one,skip,true⟩).value =
      Truncation.trunc J ((cs.eraseIdx skip.length).map
        (fun c => (X + C (decode theta - decode c))^J)).prod := by
  rw [SubexpNodeScanControl.run_skip_index]
  simpa only [one_mul] using localFold_denote decode denote cm ca pm hm ha J linear hp hl
    theta minusOne hn (cs.eraseIdx skip.length) one 1 hone

theorem localScan_localFactor_oai {Q : ℕ} (nodes : Fin Q → CodeC) (i : Fin Q)
    (skip : List Bool) (hskip : skip.length = i.val) (one : S)
    (hone : denote one = Truncation.trunc J 1) :
    denote (SubexpNodeScanControl.run (localUpdate cm ca pm linear (nodes i) minusOne J)
      (List.ofFn nodes) ⟨one,skip,true⟩).value =
      Truncation.trunc J (TruncatedInverse.localFactor (fun j => decode (nodes j)) J i) := by
  rw [localScan_denote decode denote cm ca pm hm ha J linear hp hl
    (nodes i) minusOne hn (List.ofFn nodes) skip one hone, hskip]
  congr 1
  have h := SubexpLocalProductAlgebra.product_excluding_node (fun j => decode (nodes j)) J i
  have hof : List.ofFn (fun j => decode (nodes j)) = (List.ofFn nodes).map decode := by
    rw [List.map_ofFn]
    rfl
  rw [hof, List.eraseIdx_map, List.map_map] at h
  exact h

end
end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.localScan_localFactor_oai.{u_1, u_2, u_3} := @OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.localScan_localFactor_oai.{u_1, u_2, u_3}
