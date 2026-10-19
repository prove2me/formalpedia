-- Prove2me | solution 1 for MIPRE.SAT.Circuit.evalBits_circuitBits_finite
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:47:33.763036+00:00
-- url     : https://prove2.me/submissions/7c2d40bb-393c-447b-975e-ffb2cdd3b265

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/CircuitFieldCorrect.lean (solution of MIPRE.SAT.Circuit.evalBits_circuitBits_finite);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryConstants
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_SAT_Tseitin
import Definitions.Def_MIPRE_Foundations_SAT_GateProg
import Definitions.Def_MIPRE_Foundations_SAT_InputRouting
import Definitions.Def_MIPRE_Foundations_SAT_InputRoutingProg
import Definitions.Def_MIPRE_Foundations_SAT_CircuitArithmetization
import Definitions.Def_MIPRE_Foundations_SAT_GateFieldEval
import Definitions.Def_MIPRE_Foundations_SAT_CircuitFieldEval
import Definitions.Def_MIPRE_Foundations_LowDegree_FiniteVariables
import Definitions.Def_MIPRE_Foundations_SAT_FiniteCircuitArithmetization
import Definitions.Def_MIPRE_Foundations_SAT_CircuitFieldCorrect
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_evalBits_mulReduce
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_evalBits_oneBits
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_length_mulReduce
import Theorems.Thm_MIPRE_SAT_Circuit_evalBits_factorBits

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.SAT.Circuit
section
open Cost LowDegree LowDegree.BinaryPolynomial
theorem evalBits_oneBits {R : Type*} [CommRing R] (z : R) (p : BitStr) (hp : p ≠ []) :
    BinaryPolynomial.evalBits z (oneBits p) = 1 := BinaryPolynomial.evalBits_oneBits z p hp
end
end MIPRE.SAT.Circuit

namespace MIPRE.LowDegree
noncomputable section
open MvPolynomial
open scoped Classical
variable {σ τ F : Type*} [CommRing F] {f : σ → τ} (hf : Function.Injective f)
/-- Evaluation after restriction equals evaluation at the zero extension. -/
theorem eval_killCompl (p : MvPolynomial τ F) (x : σ → F) :
    eval x (killCompl hf p) = eval (extendZero hf x) p := by
  have he : (eval x).comp (killCompl hf).toRingHom = eval (extendZero hf x) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro j
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        killCompl, aeval_X, eval_X, extendZero]
      split <;> simp
  exact RingHom.congr_fun he p
end
end MIPRE.LowDegree

namespace MIPRE.LowDegree
noncomputable section
open MvPolynomial
open scoped Classical
variable {σ τ F : Type*} [CommRing F] {f : σ → τ} (hf : Function.Injective f)
/-- A useful form of restriction correctness: any zero extension agrees. -/
theorem eval_killCompl_eq (p : MvPolynomial τ F) (x : σ → F) (y : τ → F)
    (hxy : ∀ i, y (f i) = x i) (hy : ∀ j, j ∉ Set.range f → y j = 0) :
    eval x (killCompl hf p) = eval y p := by
  rw [eval_killCompl]
  have he : extendZero hf x = y := by
    funext j
    by_cases hj : j ∈ Set.range f
    · obtain ⟨i, rfl⟩ := hj
      rw [extendZero_apply, hxy]
    · simp [extendZero, hj, hy j hj]
  rw [he]
end
end MIPRE.LowDegree

namespace MIPRE.SAT.Circuit
section
open Cost LowDegree LowDegree.BinaryPolynomial MvPolynomial Finset
theorem fieldPrefix_env (C : Circuit) (p : BitStr) (x w : List BitStr) (k : ℕ) :
    (C.fieldPrefix p x w k).1 = (p, x, w, C.fieldHistory w k) := by
  simpa [fieldPrefix] using
    (fold_fieldStep (C.fieldHistory w k) ((p, x, w, []), oneBits p)).1
end
end MIPRE.SAT.Circuit

namespace MIPRE.SAT.Circuit
section
open Cost LowDegree LowDegree.BinaryPolynomial MvPolynomial Finset
theorem fieldPrefix_succ (C : Circuit) (p : BitStr) (x w : List BitStr) (k : ℕ) :
    C.fieldPrefix p x w (k + 1) =
      fieldStep (C.fieldPrefix p x w k) (C.gates.getD k (.const false), w.getD k []) := by
  simp only [fieldPrefix, fieldHistory, List.range_succ, List.map_append,
    List.map_singleton, List.foldl_append, List.foldl_cons, List.foldl_nil]
end
end MIPRE.SAT.Circuit

namespace MIPRE.SAT.Circuit
section
open Cost LowDegree LowDegree.BinaryPolynomial MvPolynomial Finset
theorem fieldPrefix_width (C : Circuit) (p : BitStr) (x w : List BitStr) (k : ℕ) :
    (C.fieldPrefix p x w k).2.length = p.length := by
  induction k with
  | zero => exact length_oneBits p
  | succ k ih =>
    rw [fieldPrefix_succ]
    change (mulReduce _ _ _).length = p.length
    rw [show (C.fieldPrefix p x w k).1.1 = p from
      congrArg Prod.fst (fieldPrefix_env C p x w k)]
    exact length_mulReduce _ _ _ ih
end
end MIPRE.SAT.Circuit

namespace MIPRE.SAT.Circuit
section
open Cost LowDegree LowDegree.BinaryPolynomial MvPolynomial Finset
variable {F : Type*} [Field F] [CharP F 2]
/-- The accumulator is precisely the product of the factors already scanned. -/
theorem evalBits_fieldPrefix (C : Circuit) (hC : C.WellFormed) (z : F) (p : BitStr)
    (hp : p ≠ []) (hroot : z ^ p.length = BinaryPolynomial.evalBits z p)
    (x w : List BitStr) (hxlen : C.inputs ≤ x.length) (hwlen : C.size ≤ w.length)
    (hx : ∀ b ∈ x, b.length = p.length) (hw : ∀ b ∈ w, b.length = p.length)
    (k : ℕ) (hk : k ≤ C.size) :
    BinaryPolynomial.evalBits z (C.fieldPrefix p x w k).2 =
      ∏ j ∈ range k, MvPolynomial.eval
        (Sum.elim (fun i => BinaryPolynomial.evalBits z (x.getD i [])) (fun i => BinaryPolynomial.evalBits z (w.getD i [])))
        (C.consistencyFactor j) := by
  induction k with
  | zero => simpa [fieldPrefix, fieldHistory] using evalBits_oneBits z p hp
  | succ k ih =>
    rw [fieldPrefix_succ]
    change BinaryPolynomial.evalBits z (mulReduce _ _ _) = _
    rw [show (C.fieldPrefix p x w k).1 = (p, x, w, C.fieldHistory w k) from
      fieldPrefix_env C p x w k]
    rw [evalBits_mulReduce z p _ _ (fieldPrefix_width C p x w k) hroot,
      evalBits_factorBits C hC z p hp hroot x w hxlen hwlen hx hw k (by omega),
      ih (by omega), Finset.prod_range_succ]
end
end MIPRE.SAT.Circuit

namespace MIPRE.SAT.Circuit
section
open Cost LowDegree LowDegree.BinaryPolynomial MvPolynomial Finset
variable {F : Type*} [Field F] [CharP F 2]
/-- The executable coefficient-vector evaluator computes the complete routed
circuit polynomial at every correctly sized field point. -/
theorem evalBits_circuitBits (C : Circuit) (hC : C.WellFormed) (z : F) (p : BitStr)
    (hp : p ≠ []) (hroot : z ^ p.length = BinaryPolynomial.evalBits z p)
    (x w : List BitStr) (hxlen : C.inputs ≤ x.length) (hwlen : C.size ≤ w.length)
    (hx : ∀ b ∈ x, b.length = p.length) (hw : ∀ b ∈ w, b.length = p.length) :
    BinaryPolynomial.evalBits z (circuitBits p x w C.gates) =
      MvPolynomial.eval (Sum.elim (fun i => BinaryPolynomial.evalBits z (x.getD i []))
        (fun j => BinaryPolynomial.evalBits z (w.getD j []))) C.routedArith := by
  change BinaryPolynomial.evalBits z (mulReduce p (C.fieldPrefix p x w C.size).2
    (w.getD (C.size - 1) [])) = _
  rw [evalBits_mulReduce z p _ _ (fieldPrefix_width C p x w C.size) hroot,
    evalBits_fieldPrefix C hC z p hp hroot x w hxlen hwlen hx hw C.size le_rfl]
  simp [routedArith]
end
end MIPRE.SAT.Circuit

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.SAT.Circuit
open Cost LowDegree LowDegree.BinaryPolynomial MvPolynomial Finset
variable {F : Type*} [Field F] [CharP F 2]
theorem _root_.solution (C : Circuit) (hC : C.WellFormed) (z : F) (p : BitStr)
    (hp : p ≠ []) (hroot : z ^ p.length = BinaryPolynomial.evalBits z p)
    (x w : List BitStr) (hxlen : x.length = C.inputs) (hwlen : w.length = C.size)
    (hx : ∀ b ∈ x, b.length = p.length) (hw : ∀ b ∈ w, b.length = p.length) :
    BinaryPolynomial.evalBits z (circuitBits p x w C.gates) =
      MvPolynomial.eval
        (Fin.addCases (fun i => BinaryPolynomial.evalBits z (x.getD i []))
          (fun j => BinaryPolynomial.evalBits z (w.getD j []))) C.finiteArith := by
  rw [evalBits_circuitBits C hC z p hp hroot x w hxlen.ge hwlen.ge hx hw]
  symm
  apply eval_killCompl_eq
  · intro i
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · simp
    · simp
  · intro v hv
    cases v with
    | inl i =>
      have hi : ¬ i < C.inputs := by
        intro hi
        exact hv ⟨Fin.castAdd C.size ⟨i, hi⟩, wireEmbedding_input C ⟨i, hi⟩⟩
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : x.length ≤ i)]
    | inr j =>
      have hj : ¬ j < C.size := by
        intro hj
        exact hv ⟨Fin.natAdd C.inputs ⟨j, hj⟩, wireEmbedding_gate C ⟨j, hj⟩⟩
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : w.length ≤ j)]
end MIPRE.SAT.Circuit
