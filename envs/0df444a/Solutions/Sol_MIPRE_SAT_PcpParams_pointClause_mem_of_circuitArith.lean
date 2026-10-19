-- Prove2me | solution 1 for MIPRE.SAT.PcpParams.pointClause_mem_of_circuitArith
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:27:26.240063+00:00
-- url     : https://prove2.me/submissions/a122b91d-6d64-422d-9ccf-054199c90d53

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/PcpCircuit.lean (solution of MIPRE.SAT.PcpParams.pointClause_mem_of_circuitArith);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Computability.Language
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Sign.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Relation
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_SAT_Succinct
import Definitions.Def_MIPRE_Foundations_SAT_Decoupled
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_SAT_Pcp
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Cslib_Foundations_Data_RelatesInSteps
import Definitions.Def_MIPRE_Cslib_Computability_Machines_Turing_MultiTape_Deterministic
import Definitions.Def_MIPRE_TM_MultiInput_Deterministic
import Definitions.Def_MIPRE_TM_CookLevin_Local
import Definitions.Def_MIPRE_Foundations_SAT_Tseitin
import Definitions.Def_MIPRE_TM_CookLevin_Tableau
import Definitions.Def_MIPRE_TM_Interp_Instr
import Definitions.Def_MIPRE_TM_Interp_Machine
import Definitions.Def_MIPRE_TM_CookLevin_Layout
import Definitions.Def_MIPRE_Foundations_SAT_InputRouting
import Definitions.Def_MIPRE_Foundations_SAT_CircuitArithmetization
import Definitions.Def_MIPRE_Foundations_LowDegree_FiniteVariables
import Definitions.Def_MIPRE_Foundations_SAT_FiniteCircuitArithmetization
import Definitions.Def_MIPRE_Foundations_LowDegree_ZeroBasis
import Definitions.Def_MIPRE_Foundations_SAT_PcpAlgebra
import Definitions.Def_MIPRE_Foundations_SAT_PcpBlocks
import Definitions.Def_MIPRE_TM_CookLevin_PcpClauses
import Definitions.Def_MIPRE_TM_CookLevin_PcpCircuit
import Theorems.Thm_MIPRE_SAT_Circuit_eval_routedArith_iff
import Theorems.Thm_MIPRE_SAT_Circuit_routedConsistent_iff
import Theorems.Thm_MIPRE_SAT_Circuit_valueAt_congr

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.SAT.Circuit
section
variable {V : Type*}
theorem WellFormed.inputsLt {C : Circuit} (h : C.WellFormed) : C.InputsLt := h.inputs_lt
end
end MIPRE.SAT.Circuit

namespace MIPRE.SAT.Circuit
section
variable {V : Type*}
theorem eval_congr (C : Circuit) (hin : C.InputsLt) (x x' : ℕ → Bool)
    (hx : ∀ i < C.inputs, x i = x' i) : C.eval x = C.eval x' := by
  unfold eval
  split_ifs
  · rfl
  · exact valueAt_congr C hin x x' hx _
end
end MIPRE.SAT.Circuit

namespace MIPRE.SAT.Circuit
section
/-- The routed consistency equations and the output literal characterize
acceptance, using exactly the original input and gate variables. -/
theorem eval_iff_routedConsistent (C : Circuit) (hne : C.gates ≠ []) (x : ℕ → Bool) :
    C.eval x = true ↔ ∃ w, C.RoutedConsistent x w ∧ w (C.size - 1) = true := by
  have hsize : 0 < C.size := List.length_pos_iff.mpr hne
  constructor
  · intro h
    refine ⟨C.valueAt x, (routedConsistent_iff C x _).mpr (by simp), ?_⟩
    simpa [Circuit.eval, hne, size] using h
  · rintro ⟨w, hw, ho⟩
    have hvals := (routedConsistent_iff C x w).mp hw
    rw [hvals _ (by omega)] at ho
    simpa [Circuit.eval, hne, size] using ho
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
noncomputable section
open MvPolynomial LowDegree
variable {F : Type*} [Field F]
theorem eval_finiteArith (C : Circuit) (z : Fin (C.inputs + C.size) → Bool) :
    MvPolynomial.eval (fun i => (ofBool (z i) : F)) C.finiteArith =
      MvPolynomial.eval (Sum.elim (fun i => ofBool (C.inputPart z i))
        (fun j => ofBool (C.gatePart z j))) C.routedArith := by
  apply eval_killCompl_eq
  · intro i
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · simp [inputPart]
      rfl
    · simp [gatePart]
      rfl
  · intro v hv
    cases v with
    | inl i =>
      have hi : ¬ i < C.inputs := by
        intro hi
        exact hv ⟨Fin.castAdd C.size ⟨i, hi⟩, wireEmbedding_input C ⟨i, hi⟩⟩
      simp [inputPart, hi, ofBool]
    | inr j =>
      have hj : ¬ j < C.size := by
        intro hj
        exact hv ⟨Fin.natAdd C.inputs ⟨j, hj⟩, wireEmbedding_gate C ⟨j, hj⟩⟩
      simp [gatePart, hj, ofBool]
end
end MIPRE.SAT.Circuit

namespace MIPRE.SAT.Circuit
noncomputable section
open MvPolynomial LowDegree
variable {F : Type*} [Field F]
variable [CharP F 2]
/-- The finite polynomial enforces all gate values and the output literal. -/
theorem eval_finiteArith_iff (C : Circuit) (hC : C.WellFormed)
    (z : Fin (C.inputs + C.size) → Bool) :
    MvPolynomial.eval (fun i => (ofBool (z i) : F)) C.finiteArith = 1 ↔
      C.RoutedConsistent (C.inputPart z) (C.gatePart z) ∧ C.gatePart z (C.size - 1) = true := by
  rw [eval_finiteArith, eval_routedArith_iff C hC]
end
end MIPRE.SAT.Circuit

namespace MIPRE.SAT.PcpParams
noncomputable section
open LowDegree MvPolynomial
variable {F : Type*} [Field F] [CharP F 2]
theorem eval_circuitArith (P : PcpParams) (C : Circuit) (h : C.inputs + C.size = P.m')
    (y : Fin P.m' → F) :
    eval y (P.circuitArith C h) = eval (y ∘ Fin.cast h) C.finiteArith := by
  simp only [circuitArith, MvPolynomial.eval_rename]
end
end MIPRE.SAT.PcpParams

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.SAT.PcpParams
open LowDegree MvPolynomial
variable {F : Type*} [Field F] [CharP F 2]
theorem _root_.solution (P : PcpParams) (C : Circuit) (hC : C.WellFormed)
    (hI : C.inputs = 5 * P.m + 5) (h : C.inputs + C.size = P.m')
    (y : Fin P.m' → Bool) (hy : eval (pt y) (P.circuitArith (F := F) C h) = 1) :
    P.pointClause y ∈ C.formula5 P.m P.m := by
  let u := y ∘ Fin.cast h
  have hu : eval (fun i => (ofBool (u i) : F)) C.finiteArith = 1 := by
    simpa [u, eval_circuitArith, pt, Function.comp_def] using hy
  have hv := (C.eval_finiteArith_iff hC u).mp hu
  have ha := (C.eval_iff_routedConsistent hC.nonempty (C.inputPart u)).mpr
    ⟨C.gatePart u, hv⟩
  change C.eval (fun j => (clauseInput5 P.m P.m (P.pointClause y)).getD j false) = true
  rw [clauseInput5_pointClause]
  rw [C.eval_congr hC.inputsLt (C.inputPart u) (fun j => (P.inputSlice y).getD j false) ?_] at ha
  · exact ha
  · intro j hj
    rw [inputSlice_getD P y j (by omega)]
    simp [Circuit.inputPart, hj, u]
end MIPRE.SAT.PcpParams
