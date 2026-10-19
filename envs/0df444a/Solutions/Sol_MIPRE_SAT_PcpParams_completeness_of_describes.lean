-- Prove2me | solution 1 for MIPRE.SAT.PcpParams.completeness_of_describes
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:28:44.653988+00:00
-- url     : https://prove2.me/submissions/d74c1bd1-9a78-4bad-816b-2325b1319df5

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/PcpCircuit.lean (solution of MIPRE.SAT.PcpParams.completeness_of_describes);
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
import Theorems.Thm_MIPRE_SAT_Circuit_degreeOf_routedArith_le
import Theorems.Thm_MIPRE_SAT_Circuit_eval_routedArith_bool
import Theorems.Thm_MIPRE_SAT_PcpAlgebra_exists_proof_of_satisfying_assignment
import Theorems.Thm_MIPRE_SAT_PcpParams_pointClause_mem_of_circuitArith

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
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

namespace MIPRE.LowDegree
noncomputable section
open MvPolynomial
open scoped Classical
variable {σ τ F : Type*} [CommRing F] {f : σ → τ} (hf : Function.Injective f)
/-- Restriction cannot increase the degree of any retained coordinate. -/
theorem degreeOf_killCompl_le (p : MvPolynomial τ F) (i : σ) :
    (killCompl hf p).degreeOf i ≤ p.degreeOf (f i) := by
  rw [← degreeOf_rename_of_injective hf i]
  simp only [degreeOf_eq_sup]
  exact Finset.sup_mono (support_rename_killCompl_subset hf)
end
end MIPRE.LowDegree

namespace MIPRE.SAT.Circuit
noncomputable section
open MvPolynomial LowDegree
variable {F : Type*} [Field F]
theorem degreeOf_finiteArith_le (C : Circuit) (hC : C.WellFormed)
    (i : Fin (C.inputs + C.size)) : (C.finiteArith (F := F)).degreeOf i ≤ 5 :=
  (degreeOf_killCompl_le C.wireEmbedding_injective C.routedArith i).trans
    (degreeOf_routedArith_le C hC _)
end
end MIPRE.SAT.Circuit

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
/-- Boolean-valuedness is retained on the exact finite coordinate set. -/
theorem eval_finiteArith_bool (C : Circuit) (hC : C.WellFormed)
    (z : Fin (C.inputs + C.size) → Bool) :
    MvPolynomial.eval (fun i => (ofBool (z i) : F)) C.finiteArith = 0 ∨
    MvPolynomial.eval (fun i => (ofBool (z i) : F)) C.finiteArith = 1 := by
  rw [eval_finiteArith]
  exact eval_routedArith_bool C hC _ _
end
end MIPRE.SAT.Circuit

namespace MIPRE.SAT.Clause5
section
open Cost LowDegree MvPolynomial
variable {V : Type*}
/-- The five Boolean disjuncts are precisely the satisfying-literal condition
in the algebraic PCP completeness and decoding lemmas. -/
theorem eval_iff_exists (c : Clause5 V V V V V) (a : Fin 5 → V → Bool) :
    c.eval (a 0) (a 1) (a 2) (a 3) (a 4) = true ↔
      ∃ i : Fin 5, a i (c.literals i).var = (c.literals i).pos := by
  simp only [Clause5.eval, Bool.or_eq_true, lit_true_iff]
  constructor
  · rintro ((((h | h) | h) | h) | h)
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩
    · exact ⟨4, h⟩
  · rintro ⟨i, hi⟩
    fin_cases i <;> simp_all [literals]
end
end MIPRE.SAT.Clause5

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

namespace MIPRE.SAT.PcpParams
noncomputable section
open LowDegree MvPolynomial
variable {F : Type*} [Field F] [CharP F 2]
theorem degreeOf_circuitArith (P : PcpParams) (C : Circuit) (hC : C.WellFormed)
    (h : C.inputs + C.size = P.m') (i : Fin P.m') :
    (P.circuitArith (F := F) C h).degreeOf i ≤ 5 := by
  have he : i = Fin.cast h (Fin.cast h.symm i) := by simp
  rw [he, circuitArith, degreeOf_rename_of_injective (Fin.cast_injective h)]
  exact C.degreeOf_finiteArith_le hC _
end
end MIPRE.SAT.PcpParams

namespace MIPRE.SAT.PcpParams
noncomputable section
open LowDegree MvPolynomial
variable {F : Type*} [Field F] [CharP F 2]
theorem eval_circuitArith_bool (P : PcpParams) (C : Circuit) (hC : C.WellFormed)
    (h : C.inputs + C.size = P.m') (y : Fin P.m' → Bool) :
    eval (pt y) (P.circuitArith (F := F) C h) = 0 ∨
      eval (pt y) (P.circuitArith (F := F) C h) = 1 := by
  rw [eval_circuitArith]
  exact C.eval_finiteArith_bool hC (y ∘ Fin.cast h)
end
end MIPRE.SAT.PcpParams

namespace MIPRE.SAT.PcpParams
noncomputable section
open LowDegree MvPolynomial
variable {F : Type*} [Field F] [CharP F 2]
/-- A satisfying tuple for the describer's formula supplies an honest degree-seven
PCP proof for the concrete circuit polynomial. -/
theorem exists_proof_of_formula5_sat (P : PcpParams) (C : Circuit) (hC : C.WellFormed)
    (hI : C.inputs = 5 * P.m + 5) (h : C.inputs + C.size = P.m')
    (a : Fin 5 → Fin (2 ^ P.m) → Bool)
    (ha : (C.formula5 P.m P.m).Sat (a 0) (a 1) (a 2) (a 3) (a 4)) :
    ∃ pf : PcpProof P F,
      (∀ i, pf.g i = ldEnc (fun u => ofBool (a i (cubeIndex u)))) ∧
      ∀ z, PcpAlgebra.TypedAccepts (P.circuitArith C h) z (pf.ev z) := by
  apply PcpAlgebra.exists_proof_of_satisfying_assignment
    (P.circuitArith C h) (fun j => (P.degreeOf_circuitArith C hC h j).trans (by decide))
    (P.eval_circuitArith_bool C hC h) (fun i u => a i (cubeIndex u))
  intro y hy
  have hs := ha _ (P.pointClause_mem_of_circuitArith C hC hI h y hy)
  obtain ⟨i, hi⟩ := (Clause5.eval_iff_exists (P.pointClause y) a).mp hs
  exact ⟨i, by simpa only [pointClause_literals] using hi⟩
end
end MIPRE.SAT.PcpParams

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.SAT.PcpParams
open LowDegree MvPolynomial
variable {F : Type*} [Field F] [CharP F 2]
theorem _root_.solution (P : PcpParams) (C : Circuit) (hC : C.WellFormed)
    (hI : C.inputs = 5 * P.m + 5) (h : C.inputs + C.size = P.m')
    (D : Decider) (n T : ℕ) (x y ap bp : Cost.BitStr)
    (hD : C.DescribesDecider P.m P.m D n x y T)
    (hap : ap.length ≤ T) (hbp : bp.length ≤ T)
    (hacc : D.AcceptsWithin n x y ap bp T) :
    ∃ pf : PcpProof P F,
      pf.g 0 = ldEnc (answerVec F P.m ap) ∧
      pf.g 1 = ldEnc (answerVec F P.m bp) ∧
      ∀ z, PcpAlgebra.TypedAccepts (P.circuitArith C h) z (pf.ev z) := by
  obtain ⟨w₁, w₂, w₃, hs⟩ := (hD (fun j => tapeBits ap j) (fun j => tapeBits bp j)).mpr
    ⟨ap, bp, hap, hbp, (fun _ => rfl), (fun _ => rfl), hacc⟩
  let a : Fin 5 → Fin (2 ^ P.m) → Bool :=
    ![fun j => tapeBits ap j, fun j => tapeBits bp j, w₁, w₂, w₃]
  obtain ⟨pf, hg, hv⟩ := P.exists_proof_of_formula5_sat (F := F) C hC hI h a hs
  refine ⟨pf, ?_, ?_, hv⟩
  · change pf.g 0 = ldEnc (fun u => ofBool (tapeBits ap (Cost.bitsVal (List.ofFn u))))
    exact hg 0
  · change pf.g 1 = ldEnc (fun u => ofBool (tapeBits bp (Cost.bitsVal (List.ofFn u))))
    exact hg 1
end MIPRE.SAT.PcpParams
