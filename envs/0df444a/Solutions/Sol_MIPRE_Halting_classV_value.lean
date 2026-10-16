-- Prove2me | solution 1 for MIPRE.Halting.classV_value
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-15T21:44:56.379149+00:00
-- url     : https://prove2.me/submissions/bd0add37-bc2b-4a78-ae04-aa7aef36c8b8

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Paper/ClassMain.lean (solution of MIPRE.Halting.classV_value);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Computability.Halting
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecBasis
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.RE
import Mathlib.Computability.TuringMachine.Config
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawInt
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_ValueApprox
import Definitions.Def_MIPRE_Foundations_ValueApprox_Cayley
import Definitions.Def_MIPRE_Foundations_ValueApprox_Projective
import Definitions.Def_MIPRE_Foundations_ValueApprox_Gaussian
import Definitions.Def_MIPRE_Foundations_ValueApprox_Norms
import Definitions.Def_MIPRE_Foundations_ValueApprox_Dense
import Definitions.Def_MIPRE_Foundations_ValueApprox_Strategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_HaltingGameValue
import Definitions.Def_MIPRE_Foundations_GameDescription
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawStrategy
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawSemantics
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawComplete
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawPrimrec
import Definitions.Def_MIPRE_Foundations_ValueApprox_RE
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Definitions.Def_MIPRE_Foundations_Cost_Kleene
import Definitions.Def_MIPRE_Foundations_Cost_Kleene_B
import Definitions.Def_MIPRE_Foundations_Cost_FromPartrec
import Definitions.Def_MIPRE_Foundations_Cost_FromPartrec_B
import Definitions.Def_MIPRE_Foundations_Cost_Partrec
import Definitions.Def_MIPRE_Foundations_Cost_Partrec_B
import Definitions.Def_MIPRE_Foundations_Cost_Semidecide
import Definitions.Def_MIPRE_Foundations_ClassMIPStarComputable
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_Halting_Freeze
import Definitions.Def_MIPRE_Foundations_Halting_Classes
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Cost_Numeric
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Halting_Wrapper
import Definitions.Def_MIPRE_Foundations_Halting_Enumerate
import Definitions.Def_MIPRE_Foundations_ClassMIPStar
import Definitions.Def_MIPRE_Foundations_Cost_BoundedEval
import Definitions.Def_MIPRE_Foundations_Halting_Tabulate
import Definitions.Def_MIPRE_Foundations_ClassMIPStarTab
import Definitions.Def_MIPRE_Foundations_Cost_BitQuery
import Definitions.Def_MIPRE_Foundations_Cost_Succinct
import Definitions.Def_MIPRE_Foundations_Cost_Clocked
import Definitions.Def_MIPRE_Foundations_Cost_Threshold
import Definitions.Def_MIPRE_Foundations_Compression
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Definitions.Def_MIPRE_Foundations_Cost_BinaryCompare
import Definitions.Def_MIPRE_Foundations_Cost_ManyOne
import Definitions.Def_MIPRE_Foundations_Cost_SizeProgram
import Definitions.Def_MIPRE_Foundations_Halting_PolyBounded
import Definitions.Def_MIPRE_Foundations_Halting_LambdaBound
import Definitions.Def_MIPRE_Foundations_Halting_Absorb
import Definitions.Def_MIPRE_Foundations_Halting_CostBudget
import Definitions.Def_MIPRE_Foundations_Halting_Instantiation
import Definitions.Def_MIPRE_Foundations_Halting_Serial
import Definitions.Def_MIPRE_Foundations_Halting_Semidecider
import Definitions.Def_MIPRE_Foundations_Halting_WrapperCost
import Definitions.Def_MIPRE_Foundations_Halting_Strings
import Definitions.Def_MIPRE_Foundations_Halting_Reduction
import Definitions.Def_MIPRE_Foundations_Halting_Compressor
import Definitions.Def_MIPRE_Foundations_Halting_Paper_TabulateL
import Definitions.Def_MIPRE_Foundations_Halting_Paper_Decider
import Definitions.Def_MIPRE_Foundations_Halting_Paper_Size
import Definitions.Def_MIPRE_Foundations_Halting_Paper_Cost
import Definitions.Def_MIPRE_Foundations_Halting_Paper_Induction
import Definitions.Def_MIPRE_Foundations_Halting_Paper_Stages
import Definitions.Def_MIPRE_Foundations_Halting_Paper_Build
import Definitions.Def_MIPRE_Foundations_Halting_Paper_Main
import Definitions.Def_MIPRE_Foundations_Halting_Paper_ClassVerifier
import Definitions.Def_MIPRE_Foundations_Halting_Paper_ClassMain
import Theorems.Thm_MIPRE_Halting_classV_game_mu
import Theorems.Thm_MIPRE_Halting_classV_game_support
import Theorems.Thm_MIPRE_Halting_decProg_accepts
import Theorems.Thm_MIPRE_TensorProductStrategy_value_relabel_invFun
import Theorems.Thm_MIPRE_TensorProductStrategy_value_relabel_of_support

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
open Matrix Kronecker
open scoped ComplexOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
/-- **Restriction to the support.** A game whose question distribution is supported on the
image of embeddings `X' ↪ X`, `Y' ↪ Y` has the quantum value of its restriction to
`X' × Y'`: the game `G'` with `G'.μ x' y' = G.μ (eX x') (eY y')` and
`G'.D x' y' = G.D (eX x') (eY y')`. -/
theorem quantumValue_restrictQuestions {X' Y' : Type*} [Fintype X'] [Fintype Y'] [Nonempty X']
    [Nonempty Y'] (G : Game X Y A B) (G' : Game X' Y' A B) (eX : X' ↪ X) (eY : Y' ↪ Y)
    (hμ : ∀ x' y', G'.μ x' y' = G.μ (eX x') (eY y'))
    (hμ0 : ∀ x y, G.μ x y ≠ 0 → (∃ x', eX x' = x) ∧ (∃ y', eY y' = y))
    (hD : ∀ x' y' a b, G'.D x' y' a b = G.D (eX x') (eY y') a b) :
    quantumValue G' = quantumValue G := by
  apply le_antisymm
  · refine Real.iSup_le (fun S' => ?_) (quantumValue_nonneg _)
    rw [← S'.value_relabel_invFun G eX eY hμ hμ0 hD]
    exact le_ciSup (TensorProductStrategy.bddAbove_range_value G) _
  · refine Real.iSup_le (fun S => ?_) (quantumValue_nonneg _)
    rw [← S.value_relabel_of_support G' eX eY hμ hμ0 hD]
    exact le_ciSup (TensorProductStrategy.bddAbove_range_value G') _
end MIPRE

namespace MIPRE
open Matrix Kronecker
open scoped ComplexOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
/-- The restriction of a game along question maps whose images carry the whole distribution:
the same distribution and decision predicate, pulled back. -/
noncomputable def Game.restrict {X' Y' : Type*} [Fintype X'] [Fintype Y'] (G : Game X Y A B)
    (eX : X' → X) (eY : Y' → Y) (h : ∑ x', ∑ y', G.μ (eX x') (eY y') = 1) :
    Game X' Y' A B where
  μ x' y' := G.μ (eX x') (eY y')
  μ_nonneg _ _ := G.μ_nonneg _ _
  μ_sum_one := h
  D x' y' a b := G.D (eX x') (eY y') a b
end MIPRE

namespace MIPRE.Halting
open Cost Cost.Prog Cost.PolyTimeFun CL Verifier
variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)
variable (Λ₀ K : ℕ) (R : PolyTimeFun BitStr Prog)
theorem cutz_le (z : BitStr) : cutz G Λ₀ K R z ≤ cutB G Λ₀ K R z.length := by
  unfold cutz cutB
  set D := G.bound.natDegree
  set lam := lamz Λ₀ R z
  have h1 : esize lam ≤ 4 * Nat.size lam + 1 := esize_nat_le _
  have h2 : 2 ^ Nat.size lam ≤ 2 * lam + 1 := two_pow_size_le _
  have h3 : lam ≤ lamB Λ₀ R z.length := lamz_le Λ₀ R z z.length le_rfl
  calc 2 ^ (K + D * esize lam) ≤ 2 ^ (K + D * (4 * Nat.size lam + 1)) :=
        Nat.pow_le_pow_right (by norm_num) (Nat.add_le_add_left (Nat.mul_le_mul_left D h1) K)
    _ = 2 ^ (K + D) * (2 ^ Nat.size lam) ^ (4 * D) := by
        rw [show K + D * (4 * Nat.size lam + 1) = (K + D) + Nat.size lam * (4 * D) by ring,
          pow_add, pow_mul]
    _ ≤ 2 ^ (K + D) * (2 * lam + 1) ^ (4 * D) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h2 _)
    _ ≤ 2 ^ (K + D) * (2 * lamB Λ₀ R z.length + 1) ^ (4 * D) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
end MIPRE.Halting

namespace MIPRE.Halting
open Cost Cost.Prog Cost.PolyTimeFun CL Verifier
variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)
variable (Λ₀ K : ℕ) (R : PolyTimeFun BitStr Prog)
theorem cutB_le (m : ℕ) : cutB G Λ₀ K R m ≤ (classP G U UT Λ₀ K R).eval m := by
  unfold classP; simp only [Polynomial.eval_add]
  have := (polyBounded_cutB G Λ₀ K R).le_poly_eval m; omega
end MIPRE.Halting

namespace MIPRE.Halting
open Cost Cost.Prog Cost.PolyTimeFun CL Verifier
variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)
variable (Λ₀ K : ℕ) (R : PolyTimeFun BitStr Prog)
theorem cutz_le_B (z : BitStr) : cutz G Λ₀ K R z ≤ (classV G U UT Λ₀ K R).B z :=
  (cutz_le G Λ₀ K R z).trans (cutB_le G U UT Λ₀ K R _)
end MIPRE.Halting

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Halting
open Cost Cost.Prog Cost.PolyTimeFun CL Verifier
variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)
variable (Λ₀ K : ℕ) (R : PolyTimeFun BitStr Prog)
theorem _root_.solution (z : BitStr) :
    quantumValue ((classV G U UT Λ₀ K R).game z) =
      (Vz G U UT Λ₀ R z).valStar (C G) (cutz G Λ₀ K R z) := by
  classical
  set V := classV G U UT Λ₀ K R with hV
  set W := Vz G U UT Λ₀ R z with hW
  set cut := cutz G Λ₀ K R z with hcut_def
  have hcut : cut ≤ V.B z := cutz_le_B G U UT Λ₀ K R z
  set ex := qEmb G U UT Λ₀ K R z with hex
  have hμ : ∀ x y : W.Questions (C G), (V.game z).μ (ex x) (ex y) = (W.game (C G) cut).μ x y :=
    classV_game_mu G U UT Λ₀ K R z
  have hsum : ∑ x, ∑ y, (V.game z).μ (ex x) (ex y) = 1 := by
    simp_rw [hμ]; exact (W.game (C G) cut).μ_sum_one
  set Gmid := (V.game z).restrict ex ex hsum with hGmid
  have h1 : quantumValue Gmid = quantumValue (V.game z) :=
    quantumValue_restrictQuestions (V.game z) Gmid ex ex (fun _ _ => rfl)
      (classV_game_support G U UT Λ₀ K R z) (fun _ _ _ _ => rfl)
  -- acceptance on the embedded questions
  have hacc : ∀ (x y : W.Questions (C G)) (a b : BitStr),
      V.Accepts z (toBits x) (toBits y) a b ↔
        a.length ≤ cut ∧ b.length ≤ cut ∧
          W.decider.Accepts (C G) (toBits x) (toBits y) a b :=
    fun x y a b => decProg_accepts G U UT Λ₀ K R z (toBits x) (toBits y) a b
  have h2 : quantumValue Gmid = quantumValue (W.game (C G) cut) := by
    refine quantumValue_extendAnswers (W.game (C G) cut) Gmid (Answers.castLE hcut)
      (Answers.castLE hcut) hμ ?_ ?_
    · intro x y a b
      show decide (V.Accepts z (toBits x) (toBits y) a.1 b.1) =
        decide (W.decider.Accepts (C G) (toBits x) (toBits y) a.1 b.1)
      simp only [decide_eq_decide]
      rw [hacc]
      exact ⟨fun h => h.2.2, fun h => ⟨a.2, b.2, h⟩⟩
    · intro x y a' b' h
      have h' : V.Accepts z (toBits x) (toBits y) a'.1 b'.1 := of_decide_eq_true h
      obtain ⟨ha, hb, -⟩ := (hacc x y a'.1 b'.1).1 h'
      exact ⟨⟨⟨a'.1, ha⟩, Subtype.ext rfl⟩, ⟨⟨b'.1, hb⟩, Subtype.ext rfl⟩⟩
  rw [Verifier.valStar, ← h2, h1]
end MIPRE.Halting
