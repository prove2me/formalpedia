-- Prove2me | solution 1 for MIPRE.Halting.classV_values
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-15T22:04:45.636182+00:00
-- url     : https://prove2.me/submissions/c9bdfcc1-4f87-459f-9886-d658eb92fec2

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Paper/ClassMain.lean (solution of MIPRE.Halting.classV_values);
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
import Theorems.Thm_MIPRE_Halting_accepts_iff
import Theorems.Thm_MIPRE_Halting_classV_value
import Theorems.Thm_MIPRE_Halting_hasPerfectPCC_of_halts
import Theorems.Thm_MIPRE_Halting_valStar_le_of_not_halts

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
open Matrix Kronecker
open scoped ComplexOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
/-- The quantum value is at most one. -/
theorem quantumValue_le_one (G : Game X Y A B) : quantumValue G ≤ 1 :=
  Real.iSup_le (fun S => S.value_le_one) zero_le_one
end MIPRE

namespace MIPRE.Cost
open Polynomial
theorem evalWithin_isSome_iff (c : Prog) (v : Data) (k : ℕ) :
    (evalWithin c v k).isSome = true ↔ ∃ r t, t ≤ k ∧ c.Runs v r t := by
  unfold evalWithin
  split <;> simp_all
end MIPRE.Cost

namespace MIPRE.Game
open Matrix Kronecker
open scoped ComplexOrder
variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
/-- The one computation the doubling needs, in a form independent of what kind of strategy is
being summed: the four-fold sum over the doubled alphabets collapses to the original one, the
three blocks other than `(false, ·), (true, ·)` contributing zero. -/
theorem sum_doubled (G : Game X X A A) (f : (Bool × X) → (Bool × X) → A → A → ℝ) :
    (∑ p, ∑ q, ∑ a, ∑ b,
        G.doubled.μ p q * (if G.doubled.D p q a b then 1 else 0) * f p q a b)
      = ∑ x, ∑ y, ∑ a, ∑ b,
          G.μ x y * (if G.D x y a b then 1 else 0) * f (false, x) (true, y) a b := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, doubled_μ, doubled_D]
  simp
end MIPRE.Game

namespace MIPRE.TensorProductStrategy
open Matrix Kronecker
open scoped ComplexOrder
variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
theorem value_undouble {G : Game X X A A} (S : TensorProductStrategy G.doubled.toGame) :
    S.undouble.value = S.value := by
  rw [show S.value = ∑ p, ∑ q, ∑ a, ∑ b, G.doubled.μ p q *
      (if G.doubled.D p q a b then 1 else 0) *
      (star S.ψ ⬝ᵥ ((S.PA.M p a ⊗ₖ S.PB.M q b) *ᵥ S.ψ)).re from rfl,
    Game.sum_doubled]
  rfl
end MIPRE.TensorProductStrategy

namespace MIPRE.TensorProductStrategy
open Matrix Kronecker
open scoped ComplexOrder
variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
theorem value_double {G : Game X X A A} (S : TensorProductStrategy G) :
    S.double.value = S.value := by
  rw [show S.double.value = ∑ p, ∑ q, ∑ a, ∑ b, G.doubled.μ p q *
      (if G.doubled.D p q a b then 1 else 0) *
      (star S.ψ ⬝ᵥ ((S.PA.M p.2 a ⊗ₖ S.PB.M q.2 b) *ᵥ S.ψ)).re from rfl,
    Game.sum_doubled]
  rfl
end MIPRE.TensorProductStrategy

namespace MIPRE
open Matrix Kronecker
open scoped ComplexOrder
variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
/-- **The doubling preserves the quantum value.** Each direction is one strategy transported
and one `le_ciSup`; `TensorProductStrategy` carries no field mentioning the game, so `relabel`
is a bijection of the two index types of the supremum. -/
theorem quantumValue_doubled (G : Game X X A A) :
    quantumValue G.doubled.toGame = quantumValue G := by
  apply le_antisymm
  · refine Real.iSup_le (fun S => ?_) (quantumValue_nonneg _)
    rw [← S.value_undouble]
    exact le_ciSup (TensorProductStrategy.bddAbove_range_value G) S.undouble
  · refine Real.iSup_le (fun S => ?_) (quantumValue_nonneg _)
    rw [← S.value_double]
    exact le_ciSup (TensorProductStrategy.bddAbove_range_value G.doubled.toGame) S.double
end MIPRE

namespace MIPRE.Verifier
open Cost
variable {ℓ : ℕ} (V : Verifier ℓ)
/-- **The doubled game has the value it doubles**, with no synchronicity hypothesis. -/
theorem quantumValue_doubledGame (n T : ℕ) :
    quantumValue (V.doubledGame n T).toGame = V.valStar n T :=
  quantumValue_doubled (V.game n T)
end MIPRE.Verifier

namespace MIPRE.Verifier
open Cost
variable {ℓ : ℕ} (V : Verifier ℓ)
/-- A perfect PCC strategy gives quantum value `1`. -/
theorem valStar_eq_one_of_hasPerfectPCC {n T : ℕ} (h : V.HasPerfectPCC n T) :
    V.valStar n T = 1 := by
  obtain ⟨S, -, hval⟩ := h
  refine le_antisymm (quantumValue_le_one _) ?_
  have h1 := le_ciSup (TensorProductStrategy.bddAbove_range_value
    (V.doubledGame n T).toGame) S.toTensorProductStrategy
  rw [SyncStrategy.value_toTensorProductStrategy, hval] at h1
  rw [← V.quantumValue_doubledGame n T]
  exact h1
end MIPRE.Verifier

attribute [local gcongr] MIPRE.Cost.polynomial_eval_mono Nat.size_le_size

namespace MIPRE.Halting
open Cost Cost.Prog Cost.Prog.ProgD Polynomial
variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)
theorem Lam0_spec (S' M : Prog) (lam : ℕ) (h : Lam0 G U UT S' + 4 * esize M ≤ lam) :
    (Vhalt G U UT S' M lam).IsBounded lam ∧
      ∀ n, 2 ≤ n → G.bound.eval (n + lam) ≤ n ^ lam :=
  (exists_lamBound G U UT S').choose_spec M lam h
end MIPRE.Halting

namespace MIPRE.Halting
open Cost Cost.Prog
variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)
variable {S' : Prog} (hS' : S'.WellScoped 1)
  (hsem : ∀ x : BitStr, Halts S' (encode x) ↔
    (1 : ℝ) / 2 < quantumValue (tabL G U x (C G)).game)
  (M : Prog) (lam : ℕ)
  (hb : (Vhalt G U UT S' M lam).IsBounded lam)
  (hpoly : ∀ n, 2 ≤ n → G.bound.eval (n + lam) ≤ n ^ lam)
include hS' hsem hb hpoly
omit hS' hsem hb hpoly in
theorem not_branch1_of_not_halts {M : Prog} (hM : ¬ Halts M .nil) (n : ℕ) : ¬ branch1 M n := by
  intro h
  obtain ⟨r, t, -, hr⟩ := (evalWithin_isSome_iff _ _ _).1 h
  exact hM ⟨r, t, hr⟩
end MIPRE.Halting

namespace MIPRE.Halting
open Cost Cost.Prog
variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)
variable {S' : Prog} (hS' : S'.WellScoped 1)
  (hsem : ∀ x : BitStr, Halts S' (encode x) ↔
    (1 : ℝ) / 2 < quantumValue (tabL G U x (C G)).game)
  (M : Prog) (lam : ℕ)
  (hb : (Vhalt G U UT S' M lam).IsBounded lam)
  (hpoly : ∀ n, 2 ≤ n → G.bound.eval (n + lam) ≤ n ^ lam)
include hS' hsem hb hpoly
omit hS' hsem hb hpoly in
/-- Below the first branch, `𝒱^halt` rejects every answer longer than the compressed bound. -/
theorem rejectsLong_of_not_branch1 {n : ℕ} (h1 : ¬ branch1 M n) :
    (Vhalt G U UT S' M lam).RejectsLong n (G.bound.eval (n + lam)) := by
  intro x y a b hab hacc
  unfold branch1 at h1
  rw [accepts_iff, if_neg h1] at hacc
  split_ifs at hacc with h2
  · exact hacc.2.2
  · exact G.output_rejects_long _ _ _ _ _ _ _ hab hacc.2.2
end MIPRE.Halting

namespace MIPRE.Halting
open Cost Cost.Prog
variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)
theorem semL_wellScoped : (semL G U).WellScoped 1 := (exists_semL G U (C G)).choose_spec.1
end MIPRE.Halting

namespace MIPRE.Halting
open Cost Cost.Prog
variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)
theorem semL_spec (x : BitStr) :
    Halts (semL G U) (encode x) ↔ (1 : ℝ) / 2 < quantumValue (tabL G U x (C G)).game :=
  (exists_semL G U (C G)).choose_spec.2 x
end MIPRE.Halting

namespace MIPRE.Halting
open Cost Cost.Prog
variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)
/-- **`thm:halting`, the paper's form**: for `λ ≥ Λ₀ + 4|M|`, at the fixed level `C`, the game
of `𝒱^halt M λ` with answers of length at most `poly(C, λ)` has a value-`1` PCC strategy if `M`
halts on the empty input, and value at most `1/2` if it does not. -/
theorem halting_paper (M : Prog) (lam : ℕ) (h : lamThreshold G U UT + 4 * esize M ≤ lam) :
    (Halts M .nil →
      (Vpaper G U UT M lam).HasPerfectPCC (C G) (G.bound.eval (C G + lam))) ∧
    (¬ Halts M .nil →
      (Vpaper G U UT M lam).valStar (C G) (G.bound.eval (C G + lam)) ≤ 1 / 2) := by
  obtain ⟨hb, hpoly⟩ := Lam0_spec G U UT (semL G U) M lam h
  exact ⟨fun hM => hasPerfectPCC_of_halts G U UT (semL_wellScoped G U) (semL_spec G U) M lam
      hb hpoly hM,
    fun hM => valStar_le_of_not_halts G U UT (semL_wellScoped G U) (semL_spec G U) M lam
      hb hpoly hM⟩
end MIPRE.Halting

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Halting
open Cost Cost.Prog Cost.PolyTimeFun CL Verifier
variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)
variable (Λ₀ K : ℕ) (R : PolyTimeFun BitStr Prog)
theorem _root_.solution
    (hK : ∀ lam, G.bound.eval (C G + lam) ≤ 2 ^ (K + G.bound.natDegree * esize lam))
    (z : BitStr) :
    (Halts (R z) .nil →
      quantumValue ((classV G U UT (lamThreshold G U UT) K R).game z) = 1) ∧
    (¬ Halts (R z) .nil →
      quantumValue ((classV G U UT (lamThreshold G U UT) K R).game z) ≤ 1 / 2) := by
  rw [classV_value]
  set W := Vz G U UT (lamThreshold G U UT) R z
  have hT : G.bound.eval (C G + lamz (lamThreshold G U UT) R z) ≤
      cutz G (lamThreshold G U UT) K R z := hK _
  obtain ⟨h1, h2⟩ := halting_paper G U UT (R z) (lamz (lamThreshold G U UT) R z) le_rfl
  constructor
  · intro hM
    exact W.valStar_eq_one_of_hasPerfectPCC (W.hasPerfectPCC_of_le hT (h1 hM))
  · intro hM
    have hrej : W.RejectsLong (C G) (G.bound.eval (C G + lamz (lamThreshold G U UT) R z)) :=
      rejectsLong_of_not_branch1 G U UT (R z) _ (not_branch1_of_not_halts hM (C G))
    rw [W.valStar_eq_of_rejects hT hrej]
    exact h2 hM
end MIPRE.Halting
