-- Prove2me | solution 1 for MIPRE.Halting.valStar_le_of_not_halts
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-15T22:02:46.361997+00:00
-- url     : https://prove2.me/submissions/6f8a5f31-bbc3-419b-b6e3-483a5209c06d

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Paper/Induction.lean (solution of MIPRE.Halting.valStar_le_of_not_halts);
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
import Definitions.Def_MIPRE_Foundations_Cost_BoundedEval
import Definitions.Def_MIPRE_Foundations_Halting_Tabulate
import Definitions.Def_MIPRE_Foundations_Cost_BitQuery
import Definitions.Def_MIPRE_Foundations_Cost_Succinct
import Definitions.Def_MIPRE_Foundations_Cost_Clocked
import Definitions.Def_MIPRE_Foundations_Cost_Threshold
import Definitions.Def_MIPRE_Foundations_Compression
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_Cost_ManyOne
import Definitions.Def_MIPRE_Foundations_Halting_PolyBounded
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
import Definitions.Def_MIPRE_Foundations_Halting_Paper_Induction
import Theorems.Thm_MIPRE_Cost_halts_haltingReduction_iff
import Theorems.Thm_MIPRE_Halting_accepts_iff
import Theorems.Thm_MIPRE_Halting_tabL_match

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.TensorProductStrategy
open Matrix Kronecker
open scoped ComplexOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {G : Game X Y A B}
/-- Accepting more answer tuples raises the value of a strategy. -/
theorem value_copy_le (S : TensorProductStrategy G) (G' : Game X Y A B)
    (hμ : ∀ x y, G'.μ x y = G.μ x y)
    (hD : ∀ x y a b, G.D x y a b = true → G'.D x y a b = true) :
    S.value ≤ (S.copy G').value := by
  unfold value
  refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
    Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
  rw [hμ]
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (G.μ_nonneg x y))
    (S.re_dotProduct_nonneg x y a b)
  cases h : G.D x y a b with
  | false => by_cases h' : G'.D x y a b = true <;> simp [h']
  | true => rw [hD x y a b h]
end MIPRE.TensorProductStrategy

namespace MIPRE.TensorProductStrategy
open Matrix Kronecker
open scoped ComplexOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {G : Game X Y A B}
/-- Relabeling along equivalences with matching distribution and decision predicate
preserves the value. -/
theorem value_relabel {X' Y' A' B' : Type*} [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
    (S : TensorProductStrategy G) (G' : Game X' Y' A' B') (eX : X' ≃ X) (eY : Y' ≃ Y)
    (eA : A' ≃ A) (eB : B' ≃ B)
    (hμ : ∀ x' y', G'.μ x' y' = G.μ (eX x') (eY y'))
    (hD : ∀ x' y' a' b', G'.D x' y' a' b' = G.D (eX x') (eY y') (eA a') (eB b')) :
    (S.relabel G' eX eY eA eB).value = S.value := by
  unfold value
  show (∑ x', ∑ y', ∑ a', ∑ b', G'.μ x' y' * (if G'.D x' y' a' b' then 1 else 0) *
      (star S.ψ ⬝ᵥ ((S.PA.M (eX x') (eA a') ⊗ₖ S.PB.M (eY y') (eB b')) *ᵥ S.ψ)).re) =
    ∑ x, ∑ y, ∑ a, ∑ b, G.μ x y * (if G.D x y a b then 1 else 0) *
      (star S.ψ ⬝ᵥ ((S.PA.M x a ⊗ₖ S.PB.M y b) *ᵥ S.ψ)).re
  symm
  refine Fintype.sum_equiv eX.symm _ _ fun x => Fintype.sum_equiv eY.symm _ _ fun y =>
    Fintype.sum_equiv eA.symm _ _ fun a => Fintype.sum_equiv eB.symm _ _ fun b => ?_
  rw [hμ, hD, eX.apply_symm_apply, eY.apply_symm_apply, eA.apply_symm_apply,
    eB.apply_symm_apply]
end MIPRE.TensorProductStrategy

namespace MIPRE
open Matrix Kronecker
open scoped ComplexOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
/-- Games related by equivalences of their alphabets, with matching distribution and
decision predicate, have the same quantum value. -/
theorem quantumValue_eq_of_equiv {X' Y' A' B' : Type*} [Fintype X'] [Fintype Y'] [Fintype A']
    [Fintype B'] (G : Game X Y A B) (G' : Game X' Y' A' B') (eX : X' ≃ X) (eY : Y' ≃ Y)
    (eA : A' ≃ A) (eB : B' ≃ B)
    (hμ : ∀ x' y', G'.μ x' y' = G.μ (eX x') (eY y'))
    (hD : ∀ x' y' a' b', G'.D x' y' a' b' = G.D (eX x') (eY y') (eA a') (eB b')) :
    quantumValue G' = quantumValue G := by
  apply le_antisymm
  · refine Real.iSup_le (fun S' => ?_) (quantumValue_nonneg _)
    have h := le_ciSup (TensorProductStrategy.bddAbove_range_value G)
      (S'.relabel G eX.symm eY.symm eA.symm eB.symm)
    rwa [S'.value_relabel G eX.symm eY.symm eA.symm eB.symm (fun x y => by simp [hμ])
      (fun x y a b => by simp [hD])] at h
  · refine Real.iSup_le (fun S => ?_) (quantumValue_nonneg _)
    have h := le_ciSup (TensorProductStrategy.bddAbove_range_value G')
      (S.relabel G' eX eY eA eB)
    rwa [S.value_relabel G' eX eY eA eB hμ hD] at h
end MIPRE

namespace MIPRE
open Matrix Kronecker
open scoped ComplexOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
/-- Accepting more answer tuples, on the same alphabets and distribution, raises the quantum
value. -/
theorem quantumValue_mono (G G' : Game X Y A B) (hμ : ∀ x y, G'.μ x y = G.μ x y)
    (hD : ∀ x y a b, G.D x y a b = true → G'.D x y a b = true) :
    quantumValue G ≤ quantumValue G' := by
  refine Real.iSup_le (fun S => ?_) (quantumValue_nonneg _)
  exact (S.value_copy_le G' hμ hD).trans
    (le_ciSup (TensorProductStrategy.bddAbove_range_value G') (S.copy G'))
end MIPRE

namespace MIPRE
open Matrix Kronecker
open scoped ComplexOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
/-- A game whose decision predicate rejects everything has quantum value `0`. -/
theorem quantumValue_eq_zero_of_reject (G : Game X Y A B) (hD : ∀ x y a b, G.D x y a b = false) :
    quantumValue G = 0 := by
  refine le_antisymm (Real.iSup_le (fun S => ?_) le_rfl) (quantumValue_nonneg G)
  unfold TensorProductStrategy.value
  simp [hD]
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
/-- With the same sampler, a decider accepting more at index `n` gives a larger `val*`. -/
theorem valStar_le_of_accepts_imp {V W : Verifier ℓ} {n T : ℕ} (hS : W.sampler = V.sampler)
    (h : ∀ x y a b, V.decider.Accepts n x y a b → W.decider.Accepts n x y a b) :
    V.valStar n T ≤ W.valStar n T := by
  obtain ⟨SW, DW, hW⟩ := W
  obtain ⟨SV, DV, hV⟩ := V
  simp only at hS
  subst hS
  refine quantumValue_mono _ _ (fun _ _ => rfl) fun x y a b hd => ?_
  rw [game_D] at hd ⊢
  exact h _ _ _ _ hd
end MIPRE.Verifier

namespace MIPRE.Verifier
open Cost
variable {ℓ : ℕ} (V : Verifier ℓ)
/-- With the same sampler, deciders accepting the same tuples at index `n` give the same
`val*`. -/
theorem valStar_congr {V W : Verifier ℓ} {n T : ℕ} (hS : W.sampler = V.sampler)
    (h : ∀ x y a b, V.decider.Accepts n x y a b ↔ W.decider.Accepts n x y a b) :
    V.valStar n T = W.valStar n T :=
  le_antisymm (valStar_le_of_accepts_imp hS fun x y a b => (h x y a b).1)
    (valStar_le_of_accepts_imp hS.symm fun x y a b => (h x y a b).2)
end MIPRE.Verifier

namespace MIPRE.Verifier
open Cost
variable {ℓ : ℕ} (V : Verifier ℓ)
/-- A decider that accepts nothing at index `n` gives quantum value `0`. -/
theorem valStar_eq_zero_of_rejects_all {n T : ℕ}
    (hrej : ∀ x y a b, ¬ V.decider.Accepts n x y a b) : V.valStar n T = 0 := by
  classical
  refine quantumValue_eq_zero_of_reject _ fun x y a b => ?_
  exact decide_eq_false (hrej _ _ _ _)
end MIPRE.Verifier

namespace MIPRE.Verifier
open HaltingGameValue (GameData)
variable {ℓ : ℕ} (V : Verifier ℓ) (n T : ℕ) (g : GameData)
/-- **The value bridge, doubled.** A game description matching `𝒱_n`'s *doubled* game along
relabelings of the two alphabets has the value of `𝒱_n` — the doubled replacement of
`quantumValue_toGame_eq_valStar`, and unlike it free of any synchronicity hypothesis. Note
that `hD` here is total, on every question pair including the diagonal: the doubled game
rejects off the tag block, exactly as a `GameData` does, so `quantumValue_eq_of_equiv` applies
unchanged and no support-restricted version of it is needed. -/
theorem quantumValue_toGame_eq_valStar_doubled
    (eX : Fin (g.nX + 1) ≃ Bool × V.Questions n) (eA : Fin (g.nA + 1) ≃ Answers T)
    (hμ : ∀ i j, g.game.μ i j = (V.doubledGame n T).μ (eX i) (eX j))
    (hD : ∀ i j k l, g.game.D i j k l = (V.doubledGame n T).D (eX i) (eX j) (eA k) (eA l)) :
    quantumValue g.game = V.valStar n T := by
  rw [← V.quantumValue_doubledGame n T]
  exact quantumValue_eq_of_equiv (V.doubledGame n T).toGame g.game eX eX eA eA hμ hD
end MIPRE.Verifier

namespace MIPRE.Halting
open Cost
open HaltingGameValue (GameData)
variable (G : GapCompression) (U : UniversalMachine)
/-- **The value of the tabulation** is the verifier's, on a string whose verifier is bounded by
the string's own parameter, at every index `n ≥ 2`. -/
theorem tabL_value (x : BitStr) (n : ℕ) (hb : (Vof G U x).IsBounded (descLam x)) (hn : 2 ≤ n) :
    quantumValue (tabL G U x n).game = (Vof G U x).valStar n (ansBound G x n) := by
  obtain ⟨eX, eA, hμ, hD⟩ := tabL_match G U x n hb hn
  exact Verifier.quantumValue_toGame_eq_valStar_doubled _ _ _ _ eX eA hμ hD
end MIPRE.Halting

namespace MIPRE.Halting
open Cost
open HaltingGameValue (GameData)
variable (G : GapCompression) (U : UniversalMachine)
/-- The verifier the string `descOf lam e` denotes. -/
theorem Vof_descOf (lam : ℕ) (e : Prog) :
    Vof G U (descOf lam e) = Verifier.ofSamplerDecider U (G.sampler lam) e := by
  unfold Vof
  rw [descLam_descOf, descDecD_descOf]
  rfl
end MIPRE.Halting

namespace MIPRE.Halting
open Cost Cost.Prog Cost.Prog.ProgD Polynomial
variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)
theorem halts_searchP_iff {S' : Prog} (hS' : S'.WellScoped 1) (lam : ℕ) (d : Prog) :
    Halts (searchP S' lam d) .nil ↔ Halts S' (encode (descOf lam d)) :=
  halts_haltingReduction_iff hS' (descOf lam d)
end MIPRE.Halting

namespace MIPRE.Halting
open Cost Cost.Prog Cost.Prog.ProgD Polynomial
variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)
theorem Vhalt_eq_Vof (S' M : Prog) (lam : ℕ) :
    Vhalt G U UT S' M lam = Vof G U (descOf lam (dec G U UT S' M lam)) :=
  (Vof_descOf G U _ _).symm
end MIPRE.Halting

namespace MIPRE.Halting
open Cost Cost.Prog
variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)
theorem two_le_C : 2 ≤ C G := le_max_right _ _
end MIPRE.Halting

namespace MIPRE.Halting
open Cost Cost.Prog
variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)
theorem C₀_le_C : G.C₀ ≤ C G := le_max_left _ _
end MIPRE.Halting

namespace MIPRE.Halting
open Cost Cost.Prog
variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)
theorem two_pow_le_lv : ∀ j, 2 ^ j ≤ lv G j
  | 0 => (Nat.pow_le_pow_right two_pos (Nat.zero_le 1)).trans (two_le_C G)
  | j + 1 => by
    rw [lv_succ, pow_succ]
    have h := two_pow_le_lv j
    have h2 : 2 ^ j * 2 ≤ 2 ^ 2 ^ j := by
      rw [← pow_succ]
      exact Nat.pow_le_pow_right two_pos (Nat.lt_two_pow_self)
    exact h2.trans (Nat.pow_le_pow_right two_pos h)
end MIPRE.Halting

namespace MIPRE.Halting
open Cost Cost.Prog
variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)
theorem C_le_lv : ∀ j, C G ≤ lv G j
  | 0 => le_rfl
  | j + 1 => by
    rw [lv_succ]
    exact (C_le_lv j).trans Nat.lt_two_pow_self.le
end MIPRE.Halting

namespace MIPRE.Halting
open Cost Cost.Prog
variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)
theorem exists_le_size_lv (k : ℕ) : ∃ j, k ≤ Nat.size (lv G j) := by
  refine ⟨k, ?_⟩
  have h := Nat.size_le_size (two_pow_le_lv G k)
  rw [Nat.size_pow] at h
  omega
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
theorem rejects_all_of_branch2 {n : ℕ} (h1 : ¬ branch1 M n) (h2 : branch2 G U UT S' M lam n)
    (x y a b : BitStr) : ¬ (Vhalt G U UT S' M lam).decider.Accepts n x y a b := by
  unfold branch1 at h1
  unfold branch2 at h2
  rw [accepts_iff, if_neg h1, if_pos h2]
  exact fun h => h.2.2
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
theorem accepts_iff_W {n : ℕ} (h1 : ¬ branch1 M n) (h2 : ¬ branch2 G U UT S' M lam n)
    (x y a b : BitStr) :
    (Vhalt G U UT S' M lam).decider.Accepts n x y a b ↔
      (W G U UT S' M lam).decider.Accepts n x y a b := by
  unfold branch1 at h1
  unfold branch2 at h2
  rw [accepts_iff, if_neg h1, if_neg h2]
  constructor
  · exact fun h => h.2.2
  · intro h
    have hl := (W G U UT S' M lam).accepts_length n x y a b h
    rw [G.output_sampler] at hl
    exact ⟨hl.1, hl.2, h⟩
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
theorem W_sampler : (W G U UT S' M lam).sampler = (Vhalt G U UT S' M lam).sampler :=
  G.output_sampler _ _
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
variable {S' : Prog} (hS' : S'.WellScoped 1)
  (hsem : ∀ x : BitStr, Halts S' (encode x) ↔
    (1 : ℝ) / 2 < quantumValue (tabL G U x (C G)).game)
  (M : Prog) (lam : ℕ)
  (hb : (Vhalt G U UT S' M lam).IsBounded lam)
  (hpoly : ∀ n, 2 ≤ n → G.bound.eval (n + lam) ≤ n ^ lam)
include hS' hsem hb hpoly
omit hS' hsem hb hpoly in
theorem B_of_branch2 {n : ℕ} (h1 : ¬ branch1 M n) (h2 : branch2 G U UT S' M lam n) :
    B G U UT S' M lam n := by
  unfold B
  rw [(Vhalt G U UT S' M lam).valStar_eq_zero_of_rejects_all
    (rejects_all_of_branch2 G U UT M lam h1 h2)]
  norm_num
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
omit hS' hsem in
/-- **Soundness carried down a level**, where neither branch fires. -/
theorem B_step {n : ℕ} (hn : C G ≤ n) (h1 : ¬ branch1 M n) (h2 : ¬ branch2 G U UT S' M lam n)
    (hB : B G U UT S' M lam (2 ^ n)) : B G U UT S' M lam n := by
  have hW := G.soundness _ lam n hb ((C₀_le_C G).trans hn) hB
  have hV : (Vhalt G U UT S' M lam).valStar n (G.bound.eval (n + lam)) ≤ 1 / 2 := by
    rw [(Vhalt G U UT S' M lam).valStar_congr (W_sampler G U UT M lam)
      (accepts_iff_W G U UT M lam h1 h2)]
    exact hW
  unfold B
  rw [(Vhalt G U UT S' M lam).valStar_eq_of_rejects (hpoly n ((two_le_C G).trans hn))
    (rejectsLong_of_not_branch1 G U UT M lam h1)]
  exact hV
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
omit hpoly in
/-- The search halts exactly when the start level has value above `1/2`. -/
theorem halts_search_iff :
    Halts (searchP S' lam (dec G U UT S' M lam)) .nil ↔
      (1 : ℝ) / 2 < (Vhalt G U UT S' M lam).valStar (C G) (G.bound.eval (C G + lam)) := by
  rw [halts_searchP_iff hS', hsem]
  have hb' : (Vof G U (descOf lam (dec G U UT S' M lam))).IsBounded
      (descLam (descOf lam (dec G U UT S' M lam))) := by
    rw [descLam_descOf, ← Vhalt_eq_Vof]; exact hb
  rw [tabL_value G U _ _ hb' (two_le_C G), ansBound, descLam_descOf, ← Vhalt_eq_Vof]
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
omit hpoly in
theorem branch2_of_lt (h : (1 : ℝ) / 2 <
      (Vhalt G U UT S' M lam).valStar (C G) (G.bound.eval (C G + lam))) :
    ∃ k, ∀ n, k ≤ Nat.size n → branch2 G U UT S' M lam n := by
  obtain ⟨r, t, hr⟩ := (halts_search_iff G U UT hS' hsem M lam hb).2 h
  exact ⟨t, fun n hn => (evalWithin_isSome_iff _ _ _).2 ⟨r, t, hn, hr⟩⟩
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
omit hS' hsem hb in
/-- The start level is in `B` only if its value is at most `1/2` — with the answer bound of the
statement, once the first branch does not fire there. -/
theorem le_of_B_start (h1 : ¬ branch1 M (C G)) (hB : B G U UT S' M lam (C G)) :
    (Vhalt G U UT S' M lam).valStar (C G) (G.bound.eval (C G + lam)) ≤ 1 / 2 := by
  unfold B at hB
  rwa [(Vhalt G U UT S' M lam).valStar_eq_of_rejects (hpoly _ (two_le_C G))
    (rejectsLong_of_not_branch1 G U UT M lam h1)] at hB
end MIPRE.Halting

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
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
theorem _root_.solution (hM : ¬ Halts M .nil) :
    (Vhalt G U UT S' M lam).valStar (C G) (G.bound.eval (C G + lam)) ≤ 1 / 2 := by
  have hfalse := not_branch1_of_not_halts hM
  by_contra hlt
  obtain ⟨k₁, hk₁⟩ := branch2_of_lt G U UT hS' hsem M lam hb (not_le.1 hlt)
  have hB : ∀ k j, k₁ ≤ Nat.size (lv G (j + k)) → B G U UT S' M lam (lv G j) := by
    intro k
    induction k with
    | zero =>
      intro j hj
      rw [Nat.add_zero] at hj
      exact B_of_branch2 G U UT M lam (hfalse _) (hk₁ _ hj)
    | succ k ih =>
      intro j hj
      by_cases h2 : branch2 G U UT S' M lam (lv G j)
      · exact B_of_branch2 G U UT M lam (hfalse _) h2
      · have hnext := ih (j + 1) (by rw [show j + 1 + k = j + (k + 1) by omega]; exact hj)
        rw [lv_succ] at hnext
        exact B_step G U UT M lam hb hpoly (C_le_lv G j) (hfalse _) h2 hnext
  obtain ⟨k, hk⟩ := exists_le_size_lv G k₁
  have hfin := hB k 0 (by simpa using hk)
  rw [lv_zero] at hfin
  exact hlt (le_of_B_start G U UT M lam hpoly (hfalse _) hfin)
end MIPRE.Halting
