-- Prove2me | solution 1 for MIPRE.Halting.mipstar_eq_re_of
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-15T22:08:30.593719+00:00
-- url     : https://prove2.me/submissions/76ccf6c9-6058-4c30-8ce4-26343066dac8

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Paper/ClassMain.lean (solution of MIPRE.Halting.mipstar_eq_re_of);
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
import Theorems.Thm_MIPRE_Halting_re_subset_mipstar_of
import Theorems.Thm_MIPRE_PolyVerifier_D_clause
import Theorems.Thm_MIPRE_PolyVerifier_mu_clause

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
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
open HaltingGameValue (GameData)
open MIPRE.Cost
/-- **`MIP* ⊆ RE`** (the easy half of `thm:mipstar-eq-re`): enumerate strategies of the game of
`x` and accept upon finding one of value greater than `1/2`. -/
theorem MIPStarComputable.isRE {L : Set BitStr} (h : MIPStarComputable L) : IsRE L := by
  obtain ⟨g, hg, hgap⟩ := h
  refine (rePred_lt_quantumValue_comp hg 1 2).of_eq fun x => ?_
  simp only [Nat.cast_one, Nat.cast_ofNat]
  constructor
  · intro hlt
    by_contra hx
    exact absurd ((hgap x).2 hx) (not_le.2 hlt)
  · intro hx
    rw [(hgap x).1 hx]
    norm_num
end MIPRE

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

namespace MIPRE.PolyVerifier
open MIPRE.Cost Verifier
open HaltingGameValue (GameData)
theorem primrec_tuplesLE : Primrec tuplesLE := by
  have h4 : Primrec fun q : (((ℕ × BitStr) × BitStr) × BitStr) =>
      (Data.bitStrsLE q.1.1.1).map fun b => (q.1.1.2, q.1.2, q.2, b) := by
    refine Primrec.list_map
      (Data.primrec_bitStrsLE.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))) ?_
    have hx : Primrec fun r : (((ℕ × BitStr) × BitStr) × BitStr) × BitStr =>
        r.1.1.1.2 := Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
    have hy : Primrec fun r : (((ℕ × BitStr) × BitStr) × BitStr) × BitStr =>
        r.1.1.2 := Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
    have ha : Primrec fun r : (((ℕ × BitStr) × BitStr) × BitStr) × BitStr =>
        r.1.2 := Primrec.snd.comp Primrec.fst
    exact (hx.pair (hy.pair (ha.pair Primrec.snd))).to₂
  have h3 : Primrec fun q : ((ℕ × BitStr) × BitStr) =>
      (Data.bitStrsLE q.1.1).flatMap fun a =>
        (Data.bitStrsLE q.1.1).map fun b => (q.1.2, q.2, a, b) :=
    Primrec.list_flatMap
      (Data.primrec_bitStrsLE.comp (Primrec.fst.comp Primrec.fst)) h4.to₂
  have h2 : Primrec fun q : (ℕ × BitStr) =>
      (Data.bitStrsLE q.1).flatMap fun y =>
        (Data.bitStrsLE q.1).flatMap fun a =>
          (Data.bitStrsLE q.1).map fun b => (q.2, y, a, b) :=
    Primrec.list_flatMap (Data.primrec_bitStrsLE.comp Primrec.fst) h3.to₂
  exact Primrec.list_flatMap Data.primrec_bitStrsLE h2.to₂
end MIPRE.PolyVerifier

namespace MIPRE.PolyVerifier
open MIPRE.Cost Verifier
open HaltingGameValue (GameData)
theorem accListLE_eq_filterMap (T : ℕ) (fA fB : BitStr → ℕ)
    (acc? : BitStr → BitStr → BitStr → BitStr → Bool) :
    accListLE T fA fB acc? = (tuplesLE T).filterMap fun q =>
      if acc? q.1 q.2.1 q.2.2.1 q.2.2.2 then
        some (fA q.1, fB q.2.1,
          (Data.bitStrsLE T).idxOf q.2.2.1, (Data.bitStrsLE T).idxOf q.2.2.2)
      else none := by
  simp only [accListLE, tuplesLE, List.filterMap_flatMap, List.filterMap_map, Function.comp_def]
end MIPRE.PolyVerifier

namespace MIPRE.PolyVerifier
open MIPRE.Cost Verifier
open HaltingGameValue (GameData)
theorem primrec_accListLE {α : Type*} [Primcodable α] {T : α → ℕ}
    {fA fB : α → BitStr → ℕ}
    {acc? : α → BitStr → BitStr → BitStr → BitStr → Bool}
    (hT : Primrec T) (hfA : Primrec₂ fA) (hfB : Primrec₂ fB)
    (hacc : Primrec fun q : α × BitStr × BitStr × BitStr × BitStr =>
      acc? q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2) :
    Primrec fun a => accListLE (T a) (fA a) (fB a) (acc? a) := by
  have hbl : Primrec fun q : α × BitStr × BitStr × BitStr × BitStr =>
      Data.bitStrsLE (T q.1) := Data.primrec_bitStrsLE.comp (hT.comp Primrec.fst)
  have hbody : Primrec₂ fun (a : α) (q : BitStr × BitStr × BitStr × BitStr) =>
      (if acc? a q.1 q.2.1 q.2.2.1 q.2.2.2 then
        some (fA a q.1, fB a q.2.1,
          (Data.bitStrsLE (T a)).idxOf q.2.2.1, (Data.bitStrsLE (T a)).idxOf q.2.2.2)
        else none) := by
    refine Primrec.ite ⟨inferInstance, hacc.of_eq fun q => by
        cases h : acc? q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 <;> simp [h]⟩ ?_ (Primrec.const none)
    refine Primrec.option_some.comp
      ((hfA.comp Primrec.fst (Primrec.fst.comp Primrec.snd)).pair
        ((hfB.comp Primrec.fst (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))).pair
          ((Cost.primrec_idxOf_bitStr.comp
              (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))) hbl).pair
            (Cost.primrec_idxOf_bitStr.comp
              (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))) hbl))))
  exact (Primrec.listFilterMap (primrec_tuplesLE.comp hT) hbody).of_eq fun a =>
    (accListLE_eq_filterMap (T a) (fA a) (fB a) (acc? a)).symm
end MIPRE.PolyVerifier

namespace MIPRE.PolyVerifier
open MIPRE.Cost Verifier
open HaltingGameValue (GameData)
theorem primrec_qIdx (tg : Bool) : Primrec₂ fun (T : ℕ) (x : BitStr) => qIdx T tg x := by
  have hbl : Primrec fun q : ℕ × BitStr => Data.bitStrsLE q.1 :=
    Data.primrec_bitStrsLE.comp Primrec.fst
  exact (Primrec.nat_add.comp (Cost.primrec_idxOf_bitStr.comp Primrec.snd hbl)
    (Primrec.nat_mul.comp (Primrec.list_length.comp hbl)
      (Primrec.const (if tg then 1 else 0)))).to₂
end MIPRE.PolyVerifier

namespace MIPRE.PolyVerifier
open MIPRE.Cost Verifier
open HaltingGameValue (GameData)
theorem primrec_sampleC (sd : Data) :
    Primrec fun q : (ℕ × BitStr) × BitStr => sampleC sd q.1.1 q.1.2 q.2 := by
  have hin : Primrec fun q : (ℕ × BitStr) × BitStr => (encode (q.1.2, q.2) : Data) :=
    Data.primrec_cons.comp (primrec_encode_bitStr.comp (Primrec.snd.comp Primrec.fst))
      (primrec_encode_bitStr.comp Primrec.snd)
  have hrun : Primrec fun q : (ℕ × BitStr) × BitStr =>
      Machine.runForD sd (encode (q.1.2, q.2)) q.1.1 :=
    Machine.primrec_runForD.comp (((Primrec.const sd).pair hin).pair (Primrec.fst.comp Primrec.fst))
  have hinner : Primrec₂ fun (_ : (ℕ × BitStr) × BitStr) (d : Data) =>
      (SizedEncoding.decode d.left : Option BitStr).bind fun x =>
        (SizedEncoding.decode d.right : Option BitStr).map fun y => (x, y) := by
    refine Primrec.option_bind
      (Data.primrec_decode_bitStr.comp (Data.primrec_left.comp Primrec.snd)) ?_
    refine Primrec.option_map
      (Data.primrec_decode_bitStr.comp (Data.primrec_right.comp (Primrec.snd.comp Primrec.fst))) ?_
    exact (Primrec.snd.comp Primrec.fst).pair Primrec.snd
  exact Primrec.option_getD.comp (Primrec.option_bind hrun hinner) (Primrec.const ([], []))
end MIPRE.PolyVerifier

namespace MIPRE.PolyVerifier
open MIPRE.Cost Verifier
open HaltingGameValue (GameData)
set_option maxHeartbeats 1000000 in
theorem primrec_accC (pd : Data) (P : Polynomial ℕ) :
    Primrec fun q : BitStr × BitStr × BitStr × BitStr × BitStr =>
      accC pd P q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 := by
  have hz : Primrec fun q : BitStr × BitStr × BitStr × BitStr × BitStr => q.1 := Primrec.fst
  have hx : Primrec fun q : BitStr × BitStr × BitStr × BitStr × BitStr => q.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hy : Primrec fun q : BitStr × BitStr × BitStr × BitStr × BitStr => q.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have ha : Primrec fun q : BitStr × BitStr × BitStr × BitStr × BitStr => q.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hb : Primrec fun q : BitStr × BitStr × BitStr × BitStr × BitStr => q.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hebs : Primrec fun l : BitStr => (encode l : Data) := primrec_encode_bitStr
  have hinput : Primrec fun q : BitStr × BitStr × BitStr × BitStr × BitStr =>
      (encode (q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2) : Data) :=
    Data.primrec_cons.comp (hebs.comp hz)
      (Data.primrec_cons.comp (hebs.comp hx)
        (Data.primrec_cons.comp (hebs.comp hy)
          (Data.primrec_cons.comp (hebs.comp ha) (hebs.comp hb))))
  have hlen : Primrec fun q : BitStr × BitStr × BitStr × BitStr × BitStr =>
      q.1.length + q.2.1.length + q.2.2.1.length + q.2.2.2.1.length + q.2.2.2.2.length :=
    Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_add.comp
      (Primrec.nat_add.comp (Primrec.list_length.comp hz) (Primrec.list_length.comp hx))
      (Primrec.list_length.comp hy)) (Primrec.list_length.comp ha)) (Primrec.list_length.comp hb)
  have hbudget : Primrec fun q : BitStr × BitStr × BitStr × BitStr × BitStr =>
      P.eval (q.1.length + q.2.1.length + q.2.2.1.length + q.2.2.2.1.length + q.2.2.2.2.length) :=
    (Cost.primrec_poly_eval P).comp hlen
  have hfin : PrimrecPred fun q : BitStr × BitStr × BitStr × BitStr × BitStr =>
      Machine.runForD pd (encode (q.1, q.2.1, q.2.2.1, q.2.2.2.1, q.2.2.2.2))
        (P.eval (q.1.length + q.2.1.length + q.2.2.1.length + q.2.2.2.1.length + q.2.2.2.2.length))
        = some (encode true) :=
    Primrec.eq.comp (Machine.primrec_runForD.comp (((Primrec.const pd).pair hinput).pair hbudget))
      (Primrec.const (some (encode true) : Option Data))
  exact (Primrec.ite hfin (Primrec.const true) (Primrec.const false)).of_eq fun q => by
    simp only [accC]; split <;> simp_all
end MIPRE.PolyVerifier

namespace MIPRE.PolyVerifier
open MIPRE.Cost Verifier
open HaltingGameValue (GameData)
theorem primrec_tabOf (sd pd : Data) (P : Polynomial ℕ) : Primrec (tabOf sd pd P) := by
  have hT : Primrec fun z : BitStr => P.eval z.length :=
    (Cost.primrec_poly_eval P).comp Primrec.list_length
  have hN : Primrec fun z : BitStr => N (P.eval z.length) :=
    Primrec.list_length.comp (Data.primrec_bitStrsLE.comp hT)
  have hnX : Primrec fun z : BitStr => 2 * N (P.eval z.length) - 1 :=
    Primrec.nat_sub.comp (Primrec.nat_mul.comp (Primrec.const 2) hN) (Primrec.const 1)
  have hnA : Primrec fun z : BitStr => N (P.eval z.length) - 1 :=
    Primrec.nat_sub.comp hN (Primrec.const 1)
  have hT' : Primrec fun z : BitStr => P.eval (z.length + P.eval z.length) :=
    (Cost.primrec_poly_eval P).comp (Primrec.nat_add.comp Primrec.list_length hT)
  have hsamp : Primrec fun q : BitStr × BitStr =>
      sampleC sd (P.eval (q.1.length + P.eval q.1.length)) q.1 q.2 :=
    (primrec_sampleC sd).comp (((hT'.comp Primrec.fst).pair Primrec.fst).pair Primrec.snd)
  have hw : Primrec fun z : BitStr => weightList (P.eval z.length)
      (fun r => qIdx (P.eval z.length) false
        (sampleC sd (P.eval (z.length + P.eval z.length)) z r).1)
      (fun r => qIdx (P.eval z.length) true
        (sampleC sd (P.eval (z.length + P.eval z.length)) z r).2) := by
    refine Primrec.list_map (Data.primrec_bitStrsOfLen.comp hT) ?_
    exact (((primrec_qIdx false).comp (hT.comp Primrec.fst) (Primrec.fst.comp hsamp)).pair
      (((primrec_qIdx true).comp (hT.comp Primrec.fst) (Primrec.snd.comp hsamp)).pair
        (Primrec.const 1))).to₂
  have hacc : Primrec fun z : BitStr => accListLE (P.eval z.length) (qIdx (P.eval z.length) false)
      (qIdx (P.eval z.length) true) (accC pd P z) := by
    refine primrec_accListLE hT ((primrec_qIdx false).comp (hT.comp Primrec.fst) Primrec.snd)
      ((primrec_qIdx true).comp (hT.comp Primrec.fst) Primrec.snd) ?_
    exact (primrec_accC pd P).of_eq fun q => rfl
  refine ((Primrec.of_equiv_symm (e := GameData.equivTuple)).comp
    (hnX.pair (hnA.pair (hw.pair hacc)))).of_eq ?_
  intro z
  rfl
end MIPRE.PolyVerifier

namespace MIPRE.PolyVerifier
open MIPRE.Cost Verifier
open HaltingGameValue (GameData)
variable (V : PolyVerifier)
theorem tab_computable : Computable V.tab :=
  (primrec_tabOf (encode V.sampler) (encode V.decider) V.bound).to_comp
end MIPRE.PolyVerifier

namespace MIPRE.PolyVerifier
open MIPRE.Cost Verifier
open HaltingGameValue (GameData)
variable (V : PolyVerifier)
/-- **The table has the value of `G_z`**, on an efficient input. -/
theorem quantumValue_tab {z : BitStr} (h : V.Efficient z) :
    quantumValue (V.tab z).game = quantumValue (V.game z) := by
  rw [← quantumValue_doubled (V.game z)]
  exact quantumValue_eq_of_equiv (V.game z).doubled.toGame (V.tab z).game (V.eX z) (V.eX z)
    (V.eA z) (V.eA z) (V.mu_clause h) (V.D_clause h)
end MIPRE.PolyVerifier

namespace MIPRE
open MIPRE.Cost Verifier
open HaltingGameValue (GameData)
/-- **`lem:mipstar-poly-sub`: the paper's class is contained in the computable one.** -/
theorem MIPStar.toComputable {L : Set BitStr} (h : MIPStar L) : MIPStarComputable L := by
  obtain ⟨V, heff, hgap⟩ := h
  refine ⟨V.tab, V.tab_computable, fun z => ?_⟩
  rw [V.quantumValue_tab (heff z)]
  exact hgap z
end MIPRE

namespace MIPRE
open MIPRE.Cost Verifier
open HaltingGameValue (GameData)
/-- The paper's class is contained in `RE`. -/
theorem MIPStar.isRE {L : Set BitStr} (h : MIPStar L) : IsRE L :=
  h.toComputable.isRE
end MIPRE

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Halting
open Cost Cost.Prog Cost.PolyTimeFun CL Verifier
variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)
variable (Λ₀ K : ℕ) (R : PolyTimeFun BitStr Prog)
include G U UT in
theorem _root_.solution : MIPStar = IsRE :=
  funext fun _ => propext ⟨MIPStar.isRE, re_subset_mipstar_of G U UT⟩
end MIPRE.Halting
