-- Prove2me | solution 1 for MIPRE.Cost.Prog.wrapCore_hasPolyCost
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-15T20:53:15.066684+00:00
-- url     : https://prove2.me/submissions/4bd40b4f-e944-4107-bfc7-830e66c272c8

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/WrapperCost.lean (solution of MIPRE.Cost.Prog.wrapCore_hasPolyCost);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Computability.Primrec.List
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
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
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_GameTransport
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
import Definitions.Def_MIPRE_Foundations_Halting_PolyBounded
import Definitions.Def_MIPRE_Foundations_Halting_WrapperCost
import Theorems.Thm_MIPRE_Cost_Prog_polyBounded_wrapHeadZ

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Cost
open Polynomial
/-- The size of the binary encoding of `n` is polynomially bounded. -/
theorem polyBounded_esize_nat : PolyBounded fun n => esize n :=
  ((PolyBounded.size.const_mul 4).add_const 1).mono fun n => esize_nat_le n
end MIPRE.Cost

namespace MIPRE.Cost.PolyCost
open Polynomial
theorem mono {f g : ℕ → Data → ℕ} (hg : PolyCost g) (h : ∀ n d, f n d ≤ g n d) : PolyCost f :=
  let ⟨C, k, hC, hb⟩ := hg
  ⟨C, k, hC, fun n d => (h n d).trans (hb n d)⟩
end MIPRE.Cost.PolyCost

namespace MIPRE.Cost
open Polynomial
/-- A cost bound of the composable shape `PolyCost` is a `HasPolyCost`: the two differ only in
whether the polynomial in the input size is displayed. Cost analyses are assembled in the first
form, where `add`, `mul` and `poly` apply, and consumed in the second. -/
theorem Prog.hasPolyCost_of_polyCost {p : Prog} {B : ℕ → Data → ℕ} (hB : PolyCost B)
    (h : ∀ (n : ℕ) (d : Data), ∃ r t, t ≤ B n d ∧ p.Runs (.cons (encode n) d) r t) :
    p.HasPolyCost := by
  obtain ⟨C, k, hC, hb⟩ := hB
  refine ⟨C, k, hC, fun n d => ?_⟩
  obtain ⟨r, t, ht, hr⟩ := h n d
  exact ⟨r, t, ht.trans (hb n d), hr⟩
end MIPRE.Cost

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Cost.Prog
open Cost
open Data
variable {ℓ : ℕ} (U : UniversalMachine) (S : CL.Sampler ℓ) (dec : Prog)
theorem _root_.solution (hS : S.prog.HasPolyCost) (hdim : PolyBounded S.dim)
    (hdec : dec.HasPolyCost) : (wrapCore U.univ S.prog (encode dec)).HasPolyCost := by
  obtain ⟨Cf, kf, hCf, hf⟩ := hS
  obtain ⟨Cd, kd, hCd, hdrun⟩ := hdec
  refine Prog.hasPolyCost_of_polyCost
    (B := fun n d => wrapCoreCost U S dec Cf kf n (Cd n * (d.size + 1) ^ kd) d.size) ?_
    (fun n d => wrapCore_cost' U S dec Cf kf hf n (fun s => Cd n * (s + 1) ^ kd) (hdrun n) d)
  -- the bound is polynomial in the index and the input size
  have hH : PolyBounded fun n => 60 * wrapHeadZ U S Cf kf n ^ 2 + 4 :=
    (((polyBounded_wrapHeadZ U S hCf kf hdim).pow 2).const_mul 60).add_const 4
  have hsz : PolyCost fun (_ : ℕ) (d : Data) => d.size := PolyCost.size
  have hn : PolyCost fun (n : ℕ) (_ : Data) => esize n :=
    PolyCost.ofIndex polyBounded_esize_nat
  have hdm : PolyCost fun (n : ℕ) (_ : Data) => S.dim n := PolyCost.ofIndex hdim
  have hchk : PolyCost fun (n : ℕ) (d : Data) => checkCost d.size (S.dim n) := by
    have hb : PolyCost fun (n : ℕ) (d : Data) => d.size + S.dim n + 30 :=
      ((hsz.add hdm).add (PolyCost.const 30))
    exact ((PolyCost.const 60).mul (hb.mul hb)).mono fun n d => by
      simp only [checkCost]; nlinarith [sq_nonneg (d.size + S.dim n + 30)]
  have hpow : PolyCost fun (_ : ℕ) (d : Data) => (d.size + 1) ^ kd :=
    (PolyCost.poly ((Polynomial.X + Polynomial.C 1) ^ kd) hsz).mono fun n d => by simp
  have hU : PolyCost fun (n : ℕ) (d : Data) =>
      U.bound.eval (esize dec + (esize n + d.size + 1) + Cd n * (d.size + 1) ^ kd) :=
    PolyCost.poly U.bound
      (((PolyCost.const (esize dec)).add ((hn.add hsz).add (PolyCost.const 1))).add
        ((PolyCost.ofIndex hCd).mul hpow))
  exact ((((PolyCost.ofIndex hH).add ((PolyCost.const 2).mul hchk)).add
    (((PolyCost.const 2).mul ((((PolyCost.const (esize dec)).add hn).add hsz).add
      (PolyCost.const 2))).add hU)).add (PolyCost.const 20))
end MIPRE.Cost.Prog
