-- Prove2me | solution 1 for MIPRE.AnswerReduction.side_honest
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:40:14.146041+00:00
-- url     : https://prove2.me/submissions/12afdd75-52f4-4b25-9159-d46ff63b6f02

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/AnswerReduction/Honest.lean (solution of MIPRE.AnswerReduction.side_honest);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Background_LIDT_Presentation
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
import Definitions.Def_MIPRE_Background_AnswerReduction_PcpPresentation
import Definitions.Def_MIPRE_Foundations_OracularGame
import Definitions.Def_MIPRE_Background_AnswerReduction_Predicate
import Definitions.Def_MIPRE_Foundations_LowDegree_LineRestrict
import Definitions.Def_MIPRE_Background_LIDT_CLHonest
import Definitions.Def_MIPRE_Background_AnswerReduction_Honest
import Theorems.Thm_MIPRE_AnswerReduction_Pcp_pt6_block
import Theorems.Thm_MIPRE_LIDT_CL_Regs_questionOf_eval
import Theorems.Thm_MIPRE_LIDT_CL_accepts_honest

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.CL
section
open Finset Module Submodule LinearMap
variable {F : Type*} [Field F] {n : ℕ}
/-- **A point differs from its canonical representative by an element of `S`.** For a line ---
`S = span {w}` --- this is the statement that the base point the seeded test reports lies on the
line through the sampled point, which is what lets a line answer be evaluated at the point. -/
theorem sub_canonLin_mem (S : Submodule F (Fin n → F)) (x : Fin n → F) :
    x - canonLin S x ∈ S :=
  Submodule.sub_projection_mem _ x
end
end MIPRE.CL

namespace MIPRE.AnswerReduction.Pcp
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT
variable (P : PcpParams)
/-- **The overlap**: the `i`-th block of the sixth copy's point, in the PCP's block order, is the
`i`-th copy's point. -/
theorem block_ptOf_regs6 {F : Type*} [Field F] (i : Fin 5) (x : Coord P → F) :
    P.block i ((regs6 P).ptOf x) = (regs P i).ptOf x := by
  funext j
  simp only [PcpParams.block, Regs.ptOf, regs6, regs]
  rw [pt6_block]
end
end MIPRE.AnswerReduction.Pcp

namespace MIPRE.LIDT.CL
noncomputable section
open Finset MIPRE.CL MIPRE.LowDegree
variable {F : Type*} [Field F] {m : ℕ}
theorem canonLin_canonLin (S : Submodule F (Fin m → F)) (x : Fin m → F) :
    canonLin S (canonLin S x) = canonLin S x := by
  have h : canonLin S (x - canonLin S x) = 0 := by
    rw [← LinearMap.mem_ker, ker_canonLin]
    exact sub_canonLin_mem S x
  rw [map_sub, sub_eq_zero] at h
  exact h.symm
end
end MIPRE.LIDT.CL

namespace MIPRE.LIDT.CL
noncomputable section
open Finset MIPRE.CL MIPRE.LowDegree
variable {F : Type*} [Field F] {m : ℕ}
theorem rep_rep (w u : Point F m) : rep w (rep w u) = rep w u := canonLin_canonLin _ u
end
end MIPRE.LIDT.CL

namespace MIPRE.LIDT.CL
noncomputable section
open Finset MIPRE.CL MIPRE.LowDegree
variable {F : Type*} [Field F] {m : ℕ}
theorem zeroBelow_zeroBelow (i : Fin m) (v : Point F m) :
    zeroBelow i (zeroBelow i v) = zeroBelow i v := by
  funext k
  simp only [zeroBelow]
  split_ifs <;> rfl
end
end MIPRE.LIDT.CL

namespace MIPRE.LIDT.CL
noncomputable section
open Finset MIPRE.CL MIPRE.LowDegree
variable {F : Type*} [Field F] {m : ℕ}
variable [Fintype F] [DecidableEq F] [NeZero m] (hm : m ∣ Fintype.card F) {d ldc : ℕ}
variable {hm}
omit [DecidableEq F] in
/-- The sample's own questions are already canonical. -/
theorem recanon_question (sm : Sample F m) (τ : Ty) :
    recanon (hm := hm) (sm.question hm τ) = sm.question hm τ := by
  cases τ <;> simp [recanon, Sample.question, rep_rep, zeroBelow_zeroBelow]
end
end MIPRE.LIDT.CL

namespace MIPRE.LIDT.CL.Regs
noncomputable section
open Finset MIPRE.CL MIPRE.LowDegree
variable {F : Type*} [Field F] {m : ℕ}
variable [Fintype F] [DecidableEq F] [NeZero m] (hm : m ∣ Fintype.card F) {d ldc : ℕ}
variable {hm}
variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : Regs ι m) (S : Sel F m hm)
omit [DecidableEq ι] [Fintype ι] in
theorem sampleOf_question (τ : Ty) (y : ι → F) :
    (R.sampleOf S τ y).question hm τ = recanon (hm := hm) (R.questionOf S τ y) := by
  cases τ <;> rfl
end
end MIPRE.LIDT.CL.Regs

namespace MIPRE.LIDT.CL.Regs
noncomputable section
open Finset MIPRE.CL MIPRE.LowDegree
variable {F : Type*} [Field F] {m : ℕ}
variable [Fintype F] [DecidableEq F] [NeZero m] (hm : m ∣ Fintype.card F) {d ldc : ℕ}
variable {hm}
variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : Regs ι m) (S : Sel F m hm)
/-- **Reading the sample back off the presentation's output** gives the question it computes. -/
theorem sampleOf_eval_question (τ : Ty) (x : ι → F) :
    (R.sampleOf S τ ((R.pres S τ).eval x)).question hm τ = (R.sampleOf S τ x).question hm τ := by
  rw [sampleOf_question, questionOf_eval, recanon_question]
end
end MIPRE.LIDT.CL.Regs

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT Pcp
variable {P : PcpParams} {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable [NeZero P.m] {hm : P.m ∣ Fintype.card F} {hm' : P.m' ∣ Fintype.card F}
  (S : Sel F P.m hm) (S' : Sel F P.m' hm')
theorem honestAns_lt (H : HPolys P F) {i : Fin 6} (τ : Ty) (y : Coord P → F)
    (h : (i : ℕ) < 5) : honestAns S S' H (i, τ) y =
      .inl (LIDT.CL.honest hm (d := dPcp) (fun _ => H.g ⟨i, h⟩) (q1 S ⟨i, h⟩ τ y)) := by
  simp [honestAns, h]
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT Pcp
variable {P : PcpParams} {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable [NeZero P.m] {hm : P.m ∣ Fintype.card F} {hm' : P.m' ∣ Fintype.card F}
  (S : Sel F P.m hm) (S' : Sel F P.m' hm')
theorem honestAns_six (H : HPolys P F) {i : Fin 6} (τ : Ty) (y : Coord P → F)
    (h : (i : ℕ) = 5) : honestAns S S' H (i, τ) y =
      .inr (LIDT.CL.honest hm' (d := dPcp) H.c (q6 S' τ y)) := by
  simp [honestAns, h]
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT Pcp
variable {P : PcpParams} {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable [NeZero P.m] {hm : P.m ∣ Fintype.card F} {hm' : P.m' ∣ Fintype.card F}
  (S : Sel F P.m hm) (S' : Sel F P.m' hm')
omit [NeZero P.m] in
theorem ptOf_point_eval {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} [NeZero n]
    {hn : n ∣ Fintype.card F} (R : Regs ι n) (Sn : Sel F n hn) (w : ι → F) :
    R.ptOf ((R.pres Sn .point).eval w) = R.ptOf w := by
  have h := Regs.questionOf_eval R Sn .point w
  simp only [Regs.questionOf, Regs.sampleOf, Sample.question, CL.Question.point.injEq] at h
  exact h
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT Pcp
variable {P : PcpParams} {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable [NeZero P.m] {hm : P.m ∣ Fintype.card F} {hm' : P.m' ∣ Fintype.card F}
  (S : Sel F P.m hm) (S' : Sel F P.m' hm')
theorem pres_lt (w : Coord P → F) {i : Fin 6} (τ : Ty) (h : (i : ℕ) < 5) :
    (pres P S S' (i, τ)).eval w = ((regs P ⟨i, h⟩).pres S τ).eval w := by
  simp [pres, h]
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT Pcp
variable {P : PcpParams} {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable [NeZero P.m] {hm : P.m ∣ Fintype.card F} {hm' : P.m' ∣ Fintype.card F}
  (S : Sel F P.m hm) (S' : Sel F P.m' hm')
theorem pres_six (w : Coord P → F) {i : Fin 6} (τ : Ty) (h : (i : ℕ) = 5) :
    (pres P S S' (i, τ)).eval w = ((regs6 P).pres S' τ).eval w := by
  simp [pres, h]
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT Pcp
variable {P : PcpParams} {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable [NeZero P.m] {hm : P.m ∣ Fintype.card F} {hm' : P.m' ∣ Fintype.card F}
  (S : Sel F P.m hm) (S' : Sel F P.m' hm')
/-- The point of copy `v`'s register, in the `Point_v` question. -/
theorem ptOf_regs_point (w : Coord P → F) (v : Fin 5) :
    (regs P v).ptOf ((pres P S S' (v.castSucc, .point)).eval w) = (regs P v).ptOf w := by
  rw [pres_lt S S' w .point (by simp)]
  exact ptOf_point_eval _ _ w
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT Pcp
variable {P : PcpParams} {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable [NeZero P.m] {hm : P.m ∣ Fintype.card F} {hm' : P.m' ∣ Fintype.card F}
  (S : Sel F P.m hm) (S' : Sel F P.m' hm')
/-- The point of copy `v`'s register, in the `Point_6` question: the `v`-th block. -/
theorem ptOf_regs_point6 (w : Coord P → F) (v : Fin 5) {i : Fin 6} (h : (i : ℕ) = 5) :
    (regs P v).ptOf ((pres P S S' (i, .point)).eval w) = (regs P v).ptOf w := by
  rw [pres_six S S' w .point h, ← block_ptOf_regs6, ptOf_point_eval, block_ptOf_regs6]
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT Pcp
variable {P : PcpParams} {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable [NeZero P.m] {hm : P.m ∣ Fintype.card F} {hm' : P.m' ∣ Fintype.card F}
  (S : Sel F P.m hm) (S' : Sel F P.m' hm')
theorem q1_eval (w : Coord P → F) (v : Fin 5) (τ : Ty) :
    q1 S v τ ((pres P S S' (v.castSucc, τ)).eval w) =
      ((regs P v).sampleOf S τ w).question hm τ := by
  rw [pres_lt S S' w τ (by simp), q1]
  exact Regs.sampleOf_eval_question _ _ _ _
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT Pcp
variable {P : PcpParams} {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable [NeZero P.m] {hm : P.m ∣ Fintype.card F} {hm' : P.m' ∣ Fintype.card F}
  (S : Sel F P.m hm) (S' : Sel F P.m' hm')
theorem q6_eval (w : Coord P → F) {i : Fin 6} (τ : Ty) (h : (i : ℕ) = 5) :
    q6 S' τ ((pres P S S' (i, τ)).eval w) = ((regs6 P).sampleOf S' τ w).question hm' τ := by
  rw [pres_six S S' w τ h, q6]
  exact Regs.sampleOf_eval_question _ _ _ _
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT Pcp
variable {P : PcpParams} {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable [NeZero P.m] {hm : P.m ∣ Fintype.card F} {hm' : P.m' ∣ Fintype.card F}
  (S : Sel F P.m hm) (S' : Sel F P.m' hm')
theorem val1_honest (H : HPolys P F) (v : Fin 5) (y : Coord P → F) :
    val1 (honestAns S S' H (v.castSucc, .point) y) =
      MvPolynomial.eval ((regs P v).ptOf y) (H.g v) := by
  rw [honestAns_lt S S' H .point y (by simp)]
  rfl
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT Pcp
variable {P : PcpParams} {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable [NeZero P.m] {hm : P.m ∣ Fintype.card F} {hm' : P.m' ∣ Fintype.card F}
  (S : Sel F P.m hm) (S' : Sel F P.m' hm')
theorem val6_honest (H : HPolys P F) {i : Fin 6} (h : (i : ℕ) = 5) (j : Fin (P.m' + 6))
    (y : Coord P → F) :
    val6 j (honestAns S S' H (i, .point) y) = MvPolynomial.eval ((regs6 P).ptOf y) (H.c j) := by
  rw [honestAns_six S S' H .point y h]
  rfl
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT Pcp
variable {P : PcpParams} {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable [NeZero P.m] {hm : P.m ∣ Fintype.card F} {hm' : P.m' ∣ Fintype.card F}
  (S : Sel F P.m hm) (S' : Sel F P.m' hm')
theorem vals6_honest (H : HPolys P F) {i : Fin 6} (h : (i : ℕ) = 5) (y : Coord P → F) :
    vals6 (honestAns S S' H (i, .point) y) =
      fun j => MvPolynomial.eval ((regs6 P).ptOf y) (H.c j) := by
  rw [honestAns_six S S' H .point y h]
  rfl
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT Pcp
variable {P : PcpParams} {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable [NeZero P.m] {hm : P.m ∣ Fintype.card F} {hm' : P.m' ∣ Fintype.card F}
  (S : Sel F P.m hm) (S' : Sel F P.m' hm')
theorem ans1_honest (H : HPolys P F) (v : Fin 5) (τ : Ty) (y : Coord P → F) :
    ans1 (honestAns S S' H (v.castSucc, τ) y) =
      LIDT.CL.honest hm (d := dPcp) (fun _ => H.g v) (q1 S v τ y) := by
  rw [honestAns_lt S S' H τ y (by simp)]
  rfl
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT Pcp
variable {P : PcpParams} {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable [NeZero P.m] {hm : P.m ∣ Fintype.card F} {hm' : P.m' ∣ Fintype.card F}
  (S : Sel F P.m hm) (S' : Sel F P.m' hm')
theorem ans6_honest (H : HPolys P F) {i : Fin 6} (h : (i : ℕ) = 5) (τ : Ty) (y : Coord P → F) :
    ans6 (honestAns S S' H (i, τ) y) = LIDT.CL.honest hm' (d := dPcp) H.c (q6 S' τ y) := by
  rw [honestAns_six S S' H τ y h]
  rfl
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT Pcp
variable {P : PcpParams} {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable [NeZero P.m] {hm : P.m ∣ Fintype.card F} {hm' : P.m' ∣ Fintype.card F}
  (S : Sel F P.m hm) (S' : Sel F P.m' hm')
/-- The low-degree test of copy `v ≤ 5` on honest answers to two questions of one PCP vector. -/
theorem accepts_q1_honest {g : MvPolynomial (Fin P.m) F} (hg : ∀ i, g.degreeOf i ≤ dPcp)
    (v : Fin 5) (τ τ' : Ty) (w : Coord P → F) :
    CL.accepts hm (q1 S v τ ((pres P S S' (v.castSucc, τ)).eval w))
      (q1 S v τ' ((pres P S S' (v.castSucc, τ')).eval w))
      (LIDT.CL.honest hm (d := dPcp) (fun _ : Fin 1 => g)
        (q1 S v τ ((pres P S S' (v.castSucc, τ)).eval w)))
      (LIDT.CL.honest hm (d := dPcp) (fun _ : Fin 1 => g)
        (q1 S v τ' ((pres P S S' (v.castSucc, τ')).eval w))) = true := by
  rw [q1_eval, q1_eval]
  exact LIDT.CL.accepts_honest (fun _ => hg) ((regs P v).sampleOf S τ w) τ τ'
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT Pcp
variable {P : PcpParams} {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable [NeZero P.m] {hm : P.m ∣ Fintype.card F} {hm' : P.m' ∣ Fintype.card F}
  (S : Sel F P.m hm) (S' : Sel F P.m' hm')
/-- The low-degree test of copy `6` on honest answers to two questions of one PCP vector. -/
theorem accepts_q6_honest {c : Fin (P.m' + 6) → MvPolynomial (Fin P.m') F}
    (hc : ∀ j i, (c j).degreeOf i ≤ dPcp) {i i' : Fin 6} (h : (i : ℕ) = 5) (h' : (i' : ℕ) = 5)
    (τ τ' : Ty) (w : Coord P → F) :
    CL.accepts hm' (q6 S' τ ((pres P S S' (i, τ)).eval w))
      (q6 S' τ' ((pres P S S' (i', τ')).eval w))
      (LIDT.CL.honest hm' (d := dPcp) c (q6 S' τ ((pres P S S' (i, τ)).eval w)))
      (LIDT.CL.honest hm' (d := dPcp) c (q6 S' τ' ((pres P S S' (i', τ')).eval w))) = true := by
  rw [q6_eval S S' w τ h, q6_eval S S' w τ' h']
  exact LIDT.CL.accepts_honest hc ((regs6 P).sampleOf S' τ w) τ τ'
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT Pcp
variable {P : PcpParams} {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable [NeZero P.m] {hm : P.m ∣ Fintype.card F} {hm' : P.m' ∣ Fintype.card F}
  (S : Sel F P.m hm) (S' : Sel F P.m' hm')
variable {X : Type*} (check : X → (Fin P.m' → F) → (Fin (P.m' + 6) → F) → Bool)
theorem roleIdx_injective {r r' : Role} {v : Fin 5} (h : roleIdx r = some v)
    (h' : roleIdx r' = some v) : r = r' := by
  cases r <;> cases r' <;> simp only [roleIdx, Option.some.injEq, reduceCtorEq] at h h' <;>
    first | rfl | (subst h; exact absurd h' (by decide))
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT Pcp
variable {P : PcpParams} {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable [NeZero P.m] {hm : P.m ∣ Fintype.card F} {hm' : P.m' ∣ Fintype.card F}
  (S : Sel F P.m hm) (S' : Sel F P.m' hm')
variable {X : Type*} (check : X → (Fin P.m' → F) → (Fin (P.m' + 6) → F) → Bool)
/-- Step 2's comparison, or step 4's: an oracle's `Point_6` value on block `v` against a
`Point_v` value of data with the same `g_v`. -/
theorem val6_eq_val1 {chk : (Fin P.m' → F) → (Fin (P.m' + 6) → F) → Bool} (Hp Hq : HPolys P F)
    (ho : Hp.Oracle chk) (v : Fin 5) (hg : Hq.g v = Hp.g v) {i : Fin 6} (h5 : (i : ℕ) = 5)
    (w : Coord P → F) :
    val6 (HPolys.idx6 v) (honestAns S S' Hp (i, .point) ((pres P S S' (i, .point)).eval w)) =
      val1 (honestAns S S' Hq (v.castSucc, .point)
        ((pres P S S' (v.castSucc, .point)).eval w)) := by
  rw [val6_honest S S' Hp h5, val1_honest, ho.1, block_ptOf_regs6, ptOf_regs_point6 S S' w v h5,
    ptOf_regs_point, hg]
end
end MIPRE.AnswerReduction

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.AnswerReduction
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT Pcp
variable {P : PcpParams} {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable [NeZero P.m] {hm : P.m ∣ Fintype.card F} {hm' : P.m' ∣ Fintype.card F}
  (S : Sel F P.m hm) (S' : Sel F P.m' hm')
variable {X : Type*} (check : X → (Fin P.m' → F) → (Fin (P.m' + 6) → F) → Bool)
theorem _root_.solution (tp tq : Role × PcpTy) (xp xq : X) (w : Coord P → F) (Hp Hq : HPolys P F)
    (hp : Hp.LowDeg) (hpo : tp.1 = .oracle → Hp.Oracle (check xp))
    (hc : Consistent tp.1 tq.1 Hp Hq) :
    side S S' check (tp, xp, (pres P S S' tp.2).eval w) (tq, xq, (pres P S S' tq.2).eval w)
      (honestAns S S' Hp tp.2 ((pres P S S' tp.2).eval w))
      (honestAns S S' Hq tq.2 ((pres P S S' tq.2).eval w)) = true := by
  obtain ⟨rp, ip, τp⟩ := tp
  obtain ⟨rq, iq, τq⟩ := tq
  simp only [side, Bool.and_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · -- step 2
    cases rp
    · cases hv : roleIdx rq with
      | none => rfl
      | some v =>
        simp only
        split_ifs with h
        · obtain ⟨h5, rfl, hi, rfl⟩ := h
          obtain rfl : iq = v.castSucc := Fin.ext hi
          rw [decide_eq_true_eq]
          exact val6_eq_val1 S S' Hp Hq (hpo rfl) v (hc.orc v rfl hv) h5 w
        · rfl
    all_goals cases roleIdx rq <;> rfl
  · -- step 3
    cases hvp : roleIdx rp with
    | none => rfl
    | some v =>
      cases hvq : roleIdx rq with
      | none => rfl
      | some v' =>
        simp only
        split_ifs with h
        · obtain ⟨rfl, hi, hi', rfl, -⟩ := h
          obtain rfl : ip = v.castSucc := Fin.ext hi
          obtain rfl : iq = v.castSucc := Fin.ext hi'
          have hr : rp = rq := roleIdx_injective hvp hvq
          rw [ans1_honest, ans1_honest, ← hc.same hr]
          exact accepts_q1_honest S S' (hp.1 _) _ _ _ w
        · rfl
  · -- step 4
    split
    · rename_i hoo
      obtain ⟨hr, hr'⟩ := hoo
      obtain rfl : Hp = Hq := hc.same (hr.trans hr'.symm)
      simp only [Bool.and_eq_true]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · split
        · rename_i h
          obtain ⟨-, hlt, rfl, h5, rfl⟩ := h
          obtain ⟨v, rfl⟩ : ∃ v : Fin 5, ip = v.castSucc := ⟨⟨ip, hlt⟩, Fin.ext rfl⟩
          rw [decide_eq_true_eq]
          exact (val6_eq_val1 S S' Hp Hp (hpo hr) v rfl h5 w).symm
        · rfl
      · split
        · rename_i h
          obtain ⟨-, hlt, hqi, rfl, -⟩ := h
          obtain ⟨v, hv⟩ : ∃ v : Fin 5, ip = v.castSucc := ⟨⟨ip, hlt⟩, Fin.ext rfl⟩
          subst hv
          subst hqi
          rw [ans1_honest, ans1_honest]
          exact accepts_q1_honest S S' (hp.1 v) v _ _ w
        · rfl
      · split
        · rename_i h
          obtain ⟨h5, h5', rfl, -⟩ := h
          rw [ans6_honest S S' Hp h5, ans6_honest S S' Hp h5']
          exact accepts_q6_honest S S' hp.2 h5 h5' _ _ w
        · rfl
    · rfl
  · -- step 5
    split_ifs with h
    · obtain ⟨hr, h5, rfl⟩ := h
      rw [vals6_honest S S' Hp h5]
      exact (hpo hr).2 _
    · rfl
end MIPRE.AnswerReduction
