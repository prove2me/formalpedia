-- Prove2me | solution 1 for MIPRE.LIDT.Simul.sum_mu_qmap_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:42:03.763971+00:00
-- url     : https://prove2.me/submissions/efe4c3f4-fd2e-46e8-af21-ef61159a9b0e

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Padding.lean (solution of MIPRE.LIDT.Simul.sum_mu_qmap_le);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Geometry
import Definitions.Def_MIPRE_Background_LIDT_Coefficients
import Definitions.Def_MIPRE_Background_LIDT_Extraction
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Seeds
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Reparam
import Definitions.Def_MIPRE_Background_LIDT_Padding
import Theorems.Thm_MIPRE_LIDT_Simul_card_sampleMap_fiber_le
import Theorems.Thm_MIPRE_LIDT_Simul_qmap_question

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LIDT.Simul
noncomputable section
open Finset MIPRE MIPRE.LIDT MIPRE.LIDT.CL MIPRE.LIDT.Adapter
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ} [NeZero m]
  [NeZero (K + m)] (hm : m ∣ Fintype.card F) (hM : (K + m) ∣ Fintype.card F)
theorem card_ty : Fintype.card CL.Ty = 3 := rfl
end
end MIPRE.LIDT.Simul

namespace MIPRE.LIDT.Simul
noncomputable section
open Finset MIPRE MIPRE.LIDT MIPRE.LIDT.CL MIPRE.LIDT.Adapter
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ} [NeZero m]
  [NeZero (K + m)] (hm : m ∣ Fintype.card F) (hM : (K + m) ∣ Fintype.card F)
omit [Field F] [DecidableEq F] in
theorem card_sample (n : ℕ) :
    Fintype.card (CL.Sample F n)
      = 9 * (Fintype.card F ^ n * (Fintype.card F * Fintype.card F ^ n)) := by
  rw [Fintype.card_congr (sampleEquiv n)]
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, card_ty]
  ring
end
end MIPRE.LIDT.Simul

namespace MIPRE.LIDT.Simul
noncomputable section
open Finset MIPRE MIPRE.LIDT MIPRE.LIDT.CL MIPRE.LIDT.Adapter
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ} [NeZero m]
  [NeZero (K + m)] (hm : m ∣ Fintype.card F) (hM : (K + m) ∣ Fintype.card F)
/-- The mass the seeded test puts on the fibre of a pair of question maps. -/
theorem clGame_mu_fibre {n l : ℕ} [NeZero n] (hn : n ∣ Fintype.card F) {X : Type*}
    [DecidableEq X] (qA qB : CL.Question F n → X) (x y : X) :
    ∑ x' ∈ Finset.univ.filter (fun x' => qA x' = x),
        ∑ y' ∈ Finset.univ.filter (fun y' => qB y' = y), (clGame (d := d) (ldc := l) hn).μ x' y'
      = ∑ sm : CL.Sample F n, (Fintype.card (CL.Sample F n) : ℝ)⁻¹ *
          if qA (sm.question hn sm.tyA) = x ∧ qB (sm.question hn sm.tyB) = y then 1 else 0 := by
  simp only [clGame]
  rw [Finset.sum_congr rfl fun x' _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun sm _ => ?_
  simp only [← Finset.mul_sum]
  congr 1
  simp only [Prod.mk.injEq, ite_and]
  simp [Finset.sum_ite_eq, Finset.sum_ite_irrel]
end
end MIPRE.LIDT.Simul

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LIDT.Simul
open Finset MIPRE MIPRE.LIDT MIPRE.LIDT.CL MIPRE.LIDT.Adapter
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ} [NeZero m]
  [NeZero (K + m)] (hm : m ∣ Fintype.card F) (hM : (K + m) ∣ Fintype.card F)
theorem _root_.solution (x y : CL.Question F m) :
    (∑ σ : Fin (Fintype.card F / m),
        ∑ x' ∈ Finset.univ.filter (fun x' => qmap hm hM σ x' = x),
        ∑ y' ∈ Finset.univ.filter (fun y' => qmap hm hM σ y' = y),
          (clGame (d := d) (ldc := 1) hM).μ x' y')
      ≤ (Fintype.card (Fin (Fintype.card F / m)) : ℝ)
          * ((9 * (K + 1) : ℝ) * (clGame (d := d) (ldc := r) hm).μ x y) := by
  classical
  set q := Fintype.card F
  set P : CL.Sample F m → Prop := fun sm =>
    sm.question hm sm.tyA = x ∧ sm.question hm sm.tyB = y
  set f : CL.Sample F m → ℝ := fun sm => if P sm then 1 else 0
  have hf0 : ∀ sm, 0 ≤ f sm := fun sm => by simp only [f]; split_ifs <;> norm_num
  set Φ : ℕ := 9 * ((K + 1) * (q / (K + m))) * q ^ K * q ^ K
  have hcond : ∀ σ (sm : CL.Sample F (K + m)),
      (if qmap hm hM σ (sm.question hM sm.tyA) = x ∧ qmap hm hM σ (sm.question hM sm.tyB) = y
        then (1 : ℝ) else 0) = f (sampleMap hm hM σ sm) := by
    intro σ sm
    simp only [f, P]
    rw [qmap_question, qmap_question]
    rfl
  have hL : (∑ σ : Fin (q / m),
        ∑ x' ∈ Finset.univ.filter (fun x' => qmap hm hM σ x' = x),
        ∑ y' ∈ Finset.univ.filter (fun y' => qmap hm hM σ y' = y),
          (clGame (d := d) (ldc := 1) hM).μ x' y')
      = (Fintype.card (CL.Sample F (K + m)) : ℝ)⁻¹ *
          ∑ p : Fin (q / m) × CL.Sample F (K + m), f (sampleMap hm hM p.1 p.2) := by
    simp_rw [clGame_mu_fibre, hcond, ← Finset.mul_sum]
    rw [Fintype.sum_prod_type]
  have hcount : ∑ p : Fin (q / m) × CL.Sample F (K + m), f (sampleMap hm hM p.1 p.2)
      ≤ ∑ sm : CL.Sample F m, (Φ : ℝ) * f sm := by
    rw [← Finset.sum_fiberwise (Finset.univ : Finset (Fin (q / m) × CL.Sample F (K + m)))
      (fun p => sampleMap hm hM p.1 p.2)]
    refine Finset.sum_le_sum fun sm _ => ?_
    rw [Finset.sum_congr rfl fun p hp => by rw [(Finset.mem_filter.mp hp).2],
      Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_sampleMap_fiber_le hm hM sm)
      (hf0 sm)
  have hR : (clGame (d := d) (ldc := r) hm).μ x y
      = (Fintype.card (CL.Sample F m) : ℝ)⁻¹ * ∑ sm : CL.Sample F m, f sm := by
    simp only [clGame, f, P, Prod.mk.injEq, Finset.mul_sum]
  have hq : 0 < q := Fintype.card_pos
  have hdiv : q / (K + m) ≤ q / m := Nat.div_le_div_left (by omega)
    (Nat.pos_of_ne_zero (NeZero.ne m))
  have hnat : Φ * Fintype.card (CL.Sample F m)
      ≤ q / m * (9 * (K + 1)) * Fintype.card (CL.Sample F (K + m)) := by
    rw [card_sample, card_sample]
    simp only [Φ, pow_add]
    have := Nat.mul_le_mul_right (9 * (K + 1) * q ^ K * q ^ K * (9 * (q ^ m * (q * q ^ m)))) hdiv
    nlinarith [this]
  have hN : (0 : ℝ) < Fintype.card (CL.Sample F m) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨(⟨.point, .point, 0, 0, 0⟩ : CL.Sample F m)⟩
  have hN' : (0 : ℝ) < Fintype.card (CL.Sample F (K + m)) := by
    exact_mod_cast Fintype.card_pos_iff.mpr
      ⟨(⟨.point, .point, 0, 0, 0⟩ : CL.Sample F (K + m))⟩
  have hreal : (Fintype.card (CL.Sample F (K + m)) : ℝ)⁻¹ * Φ
      ≤ (q / m : ℕ) * (9 * (K + 1)) * (Fintype.card (CL.Sample F m) : ℝ)⁻¹ := by
    rw [inv_mul_eq_div, mul_comm _ ((Fintype.card (CL.Sample F m) : ℝ)⁻¹), inv_mul_eq_div,
      div_le_div_iff₀ hN' hN]
    exact_mod_cast hnat
  rw [hL, hR, Fintype.card_fin]
  have hS0 : 0 ≤ ∑ sm : CL.Sample F m, f sm := Finset.sum_nonneg fun sm _ => hf0 sm
  calc (Fintype.card (CL.Sample F (K + m)) : ℝ)⁻¹ *
        ∑ p : Fin (q / m) × CL.Sample F (K + m), f (sampleMap hm hM p.1 p.2)
      ≤ (Fintype.card (CL.Sample F (K + m)) : ℝ)⁻¹ * ∑ sm : CL.Sample F m, (Φ : ℝ) * f sm :=
        mul_le_mul_of_nonneg_left hcount (by positivity)
    _ = ((Fintype.card (CL.Sample F (K + m)) : ℝ)⁻¹ * Φ) * ∑ sm : CL.Sample F m, f sm := by
        rw [← Finset.mul_sum]; ring
    _ ≤ ((q / m : ℕ) * (9 * (K + 1)) * (Fintype.card (CL.Sample F m) : ℝ)⁻¹)
          * ∑ sm : CL.Sample F m, f sm := mul_le_mul_of_nonneg_right hreal hS0
    _ = _ := by ring
end MIPRE.LIDT.Simul
