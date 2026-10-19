-- Prove2me | solution 1 for MIPRE.LIDT.Adapter.pushforward_point
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:28:04.245401+00:00
-- url     : https://prove2.me/submissions/e86af10e-1505-420a-9c47-f299fe8a7bb9

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Adapter/Weights.lean (solution of MIPRE.LIDT.Adapter.pushforward_point);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Geometry
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Seeds
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Reparam
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Strategy
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Weights
import Theorems.Thm_MIPRE_LIDT_Adapter_card_filter_clPoint_ge
import Theorems.Thm_MIPRE_LIDT_Adapter_filter_qmapS_point_subset
import Theorems.Thm_MIPRE_LIDT_Adapter_sum_fibre_mu_eq_sum_samples
import Theorems.Thm_MIPRE_LIDT_Adapter_sum_sum_le_card_mul
import Theorems.Thm_MIPRE_LIDT_CL_card_div_pos

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LIDT.Adapter
section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
/-- **The seeded test's distribution, as a count.** It is uniform over its samples, so the
weight of a question pair is the number of samples producing it over the total. -/
theorem clGame_μ_eq (hm : m ∣ Fintype.card F) (x y : CL.Question F m) :
    (clGame (d := d) (ldc := ldc) hm).μ x y
      = ((Finset.univ.filter (fun sm : CL.Sample F m =>
            (sm.question hm sm.tyA, sm.question hm sm.tyB) = (x, y))).card : ℝ)
          / (Fintype.card (CL.Sample F m) : ℝ) := by
  classical
  show ∑ sm : CL.Sample F m, (Fintype.card (CL.Sample F m) : ℝ)⁻¹ *
    (if (sm.question hm sm.tyA, sm.question hm sm.tyB) = (x, y) then 1 else 0) = _
  rw [← Finset.mul_sum, Finset.sum_boole, div_eq_inv_mul]
end
end MIPRE.LIDT.Adapter

namespace MIPRE.LIDT.Adapter
section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
/-- And if the two points differ, nothing contributes: the one candidate fails the second
condition. -/
theorem filter_qmapS_point_eq_empty (hm : m ∣ Fintype.card F) (σc : Seed F m)
    {xp yp : Point F m} (hxy : xp ≠ yp) :
    Finset.univ.filter (fun s : Sample F m =>
        qmapS hm σc s.questions.1 = CL.Question.point xp ∧
          qmapS hm σc s.questions.2 = CL.Question.point yp)
      = ∅ := by
  classical
  refine Finset.eq_empty_iff_forall_notMem.mpr fun s hs => ?_
  have hmem := filter_qmapS_point_subset hm σc xp yp hs
  rw [Finset.mem_singleton] at hmem
  subst hmem
  obtain ⟨_, h2⟩ := (Finset.mem_filter.mp hs).2
  have h : CL.Question.point (revPoint (revPoint xp)) = CL.Question.point yp := h2
  rw [revPoint_revPoint] at h
  injection h with h'
  exact hxy h'
end
end MIPRE.LIDT.Adapter

namespace MIPRE.LIDT.Adapter
section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
omit [DecidableEq F] [NeZero m] in
theorem card_clTy : Fintype.card CL.Ty = 3 := rfl
end
end MIPRE.LIDT.Adapter

namespace MIPRE.LIDT.Adapter
section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
omit [Field F] [DecidableEq F] [NeZero m] in
/-- **The seeded test's sample space**: nine ordered type pairs against `(u, s, v)`. -/
theorem card_clSample_eq :
    Fintype.card (CL.Sample F m)
      = 9 * (Fintype.card (Point F m) * (Fintype.card F * Fintype.card (Point F m))) := by
  have e : CL.Sample F m ≃ (CL.Ty × CL.Ty) × (Point F m × F × Point F m) :=
    { toFun := fun sm => ((sm.tyA, sm.tyB), (sm.u, sm.s, sm.v))
      invFun := fun p => ⟨p.1.1, p.1.2, p.2.1, p.2.2.1, p.2.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_prod, Fintype.card_prod, Fintype.card_prod,
    Fintype.card_prod, card_clTy]
end
end MIPRE.LIDT.Adapter

namespace MIPRE.LIDT.Adapter
section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
omit [NeZero m] in
/-- **The averaging family**: a fibre position per direction index, and one nonzero scale. -/
theorem card_seed_eq :
    Fintype.card (Seed F m)
      = (Fintype.card F / m) ^ m * (Fintype.card F - 1) := by
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  congr 1
  have h : Fintype.card {c : F // c ≠ 0} = Fintype.card F - Fintype.card {c : F // c = 0} :=
    Fintype.card_subtype_compl _
  rw [h, Fintype.card_subtype_eq]
end
end MIPRE.LIDT.Adapter

namespace MIPRE.LIDT.Adapter
section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
omit [DecidableEq F] in
theorem blk_pos (hm : m ∣ Fintype.card F) : (0 : ℝ) < blk F m := by
  exact_mod_cast card_div_pos hm
end
end MIPRE.LIDT.Adapter

namespace MIPRE.LIDT.Adapter
section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
omit [DecidableEq F] [NeZero m] in
theorem cast_card_sub_one :
    ((Fintype.card F - 1 : ℕ) : ℝ) = (Fintype.card F : ℝ) - 1 := by
  rw [Nat.cast_sub Fintype.card_pos, Nat.cast_one]
end
end MIPRE.LIDT.Adapter

namespace MIPRE.LIDT.Adapter
section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
omit [DecidableEq F] [NeZero m] in
theorem card_pos_real : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
end
end MIPRE.LIDT.Adapter

namespace MIPRE.LIDT.Adapter
section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
omit [DecidableEq F] [NeZero m] in
theorem card_point_pos_real : (0 : ℝ) < Fintype.card (Point F m) := by
  exact_mod_cast Fintype.card_pos
end
end MIPRE.LIDT.Adapter

namespace MIPRE.LIDT.Adapter
section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
omit [Field F] [Fintype F] [DecidableEq F] in
theorem m_pos_real : (0 : ℝ) < m := by
  exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
end
end MIPRE.LIDT.Adapter

namespace MIPRE.LIDT.Adapter
section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
omit [Field F] [Fintype F] [DecidableEq F] in
theorem one_le_m_real : (1 : ℝ) ≤ m := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)
end
end MIPRE.LIDT.Adapter

namespace MIPRE.LIDT.Adapter
section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
omit [NeZero m] in
/-- The averaging family's size, as a real. -/
theorem card_seed_real :
    (Fintype.card (Seed F m) : ℝ) = blk F m ^ m * ((Fintype.card F : ℝ) - 1) := by
  rw [card_seed_eq]
  push_cast [cast_card_sub_one]
  ring
end
end MIPRE.LIDT.Adapter

namespace MIPRE.LIDT.Adapter
section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
omit [Field F] [DecidableEq F] [NeZero m] in
/-- The seeded test's sample space, as a real. -/
theorem cast_card_clSample :
    (Fintype.card (CL.Sample F m) : ℝ)
      = 9 * ((Fintype.card (Point F m) : ℝ) *
          ((Fintype.card F : ℝ) * (Fintype.card (Point F m) : ℝ))) := by
  rw [card_clSample_eq]
  push_cast
  ring
end
end MIPRE.LIDT.Adapter

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LIDT.Adapter
open Finset MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
theorem _root_.solution (hm : m ∣ Fintype.card F) (xp yp : Point F m) :
    (∑ σc : Seed F m,
        ∑ x' ∈ Finset.univ.filter (fun x' => qmapS hm σc x' = CL.Question.point xp),
        ∑ y' ∈ Finset.univ.filter (fun y' => qmapS hm σc y' = CL.Question.point yp),
          (lidtGame F m d).μ x' y')
      ≤ (Fintype.card (Seed F m) : ℝ) *
          (3 * m * (clGame (d := d) (ldc := ldc) hm).μ
            (CL.Question.point xp) (CL.Question.point yp)) := by
  classical
  have hsamples : ∀ σc : Seed F m,
      (∑ x' ∈ Finset.univ.filter (fun x' => qmapS hm σc x' = CL.Question.point xp),
        ∑ y' ∈ Finset.univ.filter (fun y' => qmapS hm σc y' = CL.Question.point yp),
          (lidtGame F m d).μ x' y')
      = ∑ s ∈ Finset.univ.filter (fun s : Sample F m =>
          qmapS hm σc s.questions.1 = CL.Question.point xp ∧
            qmapS hm σc s.questions.2 = CL.Question.point yp), s.weight := fun σc =>
    sum_fibre_mu_eq_sum_samples (d := d) (qmapS hm σc) (qmapS hm σc) _ _
  rw [Finset.sum_congr rfl fun σc (_ : σc ∈ Finset.univ) => hsamples σc]
  by_cases hxy : xp = yp
  · subst hxy
    have hle := sum_sum_le_card_mul (S := Seed F m) (ι := Sample F m)
      (fun s => s.weight) (fun s => s.weight_nonneg)
      (fun σc s => qmapS hm σc s.questions.1 = CL.Question.point xp ∧
          qmapS hm σc s.questions.2 = CL.Question.point xp)
      {Sample.selfConsistency (revPoint xp)}
      (1 / (3 * Fintype.card (Point F m))) (Fintype.card (Seed F m))
      (fun σc s hc => filter_qmapS_point_subset hm σc xp xp
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩))
      (fun s hs => by rw [Finset.mem_singleton] at hs; subst hs; exact le_of_eq rfl)
      (fun s _ => Finset.card_le_univ _)
    refine hle.trans ?_
    rw [Finset.card_singleton, Nat.cast_one, clGame_μ_eq, cast_card_clSample, card_seed_real]
    have hcnt : (Fintype.card F : ℝ) * (Fintype.card (Point F m) : ℝ)
        ≤ ((Finset.univ.filter (fun sm : CL.Sample F m =>
            (sm.question hm sm.tyA, sm.question hm sm.tyB)
              = ((CL.Question.point xp : CL.Question F m), CL.Question.point xp))).card : ℝ) := by
      exact_mod_cast card_filter_clPoint_ge hm xp
    set q : ℝ := (Fintype.card F : ℝ) with hqdef
    set P : ℝ := (Fintype.card (Point F m) : ℝ) with hPdef
    set N : ℝ := blk F m with hNdef
    have hq : (0 : ℝ) < q := card_pos_real
    have hq1 : (1 : ℝ) ≤ q := by rw [hqdef]; exact_mod_cast Fintype.card_pos
    have hP : (0 : ℝ) < P := card_point_pos_real
    have hmR : (0 : ℝ) < m := m_pos_real
    have hm1 : (1 : ℝ) ≤ m := one_le_m_real
    have hN : (0 : ℝ) < N := blk_pos hm
    have hden : (0 : ℝ) < 9 * (P * (q * P)) := by positivity
    have h3P : (0 : ℝ) < 3 * P := by positivity
    have hA : (0 : ℝ) ≤ N ^ m * (q - 1) := mul_nonneg (by positivity) (by linarith)
    have hval : 3 * (m : ℝ) * ((q * P) / (9 * (P * (q * P)))) = (m : ℝ) / (3 * P) := by
      field_simp
      ring
    calc (1 : ℝ) * (1 / (3 * P) * (N ^ m * (q - 1)))
        = 1 / (3 * P) * (N ^ m * (q - 1)) := one_mul _
      _ ≤ (3 * m * ((q * P) / (9 * (P * (q * P))))) * (N ^ m * (q - 1)) := by
          refine mul_le_mul_of_nonneg_right ?_ hA
          rw [hval, div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right hm1 (le_of_lt (inv_pos.mpr h3P))
      _ = N ^ m * (q - 1) * (3 * m * ((q * P) / (9 * (P * (q * P))))) := by ring
      _ ≤ N ^ m * (q - 1) * (3 * m *
            (((Finset.univ.filter (fun sm : CL.Sample F m =>
              (sm.question hm sm.tyA, sm.question hm sm.tyB)
                = ((CL.Question.point xp : CL.Question F m),
                    CL.Question.point xp))).card : ℝ) / (9 * (P * (q * P))))) := by
          refine mul_le_mul_of_nonneg_left ?_ hA
          refine mul_le_mul_of_nonneg_left ?_ (by positivity : (0:ℝ) ≤ 3 * (m:ℝ))
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right hcnt (le_of_lt (inv_pos.mpr hden))
  · have hzero : ∀ σc : Seed F m,
        (∑ s ∈ Finset.univ.filter (fun s : Sample F m =>
          qmapS hm σc s.questions.1 = CL.Question.point xp ∧
            qmapS hm σc s.questions.2 = CL.Question.point yp), s.weight) = 0 := by
      intro σc
      rw [filter_qmapS_point_eq_empty hm σc hxy, Finset.sum_empty]
    rw [Finset.sum_congr rfl fun σc (_ : σc ∈ Finset.univ) => hzero σc, Finset.sum_const_zero]
    refine mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by positivity) ?_)
    exact (clGame (d := d) (ldc := ldc) hm).μ_nonneg _ _
end MIPRE.LIDT.Adapter
