-- Prove2me | solution 1 for MIPRE.LIDT.Adapter.pushforward_axis
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:30:48.259653+00:00
-- url     : https://prove2.me/submissions/f7e898ae-efb2-42aa-b6ed-39946c13152c

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Adapter/Weights.lean (solution of MIPRE.LIDT.Adapter.pushforward_axis);
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
import Theorems.Thm_MIPRE_LIDT_Adapter_base_of_qmapS_axis
import Theorems.Thm_MIPRE_LIDT_Adapter_card_filter_axis_le
import Theorems.Thm_MIPRE_LIDT_Adapter_filter_qmapS_axis_subset
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
/-- Likewise for an axis-parallel line against a point: one sample for every raw direction. -/
theorem card_filter_clAxis_ge (hm : m ∣ Fintype.card F) (xp : Point F m) (s₀ : F) :
    Fintype.card (Point F m)
      ≤ (Finset.univ.filter (fun sm : CL.Sample F m =>
          (sm.question hm sm.tyA, sm.question hm sm.tyB)
            = ((CL.Question.aline (rep (Pi.single (chi hm s₀) 1) xp) s₀ : CL.Question F m),
                CL.Question.point xp))).card := by
  classical
  have hcard : Fintype.card (Point F m) = (Finset.univ : Finset (Point F m)).card := by simp
  rw [hcard]
  refine Finset.card_le_card_of_injOn
    (fun v => ({tyA := .aline, tyB := .point, u := xp, s := s₀, v := v} : CL.Sample F m))
    (fun v _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩) ?_
  intro a _ b _ hab
  exact congrArg CL.Sample.v hab
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
omit [Field F] [DecidableEq F] [NeZero m] in
theorem m_mul_blk (hm : m ∣ Fintype.card F) :
    (m : ℝ) * blk F m = (Fintype.card F : ℝ) := by
  exact_mod_cast Nat.mul_div_cancel' hm
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
theorem _root_.solution (hm : m ∣ Fintype.card F) (u₀ : Point F m) (s₀ : F) (yp : Point F m) :
    (∑ σc : Seed F m,
        ∑ x' ∈ Finset.univ.filter (fun x' => qmapS hm σc x' = CL.Question.aline u₀ s₀),
        ∑ y' ∈ Finset.univ.filter (fun y' => qmapS hm σc y' = CL.Question.point yp),
          (lidtGame F m d).μ x' y')
      ≤ (Fintype.card (Seed F m) : ℝ) *
          (3 * m * (clGame (d := d) (ldc := ldc) hm).μ
            (CL.Question.aline u₀ s₀) (CL.Question.point yp)) := by
  classical
  have hsamples : ∀ σc : Seed F m,
      (∑ x' ∈ Finset.univ.filter (fun x' => qmapS hm σc x' = CL.Question.aline u₀ s₀),
        ∑ y' ∈ Finset.univ.filter (fun y' => qmapS hm σc y' = CL.Question.point yp),
          (lidtGame F m d).μ x' y')
      = ∑ s ∈ Finset.univ.filter (fun s : Sample F m =>
          qmapS hm σc s.questions.1 = CL.Question.aline u₀ s₀ ∧
            qmapS hm σc s.questions.2 = CL.Question.point yp), s.weight := fun σc =>
    sum_fibre_mu_eq_sum_samples (d := d) (qmapS hm σc) (qmapS hm σc) _ _
  rw [Finset.sum_congr rfl fun σc (_ : σc ∈ Finset.univ) => hsamples σc]
  by_cases hbase : u₀ = CL.rep (Pi.single (chi hm s₀) 1) yp
  · subst hbase
    -- the three ingredients
    have hle := sum_sum_le_card_mul (S := Seed F m) (ι := Sample F m)
      (fun s => s.weight) (fun s => s.weight_nonneg)
      (fun σc s => qmapS hm σc s.questions.1
            = CL.Question.aline (CL.rep (Pi.single (chi hm s₀) 1) yp) s₀ ∧
          qmapS hm σc s.questions.2 = CL.Question.point yp)
      {Sample.axis false (revPoint yp) (Fin.rev (chi hm s₀))}
      (1 / (6 * m * Fintype.card (Point F m)))
      ((Fintype.card F / m) ^ (m - 1) * (Fintype.card F - 1))
      (fun σc s hc => filter_qmapS_axis_subset hm σc _ s₀ yp
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩))
      (fun s hs => by rw [Finset.mem_singleton] at hs; subst hs; exact le_of_eq rfl)
      (fun s hs => card_filter_axis_le hm _ s₀ yp s hs)
    refine hle.trans ?_
    rw [Finset.card_singleton, Nat.cast_one, clGame_μ_eq, cast_card_clSample, card_seed_real]
    -- the seeded test's count, from below
    have hcnt : (Fintype.card (Point F m) : ℝ)
        ≤ ((Finset.univ.filter (fun sm : CL.Sample F m =>
            (sm.question hm sm.tyA, sm.question hm sm.tyB)
              = ((CL.Question.aline (CL.rep (Pi.single (chi hm s₀) 1) yp) s₀
                    : CL.Question F m), CL.Question.point yp))).card : ℝ) := by
      exact_mod_cast card_filter_clAxis_ge hm yp s₀
    -- notation
    set q : ℝ := (Fintype.card F : ℝ) with hqdef
    set P : ℝ := (Fintype.card (Point F m) : ℝ) with hPdef
    set N : ℝ := blk F m with hNdef
    have hq : (0 : ℝ) < q := card_pos_real
    have hq1 : (1 : ℝ) ≤ q := by rw [hqdef]; exact_mod_cast Fintype.card_pos
    have hP : (0 : ℝ) < P := card_point_pos_real
    have hmR : (0 : ℝ) < m := m_pos_real
    have hm1 : (1 : ℝ) ≤ m := one_le_m_real
    have hN : (0 : ℝ) < N := blk_pos hm
    have hmN : (m : ℝ) * N = q := m_mul_blk hm
    have hden : (0 : ℝ) < 9 * (P * (q * P)) := by positivity
    have hA : (0 : ℝ) ≤ N ^ (m - 1) * (q - 1) := by
      refine mul_nonneg (by positivity) (by linarith)
    have hM : ((((Fintype.card F / m) ^ (m - 1) * (Fintype.card F - 1) : ℕ)) : ℝ)
        = N ^ (m - 1) * (q - 1) := by
      rw [hNdef, hqdef]
      push_cast [cast_card_sub_one]
      ring
    have hpow : N ^ m = N ^ (m - 1) * N := by
      rw [← pow_succ]
      congr 1
      have : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)
      omega
    calc (1 : ℝ) * (1 / (6 * m * P) *
            ((((Fintype.card F / m) ^ (m - 1) * (Fintype.card F - 1) : ℕ)) : ℝ))
        = 1 / (6 * m * P) * (N ^ (m - 1) * (q - 1)) := by rw [hM, one_mul]
      _ ≤ (N * (3 * m * (P / (9 * (P * (q * P)))))) * (N ^ (m - 1) * (q - 1)) := by
          refine mul_le_mul_of_nonneg_right ?_ hA
          have hval : N * (3 * m * (P / (9 * (P * (q * P))))) = 1 / (3 * P) := by
            rw [← hmN]
            field_simp
            ring
          rw [hval]
          refine one_div_le_one_div_of_le (by positivity) ?_
          nlinarith
      _ = N ^ m * (q - 1) * (3 * m * (P / (9 * (P * (q * P))))) := by rw [hpow]; ring
      _ ≤ N ^ m * (q - 1) * (3 * m *
            (((Finset.univ.filter (fun sm : CL.Sample F m =>
              (sm.question hm sm.tyA, sm.question hm sm.tyB)
                = ((CL.Question.aline (CL.rep (Pi.single (chi hm s₀) 1) yp) s₀
                      : CL.Question F m), CL.Question.point yp))).card : ℝ)
              / (9 * (P * (q * P))))) := by
          have hfac : (0 : ℝ) ≤ N ^ m * (q - 1) :=
            mul_nonneg (by positivity) (by linarith)
          refine mul_le_mul_of_nonneg_left ?_ hfac
          refine mul_le_mul_of_nonneg_left ?_ (by positivity : (0:ℝ) ≤ 3 * (m:ℝ))
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right hcnt (le_of_lt (inv_pos.mpr hden))
  · -- nothing contributes, and the right-hand side is nonnegative
    have hzero : ∀ σc : Seed F m,
        (∑ s ∈ Finset.univ.filter (fun s : Sample F m =>
          qmapS hm σc s.questions.1 = CL.Question.aline u₀ s₀ ∧
            qmapS hm σc s.questions.2 = CL.Question.point yp), s.weight) = 0 := by
      intro σc
      refine Finset.sum_eq_zero fun s hs => ?_
      obtain ⟨h1, h2⟩ := (Finset.mem_filter.mp hs).2
      exact absurd (base_of_qmapS_axis hm σc h1 h2) hbase
    rw [Finset.sum_congr rfl fun σc (_ : σc ∈ Finset.univ) => hzero σc, Finset.sum_const_zero]
    refine mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by positivity) ?_)
    exact (clGame (d := d) (ldc := ldc) hm).μ_nonneg _ _
end MIPRE.LIDT.Adapter
