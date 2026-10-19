-- Prove2me | solution 1 for MIPRE.LIDT.Adapter.pushforward_diag_zero
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:30:53.862005+00:00
-- url     : https://prove2.me/submissions/b9299c4e-8eeb-4f2a-aed9-7ef726d3e7c8

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Adapter/Weights.lean (solution of MIPRE.LIDT.Adapter.pushforward_diag_zero);
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
import Theorems.Thm_MIPRE_LIDT_Adapter_canonLin_bot
import Theorems.Thm_MIPRE_LIDT_Adapter_card_filter_clDiag_ge
import Theorems.Thm_MIPRE_LIDT_Adapter_card_filter_seed_le
import Theorems.Thm_MIPRE_LIDT_Adapter_eq_diag_zero_of_qmapS
import Theorems.Thm_MIPRE_LIDT_Adapter_sum_fibre_mu_eq_sum_samples
import Theorems.Thm_MIPRE_LIDT_Adapter_sum_sum_le_card_mul
import Theorems.Thm_MIPRE_LIDT_CL_card_div_pos

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LIDT.Adapter
section
open Finset Submodule Module MIPRE.CL MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]
omit [Fintype F] in
/-- The fallback, named. -/
theorem diagIdx_of_dir_eq_zero {ℓ : Line F m} (h : (revPoint ℓ.2 : Point F m) = 0) :
    diagIdx ℓ = Fin.rev idx0 := by
  refine dif_neg fun hc => ?_
  obtain ⟨j, hj⟩ := hc
  exact hj (by rw [h]; rfl)
end
end MIPRE.LIDT.Adapter

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
omit [Field F] [DecidableEq F] [NeZero m] in
theorem card_point_eq : Fintype.card (Point F m) = Fintype.card F ^ m := by
  simp
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

namespace MIPRE.LIDT.Adapter
section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
/-- The adapter's image of a singleton diagonal line. -/
theorem qmapS_diag_zero (hm : m ∣ Fintype.card F) (σc : Seed F m) (u : Point F m) (j : Fin m) :
    qmapS hm σc (Question.diagLine
        (Line.through u (Sample.extend (0 : Fin ((j : ℕ) + 1) → F))))
      = CL.Question.dline (revPoint u) (seedOf hm (Fin.rev idx0) (σc.1 (Fin.rev idx0))) 0 := by
  rw [extend_zero, through_zero, qmapS_diag,
    diagIdx_of_dir_eq_zero (ℓ := ((u, 0) : Line F m)) (by simp)]
  simp
end
end MIPRE.LIDT.Adapter

namespace MIPRE.LIDT.Adapter
section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
/-- **What a contributing sample forces, for a singleton `DLine` question.** -/
theorem base_of_qmapS_dline_zero (hm : m ∣ Fintype.card F) (σc : Seed F m)
    {u₀ : Point F m} {s₀ : F} {yp : Point F m} {s : Sample F m}
    (h1 : qmapS hm σc s.questions.1 = CL.Question.dline u₀ s₀ 0)
    (h2 : qmapS hm σc s.questions.2 = CL.Question.point yp) :
    u₀ = yp ∧ seedOf hm (Fin.rev idx0) (σc.1 (Fin.rev idx0)) = s₀ := by
  classical
  obtain ⟨j, rfl⟩ := eq_diag_zero_of_qmapS hm σc h1 h2
  have h1' : (CL.Question.dline (revPoint (revPoint yp))
      (seedOf hm (Fin.rev idx0) (σc.1 (Fin.rev idx0))) 0 : CL.Question F m)
      = CL.Question.dline u₀ s₀ 0 := by
    rw [← qmapS_diag_zero hm σc (revPoint yp) j]
    exact h1
  rw [revPoint_revPoint] at h1'
  exact ⟨(CL.Question.dline.inj h1').1.symm, (CL.Question.dline.inj h1').2.1⟩
end
end MIPRE.LIDT.Adapter

namespace MIPRE.LIDT.Adapter
section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
omit [Fintype F] [DecidableEq F] [NeZero m] in
/-- `rep` of the zero direction is the identity: a singleton line is its own base point. -/
theorem rep_zero (u : Point F m) : (CL.rep (0 : Point F m) u : Point F m) = u := by
  show MIPRE.CL.canonLin (Submodule.span F {(0 : Point F m)}) u = u
  rw [Set.singleton_zero, Submodule.span_zero, canonLin_bot]
end
end MIPRE.LIDT.Adapter

namespace MIPRE.LIDT.Adapter
section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
omit [Field F] [Fintype F] [DecidableEq F] in
theorem val_rev_idx0 : ((Fin.rev (idx0 : Fin m) : Fin m) : ℕ) = m - 1 := by
  rw [Fin.val_rev]
  rfl
end
end MIPRE.LIDT.Adapter

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LIDT.Adapter
open Finset MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
theorem _root_.solution (hm : m ∣ Fintype.card F) (u₀ : Point F m) (s₀ : F) (yp : Point F m) :
    (∑ σc : Seed F m,
        ∑ x' ∈ Finset.univ.filter (fun x' => qmapS hm σc x' = CL.Question.dline u₀ s₀ 0),
        ∑ y' ∈ Finset.univ.filter (fun y' => qmapS hm σc y' = CL.Question.point yp),
          (lidtGame F m d).μ x' y')
      ≤ (Fintype.card (Seed F m) : ℝ) *
          (3 * m * (clGame (d := d) (ldc := ldc) hm).μ
            (CL.Question.dline u₀ s₀ 0) (CL.Question.point yp)) := by
  classical
  by_cases hb : u₀ = yp ∧ chi hm s₀ = Fin.rev idx0
  · obtain ⟨rfl, hchi⟩ := hb
    have hsamples : ∀ σc : Seed F m,
        (∑ x' ∈ Finset.univ.filter (fun x' => qmapS hm σc x' = CL.Question.dline u₀ s₀ 0),
          ∑ y' ∈ Finset.univ.filter (fun y' => qmapS hm σc y' = CL.Question.point u₀),
            (lidtGame F m d).μ x' y')
        = ∑ s ∈ Finset.univ.filter (fun s : Sample F m =>
            qmapS hm σc s.questions.1 = CL.Question.dline u₀ s₀ 0 ∧
              qmapS hm σc s.questions.2 = CL.Question.point u₀), s.weight := fun σc =>
      sum_fibre_mu_eq_sum_samples (d := d) (qmapS hm σc) (qmapS hm σc) _ _
    rw [Finset.sum_congr rfl fun σc (_ : σc ∈ Finset.univ) => hsamples σc]
    have hq : (0 : ℝ) < Fintype.card F := card_pos_real
    have hq1 : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos
    have hP : (0 : ℝ) < Fintype.card (Point F m) := card_point_pos_real
    have hmR : (0 : ℝ) < m := m_pos_real
    have hm1 : (1 : ℝ) ≤ m := one_le_m_real
    have hle := sum_sum_le_card_mul (S := Seed F m) (ι := Sample F m)
      (fun s => s.weight) (fun s => s.weight_nonneg)
      (fun σc s => qmapS hm σc s.questions.1 = CL.Question.dline u₀ s₀ 0 ∧
        qmapS hm σc s.questions.2 = CL.Question.point u₀)
      (Finset.univ.image (fun j : Fin m =>
        Sample.diag false (revPoint u₀) j (0 : Fin ((j : ℕ) + 1) → F)))
      (1 / (6 * m * Fintype.card (Point F m) * (Fintype.card F : ℝ)))
      ((Fintype.card F / m) ^ (m - 1) * (Fintype.card F - 1))
      (fun σc s hc => by
        obtain ⟨j, rfl⟩ := eq_diag_zero_of_qmapS hm σc hc.1 hc.2
        exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
      (fun s hs => by
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hs
        show 1 / (6 * m * Fintype.card (Point F m) *
            (Fintype.card F : ℝ) ^ ((j : ℕ) + 1)) ≤ _
        refine one_div_le_one_div_of_le (by positivity) ?_
        have hpow : (Fintype.card F : ℝ) ^ 1 ≤ (Fintype.card F : ℝ) ^ ((j : ℕ) + 1) :=
          pow_le_pow_right₀ hq1 (by omega)
        rw [pow_one] at hpow
        exact mul_le_mul_of_nonneg_left hpow (by positivity))
      (fun s hs => by
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hs
        exact card_filter_seed_le hm (Fin.rev idx0) s₀ _
          (fun σc hc => (base_of_qmapS_dline_zero hm σc hc.1 hc.2).2))
    refine hle.trans ?_
    -- the seeded count, from below
    have hcnt : ((Fintype.card F : ℝ)) ^ (m - 1)
        ≤ ((Finset.univ.filter (fun sm : CL.Sample F m =>
            (sm.question hm sm.tyA, sm.question hm sm.tyB)
              = ((CL.Question.dline u₀ s₀ 0 : CL.Question F m),
                  CL.Question.point u₀))).card : ℝ) := by
      have h := card_filter_clDiag_ge hm u₀ s₀ 0 (fun k _ => rfl)
      rw [rep_zero, hchi, val_rev_idx0] at h
      exact_mod_cast h
    have hTcard : (Finset.univ.image (fun j : Fin m =>
        Sample.diag false (revPoint u₀) j (0 : Fin ((j : ℕ) + 1) → F))).card ≤ m := by
      refine (Finset.card_image_le).trans ?_
      rw [Finset.card_univ, Fintype.card_fin]
    rw [clGame_μ_eq, cast_card_clSample, card_seed_real]
    set q : ℝ := (Fintype.card F : ℝ) with hqdef
    set P : ℝ := (Fintype.card (Point F m) : ℝ) with hPdef
    set N : ℝ := blk F m with hNdef
    set cnt : ℝ := ((Finset.univ.filter (fun sm : CL.Sample F m =>
      (sm.question hm sm.tyA, sm.question hm sm.tyB)
        = ((CL.Question.dline u₀ s₀ 0 : CL.Question F m),
            CL.Question.point u₀))).card : ℝ) with hcntdef
    have hN : (0 : ℝ) < N := blk_pos hm
    have hmN : (m : ℝ) * N = q := m_mul_blk hm
    have hPq : P = q ^ m := by rw [hPdef, hqdef, card_point_eq]; push_cast; ring
    have hmpos : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)
    have hY : P = q ^ (m - 1) * q := by
      rw [hPq, ← pow_succ]
      congr 1
      omega
    set Y : ℝ := q ^ (m - 1) with hYdef
    set Z : ℝ := N ^ (m - 1) with hZdef
    have hYpos : (0 : ℝ) < Y := by rw [hYdef]; positivity
    have hZpos : (0 : ℝ) < Z := by rw [hZdef]; positivity
    have hNm : N ^ m = Z * N := by
      rw [hZdef, ← pow_succ]
      congr 1
      omega
    have hMcast : ((((Fintype.card F / m) ^ (m - 1) * (Fintype.card F - 1) : ℕ)) : ℝ)
        = Z * (q - 1) := by
      rw [hZdef, hNdef, hqdef]
      push_cast [cast_card_sub_one]
      ring
    have hAnn : (0 : ℝ) ≤ Z * (q - 1) := mul_nonneg hZpos.le (by linarith)
    calc ((Finset.univ.image (fun j : Fin m =>
              Sample.diag false (revPoint u₀) j (0 : Fin ((j : ℕ) + 1) → F))).card : ℝ)
            * (1 / (6 * m * P * q) *
              ((((Fintype.card F / m) ^ (m - 1) * (Fintype.card F - 1) : ℕ)) : ℝ))
        ≤ (m : ℝ) * (1 / (6 * m * P * q) * (Z * (q - 1))) := by
          rw [hMcast]
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact_mod_cast hTcard
      _ = ((m : ℝ) * (1 / (6 * m * P * q))) * (Z * (q - 1)) := by ring
      _ ≤ (N * (3 * m * (Y / (9 * (P * (q * P)))))) * (Z * (q - 1)) := by
          refine mul_le_mul_of_nonneg_right ?_ hAnn
          have hL : (m : ℝ) * (1 / (6 * m * P * q)) = 1 / (6 * (Y * q ^ 2)) := by
            rw [hY]; field_simp
          have hR : N * (3 * m * (Y / (9 * (P * (q * P))))) = 1 / (3 * (Y * q ^ 2)) := by
            rw [hY, ← hmN]; field_simp; ring
          rw [hL, hR]
          have hW : (0 : ℝ) < Y * q ^ 2 := mul_pos hYpos (pow_pos hq 2)
          exact one_div_le_one_div_of_le (by linarith) (by linarith)
      _ = N ^ m * (q - 1) * (3 * m * (Y / (9 * (P * (q * P))))) := by rw [hNm]; ring
      _ ≤ N ^ m * (q - 1) * (3 * m * (cnt / (9 * (P * (q * P))))) := by
          refine mul_le_mul_of_nonneg_left ?_
            (mul_nonneg (by positivity) (by linarith : (0:ℝ) ≤ q - 1))
          refine mul_le_mul_of_nonneg_left ?_ (by positivity : (0:ℝ) ≤ 3 * (m:ℝ))
          rw [div_eq_mul_inv, div_eq_mul_inv]
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [hYdef]
          exact hcnt
  · -- nothing contributes
    have hsamples : ∀ σc : Seed F m,
        (∑ x' ∈ Finset.univ.filter (fun x' => qmapS hm σc x' = CL.Question.dline u₀ s₀ 0),
          ∑ y' ∈ Finset.univ.filter (fun y' => qmapS hm σc y' = CL.Question.point yp),
            (lidtGame F m d).μ x' y')
        = ∑ s ∈ Finset.univ.filter (fun s : Sample F m =>
            qmapS hm σc s.questions.1 = CL.Question.dline u₀ s₀ 0 ∧
              qmapS hm σc s.questions.2 = CL.Question.point yp), s.weight := fun σc =>
      sum_fibre_mu_eq_sum_samples (d := d) (qmapS hm σc) (qmapS hm σc) _ _
    rw [Finset.sum_congr rfl fun σc (_ : σc ∈ Finset.univ) => hsamples σc]
    have hzero : ∀ σc : Seed F m,
        (∑ s ∈ Finset.univ.filter (fun s : Sample F m =>
          qmapS hm σc s.questions.1 = CL.Question.dline u₀ s₀ 0 ∧
            qmapS hm σc s.questions.2 = CL.Question.point yp), s.weight) = 0 := by
      intro σc
      refine Finset.sum_eq_zero fun s hs => ?_
      obtain ⟨h1, h2⟩ := (Finset.mem_filter.mp hs).2
      obtain ⟨hu, hseed⟩ := base_of_qmapS_dline_zero hm σc h1 h2
      exact absurd ⟨hu, by rw [← hseed, chi_seedOf]⟩ hb
    rw [Finset.sum_congr rfl fun σc (_ : σc ∈ Finset.univ) => hzero σc, Finset.sum_const_zero]
    refine mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by positivity) ?_)
    exact (clGame (d := d) (ldc := ldc) hm).μ_nonneg _ _
end MIPRE.LIDT.Adapter
