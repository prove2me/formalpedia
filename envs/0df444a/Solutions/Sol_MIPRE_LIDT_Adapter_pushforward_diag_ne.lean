-- Prove2me | solution 1 for MIPRE.LIDT.Adapter.pushforward_diag_ne
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:32:16.652987+00:00
-- url     : https://prove2.me/submissions/12c5eae2-a02b-461c-8388-d1512b070620

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Adapter/Weights.lean (solution of MIPRE.LIDT.Adapter.pushforward_diag_ne);
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
import Theorems.Thm_MIPRE_LIDT_Adapter_base_of_qmapS_dline
import Theorems.Thm_MIPRE_LIDT_Adapter_card_filter_clDiag_ge
import Theorems.Thm_MIPRE_LIDT_Adapter_card_filter_diag_le
import Theorems.Thm_MIPRE_LIDT_Adapter_card_filter_pinned_le
import Theorems.Thm_MIPRE_LIDT_Adapter_forced_of_qmapS_dline
import Theorems.Thm_MIPRE_LIDT_Adapter_sum_fibre_mu_eq_sum_samples
import Theorems.Thm_MIPRE_LIDT_Adapter_sum_sum_le_card_mul
import Theorems.Thm_MIPRE_LIDT_Adapter_weight_le_of_questions_diag
import Theorems.Thm_MIPRE_LIDT_CL_card_div_pos

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LIDT.Adapter
section
open Finset Submodule Module MIPRE.CL
variable {F : Type*} [Field F] {n : ℕ}
variable [DecidableEq F]
/-- The canonical presentation, unfolded. -/
theorem through_eq {u z : Fin n → F} (hz : ∃ k, z k ≠ 0) :
    Line.through u z
      = (u - u (Fin.find (fun k => z k ≠ 0) hz) •
            ((z (Fin.find (fun k => z k ≠ 0) hz))⁻¹ • z),
          (z (Fin.find (fun k => z k ≠ 0) hz))⁻¹ • z) := by
  rw [Line.through, dif_pos hz]
end
end MIPRE.LIDT.Adapter

namespace MIPRE.LIDT.Adapter
section
open Finset Submodule Module MIPRE.CL
variable {F : Type*} [Field F] {n : ℕ}
variable [DecidableEq F]
/-- The canonical direction, projected out. -/
theorem through_snd {u z : Fin n → F} (hz : ∃ k, z k ≠ 0) :
    (Line.through u z).2 = (z (Fin.find (fun k => z k ≠ 0) hz))⁻¹ • z := by
  rw [through_eq hz]
end
end MIPRE.LIDT.Adapter

namespace MIPRE.LIDT.Adapter
section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ} [NeZero m]
omit [Field F] [DecidableEq F] [NeZero m] in
/-- The `q/m` seeds of a fibre are distinct, so averaging a choice over `r` averages over the
whole fibre. -/
theorem seedOf_injective (hm : m ∣ Fintype.card F) (i : Fin m) :
    Function.Injective (seedOf hm i) := by
  intro r r' h
  have h' := congrArg (fun s => ((Fintype.equivFin F) s : ℕ)) h
  simp only [equivFin_seedOf] at h'
  exact Fin.ext (by omega)
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
omit [Fintype F] [NeZero m] in
theorem exists_ne_zero {x : Point F m} (h : x ≠ 0) : ∃ k, x k ≠ 0 := by
  by_contra hall
  exact h (funext fun k => not_not.mp fun hc => hall ⟨k, hc⟩)
end
end MIPRE.LIDT.Adapter

namespace MIPRE.LIDT.Adapter
section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
omit [Fintype F] [DecidableEq F] [NeZero m] in
theorem revPoint_ne_zero {x : Point F m} (h : x ≠ 0) : (revPoint x : Point F m) ≠ 0 := by
  intro hc
  exact h (by rw [← revPoint_revPoint x, hc, revPoint_zero])
end
end MIPRE.LIDT.Adapter

namespace MIPRE.LIDT.Adapter
section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
omit [Fintype F] [DecidableEq F] [NeZero m] in
theorem ne_zero_of_exists {x : Point F m} (h : ∃ k, x k ≠ 0) : x ≠ 0 := by
  obtain ⟨k, hk⟩ := h
  intro hc
  exact hk (congrFun hc k)
end
end MIPRE.LIDT.Adapter

namespace MIPRE.LIDT.Adapter
section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
omit [Fintype F] [NeZero m] in
/-- A canonical presentation has a nonzero direction as soon as its input direction is
nonzero. -/
theorem exists_dir_through {u z : Point F m} (hz : ∃ k, z k ≠ 0) :
    ∃ k, (Line.through u z).2 k ≠ 0 := by
  classical
  refine ⟨Fin.find (fun k => z k ≠ 0) hz, ?_⟩
  rw [through_snd hz]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [inv_mul_cancel₀ (Fin.find_spec hz)]
  exact one_ne_zero
end
end MIPRE.LIDT.Adapter

namespace MIPRE.LIDT.Adapter
section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
/-- **The data a contributing sample carries**, read off the question. -/
theorem data_of_questions_diagLine (hm : m ∣ Fintype.card F) (σc : Seed F m)
    {u₀ : Point F m} {s₀ : F} {w yp : Point F m} {s : Sample F m} {ℓ : Line F m}
    (hq : s.questions = ((Question.diagLine ℓ : Question F m), Question.point (revPoint yp)))
    (h1 : qmapS hm σc s.questions.1 = CL.Question.dline u₀ s₀ w) :
    revPoint ℓ.1 - shiftOf ℓ • revPoint ℓ.2 = u₀ ∧
      seedOf hm (diagIdx ℓ) (σc.1 (diagIdx ℓ)) = s₀ ∧ (σc.2 : F) • revPoint ℓ.2 = w := by
  have hq1 : s.questions.1 = (Question.diagLine ℓ : Question F m) := congrArg Prod.fst hq
  rw [hq1, qmapS_diag] at h1
  exact CL.Question.dline.inj h1
end
end MIPRE.LIDT.Adapter

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LIDT.Adapter
open Finset MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
theorem _root_.solution (hm : m ∣ Fintype.card F) (u₀ : Point F m) (s₀ : F) {w : Point F m}
    (hw : w ≠ 0) (yp : Point F m) :
    (∑ σc : Seed F m,
        ∑ x' ∈ Finset.univ.filter (fun x' => qmapS hm σc x' = CL.Question.dline u₀ s₀ w),
        ∑ y' ∈ Finset.univ.filter (fun y' => qmapS hm σc y' = CL.Question.point yp),
          (lidtGame F m d).μ x' y')
      ≤ (Fintype.card (Seed F m) : ℝ) *
          (3 * m * (clGame (d := d) (ldc := ldc) hm).μ
            (CL.Question.dline u₀ s₀ w) (CL.Question.point yp)) := by
  classical
  have hwnz : ∃ k, (revPoint w : Point F m) k ≠ 0 := exists_ne_zero (revPoint_ne_zero hw)
  have hdir : ∃ k, (Line.through (revPoint yp) (revPoint w) : Line F m).2 k ≠ 0 :=
    exists_dir_through hwnz
  have hsamples : ∀ σc : Seed F m,
      (∑ x' ∈ Finset.univ.filter (fun x' => qmapS hm σc x' = CL.Question.dline u₀ s₀ w),
        ∑ y' ∈ Finset.univ.filter (fun y' => qmapS hm σc y' = CL.Question.point yp),
          (lidtGame F m d).μ x' y')
      = ∑ s ∈ Finset.univ.filter (fun s : Sample F m =>
          qmapS hm σc s.questions.1 = CL.Question.dline u₀ s₀ w ∧
            qmapS hm σc s.questions.2 = CL.Question.point yp), s.weight := fun σc =>
    sum_fibre_mu_eq_sum_samples (d := d) (qmapS hm σc) (qmapS hm σc) _ _
  rw [Finset.sum_congr rfl fun σc (_ : σc ∈ Finset.univ) => hsamples σc]
  by_cases hb : u₀ = CL.rep w yp
      ∧ chi hm s₀ = diagIdx (Line.through (revPoint yp) (revPoint w) : Line F m)
      ∧ ∀ k : Fin m, (k : ℕ) < ((chi hm s₀ : Fin m) : ℕ) → w k = 0
  · obtain ⟨hbase, hchi, hvan⟩ := hb
    have hq : (0 : ℝ) < Fintype.card F := card_pos_real
    have hq1 : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos
    have hq2N : 2 ≤ Fintype.card F := Fintype.one_lt_card
    have hP : (0 : ℝ) < Fintype.card (Point F m) := card_point_pos_real
    have hmR : (0 : ℝ) < m := m_pos_real
    have hm1 : (1 : ℝ) ≤ m := one_le_m_real
    have hle := sum_sum_le_card_mul (S := Seed F m) (ι := Sample F m)
      (fun s => s.weight) (fun s => s.weight_nonneg)
      (fun σc s => qmapS hm σc s.questions.1 = CL.Question.dline u₀ s₀ w ∧
        qmapS hm σc s.questions.2 = CL.Question.point yp)
      (Finset.univ.filter (fun s : Sample F m => s.questions
        = ((Question.diagLine (Line.through (revPoint yp) (revPoint w)) : Question F m),
            Question.point (revPoint yp))))
      (1 / (6 * m * Fintype.card (Point F m) * (Fintype.card F : ℝ) ^
        ((Fin.rev (diagIdx (Line.through (revPoint yp) (revPoint w) : Line F m)) : ℕ) + 1)))
      ((Fintype.card F / m) ^ (m - 1))
      (fun σc s hc => Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, forced_of_qmapS_dline hm σc hw hc.1 hc.2⟩)
      (fun s hs => weight_le_of_questions_diag hdir (Finset.mem_filter.mp hs).2)
      (fun s hs => by
        refine card_filter_pinned_le
          (diagIdx (Line.through (revPoint yp) (revPoint w) : Line F m)) _ ?_
        intro a ha b hb'
        have hqs := (Finset.mem_filter.mp hs).2
        obtain ⟨_, hsa, hca⟩ :=
          data_of_questions_diagLine hm a hqs (Finset.mem_filter.mp ha).2.1
        obtain ⟨_, hsb, hcb⟩ :=
          data_of_questions_diagLine hm b hqs (Finset.mem_filter.mp hb').2.1
        refine ⟨seedOf_injective hm _ (hsa.trans hsb.symm), ?_⟩
        have hX : (revPoint (Line.through (revPoint yp) (revPoint w) : Line F m).2
            : Point F m) ≠ 0 := revPoint_ne_zero (ne_zero_of_exists hdir)
        have hsub : (((a.2 : F) - (b.2 : F)) •
            (revPoint (Line.through (revPoint yp) (revPoint w) : Line F m).2 : Point F m)) = 0 := by
          rw [sub_smul, hca, hcb, sub_self]
        rcases smul_eq_zero.mp hsub with h | h
        · exact sub_eq_zero.mp h
        · exact absurd h hX)
    refine hle.trans ?_
    -- the seeded count, from below
    have hcnt : ((Fintype.card F : ℝ))
        ^ ((diagIdx (Line.through (revPoint yp) (revPoint w) : Line F m) : Fin m) : ℕ)
        ≤ ((Finset.univ.filter (fun sm : CL.Sample F m =>
            (sm.question hm sm.tyA, sm.question hm sm.tyB)
              = ((CL.Question.dline u₀ s₀ w : CL.Question F m),
                  CL.Question.point yp))).card : ℝ) := by
      have h := card_filter_clDiag_ge hm yp s₀ w hvan
      rw [← hbase, hchi] at h
      exact_mod_cast h
    have hTcard : (Finset.univ.filter (fun s : Sample F m => s.questions
        = ((Question.diagLine (Line.through (revPoint yp) (revPoint w)) : Question F m),
            Question.point (revPoint yp)))).card ≤ m * Fintype.card F :=
      card_filter_diag_le hdir (revPoint yp)
    rw [clGame_μ_eq, cast_card_clSample, card_seed_real]
    set q : ℝ := (Fintype.card F : ℝ) with hqdef
    set P : ℝ := (Fintype.card (Point F m) : ℝ) with hPdef
    set N : ℝ := blk F m with hNdef
    set cnt : ℝ := ((Finset.univ.filter (fun sm : CL.Sample F m =>
      (sm.question hm sm.tyA, sm.question hm sm.tyB)
        = ((CL.Question.dline u₀ s₀ w : CL.Question F m),
            CL.Question.point yp))).card : ℝ) with hcntdef
    have hq2 : (2 : ℝ) ≤ q := by rw [hqdef]; exact_mod_cast hq2N
    have hN : (0 : ℝ) < N := blk_pos hm
    have hmN : (m : ℝ) * N = q := m_mul_blk hm
    have hPq : P = q ^ m := by rw [hPdef, hqdef, card_point_eq]; push_cast; ring
    set U : ℝ := q ^ ((Fin.rev (diagIdx (Line.through (revPoint yp) (revPoint w)
      : Line F m)) : ℕ) + 1) with hUdef
    set V : ℝ := q ^ ((diagIdx (Line.through (revPoint yp) (revPoint w)
      : Line F m) : Fin m) : ℕ) with hVdef
    set Z : ℝ := N ^ (m - 1) with hZdef
    have hUpos : (0 : ℝ) < U := by rw [hUdef]; exact pow_pos hq _
    have hVpos : (0 : ℝ) < V := by rw [hVdef]; exact pow_pos hq _
    have hZpos : (0 : ℝ) < Z := by rw [hZdef]; exact pow_pos hN _
    have hmpos : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)
    have hUV : U * V = P := by
      rw [hUdef, hVdef, ← pow_add, hPq]
      congr 1
      have h1 : ((Fin.rev (diagIdx (Line.through (revPoint yp) (revPoint w) : Line F m))
          : Fin m) : ℕ) = m - (((diagIdx (Line.through (revPoint yp) (revPoint w)
            : Line F m) : Fin m) : ℕ) + 1) := Fin.val_rev _
      have h2 : (((diagIdx (Line.through (revPoint yp) (revPoint w) : Line F m))
          : Fin m) : ℕ) < m := (diagIdx _).isLt
      omega
    have hNm : N ^ m = Z * N := by
      rw [hZdef, ← pow_succ]
      congr 1
      omega
    have hMcast : ((((Fintype.card F / m) ^ (m - 1) : ℕ)) : ℝ) = Z := by
      rw [hZdef, hNdef]
      push_cast
      ring
    calc ((Finset.univ.filter (fun s : Sample F m => s.questions
              = ((Question.diagLine (Line.through (revPoint yp) (revPoint w)) : Question F m),
                  Question.point (revPoint yp)))).card : ℝ)
            * (1 / (6 * m * P * U) * ((((Fintype.card F / m) ^ (m - 1) : ℕ)) : ℝ))
        ≤ ((m : ℝ) * q) * (1 / (6 * m * P * U) * Z) := by
          rw [hMcast]
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have h : ((m * Fintype.card F : ℕ) : ℝ) = (m : ℝ) * q := by
            rw [hqdef]; push_cast; ring
          rw [← h]
          exact_mod_cast hTcard
      _ = (((m : ℝ) * q) * (1 / (6 * m * P * U))) * Z := by ring
      _ ≤ (N * (q - 1) * (3 * m * (V / (9 * (P * (q * P)))))) * Z := by
          refine mul_le_mul_of_nonneg_right ?_ hZpos.le
          have hL : ((m : ℝ) * q) * (1 / (6 * m * P * U)) = q / (6 * P * U) := by
            field_simp
          have hR : N * (q - 1) * (3 * m * (V / (9 * (P * (q * P)))))
              = ((q - 1) * V) / (3 * P * P) := by
            rw [← hmN]; field_simp; ring
          rw [hL, hR, div_le_div_iff₀ (by positivity) (by positivity)]
          have hkey : (q - 1) * V * (6 * P * U) = 6 * P * P * (q - 1) := by
            linear_combination (6 * P * (q - 1)) * hUV
          rw [hkey]
          nlinarith [mul_pos hP hP, hq2]
      _ = N ^ m * (q - 1) * (3 * m * (V / (9 * (P * (q * P))))) := by rw [hNm]; ring
      _ ≤ N ^ m * (q - 1) * (3 * m * (cnt / (9 * (P * (q * P))))) := by
          refine mul_le_mul_of_nonneg_left ?_
            (mul_nonneg (by positivity) (by linarith : (0:ℝ) ≤ q - 1))
          refine mul_le_mul_of_nonneg_left ?_ (by positivity : (0:ℝ) ≤ 3 * (m:ℝ))
          rw [div_eq_mul_inv, div_eq_mul_inv]
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [hVdef]
          exact hcnt
  · have hzero : ∀ σc : Seed F m,
        (∑ s ∈ Finset.univ.filter (fun s : Sample F m =>
          qmapS hm σc s.questions.1 = CL.Question.dline u₀ s₀ w ∧
            qmapS hm σc s.questions.2 = CL.Question.point yp), s.weight) = 0 := by
      intro σc
      refine Finset.sum_eq_zero fun s hs => ?_
      obtain ⟨h1, h2⟩ := (Finset.mem_filter.mp hs).2
      exact absurd (base_of_qmapS_dline hm σc hw h1 h2) hb
    rw [Finset.sum_congr rfl fun σc (_ : σc ∈ Finset.univ) => hzero σc, Finset.sum_const_zero]
    refine mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by positivity) ?_)
    exact (clGame (d := d) (ldc := ldc) hm).μ_nonneg _ _
end MIPRE.LIDT.Adapter
