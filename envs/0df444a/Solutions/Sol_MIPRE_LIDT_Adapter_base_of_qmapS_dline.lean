-- Prove2me | solution 1 for MIPRE.LIDT.Adapter.base_of_qmapS_dline
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:30:54.563884+00:00
-- url     : https://prove2.me/submissions/7ea36595-3e7b-4c4d-863d-12ea95525452

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Adapter/Weights.lean (solution of MIPRE.LIDT.Adapter.base_of_qmapS_dline);
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
import Theorems.Thm_MIPRE_LIDT_Adapter_forced_of_qmapS_dline
import Theorems.Thm_MIPRE_LIDT_Adapter_rep_eq

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LIDT.Adapter
section
open Finset Submodule Module MIPRE.CL
variable {F : Type*} [Field F] {n : ℕ}
variable [DecidableEq F]
omit [DecidableEq F] in
/-- The base point depends only on the line, not on the point of it that produced it. -/
theorem rep_add_smul (w x : Fin n → F) (t : F) :
    canonLin (span F {w}) (x + t • w) = canonLin (span F {w}) x := by
  have hker : (t • w) ∈ LinearMap.ker (canonLin (span F {w})) := by
    rw [ker_canonLin]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
  rw [map_add, (LinearMap.mem_ker).mp hker, add_zero]
end
end MIPRE.LIDT.Adapter

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
open Finset Submodule Module MIPRE.CL
variable {F : Type*} [Field F] {n : ℕ}
variable [DecidableEq F]
/-- The canonical base point, projected out. -/
theorem through_fst {u z : Fin n → F} (hz : ∃ k, z k ≠ 0) :
    (Line.through u z).1 = u - u (Fin.find (fun k => z k ≠ 0) hz) •
      ((z (Fin.find (fun k => z k ≠ 0) hz))⁻¹ • z) := by
  rw [through_eq hz]
end
end MIPRE.LIDT.Adapter

namespace MIPRE.LIDT.Adapter
section
open Finset Submodule Module MIPRE.CL
variable {F : Type*} [Field F] {n : ℕ}
variable [DecidableEq F]
/-- The point a canonical presentation was built from lies on the line it presents. -/
theorem through_mem {u z : Fin n → F} (hz : ∃ k, z k ≠ 0) :
    u = (Line.through u z).1
      + (u (Fin.find (fun k => z k ≠ 0) hz)) • (Line.through u z).2 := by
  rw [through_fst hz, through_snd hz, sub_add_cancel]
end
end MIPRE.LIDT.Adapter

namespace MIPRE.LIDT.Adapter
section
open Finset Submodule Module MIPRE.CL MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]
omit [Fintype F] in
/-- On a nondegenerate line `diagIdx` is the pivot. -/
theorem diagIdx_eq_find {ℓ : Line F m} (h : ∃ j, (revPoint ℓ.2) j ≠ 0) :
    diagIdx ℓ = Fin.find (fun j => (revPoint ℓ.2) j ≠ 0) h := dif_pos h
end
end MIPRE.LIDT.Adapter

namespace MIPRE.LIDT.Adapter
section
open Finset Submodule Module MIPRE.CL MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]
omit [Fintype F] [NeZero m] in
/-- **The two base points differ by the shift times the direction.** -/
theorem rep_rev_eq (ℓ : Line F m) :
    canonLin (span F {revPoint ℓ.2}) (revPoint ℓ.1)
      = revPoint ℓ.1 - shiftOf ℓ • revPoint ℓ.2 := by
  by_cases h : ∃ j, (revPoint ℓ.2) j ≠ 0
  · rw [rep_eq h, shiftOf, dif_pos h]
  · have h0 : (revPoint ℓ.2 : Fin m → F) = 0 := by
      funext j
      exact not_not.mp (fun hc => h ⟨j, hc⟩)
    rw [h0, Set.singleton_zero, Submodule.span_zero, canonLin_bot, shiftOf, dif_neg h,
      zero_smul, sub_zero]
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
omit [Fintype F] [NeZero m] in
/-- **Rescaling a reversed direction does not move the adapter's base point off the seeded
test's.** This is the diagonal analogue of `revPoint_through_single_eq_rep`: the seeded question
carries `c · ρℓ₂` as its direction and `rep` of that is the adapter's `ρℓ₁ - sh · ρℓ₂`. -/
theorem adapter_base_eq_rep {ℓ : Line F m}
    {x : Point F m} (hx : ∃ t : F, (revPoint x : Point F m) = ℓ.1 + t • ℓ.2)
    {c : F} (hc : c ≠ 0) :
    revPoint ℓ.1 - shiftOf ℓ • revPoint ℓ.2 = CL.rep (c • revPoint ℓ.2) x := by
  classical
  obtain ⟨t, ht⟩ := hx
  have hx' : (x : Point F m) = revPoint ℓ.1 + t • revPoint ℓ.2 := by
    have h := congrArg (fun z : Point F m => (revPoint z : Point F m)) ht
    simpa using h
  rw [← rep_rev_eq]
  show MIPRE.CL.canonLin (Submodule.span F {(revPoint ℓ.2 : Point F m)}) (revPoint ℓ.1)
      = MIPRE.CL.canonLin (Submodule.span F {(c • revPoint ℓ.2 : Point F m)}) x
  rw [Submodule.span_singleton_smul_eq (IsUnit.mk0 c hc), hx', rep_add_smul]
end
end MIPRE.LIDT.Adapter

namespace MIPRE.LIDT.Adapter
section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
omit [Fintype F] in
/-- **A seeded direction vanishes below its own `χ`-index**, which is what puts the question in
the seeded test's support. -/
theorem smul_revPoint_eq_zero_below {ℓ : Line F m} (hℓ : ∃ k, ℓ.2 k ≠ 0) (c : F)
    {k : Fin m} (hk : (k : ℕ) < ((diagIdx ℓ : Fin m) : ℕ)) :
    (c • revPoint ℓ.2 : Point F m) k = 0 := by
  classical
  have hex : ∃ j, (revPoint ℓ.2 : Point F m) j ≠ 0 := by
    obtain ⟨j, hj⟩ := hℓ
    exact ⟨Fin.rev j, by rwa [revPoint_apply, Fin.rev_rev]⟩
  rw [diagIdx_eq_find hex] at hk
  have hz : (revPoint ℓ.2 : Point F m) k = 0 := not_not.mp (Fin.find_min hex hk)
  simp only [Pi.smul_apply, hz, smul_zero]
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
theorem _root_.solution (hm : m ∣ Fintype.card F) (σc : Seed F m)
    {u₀ : Point F m} {s₀ : F} {w yp : Point F m} {s : Sample F m} (hw : w ≠ 0)
    (h1 : qmapS hm σc s.questions.1 = CL.Question.dline u₀ s₀ w)
    (h2 : qmapS hm σc s.questions.2 = CL.Question.point yp) :
    u₀ = CL.rep w yp
      ∧ chi hm s₀ = diagIdx (Line.through (revPoint yp) (revPoint w) : Line F m)
      ∧ ∀ k : Fin m, (k : ℕ) < ((chi hm s₀ : Fin m) : ℕ) → w k = 0 := by
  classical
  have hwnz : ∃ k, (revPoint w : Point F m) k ≠ 0 := exists_ne_zero (revPoint_ne_zero hw)
  have hq := forced_of_qmapS_dline hm σc hw h1 h2
  obtain ⟨hb, hseed, hscale⟩ := data_of_questions_diagLine hm σc hq h1
  have hchi : chi hm s₀ = diagIdx (Line.through (revPoint yp) (revPoint w) : Line F m) := by
    rw [← hseed, chi_seedOf]
  refine ⟨?_, hchi, ?_⟩
  case refine_2 =>
    intro k hk
    rw [hchi] at hk
    have hz := smul_revPoint_eq_zero_below (exists_dir_through hwnz) (σc.2 : F) hk
    rwa [hscale] at hz
  rw [← hb]
  have hgen := adapter_base_eq_rep (ℓ := (Line.through (revPoint yp) (revPoint w) : Line F m))
    (x := yp) ⟨_, through_mem hwnz⟩ σc.2.2
  rw [hscale] at hgen
  exact hgen
end MIPRE.LIDT.Adapter
