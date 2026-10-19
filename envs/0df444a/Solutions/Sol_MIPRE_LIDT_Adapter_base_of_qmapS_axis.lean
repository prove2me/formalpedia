-- Prove2me | solution 1 for MIPRE.LIDT.Adapter.base_of_qmapS_axis
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:29:38.629464+00:00
-- url     : https://prove2.me/submissions/df3152fc-bde4-4edb-ab70-caf6969d3c3d

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Adapter/Weights.lean (solution of MIPRE.LIDT.Adapter.base_of_qmapS_axis);
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
import Theorems.Thm_MIPRE_LIDT_Adapter_filter_qmapS_axis_subset
import Theorems.Thm_MIPRE_LIDT_Adapter_pivots_line

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LIDT.Adapter
section
open Finset Submodule Module MIPRE.CL
variable {F : Type*} [Field F] {n : ℕ}
/-- Uniqueness of the decomposition along complementary submodules, as a rewriting rule:
an element of `p` congruent to `x` modulo `q` *is* the projection of `x`. This is how
`canonLin` is computed, since `canonLin S` is the projection onto the canonical complement
along `S`. -/
theorem projection_eq_of {E : Type*} [AddCommGroup E] [Module F E] {p q : Submodule F E}
    (hpq : IsCompl p q) {x y : E} (hy : y ∈ p) (hxy : x - y ∈ q) :
    p.projection q hpq x = y := by
  have h1 : (p.projection q hpq x : E) - y ∈ p :=
    Submodule.sub_mem _ (Submodule.projection_apply_mem hpq x) hy
  have h2 : (p.projection q hpq x : E) - y ∈ q := by
    have e : (p.projection q hpq x : E) - y = -(x - (p.projection q hpq x : E)) + (x - y) := by
      abel
    rw [e]
    exact Submodule.add_mem _ (Submodule.neg_mem _ (Submodule.sub_projection_mem hpq x)) hxy
  have hbot := hpq.inf_eq_bot
  rw [Submodule.eq_bot_iff] at hbot
  exact sub_eq_zero.mp (hbot _ ⟨h1, h2⟩)
end
end MIPRE.LIDT.Adapter

namespace MIPRE.LIDT.Adapter
section
open Finset Submodule Module MIPRE.CL
variable {F : Type*} [Field F] {n : ℕ}
/-- The seeded test's canonical base point for an axis-parallel direction: `rep eᵢ u`
zeroes the `i`-th coordinate of `u`. -/
theorem rep_single (i : Fin n) (u : Fin n → F) :
    canonLin (span F {(Pi.single i 1 : Fin n → F)}) u
      = u - u i • (Pi.single i 1 : Fin n → F) := by
  classical
  refine projection_eq_of
    (isCompl_canonCompl (span F {(Pi.single i 1 : Fin n → F)})).symm ?_ ?_
  · rw [canonCompl, mem_coordSub]
    intro j hj
    rw [pivots_line, Finset.mem_singleton] at hj
    subst hj
    simp
  · rw [sub_sub_cancel]
    exact Submodule.mem_span_singleton.mpr ⟨u i, rfl⟩
end
end MIPRE.LIDT.Adapter

namespace MIPRE.LIDT.Adapter
section
open Finset Submodule Module MIPRE.CL
variable {F : Type*} [Field F] {n : ℕ}
/-- The canonical-line test's presentation of an axis-parallel line: the direction is already
normalized, so it is unchanged, and the base point zeroes the `i`-th coordinate. -/
theorem through_single [DecidableEq F] (i : Fin n) (u : Fin n → F) :
    Line.through u (Pi.single i 1)
      = (u - u i • (Pi.single i 1 : Fin n → F), (Pi.single i 1 : Fin n → F)) := by
  classical
  have hex : ∃ j, (Pi.single i 1 : Fin n → F) j ≠ 0 := ⟨i, by simp⟩
  have hfind : Fin.find (fun j => (Pi.single i 1 : Fin n → F) j ≠ 0) hex = i := by
    rw [Fin.find_eq_iff]
    refine ⟨by simp, fun j hj => ?_⟩
    simp only [Pi.single_apply, ne_eq, ite_eq_right_iff, not_forall]
    intro hcon
    exact absurd hcon.1 (fun h : j = i => by subst h; exact absurd hj (lt_irrefl _))
  rw [Line.through, dif_pos hex]
  simp only [hfind, Pi.single_eq_same, inv_one, one_smul]
end
end MIPRE.LIDT.Adapter

namespace MIPRE.LIDT.Adapter
section
open Finset Submodule Module MIPRE.CL
variable {F : Type*} [Field F] {n : ℕ}
/-- Reversal sends the `i`-th coordinate direction to the `rev i`-th. -/
theorem revPoint_single [DecidableEq F] (i : Fin n) :
    revPoint (Pi.single i 1 : Fin n → F) = Pi.single (Fin.rev i) 1 := by
  funext j
  rw [revPoint_apply, Pi.single_apply, Pi.single_apply]
  by_cases h : j = Fin.rev i
  · rw [if_pos h, if_pos (by rw [h, Fin.rev_rev])]
  · rw [if_neg h, if_neg (fun hc : Fin.rev j = i => h (by rw [← hc, Fin.rev_rev]))]
end
end MIPRE.LIDT.Adapter

namespace MIPRE.LIDT.Adapter
section
open Finset Submodule Module MIPRE.CL
variable {F : Type*} [Field F] {n : ℕ}
/-- **Reversal exchanges the two tests' base points on an axis-parallel line.** The adapter sends
the canonical line through `u` in direction `eᵢ` to a seeded question with base point
`rep e_{rev i} (ρ u)`; reversing that back gives exactly the base point the *seeded* test
produces for the unreversed data. This is the form the weight bookkeeping needs, since the
seeded test's own samples carry the unreversed point. -/
theorem revPoint_rep_single [DecidableEq F] (i : Fin n) (u : Fin n → F) :
    revPoint (canonLin (span F {(Pi.single (Fin.rev i) 1 : Fin n → F)}) (revPoint u))
      = canonLin (span F {(Pi.single i 1 : Fin n → F)}) u := by
  rw [rep_single, rep_single, revPoint_sub, revPoint_revPoint, revPoint_smul, revPoint_single,
    Fin.rev_rev, revPoint_apply, Fin.rev_rev]
end
end MIPRE.LIDT.Adapter

namespace MIPRE.LIDT.Adapter
section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
omit [Fintype F] [NeZero m] in
/-- The adapter's axis-parallel base point, unreversed: exactly the seeded test's own. -/
theorem revPoint_through_single_eq_rep (i : Fin m) (u : Point F m) :
    revPoint (Line.through (revPoint u) (Pi.single (Fin.rev i) 1) : Line F m).1
      = CL.rep (Pi.single i 1) u := by
  have hthr : (Line.through (revPoint u) (Pi.single (Fin.rev i) 1) : Line F m).1
      = revPoint u - (revPoint u) (Fin.rev i) • (Pi.single (Fin.rev i) 1 : Point F m) := by
    rw [through_single]
  show revPoint (Line.through (revPoint u) (Pi.single (Fin.rev i) 1) : Line F m).1
      = MIPRE.CL.canonLin (Submodule.span F {(Pi.single i 1 : Point F m)}) u
  rw [hthr, ← rep_single]
  exact revPoint_rep_single i u
end
end MIPRE.LIDT.Adapter

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LIDT.Adapter
open Finset MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
theorem _root_.solution (hm : m ∣ Fintype.card F) (σc : Seed F m)
    {u₀ : Point F m} {s₀ : F} {yp : Point F m} {s : Sample F m}
    (h1 : qmapS hm σc s.questions.1 = CL.Question.aline u₀ s₀)
    (h2 : qmapS hm σc s.questions.2 = CL.Question.point yp) :
    u₀ = CL.rep (Pi.single (chi hm s₀) 1) yp := by
  classical
  have hmem := filter_qmapS_axis_subset hm σc u₀ s₀ yp
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2⟩)
  rw [Finset.mem_singleton] at hmem
  subst hmem
  have h1' : (CL.Question.aline
      (revPoint (Line.through (revPoint yp)
        (Pi.single (Fin.rev (chi hm s₀)) 1) : Line F m).1)
      (seedOf hm (Fin.rev (axisIdx (Line.through (revPoint yp)
          (Pi.single (Fin.rev (chi hm s₀)) 1) : Line F m)))
        (σc.1 (Fin.rev (axisIdx (Line.through (revPoint yp)
          (Pi.single (Fin.rev (chi hm s₀)) 1) : Line F m))))) : CL.Question F m)
      = CL.Question.aline u₀ s₀ := h1
  rw [← (CL.Question.aline.inj h1').1]
  exact revPoint_through_single_eq_rep (chi hm s₀) yp
end MIPRE.LIDT.Adapter
