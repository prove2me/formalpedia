-- Prove2me | solution 1 for MIPRE.CL.Detyping.valid_average_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:41:24.755259+00:00
-- url     : https://prove2.me/submissions/1414ea57-e722-4fa8-878c-866ef5f9d2f7

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/DetypingSoundness.lean (solution of MIPRE.CL.Detyping.valid_average_le);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.CL.Graph
noncomputable section
open Finset Classical
variable {T : Type*} [Fintype T] [DecidableEq T]
/-- The one-hot half makes the encoding injective, even for an isolated vertex. -/
theorem encode_injective (E : T → T → Prop) [DecidableRel E] :
    Function.Injective (encode E) := by
  intro u v h
  have hh := congrFun h (false, u)
  by_contra huv
  simpa [encode, huv] using hh
end
end MIPRE.CL.Graph

namespace MIPRE.CL.Graph
noncomputable section
open Finset Classical
variable {T : Type*} [Fintype T] [DecidableEq T]
/-- Encoding an ordered pair is injective. -/
theorem pairSeed_injective (E : T → T → Prop) [DecidableRel E] :
    Function.Injective (pairSeed E) := by
  intro uv uv' h
  apply Prod.ext
  · apply encode_injective E
    funext p
    exact congrFun h (false, p)
  · apply encode_injective E
    funext p
    exact congrFun h (true, p)
end
end MIPRE.CL.Graph

namespace MIPRE.CL.Graph
noncomputable section
open Finset Classical
variable {T : Type*} [Fintype T] [DecidableEq T]
/-- The rejection event has exactly one seed per ordered edge. -/
theorem card_validSeeds (E : T → T → Prop) [DecidableRel E] :
    (validSeeds E).card = (edges E).card :=
  Finset.card_image_of_injective _ (pairSeed_injective E)
end
end MIPRE.CL.Graph

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.CL.Detyping
open Finset Classical
variable {T ι : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]
theorem _root_.solution (E : T → T → Prop) [DecidableRel E] (hne : (Graph.edges E).Nonempty)
    (f : (Graph.Coord T → ZMod 2) → (ι → ZMod 2) → ℝ) (hf : ∀ g v, 0 ≤ f g v) :
    (∑ g ∈ Graph.validSeeds E, ∑ v, f g v) /
        ((Graph.validSeeds E).card * Fintype.card (ι → ZMod 2)) ≤
      (16 : ℝ) ^ Fintype.card T *
        ((∑ g, ∑ v, f g v) / ((16 : ℝ) ^ Fintype.card T * Fintype.card (ι → ZMod 2))) := by
  have hv : (0 : ℝ) < Fintype.card (ι → ZMod 2) := by exact_mod_cast Fintype.card_pos
  have he : (1 : ℝ) ≤ (Graph.edges E).card := by exact_mod_cast hne.card_pos
  have hp : (16 : ℝ) ^ Fintype.card T ≠ 0 := pow_ne_zero _ (by norm_num)
  have hnonneg : 0 ≤ ∑ g ∈ Graph.validSeeds E, ∑ v, f g v :=
    Finset.sum_nonneg fun g _ => Finset.sum_nonneg fun v _ => hf g v
  have hsub : (∑ g ∈ Graph.validSeeds E, ∑ v, f g v) ≤ ∑ g, ∑ v, f g v :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun g _ _ => Finset.sum_nonneg fun v _ => hf g v)
  rw [Graph.card_validSeeds]
  calc
    _ ≤ (∑ g ∈ Graph.validSeeds E, ∑ v, f g v) / Fintype.card (ι → ZMod 2) := by
      apply div_le_div_of_nonneg_left hnonneg hv
      nlinarith
    _ ≤ (∑ g, ∑ v, f g v) / Fintype.card (ι → ZMod 2) :=
      div_le_div_of_nonneg_right hsub hv.le
    _ = _ := by field_simp
end MIPRE.CL.Detyping
