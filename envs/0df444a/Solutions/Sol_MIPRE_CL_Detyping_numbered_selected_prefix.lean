-- Prove2me | solution 1 for MIPRE.CL.Detyping.numbered_selected_prefix
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:43:17.244763+00:00
-- url     : https://prove2.me/submissions/fd11a284-4a0b-459f-9de7-9b961a23b14f

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/DetypingProgQueries.lean (solution of MIPRE.CL.Detyping.numbered_selected_prefix);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgQueries
import Theorems.Thm_MIPRE_CL_Detyping_numbered_marginal_content
import Theorems.Thm_MIPRE_CL_Detyping_select_output

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.CL.Detyping
open Finset Classical
set_option linter.unusedSectionVars false
variable {T : Type*} [Fintype T] [DecidableEq T]
theorem _root_.solution {s ℓ : ℕ} (E : T → T → Prop) [DecidableRel E] (w : Player)
    (P : T → CLFun 𝔽₂ (Fin s) ℓ) (hP : ∀ t, (P t).ExactlyOn univ) (hℓ : 0 < ℓ)
    (r : ℕ) (hr : 1 ≤ r) (u : Cost.BitStr)
    (hu : ∃ x, u = toBits (((numbered E w P).truncate (r + 1)).eval x))
    {t : T} (ht : select E w.toBool (graphOfBits (u.take (graphDim T))) = some t) :
    ∃ v, u.drop (graphDim T) = toBits (((P t).truncate (r - 1)).eval v) := by
  obtain ⟨x, rfl⟩ := hu
  have hi : r - 1 + 2 = r + 1 := by omega
  have hm := numbered_marginal_content E w P hP hℓ (r - 1) (toBits x) (length_toBits x)
  rw [ofBits_toBits, hi] at hm
  rw [hm] at ht ⊢
  simp only [take_graph_append, graphOfBits_graphBits, select_output] at ht
  refine ⟨ofBits s ((toBits x).drop (graphDim T)), ?_⟩
  rw [drop_graph_append, ht]
  rfl
end MIPRE.CL.Detyping
