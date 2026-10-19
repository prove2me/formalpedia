-- Prove2me | solution 1 for MIPRE.Introspection.TypedPresentation.mu_aux
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:22:15.230227+00:00
-- url     : https://prove2.me/submissions/ad228cbe-1dde-4a3f-8f26-0ba00a170e89

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/TypedPresentation.lean (solution of MIPRE.Introspection.TypedPresentation.mu_aux);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
import Definitions.Def_MIPRE_Foundations_Introspection_Types
import Definitions.Def_MIPRE_Foundations_Introspection_TypeGraph
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPresentation
import Theorems.Thm_MIPRE_Introspection_TypeGraph_edges_nonempty

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.TypedPresentation
open Finset Classical
variable {PauliType F ι : Type*} [Fintype ι] [DecidableEq ι] [Semiring F] {ℓ : ℕ}
variable [Fintype PauliType] [DecidableEq PauliType]
  {A B : Type*} [Fintype A] [Fintype B]
theorem _root_.solution (E : PauliType → PauliType → Bool) (X Z : PauliType)
    (P : PauliType → CL.CLFun (ZMod 2) ι 3)
    (D : CL.Detyping.Question (QuestionType PauliType ℓ) ι →
      CL.Detyping.Question (QuestionType PauliType ℓ) ι → A → B → Bool)
    (t u : AuxType ℓ) (w w' : Bool)
    (h : TypeGraph.Adj E X Z (.inr (t, w)) (.inr (u, w'))) :
    (game E X Z ℓ P D).μ (.inr (t, w), 0) (.inr (u, w'), 0) =
      ((TypeGraph.edges E X Z ℓ).card : ℝ)⁻¹ := by
  let G := TypeGraph.Adj (ℓ := ℓ) E X Z
  let e₀ : CL.Detyping.Edge G := ⟨(.inr (t, w), .inr (u, w')), by
    simp only [CL.Graph.edges, Finset.mem_filter, Finset.mem_univ, true_and]
    exact h⟩
  have heq (e : CL.Detyping.Edge G) (z : ι → ZMod 2) :
      (CL.Detyping.typedQuestion (fun _ => family P) false (e, z),
        CL.Detyping.typedQuestion (fun _ => family P) true (e, z)) =
        ((.inr (t, w), 0), (.inr (u, w'), 0)) ↔ e = e₀ := by
    constructor
    · intro hh
      apply Subtype.ext
      have hh' := congrArg (fun p => (p.1.1, p.2.1)) hh
      exact hh'
    · rintro rfl
      simp [CL.Detyping.typedQuestion, e₀]
  unfold game CL.Detyping.typedGame SampledGame.game SampledGame.dist
  dsimp only
  simp only [Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type, heq,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, mul_one]
  have hc : (Fintype.card (ι → ZMod 2) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [mul_inv_rev, mul_assoc, mul_left_comm, inv_mul_cancel₀ hc, mul_one]
  simp only [Fintype.card_coe, TypeGraph.edges]
end MIPRE.Introspection.TypedPresentation
