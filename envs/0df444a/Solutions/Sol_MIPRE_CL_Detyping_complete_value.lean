-- Prove2me | solution 1 for MIPRE.CL.Detyping.complete_value
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:43:15.930632+00:00
-- url     : https://prove2.me/submissions/8253a53e-ef54-4b68-85eb-a74bc745d70c

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/DetypingComplete.lean (solution of MIPRE.CL.Detyping.complete_value);
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
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingCompleteSupport
import Definitions.Def_MIPRE_Foundations_CL_DetypingComplete
import Theorems.Thm_MIPRE_CL_Detyping_complete_failAt_sample
import Theorems.Thm_MIPRE_SampledGame_one_sub_value

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Game
section
open Matrix Kronecker
open scoped ComplexOrder
variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
/-- The one computation the doubling needs, in a form independent of what kind of strategy is
being summed: the four-fold sum over the doubled alphabets collapses to the original one, the
three blocks other than `(false, ·), (true, ·)` contributing zero. -/
theorem sum_doubled (G : Game X X A A) (f : (Bool × X) → (Bool × X) → A → A → ℝ) :
    (∑ p, ∑ q, ∑ a, ∑ b,
        G.doubled.μ p q * (if G.doubled.D p q a b then 1 else 0) * f p q a b)
      = ∑ x, ∑ y, ∑ a, ∑ b,
          G.μ x y * (if G.D x y a b then 1 else 0) * f (false, x) (true, y) a b := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, doubled_μ, doubled_D]
  simp
end
end MIPRE.Game

namespace MIPRE.TensorProductStrategy
section
open Matrix Kronecker
open scoped ComplexOrder
variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
theorem value_undouble {G : Game X X A A} (S : TensorProductStrategy G.doubled.toGame) :
    S.undouble.value = S.value := by
  rw [show S.value = ∑ p, ∑ q, ∑ a, ∑ b, G.doubled.μ p q *
      (if G.doubled.D p q a b then 1 else 0) *
      (star S.ψ ⬝ᵥ ((S.PA.M p a ⊗ₖ S.PB.M q b) *ᵥ S.ψ)).re from rfl,
    Game.sum_doubled]
  rfl
end
end MIPRE.TensorProductStrategy

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.CL.Detyping
open Finset Classical Matrix Kronecker
set_option linter.unusedSectionVars false
variable {T ι A : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]
  [Fintype A] [DecidableEq A]
theorem _root_.solution {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E]
    (hE : ∀ u v, E u v → E v u) (hne : (Graph.edges E).Nonempty)
    (P : Bool → T → CLFun (ZMod 2) ι ℓ) (hP : ∀ w t, (P w t).ExactlyOn univ) (hℓ : 0 < ℓ)
    (D : Question T ι → Question T ι → A → A → Bool)
    (S : SyncStrategy (typedGame E hne P D).doubled) (hval : S.value = 1) (a₀ : A) :
    (complete E hne P D S a₀).value = 1 := by
  have h := SampledGame.one_sub_value (presentation E false (P false)).eval
    (presentation E true (P true)).eval (accepts E D)
    (complete E hne P D S a₀).toTensorProductStrategy.undouble
  have hz : ∀ s : Coord T ι → ZMod 2,
      (complete E hne P D S a₀).toTensorProductStrategy.undouble.failAt
        ((presentation E false (P false)).eval s) ((presentation E true (P true)).eval s) = 0 := by
    intro s
    have hs : s = Sum.elim (pull .inl s) (pull .inr s) := by ext p; cases p <;> rfl
    rw [hs]
    exact complete_failAt_sample E hE hne P hP hℓ D S hval a₀ _ _
  change 1 - (complete E hne P D S a₀).toTensorProductStrategy.undouble.value =
    (∑ s : Coord T ι → ZMod 2,
      (complete E hne P D S a₀).toTensorProductStrategy.undouble.failAt
        ((presentation E false (P false)).eval s) ((presentation E true (P true)).eval s)) /
      Fintype.card (Coord T ι → ZMod 2) at h
  rw [TensorProductStrategy.value_undouble, SyncStrategy.value_toTensorProductStrategy] at h
  simp only [hz, Finset.sum_const_zero, zero_div] at h
  linarith
end MIPRE.CL.Detyping
