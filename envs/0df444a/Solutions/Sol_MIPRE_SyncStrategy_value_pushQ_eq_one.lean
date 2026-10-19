-- Prove2me | solution 1 for MIPRE.SyncStrategy.value_pushQ_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:46:35.532292+00:00
-- url     : https://prove2.me/submissions/0d374e18-cc7b-4a46-8953-bc14df88ce6d

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SyncPushQ.lean (solution of MIPRE.SyncStrategy.value_pushQ_eq_one);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_PerfectStrategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_SyncPushQ
import Theorems.Thm_MIPRE_tracialValue_eq_one_of_re_eq_zero

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.SyncStrategy
section
open Finset
open scoped ComplexOrder
variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
variable {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Module ℂ 𝒜]
variable {G : SynchronousGame X A}
/-- `SyncStrategy.value` is the generic tracial value at the normalized trace, by definition.
Named so that the application below need not ask the unifier to see through `value`, which is
a `whnf` timeout when it does. -/
theorem value_eq_tracialValue (S : SyncStrategy G) :
    S.value = tracialValue G
      (normalizedTrace (Fin S.d) (hn := Fin.pos_iff_nonempty.mp S.d_pos)) S.P := rfl
end
end MIPRE.SyncStrategy

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.SyncStrategy
open Finset
variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A] {G : SynchronousGame X A}
theorem _root_.solution (S : SyncStrategy G) {X' A' : Type*} [Fintype X'] [Fintype A']
    [DecidableEq A'] (G' : SynchronousGame X' A') (g : X' → X) (f : X' → A → A')
    (hZ : ∀ x y, 0 < G.μ x y → ∀ a b, G.D x y a b = false → S.P.M x a * S.P.M y b = 0)
    (h : ∀ x' y', 0 < G'.μ x' y' → 0 < G.μ (g x') (g y') ∧ ∀ a b,
      (0 < G.μ (g x') (g x') → G.D (g x') (g x') a a = true) →
      (0 < G.μ (g y') (g y') → G.D (g y') (g y') b b = true) →
      G.D (g x') (g y') a b = true → G'.D x' y' (f x' a) (f y' b) = true) :
    (S.pushQ G' g f).value = 1 := by
  rw [value_eq_tracialValue]
  refine tracialValue_eq_one_of_re_eq_zero G' _ _ ?_
  intro x' y' hxy a' b' hrej
  obtain ⟨hμ, hacc⟩ := h x' y' hxy
  have hprod : (S.pushQ G' g f).P.M x' a' * (S.pushQ G' g f).P.M y' b' = 0 := by
    change (∑ a ∈ univ.filter fun a => f x' a = a', S.P.M (g x') a) *
      (∑ b ∈ univ.filter fun b => f y' b = b', S.P.M (g y') b) = 0
    rw [Finset.sum_mul_sum]
    refine Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun b hb => ?_
    have ha' := (Finset.mem_filter.1 ha).2
    have hb' := (Finset.mem_filter.1 hb).2
    by_cases hA : 0 < G.μ (g x') (g x') ∧ G.D (g x') (g x') a a = false
    · have h0 : S.P.M (g x') a = 0 := by
        rw [← S.P.projective (g x') a]
        exact hZ _ _ hA.1 a a hA.2
      rw [h0, Matrix.zero_mul]
    by_cases hB : 0 < G.μ (g y') (g y') ∧ G.D (g y') (g y') b b = false
    · have h0 : S.P.M (g y') b = 0 := by
        rw [← S.P.projective (g y') b]
        exact hZ _ _ hB.1 b b hB.2
      rw [h0, Matrix.mul_zero]
    by_cases hD : G.D (g x') (g y') a b = true
    · have := hacc a b (fun hp => by simpa [hp] using hA) (fun hp => by simpa [hp] using hB) hD
      rw [ha', hb', hrej] at this
      exact absurd this Bool.false_ne_true
    · exact hZ _ _ hμ a b (by simpa using hD)
  rw [hprod, normalizedTrace_apply, Matrix.trace_zero, mul_zero, Complex.zero_re]
end MIPRE.SyncStrategy
