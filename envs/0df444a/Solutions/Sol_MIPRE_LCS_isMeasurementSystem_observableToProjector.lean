-- Prove2me | solution 1 for MIPRE.LCS.isMeasurementSystem_observableToProjector
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:40:34.278308+00:00
-- url     : https://prove2.me/submissions/15bc7599-da70-494a-a547-5819031db840

/-
Copyright (c) 2026 Sean Perazzolo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sean Perazzolo
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/LCS/Strategy/ObservableToProjector.lean (solution of MIPRE.LCS.isMeasurementSystem_observableToProjector);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_LCS_Basic
import Definitions.Def_MIPRE_LCS_Common
import Definitions.Def_MIPRE_LCS_Measurement
import Definitions.Def_MIPRE_LCS_Observable
import Definitions.Def_MIPRE_LCS_Strategy_ObservableToProjector
import Theorems.Thm_MIPRE_LCS_idempotent_observableToProjector
import Theorems.Thm_MIPRE_LCS_zmod_two_eq_zero_or_one

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LCS
section
/-- The `ZMod 2` counterpart of `Fin.sum_univ_two`. -/
lemma sum_univ_zmod_two {M : Type*} [AddCommMonoid M] (f : ZMod 2 → M) :
    ∑ x, f x = f 0 + f 1 := by
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} from by decide,
    Finset.sum_insert (by decide), Finset.sum_singleton]
end
end MIPRE.LCS

namespace MIPRE.LCS
section
variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
/-- If $O$ is an observable, then the projector
$P_a = (1/2)(1 + (-1)^a O)$ is self-adjoint. -/
lemma star_observableToProjector (O : R) (hO : IsObservable O) (a : ZMod 2) :
    star (observableToProjector O a) = observableToProjector O a := by
  rcases zmod_two_eq_zero_or_one a with rfl | rfl
  all_goals (
    simp [observableToProjector]
    simp [observableSign]
    simp [hO.self_adjoint]
  )
end
end MIPRE.LCS

namespace MIPRE.LCS
section
variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
omit [StarModule ℂ R] in
/-- The two projectors associated to the two outcomes of a single observable are orthogonal:
$P_0 P_1 = 0$. -/
lemma orthogonal_observableToProjector (O : R) (hO : IsObservable O) :
    observableToProjector O 0 * observableToProjector O 1 = 0 := by
  calc
    observableToProjector O 0 * observableToProjector O 1
        = ((1 / 2 : ℂ) * (1 / 2 : ℂ)) • ((1 + O) * (1 + (-1 : ℂ) • O)) := by
            simpa [observableToProjector, observableSign] using
              (smul_mul_smul (1 / 2 : ℂ) (1 + O) (1 / 2 : ℂ) (1 + (-1 : ℂ) • O))
      _ = ((1 / 2 : ℂ) * (1 / 2 : ℂ)) • (0 : R) := by
          congr 1
          rw [add_mul, one_mul, mul_add, mul_one, mul_smul_comm, hO.involutive]
          norm_num
      _ = 0 := by simp
end
end MIPRE.LCS

namespace MIPRE.LCS
section
variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
omit [StarRing R] [StarModule ℂ R] in
/-- The two projectors associated to a single observable form a complete binary measurement:
$P_0 + P_1 = 1$. -/
lemma sum_one_observableToProjector (O : R) :
    observableToProjector O 0 + observableToProjector O 1 = 1 := by
  calc
    observableToProjector O 0 + observableToProjector O 1
    = ((1 / 2 : ℂ) + (1 / 2 : ℂ)) • (1 : R) := by
      rw [observableToProjector, observableToProjector, observableSign, observableSign, if_pos rfl,
        if_neg (by decide)]
      simp [smul_add, add_assoc, ← add_smul]
    _ = 1 := by
      norm_num
end
end MIPRE.LCS

namespace MIPRE.LCS
section
variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
omit [StarRing R] [StarModule ℂ R] in
/-- If observables $O₁$ and $O₂$ commute, then all corresponding projectors
$P_a(O₁)$ and $P_b(O₂)$ commute as well. -/
lemma commute_observableToProjector {O1 O2 : R} (h : Commute O1 O2) (a b : ZMod 2) :
    Commute (observableToProjector O1 a) (observableToProjector O2 b) := by
  rw [observableToProjector, observableToProjector]
  apply Commute.smul_right
  apply Commute.smul_left
  apply Commute.add_left (.one_left _)
  apply Commute.add_right (.one_right _)
  exact (h.smul_left _).smul_right _
end
end MIPRE.LCS

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LCS
variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
theorem _root_.solution (O : R) (hO : IsObservable O) :
    IsMeasurementSystem (observableToProjector O) where
  sum_one := by
    rw [sum_univ_zmod_two, sum_one_observableToProjector]
  idempotent a := idempotent_observableToProjector O hO a
  orthogonal a b hab := by
    rcases zmod_two_eq_zero_or_one a with rfl | rfl <;>
      rcases zmod_two_eq_zero_or_one b with rfl | rfl <;>
        try exact absurd rfl hab
    · exact orthogonal_observableToProjector O hO
    · rw [commute_observableToProjector (Commute.refl O) 1 0]
      exact orthogonal_observableToProjector O hO
  self_adjoint a := star_observableToProjector O hO a
end MIPRE.LCS
