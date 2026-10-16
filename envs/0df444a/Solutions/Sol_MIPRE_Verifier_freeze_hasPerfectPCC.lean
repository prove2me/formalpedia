-- Prove2me | solution 1 for MIPRE.Verifier.freeze_hasPerfectPCC
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-15T20:33:08.540987+00:00
-- url     : https://prove2.me/submissions/147f6951-594b-413f-9ef1-137dc5974c48

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Freeze.lean (solution of MIPRE.Verifier.freeze_hasPerfectPCC);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_Halting_Freeze

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.SyncStrategy
open Matrix Kronecker
open scoped ComplexOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [DecidableEq A] {G : SynchronousGame X A}
theorem value_copy (S : SyncStrategy G) (G' : SynchronousGame X A)
    (hμ : ∀ x y, G'.μ x y = G.μ x y) (hD : ∀ x y a b, G'.D x y a b = G.D x y a b) :
    (S.copy G').value = S.value := by
  rw [value_eq, value_eq]
  show (∑ x, ∑ y, ∑ a, ∑ b, G'.μ x y * (if G'.D x y a b then 1 else 0) *
      ((S.P.M x a * S.P.M y b).trace.re / (S.d : ℝ))) =
    ∑ x, ∑ y, ∑ a, ∑ b, G.μ x y * (if G.D x y a b then 1 else 0) *
      ((S.P.M x a * S.P.M y b).trace.re / (S.d : ℝ))
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hμ, hD]
end MIPRE.SyncStrategy

namespace MIPRE.SyncStrategy
open Matrix Kronecker
open scoped ComplexOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [DecidableEq A] {G : SynchronousGame X A}
theorem isPCC_copy {S : SyncStrategy G} (hS : S.IsPCC) (G' : SynchronousGame X A)
    (hμ : ∀ x y, G'.μ x y = G.μ x y) : (S.copy G').IsPCC :=
  fun x y hxy a b => hS x y (by rwa [hμ] at hxy) a b
end MIPRE.SyncStrategy

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Verifier
open Cost
variable {ℓ : ℕ} (V : Verifier ℓ)
theorem _root_.solution (k n T : ℕ) :
    (V.freeze k).HasPerfectPCC n T ↔ V.HasPerfectPCC k T := by
  have hD : ∀ p q a b, ((V.freeze k).doubledGame n T).D p q a b
      = (V.doubledGame k T).D p q a b := by
    intro p q a b
    change (if p.1 = false ∧ q.1 = true then ((V.freeze k).game n T).D p.2 q.2 a b else false)
      = (if p.1 = false ∧ q.1 = true then (V.game k T).D p.2 q.2 a b else false)
    split_ifs
    · exact decide_eq_decide.2 (V.decider.freeze_accepts k n _ _ _ _)
    · rfl
  constructor
  · rintro ⟨S, hpcc, hval⟩
    refine ⟨S.copy (V.doubledGame k T), S.isPCC_copy hpcc _ (fun _ _ => rfl), ?_⟩
    exact (S.value_copy (V.doubledGame k T) (fun _ _ => rfl) fun p q a b =>
      (hD p q a b).symm).trans hval
  · rintro ⟨S, hpcc, hval⟩
    refine ⟨S.copy ((V.freeze k).doubledGame n T), S.isPCC_copy hpcc _ (fun _ _ => rfl), ?_⟩
    exact (S.value_copy ((V.freeze k).doubledGame n T) (fun _ _ => rfl) hD).trans hval
end MIPRE.Verifier
