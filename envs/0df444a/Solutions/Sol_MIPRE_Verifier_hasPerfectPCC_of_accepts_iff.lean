-- Prove2me | solution 1 for MIPRE.Verifier.hasPerfectPCC_of_accepts_iff
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-15T20:58:25.736988+00:00
-- url     : https://prove2.me/submissions/a82c3c48-f87c-475b-bf6a-b64a2f054152

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/VerifierValue.lean (solution of MIPRE.Verifier.hasPerfectPCC_of_accepts_iff);
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
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_VerifierValue

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
theorem _root_.solution {V W : Verifier ℓ} {n T : ℕ} (hS : W.sampler = V.sampler)
    (h : ∀ x y a b, V.decider.Accepts n x y a b ↔ W.decider.Accepts n x y a b)
    (hV : V.HasPerfectPCC n T) : W.HasPerfectPCC n T := by
  obtain ⟨SW, DW, hW⟩ := W
  obtain ⟨SV, DV, hV'⟩ := V
  simp only at hS
  subst hS
  obtain ⟨S, hpcc, hval⟩ := hV
  have hD : ∀ p q a b, ((⟨SW, DW, hW⟩ : Verifier ℓ).doubledGame n T).D p q a b =
      ((⟨SW, DV, hV'⟩ : Verifier ℓ).doubledGame n T).D p q a b := by
    intro p q a b
    classical
    simp only [doubledGame, Game.doubled_D]
    split_ifs
    · exact decide_eq_decide.2 (h _ _ _ _).symm
    · rfl
  refine ⟨S.copy _, S.isPCC_copy hpcc _ (fun _ _ => rfl), ?_⟩
  rw [S.value_copy (Verifier.doubledGame ⟨SW, DW, hW⟩ n T) (fun _ _ => rfl) hD, hval]
end MIPRE.Verifier
