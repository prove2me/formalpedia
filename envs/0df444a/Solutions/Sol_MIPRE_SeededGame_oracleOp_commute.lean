-- Prove2me | solution 1 for MIPRE.SeededGame.oracleOp_commute
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:44:17.666734+00:00
-- url     : https://prove2.me/submissions/f7846956-19e5-45aa-90c4-e762b5cb9ada

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/OracularComplete.lean (solution of MIPRE.SeededGame.oracleOp_commute);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_OracularGame
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_PerfectStrategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_OracularComplete

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.SeededGame
section
open Finset Matrix
variable {V A : Type*} [Fintype V] [DecidableEq V] [Nonempty V] [Fintype A] [DecidableEq A]
variable (S : SeededGame V A)
variable {S}
variable (S)
variable {S}
omit [Nonempty V] [Fintype A] [DecidableEq A] in
/-- On the support of `oDist` the two questions are read off one seed. -/
theorem exists_of_oDist_pos {p q : Role × V} (h : 0 < S.oDist p q) :
    ∃ r₁ r₂ z, S.oquestion r₁ z = p ∧ S.oquestion r₂ z = q := by
  by_contra hc
  push Not at hc
  rw [oDist] at h
  refine absurd (Finset.sum_eq_zero fun s _ => ?_) h.ne'
  obtain ⟨r₁, r₂, z⟩ := s
  have hne : (S.oquestion r₁ z, S.oquestion r₂ z) ≠ (p, q) := by
    intro he
    rw [Prod.ext_iff] at he
    exact hc r₁ r₂ z he.1 he.2
  simp [hne]
end
end MIPRE.SeededGame

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.SeededGame
open Finset Matrix
variable {V A : Type*} [Fintype V] [DecidableEq V] [Nonempty V] [Fintype A] [DecidableEq A]
variable (S : SeededGame V A)
variable {S}
variable (S)
variable {S}
variable (S)
variable {S}
theorem _root_.solution (T : SyncStrategy S.toGame.doubled) (hT : T.IsPCC)
    {p q : Role × V} (hμ : 0 < S.oDist p q) (u v : OAns A) :
    S.oracleOp T p u * S.oracleOp T q v = S.oracleOp T q v * S.oracleOp T p u := by
  obtain ⟨r₁, r₂, z, hp, hq⟩ := exists_of_oDist_pos hμ
  subst hp; subst hq
  -- the four atoms at seed `z` commute pairwise
  have c1 : ∀ a a' : A, Commute (T.P.M (false, S.LA z) a) (T.P.M (false, S.LA z) a') := by
    intro a a'
    by_cases h : a = a'
    · rw [h]
    · show _ * _ = _ * _
      rw [T.orthogonal (false, S.LA z) h, T.orthogonal (false, S.LA z) (Ne.symm h)]
  have c2 : ∀ b b' : A, Commute (T.P.M (true, S.LB z) b) (T.P.M (true, S.LB z) b') := by
    intro b b'
    by_cases h : b = b'
    · rw [h]
    · show _ * _ = _ * _
      rw [T.orthogonal (true, S.LB z) h, T.orthogonal (true, S.LB z) (Ne.symm h)]
  have c3 : ∀ a b : A, Commute (T.P.M (false, S.LA z) a) (T.P.M (true, S.LB z) b) :=
    fun a b => commute_of_isPCC hT z a b
  -- hence every honest operator at seed `z` commutes with each atom
  have kA : ∀ (r : Role) (w : OAns A) (a : A),
      Commute (S.oracleOp T (S.oquestion r z) w) (T.P.M (false, S.LA z) a) := by
    intro r w a
    cases r <;> cases w <;>
      simp only [oquestion, oracleOp_oracle_pair, oracleOp_oracle_single, oracleOp_alice_pair,
        oracleOp_alice_single, oracleOp_bob_pair, oracleOp_bob_single] <;>
      first
        | exact Commute.zero_left _
        | exact c1 _ _
        | exact (c3 _ _).symm
        | exact Commute.mul_left (c1 _ _) ((c3 _ _).symm)
  have kB : ∀ (r : Role) (w : OAns A) (b : A),
      Commute (S.oracleOp T (S.oquestion r z) w) (T.P.M (true, S.LB z) b) := by
    intro r w b
    cases r <;> cases w <;>
      simp only [oquestion, oracleOp_oracle_pair, oracleOp_oracle_single, oracleOp_alice_pair,
        oracleOp_alice_single, oracleOp_bob_pair, oracleOp_bob_single] <;>
      first
        | exact Commute.zero_left _
        | exact c2 _ _
        | exact c3 _ _
        | exact Commute.mul_left (c3 _ _) (c2 _ _)
  -- so it commutes with every honest operator, by induction on the second one's shape
  cases r₂ <;> cases v <;>
    simp only [oquestion, oracleOp_oracle_pair, oracleOp_oracle_single, oracleOp_alice_pair,
      oracleOp_alice_single, oracleOp_bob_pair, oracleOp_bob_single] <;>
    first
      | exact Commute.zero_right _
      | exact kA _ _ _
      | exact kB _ _ _
      | exact Commute.mul_right (kA _ _ _) (kB _ _ _)
end MIPRE.SeededGame
