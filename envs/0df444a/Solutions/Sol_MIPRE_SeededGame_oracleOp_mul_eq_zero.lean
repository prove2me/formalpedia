-- Prove2me | solution 1 for MIPRE.SeededGame.oracleOp_mul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:46:32.615986+00:00
-- url     : https://prove2.me/submissions/aef68e90-f467-44ee-b8fc-e8244c6fdde1

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/OracularComplete.lean (solution of MIPRE.SeededGame.oracleOp_mul_eq_zero);
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
import Theorems.Thm_MIPRE_re_eq_zero_of_tracialValue_eq_one

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

namespace MIPRE.SyncStrategy
section
open Finset
open scoped ComplexOrder
variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
variable {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Module ℂ 𝒜]
variable {G : SynchronousGame X A}
open scoped Matrix in
/-- The real part of the normalized trace, written out. Stated once because both the value-one
characterization and the faithfulness lemmas below need it. -/
theorem normalizedTrace_re (S : SyncStrategy G) (M : Matrix (Fin S.d) (Fin S.d) ℂ) :
    ((normalizedTrace (Fin S.d) (hn := Fin.pos_iff_nonempty.mp S.d_pos)) M).re
      = M.trace.re / (S.d : ℝ) := by
  show ((Fintype.card (Fin S.d) : ℂ)⁻¹ * M.trace).re = _
  rw [Fintype.card_fin, ← Complex.ofReal_natCast, ← Complex.ofReal_inv,
    Complex.re_ofReal_mul, inv_mul_eq_div]
end
end MIPRE.SyncStrategy

namespace MIPRE.SyncStrategy
section
open Finset
open scoped ComplexOrder
variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
variable {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Module ℂ 𝒜]
variable {G : SynchronousGame X A}
/-- The synchronous spelling: a value-`1` synchronous strategy has `Tr(M^x_a M^y_b) = 0` for
every rejected answer pair at every question pair of positive weight. -/
theorem re_eq_zero_of_value_eq_one (S : SyncStrategy G) (h : S.value = 1)
    {x y : X} (hxy : 0 < G.μ x y) {a b : A} (hD : G.D x y a b = false) :
    (S.P.M x a * S.P.M y b).trace.re / (S.d : ℝ) = 0 := by
  have h' : tracialValue G
      (normalizedTrace (Fin S.d) (hn := Fin.pos_iff_nonempty.mp S.d_pos)) S.P = 1 := by
    rw [← value_eq_tracialValue]; exact h
  rw [← normalizedTrace_re]
  exact re_eq_zero_of_tracialValue_eq_one G _ S.P h' hxy hD
end
end MIPRE.SyncStrategy

namespace MIPRE.SyncStrategy
section
open Finset
open scoped ComplexOrder
variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
variable {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Module ℂ 𝒜]
variable {G : SynchronousGame X A}
open scoped Matrix in
/-- A self-adjoint idempotent whose normalized trace vanishes is the zero operator. -/
theorem eq_zero_of_trace_re_eq_zero (S : SyncStrategy G) {M : Matrix (Fin S.d) (Fin S.d) ℂ}
    (hsa : star M = M) (hidem : M * M = M) (h : M.trace.re / (S.d : ℝ) = 0) : M = 0 := by
  have hd : (S.d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr S.d_pos.ne'
  have hre : M.trace.re = 0 := (div_eq_zero_iff.mp h).resolve_right hd
  have him : M.trace.im = 0 := by
    refine Complex.conj_eq_iff_im.mp ?_
    rw [starRingEnd_apply, ← Matrix.trace_conjTranspose, ← Matrix.star_eq_conjTranspose, hsa]
  have htr : M.trace = 0 := Complex.ext hre him
  have hH : Mᴴ * M = M := by rw [← Matrix.star_eq_conjTranspose, hsa, hidem]
  exact Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp (by rw [hH, htr])
end
end MIPRE.SyncStrategy

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

namespace MIPRE.SeededGame
section
open Finset Matrix
variable {V A : Type*} [Fintype V] [DecidableEq V] [Nonempty V] [Fintype A] [DecidableEq A]
variable (S : SeededGame V A)
variable {S}
variable (S)
variable {S}
omit [Nonempty V] [Fintype A] [DecidableEq A] in
/-- On the support, equal roles mean equal questions. -/
theorem eq_of_oDist_pos_of_fst_eq {p q : Role × V} (h : 0 < S.oDist p q) (hr : p.1 = q.1) :
    p = q := by
  obtain ⟨r₁, r₂, z, hp, hq⟩ := exists_of_oDist_pos h
  have h1 : r₁ = p.1 := by rw [← hp, oquestion_fst]
  have h2 : r₂ = q.1 := by rw [← hq, oquestion_fst]
  have hrr : r₁ = r₂ := by rw [h1, h2]; exact hr
  rw [← hp, ← hq, hrr]
end
end MIPRE.SeededGame

namespace MIPRE.SeededGame
section
open Finset Matrix
variable {V A : Type*} [Fintype V] [DecidableEq V] [Nonempty V] [Fintype A] [DecidableEq A]
variable (S : SeededGame V A)
variable {S}
variable (S)
variable {S}
/-- An answer whose shape does not match the role gets the zero operator. -/
theorem oracleOp_eq_zero_of_shapeOk (T : SyncStrategy S.toGame.doubled) {p : Role × V}
    {u : OAns A} (h : shapeOk p.1 u = false) : S.oracleOp T p u = 0 := by
  obtain ⟨r, z⟩ := p
  cases r <;> cases u <;> simp_all [shapeOk]
end
end MIPRE.SeededGame

namespace MIPRE.SeededGame
section
open Finset Matrix
variable {V A : Type*} [Fintype V] [DecidableEq V] [Nonempty V] [Fintype A] [DecidableEq A]
variable (S : SeededGame V A)
variable {S}
variable (S)
variable {S}
/-- An oracle's answer pair that the original predicate rejects gets the zero operator. -/
theorem oracleOp_eq_zero_of_gameCheck (T : SyncStrategy S.toGame.doubled) (hT : T.IsPCC)
    (hval : T.value = 1) {p : Role × V} {u : OAns A} (h : S.gameCheck p u = false) :
    S.oracleOp T p u = 0 := by
  obtain ⟨r, z⟩ := p
  cases r <;> cases u <;> simp only [gameCheck, Bool.true_eq_false] at h
  rename_i a b
  have hD : S.toGame.doubled.D (false, S.LA z) (true, S.LB z) a b = false := by
    simpa using h
  exact T.eq_zero_of_trace_re_eq_zero
    ((S.oracleMeas T hT).selfAdjoint (.oracle, z) (.pair a b))
    ((S.oracleMeas T hT).projective (.oracle, z) (.pair a b))
    (T.re_eq_zero_of_value_eq_one hval (S.doubled_mu_pos z) hD)
end
end MIPRE.SeededGame

namespace MIPRE.SeededGame
section
open Finset Matrix
variable {V A : Type*} [Fintype V] [DecidableEq V] [Nonempty V] [Fintype A] [DecidableEq A]
variable (S : SeededGame V A)
variable {S}
variable (S)
variable {S}
/-- Transposing a vanishing product: the operators are self-adjoint, so one order vanishes
exactly when the other does. -/
theorem oracleOp_mul_eq_zero_of_swap (T : SyncStrategy S.toGame.doubled) (hT : T.IsPCC)
    {p q : Role × V} {u v : OAns A} (h : S.oracleOp T q v * S.oracleOp T p u = 0) :
    S.oracleOp T p u * S.oracleOp T q v = 0 := by
  have h1 : star (S.oracleOp T p u) = S.oracleOp T p u := by
    simpa using (S.oracleMeas T hT).selfAdjoint p u
  have h2 : star (S.oracleOp T q v) = S.oracleOp T q v := by
    simpa using (S.oracleMeas T hT).selfAdjoint q v
  have := congrArg star h
  rwa [star_mul, h1, h2, star_zero] at this
end
end MIPRE.SeededGame

namespace MIPRE.SeededGame
section
open Finset Matrix
variable {V A : Type*} [Fintype V] [DecidableEq V] [Nonempty V] [Fintype A] [DecidableEq A]
variable (S : SeededGame V A)
variable {S}
variable (S)
variable {S}
/-- Check 2(b) for Alice: the oracle's first component against Alice's answer. -/
theorem oracleOp_oracle_mul_alice (T : SyncStrategy S.toGame.doubled) (hT : T.IsPCC) (z : V)
    {a a' : A} (b : A) (h : a ≠ a') :
    S.oracleOp T (.oracle, z) (.pair a b) * S.oracleOp T (.alice, S.LA z) (.single a') = 0 := by
  simp only [oracleOp_oracle_pair, oracleOp_alice_single]
  calc T.P.M (false, S.LA z) a * T.P.M (true, S.LB z) b * T.P.M (false, S.LA z) a'
      = T.P.M (false, S.LA z) a * (T.P.M (true, S.LB z) b * T.P.M (false, S.LA z) a') := by
        noncomm_ring
    _ = T.P.M (false, S.LA z) a * (T.P.M (false, S.LA z) a' * T.P.M (true, S.LB z) b) := by
        rw [← commute_of_isPCC hT z a' b]
    _ = T.P.M (false, S.LA z) a * T.P.M (false, S.LA z) a' * T.P.M (true, S.LB z) b := by
        noncomm_ring
    _ = 0 := by rw [T.orthogonal (false, S.LA z) h, Matrix.zero_mul]
end
end MIPRE.SeededGame

namespace MIPRE.SeededGame
section
open Finset Matrix
variable {V A : Type*} [Fintype V] [DecidableEq V] [Nonempty V] [Fintype A] [DecidableEq A]
variable (S : SeededGame V A)
variable {S}
variable (S)
variable {S}
/-- Check 2(b) for Bob: the oracle's second component against Bob's answer. -/
theorem oracleOp_oracle_mul_bob (T : SyncStrategy S.toGame.doubled) (z : V) (a : A)
    {b b' : A} (h : b ≠ b') :
    S.oracleOp T (.oracle, z) (.pair a b) * S.oracleOp T (.bob, S.LB z) (.single b') = 0 := by
  simp only [oracleOp_oracle_pair, oracleOp_bob_single]
  rw [Matrix.mul_assoc, T.orthogonal (true, S.LB z) h, Matrix.mul_zero]
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
    (hval : T.value = 1) {p q : Role × V} (hμ : 0 < S.oDist p q) {u v : OAns A}
    (hrej : S.oaccepts p q u v = false) :
    S.oracleOp T p u * S.oracleOp T q v = 0 := by
  simp only [oaccepts, Bool.and_eq_false_iff] at hrej
  rcases hrej with ((((((h | h) | h) | h) | h) | h) | h)
  · rw [oracleOp_eq_zero_of_shapeOk T h, Matrix.zero_mul]
  · rw [oracleOp_eq_zero_of_shapeOk T h, Matrix.mul_zero]
  · rw [oracleOp_eq_zero_of_gameCheck T hT hval h, Matrix.zero_mul]
  · rw [oracleOp_eq_zero_of_gameCheck T hT hval h, Matrix.mul_zero]
  · -- check 2(a): equal roles, unequal answers. On the support equal roles mean equal
    -- questions, so this is orthogonality of distinct outcomes.
    by_cases hpq : p.1 = q.1
    · have huv : u ≠ v := by simpa [hpq] using h
      have hp : p = q := eq_of_oDist_pos_of_fst_eq hμ hpq
      subst hp
      exact (S.oracleStrategy T hT).orthogonal p huv
    · simp [hpq] at h
  · -- check 2(b), the oracle first
    obtain ⟨r₁, r₂, z, hp, hq⟩ := exists_of_oDist_pos hμ
    subst hp; subst hq
    cases r₁ <;> cases r₂ <;> cases u <;> cases v <;>
      simp only [oquestion, oracleVsPlayer, Bool.true_eq_false, decide_eq_false_iff_not] at h ⊢
    · exact oracleOp_oracle_mul_alice T hT z _ h
    · exact oracleOp_oracle_mul_bob T z _ h
  · -- check 2(b), the isolated player first
    refine oracleOp_mul_eq_zero_of_swap T hT ?_
    obtain ⟨r₁, r₂, z, hp, hq⟩ := exists_of_oDist_pos hμ
    subst hp; subst hq
    cases r₁ <;> cases r₂ <;> cases u <;> cases v <;>
      simp only [oquestion, oracleVsPlayer, Bool.true_eq_false, decide_eq_false_iff_not] at h ⊢
    · exact oracleOp_oracle_mul_alice T hT z _ h
    · exact oracleOp_oracle_mul_bob T z _ h
end MIPRE.SeededGame
