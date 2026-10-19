-- Prove2me | solution 1 for MIPRE.SyncStrategy.perfect_mergeAnswersByQuestion
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:47:39.828462+00:00
-- url     : https://prove2.me/submissions/fcbb5222-f602-47d5-9c33-fa0e3a5472b6

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SyncMergeByQuestion.lean (solution of MIPRE.SyncStrategy.perfect_mergeAnswersByQuestion);
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
import Definitions.Def_MIPRE_Foundations_GameTransportByQuestion
import Definitions.Def_MIPRE_Foundations_SyncMergeByQuestion
import Theorems.Thm_MIPRE_re_eq_zero_of_tracialValue_eq_one
import Theorems.Thm_MIPRE_tracialValue_eq_one_of_re_eq_zero

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
section
open Finset ComplexOrder Matrix
variable {n : Type*} [Fintype n]
theorem ntr_fin (d : ℕ) (M : Matrix (Fin d) (Fin d) ℂ) : ntr M = M.trace.re / (d : ℝ) := by
  rw [ntr, Fintype.card_fin]
end
end MIPRE

namespace MIPRE
section
open Finset ComplexOrder Matrix
variable {n : Type*} [Fintype n]
theorem ntr_sum {ι : Type*} (s : Finset ι) (f : ι → Matrix n n ℂ) :
    ntr (∑ i ∈ s, f i) = ∑ i ∈ s, ntr (f i) := by
  simp [ntr, Matrix.trace_sum, Complex.re_sum, Finset.sum_div]
end
end MIPRE

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
theorem normalizedTrace_re_eq_ntr (S : SyncStrategy G) (M : Matrix (Fin S.d) (Fin S.d) ℂ) :
    ((normalizedTrace (Fin S.d) (hn := Fin.pos_iff_nonempty.mp S.d_pos)) M).re = ntr M := by
  rw [normalizedTrace_re, ntr_fin]
end
end MIPRE.SyncStrategy

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.SyncStrategy
open Matrix Finset Classical
variable {X A B : Type*} [Fintype X] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] {G : SynchronousGame X A}
theorem _root_.solution (S : SyncStrategy G) (H : SynchronousGame X B)
    (f : X → A → B) (hμ : ∀ x y, H.μ x y = G.μ x y)
    (hD : ∀ x y a b, 0 < G.μ x y → S.P.M x a ≠ 0 → S.P.M y b ≠ 0 →
      G.D x y a b = true → H.D x y (f x a) (f y b) = true)
    (hv : S.value = 1) : (S.mergeAnswersByQuestion H f).value = 1 := by
  rw [value_eq_tracialValue]
  apply tracialValue_eq_one_of_re_eq_zero
  intro x y hxy a b hr
  rw [hμ] at hxy
  change ((normalizedTrace (Fin S.d) (hn := Fin.pos_iff_nonempty.mp S.d_pos))
    ((S.P.mergeByQuestion f).M x a * (S.P.mergeByQuestion f).M y b)).re = 0
  rw [S.normalizedTrace_re_eq_ntr]
  simp only [ProjectiveMeasurement.mergeByQuestion_M, Finset.sum_mul, Finset.mul_sum, ntr_sum]
  apply Finset.sum_eq_zero
  intro v hv'
  apply Finset.sum_eq_zero
  intro u hu
  by_cases hu0 : S.P.M x u = 0
  · simp [hu0]
  by_cases hv0 : S.P.M y v = 0
  · simp [hv0]
  have hd : G.D x y u v = false := by
    cases hd : G.D x y u v with
    | false => rfl
    | true =>
      have hh := hD x y u v hxy hu0 hv0 hd
      rw [(mem_filter.mp hu).2,(mem_filter.mp hv').2,hr] at hh
      cases hh
  rw [ntr_fin]
  exact S.re_eq_zero_of_value_eq_one hv hxy hd
end MIPRE.SyncStrategy
