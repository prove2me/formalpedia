-- Prove2me | solution 1 for MIPRE.SyncStrategy.value_le_copy
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:23:05.774985+00:00
-- url     : https://prove2.me/submissions/6f2a8c42-b4cc-482f-b781-866e29a05c49

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/GameTransportByQuestion.lean (solution of MIPRE.SyncStrategy.value_le_copy);
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

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.TracialState
section
open ComplexOrder Kronecker Matrix
open scoped MatrixOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {𝒜 ℬ : Type*} [Ring 𝒜] [StarRing 𝒜] [Module ℂ 𝒜]
  [Ring ℬ] [StarRing ℬ] [Module ℂ ℬ]
/-- The trace of a product of two projections is nonnegative:
`τ (p * q) = τ (star (q * p) * (q * p))`. This is the positivity of outcome
probabilities for the strategies below. -/
theorem nonneg_mul (τ : TracialState 𝒜) {p q : 𝒜} (hps : star p = p) (hpp : p * p = p)
    (hqs : star q = q) (hqq : q * q = q) : 0 ≤ τ (p * q) := by
  have key : star (q * p) * (q * p) = p * q * p := by
    rw [star_mul, hps, hqs, mul_assoc p q (q * p), ← mul_assoc q q p, hqq, ← mul_assoc]
  calc (0 : ℂ) ≤ τ (star (q * p) * (q * p)) := τ.star_mul_self_nonneg _
    _ = τ (p * q * p) := by rw [key]
    _ = τ (p * q) := by rw [τ.map_mul_comm (p * q) p, ← mul_assoc, hpp]
end
end MIPRE.TracialState

namespace MIPRE.TracialState
section
open ComplexOrder Kronecker Matrix
open scoped MatrixOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {𝒜 ℬ : Type*} [Ring 𝒜] [StarRing 𝒜] [Module ℂ 𝒜]
  [Ring ℬ] [StarRing ℬ] [Module ℂ ℬ]
/-- Real-part form of `TracialState.nonneg_mul`. -/
theorem re_nonneg_mul (τ : TracialState 𝒜) {p q : 𝒜} (hps : star p = p) (hpp : p * p = p)
    (hqs : star q = q) (hqq : q * q = q) : 0 ≤ (τ (p * q)).re := by
  simpa using (Complex.le_def.mp (τ.nonneg_mul hps hpp hqs hqq)).1
end
end MIPRE.TracialState

attribute [instance] MIPRE.CommutingStrategy.cstarAlgebra

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
open Finset
open scoped ComplexOrder
variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
variable {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Module ℂ 𝒜]
omit [Fintype X] [DecidableEq A] in
/-- The outcome probabilities are nonnegative. -/
theorem re_nonneg_tracial (τ : TracialState 𝒜) (P : ProjectiveMeasurement X A 𝒜)
    (x y : X) (a b : A) : 0 ≤ (τ (P.M x a * P.M y b)).re :=
  τ.re_nonneg_mul (P.selfAdjoint x a) (P.projective x a) (P.selfAdjoint y b) (P.projective y b)
end
end MIPRE

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
theorem normalizedTrace_re_eq_ntr (S : SyncStrategy G) (M : Matrix (Fin S.d) (Fin S.d) ℂ) :
    ((normalizedTrace (Fin S.d) (hn := Fin.pos_iff_nonempty.mp S.d_pos)) M).re = ntr M := by
  rw [normalizedTrace_re, ntr_fin]
end
end MIPRE.SyncStrategy

namespace MIPRE.SyncStrategy
section
open Finset
open scoped ComplexOrder
variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
variable {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Module ℂ 𝒜]
variable {G : SynchronousGame X A}
/-- Outcome probabilities are nonnegative. -/
theorem ntr_mul_nonneg (S : SyncStrategy G) (x y : X) (a b : A) :
    0 ≤ ntr (S.P.M x a * S.P.M y b) := by
  rw [← normalizedTrace_re_eq_ntr]
  exact re_nonneg_tracial _ S.P x y a b
end
end MIPRE.SyncStrategy

namespace MIPRE.SyncStrategy
section
open Finset
open scoped ComplexOrder
variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
variable {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Module ℂ 𝒜]
variable {G : SynchronousGame X A}
theorem value_eq_ntr (S : SyncStrategy G) :
    S.value = ∑ x, ∑ y, ∑ a, ∑ b, G.μ x y * (if G.D x y a b then 1 else 0) *
      ntr (S.P.M x a * S.P.M y b) := by
  rw [value_eq]
  simp only [ntr_fin]
end
end MIPRE.SyncStrategy

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.SyncStrategy
open Matrix Kronecker Finset Classical
variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
  {G : SynchronousGame X A}
theorem _root_.solution (S : SyncStrategy G) (G' : SynchronousGame X A)
    (hμ : ∀ x y, G'.μ x y = G.μ x y)
    (hD : ∀ x y a b, G.D x y a b = true → G'.D x y a b = true) :
    S.value ≤ (S.copy G').value := by
  rw [value_eq_ntr, value_eq_ntr]
  change (∑ x, ∑ y, ∑ a, ∑ b, G.μ x y * (if G.D x y a b then 1 else 0) *
      ntr (S.P.M x a * S.P.M y b)) ≤
    ∑ x, ∑ y, ∑ a, ∑ b, G'.μ x y * (if G'.D x y a b then 1 else 0) *
      ntr (S.P.M x a * S.P.M y b)
  refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
    Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
  rw [hμ]
  apply mul_le_mul_of_nonneg_right _ (S.ntr_mul_nonneg x y a b)
  apply mul_le_mul_of_nonneg_left _ (G.μ_nonneg x y)
  cases h : G.D x y a b with
  | false => cases G'.D x y a b <;> norm_num
  | true => rw [hD x y a b h]
end MIPRE.SyncStrategy
