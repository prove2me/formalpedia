-- Prove2me | solution 1 for MIPRE.exists_perfectPCC_repeat_doubled
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:50:26.337033+00:00
-- url     : https://prove2.me/submissions/788d6f31-2413-40e6-b81d-c0bca35bf523

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Repetition/TensorPower.lean (solution of MIPRE.exists_perfectPCC_repeat_doubled);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Background_Repetition_Direct
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_TensorFamily
import Definitions.Def_MIPRE_Background_Repetition_TensorPower
import Theorems.Thm_MIPRE_SyncStrategy_isPCC_tensorPow
import Theorems.Thm_MIPRE_sum_pi_prod

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

attribute [instance] MIPRE.CommutingStrategy.cstarAlgebra

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

namespace MIPRE.SyncStrategy
section
open Matrix Kronecker
open scoped ComplexOrder
variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
variable {G : SynchronousGame X A}
/-- The support-restricted `SyncStrategy.isPCC_relabel`: the commutation condition is
quantified over the support of `μ`, so a relabeling that only shrinks the support transports
it. `isPCC_relabel` is the case of a total `hμ`. Not used by the doubling — whose relabelings
are total — and kept because it is the general statement. -/
theorem isPCC_relabel_of_support {X' A' : Type*} [Fintype X'] [Fintype A'] [DecidableEq A']
    {S : SyncStrategy G} (hS : S.IsPCC) (G' : SynchronousGame X' A') (eX : X' → X)
    (eA : A' ≃ A) (hμ : ∀ x' y', 0 < G'.μ x' y' → 0 < G.μ (eX x') (eX y')) :
    (S.relabel G' eX eA).IsPCC :=
  fun x' y' hxy _ _ => hS _ _ (hμ x' y' hxy) _ _
end
end MIPRE.SyncStrategy

namespace MIPRE
section
open Matrix
variable {k : ℕ} {ι : Type*}
theorem tensorFamily_mul [Fintype ι] (M N : Fin k → Matrix ι ι ℂ) :
    tensorFamily M * tensorFamily N = tensorFamily fun i => M i * N i := by
  ext v w
  simp only [Matrix.mul_apply, tensorFamily_apply]
  rw [Fintype.prod_sum]
  exact Finset.sum_congr rfl fun x _ => (Finset.prod_mul_distrib).symm
end
end MIPRE

namespace MIPRE
section
open Matrix
variable {k : ℕ} {ι : Type*}
theorem trace_tensorFamily [Fintype ι] (M : Fin k → Matrix ι ι ℂ) :
    (tensorFamily M).trace = ∏ i, (M i).trace := by
  simp only [Matrix.trace, Matrix.diag, tensorFamily_apply]
  rw [Fintype.prod_sum]
end
end MIPRE

namespace MIPRE
section
open Matrix
variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
/-- The trace is invariant under reindexing along an equivalence. -/
theorem trace_submatrix_equiv {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (M : Matrix ι ι ℂ) : (M.submatrix e.symm e.symm).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  exact Equiv.sum_comp e.symm fun i => M i i
end
end MIPRE

namespace MIPRE.ProjectiveMeasurement
section
open Matrix
variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
omit [Fintype X] [DecidableEq A] in
theorem reindexMat_trace_mul {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    [DecidableEq κ] (e : ι ≃ κ) (P : ProjectiveMeasurement X A (Matrix ι ι ℂ)) (x y : X)
    (a b : A) :
    ((P.reindexMat e).M x a * (P.reindexMat e).M y b).trace = (P.M x a * P.M y b).trace := by
  rw [reindexMat_M, reindexMat_M, Matrix.submatrix_mul_equiv, trace_submatrix_equiv]
end
end MIPRE.ProjectiveMeasurement

namespace MIPRE
section
open Matrix
variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
/-- For self-adjoint idempotents `P`, `Q` on `ℂ^d` (`d > 0`), `Tr(PQ)` is real. -/
theorem trace_mul_im_eq_zero {d : ℕ} (hd : 0 < d) {P Q : Matrix (Fin d) (Fin d) ℂ}
    (hP : star P = P) (hPP : P * P = P) (hQ : star Q = Q) (hQQ : Q * Q = Q) :
    (P * Q).trace.im = 0 := by
  have : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  have h := (normalizedTrace (Fin d)).nonneg_mul hP hPP hQ hQQ
  rw [normalizedTrace_apply, Complex.le_def] at h
  have him := h.2
  rw [Complex.zero_im, Complex.mul_im, Fintype.card_fin] at him
  have h1 : ((d : ℂ)⁻¹).im = 0 := by simp
  have h2 : ((d : ℂ)⁻¹).re = (d : ℝ)⁻¹ := by simp
  rw [h1, h2, zero_mul, add_zero] at him
  have hd' : (d : ℝ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast hd.ne')
  exact (mul_eq_zero.1 him.symm).resolve_left hd'
end
end MIPRE

namespace MIPRE
section
open Matrix
variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
/-- The normalized trace of a tensor product of pairs of projections is the product of the
normalized traces, in real parts. -/
theorem re_trace_tensorFamily_div {d k : ℕ} (hd : 0 < d)
    (P Q : Fin k → Matrix (Fin d) (Fin d) ℂ)
    (hP : ∀ i, star (P i) = P i) (hPP : ∀ i, P i * P i = P i)
    (hQ : ∀ i, star (Q i) = Q i) (hQQ : ∀ i, Q i * Q i = Q i) :
    (tensorFamily P * tensorFamily Q).trace.re / ((d ^ k : ℕ) : ℝ) =
      ∏ i, (P i * Q i).trace.re / (d : ℝ) := by
  rw [tensorFamily_mul, trace_tensorFamily]
  have hreal : ∀ i, (P i * Q i).trace = (((P i * Q i).trace.re : ℝ) : ℂ) := fun i =>
    Complex.ext (by simp) (by simp [trace_mul_im_eq_zero hd (hP i) (hPP i) (hQ i) (hQQ i)])
  rw [Finset.prod_congr rfl fun i _ => hreal i, ← Complex.ofReal_prod, Complex.ofReal_re,
    Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  push_cast
  rfl
end
end MIPRE

namespace MIPRE.SyncStrategy
section
open Matrix
variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
variable {G : Game X X A A}
theorem value_tensorPowDoubled (S : SyncStrategy G.doubled) (k : ℕ) :
    (S.tensorPowDoubled k).value = S.value ^ k := by
  rw [value_eq, value_eq]
  rw [show (∑ p, ∑ q, ∑ a, ∑ b, (G.repeat k).doubled.μ p q *
      (if (G.repeat k).doubled.D p q a b then (1 : ℝ) else 0) *
      (((S.tensorPowDoubled k).P.M p a * (S.tensorPowDoubled k).P.M q b).trace.re /
        ((S.tensorPowDoubled k).d : ℝ))) = _ from Game.sum_doubled (G.repeat k) _]
  rw [show (∑ p, ∑ q, ∑ a, ∑ b, G.doubled.μ p q * (if G.doubled.D p q a b then (1 : ℝ) else 0) *
      ((S.P.M p a * S.P.M q b).trace.re / (S.d : ℝ))) = _ from Game.sum_doubled G _]
  rw [← sum_pi_prod]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  -- the summand of the doubled repeated game against the relabeled tensor power
  have htr : (((S.tensorPowDoubled k).P.M (false, x) a * (S.tensorPowDoubled k).P.M (true, y) b).trace.re /
      ((S.tensorPowDoubled k).d : ℝ)) =
      ∏ i, (S.P.M (false, x i) (a i) * S.P.M (true, y i) (b i)).trace.re / (S.d : ℝ) := by
    change (((S.P.tensorPow k).reindexMat (equivFinPow S.d k)).M (fun i => (false, x i)) a *
      ((S.P.tensorPow k).reindexMat (equivFinPow S.d k)).M (fun i => (true, y i)) b).trace.re /
        ((S.d ^ k : ℕ) : ℝ) = _
    rw [ProjectiveMeasurement.reindexMat_trace_mul, ProjectiveMeasurement.tensorPow_M,
      ProjectiveMeasurement.tensorPow_M]
    exact re_trace_tensorFamily_div S.d_pos _ _ (fun i => S.P.selfAdjoint _ _)
      (fun i => S.P.projective _ _) (fun i => S.P.selfAdjoint _ _) (fun i => S.P.projective _ _)
  rw [htr]
  have hμ : (G.repeat k).μ x y = ∏ i, G.μ (x i) (y i) := rfl
  have hD : (if (G.repeat k).D x y a b then (1 : ℝ) else 0) =
      ∏ i, if G.D (x i) (y i) (a i) (b i) then (1 : ℝ) else 0 := by
    show (if decide (∀ i, G.D (x i) (y i) (a i) (b i) = true) = true then (1 : ℝ) else 0) = _
    rw [Finset.prod_boole]
    simp
  rw [hμ, hD, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
end
end MIPRE.SyncStrategy

namespace MIPRE.SyncStrategy
section
open Matrix
variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
variable {G : Game X X A A}
theorem isPCC_tensorPowDoubled {S : SyncStrategy G.doubled} (hS : S.IsPCC) (k : ℕ) :
    (S.tensorPowDoubled k).IsPCC := by
  refine isPCC_relabel_of_support (isPCC_tensorPow hS k) _ _ _ fun p q hpq => ?_
  rw [Game.doubled_μ] at hpq
  split_ifs at hpq with h
  · show 0 < ∏ i, G.doubled.μ (p.1, p.2 i) (q.1, q.2 i)
    have : ∀ i, G.doubled.μ (p.1, p.2 i) (q.1, q.2 i) = G.μ (p.2 i) (q.2 i) := fun i => by
      simp [Game.doubled_μ, h.1, h.2]
    simp only [this]
    exact hpq
  · exact absurd hpq (lt_irrefl 0)
end
end MIPRE.SyncStrategy

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Matrix
variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
theorem _root_.solution {G : Game X X A A} (k : ℕ)
    (h : ∃ S : SyncStrategy G.doubled, S.IsPCC ∧ S.value = 1) :
    ∃ S' : SyncStrategy (G.repeat k).doubled, S'.IsPCC ∧ S'.value = 1 := by
  obtain ⟨S, hS, hv⟩ := h
  exact ⟨S.tensorPowDoubled k, SyncStrategy.isPCC_tensorPowDoubled hS k, by
    rw [SyncStrategy.value_tensorPowDoubled, hv, one_pow]⟩
end MIPRE
