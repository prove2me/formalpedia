-- Prove2me | solution 1 for OAI.GAD.trace_square_re_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:18:39.446387+00:00
-- url     : https://prove2.me/submissions/f906dbb8-ac09-418a-b280-22a9ec132d76

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/MatrixDifferentiation.lean:L147-L166
-- (upload_full_project.md Phase 4): solution for node OAI.GAD.trace_square_re_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation

-- ---- from OAI.InformationTheory.AmplitudeDamping.MatrixDifferentiation ----
namespace OAI

universe u_1 u_2

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise
open Matrix
namespace GAD

variable {ι : Type u_1} [Fintype ι] [DecidableEq ι]

end GAD

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_2} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Entrywise real trace bound, avoiding any norm convention for matrices. -/
theorem trace_square_re_le (B : Matrix ι ι ℂ) :
    (Matrix.trace (B * B)).re ≤ (Matrix.trace (B.conjTranspose * B)).re := by
  have he (z w : ℂ) : 2 * (z * w).re ≤ Complex.normSq z + Complex.normSq w := by
    simp only [Complex.mul_re, Complex.normSq_apply]
    nlinarith [sq_nonneg (z.re - w.re), sq_nonneg (z.im + w.im)]
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦
    Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ he (B i j) (B j i)))
  have hs : (∑ i, ∑ j, Complex.normSq (B i j)) =
      ∑ i, ∑ j, Complex.normSq (B j i) := Finset.sum_comm
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hh
  rw [hs] at hh
  have hb : (Matrix.trace (B.conjTranspose * B)).re =
      ∑ i, ∑ j, Complex.normSq (B j i) := by
    simp [Matrix.trace, Matrix.mul_apply, Complex.normSq_apply,
      Complex.mul_re, Matrix.conjTranspose_apply, RCLike.star_def]
  rw [hb]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Complex.re_sum]
  linarith

end GAD

end

end OAI

-- ---- platform node ----
open OAI OAI.GAD
open scoped BigOperators
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix


theorem solution : type_of% @_root_.OAI.GAD.trace_square_re_le := @_root_.OAI.GAD.trace_square_re_le
