-- Prove2me | solution 1 for OAI.PermanentBorder.PolarAnalysis.Schur.solved_left
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:45:17.620521+00:00
-- url     : https://prove2.me/submissions/7ece153e-7bf5-4fb3-aa9d-68c5298772f2

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/KernelCharts.lean:L416-L431
-- (upload_full_project.md Phase 4): solution for node OAI.PermanentBorder.PolarAnalysis.Schur.solved_left. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Definitions.Def_OAI_Algebra_Determinantal_LinearForms
import Definitions.Def_OAI_Algebra_Determinantal_PointBounds
import Definitions.Def_OAI_Algebra_Determinantal_ProjectiveCounts
import Definitions.Def_OAI_Algebra_Determinantal_KernelCharts

-- ---- from OAI.Algebra.Determinantal.KernelCharts ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace PermanentBorder.Multigraded
open MvPolynomial
open scoped Classical

section Reindex
variable {ι σ E L V : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ]
  [Fintype E] [Fintype L] [DecidableEq L]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

end Reindex
end PermanentBorder.Multigraded

namespace PermanentBorder.KernelBilinear
open MvPolynomial
open scoped Classical

variable {κ : Type} [Fintype κ] {n : ℕ}

end PermanentBorder.KernelBilinear

namespace PermanentBorder.Multigraded
open MvPolynomial
open scoped Classical
variable {σ : Type*} [DecidableEq σ]
end PermanentBorder.Multigraded

namespace PermanentBorder.KernelBilinear
open MvPolynomial
open scoped Classical
variable {κ : Type} [Fintype κ] {n : ℕ}
end PermanentBorder.KernelBilinear

namespace PermanentBorder.PolarAnalysis
open Filter
open scoped Topology

section Elimination
variable {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]

end Elimination
end PermanentBorder.PolarAnalysis

namespace PermanentBorder.PolarAnalysis.Schur
open Matrix
open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

 theorem solved_left (a : ℂ) (β γ : ι → ℂ) (E : Matrix ι ι ℂ) (hE : E.det ≠ 0) :
    normalized (left β E) ᵥ* block a β γ E =
      Sum.elim (fun _ => scalar a β γ E) (fun _ => 0) := by
  have hu : IsUnit E.det := isUnit_iff_ne_zero.mpr hE
  simp only [block, normalized, vecMul_fromBlocks, left, Sum.elim_comp_inl, Sum.elim_comp_inr]
  have hh : -(β ᵥ* E⁻¹) ᵥ* E = -β := by
    rw [neg_vecMul, vecMul_vecMul, nonsing_inv_mul E hu, vecMul_one]
  rw [hh]
  ext j
  cases j with
  | inl u =>
    simp only [Sum.elim_inl, Pi.add_apply, vecMul, dotProduct, Matrix.of_apply,
      Fintype.sum_unique, one_mul, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib,
      scalar, mulVec, Finset.sum_mul, Finset.mul_sum, mul_assoc, sub_eq_add_neg]
    rw [Finset.sum_comm]
  | inr j => simp [vecMul, dotProduct]

section Calculus
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

end Calculus
end PermanentBorder.PolarAnalysis.Schur

end OAI

-- ---- platform node ----
open OAI OAI.PermanentBorder OAI.PermanentBorder.PolarAnalysis OAI.PermanentBorder.PolarAnalysis.Schur
open Matrix
open scoped Matrix


theorem solution : type_of% @_root_.OAI.PermanentBorder.PolarAnalysis.Schur.solved_left := @_root_.OAI.PermanentBorder.PolarAnalysis.Schur.solved_left
