-- Prove2me | solution 1 for OAI.DirectCrouzeix.exists_singular_pair
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:48:22.91333+00:00
-- url     : https://prove2.me/submissions/b4197e7b-ec9e-48a2-b120-936ba10a099c

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/SingularPairs.lean:L51-L78
-- (upload_full_project.md Phase 4): solution for node OAI.DirectCrouzeix.exists_singular_pair. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DirectCrouzeix
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PositiveBlocks
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Resolvent
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialCalculus
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HilbertSchmidt
import Definitions.Def_OAI_Analysis_DirectCrouzeix_SingularPairs

-- ---- from OAI.Analysis.DirectCrouzeix.SingularPairs ----
namespace OAI

universe u_37 u_38 u_39 u_40

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

theorem exists_norm_attainer {ι : Type u_37} [Fintype ι] [Nonempty ι]
    (T : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :
    ∃ x : EuclideanSpace ℂ ι, ‖x‖ = 1 ∧ ‖T x‖ = ‖T‖ := by
  obtain ⟨x, hx, hmax⟩ := (isCompact_sphere (0 : EuclideanSpace ℂ ι) 1).exists_isMaxOn
    (NormedSpace.sphere_nonempty.mpr (by norm_num : (0 : ℝ) ≤ 1))
    T.continuous.norm.continuousOn
  have hx' : ‖x‖ = 1 := by simpa using hx
  refine ⟨x, hx', le_antisymm ?_ ?_⟩
  · simpa [hx'] using T.le_opNorm x
  · apply T.opNorm_le_bound (norm_nonneg _)
    intro v
    by_cases hv : v = 0
    · simp [hv]
    let u : EuclideanSpace ℂ ι := (‖v‖ : ℂ)⁻¹ • v
    have hu : ‖u‖ = 1 := norm_smul_inv_norm hv
    have hm : ‖T u‖ ≤ ‖T x‖ := hmax (by simpa using hu)
    have he : ‖T u‖ = ‖T v‖ / ‖v‖ := by
      simp [u, norm_smul, div_eq_mul_inv, mul_comm]
    rw [he] at hm
    exact (div_le_iff₀ (norm_pos_iff.mpr hv)).mp hm

theorem exists_singular_pair {ι : Type u_38} [Fintype ι] [Nonempty ι]
    (T : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) (hT : 0 < ‖T‖) :
    ∃ x y : EuclideanSpace ℂ ι, ‖x‖ = 1 ∧ ‖y‖ = 1 ∧
      T x = (‖T‖ : ℂ) • y ∧
      ContinuousLinearMap.adjoint T y = (‖T‖ : ℂ) • x := by
  obtain ⟨x, hx, hTx⟩ := exists_norm_attainer T
  let y : EuclideanSpace ℂ ι := (‖T‖ : ℂ)⁻¹ • T x
  have hn : (‖T‖ : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  have hy : ‖y‖ = 1 := by
    simp [y, norm_smul, hTx, ne_of_gt hT]
  have hxy : T x = (‖T‖ : ℂ) • y := by simp [y, smul_smul, hn]
  refine ⟨x, y, hx, hy, hxy, ?_⟩
  have ha : ‖ContinuousLinearMap.adjoint T y‖ ≤ ‖T‖ := by
    simpa [hy] using (ContinuousLinearMap.adjoint T).le_opNorm y
  have hi : inner ℂ (ContinuousLinearMap.adjoint T y) x = (‖T‖ : ℂ) := by
    rw [ContinuousLinearMap.adjoint_inner_left, hxy, inner_smul_right,
      inner_self_eq_norm_sq_to_K, hy]
    simp
  have hd : ‖ContinuousLinearMap.adjoint T y - (‖T‖ : ℂ) • x‖ ^ 2 =
      ‖ContinuousLinearMap.adjoint T y‖ ^ 2 - ‖T‖ ^ 2 := by
    rw [norm_sub_sq (𝕜 := ℂ), inner_smul_right, hi]
    simp [norm_smul, hx]
    ring
  have he : ‖ContinuousLinearMap.adjoint T y - (‖T‖ : ℂ) • x‖ = 0 := by
    have hs := pow_le_pow_left₀ (norm_nonneg _) ha 2
    nlinarith [sq_nonneg ‖ContinuousLinearMap.adjoint T y - (‖T‖ : ℂ) • x‖,
      norm_nonneg (ContinuousLinearMap.adjoint T y - (‖T‖ : ℂ) • x)]
  exact sub_eq_zero.mp (norm_eq_zero.mp he)

end DirectCrouzeix

end

end OAI

-- ---- platform node ----
open OAI OAI.DirectCrouzeix
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open scoped MatrixOrder ComplexOrder


theorem solution : type_of% @_root_.OAI.DirectCrouzeix.exists_singular_pair := @_root_.OAI.DirectCrouzeix.exists_singular_pair
