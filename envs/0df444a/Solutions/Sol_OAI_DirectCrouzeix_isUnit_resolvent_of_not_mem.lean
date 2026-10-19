-- Prove2me | solution 1 for OAI.DirectCrouzeix.isUnit_resolvent_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:44:08.495994+00:00
-- url     : https://prove2.me/submissions/3d4358a4-8bbf-477b-a0c3-f15752c479dd

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/Resolvent.lean:L130-L142
-- (upload_full_project.md Phase 4): solution for node OAI.DirectCrouzeix.isUnit_resolvent_of_not_mem. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DirectCrouzeix
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PositiveBlocks
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Resolvent

-- ---- from OAI.Analysis.DirectCrouzeix.Resolvent ----
namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

theorem mem_numericalRange_of_eigenvector {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    {z : ℂ} {x : Fin n → ℂ} (hx : x ≠ 0) (he : A *ᵥ x = z • x) :
    z ∈ numericalRange A := by
  let v : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 x
  have hv : v ≠ 0 := by simpa [v] using hx
  have he' : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A v = z • v := by
    simpa [v, Matrix.toEuclideanCLM_toLp] using congrArg (WithLp.toLp 2) he
  let u : EuclideanSpace ℂ (Fin n) := (‖v‖ : ℂ)⁻¹ • v
  have hu : ‖u‖ = 1 := norm_smul_inv_norm hv
  have heu : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A u = z • u := by
    simp [u, he', smul_smul, mul_comm]
  refine ⟨u, hu, ?_⟩
  rw [heu, inner_smul_right, inner_self_eq_norm_sq_to_K, hu]
  simp

theorem isUnit_resolvent_of_not_mem {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    {z : ℂ} (hz : z ∉ numericalRange A) : IsUnit (z • 1 - A) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y hxy
  by_contra hh
  have hv : x - y ≠ 0 := sub_ne_zero.mpr hh
  have hzero : (z • 1 - A) *ᵥ (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hxy, sub_self]
  have he : A *ᵥ (x - y) = z • (x - y) := by
    symm
    apply sub_eq_zero.mp
    simpa only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] using hzero
  exact hz (mem_numericalRange_of_eigenvector A hv he)

end DirectCrouzeix

end

end OAI

-- ---- platform node ----
open OAI OAI.DirectCrouzeix
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open scoped MatrixOrder ComplexOrder


theorem solution : type_of% @_root_.OAI.DirectCrouzeix.isUnit_resolvent_of_not_mem := @_root_.OAI.DirectCrouzeix.isUnit_resolvent_of_not_mem
