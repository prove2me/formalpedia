-- Prove2me | solution 1 for KernelRank.exists_rank_le_two_mul_tendstoUniformlyOn_radial_sq_mul_cos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:48:04.810327+00:00
-- url     : https://prove2.me/submissions/197d0cff-6dff-429a-bd0c-5ec27c493bf7

import Definitions.Def_KernelRankLean_Necessity
import Definitions.Def_KernelRankLean_MultiComplexRank
import Definitions.Def_KernelRankLean_MultiRealRank
import Definitions.Def_KernelRankLean_Main
import Theorems.Thm_KernelRank_exists_rank_le_borderTotalCost_tendstoUniformlyOn_radial_profile
import Theorems.Thm_KernelRank_expPoly_zero
import Theorems.Thm_KernelRank_fin2Vec_one
import Theorems.Thm_KernelRank_fin2Vec_zero
import Theorems.Thm_KernelRank_singleCoeff_same
attribute [local simp] KernelRank.expPoly_zero
attribute [local simp] KernelRank.fin2Vec_one
attribute [local simp] KernelRank.fin2Vec_zero
attribute [local simp] KernelRank.singleCoeff_same


section
open Complex Polynomial Filter Topology
namespace KernelRank
private lemma re_ofReal_mul_exp_I_mul (r s : ℝ) :
    (((r : ℂ) * exp (I * (s : ℂ))).re) = r * Real.cos s := by
  rw [mul_comm I (s : ℂ), exp_mul_I]
  simp [mul_add, Complex.cos_ofReal_re]
end KernelRank
end

set_option autoImplicit true
open Complex Polynomial Filter Topology
open KernelRank
namespace KernelRank
theorem _root_.solution {d : ℕ} (hd : 2 ≤ d) :
    ∃ F : ℝ → (Fin d → ℝ) → ℝ,
      (∀ h, separableRank (F h) ≤ (2 * d : ℕ)) ∧
      ∀ C : Set (Fin d → ℝ), IsCompact C →
        TendstoUniformlyOn F (fun x => (∑ j, x j ^ 2) * Real.cos (∑ j, x j ^ 2))
          (𝓝[≠] (0 : ℝ)) C := by
  let c : Component := ⟨I, Polynomial.X⟩
  have hwf : ∀ c' ∈ ([c] : List Component), c'.WellFormed := by
    simp only [List.mem_singleton, forall_eq]
    exact ⟨Polynomial.X_ne_zero, by simp [c], fun h => by simp [c] at h⟩
  obtain ⟨F, hrank, htend⟩ :=
    exists_rank_le_borderTotalCost_tendstoUniformlyOn_radial_profile hd [c] hwf
  have hcost : borderTotalCost d [c] = 2 * d := by
    have : c.rate.im ≠ 0 := by simp [c]
    simp only [borderTotalCost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      Component.borderCost, this, ↓reduceIte, c, Polynomial.natDegree_X]
    ring
  have hfun : (fun x : Fin d → ℝ => profile [c] (∑ j, x j ^ 2)) =
      fun x => (∑ j, x j ^ 2) * Real.cos (∑ j, x j ^ 2) := by
    funext x
    simp only [profile, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      Component.eval, c, Polynomial.eval_X]
    exact re_ofReal_mul_exp_I_mul _ _
  rw [hcost] at hrank
  rw [hfun] at htend
  exact ⟨F, hrank, htend⟩
end KernelRank
