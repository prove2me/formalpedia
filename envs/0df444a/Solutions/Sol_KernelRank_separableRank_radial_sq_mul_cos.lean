-- Prove2me | solution 1 for KernelRank.separableRank_radial_sq_mul_cos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:51:38.242654+00:00
-- url     : https://prove2.me/submissions/98b84bb2-b71e-4214-aaba-59897d05f263

import Definitions.Def_KernelRankLean_Necessity
import Definitions.Def_KernelRankLean_MultiComplexRank
import Definitions.Def_KernelRankLean_MultiRealRank
import Definitions.Def_KernelRankLean_Main
import Theorems.Thm_KernelRank_expPoly_zero
import Theorems.Thm_KernelRank_fin2Vec_one
import Theorems.Thm_KernelRank_fin2Vec_zero
import Theorems.Thm_KernelRank_separableRank_radial_profile
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
    separableRank (fun x : Fin d → ℝ => (∑ j, x j ^ 2) * Real.cos (∑ j, x j ^ 2)) =
      (3 * d - 2 : ℕ) := by
  let c : Component := ⟨I, Polynomial.X⟩
  have hwf : IsRepresentation [c] := by
    refine ⟨?_, List.nodup_singleton _⟩
    simp only [List.mem_singleton, forall_eq]
    refine ⟨Polynomial.X_ne_zero, by simp [c], fun h => by simp [c] at h⟩
  have heval (s : ℝ) : s * Real.cos s = profile [c] s := by
    simp only [profile, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      Component.eval, c, Polynomial.eval_X]
    exact (re_ofReal_mul_exp_I_mul s s).symm
  have hfun : (fun x : Fin d → ℝ => (∑ j, x j ^ 2) * Real.cos (∑ j, x j ^ 2)) =
      fun x => profile [c] (∑ j, x j ^ 2) := funext fun x => heval _
  rw [hfun, separableRank_radial_profile hd hwf]
  have hcost : multiTotalCost d [c] = 3 * d - 2 := by
    have : c.rate.im ≠ 0 := by simp [c]
    simp only [multiTotalCost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      Component.multiCost, this, ↓reduceIte, c, Polynomial.natDegree_X]
    omega
  rw [hcost]
end KernelRank
