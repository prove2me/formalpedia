-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.wtProj_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:15:30.319689+00:00
-- url     : https://prove2.me/submissions/d2d2122e-3f1a-4021-a69a-bf1f15fe2e30

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RepBase
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_FischerForm
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Fischer
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_coeff_wtProj
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_wtProj_wtProj
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_rowOp_self_of_wtProj
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_wtProj_eq_self_of_eigen
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_sum_wtProj
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_fischer_zero_left
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_fischer_zero_right
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HarishChandra.fischer_zero_left
attribute [local simp] GroundTheory.Automorphic.HarishChandra.fischer_zero_right



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
open MvPolynomial
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution {T : Module.End ℂ (Poly n)} (hT : ∀ a, T * rowOp a a = rowOp a a * T)
    (μ : Fin n → ℕ) (f : Poly n) : wtProj μ (T f) = T (wtProj μ f) := by
  classical
  have hν : ∀ ν, wtProj ν (T (wtProj ν f)) = T (wtProj ν f) := fun ν =>
    wtProj_eq_self_of_eigen ν fun a => by
      have h1 := congrArg (fun S : Module.End ℂ (Poly n) => S (wtProj ν f)) (hT a)
      simp only [Module.End.mul_apply] at h1
      rw [← h1, rowOp_self_of_wtProj ν _ a (by rw [wtProj_wtProj, if_pos rfl]), map_smul]
  conv_lhs => rw [← sum_wtProj f, map_sum, map_sum]
  rw [Finset.sum_eq_single μ]
  · exact hν μ
  · intro ν _ hne
    rw [← hν ν, wtProj_wtProj, if_neg (Ne.symm hne)]
  · intro hμ
    have h0 : wtProj μ f = 0 := by
      ext m
      rw [coeff_wtProj, coeff_zero]
      split_ifs with hm
      · by_contra hc
        exact hμ (Finset.mem_image.2 ⟨m, MvPolynomial.mem_support_iff.2 hc, hm⟩)
      · rfl
    rw [h0, map_zero, map_zero]
end GroundTheory.Automorphic.HarishChandra
