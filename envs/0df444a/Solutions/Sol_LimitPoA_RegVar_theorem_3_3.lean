-- Prove2me | solution 1 for LimitPoA.RegVar.theorem_3_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T19:56:09.472996+00:00
-- url     : https://prove2.me/submissions/776dce0d-fd8a-45e9-bbf4-5e4f73b11eb6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_LimitPoA_RegVar_Model
import Theorems.Thm_LimitPoA_RegVar_corollary_3_2
import Theorems.Thm_LimitPoA_RegVar_theorem_3_3_scalable

open Filter Topology LimitPoA.RegVar

theorem solution (Γ : Game) (hΓ : Γ.Standing) (τ : Fin Γ.J → ℝ → ℝ)
    (hτ : ∀ a, IsCostFn (τ a)) (hrv : ∀ a, IsRegularlyVarying (τ a)) :
    IsAsymptoticallyWellDesigned Γ τ := by
  have hnd : ∀ a, ∃ x, 0 < x ∧ τ a x ≠ 0 := by
    intro a
    by_contra hcon
    push_neg at hcon
    obtain ⟨q, hq, hlim⟩ := hrv a 1 one_pos
    have h0 : (fun t => τ a (t * 1) / τ a t) =ᶠ[atTop] fun _ => (0 : ℝ) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      simp [hcon t ht]
    have := tendsto_nhds_unique (hlim.congr' h0) tendsto_const_nhds
    linarith
  exact corollary_3_2 Γ hΓ τ hτ hnd (theorem_3_3_scalable Γ hΓ τ hτ hrv)
