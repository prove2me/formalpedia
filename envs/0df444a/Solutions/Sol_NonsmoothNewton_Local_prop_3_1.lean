-- Prove2me | solution 1 for NonsmoothNewton.Local.prop_3_1
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T11:08:22.774238+00:00
-- url     : https://prove2.me/submissions/eda8ddf9-d9cc-497d-abad-72904b40f398

import Theorems.Thm_NonsmoothNewton_Shared_isCompact_clarkeJac
import Theorems.Thm_NonsmoothNewton_Shared_exists_local_clarkeJac_subset_thickening
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic
open Filter Topology
open NonsmoothNewton.Shared

theorem solution {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hF : LocallyLipschitz F)
    (x : EuclideanSpace ℝ (Fin n)) (hns : ∀ V ∈ clarkeJac F x, IsUnit V) :
    ∃ N ∈ 𝓝 x, ∃ C : ℝ, ∀ y ∈ N, ∀ V ∈ clarkeJac F y,
      ∃ W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n),
        V.comp W = ContinuousLinearMap.id ℝ _ ∧ W.comp V = ContinuousLinearMap.id ℝ _ ∧
        ‖W‖ ≤ C := by
  let R := EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)
  have hc := isCompact_clarkeJac F hF x
  have hi : ContinuousOn (Ring.inverse : R → R) (clarkeJac F x) := by
    intro V hV
    obtain ⟨u,rfl⟩ := hns V hV
    exact (NormedRing.inverse_continuousAt u).continuousWithinAt
  obtain ⟨C,hC⟩ := hc.bddAbove_image hi.norm
  let U : Set R := {V | IsUnit V ∧ ‖Ring.inverse V‖ < C+1}
  have hU : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro V hV
    obtain ⟨⟨u,rfl⟩,hu⟩ := hV
    have hh := (NormedRing.inverse_continuousAt u).norm.eventually_lt_const hu
    exact Filter.inter_mem u.nhds hh
  have hsub : clarkeJac F x ⊆ U := by
    intro V hV
    refine ⟨hns V hV,?_⟩
    have hh := hC (Set.mem_image_of_mem (fun V : R => ‖Ring.inverse V‖) hV)
    linarith
  obtain ⟨eps,heps,hth⟩ := hc.exists_thickening_subset_open hU hsub
  obtain ⟨delta,hdelta,hd⟩ := exists_local_clarkeJac_subset_thickening F hF x heps
  refine ⟨Metric.ball x delta,Metric.ball_mem_nhds x hdelta,C+1,?_⟩
  intro y hy V hV
  have hg := hth (hd y hy hV)
  refine ⟨Ring.inverse V,?_,?_,hg.2.le⟩
  · change V*Ring.inverse V=1
    exact Ring.mul_inverse_cancel V hg.1
  · change Ring.inverse V*V=1
    exact Ring.inverse_mul_cancel V hg.1
