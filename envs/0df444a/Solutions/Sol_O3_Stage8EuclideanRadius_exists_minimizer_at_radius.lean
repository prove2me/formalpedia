-- Prove2me | solution 1 for O3.Stage8EuclideanRadius.exists_minimizer_at_radius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:25:21.570443+00:00
-- url     : https://prove2.me/submissions/e33c470c-60fd-4ba7-a855-f2d8aa4ef5a5

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_Stage2RouteC
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Definitions.Def_O3_Stage8EuclideanRadius
import Theorems.Thm_O3_Stage8EuclideanRadius_minimizerSet_isClosed
import Theorems.Thm_O3_Stage8EuclideanRadius_lpNorm_two_eq_transport_dist
import Theorems.Thm_O3_lpNorm_nonneg


set_option autoImplicit true
open O3 O3.Stage8EuclideanRadius
open O3
namespace O3.Stage8EuclideanRadius
theorem _root_.solution {d : ℕ} (P : AdmissibleInstance d 2) :
    ∃ xstar : Vec d,
      xstar ∈ MinimizerSet P.f ∧ lpNorm 2 (xstar - P.x0) = P.radius := by
  let e : Vec d ≃ₜ EuclideanLpSpace d :=
    (PiLp.homeomorph (ENNReal.ofReal (2 : ℝ)) (fun _ : Fin d ↦ ℝ)).symm
  let S : Set (EuclideanLpSpace d) := e '' MinimizerSet P.f
  let _ : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := ⟨by norm_num⟩
  let _ : ProperSpace (EuclideanLpSpace d) :=
    FiniteDimensional.proper ℝ (EuclideanLpSpace d)
  have hSclosed : IsClosed S := e.isClosedMap _ (minimizerSet_isClosed P)
  have hSne : S.Nonempty := P.minimizer_nonempty.image e
  obtain ⟨z, hzS, hz⟩ := hSclosed.exists_infDist_eq_dist hSne (e P.x0)
  rcases hzS with ⟨xstar, hxstar, rfl⟩
  refine ⟨xstar, hxstar, ?_⟩
  let distances : Set ℝ :=
    (fun x : Vec d ↦ lpNorm 2 (x - P.x0)) '' MinimizerSet P.f
  have hnonempty : distances.Nonempty := P.minimizer_nonempty.image _
  have hbelow : BddBelow distances := ⟨0, by
    intro r hr
    rcases hr with ⟨x, hx, rfl⟩
    exact lpNorm_nonneg 2 (x - P.x0)⟩
  have hle : lpNorm 2 (xstar - P.x0) ≤ sInf distances := by
    apply le_csInf hnonempty
    intro r hr
    rcases hr with ⟨x, hx, rfl⟩
    have hxS : e x ∈ S := ⟨x, hx, rfl⟩
    change lpNorm 2 (xstar - P.x0) ≤ lpNorm 2 (x - P.x0)
    rw [lpNorm_two_eq_transport_dist, lpNorm_two_eq_transport_dist]
    change dist (e xstar) (e P.x0) ≤ dist (e x) (e P.x0)
    rw [dist_comm (e xstar) (e P.x0), dist_comm (e x) (e P.x0)]
    calc
      dist (e P.x0) (e xstar) = Metric.infDist (e P.x0) S := hz.symm
      _ ≤ dist (e P.x0) (e x) := Metric.infDist_le_dist_of_mem hxS
  have hge : sInf distances ≤ lpNorm 2 (xstar - P.x0) :=
    csInf_le hbelow ⟨xstar, hxstar, rfl⟩
  change lpNorm 2 (xstar - P.x0) = sInf distances
  exact le_antisymm hle hge
end O3.Stage8EuclideanRadius
