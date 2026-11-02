-- Prove2me | solution 1 for HryniewiczCriterion.exists_continuous_lift_of_continuous_mod_one
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-01T16:04:23.594543+00:00
-- url     : https://prove2.me/submissions/bd503151-b3c0-424e-bbc8-e8fabebfe6c8

import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Instances.ZMultiples
import Mathlib.Analysis.LocallyConvex.WithSeminorms



/-!
# A real function that is continuous modulo `1` has a continuous integer correction

Child of `exists_page_parameter_along_trajectory`.
-/

namespace HryniewiczCriterion

theorem exists_continuous_lift_of_continuous_mod_one_aux (f : ℝ → ℝ)
    (hf : Continuous (fun t => (f t : AddCircle (1 : ℝ)))) :
    ∃ Θ : ℝ → ℝ, Continuous Θ ∧ ∀ t, ∃ n : ℤ, Θ t = f t + n := by
  have hcov : IsCoveringMap ((↑) : ℝ → AddCircle (1 : ℝ)) := AddCircle.isCoveringMap_coe 1
  obtain ⟨F, ⟨-, hF⟩, -⟩ := hcov.existsUnique_continuousMap_lifts
    (⟨fun t => (f t : AddCircle (1 : ℝ)), hf⟩ : C(ℝ, AddCircle (1 : ℝ))) 0 (f 0) rfl
  refine ⟨F, F.continuous, fun t => ?_⟩
  have h := congrFun hF t
  simp only [Function.comp_apply, ContinuousMap.coe_mk] at h
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 (QuotientAddGroup.eq.1 h.symm)
  refine ⟨k, ?_⟩
  simp only [zsmul_eq_mul, mul_one] at hk
  linarith

end HryniewiczCriterion

open HryniewiczCriterion

theorem solution (f : ℝ → ℝ)
    (hf : Continuous (fun t => (f t : AddCircle (1 : ℝ)))) :
    ∃ Θ : ℝ → ℝ, Continuous Θ ∧ ∀ t, ∃ n : ℤ, Θ t = f t + n :=
  exists_continuous_lift_of_continuous_mod_one_aux f hf
