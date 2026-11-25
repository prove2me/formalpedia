-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.eq_zero_of_mem_center_of_hcProjLin_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:03:41.855452+00:00
-- url     : https://prove2.me/submissions/cc7a1a77-bf25-40dd-a187-457083de5ff5

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Fischer
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Injective
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_exists_adjoint
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_eq_zero_of_forall_highestWeight
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_eq_zero_of_rho_zero_eq_zero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_rep_apply_of_highestWeight
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_rho_zero_e
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_rowOp_self_of_wtProj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
open MvPolynomial
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution {z : U n}
    (hz : z ∈ Subalgebra.center ℂ (U n)) (h : hcProjLin z = 0) : z = 0 := by
  obtain ⟨z', hz'⟩ := exists_adjoint z
  have hc : ∀ u : U n, u * z = z * u := fun u => (Subalgebra.mem_center_iff.1 hz) u
  apply eq_zero_of_rho_zero_eq_zero
  refine eq_zero_of_forall_highestWeight (rho 0 z) (rho 0 z') ?_ hz' ?_ ?_
  · intro i j
    rw [← rho_zero_e, ← map_mul, ← map_mul, hc]
  · rw [← map_mul, ← map_mul, hc]
  · intro v μ hup hwt
    have := rep_apply_of_highestWeight (rho 0) (fun i => (μ i : ℂ)) (v := v)
      (fun a ha => by
        rw [show e a = e (a.1, a.2) from rfl, rho_zero_e]
        exact hup a.1 a.2 ha)
      (fun k => by rw [rho_zero_e]; exact rowOp_self_of_wtProj μ v k hwt)
      (fun k => hc (e (k, k)))
    rw [this, h, map_zero, zero_smul]
end GroundTheory.Automorphic.HarishChandra
