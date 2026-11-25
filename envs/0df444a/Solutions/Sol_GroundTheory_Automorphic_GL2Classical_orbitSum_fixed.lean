-- Prove2me | solution 1 for GroundTheory.Automorphic.GL2Classical.orbitSum_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:48:50.613989+00:00
-- url     : https://prove2.me/submissions/8a0d6a0d-da78-4335-acd7-f9cb4c531198

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2Classical_UnitaryEigenSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.GL2Classical
variable {G : Type*} [Group G] {E : Type*} [AddCommGroup E] [Module ℂ E]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (ρ : Representation ℂ G E) (ι : E →ₗ[ℂ] H) (T : Submodule ℂ E)
variable {ρ}
namespace GroundTheory.Automorphic.GL2Classical
theorem _root_.solution {K : Subgroup G} {v : E} (hv : (Set.range fun k : K => ρ k v).Finite)
    (k : K) : ρ k (orbitSum ρ K v hv) = orbitSum ρ K v hv := by
  unfold orbitSum
  rw [map_sum]
  refine Finset.sum_nbij' (fun w => ρ k w) (fun w => ρ (k⁻¹ : K) w) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
  · intro w hw
    simp only [Set.Finite.mem_toFinset] at hw ⊢
    obtain ⟨k', rfl⟩ := hw
    exact ⟨k * k', by show ρ ((k * k' : K) : G) v = _; rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply]⟩
  · intro w hw
    simp only [Set.Finite.mem_toFinset] at hw ⊢
    obtain ⟨k', rfl⟩ := hw
    exact ⟨k⁻¹ * k', by show ρ ((k⁻¹ * k' : K) : G) v = _; rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply]⟩
  · intro w _
    change ρ ((k⁻¹ : K) : G) (ρ k w) = w
    rw [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, inv_mul_cancel, map_one, Module.End.one_apply]
  · intro w _
    change ρ (k : G) (ρ ((k⁻¹ : K) : G) w) = w
    rw [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, mul_inv_cancel, map_one, Module.End.one_apply]
end GroundTheory.Automorphic.GL2Classical
