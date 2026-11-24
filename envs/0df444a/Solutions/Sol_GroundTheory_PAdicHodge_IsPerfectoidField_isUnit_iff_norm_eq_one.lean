-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.isUnit_iff_norm_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:42.89169+00:00
-- url     : https://prove2.me/submissions/4423793e-b1be-485c-9e56-8d371359a588

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeSpanSingletonOfForallMemEq
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open WittVector
open GroundTheory.PAdicHodge.IsPerfectoidField
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable (p : ℕ) [Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
variable {p}
namespace GroundTheory.PAdicHodge.IsPerfectoidField
theorem _root_.solution {u : 𝒪} : IsUnit u ↔ ‖(u : K)‖ = 1 := by
  constructor
  · rintro ⟨w, rfl⟩
    have h1 : ‖((w : 𝒪) : K)‖ * ‖(((w⁻¹ : 𝒪ˣ) : 𝒪) : K)‖ = 1 := by
      rw [← norm_mul, ← Subring.coe_mul, Units.mul_inv]; simp
    have ha := mem_normInteger.1 (w : 𝒪).2
    have hb := mem_normInteger.1 ((w⁻¹ : 𝒪ˣ) : 𝒪).2
    nlinarith [norm_nonneg ((w : 𝒪) : K), norm_nonneg (((w⁻¹ : 𝒪ˣ) : 𝒪) : K)]
  · intro h
    have h0 : (u : K) ≠ 0 := by
      intro h0; rw [h0, norm_zero] at h; exact zero_ne_one h
    refine isUnit_iff_exists_inv.2 ⟨⟨(u : K)⁻¹, mem_normInteger.2 (by rw [norm_inv, h, inv_one])⟩, ?_⟩
    ext
    simp [h0]
end GroundTheory.PAdicHodge.IsPerfectoidField
