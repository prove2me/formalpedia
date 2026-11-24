-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.norm_le_of_mem_span_p
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:02:04.492342+00:00
-- url     : https://prove2.me/submissions/3e7f68ff-fa70-41e4-b122-0bd2ecc311cb

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
omit [Fact p.Prime] [IsPerfectoidField K p]
namespace GroundTheory.PAdicHodge.IsPerfectoidField
theorem _root_.solution {b : 𝒪} (hb : b ∈ Ideal.span {(p : 𝒪)}) :
    ‖(b : K)‖ ≤ ‖(p : K)‖ := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hb
  rw [Subring.coe_mul, norm_mul]
  have hc := mem_normInteger.1 c.2
  have : ((p : 𝒪) : K) = (p : K) := by simp
  rw [this]
  calc ‖(c : K)‖ * ‖(p : K)‖ ≤ 1 * ‖(p : K)‖ := by gcongr
    _ = _ := one_mul _
end GroundTheory.PAdicHodge.IsPerfectoidField
