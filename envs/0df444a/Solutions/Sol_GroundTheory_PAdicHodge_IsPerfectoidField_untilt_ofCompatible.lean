-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.untilt_ofCompatible
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:42.637307+00:00
-- url     : https://prove2.me/submissions/7ad79572-1128-4b0a-9785-f92789e5d9cf

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
namespace GroundTheory.PAdicHodge.IsPerfectoidField
theorem _root_.solution (y : ℕ → 𝒪) (hy : ∀ n, y (n + 1) ^ p = y n) :
    PreTilt.untilt (ofCompatible p y hy) = y 0 := by
  have hpow : ∀ n, y n ^ p ^ n = y 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', pow_mul, hy, ih]
  exact Perfection.teichmuller_spec fun n => ⟨y n, rfl, by rw [hpow n]; exact SModEq.refl _⟩
end GroundTheory.PAdicHodge.IsPerfectoidField
