-- Prove2me | solution 2 for GroundTheory.PAdicHodge.AInf.ker_fontaineTheta_eq_span_xi_ofCompatible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:50:24.634223+00:00
-- url     : https://prove2.me/submissions/c5989668-60ba-4366-b0a7-3fb40debf9d1

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfXi
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_ker_fontaineTheta_eq_span_xi
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_frobeniusEquiv_symm_ofCompatible
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_untilt_ofCompatible


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
open WittVector
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.AInf
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)
namespace GroundTheory.PAdicHodge.AInf
theorem _root_.solution (y : ℕ → 𝒪) (hy : ∀ n, y (n + 1) ^ p = y n)
    (h0 : y 0 = 1) (h1 : y 1 ≠ 1) :
    RingHom.ker θ = Ideal.span {xi (IsPerfectoidField.ofCompatible p y hy)} := by
  refine ker_fontaineTheta_eq_span_xi ?_ ?_
  · rw [IsPerfectoidField.untilt_ofCompatible, h0]
  · rw [frobeniusEquiv_symm_ofCompatible, IsPerfectoidField.untilt_ofCompatible]
    exact h1
end GroundTheory.PAdicHodge.AInf
