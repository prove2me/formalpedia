-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.exists_mk_untilt_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:44:18.72904+00:00
-- url     : https://prove2.me/submissions/901c1ed1-9779-4a63-8645-062600b1b90f

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeSpanSingletonOfForallMemEq
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_mk_untilt
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_surjective_frobenius


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
local notation "φ" => RingEquiv.symm (frobeniusEquiv (PreTilt (normInteger K) p) p)
namespace GroundTheory.PAdicHodge.IsPerfectoidField
theorem _root_.solution (b : 𝒪) :
    ∃ a : 𝒪♭, Ideal.Quotient.mk (Ideal.span {(p : 𝒪)}) (PreTilt.untilt a) =
      Ideal.Quotient.mk _ b := by
  obtain ⟨a, ha⟩ : ∃ a : 𝒪♭, PreTilt.coeff 0 a = Ideal.Quotient.mk _ b :=
    Perfection.coeff_surjective (surjective_frobenius (K := K) p) 0
    (Ideal.Quotient.mk _ b)
  exact ⟨a, by rw [mk_untilt]; exact ha⟩
end GroundTheory.PAdicHodge.IsPerfectoidField
