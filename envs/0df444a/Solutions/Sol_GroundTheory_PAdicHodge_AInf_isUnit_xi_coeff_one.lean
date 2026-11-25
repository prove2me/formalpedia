-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.isUnit_xi_coeff_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:45:04.435838+00:00
-- url     : https://prove2.me/submissions/f3c6f16c-7654-4906-922f-2255e25cf851

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfXi
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_fontaineTheta_xi
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_norm_natCast_ne_zero
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_norm_xi_coeff_zero
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_isUnit_iff_norm_untilt
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_mk_untilt
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_norm_eq_one_of_mk_eq
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_norm_untilt_coeff_zero
import Theorems.Thm_GroundTheory_PAdicHodge_coeff_one_teichmuller_add_mul_p
import Theorems.Thm_GroundTheory_PAdicHodge_exists_eq_teichmuller_add_mul_p


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
theorem _root_.solution {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) :
    IsUnit ((xi ε).coeff 1) := by
  obtain ⟨v, hv⟩ := exists_eq_teichmuller_add_mul_p (xi ε)
  have hker : xi ε ∈ RingHom.ker θ := fontaineTheta_xi hε hζ
  have h1 := IsPerfectoidField.norm_untilt_coeff_zero hker hv
  rw [← preTilt_norm_def, norm_xi_coeff_zero hε hζ] at h1
  have hθv : ‖((θ v : 𝒪) : K)‖ = 1 :=
    (mul_eq_right₀ (norm_natCast_ne_zero hε hζ)).1 h1.symm
  have hmk : Ideal.Quotient.mk (Ideal.span {(p : 𝒪)}) (PreTilt.untilt (v.coeff 0)) =
      Ideal.Quotient.mk _ (θ v) := by
    rw [IsPerfectoidField.mk_untilt, WittVector.mk_fontaineTheta]
  have hu := IsPerfectoidField.norm_eq_one_of_mk_eq p hmk hθv
  rw [hv, coeff_one_teichmuller_add_mul_p]
  exact ((IsPerfectoidField.isUnit_iff_norm_untilt p).2 hu).pow p
end GroundTheory.PAdicHodge.AInf
