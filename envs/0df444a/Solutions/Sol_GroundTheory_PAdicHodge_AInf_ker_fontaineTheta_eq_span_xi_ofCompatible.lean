-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.ker_fontaineTheta_eq_span_xi_ofCompatible
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-27T03:03:57.609971+00:00
-- url     : https://prove2.me/submissions/e9240df0-aa32-49ef-9212-b8907ff80f8d

import Mathlib
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_ker_fontaineTheta_eq_span_xi
import Theorems.Thm_GroundTheory_PAdicHodge_AInf_frobeniusEquiv_symm_ofCompatible
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_untilt_ofCompatible
import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfXi
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
theorem solution (y : ℕ → 𝒪) (hy : ∀ n, y (n + 1) ^ p = y n)
    (h0 : y 0 = 1) (h1 : y 1 ≠ 1) :
    RingHom.ker θ = Ideal.span {xi (IsPerfectoidField.ofCompatible p y hy)} := by
  have hε : PreTilt.untilt (IsPerfectoidField.ofCompatible p y hy) = 1 := by
    rw [IsPerfectoidField.untilt_ofCompatible]; exact h0
  have hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm
      (IsPerfectoidField.ofCompatible p y hy)) ≠ 1 := by
    rw [AInf.frobeniusEquiv_symm_ofCompatible, IsPerfectoidField.untilt_ofCompatible]; exact h1
  exact AInf.ker_fontaineTheta_eq_span_xi hε hζ
