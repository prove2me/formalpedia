-- Prove2me | solution 1 for GroundTheory.PAdicHodge.AInf.ker_fontaineTheta_comp_frobeniusEquiv_symm_pow
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-27T03:01:33.54885+00:00
-- url     : https://prove2.me/submissions/dc6acfa9-d66d-4248-933b-a3f09c9b8a5b

import Mathlib
import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
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
open GroundTheory.PAdicHodge.AInf
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)
theorem solution {ξ : AInf K p}
    (hξ : RingHom.ker θ = Ideal.span {ξ}) (n : ℕ) :
    RingHom.ker ((fontaineTheta (normInteger K) p).comp ((φ).symm ^ n : AInf K p ≃+* AInf K p).toRingHom) =
      Ideal.span {(φ ^ n) ξ} := by
  have he : (((φ).symm ^ n : AInf K p ≃+* AInf K p)).symm = φ ^ n := by
    show ((φ)⁻¹ ^ n)⁻¹ = φ ^ n
    rw [inv_pow, inv_inv]
  rw [← RingHom.comap_ker, hξ]
  have h1 : Ideal.comap (((φ).symm ^ n : AInf K p ≃+* AInf K p)).toRingHom (Ideal.span {ξ}) =
      Ideal.map (((φ).symm ^ n : AInf K p ≃+* AInf K p)).symm (Ideal.span {ξ}) :=
    (Ideal.map_symm _).symm
  rw [h1, Ideal.map_span, Set.image_singleton, he]
