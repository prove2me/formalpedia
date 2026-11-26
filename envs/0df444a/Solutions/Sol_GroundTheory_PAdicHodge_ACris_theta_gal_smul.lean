-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ACris.theta_gal_smul
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T16:05:44.991868+00:00
-- url     : https://prove2.me/submissions/67460020-73d4-46f8-b158-7c411979fb5b

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Definitions.Def_GroundTheory_PAdicHodge_AInfGalois
import Definitions.Def_GroundTheory_PAdicHodge_ACrisGalois
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
open GroundTheory.PAdicHodge.ACris
variable {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
local notation "𝔸" => Localization.Away (p : AInf ℂ_[p] p)
local notation "θ" => WittVector.fontaineTheta (normInteger ℂ_[p]) p
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger ℂ_[p]) p)

open GroundTheory.PAdicHodge.ACris in
theorem solution (σ : Gal(PadicAlgCl p/K)) (x : ACris ℂ_[p] p) :
    ((theta ℂ_[p] p (σ • x) : normInteger ℂ_[p]) : ℂ_[p]) =
      σ • ((theta ℂ_[p] p x : normInteger ℂ_[p]) : ℂ_[p]) := by
  change ((theta ℂ_[p] p (galCris σ x) : normInteger ℂ_[p]) : ℂ_[p]) =
    (galCp σ : ℂ_[p] →+* ℂ_[p]) (theta ℂ_[p] p x)
  have haway :
      (thetaAway ℂ_[p] p).comp (galAway σ) =
        (galCp σ : ℂ_[p] →+* ℂ_[p]).comp (thetaAway ℂ_[p] p) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (p : AInf ℂ_[p] p)) ?_
    ext y
    simp only [RingHom.comp_apply, galAway_algebraMap, thetaAway_algebraMap]
    exact AInf.fontaineTheta_gal_smul σ y
  have hmem (z : ACris ℂ_[p] p) :
      (galCp σ : ℂ_[p] →+* ℂ_[p]) (theta ℂ_[p] p z) ∈ normInteger ℂ_[p] := by
    have hn : ‖(galCp σ : ℂ_[p] →+* ℂ_[p]) (theta ℂ_[p] p z : ℂ_[p])‖ ≤ 1 := by
      rw [AInf.norm_galCp_toRingHom]
      exact (theta ℂ_[p] p z).2
    exact hn
  let G : ACris ℂ_[p] p →+* normInteger ℂ_[p] :=
    (((galCp σ : ℂ_[p] →+* ℂ_[p]).comp
      (algebraMap (normInteger ℂ_[p]) ℂ_[p])).comp (theta ℂ_[p] p)).codRestrict
      (normInteger ℂ_[p]) hmem
  have hFG : (theta ℂ_[p] p).comp (galCris σ) = G := by
    refine ringHom_ext fun y => ?_
    dsimp [galCris]
    rw [extendEndo_of]
    -- theta (of (galZero y)) = G (of y)
    rw [show theta ℂ_[p] p = AdicCompletion.extendRingHom
        (Ideal.span {(p : ACrisZero ℂ_[p] p)}) (Ideal.span {(p : normInteger ℂ_[p])})
        (thetaZero ℂ_[p] p) span_p_le_comap_thetaZero from rfl]
    rw [AdicCompletion.extendRingHom_of]
    refine Subtype.ext ?_
    change (thetaZero ℂ_[p] p (galZero σ y) : ℂ_[p]) =
      (galCp σ : ℂ_[p] →+* ℂ_[p]) (theta ℂ_[p] p (AdicCompletion.of _ _ y))
    rw [show theta ℂ_[p] p = AdicCompletion.extendRingHom
        (Ideal.span {(p : ACrisZero ℂ_[p] p)}) (Ideal.span {(p : normInteger ℂ_[p])})
        (thetaZero ℂ_[p] p) span_p_le_comap_thetaZero from rfl]
    rw [AdicCompletion.extendRingHom_of]
    simp [thetaZero, G]
    exact congrFun (congrArg DFunLike.coe haway) (y : 𝔸)
  have hx := congrFun (congrArg DFunLike.coe hFG) x
  rw [RingHom.comp_apply] at hx
  rw [hx]
  rfl
