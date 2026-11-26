-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ACris.phiZero_gal_smul
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T16:11:54.696919+00:00
-- url     : https://prove2.me/submissions/39984cd2-025c-4cc4-9a4a-1d88db67d87e

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

open GroundTheory.PAdicHodge.ACris WittVector in
theorem solution (σ : Gal(PadicAlgCl p/K)) (y : ACrisZero ℂ_[p] p) :
    phiZero ℂ_[p] p (σ • y) = σ • phiZero ℂ_[p] p y := by
  change phiZero ℂ_[p] p (galZero σ y) = galZero σ (phiZero ℂ_[p] p y)
  have hcomm_inf (z : AInf ℂ_[p] p) : φ (σ • z) = σ • φ z := by
    change frobenius (AInf.galMap σ z) = AInf.galMap σ (frobenius z)
    rw [frobenius_eq_map_frobenius, AInf.galMap]
    refine ext fun n => ?_
    simp [AInf.map_coeff, map_coeff, frobenius_def, map_pow]
  have hcomm_away :
      (phiAway ℂ_[p] p).comp (galAway σ) = (galAway σ).comp (phiAway ℂ_[p] p) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (p : AInf ℂ_[p] p)) ?_
    ext z
    simp only [RingHom.comp_apply, galAway_algebraMap, phiAway_algebraMap]
    congr 1
    exact hcomm_inf z
  have hcomm_zero :
      (phiZero ℂ_[p] p).comp (galZero σ) = (galZero σ).comp (phiZero ℂ_[p] p) := by
    ext z
    change (phiAway ℂ_[p] p (galAway σ (z : 𝔸)) : 𝔸) =
      galAway σ (phiAway ℂ_[p] p (z : 𝔸))
    exact congrFun (congrArg DFunLike.coe hcomm_away) (z : 𝔸)
  exact congrFun (congrArg DFunLike.coe hcomm_zero) y
