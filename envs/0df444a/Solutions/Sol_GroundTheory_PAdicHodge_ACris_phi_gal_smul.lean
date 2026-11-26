-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ACris.phi_gal_smul
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T15:58:31.738954+00:00
-- url     : https://prove2.me/submissions/32479238-7b79-4a96-85fc-e7b6a3db88c0

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
theorem solution (σ : Gal(PadicAlgCl p/K)) (x : ACris ℂ_[p] p) :
    phi ℂ_[p] p (σ • x) = σ • phi ℂ_[p] p x := by
  change phi ℂ_[p] p (galCris σ x) = galCris σ (phi ℂ_[p] p x)
  have hcomm_inf (y : AInf ℂ_[p] p) : φ (σ • y) = σ • φ y := by
    change frobenius (AInf.galMap σ y) = AInf.galMap σ (frobenius y)
    rw [frobenius_eq_map_frobenius, AInf.galMap]
    refine ext fun n => ?_
    simp [AInf.map_coeff, map_coeff, frobenius_def, map_pow]
  have hcomm_away :
      (phiAway ℂ_[p] p).comp (galAway σ) = (galAway σ).comp (phiAway ℂ_[p] p) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (p : AInf ℂ_[p] p)) ?_
    ext y
    simp only [RingHom.comp_apply, galAway_algebraMap, phiAway_algebraMap]
    congr 1
    exact hcomm_inf y
  have hcomm_zero :
      (phiZero ℂ_[p] p).comp (galZero σ) = (galZero σ).comp (phiZero ℂ_[p] p) := by
    ext y
    change (phiAway ℂ_[p] p (galAway σ (y : 𝔸)) : 𝔸) =
      galAway σ (phiAway ℂ_[p] p (y : 𝔸))
    exact congrFun (congrArg DFunLike.coe hcomm_away) (y : 𝔸)
  have hx : (phi ℂ_[p] p).comp (galCris σ) = (galCris σ).comp (phi ℂ_[p] p) := by
    refine ringHom_ext fun y => ?_
    dsimp [galCris]
    rw [extendEndo_of]
    conv_lhs => rw [phi, AdicCompletion.extendRingHom_of]
    conv_rhs => rw [phi, AdicCompletion.extendRingHom_of]
    simp only [RingHom.comp_apply]
    have hφz : phiZero ℂ_[p] p (galZero σ y) = galZero σ (phiZero ℂ_[p] p y) :=
      congrFun (congrArg DFunLike.coe hcomm_zero) y
    rw [hφz]
    erw [extendEndo_of]
    simp [Algebra.algebraMap_self, RingHom.id_apply]
    rfl
  simpa [RingHom.comp_apply] using congrFun (congrArg DFunLike.coe hx) x
