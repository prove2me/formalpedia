-- Prove2me | solution 1 for GlobalTheory.CurveNorm.exists_smooth_normalisation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:50:35.804892+00:00
-- url     : https://prove2.me/submissions/f2127208-13a7-4e2e-bfa4-9bd198675f82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteIntegralClosureOfIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SmoothOfIsDedekindDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsSmoothNormalisation
import Theorems.Thm_GlobalTheory_CurveNorm_exists_lift_of_isIntegral
import Theorems.Thm_GlobalTheory_DedekindSmooth_smooth_of_isDedekindDomain
import Theorems.Thm_GlobalTheory_NormFin_finite_integralClosure_of_isAlgClosed


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CurveNorm
namespace GlobalTheory.CurveNorm
theorem _root_.solution (E : Type) [CommRing E] [IsDomain E] [Algebra ℂ E]
    [Algebra.FiniteType ℂ E] [Ring.DimensionLEOne E] (e : E →ₐ[ℂ] ℂ) :
    ∃ (E' : Type) (_ : CommRing E') (_ : IsDomain E') (_ : Algebra ℂ E') (ρ : E →ₐ[ℂ] E')
      (e' : E' →ₐ[ℂ] ℂ), Algebra.Smooth ℂ E' ∧ Function.Injective ρ ∧ e'.comp ρ = e := by
  let F := FractionRing E
  let E' : Type := integralClosure E F
  haveI : Module.Finite E E' := GlobalTheory.NormFin.finite_integralClosure_of_isAlgClosed ℂ E F
  letI : Algebra ℂ E' := ((algebraMap E E').comp (algebraMap ℂ E)).toAlgebra
  haveI : IsScalarTower ℂ E E' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.FiniteType ℂ E' := Algebra.FiniteType.trans (S := E) inferInstance inferInstance
  haveI : IsNoetherianRing E' := Algebra.FiniteType.isNoetherianRing ℂ E'
  haveI : Ring.DimensionLEOne E' := Ring.DimensionLEOne.integralClosure E F
  haveI : IsIntegrallyClosed E' := integralClosure.isIntegrallyClosedOfFiniteExtension F
  haveI : IsDedekindRing E' := ⟨⟩
  haveI : IsDedekindDomain E' := inferInstance
  have hinj : Function.Injective (algebraMap E E') := by
    intro x y h
    apply IsFractionRing.injective E F
    exact congrArg Subtype.val h
  obtain ⟨e', he'⟩ := exists_lift_of_isIntegral hinj e
  exact ⟨E', inferInstance, inferInstance, inferInstance, IsScalarTower.toAlgHom ℂ E E', e',
    GlobalTheory.DedekindSmooth.smooth_of_isDedekindDomain ℂ E', hinj, he'⟩
end GlobalTheory.CurveNorm
