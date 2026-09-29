-- Prove2me | solution 1 for ModularCurve.FullLevel.variableChange_map_eq_one_of_eq_act_of_map_residue_eq_gamma0Pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/37c36241-4c91-5692-9f07-aa638fa96ac1

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Theorems.Thm_ModularCurve_IsLevelPStructure_variableChange_eq_one_of_smul_eq_of_variableChange_eq_of_prime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_variableChange_map_eq_one_of_eq_act_of_map_residue_eq_gamma0Pow
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

universe u

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing FormalGroup

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    (q ℓ M' : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ)
    (A₀ : Type) [CommRing A₀]
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (𝒢 : GroupLaws A₀) (𝒯 : LevelTransport A₀ 𝒢 q)
    (T : Type) [CommRing T] [Algebra A₀ T] (k : Type) [Field k] (resT : T →+* k) (hℓk : ((ℓ : ℕ) : k) ≠ 0)
    (x y : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Raw T) (C : WeierstrassCurve.VariableChange T)
    (hC : y = (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act C x)
    (hcurve : y.curve.map resT = x.curve.map resT)
    (hlev : y.level.2.1.map resT = x.level.2.1.map resT) :
    C.map resT = 1 := by
  subst hC
  have hℓu : IsUnit ((ℓ : ℕ) : k) := isUnit_iff_ne_zero.mpr hℓk
  have hΔ : IsUnit (x.curve.map resT).Δ := x.curve.isUnit_Δ_map resT x.isUnit_Δ
  have hD : ModularCurve.IsLevelPStructure (x.curve.map resT) ℓ (x.level.2.1.map resT) :=
    (x.isLevel.2.1 : ModularCurve.IsLevelPStructure x.curve ℓ x.level.2.1).map resT
  have hCW : C.map resT • x.curve.map resT = x.curve.map resT := by
    rw [x.curve.map_variableChange C resT]; exact hcurve
  have hCD : (x.level.2.1.map resT).variableChange (C.map resT) = x.level.2.1.map resT := by
    rw [← ModularCurve.LevelPData.map_variableChange resT C]; exact hlev
  exact ModularCurve.IsLevelPStructure.variableChange_eq_one_of_smul_eq_of_variableChange_eq_of_prime
    ℓ hℓ3 hℓu _ hΔ _ hD _ hCW hCD

end S_ModularCurve_FullLevel_variableChange_map_eq_one_of_eq_act_of_map_residue_eq_gamma0Pow
end P2MW
export P2MW.S_ModularCurve_FullLevel_variableChange_map_eq_one_of_eq_act_of_map_residue_eq_gamma0Pow (solution)
