-- Prove2me | solution 1 for ModularCurve.LevelRelabelling.exists_problemAut_act_mk_eq_mk_relabel_of_isUnit_det_gamma0Pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/60cbaa5b-1220-5519-90d9-aae7a88920c2

import Mathlib
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_LevelRelabelling

import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_IsDrinfeldBasis_zlinComb_zlinComb_of_isUnit_det
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_GroupLaws_mul_comm_of_isOriginIdentity
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_LevelTransport_act_relabel_eq_relabel_act
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_LevelTransport_map_relabel_eq_relabel_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LevelRelabelling_exists_problemAut_act_mk_eq_mk_relabel_of_isUnit_det_gamma0Pow
p2m_attr_erase "instance" "WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType"
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X WeierstrassProjModel.kw_lrThird_substHom_X GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left"

set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularCurve_LevelRelabelling_exists_problemAut_act_mk_eq_mk_relabel_of_isUnit_det_gamma0Pow.ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel"

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ModularCurve
p2m_export "ModularCurve" "LevelComponent LevelComponent.Raw LevelComponent.Raw.ext' kernelVariableChangeDeg LevelPData IsLevelPStructure LevelRelabelling.RawDrinfeldPair.relabel gamma0PowDeg IsGamma0PowAt"
namespace LevelRelabelling
p2m_export "ModularCurve.LevelRelabelling" "RawDrinfeldPair.relabel"
namespace DrinfeldRelabelAutAux
p2m_open "ModularCurve.LevelRelabelling ModularCurve"

variable {A : Type} [CommRing A] {ℓ M' q : ℕ}
  {hℓ : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
    (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
      ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C)}
  {hM : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
    (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
      ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h)}
  {𝒢 : GroupLaws A} {𝒯 : LevelTransport A 𝒢 q}

theorem isUnit_Δ_drinfeld {T : Type} [CommRing T] [Algebra A T] (x : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw T) :
    IsUnit x.level.2.2.curve.Δ := by
  obtain ⟨-, -, hxL⟩ := x.isLevel
  obtain ⟨-, hΔ, -⟩ := hxL
  exact hΔ

variable (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : IsUnit ((g.det : ℤ) : ZMod q))
  (hcomm : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (hΔ : IsUnit W.Δ)
    (P Q : Section W), (𝒢 T W hΔ).mul _ P Q = (𝒢 T W hΔ).mul _ Q P)

noncomputable def relabelRaw {T : Type} [CommRing T] [Algebra A T] (x : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw T) :
    (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw T where
  curve := x.curve
  isUnit_Δ := x.isUnit_Δ
  level := (x.level.1, x.level.2.1, RawDrinfeldPair.relabel 𝒢 g x.level.2.2 (isUnit_Δ_drinfeld x))
  isLevel := by
    obtain ⟨h0, h1, hxL⟩ := x.isLevel
    obtain ⟨hc, hΔ, hB⟩ := hxL
    refine ⟨h0, h1, hc, hΔ, ?_⟩
    exact IsDrinfeldBasis.zlinComb_zlinComb_of_isUnit_det (𝒢 T x.level.2.2.curve hΔ)
      (hcomm T x.level.2.2.curve hΔ) q x.level.2.2.P x.level.2.2.Q hB g hg

theorem relabelRaw_level_snd_snd {T : Type} [CommRing T] [Algebra A T] (x : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw T)
    (hΔ : IsUnit x.level.2.2.curve.Δ) :
    (relabelRaw g hg hcomm x).level.2.2 = RawDrinfeldPair.relabel 𝒢 g x.level.2.2 hΔ := rfl

variable (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity) (h𝒯 : 𝒯.IsSectionTransport)
    (hVC : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (hCO : ∀ (T T' : Type) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ)

include h𝒢 h𝒢O h𝒯 hVC hCO in
theorem relabelRaw_act {T : Type} [CommRing T] [Algebra A T] (C : WeierstrassCurve.VariableChange T)
    (x : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw T) :
    relabelRaw g hg hcomm ((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).act C x) =
      (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).act C (relabelRaw g hg hcomm x) := by
  refine LevelComponent.Raw.ext' ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · rfl
  · rfl
  · rfl
  show RawDrinfeldPair.relabel 𝒢 g (𝒯.act C x.level.2.2) _ = 𝒯.act C (RawDrinfeldPair.relabel 𝒢 g x.level.2.2 _)
  exact (LevelTransport.act_relabel_eq_relabel_act 𝒢 h𝒢 h𝒢O q 𝒯 h𝒯 hVC hCO T C g x.level.2.2
    (isUnit_Δ_drinfeld x) _).symm

include h𝒢 h𝒢O h𝒯 hVC hCO in
theorem relabelRaw_mapRing {T T' : Type} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
    (x : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw T) :
    relabelRaw g hg hcomm ((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).mapRing f x) =
      (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).mapRing f (relabelRaw g hg hcomm x) := by
  refine LevelComponent.Raw.ext' ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · rfl
  · rfl
  · rfl
  show RawDrinfeldPair.relabel 𝒢 g (𝒯.map f x.level.2.2) _ = 𝒯.map f (RawDrinfeldPair.relabel 𝒢 g x.level.2.2 _)
  exact (LevelTransport.map_relabel_eq_relabel_map 𝒢 h𝒢 h𝒢O q 𝒯 h𝒯 hVC hCO T T' f g x.level.2.2
    (isUnit_Δ_drinfeld x) _).symm

noncomputable def relabelAut : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.ProblemAut where
  act := fun {T} _ _ =>
    Quot.map (relabelRaw g hg hcomm) (by
      rintro x y ⟨C, rfl⟩
      exact ⟨C, relabelRaw_act g hg hcomm h𝒢 h𝒢O h𝒯 hVC hCO C x⟩)
  act_map := by
    intro T T' _ _ _ _ f p
    induction p using Quot.ind with
    | mk x =>
      show Quot.mk _ (relabelRaw g hg hcomm ((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).mapRing f x)) =
        Quot.mk _ ((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).mapRing f (relabelRaw g hg hcomm x))
      rw [relabelRaw_mapRing g hg hcomm h𝒢 h𝒢O h𝒯 hVC hCO]
  jOf_act := by
    intro T _ _ p
    induction p using Quot.ind with
    | mk x => rfl

end ModularCurve.LevelRelabelling.DrinfeldRelabelAutAux

open ModularCurve.LevelRelabelling.DrinfeldRelabelAutAux in
theorem solution
    (q ℓ M' : ℕ) (hq : 2 ≤ q) (A : Type) [CommRing A]
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    (hVC : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (hCO : ∀ (T T' : Type) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ)
    (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : IsUnit ((g.det : ℤ) : ZMod q)) :
    ∃ ρ : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.ProblemAut,
      ∀ (T : Type) [CommRing T] [Algebra A T] (x : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw T)
        (hΔ : IsUnit x.level.2.2.curve.Δ),
        ∃ x' : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw T,
          x'.curve = x.curve ∧ x'.level.1 = x.level.1 ∧ x'.level.2.1 = x.level.2.1 ∧
          x'.level.2.2 = ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel 𝒢 g x.level.2.2 hΔ ∧
          ρ.act (Quot.mk _ x) = (Quot.mk _ x' : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Pt T) := by
  have hcomm : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (hΔ : IsUnit W.Δ)
      (P Q : Section W), (𝒢 T W hΔ).mul _ P Q = (𝒢 T W hΔ).mul _ Q P :=
    fun T _ _ W hΔ P Q => GroupLaws.mul_comm_of_isOriginIdentity 𝒢 h𝒢 h𝒢O hVC hCO T W hΔ P Q
  refine ⟨relabelAut g hg hcomm h𝒢 h𝒢O h𝒯 hVC hCO, fun T _ _ x hΔ => ⟨relabelRaw g hg hcomm x, rfl, rfl, rfl, rfl, rfl⟩⟩

end S_ModularCurve_LevelRelabelling_exists_problemAut_act_mk_eq_mk_relabel_of_isUnit_det_gamma0Pow
end P2MW
export P2MW.S_ModularCurve_LevelRelabelling_exists_problemAut_act_mk_eq_mk_relabel_of_isUnit_det_gamma0Pow (solution)
