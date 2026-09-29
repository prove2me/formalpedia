-- Prove2me | solution 1 for ModularCurve.LevelModuliPackageAbs.exists_raw_linComb_algEquiv_map_univ_eq_gamma0Pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/3fb14d57-833d-5e8e-a437-86a38e18b8dd

import Mathlib
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor

import Definitions.Def_ModularCurve_LevelRelabelling
import Theorems.Thm_ModularCurve_LevelModuliPackageAbs_exists_algEquiv_map_univ_eq_act
import Theorems.Thm_ModularCurve_LevelRelabelling_exists_problemAut_act_mk_eq_mk_relabel_of_isUnit_det_gamma0Pow
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Theorems.Thm_ModularCurve_LevelRelabelling_RawDrinfeldPair_relabel_relabel_eq_self_of_mul_map_eq_one_of_isLevel
import Theorems.Thm_Matrix_exists_isUnit_det_and_mul_map_castRingHom_zmod_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LevelModuliPackageAbs_exists_raw_linComb_algEquiv_map_univ_eq_gamma0Pow
p2m_attr_erase "instance" "WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType"
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X WeierstrassProjModel.kw_lrThird_substHom_X GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left"

set_option autoImplicit false

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    (q : ℕ) [Fact q.Prime] (ℓ M' : ℕ) [Fact ℓ.Prime] [NeZero M']
    (A₀ : Type) [CommRing A₀]
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (𝒢 : GroupLaws A₀) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A₀ 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    (hVC : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (hCO : ∀ (T T' : Type) [CommRing T] [Algebra A₀ T] [CommRing T'] [Algebra A₀ T'] (f : T →ₐ[A₀] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ)
    (P₀ : LevelModuliPackageAbs A₀ (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum)
    (x : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Raw P₀.B₀)
    (hx : (Quot.mk _ x : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Pt P₀.B₀) = P₀.univ)
    (hΔ : IsUnit x.level.2.2.curve.Δ)

    (a b c d : ℕ) (hγ : IsUnit (((a * d : ℤ) - (b * c : ℤ) : ℤ) : ZMod q)) :
    ∃ (y : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Raw P₀.B₀) (σ : P₀.B₀ ≃ₐ[A₀] P₀.B₀),
      y.curve = x.curve ∧ y.level.1 = x.level.1 ∧ y.level.2.1 = x.level.2.1 ∧
      y.level.2.2 =
        { curve := x.level.2.2.curve
          P := linComb (𝒢 P₀.B₀ x.level.2.2.curve hΔ) x.level.2.2.P x.level.2.2.Q a b
          Q := linComb (𝒢 P₀.B₀ x.level.2.2.curve hΔ) x.level.2.2.P x.level.2.2.Q c d } ∧
      (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.map (σ : P₀.B₀ →ₐ[A₀] P₀.B₀) P₀.univ =
        (Quot.mk _ y : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Pt P₀.B₀) := by
  classical

  let g : Matrix (Fin 2) (Fin 2) ℤ := !![(a : ℤ), (c : ℤ); (b : ℤ), (d : ℤ)]
  have hdet : g.det = (a * d : ℤ) - (b * c : ℤ) := by
    simp only [g, Matrix.det_fin_two_of]; ring
  have hg : IsUnit ((g.det : ℤ) : ZMod q) := by rw [hdet]; exact hγ
  have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le

  obtain ⟨g', hg', hgg', hg'g⟩ := Matrix.exists_isUnit_det_and_mul_map_castRingHom_zmod_eq_one q g hg

  obtain ⟨ρ, hρ⟩ := ModularCurve.LevelRelabelling.exists_problemAut_act_mk_eq_mk_relabel_of_isUnit_det_gamma0Pow
    q ℓ M' hq2 A₀ hℓ hM 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 hVC hCO g hg
  obtain ⟨ρ', hρ'⟩ := ModularCurve.LevelRelabelling.exists_problemAut_act_mk_eq_mk_relabel_of_isUnit_det_gamma0Pow
    q ℓ M' hq2 A₀ hℓ hM 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 hVC hCO g' hg'

  have hinv : ∀ (g₁ g₂ : Matrix (Fin 2) (Fin 2) ℤ), (g₁ * g₂).map (Int.castRingHom (ZMod q)) = 1 →
      ∀ (ρ₁ ρ₂ : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.ProblemAut),
        (∀ (T : Type) [CommRing T] [Algebra A₀ T] (x : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Raw T)
          (hΔ : IsUnit x.level.2.2.curve.Δ),
          ∃ x' : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Raw T,
            x'.curve = x.curve ∧ x'.level.1 = x.level.1 ∧ x'.level.2.1 = x.level.2.1 ∧
            x'.level.2.2 = LevelRelabelling.RawDrinfeldPair.relabel 𝒢 g₁ x.level.2.2 hΔ ∧
            ρ₁.act (Quot.mk _ x) = (Quot.mk _ x' : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Pt T)) →
        (∀ (T : Type) [CommRing T] [Algebra A₀ T] (x : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Raw T)
          (hΔ : IsUnit x.level.2.2.curve.Δ),
          ∃ x' : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Raw T,
            x'.curve = x.curve ∧ x'.level.1 = x.level.1 ∧ x'.level.2.1 = x.level.2.1 ∧
            x'.level.2.2 = LevelRelabelling.RawDrinfeldPair.relabel 𝒢 g₂ x.level.2.2 hΔ ∧
            ρ₂.act (Quot.mk _ x) = (Quot.mk _ x' : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Pt T)) →
        ∀ (T : Type) [CommRing T] [Algebra A₀ T] (y : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt T),
          ρ₂.act (ρ₁.act y) = y := by
    intro g₁ g₂ h12 ρ₁ ρ₂ h₁ h₂ T _ _ y
    induction y using Quot.ind with
    | mk x =>
      obtain ⟨-, -, hxL⟩ := x.isLevel
      have hxL' := hxL
      obtain ⟨-, hΔx, -⟩ := hxL'
      obtain ⟨x₁, h1c, h11, h121, h122, hρ1⟩ := h₁ T x hΔx
      have hΔ1 : IsUnit x₁.level.2.2.curve.Δ := by rw [h122]; exact hΔx
      obtain ⟨x₂, h2c, h21, h221, h222, hρ2⟩ := h₂ T x₁ hΔ1
      have key : ∀ (z : RawDrinfeldPair T) (hz : IsUnit z.curve.Δ),
          z = LevelRelabelling.RawDrinfeldPair.relabel 𝒢 g₁ x.level.2.2 hΔx →
          LevelRelabelling.RawDrinfeldPair.relabel 𝒢 g₂ z hz = x.level.2.2 := by
        rintro z hz rfl
        exact ModularCurve.LevelRelabelling.RawDrinfeldPair.relabel_relabel_eq_self_of_mul_map_eq_one_of_isLevel
          𝒢 h𝒢 h𝒢O hVC hCO q hq2 T _ x.level.2.2 hΔx hxL g₁ g₂ h12
      have hx2 : x₂ = x :=
        LevelComponent.Raw.ext' (h2c.trans h1c)
          (Prod.ext (h21.trans h11) (Prod.ext (h221.trans h121) ((h222.trans (key _ hΔ1 h122)))))
      show ρ₂.act (ρ₁.act (Quot.mk _ x)) = Quot.mk _ x
      rw [hρ1, hρ2, hx2]
  have h₁ := hinv g g' hgg' ρ ρ' hρ hρ'
  have h₂ := hinv g' g hg'g ρ' ρ hρ' hρ

  obtain ⟨σ, hσ, -⟩ := ModularCurve.LevelModuliPackageAbs.exists_algEquiv_map_univ_eq_act P₀ ρ ρ' h₁ h₂

  obtain ⟨y, hyc, hy1, hy21, hy22, hρy⟩ := hρ P₀.B₀ x hΔ
  refine ⟨y, σ, hyc, hy1, hy21, ?_, ?_⟩
  · rw [hy22]
    rfl
  · rw [hσ, ← hx]
    exact hρy

end S_ModularCurve_LevelModuliPackageAbs_exists_raw_linComb_algEquiv_map_univ_eq_gamma0Pow
end P2MW
export P2MW.S_ModularCurve_LevelModuliPackageAbs_exists_raw_linComb_algEquiv_map_univ_eq_gamma0Pow (solution)
