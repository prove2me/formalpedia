-- Prove2me | solution 1 for ModularCurve.JZeroNeronObjectAtP.LevelModel.pointEquivPlace_ofGenerator_eq_of_comp_eeta0_of_chartPin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/72f31168-f151-5819-b2e9-3f81684a2637

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_LevelModel
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import Definitions.Def_ModularCurve_FibreModel
import Theorems.Thm_AlgebraicCurve_CurveModel_pointEquivPlace_comp_eq_congrRingEquiv_of_fromSpecStalk_comp_eq
import Theorems.Thm_ModularCurve_adjoin_jBar_jNBar_eq_top
import Theorems.Thm_ModularCurve_IgusaScheme_qExpand_jq_mem_chartAlgFin_and_jFull_mem_chartAlg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_LevelModel_pointEquivPlace_ofGenerator_eq_of_comp_eeta0_of_chartPin
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "HahnSeries.ramScale_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

universe u v

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom Scheme.Hom.appLE_comp_appLE Scheme.Hom.appIso_hom' Scheme.SpecMap_stalkSpecializes_fromSpecStalk Spec IsIntegral Spec.map Scheme.ΓSpecIso_inv_naturality Scheme IsOpenImmersion genericPoint_eq_of_isOpenImmersion Scheme.SpecMap_stalkMap_fromSpecStalk Scheme.Hom.germ_stalkMap Scheme.Hom.appLE Scheme.ΓSpecIso Scheme.Hom.appLE_eq_app"
p2m_open "AlgebraicGeometry"

section FFMap

open CategoryTheory CategoryTheory.Limits

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (θ : X ⟶ Y) [IsIso θ]

private theorem e4_genericPoint_specializes :
    θ.base (genericPoint X) ⤳ genericPoint Y := by
  rw [genericPoint_eq_of_isOpenImmersion θ]

private noncomputable def e4_ffMap : Y.functionField ⟶ X.functionField :=
  Y.presheaf.stalkSpecializes (e4_genericPoint_specializes θ) ≫ θ.stalkMap (genericPoint X)

@[reassoc]
private theorem e4_SpecMap_ffMap_fromSpecStalk :
    Spec.map (e4_ffMap θ) ≫ Y.fromSpecStalk (genericPoint Y) = X.fromSpecStalk (genericPoint X) ≫ θ := by
  rw [e4_ffMap, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

private theorem e4_germ_ffMap (U : Y.Opens) (hU : genericPoint Y ∈ U) :
    Y.presheaf.germ U (genericPoint Y) hU ≫ e4_ffMap θ =
      θ.app U ≫ X.presheaf.germ (θ ⁻¹ᵁ U) (genericPoint X)
        (show θ.base (genericPoint X) ∈ U by rwa [genericPoint_eq_of_isOpenImmersion θ]) := by
  rw [e4_ffMap, TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.Hom.germ_stalkMap]

private theorem e4_ffMap_germ_apply (U : Y.Opens) (hU : genericPoint Y ∈ U) (s : Γ(Y, U)) :
    e4_ffMap θ (Y.presheaf.germ U (genericPoint Y) hU s) =
      X.presheaf.germ (θ ⁻¹ᵁ U) (genericPoint X)
        (show θ.base (genericPoint X) ∈ U by rwa [genericPoint_eq_of_isOpenImmersion θ]) (θ.app U s) := by
  rw [← CommRingCat.comp_apply, e4_germ_ffMap]; rfl

private theorem e4_ffMap_germ_of_eq {Z : Scheme.{u}} (g₂ : Y ⟶ Z) (g₁ : X ⟶ Z) (e : g₁ = θ ≫ g₂)
    (U : Z.Opens) (h₂ : genericPoint Y ∈ g₂ ⁻¹ᵁ U) (h₁ : genericPoint X ∈ g₁ ⁻¹ᵁ U) (s : Γ(Z, U)) :
    e4_ffMap θ (Y.presheaf.germ (g₂ ⁻¹ᵁ U) (genericPoint Y) h₂ (g₂.app U s)) =
      X.presheaf.germ (g₁ ⁻¹ᵁ U) (genericPoint X) h₁ (g₁.app U s) := by
  subst e
  rw [e4_ffMap_germ_apply]
  rfl

end FFMap

end AlgebraicGeometry

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.congrRingEquiv Place.congrRingEquiv_toValuationSubring baseToFunctionField CurveModel CurveModel.incl₀ CurveModel.X₀ CurveModel.XOverlap CurveModel.f₀ CurveModel.glued CurveModel.ι₀ CurveModel.ιU_genericPoint CurveModel.gluedFunctionFieldEquiv CurveModel.thetaHom_algebraMap CurveModel.ffEquiv_symm_germ_appIso_inv CurveModel.ofGenerator CurveModel.chartRing CurveModel.pointEquivPlace_comp_eq_congrRingEquiv_of_fromSpecStalk_comp_eq"
namespace CurveModel
p2m_export "AlgebraicCurve.CurveModel" "pointEquivPlace toBase C ffEquiv ffEquiv_algebraMap incl₀ X₀ XOverlap f₀ glued ι₀ ιU_genericPoint gluedFunctionFieldEquiv germ_res_secTop thetaHom_algebraMap ffEquiv_symm_germ_appIso_inv ofGenerator chartRing coe_chartIncl pointEquivPlace_comp_eq_congrRingEquiv_of_fromSpecStalk_comp_eq"
p2m_open "AlgebraicCurve.CurveModel AlgebraicCurve"

section FFPull

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_JZeroNeronObjectAtP_LevelModel_pointEquivPlace_ofGenerator_eq_of_comp_eeta0_of_chartPin.AlgebraicGeometry"

variable {K : Type u} [Field K] {L₁ : Type v} [Field L₁] [Algebra K L₁] {L₂ : Type v} [Field L₂] [Algebra K L₂]
  (M₁ : CurveModel K L₁) (M₂ : CurveModel K L₂) (θ : M₁.C ⟶ M₂.C) [IsIso θ]

private noncomputable def e4_ffPull : L₂ →+* L₁ :=
  M₁.ffEquiv.symm.toRingHom.comp ((e4_ffMap θ).hom.comp M₂.ffEquiv.toRingHom)

private theorem e4_ffPull_apply (f : L₂) : e4_ffPull M₁ M₂ θ f = M₁.ffEquiv.symm (e4_ffMap θ (M₂.ffEquiv f)) := rfl

private theorem e4_ffMap_baseToFunctionField (hθ : θ ≫ M₂.toBase = M₁.toBase) (a : K) :
    e4_ffMap θ (baseToFunctionField M₂.toBase a) = baseToFunctionField M₁.toBase a := by
  simp only [baseToFunctionField, RingHom.comp_apply]
  erw [e4_ffMap_germ_apply θ ⊤ trivial]
  rw [← hθ]
  rfl

private theorem e4_ffPull_algebraMap (hθ : θ ≫ M₂.toBase = M₁.toBase) (a : K) :
    e4_ffPull M₁ M₂ θ (algebraMap K L₂ a) = algebraMap K L₁ a := by
  rw [e4_ffPull_apply, M₂.ffEquiv_algebraMap, e4_ffMap_baseToFunctionField M₁ M₂ θ hθ,
    ← M₁.ffEquiv_algebraMap, RingEquiv.symm_apply_apply]

private theorem e4_fromSpecStalk_comp_eq_of_ffPull_eq (φ : L₁ ≃+* L₂)
    (hΦ : ∀ f, e4_ffPull M₁ M₂ θ f = φ.symm f) :
    M₁.C.fromSpecStalk (genericPoint M₁.C) ≫ θ =
      Spec.map (CommRingCat.ofHom
        (M₁.ffEquiv.toRingHom.comp (φ.symm.toRingHom.comp M₂.ffEquiv.symm.toRingHom))) ≫
        M₂.C.fromSpecStalk (genericPoint M₂.C) := by
  rw [← e4_SpecMap_ffMap_fromSpecStalk θ]
  congr 2
  ext z
  obtain ⟨w, rfl⟩ := M₂.ffEquiv.surjective z
  have h := hΦ w
  rw [e4_ffPull_apply, RingEquiv.symm_apply_eq] at h
  rw [h]
  simp

end FFPull

end AlgebraicCurve.CurveModel

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom Scheme.Hom.appLE_comp_appLE Scheme.Hom.appIso_hom' Scheme.SpecMap_stalkSpecializes_fromSpecStalk Spec IsIntegral Spec.map Scheme.ΓSpecIso_inv_naturality Scheme IsOpenImmersion genericPoint_eq_of_isOpenImmersion Scheme.SpecMap_stalkMap_fromSpecStalk Scheme.Hom.germ_stalkMap Scheme.Hom.appLE Scheme.ΓSpecIso Scheme.Hom.appLE_eq_app"
p2m_open "AlgebraicGeometry"

section ChartGerm

open CategoryTheory CategoryTheory.Limits

private theorem e4_germ_app_chart_eq {X Z : Scheme.{u}} {A B : CommRingCat.{u}}
    (ι : Spec A ⟶ Z) [IsOpenImmersion ι] (j : Spec B ⟶ X) [IsOpenImmersion j]
    (g : X ⟶ Z) (ψ : A ⟶ B) (hg : j ≫ g = Spec.map ψ ≫ ι)
    (x : X) (hx : x ∈ g ⁻¹ᵁ (ι ''ᵁ ⊤)) (hx' : x ∈ j ''ᵁ ⊤) (a : A) :
    X.presheaf.germ (g ⁻¹ᵁ (ι ''ᵁ ⊤)) x hx (g.app (ι ''ᵁ ⊤) ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso A).inv a))) =
      X.presheaf.germ (j ''ᵁ ⊤) x hx' ((j.appIso ⊤).inv ((Scheme.ΓSpecIso B).inv (ψ a))) := by
  have hWV : j ''ᵁ ⊤ ≤ g ⁻¹ᵁ (ι ''ᵁ ⊤) := by
    rintro _ ⟨p, -, rfl⟩
    have e : (j ≫ g).base p = (Spec.map ψ ≫ ι).base p := by rw [hg]
    show (j ≫ g).base p ∈ ι ''ᵁ ⊤
    rw [e]
    exact ⟨_, trivial, rfl⟩
  set σ : Γ(Z, ι ''ᵁ ⊤) := (ι.appIso ⊤).inv ((Scheme.ΓSpecIso A).inv a) with hσ

  have h1 : X.presheaf.germ (g ⁻¹ᵁ (ι ''ᵁ ⊤)) x hx (g.app (ι ''ᵁ ⊤) σ) =
      X.presheaf.germ (j ''ᵁ ⊤) x hx' (g.appLE (ι ''ᵁ ⊤) (j ''ᵁ ⊤) hWV σ) := by
    rw [Scheme.Hom.appLE, CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply]

  have h2 : (j.appIso ⊤).hom (g.appLE (ι ''ᵁ ⊤) (j ''ᵁ ⊤) hWV σ) = (Scheme.ΓSpecIso B).inv (ψ a) := by
    rw [Scheme.Hom.appIso_hom']
    change (g.appLE (ι ''ᵁ ⊤) (j ''ᵁ ⊤) hWV ≫ j.appLE (j ''ᵁ ⊤) ⊤ (j.preimage_image_eq ⊤).ge) σ = _
    rw [Scheme.Hom.appLE_comp_appLE]

    have key : ∀ (f : Spec B ⟶ Z) (e : (⊤ : (Spec B).Opens) ≤ f ⁻¹ᵁ (ι ''ᵁ ⊤)), f = Spec.map ψ ≫ ι →
        f.appLE (ι ''ᵁ ⊤) ⊤ e σ = (Scheme.ΓSpecIso B).inv (ψ a) := by
      rintro f e rfl
      rw [← Scheme.Hom.appLE_comp_appLE _ _ (ι ''ᵁ ⊤) ⊤ ⊤ (ι.preimage_image_eq ⊤).ge le_top,
        CommRingCat.comp_apply, hσ, ← Scheme.Hom.appIso_hom', Iso.inv_hom_id_apply]
      have happ : (Spec.map ψ).appLE ⊤ ⊤ le_top = (Spec.map ψ).appTop := Scheme.Hom.appLE_eq_app _
      rw [happ, ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
    exact key _ _ hg
  have h3 : g.appLE (ι ''ᵁ ⊤) (j ''ᵁ ⊤) hWV σ = (j.appIso ⊤).inv ((Scheme.ΓSpecIso B).inv (ψ a)) := by
    rw [← h2, Iso.hom_inv_id_apply]
  rw [h1, h3]

end ChartGerm

end AlgebraicGeometry

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.congrRingEquiv Place.congrRingEquiv_toValuationSubring baseToFunctionField CurveModel CurveModel.incl₀ CurveModel.X₀ CurveModel.XOverlap CurveModel.f₀ CurveModel.glued CurveModel.ι₀ CurveModel.ιU_genericPoint CurveModel.gluedFunctionFieldEquiv CurveModel.thetaHom_algebraMap CurveModel.ffEquiv_symm_germ_appIso_inv CurveModel.ofGenerator CurveModel.chartRing CurveModel.pointEquivPlace_comp_eq_congrRingEquiv_of_fromSpecStalk_comp_eq"
namespace CurveModel
p2m_export "AlgebraicCurve.CurveModel" "pointEquivPlace toBase C ffEquiv ffEquiv_algebraMap incl₀ X₀ XOverlap f₀ glued ι₀ ιU_genericPoint gluedFunctionFieldEquiv germ_res_secTop thetaHom_algebraMap ffEquiv_symm_germ_appIso_inv ofGenerator chartRing coe_chartIncl pointEquivPlace_comp_eq_congrRingEquiv_of_fromSpecStalk_comp_eq"
p2m_open "AlgebraicCurve.CurveModel AlgebraicCurve"

section ChartGermReading

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_JZeroNeronObjectAtP_LevelModel_pointEquivPlace_ofGenerator_eq_of_comp_eeta0_of_chartPin.AlgebraicGeometry IntermediateField"

variable (K : Type u) [Field K] [CharZero K] {L : Type u} [Field L] [Algebra K L] (t : L)
  [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]

omit [CharZero K] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L] in

private theorem e4_genericPoint_mem_image_ι₀ : genericPoint (CurveModel.glued K t) ∈ CurveModel.ι₀ K t ''ᵁ ⊤ :=
  ⟨(CurveModel.f₀ K t).base (genericPoint (CurveModel.XOverlap K t)), trivial, CurveModel.ιU_genericPoint K t⟩

omit [CharZero K] [FiniteDimensional K⟮t⁻¹⟯ L] in

private theorem e4_gluedFunctionFieldEquiv_symm_germ_chart (r : chartRing K ({t} : Set L))
    (hη : genericPoint (CurveModel.glued K t) ∈ CurveModel.ι₀ K t ''ᵁ ⊤) :
    (CurveModel.gluedFunctionFieldEquiv K t).symm
      ((CurveModel.glued K t).presheaf.germ (CurveModel.ι₀ K t ''ᵁ ⊤) (genericPoint (CurveModel.glued K t)) hη
        (((CurveModel.ι₀ K t).appIso ⊤).inv
          ((Scheme.ΓSpecIso (CommRingCat.of (chartRing K ({t} : Set L)))).inv r))) = (r : L) := by
  rw [CurveModel.ffEquiv_symm_germ_appIso_inv K t (chartRing K ({t} : Set L)) (CurveModel.ι₀ K t)
    (CurveModel.incl₀ K t) (fun b => coe_chartIncl K _ b) rfl ⊤ _ (genericPoint (CurveModel.X₀ K t)) trivial hη]

  exact CurveModel.thetaHom_algebraMap K t _ (CurveModel.incl₀ K t) (fun b => coe_chartIncl K _ b) _ r

omit [CharZero K] [FiniteDimensional K⟮t⁻¹⟯ L] in

private theorem e4_ffEquiv_symm_germ_chart
    {Z : Scheme.{u}} {A : CommRingCat.{u}} (ι : Spec A ⟶ Z) [IsOpenImmersion ι]
    (g : CurveModel.glued K t ⟶ Z) (ψ : A →+* chartRing K ({t} : Set L))
    (hg : CurveModel.ι₀ K t ≫ g = Spec.map (CommRingCat.ofHom ψ) ≫ ι)
    (hη : genericPoint (CurveModel.glued K t) ∈ g ⁻¹ᵁ (ι ''ᵁ ⊤)) (a : A) :
    (CurveModel.gluedFunctionFieldEquiv K t).symm
      ((CurveModel.glued K t).presheaf.germ (g ⁻¹ᵁ (ι ''ᵁ ⊤)) (genericPoint _) hη
        (g.app (ι ''ᵁ ⊤) ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso A).inv a)))) = (ψ a : L) := by
  have hη' := e4_genericPoint_mem_image_ι₀ K t (L := L)
  rw [e4_germ_app_chart_eq ι (CurveModel.ι₀ K t) g (CommRingCat.ofHom ψ) hg _ hη hη' a]
  exact e4_gluedFunctionFieldEquiv_symm_germ_chart K t (ψ a) hη'

omit [CharZero K] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L] in

private theorem e4_genericPoint_mem_preimage
    {Z : Scheme.{u}} {A : CommRingCat.{u}} (ι : Spec A ⟶ Z) [IsOpenImmersion ι]
    (g : CurveModel.glued K t ⟶ Z) (ψ : A →+* chartRing K ({t} : Set L))
    (hg : CurveModel.ι₀ K t ≫ g = Spec.map (CommRingCat.ofHom ψ) ≫ ι) :
    genericPoint (CurveModel.glued K t) ∈ g ⁻¹ᵁ (ι ''ᵁ ⊤) := by
  obtain ⟨p, -, hp⟩ := e4_genericPoint_mem_image_ι₀ K t (L := L)
  have e : (CurveModel.ι₀ K t ≫ g).base p = (Spec.map (CommRingCat.ofHom ψ) ≫ ι).base p := by rw [hg]
  show g.base (genericPoint (CurveModel.glued K t)) ∈ ι ''ᵁ ⊤
  rw [← hp]
  show (CurveModel.ι₀ K t ≫ g).base p ∈ ι ''ᵁ ⊤
  rw [e]
  exact ⟨_, trivial, rfl⟩

end ChartGermReading

end AlgebraicCurve.CurveModel

section Algebra

private theorem e4_eq_self_of_adjoin_eq_top {K L : Type*} [Field K] [Field L] [Algebra K L]
    (Φ : L →+* L) (hΦ : ∀ a : K, Φ (algebraMap K L a) = algebraMap K L a)
    (S : Set L) (hS : ∀ s ∈ S, Φ s = s) (htop : IntermediateField.adjoin K S = ⊤) (f : L) : Φ f = f := by
  let ΦA : L →ₐ[K] L := { Φ with commutes' := hΦ }
  let E : IntermediateField K L :=
    { AlgHom.equalizer ΦA (AlgHom.id K L) with
      inv_mem' := fun x (hx : Φ x = x) => show Φ x⁻¹ = x⁻¹ by rw [map_inv₀, hx] }
  have hle : IntermediateField.adjoin K S ≤ E := IntermediateField.adjoin_le_iff.mpr fun s hs => hS s hs
  rw [htop] at hle
  exact hle (show f ∈ (⊤ : IntermediateField K L) from IntermediateField.mem_top)

private theorem e4_congrRingEquiv_refl {K F : Type*} [Field K] [Field F] [Algebra K F]
    (he : ∀ a : K, (RingEquiv.refl F) (algebraMap K F a) = algebraMap K F a) (v : AlgebraicCurve.Place K F) :
    AlgebraicCurve.Place.congrRingEquiv (e := RingEquiv.refl F) (he := he) v = v := by
  apply AlgebraicCurve.Place.ext
  rw [AlgebraicCurve.Place.congrRingEquiv_toValuationSubring]
  ext x
  exact Iff.rfl

end Algebra

section Solution

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_JZeroNeronObjectAtP_LevelModel_pointEquivPlace_ofGenerator_eq_of_comp_eeta0_of_chartPin.AlgebraicGeometry AlgebraicCurve P2MW.S_ModularCurve_JZeroNeronObjectAtP_LevelModel_pointEquivPlace_ofGenerator_eq_of_comp_eeta0_of_chartPin.AlgebraicCurve ModularCurve ModularCurve.IgusaScheme ModularCurve.JZeroNeronObjectAtP ModularCurve.CharPModel"

open scoped TensorProduct

set_option maxHeartbeats 1600000 in

private theorem e4_main
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (M : LevelModel N₀ q A)
    (htrans : Transcendental (AlgebraicClosure ℚ) (CharPModel.jBar N₀))
    [hne : Fact (CharPModel.jBar N₀ ≠ 0)]
    [hfd : FiniteDimensional
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({CharPModel.jBar N₀} : Set (modularFunctionFieldBar N₀)))
      (modularFunctionFieldBar N₀)]
    [hfd_inv : FiniteDimensional
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({(CharPModel.jBar N₀)⁻¹} : Set (modularFunctionFieldBar N₀)))
      (modularFunctionFieldBar N₀)]
    (eFin : (AlgebraicClosure ℚ) ⊗[↥(GaloisRep.ratLocalizedAt q)] ↥(chartAlgFin N₀ q)
        ≃ₐ[AlgebraicClosure ℚ]
      ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ)
        ({CharPModel.jBar N₀} : Set (modularFunctionFieldBar N₀))))
    (hFin : ∀ b : chartAlgFin N₀ q, ((eFin (1 ⊗ₜ b) :
        ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ)
        ({CharPModel.jBar N₀} : Set (modularFunctionFieldBar N₀)))) : modularFunctionFieldBar N₀)
      = (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (b : ↥(modularFunctionFieldFull N₀)).2⟩ : modularFunctionFieldBar N₀))
    (eη : (CurveModel.ofGenerator (AlgebraicClosure ℚ) (CharPModel.jBar N₀) htrans).C ⟶
      pullback (igusaTo N₀ q) (Spec.map (CommRingCat.ofHom
        (algebraMap ↥(GaloisRep.ratLocalizedAt q) (AlgebraicClosure ℚ))))) [IsIso eη]
    (heη : eη ≫ pullback.snd (igusaTo N₀ q) _ = (CurveModel.ofGenerator (AlgebraicClosure ℚ) (CharPModel.jBar N₀) htrans).toBase)
    (hchartFin : AlgebraicCurve.CurveModel.ι₀ (AlgebraicClosure ℚ)
        (CharPModel.jBar N₀) ≫ eη ≫ pullback.fst (igusaTo N₀ q) _ =
      Spec.map (CommRingCat.ofHom (eFin.toAlgHom.toRingHom.comp
        (Algebra.TensorProduct.includeRight
          (R := ↥(GaloisRep.ratLocalizedAt q)) (A := AlgebraicClosure ℚ)
          (B := ↥(chartAlgFin N₀ q))).toRingHom)) ≫ ModularCurve.IgusaScheme.ιFin N₀ q)
    (x : {q' : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ (CurveModel.ofGenerator (AlgebraicClosure ℚ) (CharPModel.jBar N₀) htrans).C //
      q' ≫ (CurveModel.ofGenerator (AlgebraicClosure ℚ) (CharPModel.jBar N₀) htrans).toBase = 𝟙 _})
    (x₀ : {q' : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ M.Meta₀.C // q' ≫ M.Meta₀.toBase = 𝟙 _})
    (hxx₀ : x.1 ≫ eη = x₀.1 ≫ M.eeta₀) :
    (CurveModel.ofGenerator (AlgebraicClosure ℚ) (CharPModel.jBar N₀) htrans).pointEquivPlace x =
      M.Meta₀.pointEquivPlace x₀ := by

  let θ : (CurveModel.ofGenerator (AlgebraicClosure ℚ) (CharPModel.jBar N₀) htrans).C ⟶ M.Meta₀.C := eη ≫ inv M.eeta₀
  haveI : IsIso θ := IsIso.comp_isIso
  have hθ : θ ≫ M.Meta₀.toBase = (CurveModel.ofGenerator (AlgebraicClosure ℚ) (CharPModel.jBar N₀) htrans).toBase := by
    simp only [θ, Category.assoc]
    rw [← M.heeta₀, IsIso.inv_hom_id_assoc, heη]
  have hθg : eη ≫ pullback.fst (igusaTo N₀ q) _ = θ ≫ (M.eeta₀ ≫ pullback.fst (igusaTo N₀ q) (genPt q)) := by
    simp [θ]

  have hfix : ∀ a : ↥(chartAlgFin N₀ q),
      CurveModel.e4_ffPull (CurveModel.ofGenerator (AlgebraicClosure ℚ) (CharPModel.jBar N₀) htrans) M.Meta₀ θ
        ⟨coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (a : ↥(modularFunctionFieldFull N₀)).2⟩ =
        ⟨coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (a : ↥(modularFunctionFieldFull N₀)).2⟩ := by
    intro a

    have hpin : M.Meta₀.ffEquiv.symm
        (M.Meta₀.C.germToFunctionField
          ((M.eeta₀ ≫ pullback.fst (IgusaScheme.igusaTo N₀ q) (genPt q)) ⁻¹ᵁ ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤))
          (((M.eeta₀ ≫ pullback.fst (IgusaScheme.igusaTo N₀ q) (genPt q)).app ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤)).hom
            (((IgusaScheme.ιFin N₀ q).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin N₀ q))).inv a)))) =
        ⟨coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (a : ↥(modularFunctionFieldFull N₀)).2⟩ :=
      Subtype.ext (M.Meta₀_pin a)
    have hpin' := (RingEquiv.eq_symm_apply _).mp hpin.symm

    rw [CurveModel.e4_ffPull_apply, hpin']

    have h₁ : genericPoint (CurveModel.ofGenerator (AlgebraicClosure ℚ) (CharPModel.jBar N₀) htrans).C ∈
        (eη ≫ pullback.fst (igusaTo N₀ q) _) ⁻¹ᵁ ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤) :=
      CurveModel.e4_genericPoint_mem_preimage (AlgebraicClosure ℚ) (CharPModel.jBar N₀)
        (IgusaScheme.ιFin N₀ q) _ _ hchartFin
    erw [AlgebraicGeometry.e4_ffMap_germ_of_eq θ (M.eeta₀ ≫ pullback.fst (IgusaScheme.igusaTo N₀ q) (genPt q))
      (eη ≫ pullback.fst (igusaTo N₀ q) _) hθg ((IgusaScheme.ιFin N₀ q) ''ᵁ ⊤) _ h₁]

    erw [CurveModel.e4_ffEquiv_symm_germ_chart (AlgebraicClosure ℚ) (CharPModel.jBar N₀)
      (IgusaScheme.ιFin N₀ q) _ _ hchartFin h₁ a]
    exact hFin a

  have hΦ : ∀ f, CurveModel.e4_ffPull (CurveModel.ofGenerator (AlgebraicClosure ℚ) (CharPModel.jBar N₀) htrans) M.Meta₀ θ f =
      (RingEquiv.refl (modularFunctionFieldBar N₀)).symm f := by
    intro f
    refine e4_eq_self_of_adjoin_eq_top (K := AlgebraicClosure ℚ) (CurveModel.e4_ffPull _ M.Meta₀ θ)
      (CurveModel.e4_ffPull_algebraMap _ M.Meta₀ θ hθ) _ ?_ (ModularCurve.adjoin_jBar_jNBar_eq_top (AlgebraicClosure ℚ) N₀) f
    rintro s (rfl | rfl)
    · exact hfix (IgusaScheme.jChartFin N₀ q)
    · exact hfix ⟨⟨qExpand ℚ N₀ jq, jqd_mem_full N₀ (dvd_refl N₀)⟩,
        (IgusaScheme.qExpand_jq_mem_chartAlgFin_and_jFull_mem_chartAlg N₀ q N₀ (dvd_refl N₀)).2.1⟩

  have hθgen := CurveModel.e4_fromSpecStalk_comp_eq_of_ffPull_eq _ M.Meta₀ θ (RingEquiv.refl _) hΦ
  have hT := AlgebraicCurve.CurveModel.pointEquivPlace_comp_eq_congrRingEquiv_of_fromSpecStalk_comp_eq
    (CurveModel.ofGenerator (AlgebraicClosure ℚ) (CharPModel.jBar N₀) htrans) M.Meta₀ (RingEquiv.refl _) (fun _ => rfl) θ hθ hθgen x
  rw [e4_congrRingEquiv_refl] at hT
  have hx₀ : (⟨x.1 ≫ θ, by rw [Category.assoc, hθ, x.2]⟩ :
      {q' : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ M.Meta₀.C // q' ≫ M.Meta₀.toBase = 𝟙 _}) = x₀ :=
    Subtype.ext (by simp only [θ]; rw [reassoc_of% hxx₀, IsIso.hom_inv_id, Category.comp_id])
  rw [hx₀] at hT
  exact hT.symm

set_option maxHeartbeats 1600000 in
theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (M : LevelModel N₀ q A)
    (htrans : Transcendental (AlgebraicClosure ℚ) (CharPModel.jBar N₀))
    [hne : Fact (CharPModel.jBar N₀ ≠ 0)]
    [hfd : FiniteDimensional
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({CharPModel.jBar N₀} : Set (modularFunctionFieldBar N₀)))
      (modularFunctionFieldBar N₀)]
    [hfd_inv : FiniteDimensional
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({(CharPModel.jBar N₀)⁻¹} : Set (modularFunctionFieldBar N₀)))
      (modularFunctionFieldBar N₀)]
    (eFin : (AlgebraicClosure ℚ) ⊗[↥(GaloisRep.ratLocalizedAt q)] ↥(chartAlgFin N₀ q)
        ≃ₐ[AlgebraicClosure ℚ]
      ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ)
        ({CharPModel.jBar N₀} : Set (modularFunctionFieldBar N₀))))
    (hFin : ∀ b : chartAlgFin N₀ q, ((eFin (1 ⊗ₜ b) :
        ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ)
        ({CharPModel.jBar N₀} : Set (modularFunctionFieldBar N₀)))) : modularFunctionFieldBar N₀)
      = (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull N₀)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (b : ↥(modularFunctionFieldFull N₀)).2⟩ : modularFunctionFieldBar N₀)) :
    let Mη : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar N₀) :=
      CurveModel.ofGenerator (AlgebraicClosure ℚ) (CharPModel.jBar N₀) htrans
    ∀ (eη : Mη.C ⟶ pullback (igusaTo N₀ q) (Spec.map (CommRingCat.ofHom
        (algebraMap ↥(GaloisRep.ratLocalizedAt q) (AlgebraicClosure ℚ))))) (_ : IsIso eη)
      (heη : eη ≫ pullback.snd (igusaTo N₀ q) _ = Mη.toBase)
      (hchartFin : AlgebraicCurve.CurveModel.ι₀ (AlgebraicClosure ℚ)
          (CharPModel.jBar N₀) ≫ eη ≫ pullback.fst (igusaTo N₀ q) _ =
        Spec.map (CommRingCat.ofHom (eFin.toAlgHom.toRingHom.comp
          (Algebra.TensorProduct.includeRight
            (R := ↥(GaloisRep.ratLocalizedAt q)) (A := AlgebraicClosure ℚ)
            (B := ↥(chartAlgFin N₀ q))).toRingHom)) ≫ ModularCurve.IgusaScheme.ιFin N₀ q)
      (x : {q' : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q' ≫ Mη.toBase = 𝟙 _})
      (x₀ : {q' : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ M.Meta₀.C // q' ≫ M.Meta₀.toBase = 𝟙 _}),
      x.1 ≫ eη = x₀.1 ≫ M.eeta₀ →
      Mη.pointEquivPlace x = M.Meta₀.pointEquivPlace x₀ := by
  intro Mη eη hiso heη hchartFin x x₀ hxx₀
  exact e4_main N₀ q A M htrans eFin hFin eη heη hchartFin x x₀ hxx₀

end Solution

#print axioms solution

end S_ModularCurve_JZeroNeronObjectAtP_LevelModel_pointEquivPlace_ofGenerator_eq_of_comp_eeta0_of_chartPin
end P2MW
export P2MW.S_ModularCurve_JZeroNeronObjectAtP_LevelModel_pointEquivPlace_ofGenerator_eq_of_comp_eeta0_of_chartPin (solution)
