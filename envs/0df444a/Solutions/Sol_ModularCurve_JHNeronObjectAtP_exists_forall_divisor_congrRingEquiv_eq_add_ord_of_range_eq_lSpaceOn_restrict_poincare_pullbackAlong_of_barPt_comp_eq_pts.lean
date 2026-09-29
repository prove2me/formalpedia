-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.exists_forall_divisor_congrRingEquiv_eq_add_ord_of_range_eq_lSpaceOn_restrict_poincare_pullbackAlong_of_barPt_comp_eq_pts
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/f17208ee-ad01-5617-8e96-237c69c8fb49

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_ModularCurve_XHHeckeOperator
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_PlacesOf
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicCurve_RelCartier
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_divisor_range_eq_lSpaceOn
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_eq_mul_and_eq_add_ord_of_presentations
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isPrincipal_sub_sub_of_presentations_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isPrincipal_sub_single_of_presentation_ker_pow
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_unit_range_eq_lSpaceOn_zero
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isFrameOn
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_pullback_invModule_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isIso_pullbackModuleComparison
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_mul_iso
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_one_iso
import Theorems.Thm_ModularCurve_XHDRModelAtP_nonempty_poincare_pullbackAlong_iso_ofPoint_tensor_ofPoint_idealModule_of_eq_comp_ajbar
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_IdealSheafModuleMaps
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_exists_forall_divisor_congrRingEquiv_eq_add_ord_of_range_eq_lSpaceOn_restrict_poincare_pullbackAlong_of_barPt_comp_eq_pts
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply"

set_option autoImplicit false
open scoped MatrixGroups
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve"

universe u

set_option linter.unusedSectionVars false

noncomputable section

namespace HDV

section Curve

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
  [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x]

def LinEq (E E' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    AlgebraicCurve.Divisor K X.functionField) : Prop :=
  letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
  ∃ g : X.functionField, g ≠ 0 ∧ ∀ v : AlgebraicCurve.Place K X.functionField, E v = E' v + v.ord g

def RF (M : X.Modules) (E : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    AlgebraicCurve.Divisor K X.functionField) : Prop :=
  letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
  ∃ φ : ∀ U : X.Opens, Γ(M, U) →+ (X.functionField : Type u),
    (∀ (U V : X.Opens) (h : V ≤ U), Nonempty V → ∀ m : Γ(M, U), φ V (M.presheaf.map (homOfLE h).op m) = φ U m) ∧
    (∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(M, U)), φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m) ∧
    (∀ U : X.Opens, Nonempty U → Function.Injective (φ U)) ∧
    (∀ U : X.Opens, IsAffineOpen U → Nonempty U →
      Set.range (φ U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) E : Set X.functionField))

def HasDiv (M : X.Modules) (E : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    AlgebraicCurve.Divisor K X.functionField) : Prop :=
  Scheme.Modules.IsInvertible M ∧ ∃ E₁, RF x M E₁ ∧ LinEq x E₁ E

variable {x}

theorem linEq_refl (E : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    AlgebraicCurve.Divisor K X.functionField) : LinEq x E E := by
  letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
  exact ⟨1, one_ne_zero, fun v => by simp⟩

theorem LinEq.symm {E E' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    AlgebraicCurve.Divisor K X.functionField} (h : LinEq x E E') : LinEq x E' E := by
  letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
  obtain ⟨g, hg, hE⟩ := h
  refine ⟨g⁻¹, inv_ne_zero hg, fun v => ?_⟩
  rw [hE v, AlgebraicCurve.Place.ord_inv]
  ring

theorem LinEq.trans {E E' E'' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    AlgebraicCurve.Divisor K X.functionField} (h : LinEq x E E') (h' : LinEq x E' E'') : LinEq x E E'' := by
  letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
  obtain ⟨g, hg, hE⟩ := h
  obtain ⟨g', hg', hE'⟩ := h'
  refine ⟨g * g', mul_ne_zero hg hg', fun v => ?_⟩
  rw [hE v, hE' v, AlgebraicCurve.Place.ord_mul _ hg hg']
  ring

theorem LinEq.add {E₁ E₁' E₂ E₂' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    AlgebraicCurve.Divisor K X.functionField} (h₁ : LinEq x E₁ E₁') (h₂ : LinEq x E₂ E₂') :
    LinEq x (E₁ + E₂) (E₁' + E₂') := by
  letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
  obtain ⟨g, hg, hE⟩ := h₁
  obtain ⟨g', hg', hE'⟩ := h₂
  refine ⟨g * g', mul_ne_zero hg hg', fun v => ?_⟩
  rw [Finsupp.add_apply, Finsupp.add_apply, hE v, hE' v, AlgebraicCurve.Place.ord_mul _ hg hg']
  ring

theorem LinEq.neg {E E' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    AlgebraicCurve.Divisor K X.functionField} (h : LinEq x E E') : LinEq x (-E) (-E') := by
  letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
  obtain ⟨g, hg, hE⟩ := h
  refine ⟨g⁻¹, inv_ne_zero hg, fun v => ?_⟩
  rw [Finsupp.neg_apply, Finsupp.neg_apply, hE v, AlgebraicCurve.Place.ord_inv]
  ring

theorem LinEq.zsmul {E E' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    AlgebraicCurve.Divisor K X.functionField} (n : ℤ) (h : LinEq x E E') : LinEq x (n • E) (n • E') := by
  letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
  obtain ⟨g, hg, hE⟩ := h
  refine ⟨g ^ n, zpow_ne_zero n hg, fun v => ?_⟩
  rw [Finsupp.smul_apply, Finsupp.smul_apply, hE v, AlgebraicCurve.Place.ord_zpow, smul_eq_mul, smul_eq_mul]
  ring

theorem exists_rf (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) : ∃ E, RF x M E := by
  haveI : IsSeparated x := inferInstance
  haveI : QuasiCompact x := inferInstance
  obtain ⟨D, φ, h1, h2, h3, h4, -⟩ := Scheme.Modules.IsInvertible.exists_divisor_range_eq_lSpaceOn x M hM
  exact ⟨D, φ, h1, fun U _ a m => h2 U a m, h3, h4⟩

theorem hasDiv_of_rf {M : X.Modules} (hM : Scheme.Modules.IsInvertible M)
    {E : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.Divisor K X.functionField} (h : RF x M E) : HasDiv x M E :=
  ⟨hM, E, h, linEq_refl E⟩

omit [IsAlgClosed K] [IsProper x] [SmoothOfRelativeDimension 1 x] in
theorem ne_zero_of_isFrameOn {M : X.Modules} {U : X.Opens} [Nontrivial Γ(X, U)] {s : Γ(M, U)}
    (hs : Scheme.Modules.IsFrameOn s U) : s ≠ 0 := by
  intro h
  have h1 : (1 : Γ(X, U)) • M.presheaf.map (homOfLE (le_refl U)).op s = 0 := by
    rw [h, map_zero, smul_zero]
  have := (hs.smul_eq_zero_iff le_rfl le_rfl (1 : Γ(X, U))).mp h1
  exact one_ne_zero this

omit [IsAlgClosed K] [IsProper x] [SmoothOfRelativeDimension 1 x] in
theorem exists_ne_zero_of_isInvertible {M : X.Modules} (hM : Scheme.Modules.IsInvertible M) :
    ∃ (U : X.Opens) (m : Γ(M, U)), m ≠ 0 := by
  obtain ⟨U, s, hη, hs⟩ := hM.exists_isFrameOn (genericPoint X)
  haveI : Nonempty U := ⟨⟨_, hη⟩⟩
  exact ⟨U, s, ne_zero_of_isFrameOn hs⟩

theorem RF.linEq {M : X.Modules} (hM : Scheme.Modules.IsInvertible M)
    {E E' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.Divisor K X.functionField} (h : RF x M E) (h' : RF x M E') : LinEq x E E' := by
  obtain ⟨φ, h1, h2, h3, h4⟩ := h
  obtain ⟨φ', h1', h2', h3', h4'⟩ := h'
  obtain ⟨g, hg, -, hD, -⟩ := Scheme.Modules.exists_eq_mul_and_eq_add_ord_of_presentations x M E E' φ φ' h1 h1'
    (fun U _ a m => h2 U a m) (fun U _ a m => h2' U a m) h3 h3' h4 h4' (exists_ne_zero_of_isInvertible hM)
  exact ⟨g, hg, hD⟩

theorem HasDiv.linEq_of_rf {M : X.Modules} {E E₂ : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.Divisor K X.functionField} (h : HasDiv x M E) (h₂ : RF x M E₂) : LinEq x E₂ E := by
  obtain ⟨hM, E₁, h₁, hl⟩ := h
  exact LinEq.trans (RF.linEq hM h₂ h₁) hl

theorem HasDiv.congr {M : X.Modules} {E E' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.Divisor K X.functionField} (h : HasDiv x M E) (hl : LinEq x E E') : HasDiv x M E' := by
  obtain ⟨hM, E₁, h₁, hl₁⟩ := h
  exact ⟨hM, E₁, h₁, LinEq.trans hl₁ hl⟩

omit [IsAlgClosed K] [IsProper x] [SmoothOfRelativeDimension 1 x] in
theorem app_naturality {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens} (h : V ≤ U) (m : Γ(M, U)) :
    N.presheaf.map (homOfLE h).op (φ.app U m) = φ.app V (M.presheaf.map (homOfLE h).op m) := by
  have := (φ.mapPresheaf).naturality (homOfLE h).op
  exact (congrFun (congrArg (fun f => (ConcreteCategory.hom f : Γ(M, U) → Γ(N, V))) this) m).symm

omit [IsAlgClosed K] [IsProper x] [SmoothOfRelativeDimension 1 x] in
theorem app_bijective_of_iso {M N : X.Modules} (e : M ≅ N) (U : X.Opens) : Function.Bijective (e.hom.app U) := by
  refine Function.bijective_iff_has_inverse.2 ⟨e.inv.app U, fun y => ?_, fun y => ?_⟩
  · change (e.hom.app U ≫ e.inv.app U) y = y
    rw [← Scheme.Modules.Hom.comp_app, e.hom_inv_id, Scheme.Modules.Hom.id_app]; rfl
  · change (e.inv.app U ≫ e.hom.app U) y = y
    rw [← Scheme.Modules.Hom.comp_app, e.inv_hom_id, Scheme.Modules.Hom.id_app]; rfl

theorem RF.of_iso {M N : X.Modules} (e : M ≅ N) {E : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.Divisor K X.functionField} (h : RF x M E) : RF x N E := by
  letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
  obtain ⟨φ, h1, h2, h3, h4⟩ := h
  refine ⟨fun U => (φ U).comp (e.inv.app U).hom, ?_, ?_, ?_, ?_⟩
  · intro U V hVU hV m
    show φ V (e.inv.app V (N.presheaf.map (homOfLE hVU).op m)) = φ U (e.inv.app U m)
    rw [← app_naturality, h1 U V hVU hV]
  · intro U _ a m
    show φ U (e.inv.app U (a • m)) = _ * φ U (e.inv.app U m)
    rw [Scheme.Modules.Hom.app_smul, h2]
  · intro U hU
    exact (h3 U hU).comp (app_bijective_of_iso e.symm U).1
  · intro U hU hne
    rw [← h4 U hU hne]
    show Set.range (φ U ∘ e.inv.app U) = Set.range (φ U)
    exact (app_bijective_of_iso e.symm U).2.range_comp _

theorem isInvertible_of_iso {M N : X.Modules} (e : M ≅ N) (hM : Scheme.Modules.IsInvertible M) :
    Scheme.Modules.IsInvertible N := by
  refine ⟨fun y => ?_⟩
  obtain ⟨U, hxU, ⟨eU⟩⟩ := hM.1 y
  exact ⟨U, hxU, ⟨((Scheme.Modules.pullback U.ι).mapIso e).symm ≪≫ eU⟩⟩

theorem HasDiv.of_iso {M N : X.Modules} (e : M ≅ N) {E : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.Divisor K X.functionField} (h : HasDiv x M E) : HasDiv x N E := by
  obtain ⟨hM, E₁, h₁, hl⟩ := h
  exact ⟨isInvertible_of_iso e hM, E₁, RF.of_iso e h₁, hl⟩

theorem HasDiv.tensor {M N : X.Modules} {E E' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.Divisor K X.functionField} (h : HasDiv x M E) (h' : HasDiv x N E') :
    HasDiv x (M ⊗ N) (E + E') := by
  letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
  obtain ⟨hM, E₁, ⟨φ, h1, h2, h3, h4⟩, l₁⟩ := h
  obtain ⟨hN, E₁', ⟨φ', h1', h2', h3', h4'⟩, l₁'⟩ := h'
  have hMN := hM.tensor hN
  obtain ⟨E'', ⟨φ'', h1'', h2'', h3'', h4''⟩⟩ := exists_rf (x := x) (M ⊗ N) hMN
  obtain ⟨f, hf, hfv⟩ := Scheme.Modules.isPrincipal_sub_sub_of_presentations_tensor x M N hM hN E₁ E₁' E''
    φ h1 (fun U _ a m => h2 U a m) h3 h4 φ' h1' (fun U _ a m => h2' U a m) h3' h4'
    φ'' h1'' (fun U _ a m => h2'' U a m) h3'' h4''
  refine ⟨hMN, E'', ⟨φ'', h1'', h2'', h3'', h4''⟩, LinEq.trans ?_ (LinEq.add l₁ l₁')⟩
  refine ⟨f, hf, fun v => ?_⟩
  have := hfv v
  simp only [Finsupp.sub_apply] at this
  linarith [Finsupp.add_apply E₁ E₁' v]

theorem hasDiv_unit : HasDiv x (𝟙_ X.Modules) 0 := by
  obtain ⟨φ, -, h1, h2, h3, h4⟩ := Scheme.Modules.exists_unit_range_eq_lSpaceOn_zero x
  exact ⟨Scheme.Modules.isInvertible_unit X, 0, ⟨φ, h1, fun U _ a m => h2 U a m, h3, h4⟩, linEq_refl _⟩

theorem HasDiv.of_tensor_iso_unit {M N : X.Modules} (e : M ⊗ N ≅ 𝟙_ X.Modules)
    {E : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.Divisor K X.functionField} (h : HasDiv x M E) (hN : Scheme.Modules.IsInvertible N) :
    HasDiv x N (-E) := by
  letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
  obtain ⟨E₁', hrf⟩ := exists_rf (x := x) N hN
  have ht : HasDiv x (M ⊗ N) (E + E₁') := HasDiv.tensor h (hasDiv_of_rf hN hrf)
  have h0 : HasDiv x (M ⊗ N) 0 := HasDiv.of_iso e.symm (hasDiv_unit (x := x))
  obtain ⟨-, E₂, hrf₂, hl₂⟩ := ht
  have hl0 : LinEq x E₂ 0 := HasDiv.linEq_of_rf h0 hrf₂
  obtain ⟨g, hg, hgv⟩ := LinEq.trans (LinEq.symm hl₂) hl0
  refine ⟨hN, E₁', hrf, ⟨g, hg, fun v => ?_⟩⟩
  have := hgv v
  rw [Finsupp.add_apply, Finsupp.zero_apply] at this
  rw [Finsupp.neg_apply]
  linarith

theorem hasDiv_ker_invModule_and_module (P : Spec (CommRingCat.of K) ⟶ X) (hP : P ≫ x = 𝟙 _)
    (v : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.Place K X.functionField)
    (hv : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      (algebraMap (X.presheaf.stalk (P.base (IsLocalRing.closedPoint K))) X.functionField).range =
        v.toValuationSubring.toSubring) :
    HasDiv x ((P.ker ^ 1).invModule) (Finsupp.single v 1) ∧ HasDiv x ((P.ker ^ 1).module) (-Finsupp.single v 1) := by
  letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
  haveI : IsSeparated x := inferInstance
  have hker : (P.ker ^ 1).IsInvertible := by
    rw [pow_one]
    exact Scheme.Hom.isInvertible_ker_of_comp_eq_id P hP
  have hinv := hker.isInvertible_invModule
  have hmod := hker.isInvertible_module
  obtain ⟨E, ⟨φ, h1, h2, h3, h4⟩⟩ := exists_rf (x := x) _ hinv
  obtain ⟨E', ⟨φ', h1', h2', h3', h4'⟩⟩ := exists_rf (x := x) _ hmod
  obtain ⟨⟨f, hf, hfv⟩, ⟨f', hf', hfv'⟩⟩ := Scheme.Modules.isPrincipal_sub_single_of_presentation_ker_pow x P hP 1 v hv E E'
    φ h1 (fun U _ a m => h2 U a m) h3 h4 φ' h1' (fun U _ a m => h2' U a m) h3' h4'
  refine ⟨⟨hinv, E, ⟨φ, h1, h2, h3, h4⟩, ⟨f, hf, fun w => ?_⟩⟩, ⟨hmod, E', ⟨φ', h1', h2', h3', h4'⟩, ⟨f', hf', fun w => ?_⟩⟩⟩
  · have := hfv w
    simp only [Finsupp.sub_apply, one_smul] at this
    linarith
  · have := hfv' w
    simp only [Finsupp.add_apply, one_smul, Finsupp.neg_apply] at this ⊢
    linarith

end Curve

section Pieces

open ModularCurve

theorem sum_image_zsmul_single_sub_single_eq
    {K : Type} [Field K] [IsAlgClosed K] {F : Type} [Field F] [Algebra K F]
    (Mdl : AlgebraicCurve.CurveModel K F)
    [DecidableEq {q : Spec (CommRingCat.of K) ⟶ Mdl.C // q ≫ Mdl.toBase = 𝟙 _}]
    (εbar : {q : Spec (CommRingCat.of K) ⟶ Mdl.C // q ≫ Mdl.toBase = 𝟙 _})
    (hdeg1 : ∀ v : AlgebraicCurve.Place K F, v.deg = 1)
    (D' : AlgebraicCurve.Divisor.degZero (K := K) (F := F)) :
    ∑ y ∈ ((D' : AlgebraicCurve.Divisor K F).support).image Mdl.pointEquivPlace.symm,
        (D' : AlgebraicCurve.Divisor K F) (Mdl.pointEquivPlace y) •
          (Finsupp.single (Mdl.pointEquivPlace y) (1 : ℤ) - Finsupp.single (Mdl.pointEquivPlace εbar) 1) =
      (D' : AlgebraicCurve.Divisor K F) := by
  rw [Finset.sum_image (fun a _ b _ h => Mdl.pointEquivPlace.symm.injective h)]
  simp only [Equiv.apply_symm_apply]

  have hsum0 : ∑ v ∈ (D' : AlgebraicCurve.Divisor K F).support, (D' : AlgebraicCurve.Divisor K F) v = 0 := by
    have h : AlgebraicCurve.Divisor.degree (D' : AlgebraicCurve.Divisor K F) = 0 := D'.2
    rw [AlgebraicCurve.Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum] at h
    simpa only [AddMonoidHom.coe_mulRight, hdeg1, Nat.cast_one, mul_one] using h
  simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hsum0, zero_smul, sub_zero]
  conv_rhs => rw [← Finsupp.sum_single (D' : AlgebraicCurve.Divisor K F)]
  rw [Finsupp.sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finsupp.smul_single, smul_eq_mul, mul_one]

theorem nonempty_restrict_poincare_pullbackAlong_iso_pullback_eeta
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (H : Subgroup (ZMod M)ˣ)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (Λ : ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl)
    (O : ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ)
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf)
      (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ :
        RelativePic0Designation (R p) (toBase p (ΓM M H) hj)))
    (ρ : ModularCurve.XHDRLevel.R p →+* ↥Pl)
    (hρ : Pl.subtype.comp ρ = algebraMap (ModularCurve.XHDRLevel.R p) (AlgebraicClosure ℚ))
    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt Pl)
    [IsOpenImmersion gA]
    (z : ModularCurve.JH M H)
    (σ : NeronModelInfra.SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) O.g)
    (hσ : ModularCurve.JZeroNeronObjectAtP.barPt Pl ≫ σ.1 = (O.pts z).1) :
    Nonempty ((((hD.poincare.pullbackAlong σ).L).restrict gA) ≅
      (Scheme.Modules.pullback 𝔛.eeta).obj (hD.poincare.pullbackAlong (O.pts z)).L) := by

  have hcomm : gA ≫ baseChangeSnd (toBase p (ΓM M H) hj) σ =
      𝔛.eeta ≫ baseChangeSnd (toBase p (ΓM M H) hj) (O.pts z) := by
    apply pullback.hom_ext
    · simp only [Category.assoc, baseChangeSnd, pullback.map, pullback.lift_fst, Category.comp_id]
      exact hgA₁
    · simp only [Category.assoc, baseChangeSnd, pullback.map, pullback.lift_snd]
      rw [← Category.assoc, hgA₂, Category.assoc, hσ, ← Category.assoc, 𝔛.heeta]
  exact ⟨(Scheme.Modules.restrictFunctorIsoPullback gA).app _ ≪≫
    (Scheme.Modules.pullbackComp gA (baseChangeSnd (toBase p (ΓM M H) hj) σ)).app hD.poincare.L ≪≫
    (Scheme.Modules.pullbackCongr hcomm).app hD.poincare.L ≪≫
    ((Scheme.Modules.pullbackComp 𝔛.eeta (baseChangeSnd (toBase p (ΓM M H) hj) (O.pts z))).app hD.poincare.L).symm⟩

theorem exists_finset_sum_zsmul_pic0Mk_single_sub_single_eq
    {K : Type} [Field K] [IsAlgClosed K] {F : Type} [Field F] [Algebra K F] {F' : Type} [Field F'] [Algebra K F']
    (Mdl : AlgebraicCurve.CurveModel K F)
    (εbar : {q : Spec (CommRingCat.of K) ⟶ Mdl.C // q ≫ Mdl.toBase = 𝟙 _})
    (hdeg : ∀ y : {q : Spec (CommRingCat.of K) ⟶ Mdl.C // q ≫ Mdl.toBase = 𝟙 _},
      Finsupp.single (Mdl.pointEquivPlace y) (1 : ℤ) - Finsupp.single (Mdl.pointEquivPlace εbar) 1 ∈
        AlgebraicCurve.Divisor.degZero (K := K) (F := F))
    (hdeg1 : ∀ v : AlgebraicCurve.Place K F, v.deg = 1)
    (D' : AlgebraicCurve.Divisor.degZero (K := K) (F := F))
    (cKE : AlgebraicCurve.Place K F ≃ AlgebraicCurve.Place K F') :
    ∃ (s : Finset {q : Spec (CommRingCat.of K) ⟶ Mdl.C // q ≫ Mdl.toBase = 𝟙 _})
      (n : {q : Spec (CommRingCat.of K) ⟶ Mdl.C // q ≫ Mdl.toBase = 𝟙 _} → ℤ),
      AlgebraicCurve.Pic0.mk D' = ∑ y ∈ s, n y • AlgebraicCurve.Pic0.mk ⟨_, hdeg y⟩ ∧
      (∑ y ∈ s, n y • (Finsupp.single (cKE (Mdl.pointEquivPlace y)) (1 : ℤ) - Finsupp.single (cKE (Mdl.pointEquivPlace εbar)) 1)) =
        Finsupp.equivMapDomain cKE (D' : AlgebraicCurve.Divisor K F) := by
  classical

  refine ⟨((D' : AlgebraicCurve.Divisor K F).support).image Mdl.pointEquivPlace.symm,
    fun y => (D' : AlgebraicCurve.Divisor K F) (Mdl.pointEquivPlace y), ?_, ?_⟩
  ·
    let mkHom : AlgebraicCurve.Divisor.degZero (K := K) (F := F) →+ AlgebraicCurve.Pic0 K F := QuotientAddGroup.mk' _
    have hmk : ∀ E : AlgebraicCurve.Divisor.degZero (K := K) (F := F), AlgebraicCurve.Pic0.mk E = mkHom E := fun E => rfl
    simp only [hmk]
    rw [show (∑ y ∈ ((D' : AlgebraicCurve.Divisor K F).support).image Mdl.pointEquivPlace.symm,
        (D' : AlgebraicCurve.Divisor K F) (Mdl.pointEquivPlace y) •
          mkHom ⟨_, hdeg y⟩) = mkHom (∑ y ∈ ((D' : AlgebraicCurve.Divisor K F).support).image Mdl.pointEquivPlace.symm,
        (D' : AlgebraicCurve.Divisor K F) (Mdl.pointEquivPlace y) • ⟨_, hdeg y⟩) by
      rw [map_sum]
      simp only [map_zsmul]]
    congr 1
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    simp only [AddSubgroupClass.coe_zsmul]
    exact (HDV.sum_image_zsmul_single_sub_single_eq Mdl εbar hdeg1 D').symm
  ·
    let Φ : AlgebraicCurve.Divisor K F →+ AlgebraicCurve.Divisor K F' := Finsupp.mapDomain.addMonoidHom cKE
    have hΦ : ∀ v : AlgebraicCurve.Place K F, (Finsupp.single (cKE v) (1 : ℤ) : AlgebraicCurve.Divisor K F') =
        Φ (Finsupp.single v 1) := fun v => by
      simp only [Φ, Finsupp.mapDomain.addMonoidHom_apply, Finsupp.mapDomain_single]
    simp only [hΦ, ← map_sub, ← map_zsmul]
    rw [← map_sum, HDV.sum_image_zsmul_single_sub_single_eq Mdl εbar hdeg1 D', Finsupp.equivMapDomain_eq_mapDomain]
    rfl

end Pieces

section PointModules

theorem smoothOfRelativeDimension_one_of_iso {S X Y : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} (e : X ≅ Y)
    (he : e.inv ≫ f = g) [SmoothOfRelativeDimension 1 f] : SmoothOfRelativeDimension 1 g := by
  rw [← he]
  exact (MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension 1) e.inv f).mpr ‹_›

theorem comap_ker_eq_ker_of_isPullback {X₀ X T Z : Scheme.{u}} {iX : Z ⟶ X₀} {g : Z ⟶ T} {f : X₀ ⟶ X}
    {iY : T ⟶ X} [IsClosedImmersion iY] (H : IsPullback iX g f iY) : iY.ker.comap f = iX.ker := by
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, ← H.isoPullback_hom_fst,
    Scheme.Hom.ker_comp_of_isIso]

theorem nonempty_pullback_ker_invModule_iso_and_module_iso {C Y T : Scheme.{u}} (e : C ⟶ Y) [IsIso e] (P : T ⟶ C)
    [IsClosedImmersion P] [IsClosedImmersion (P ≫ e)]
    (hI : (P ≫ e).ker.IsInvertible) (hI' : P.ker.IsInvertible) :
    Nonempty ((Scheme.Modules.pullback e).obj (P ≫ e).ker.invModule ≅ P.ker.invModule) ∧
      Nonempty ((Scheme.Modules.pullback e).obj (P ≫ e).ker.module ≅ P.ker.module) := by
  have hsq : IsPullback P (𝟙 T) e (P ≫ e) := IsPullback.of_vert_isIso ⟨by simp⟩
  have hc : (P ≫ e).ker.comap e = P.ker := comap_ker_eq_ker_of_isPullback hsq
  have hIc : ((P ≫ e).ker.comap e).IsInvertible := hc ▸ hI'
  obtain ⟨e1⟩ := hI.nonempty_pullback_invModule_iso e hIc
  haveI := hI.isIso_pullbackModuleComparison e hIc
  refine ⟨⟨e1 ≪≫ eqToIso (by rw [hc])⟩, ⟨asIso ((P ≫ e).ker.pullbackModuleComparison e) ≪≫ eqToIso (by rw [hc])⟩⟩

theorem range_algebraMap_stalk_eq_congrRingEquiv_pointEquivPlace
    {K : Type u} [Field K] [IsAlgClosed K] {L : Type} [Field L] [Algebra K L]
    (Mdl : AlgebraicCurve.CurveModel K L) (q : {q : Spec (CommRingCat.of K) ⟶ Mdl.C // q ≫ Mdl.toBase = 𝟙 _}) :
    letI := Mdl.functionFieldAlgebra
    (algebraMap (Mdl.C.presheaf.stalk (q.1.base (IsLocalRing.closedPoint K))) Mdl.C.functionField).range =
      (AlgebraicCurve.Place.congrRingEquiv Mdl.ffEquiv Mdl.ffEquiv_algebraMap (Mdl.pointEquivPlace q)).toValuationSubring.toSubring := by
  letI := Mdl.functionFieldAlgebra
  set y : Mdl.C := q.1.base (IsLocalRing.closedPoint K) with hy
  have hyc : IsClosed ({y} : Set Mdl.C) := (pointEquivClosedPoint Mdl.toBase q).2
  have hqy : pointEquivClosedPoint Mdl.toBase q = ⟨y, hyc⟩ := Subtype.ext rfl
  have hplace : Mdl.pointEquivPlace q = Mdl.placeOfPoint ⟨y, hyc⟩ := by
    rw [AlgebraicCurve.CurveModel.pointEquivPlace_apply, hqy]
  have hr := Mdl.range_stalk_eq ⟨y, hyc⟩
  ext x
  simp only [AlgebraicCurve.Place.congrRingEquiv_toValuationSubring]
  constructor
  · rintro ⟨t, rfl⟩
    show Mdl.ffEquiv.symm _ ∈ (Mdl.pointEquivPlace q).toValuationSubring
    rw [hplace]
    have : (Mdl.ffEquiv.symm : Mdl.C.functionField ≃+* _).toRingHom.comp
        (algebraMap (Mdl.C.presheaf.stalk y) Mdl.C.functionField) t ∈
        (Mdl.placeOfPoint ⟨y, hyc⟩).toValuationSubring.toSubring := by
      rw [← hr]; exact ⟨t, rfl⟩
    exact this
  · intro hx
    have hx' : Mdl.ffEquiv.symm x ∈ (Mdl.placeOfPoint ⟨y, hyc⟩).toValuationSubring.toSubring := by
      rw [← hplace]; exact hx
    rw [← hr] at hx'
    obtain ⟨t, ht⟩ := hx'
    refine ⟨t, ?_⟩
    have := congrArg Mdl.ffEquiv ht
    simpa using this

end PointModules

end HDV

end

set_option maxHeartbeats 3200000 in
open ModularCurve in

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (Λ : ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl)
    (O : ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ)
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)))
    (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)
        (algEquivZeroCut (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)) (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ))
    (hsep : IsSeparated (baseChange (R p) (toBase p (ΓM M H) hj) ℚ))
    (ajQ : SchemeHomOver (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ).toBase)
    (kQ : pullback (toBase p (ΓM M H) hj) (genPt p) ⟶ pullback (toBase p (ΓM M H) hj) (specMap (R p) ℚ))
    (ajbar : 𝔛.Meta.C ⟶ O.G)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (hpoinc : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase p (ΓM M H) hj) 𝔛.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst O.g (specMap (R p) ℚ), pullback.condition⟩)).L))
    (hajQε : (sectionBaseChange ℚ 𝔛.εinf).1 ≫ ajQ.1 = (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ).zeroSection)
    (hajQ : (∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
        (x : SchemeHomOver t (baseChange (R p) (toBase p (ΓM M H) hj) ℚ)),
        Nonempty ((hDQ.poincare.pullbackAlong
        ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) x.1 x.2).lineBundle ⊗
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (t ≫ (sectionBaseChange ℚ 𝔛.εinf).1)
        ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔛.εinf).2).trans
        (Category.comp_id t)))).idealModule)))
    (hkQ₁ : kQ ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.fst (toBase p (ΓM M H) hj) (genPt p))
    (hkQ₂ : kQ ≫ pullback.snd (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.snd (toBase p (ΓM M H) hj) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))
    (hajbar : ajbar = 𝔛.eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst O.g (specMap (R p) ℚ))
    (hajbar_over : ajbar ≫ O.g = 𝔛.Meta.toBase ≫ genPt p)
    (hεbar : εbar.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1)
    (hεbar_aj : εbar.1 ≫ ajbar = genPt p ≫ (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1)
    (hpts_law : (∀ x y : JH M H,
        O.pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (O.pts x) (O.pts y)))
    (hAJ : (∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
        s.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 →
        ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)),
        (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace s) 1 ∧
        (O.pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar))
    (ρ : ModularCurve.XHDRLevel.R p →+* ↥Pl)
    (hρ : Pl.subtype.comp ρ = algebraMap (ModularCurve.XHDRLevel.R p) (AlgebraicClosure ℚ))

    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt Pl)
    [hint : IsIntegral (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)))]

    (z : ModularCurve.JH M H)
    (D' : AlgebraicCurve.Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.xHFunctionFieldBar M H)))
    (hD' : AlgebraicCurve.Pic0.mk D' = z)
    (σ : NeronModelInfra.SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) O.g)
    (hσ : ModularCurve.JZeroNeronObjectAtP.barPt Pl ≫ σ.1 = (O.pts z).1)
    [hgAo : IsOpenImmersion gA]
    (D₁ : letI := 𝔛.Meta.functionFieldAlgebra
      AlgebraicCurve.Divisor (AlgebraicClosure ℚ) 𝔛.Meta.C.functionField)
    (φ₁ : ∀ V : 𝔛.Meta.C.Opens, Γ(((hD.poincare.pullbackAlong σ).L).restrict gA, V) →+ (𝔛.Meta.C.functionField : Type))
    (h1nat : ∀ (U V : 𝔛.Meta.C.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(((hD.poincare.pullbackAlong σ).L).restrict gA, U),
        φ₁ V ((((hD.poincare.pullbackAlong σ).L).restrict gA).presheaf.map (homOfLE h).op m) = φ₁ U m)
    (h1smul : ∀ (U : 𝔛.Meta.C.Opens) [Nonempty U] (a : Γ(𝔛.Meta.C, U)) (m : Γ(((hD.poincare.pullbackAlong σ).L).restrict gA, U)),
      φ₁ U (a • m) = algebraMap Γ(𝔛.Meta.C, U) 𝔛.Meta.C.functionField a * φ₁ U m)
    (h1inj : ∀ U : 𝔛.Meta.C.Opens, Nonempty U → Function.Injective (φ₁ U))
    (h1range : letI := 𝔛.Meta.functionFieldAlgebra
      ∀ U : 𝔛.Meta.C.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ₁ U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf 𝔛.Meta.toBase U) D₁ : Set 𝔛.Meta.C.functionField)) :
    letI := 𝔛.Meta.functionFieldAlgebra
    ∃ g₂ : 𝔛.Meta.C.functionField, g₂ ≠ 0 ∧
      ∀ v : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H),
        D₁ (AlgebraicCurve.Place.congrRingEquiv 𝔛.Meta.ffEquiv 𝔛.Meta.ffEquiv_algebraMap v) =
          (D' : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)) v +
          (AlgebraicCurve.Place.congrRingEquiv 𝔛.Meta.ffEquiv 𝔛.Meta.ffEquiv_algebraMap v).ord g₂ := by
  classical
  letI := 𝔛.Meta.functionFieldAlgebra
  haveI : NeZero (M / p) := ModularCurve.neZero_div p M hpM

  let Lw := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD
  letI grp : Group (SchemeHomOver (genPt p) O.g) := Lw.pointGroup _
  let Q : SchemeHomOver (genPt p) O.g → 𝔛.Meta.C.Modules := fun a =>
    (Scheme.Modules.pullback 𝔛.eeta).obj (hD.poincare.pullbackAlong a).L
  let cK := fun v : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) =>
    AlgebraicCurve.Place.congrRingEquiv 𝔛.Meta.ffEquiv 𝔛.Meta.ffEquiv_algebraMap v
  let cKE : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) ≃
      AlgebraicCurve.Place (AlgebraicClosure ℚ) 𝔛.Meta.C.functionField :=
    AlgebraicCurve.Place.congrEquiv 𝔛.Meta.ffEquiv 𝔛.Meta.ffEquiv_algebraMap

  have hQinv : ∀ a, Scheme.Modules.IsInvertible (Q a) := fun a =>
    (hD.poincare.pullbackAlong a).isInvertible.pullback _
  letI := RepresentsRelSubPic.grpObj (P := algEquivZeroGroupCut _ _) hD
  have hQmul : ∀ a b : SchemeHomOver (genPt p) O.g, Nonempty (Q (a * b) ≅ Q a ⊗ Q b) := by
    intro a b
    have hm : Nonempty ((hD.poincare.pullbackAlong (a * b)).L ≅ (hD.poincare.pullbackAlong a).L ⊗ (hD.poincare.pullbackAlong b).L) := by
      have := RepresentsRelSubPic.nonempty_poincare_pullbackAlong_mul_iso (P := algEquivZeroGroupCut _ _) hD
        (T := Over.mk (genPt p)) (schemeHomOverToOverHom a) (schemeHomOverToOverHom b)
      exact this
    obtain ⟨em⟩ := hm
    exact ⟨(Scheme.Modules.pullback 𝔛.eeta).mapIso em ≪≫ Scheme.Modules.pullbackTensorObjIso _ _ _⟩
  have hQone : Nonempty (Q 1 ≅ 𝟙_ 𝔛.Meta.C.Modules) := by
    have h1 : Nonempty ((hD.poincare.pullbackAlong (1 : SchemeHomOver (genPt p) O.g)).L ≅
        𝟙_ (pullback (toBase p (ΓM M H) hj) (genPt p)).Modules) := by
      have := RepresentsRelSubPic.nonempty_poincare_pullbackAlong_one_iso (P := algEquivZeroGroupCut _ _) hD (Over.mk (genPt p))
      exact this
    obtain ⟨e1⟩ := h1
    exact ⟨(Scheme.Modules.pullback 𝔛.eeta).mapIso e1 ≪≫ Scheme.Modules.pullbackTensorUnitObjIso _⟩

  have pts_mul : ∀ x y : JH M H, O.pts (x + y) = O.pts x * O.pts y := fun x y => hpts_law x y
  have pts_zero : O.pts 0 = 1 := by
    have h := pts_mul 0 0
    rw [add_zero] at h
    exact left_eq_mul.mp h |>.symm ▸ rfl
  have pts_neg : ∀ x : JH M H, O.pts (-x) = (O.pts x)⁻¹ := by
    intro x
    apply eq_inv_of_mul_eq_one_left
    rw [← pts_mul, neg_add_cancel, pts_zero]
  have pts_nsmul : ∀ (n : ℕ) (x : JH M H), O.pts (n • x) = O.pts x ^ n := by
    intro n x
    induction n with
    | zero => rw [zero_nsmul, pow_zero, pts_zero]
    | succ n ih => rw [succ_nsmul, pts_mul, ih, pow_succ]
  have pts_zsmul : ∀ (n : ℤ) (x : JH M H), O.pts (n • x) = O.pts x ^ n := by
    intro n x
    cases n with
    | ofNat n => rw [Int.ofNat_eq_natCast, natCast_zsmul, zpow_natCast, pts_nsmul]
    | negSucc n => rw [negSucc_zsmul, pts_neg, pts_nsmul, zpow_negSucc]

  have hQzpow : ∀ (a : SchemeHomOver (genPt p) O.g) (E : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) 𝔛.Meta.C.functionField)
      (n : ℤ), HDV.HasDiv 𝔛.Meta.toBase (Q a) E → HDV.HasDiv 𝔛.Meta.toBase (Q (a ^ n)) (n • E) := by
    have hnat : ∀ (a : SchemeHomOver (genPt p) O.g) (E : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) 𝔛.Meta.C.functionField)
        (n : ℕ), HDV.HasDiv 𝔛.Meta.toBase (Q a) E → HDV.HasDiv 𝔛.Meta.toBase (Q (a ^ n)) (n • E) := by
      intro a E n h
      induction n with
      | zero =>
        rw [pow_zero, zero_smul]
        exact HDV.HasDiv.of_iso hQone.some.symm (HDV.hasDiv_unit (x := 𝔛.Meta.toBase))
      | succ n ih =>
        rw [pow_succ, succ_nsmul]
        exact HDV.HasDiv.of_iso (hQmul _ _).some.symm (HDV.HasDiv.tensor ih h)
    intro a E n h
    cases n with
    | ofNat n =>
      rw [Int.ofNat_eq_natCast, zpow_natCast, natCast_zsmul]
      exact hnat a E n h
    | negSucc n =>
      rw [zpow_negSucc, negSucc_zsmul]
      have hb := hnat a E (n + 1) h
      have e : Q (a ^ (n + 1)) ⊗ Q (a ^ (n + 1))⁻¹ ≅ 𝟙_ 𝔛.Meta.C.Modules :=
        (hQmul _ _).some.symm ≪≫ eqToIso (by rw [mul_inv_cancel]) ≪≫ hQone.some
      exact HDV.HasDiv.of_tensor_iso_unit e hb (hQinv _)

  have hdeg : ∀ y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _},
      Finsupp.single (𝔛.Meta.pointEquivPlace y) (1 : ℤ) - Finsupp.single (𝔛.Meta.pointEquivPlace εbar) 1 ∈
        AlgebraicCurve.Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.xHFunctionFieldBar M H)) := by
    haveI : AlgebraicCurve.IsCurveOver (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) :=
      AlgebraicCurve.isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
        𝔛.Meta.toBase 𝔛.Meta.ffEquiv 𝔛.Meta.ffEquiv_algebraMap
    intro y
    rw [AlgebraicCurve.Divisor.mem_degZero, map_sub, AlgebraicCurve.Divisor.degree_single, AlgebraicCurve.Divisor.degree_single,
      AlgebraicCurve.IsCurveOver.deg_eq_one_of_isAlgClosed, AlgebraicCurve.IsCurveOver.deg_eq_one_of_isAlgClosed, sub_self]
  let xcls : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _} → JH M H := fun y =>
    AlgebraicCurve.Pic0.mk ⟨_, hdeg y⟩
  let δ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _} →
      AlgebraicCurve.Divisor (AlgebraicClosure ℚ) 𝔛.Meta.C.functionField := fun y =>
    Finsupp.single (cK (𝔛.Meta.pointEquivPlace y)) 1 - Finsupp.single (cK (𝔛.Meta.pointEquivPlace εbar)) 1
  have hQpt : ∀ y, HDV.HasDiv 𝔛.Meta.toBase (Q (O.pts (xcls y))) (δ y) := by
    intro y

    obtain ⟨Dv, hDv, hpts⟩ := hAJ y εbar hεbar
    have hxy : xcls y = AlgebraicCurve.Pic0.mk Dv := congrArg AlgebraicCurve.Pic0.mk (Subtype.ext hDv.symm)
    let ybar : SchemeHomOver (genPt p) (toBase p (ΓM M H) hj) :=
      ⟨y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _, by
        rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc 𝔛.eeta, 𝔛.heeta, ← Category.assoc, y.2,
          Category.id_comp]⟩
    haveI := 𝔛.isProper
    haveI : IsSeparated (toBase p (ΓM M H) hj) := inferInstance
    haveI := hsep
    have hP := ModularCurve.XHDRModelAtP.nonempty_poincare_pullbackAlong_iso_ofPoint_tensor_ofPoint_idealModule_of_eq_comp_ajbar
      p M H hpM hj 𝔛 _ hD hDQ ajQ kQ ajbar hpoinc hajQ hkQ₁ hkQ₂ hajbar y ybar rfl (O.pts (xcls y)) (by rw [hxy]; exact hpts)
    obtain ⟨eP⟩ := hP

    have hgr : AlgebraicGeometry.graphOver (toBase p (ΓM M H) hj) ybar.1 ybar.2 = y.1 ≫ 𝔛.eeta := by
      apply pullback.hom_ext
      · rw [AlgebraicGeometry.graphOver_fst, Category.assoc]
      · rw [AlgebraicGeometry.graphOver_snd, Category.assoc, 𝔛.heeta, y.2]
    have hgrε : AlgebraicGeometry.graphOver (toBase p (ΓM M H) hj) (genPt p ≫ 𝔛.εinf.1)
        ((Category.assoc _ _ _).trans ((congrArg (genPt p ≫ ·) 𝔛.εinf.2).trans (Category.comp_id _))) = εbar.1 ≫ 𝔛.eeta := by
      apply pullback.hom_ext
      · rw [AlgebraicGeometry.graphOver_fst, Category.assoc, hεbar]
      · rw [AlgebraicGeometry.graphOver_snd, Category.assoc, 𝔛.heeta, εbar.2]

    haveI hsm : SmoothOfRelativeDimension 1 (pullback.snd (toBase p (ΓM M H) hj) (genPt p)) :=
      HDV.smoothOfRelativeDimension_one_of_iso (asIso 𝔛.eeta) (by rw [asIso_inv, IsIso.inv_comp_eq, 𝔛.heeta])
    haveI : IsClosedImmersion y.1 := isClosedImmersion_of_comp_eq_id _ _ y.2
    haveI : IsClosedImmersion εbar.1 := isClosedImmersion_of_comp_eq_id _ _ εbar.2
    have hIy : (y.1 ≫ 𝔛.eeta).ker.IsInvertible :=
      Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd (toBase p (ΓM M H) hj) (genPt p)) (y.1 ≫ 𝔛.eeta)
        (by rw [Category.assoc, 𝔛.heeta, y.2])
    have hIy' : y.1.ker.IsInvertible := Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := 𝔛.Meta.toBase) y.1 y.2
    have hIε : (εbar.1 ≫ 𝔛.eeta).ker.IsInvertible :=
      Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd (toBase p (ΓM M H) hj) (genPt p)) (εbar.1 ≫ 𝔛.eeta)
        (by rw [Category.assoc, 𝔛.heeta, εbar.2])
    have hIε' : εbar.1.ker.IsInvertible := Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := 𝔛.Meta.toBase) εbar.1 εbar.2
    obtain ⟨⟨eL⟩, -⟩ := HDV.nonempty_pullback_ker_invModule_iso_and_module_iso 𝔛.eeta y.1 hIy hIy'
    obtain ⟨-, ⟨eM⟩⟩ := HDV.nonempty_pullback_ker_invModule_iso_and_module_iso 𝔛.eeta εbar.1 hIε hIε'

    have hI1 : (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) ybar.1 ybar.2).I = (y.1 ≫ 𝔛.eeta).ker := by
      rw [RelEffCartierDiv.ofPoint_I, hgr]
    have hI2 : (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) (genPt p ≫ 𝔛.εinf.1)
        ((Category.assoc _ _ _).trans ((congrArg (genPt p ≫ ·) 𝔛.εinf.2).trans (Category.comp_id _)))).I = (εbar.1 ≫ 𝔛.eeta).ker := by
      rw [RelEffCartierDiv.ofPoint_I, hgrε]
    have eQ : Q (O.pts (xcls y)) ≅ y.1.ker.invModule ⊗ εbar.1.ker.module :=
      (Scheme.Modules.pullback 𝔛.eeta).mapIso eP ≪≫ Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
        ((eqToIso (congrArg (fun I : (pullback (toBase p (ΓM M H) hj) (genPt p)).IdealSheafData =>
            (Scheme.Modules.pullback 𝔛.eeta).obj I.invModule) hI1) ≪≫ eL) ⊗ᵢ
         (eqToIso (congrArg (fun I : (pullback (toBase p (ΓM M H) hj) (genPt p)).IdealSheafData =>
            (Scheme.Modules.pullback 𝔛.eeta).obj I.module) hI2) ≪≫ eM))

    have hvy := HDV.range_algebraMap_stalk_eq_congrRingEquiv_pointEquivPlace 𝔛.Meta y
    have hvε := HDV.range_algebraMap_stalk_eq_congrRingEquiv_pointEquivPlace 𝔛.Meta εbar
    have h1 := (HDV.hasDiv_ker_invModule_and_module (x := 𝔛.Meta.toBase) y.1 y.2 (cK (𝔛.Meta.pointEquivPlace y)) hvy).1
    have h2 := (HDV.hasDiv_ker_invModule_and_module (x := 𝔛.Meta.toBase) εbar.1 εbar.2 (cK (𝔛.Meta.pointEquivPlace εbar)) hvε).2
    have h1' : HDV.HasDiv 𝔛.Meta.toBase y.1.ker.invModule (Finsupp.single (cK (𝔛.Meta.pointEquivPlace y)) 1) :=
      HDV.HasDiv.of_iso (eqToIso (by rw [pow_one])) h1
    have h2' : HDV.HasDiv 𝔛.Meta.toBase εbar.1.ker.module (-Finsupp.single (cK (𝔛.Meta.pointEquivPlace εbar)) 1) :=
      HDV.HasDiv.of_iso (eqToIso (by rw [pow_one])) h2
    have h12 := HDV.HasDiv.tensor h1' h2'
    rw [← sub_eq_add_neg] at h12
    exact HDV.HasDiv.of_iso eQ.symm h12

  have hsum : ∀ (s : Finset {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (n : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _} → ℤ),
      HDV.HasDiv 𝔛.Meta.toBase (Q (O.pts (∑ y ∈ s, n y • xcls y))) (∑ y ∈ s, n y • δ y) := by
    intro s n
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty, Finset.sum_empty, pts_zero]
      exact HDV.HasDiv.of_iso hQone.some.symm (HDV.hasDiv_unit (x := 𝔛.Meta.toBase))
    | insert y s hy ih =>
      rw [Finset.sum_insert hy, Finset.sum_insert hy, pts_mul]
      refine HDV.HasDiv.of_iso (hQmul _ _).some.symm (HDV.HasDiv.tensor ?_ ih)
      rw [pts_zsmul]
      exact hQzpow _ _ _ (hQpt y)

  have hdec : ∃ (s : Finset {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (n : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _} → ℤ),
      z = ∑ y ∈ s, n y • xcls y ∧ (∑ y ∈ s, n y • δ y) = Finsupp.equivMapDomain cKE (D' : AlgebraicCurve.Divisor _ _) := by
    haveI : AlgebraicCurve.IsCurveOver (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) :=
      AlgebraicCurve.isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
        𝔛.Meta.toBase 𝔛.Meta.ffEquiv 𝔛.Meta.ffEquiv_algebraMap
    obtain ⟨s, n, h1, h2⟩ := HDV.exists_finset_sum_zsmul_pic0Mk_single_sub_single_eq 𝔛.Meta εbar hdeg
      AlgebraicCurve.IsCurveOver.deg_eq_one_of_isAlgClosed D' cKE
    exact ⟨s, n, hD'.symm.trans h1, h2⟩

  have hlink : Nonempty ((((hD.poincare.pullbackAlong σ).L).restrict gA) ≅ Q (O.pts z)) :=
    HDV.nonempty_restrict_poincare_pullbackAlong_iso_pullback_eeta p M hpM H Pl hPl hj 𝔛 Λ O hD ρ hρ gA hgA₁ hgA₂ z σ hσ

  obtain ⟨s, n, hzs, hE⟩ := hdec
  have hmain : HDV.HasDiv 𝔛.Meta.toBase (((hD.poincare.pullbackAlong σ).L).restrict gA)
      (Finsupp.equivMapDomain cKE (D' : AlgebraicCurve.Divisor _ _)) := by
    rw [← hE]
    obtain ⟨el⟩ := hlink
    have h := hsum s n
    rw [← hzs] at h
    exact HDV.HasDiv.of_iso el.symm h
  have hrf : HDV.RF 𝔛.Meta.toBase (((hD.poincare.pullbackAlong σ).L).restrict gA) D₁ :=
    ⟨φ₁, h1nat, fun U _ a m => h1smul U a m, h1inj, h1range⟩
  obtain ⟨g₂, hg₂, hlin⟩ := HDV.HasDiv.linEq_of_rf hmain hrf
  refine ⟨g₂, hg₂, fun v => ?_⟩
  have := hlin (cK v)
  rw [this, Finsupp.equivMapDomain_apply]
  congr 1
  show (D' : AlgebraicCurve.Divisor _ _) (cKE.symm (cKE v)) = _
  rw [Equiv.symm_apply_apply]

end S_ModularCurve_JHNeronObjectAtP_exists_forall_divisor_congrRingEquiv_eq_add_ord_of_range_eq_lSpaceOn_restrict_poincare_pullbackAlong_of_barPt_comp_eq_pts
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_exists_forall_divisor_congrRingEquiv_eq_add_ord_of_range_eq_lSpaceOn_restrict_poincare_pullbackAlong_of_barPt_comp_eq_pts (solution)
