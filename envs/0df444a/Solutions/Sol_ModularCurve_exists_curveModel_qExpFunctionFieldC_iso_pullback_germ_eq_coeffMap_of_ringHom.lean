-- Prove2me | solution 1 for ModularCurve.exists_curveModel_qExpFunctionFieldC_iso_pullback_germ_eq_coeffMap_of_ringHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/6cad8d72-5a2d-5f4b-9992-00629e59cfd5

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_curveModel_iso_pullback_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_exists_ringHom_functionField_germ_eq_and_linearIndependent_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_curveModel_qExpFunctionFieldC_iso_pullback_germ_eq_coeffMap_of_ringHom
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

open scoped MatrixGroups
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve P2MW.S_ModularCurve_exists_curveModel_qExpFunctionFieldC_iso_pullback_germ_eq_coeffMap_of_ringHom.ModularCurve IntermediateField HahnSeries Module"

universe u

namespace ModularCurve
p2m_export "ModularCurve" "intSeriesC intFormRatiosC qExpFunctionFieldC intFormRatiosC_subset coeffMap coeffMap_coeff coeffMap_single algebraMap_laurentSeries_eq_single"
namespace QExpModelBaseChange
p2m_open "ModularCurve"

section FreeCompositum

variable {κ : Type u} (k : Type u) [Field κ] [Field k] (ι : κ →+* k)
variable {E₀ : Type u} [Field E₀] [Algebra κ E₀]
variable {K' : Type u} [Field K'] [Algebra k K'] (Ψ : E₀ →+* K')

def R : Subalgebra k K' where
  carrier := Submodule.span k (Set.range Ψ)
  mul_mem' {a b} ha hb := by
    change a * b ∈ Submodule.span k (Set.range Ψ)
    refine Submodule.span_induction (p := fun a _ => a * b ∈ Submodule.span k (Set.range Ψ)) ?_ ?_ ?_ ?_ ha
    · rintro _ ⟨y, rfl⟩
      refine Submodule.span_induction (p := fun b _ => Ψ y * b ∈ Submodule.span k (Set.range Ψ)) ?_ ?_ ?_ ?_ hb
      · rintro _ ⟨z, rfl⟩
        rw [← map_mul]
        exact Submodule.subset_span ⟨y * z, rfl⟩
      · show Ψ y * 0 ∈ _
        rw [mul_zero]; exact zero_mem _
      · intro u v _ _ hu hv
        show Ψ y * (u + v) ∈ _
        rw [mul_add]; exact add_mem hu hv
      · intro c u _ hu
        show Ψ y * (c • u) ∈ _
        rw [mul_smul_comm]; exact Submodule.smul_mem _ c hu
    · show (0 : K') * b ∈ _
      rw [zero_mul]; exact zero_mem _
    · intro u v _ _ hu hv
      show (u + v) * b ∈ _
      rw [add_mul]; exact add_mem hu hv
    · intro c u _ hu
      show (c • u) * b ∈ _
      rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hu
  add_mem' {a b} ha hb := add_mem ha hb
  algebraMap_mem' c := by
    change algebraMap k K' c ∈ Submodule.span k (Set.range Ψ)
    rw [Algebra.algebraMap_eq_smul_one]
    refine Submodule.smul_mem _ c (Submodule.subset_span ⟨1, ?_⟩)
    rw [map_one]

theorem mem_R_iff (a : K') : a ∈ R k Ψ ↔ a ∈ Submodule.span k (Set.range Ψ) := Iff.rfl

theorem apply_mem_R (y : E₀) : Ψ y ∈ R k Ψ := Submodule.subset_span ⟨y, rfl⟩

theorem adjoin_le_R : Algebra.adjoin k (Set.range Ψ) ≤ R k Ψ :=
  Algebra.adjoin_le (by rintro _ ⟨y, rfl⟩; exact apply_mem_R k Ψ y)

def ΨR (y : E₀) : R k Ψ := ⟨Ψ y, apply_mem_R k Ψ y⟩

@[scoped simp] theorem coe_ΨR (y : E₀) : ((ΨR k Ψ y : R k Ψ) : K') = Ψ y := rfl

theorem ΨR_mul (y z : E₀) : ΨR k Ψ (y * z) = ΨR k Ψ y * ΨR k Ψ z := Subtype.ext (map_mul _ _ _)

theorem ΨR_one : ΨR k Ψ (1 : E₀) = 1 := Subtype.ext (map_one _)

variable (hΨ : ∀ c : κ, Ψ (algebraMap κ E₀ c) = algebraMap k K' (ι c))

include hΨ in
theorem Ψ_smul (c : κ) (y : E₀) : Ψ (c • y) = ι c • Ψ y := by
  rw [Algebra.smul_def, map_mul, hΨ, Algebra.smul_def]

def ΨRsl : E₀ →ₛₗ[ι] R k Ψ where
  toFun := ΨR k Ψ
  map_add' a b := Subtype.ext (map_add _ _ _)
  map_smul' c a := by
    apply Subtype.ext
    rw [Subalgebra.coe_smul, coe_ΨR, coe_ΨR, Ψ_smul k ι Ψ hΨ]

@[scoped simp] theorem ΨRsl_apply (y : E₀) : ΨRsl k ι Ψ hΨ y = ΨR k Ψ y := rfl

section WithBasis

variable {ιb : Type u} (b : Basis ιb κ E₀) (hli : LinearIndependent k (fun j => Ψ (b j)))

def w (j : ιb) : R k Ψ := ΨR k Ψ (b j)

include hli in
theorem linearIndependent_w : LinearIndependent k (w k Ψ b) := by
  refine LinearIndependent.of_comp (R k Ψ).val.toLinearMap ?_
  exact hli

include hΨ in

theorem apply_mem_span (y : E₀) : Ψ y ∈ Submodule.span k (Set.range fun j => Ψ (b j)) := by
  let ΨSL : E₀ →ₛₗ[ι] K' :=
    { toFun := Ψ
      map_add' := fun a b => map_add _ _ _
      map_smul' := fun c a => Ψ_smul k ι Ψ hΨ c a }
  have key : ∀ l : ιb →₀ κ,
      ΨSL (Finsupp.linearCombination κ b l) ∈ Submodule.span k (Set.range fun j => Ψ (b j)) := by
    intro l
    rw [Finsupp.linearCombination_apply, map_finsuppSum]
    refine Submodule.finsuppSum_mem _ _ _ _ fun j _ => ?_
    rw [LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have := key (b.repr y)
  rwa [b.linearCombination_repr y] at this

include hΨ in
theorem span_w : ⊤ ≤ Submodule.span k (Set.range (w k Ψ b)) := by
  intro r _
  have h1 : (r : K') ∈ Submodule.span k (Set.range Ψ) := r.2
  have h2 : Submodule.span k (Set.range Ψ) ≤ Submodule.span k (Set.range fun j => Ψ (b j)) :=
    Submodule.span_le.mpr (by
      rintro _ ⟨y, rfl⟩
      exact apply_mem_span k ι Ψ hΨ b y)
  have h3 : Submodule.span k (Set.range fun j => Ψ (b j)) =
      (Submodule.span k (Set.range (w k Ψ b))).map (R k Ψ).val.toLinearMap := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have h4 := h2 h1
  rw [h3, Submodule.mem_map] at h4
  obtain ⟨r', hr', hval⟩ := h4
  have : r' = r := Subtype.ext hval
  rw [← this]
  exact hr'

def bR : Basis ιb k (R k Ψ) :=
  Basis.mk (linearIndependent_w k Ψ b hli) (span_w k ι Ψ hΨ b)

theorem bR_apply (j : ιb) : bR k ι Ψ hΨ b hli j = ΨR k Ψ (b j) :=
  Basis.mk_apply _ _ j

variable {K'' : Type u} [Field K''] [Algebra k K''] (Ψ' : E₀ →+* K'')
  (hΨ' : ∀ c : κ, Ψ' (algebraMap κ E₀ c) = algebraMap k K'' (ι c))
  (hli' : LinearIndependent k (fun j => Ψ' (b j)))

def T : R k Ψ →ₗ[k] R k Ψ' :=
  (bR k ι Ψ hΨ b hli).constr k fun j => ΨR k Ψ' (b j)

theorem T_bR (j : ιb) : T k ι Ψ hΨ b hli Ψ' (bR k ι Ψ hΨ b hli j) = ΨR k Ψ' (b j) :=
  Basis.constr_basis _ _ _ j

include hΨ' in

theorem T_ΨR (y : E₀) : T k ι Ψ hΨ b hli Ψ' (ΨR k Ψ y) = ΨR k Ψ' y := by
  have key : (T k ι Ψ hΨ b hli Ψ').comp (ΨRsl k ι Ψ hΨ) = ΨRsl k ι Ψ' hΨ' := by
    refine b.ext fun j => ?_
    rw [LinearMap.comp_apply, ΨRsl_apply, ΨRsl_apply, ← bR_apply k ι Ψ hΨ b hli, T_bR]
  have := congrArg (fun f => f y) key
  simpa using this

include hΨ' in
theorem T_one : T k ι Ψ hΨ b hli Ψ' 1 = 1 := by
  rw [← ΨR_one, T_ΨR, ΨR_one]
  exact hΨ'

include hΨ' in
theorem T_mul (r s : R k Ψ) : T k ι Ψ hΨ b hli Ψ' (r * s) = T k ι Ψ hΨ b hli Ψ' r * T k ι Ψ hΨ b hli Ψ' s := by
  have key : (LinearMap.mul k (R k Ψ)).compr₂ (T k ι Ψ hΨ b hli Ψ') =
      (LinearMap.mul k (R k Ψ')).compl₁₂ (T k ι Ψ hΨ b hli Ψ') (T k ι Ψ hΨ b hli Ψ') := by
    refine (bR k ι Ψ hΨ b hli).ext fun i => (bR k ι Ψ hΨ b hli).ext fun j => ?_
    simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearMap.mul_apply']
    rw [bR_apply, bR_apply, ← ΨR_mul, T_ΨR k ι Ψ hΨ b hli Ψ' hΨ', T_ΨR k ι Ψ hΨ b hli Ψ' hΨ',
      T_ΨR k ι Ψ hΨ b hli Ψ' hΨ', ΨR_mul]
  have := congrArg (fun f => f r s) key
  simpa using this

include hΨ hΨ' in
theorem T_T (r : R k Ψ) : T k ι Ψ' hΨ' b hli' Ψ (T k ι Ψ hΨ b hli Ψ' r) = r := by
  have key : (T k ι Ψ' hΨ' b hli' Ψ).comp (T k ι Ψ hΨ b hli Ψ') = LinearMap.id := by
    refine (bR k ι Ψ hΨ b hli).ext fun j => ?_
    rw [LinearMap.comp_apply, LinearMap.id_apply, bR_apply, T_ΨR k ι Ψ hΨ b hli Ψ' hΨ',
      T_ΨR k ι Ψ' hΨ' b hli' Ψ hΨ]
  exact congrArg (fun f => f r) key

def Tequiv : R k Ψ ≃ₗ[k] R k Ψ' :=
  LinearEquiv.ofLinear (T k ι Ψ hΨ b hli Ψ') (T k ι Ψ' hΨ' b hli' Ψ)
    (LinearMap.ext fun r => T_T k ι Ψ' hΨ' b hli' Ψ hΨ hli r)
    (LinearMap.ext fun r => T_T k ι Ψ hΨ b hli Ψ' hΨ' hli' r)

def TA : R k Ψ ≃ₐ[k] R k Ψ' :=
  AlgEquiv.ofLinearEquiv (Tequiv k ι Ψ hΨ b hli Ψ' hΨ' hli') (T_one k ι Ψ hΨ b hli Ψ' hΨ')
    (T_mul k ι Ψ hΨ b hli Ψ' hΨ')

theorem TA_apply (r : R k Ψ) : TA k ι Ψ hΨ b hli Ψ' hΨ' hli' r = T k ι Ψ hΨ b hli Ψ' r := rfl

theorem TA_ΨR (y : E₀) : TA k ι Ψ hΨ b hli Ψ' hΨ' hli' (ΨR k Ψ y) = ΨR k Ψ' y :=
  T_ΨR k ι Ψ hΨ b hli Ψ' hΨ' y

end WithBasis

theorem isFractionRing_R
    (hgen : ∀ z : K', ∃ u ∈ Algebra.adjoin k (Set.range Ψ), ∃ v ∈ Algebra.adjoin k (Set.range Ψ),
      v ≠ 0 ∧ z * v = u) :
    IsFractionRing (R k Ψ) K' where
  map_units := by
    rintro ⟨s, hs⟩
    have hs0 : (s : K') ≠ 0 := fun h => nonZeroDivisors.ne_zero hs (Subtype.ext (by rw [h]; rfl))
    exact isUnit_iff_ne_zero.mpr hs0
  surj := by
    intro z
    obtain ⟨u, hu, v, hv, hv0, hz⟩ := hgen z
    have huR : u ∈ R k Ψ := adjoin_le_R k Ψ hu
    have hvR : v ∈ R k Ψ := adjoin_le_R k Ψ hv
    have hvR0 : (⟨v, hvR⟩ : R k Ψ) ≠ 0 := fun h => hv0 (congrArg Subtype.val h)
    refine ⟨(⟨u, huR⟩, ⟨⟨v, hvR⟩, mem_nonZeroDivisors_of_ne_zero hvR0⟩), ?_⟩
    exact hz
  exists_of_eq := by
    intro x y h
    have hxy : x = y := Subtype.ext h
    exact ⟨1, by rw [hxy]⟩

end FreeCompositum

section Theta

variable {κ : Type u} (k : Type u) [Field κ] [Field k] (ι : κ →+* k)
variable {E₀ : Type u} [Field E₀] [Algebra κ E₀]
variable {K' : Type u} [Field K'] [Algebra k K'] (Ψ : E₀ →+* K')
  (hΨ : ∀ c : κ, Ψ (algebraMap κ E₀ c) = algebraMap k K' (ι c))
variable {K'' : Type u} [Field K''] [Algebra k K''] (Ψ' : E₀ →+* K'')
  (hΨ' : ∀ c : κ, Ψ' (algebraMap κ E₀ c) = algebraMap k K'' (ι c))
variable {ιb : Type u} (b : Basis ιb κ E₀)
  (hli : LinearIndependent k (fun j => Ψ (b j))) (hli' : LinearIndependent k (fun j => Ψ' (b j)))
  (hgen : ∀ z : K', ∃ u ∈ Algebra.adjoin k (Set.range Ψ), ∃ v ∈ Algebra.adjoin k (Set.range Ψ),
      v ≠ 0 ∧ z * v = u)
  (hgen' : ∀ z : K'', ∃ u ∈ Algebra.adjoin k (Set.range Ψ'), ∃ v ∈ Algebra.adjoin k (Set.range Ψ'),
      v ≠ 0 ∧ z * v = u)

include ι hΨ hΨ' b hli hli' hgen hgen' in

theorem exists_ringEquiv_apply_eq :
    ∃ θ : K' ≃+* K'', (∀ y : E₀, θ (Ψ y) = Ψ' y) ∧ (∀ c : k, θ (algebraMap k K' c) = algebraMap k K'' c) := by
  haveI := isFractionRing_R k Ψ hgen
  haveI := isFractionRing_R k Ψ' hgen'
  let e : R k Ψ ≃+* R k Ψ' := (TA k ι Ψ hΨ b hli Ψ' hΨ' hli' : R k Ψ ≃ₐ[k] R k Ψ')
  refine ⟨IsFractionRing.ringEquivOfRingEquiv (K := K') (L := K'') e, ?_, ?_⟩
  · intro y
    have h1 : Ψ y = algebraMap (R k Ψ) K' (ΨR k Ψ y) := rfl
    rw [h1, IsFractionRing.ringEquivOfRingEquiv_algebraMap]
    change ((TA k ι Ψ hΨ b hli Ψ' hΨ' hli' (ΨR k Ψ y) : R k Ψ') : K'') = Ψ' y
    rw [TA_ΨR]
    rfl
  · intro c
    rw [IsScalarTower.algebraMap_apply k (R k Ψ) K' c, IsFractionRing.ringEquivOfRingEquiv_algebraMap]
    change ((TA k ι Ψ hΨ b hli Ψ' hΨ' hli' (algebraMap k (R k Ψ) c) : R k Ψ') : K'') = algebraMap k K'' c
    rw [AlgEquiv.commutes]
    rfl

end Theta

section QExp

attribute [local instance 2000] Algebra.toSMul Algebra.toModule

variable {κ k : Type u} [Field κ] [Field k] (ι : κ →+* k) (Γ : Subgroup SL(2, ℤ))

theorem coeff_smul' {L : Type*} [Field L] (r : L) (x : LaurentSeries L) (n : ℤ) :
    (r • x).coeff n = r * x.coeff n := by
  rw [Algebra.smul_def, algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_zero_mul]

theorem coeffMap_ofPowerSeries' {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (x : PowerSeries A) :
    coeffMap f (HahnSeries.ofPowerSeries ℤ A x) = HahnSeries.ofPowerSeries ℤ B (x.map f) := by
  ext i
  rw [coeffMap_coeff, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs with hi
  · exact map_zero f
  · rw [PowerSeries.coeff_map]

theorem coeffMap_intSeriesC (p : PowerSeries ℤ) : coeffMap ι (intSeriesC κ p) = intSeriesC k p := by
  rw [intSeriesC, intSeriesC, coeffMap_ofPowerSeries', ← RingHom.comp_apply (PowerSeries.map ι),
    ← PowerSeries.map_comp, RingHom.ext_int (ι.comp (Int.castRingHom κ)) (Int.castRingHom k)]

theorem coeffMap_injective : Function.Injective (coeffMap ι) := by
  intro x y h
  ext n
  have := congrArg (fun z : LaurentSeries k => z.coeff n) h
  simp only [coeffMap_coeff] at this
  exact ι.injective this

include ι in
theorem intSeriesC_ne_zero_iff (p : PowerSeries ℤ) : intSeriesC k p ≠ 0 ↔ intSeriesC κ p ≠ 0 := by
  rw [← coeffMap_intSeriesC ι]
  refine ⟨fun h h0 => h (by rw [h0, map_zero]), fun h h0 => h ?_⟩
  exact coeffMap_injective ι (h0.trans (map_zero _).symm)

theorem coeffMap_algebraMap' (c : κ) :
    coeffMap ι (algebraMap κ (LaurentSeries κ) c) = algebraMap k (LaurentSeries k) (ι c) := by
  rw [algebraMap_laurentSeries_eq_single, coeffMap_single, ← algebraMap_laurentSeries_eq_single]

theorem intFormRatiosC_eq_image : intFormRatiosC k Γ = coeffMap ι '' intFormRatiosC κ Γ := by
  ext y
  constructor
  · rintro ⟨wt, f, g, pf, pg, hf, hg, hg0, rfl⟩
    refine ⟨intSeriesC κ pf / intSeriesC κ pg,
      ⟨wt, f, g, pf, pg, hf, hg, (intSeriesC_ne_zero_iff ι pg).mp hg0, rfl⟩, ?_⟩
    rw [map_div₀, coeffMap_intSeriesC, coeffMap_intSeriesC]
  · rintro ⟨x, ⟨wt, f, g, pf, pg, hf, hg, hg0, rfl⟩, rfl⟩
    refine ⟨wt, f, g, pf, pg, hf, hg, (intSeriesC_ne_zero_iff ι pg).mpr hg0, ?_⟩
    rw [map_div₀, coeffMap_intSeriesC, coeffMap_intSeriesC]

theorem coeffMap_mem {x : LaurentSeries κ} (hx : x ∈ qExpFunctionFieldC κ Γ) :
    coeffMap ι x ∈ qExpFunctionFieldC k Γ := by
  let Tf : Subfield (LaurentSeries κ) := (qExpFunctionFieldC k Γ).toSubfield.comap (coeffMap ι)
  have hgen : intFormRatiosC κ Γ ⊆ (Tf : Set (LaurentSeries κ)) := by
    intro y hy
    change coeffMap ι y ∈ qExpFunctionFieldC k Γ
    apply intFormRatiosC_subset k Γ
    rw [intFormRatiosC_eq_image ι Γ]
    exact ⟨y, hy, rfl⟩
  have hconst : Set.range (algebraMap κ (LaurentSeries κ)) ⊆ (Tf : Set (LaurentSeries κ)) := by
    rintro y ⟨c, rfl⟩
    change coeffMap ι (algebraMap κ (LaurentSeries κ) c) ∈ qExpFunctionFieldC k Γ
    rw [coeffMap_algebraMap']
    exact (qExpFunctionFieldC k Γ).algebraMap_mem _
  have hle : (qExpFunctionFieldC κ Γ).toSubfield ≤ Tf := by
    rw [qExpFunctionFieldC, IntermediateField.adjoin_toSubfield]
    exact Subfield.closure_le.mpr (Set.union_subset hconst hgen)
  exact hle hx

abbrev E₀ : Type u := ↥(qExpFunctionFieldC κ Γ)
abbrev E : Type u := ↥(qExpFunctionFieldC k Γ)

def psi : E₀ (κ := κ) Γ →+* E (k := k) Γ where
  toFun y := ⟨coeffMap ι y, coeffMap_mem ι Γ y.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add _ _ _)

@[scoped simp] theorem coe_psi (y : E₀ (κ := κ) Γ) : ((psi ι Γ y : E (k := k) Γ) : LaurentSeries k) = coeffMap ι y :=
  rfl

theorem psi_algebraMap (c : κ) : psi ι Γ (algebraMap κ (E₀ Γ) c) = algebraMap k (E (k := k) Γ) (ι c) := by
  apply Subtype.ext
  change coeffMap ι (algebraMap κ (LaurentSeries κ) c) = algebraMap k (LaurentSeries k) (ι c)
  exact coeffMap_algebraMap' ι c

theorem linearIndependent_coeffMap {ιv : Type*} {v : ιv → LaurentSeries κ} (hv : LinearIndependent κ v) :
    LinearIndependent k (fun i => coeffMap ι (v i)) := by
  classical
  letI : Algebra κ k := ι.toAlgebra
  have hφ : ∀ c : κ, algebraMap κ k c = ι c := fun _ => rfl
  rw [linearIndependent_iff']
  intro s c hsum i hi
  let Wc : Submodule κ k := Submodule.span κ (Set.range fun j : s => c j)
  haveI : Module.Finite κ Wc := Module.Finite.span_of_finite κ (Set.finite_range _)
  let bW := Module.finBasis κ Wc
  have hcW : ∀ j : s, c j ∈ Wc := fun j => Submodule.subset_span ⟨j, rfl⟩
  let a : s → Fin (Module.finrank κ Wc) → κ := fun j l => bW.repr ⟨c j, hcW j⟩ l
  have hca : ∀ j : s, c j = ∑ l, a j l • (bW l : k) := by
    intro j
    have h1 := bW.sum_repr ⟨c j, hcW j⟩
    have h2 := congrArg (Submodule.subtype Wc) h1
    rw [map_sum] at h2
    simp only [Submodule.subtype_apply, Submodule.coe_smul] at h2
    exact h2.symm
  have hcoeff : ∀ n : ℤ, ∑ j ∈ s, c j * ι ((v j).coeff n) = 0 := by
    intro n
    have := congrArg (fun x : LaurentSeries k => x.coeff n) hsum
    simpa [HahnSeries.coeff_sum, coeff_smul', coeffMap_coeff] using this
  have hbi : LinearIndependent κ (fun l' => (bW l' : k)) :=
    bW.linearIndependent.map' Wc.subtype (Submodule.ker_subtype Wc)
  have hv' : LinearIndependent κ (fun j : s => v j) := hv.comp _ Subtype.val_injective
  have hrel : ∀ l, ∑ j : s, a j l • v j = 0 := by
    intro l
    ext n
    have h1 : ∑ l', (∑ j : s, a j l' * (v j).coeff n) • (bW l' : k) = 0 := by
      have h0 := hcoeff n
      rw [← Finset.sum_coe_sort] at h0
      simp_rw [hca, Finset.sum_mul] at h0
      rw [Finset.sum_comm] at h0
      rw [← h0]
      refine Finset.sum_congr rfl fun l' _ => ?_
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, hφ, hφ]; ring
    have := Fintype.linearIndependent_iff.mp hbi (fun l' => ∑ j : s, a j l' * (v j).coeff n) h1 l
    rw [HahnSeries.coeff_sum]
    simpa [coeff_smul'] using this
  have ha : ∀ (j : s) l, a j l = 0 := fun j l =>
    Fintype.linearIndependent_iff.mp hv' (fun j => a j l) (hrel l) j
  rw [show c i = c (⟨i, hi⟩ : s) from rfl, hca]
  simp [ha]

theorem linearIndependent_psi {ιv : Type*} {v : ιv → E₀ (κ := κ) Γ} (hv : LinearIndependent κ v) :
    LinearIndependent k (fun i => psi ι Γ (v i)) := by
  have h0 : LinearIndependent κ (fun i => ((v i : E₀ Γ) : LaurentSeries κ)) :=
    hv.map' (IntermediateField.val _).toLinearMap (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have h1 := linearIndependent_coeffMap ι h0
  refine LinearIndependent.of_comp (IntermediateField.val (qExpFunctionFieldC k Γ)).toLinearMap ?_
  exact h1

theorem exists_adjoin_of_mem_closure {t : LaurentSeries k}
    (ht : t ∈ Subring.closure (Set.range (algebraMap k (LaurentSeries k)) ∪ intFormRatiosC k Γ)) :
    ∃ r ∈ Algebra.adjoin k (Set.range (psi ι Γ)), ((r : E (k := k) Γ) : LaurentSeries k) = t := by
  let Rimg : Subring (LaurentSeries k) :=
    (Algebra.adjoin k (Set.range (psi ι Γ))).toSubring.map
      ((IntermediateField.val (qExpFunctionFieldC k Γ)) : E (k := k) Γ →+* LaurentSeries k)
  have hle : Subring.closure (Set.range (algebraMap k (LaurentSeries k)) ∪ intFormRatiosC k Γ) ≤ Rimg := by
    refine Subring.closure_le.mpr ?_
    rintro y (⟨c, rfl⟩ | hy)
    · exact ⟨algebraMap k (E Γ) c, (Algebra.adjoin k _).algebraMap_mem c, rfl⟩
    · rw [intFormRatiosC_eq_image ι Γ] at hy
      obtain ⟨y₀, hy₀, rfl⟩ := hy
      exact ⟨psi ι Γ ⟨y₀, intFormRatiosC_subset κ Γ hy₀⟩, Algebra.subset_adjoin ⟨_, rfl⟩, rfl⟩
  obtain ⟨r, hr, hrt⟩ := hle ht
  exact ⟨r, hr, hrt⟩

theorem psi_gen (z : E (k := k) Γ) :
    ∃ u ∈ Algebra.adjoin k (Set.range (psi ι Γ)), ∃ v ∈ Algebra.adjoin k (Set.range (psi ι Γ)),
      v ≠ 0 ∧ z * v = u := by
  have hz : (z : LaurentSeries k) ∈ (IntermediateField.adjoin k (intFormRatiosC k Γ)).toSubfield := z.2
  rw [IntermediateField.adjoin_toSubfield, Subfield.mem_closure_iff] at hz
  obtain ⟨y, hy, y', hy', hyz⟩ := hz
  obtain ⟨a, ha, hay⟩ := exists_adjoin_of_mem_closure ι Γ hy
  obtain ⟨s, hs, hsy⟩ := exists_adjoin_of_mem_closure ι Γ hy'
  by_cases hs0 : (s : LaurentSeries k) = 0
  · refine ⟨0, zero_mem _, 1, one_mem _, one_ne_zero, ?_⟩
    have hz0 : z = 0 := by
      apply Subtype.ext
      rw [← hyz, ← hsy, hs0, div_zero]
      rfl
    rw [hz0, zero_mul]
  · have hsE : s ≠ 0 := fun h => hs0 (by rw [h]; rfl)
    refine ⟨a, ha, s, hs, hsE, ?_⟩
    apply Subtype.ext
    rw [MulMemClass.coe_mul, ← hyz, ← hay, ← hsy, div_mul_cancel₀ _ hs0]

end QExp

section Transport

variable {k : Type u} [Field k] {L F : Type u} [Field L] [Field F] [Algebra k L] [Algebra k F]
  (e : L ≃+* F) (he : ∀ a : k, e (algebraMap k L a) = algebraMap k F a)

def valuationSubringEquiv (A : ValuationSubring L) : A ≃+* (A.comap e.symm.toRingHom) where
  toFun x := ⟨e x, by
    change e.symm.toRingHom (e x) ∈ A
    simp⟩
  invFun y := ⟨e.symm y, y.2⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_mul' x y := Subtype.ext (by change e ((x : L) * y) = e x * e y; exact map_mul e _ _)
  map_add' x y := Subtype.ext (by change e ((x : L) + y) = e x + e y; exact map_add e _ _)

include he in

def placeMap (v : Place k L) : Place k F where
  toValuationSubring := v.toValuationSubring.comap e.symm.toRingHom
  algebraMap_mem' a := by
    change e.symm.toRingHom (algebraMap k F a) ∈ v.toValuationSubring
    have : e.symm (algebraMap k F a) = algebraMap k L a := by
      rw [← he, RingEquiv.symm_apply_apply]
    rw [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, this]
    exact v.algebraMap_mem' a
  ne_top' h := v.ne_top' <| by
    ext x
    refine ⟨fun _ => ValuationSubring.mem_top x, fun _ => ?_⟩
    have hx : e x ∈ (v.toValuationSubring.comap e.symm.toRingHom) := by rw [h]; exact ValuationSubring.mem_top _
    change e.symm.toRingHom (e x) ∈ v.toValuationSubring at hx
    simpa using hx
  isPrincipalIdealRing' :=
    IsPrincipalIdealRing.of_surjective (valuationSubringEquiv e v.toValuationSubring)
      (valuationSubringEquiv e v.toValuationSubring).surjective

@[scoped simp]
theorem placeMap_toValuationSubring (v : Place k L) :
    (placeMap e he v).toValuationSubring = v.toValuationSubring.comap e.symm.toRingHom := rfl

include he in
theorem he_symm : ∀ a : k, e.symm (algebraMap k F a) = algebraMap k L a := fun a => by
  rw [← he, RingEquiv.symm_apply_apply]

theorem placeMap_symm_placeMap (v : Place k L) : placeMap e.symm (he_symm e he) (placeMap e he v) = v := by
  apply Place.ext
  rw [placeMap_toValuationSubring, placeMap_toValuationSubring, ValuationSubring.comap_comap]
  ext x
  rw [ValuationSubring.mem_comap]
  change e.symm.toRingHom (e.symm.symm.toRingHom x) ∈ _ ↔ _
  simp

theorem placeMap_placeMap_symm (v : Place k F) : placeMap e he (placeMap e.symm (he_symm e he) v) = v := by
  apply Place.ext
  rw [placeMap_toValuationSubring, placeMap_toValuationSubring, ValuationSubring.comap_comap]
  ext x
  rw [ValuationSubring.mem_comap]
  change e.symm.symm.toRingHom (e.symm.toRingHom x) ∈ _ ↔ _
  simp

theorem placeMap_bijective : Function.Bijective (placeMap e he) :=
  ⟨fun v w h => by
    have := congrArg (placeMap e.symm (he_symm e he)) h
    rwa [placeMap_symm_placeMap, placeMap_symm_placeMap] at this,
   fun v => ⟨placeMap e.symm (he_symm e he) v, placeMap_placeMap_symm e he v⟩⟩

def curveModelOfRingEquiv (M' : CurveModel k L) (θ : F ≃+* M'.C.functionField)
    (hθ : ∀ a : k, θ (algebraMap k F a) = baseToFunctionField M'.toBase a) : CurveModel k F :=
  let lam : L ≃+* F := M'.ffEquiv.trans θ.symm
  have hlam : ∀ a : k, lam (algebraMap k L a) = algebraMap k F a := fun a => by
    change θ.symm (M'.ffEquiv (algebraMap k L a)) = algebraMap k F a
    rw [M'.ffEquiv_algebraMap, ← hθ, RingEquiv.symm_apply_apply]
  { C := M'.C
    toBase := M'.toBase
    ffEquiv := θ
    ffEquiv_algebraMap := hθ
    placeOfPoint := fun x => placeMap lam hlam (M'.placeOfPoint x)
    placeOfPoint_bijective := (placeMap_bijective lam hlam).comp M'.placeOfPoint_bijective
    range_stalk_eq := fun x => by
      have h0 := M'.range_stalk_eq x
      rw [placeMap_toValuationSubring]
      have hcomp : (θ.symm : M'.C.functionField ≃+* F).toRingHom.comp
          (algebraMap (M'.C.presheaf.stalk x.1) M'.C.functionField) =
          lam.toRingHom.comp ((M'.ffEquiv.symm : M'.C.functionField ≃+* L).toRingHom.comp
            (algebraMap (M'.C.presheaf.stalk x.1) M'.C.functionField)) := by
        ext z
        change θ.symm _ = θ.symm (M'.ffEquiv (M'.ffEquiv.symm _))
        rw [RingEquiv.apply_symm_apply]
      rw [hcomp]
      ext y
      constructor
      · rintro ⟨z, rfl⟩
        have hz : (((M'.ffEquiv.symm : M'.C.functionField ≃+* L).toRingHom.comp
            (algebraMap (M'.C.presheaf.stalk x.1) M'.C.functionField)) z) ∈
            (M'.placeOfPoint x).toValuationSubring.toSubring := h0 ▸ ⟨z, rfl⟩
        change lam.symm.toRingHom (lam.toRingHom _) ∈ (M'.placeOfPoint x).toValuationSubring
        simpa using hz
      · intro hy
        change lam.symm.toRingHom y ∈ (M'.placeOfPoint x).toValuationSubring at hy
        have hy' : lam.symm y ∈ ((M'.ffEquiv.symm : M'.C.functionField ≃+* L).toRingHom.comp
            (algebraMap (M'.C.presheaf.stalk x.1) M'.C.functionField)).range := by
          rw [h0]; exact hy
        obtain ⟨z, hz⟩ := hy'
        refine ⟨z, ?_⟩
        change lam _ = y
        rw [hz]
        exact lam.apply_symm_apply y
    finset_subset_affineOpen := M'.finset_subset_affineOpen }

@[scoped simp] theorem curveModelOfRingEquiv_C (M' : CurveModel k L) (θ : F ≃+* M'.C.functionField)
    (hθ : ∀ a : k, θ (algebraMap k F a) = baseToFunctionField M'.toBase a) :
    (curveModelOfRingEquiv M' θ hθ).C = M'.C := rfl

@[scoped simp] theorem curveModelOfRingEquiv_toBase (M' : CurveModel k L) (θ : F ≃+* M'.C.functionField)
    (hθ : ∀ a : k, θ (algebraMap k F a) = baseToFunctionField M'.toBase a) :
    (curveModelOfRingEquiv M' θ hθ).toBase = M'.toBase := rfl

@[scoped simp] theorem curveModelOfRingEquiv_ffEquiv (M' : CurveModel k L) (θ : F ≃+* M'.C.functionField)
    (hθ : ∀ a : k, θ (algebraMap k F a) = baseToFunctionField M'.toBase a) :
    (curveModelOfRingEquiv M' θ hθ).ffEquiv = θ := rfl

end Transport

end ModularCurve.QExpModelBaseChange
p2m_reactivate "P2MW.S_ModularCurve_exists_curveModel_qExpFunctionFieldC_iso_pullback_germ_eq_coeffMap_of_ringHom.ModularCurve P2MW.S_ModularCurve_exists_curveModel_qExpFunctionFieldC_iso_pullback_germ_eq_coeffMap_of_ringHom.ModularCurve.QExpModelBaseChange"
p2m_reactivate "P2MW.S_ModularCurve_exists_curveModel_qExpFunctionFieldC_iso_pullback_germ_eq_coeffMap_of_ringHom.ModularCurve"

open ModularCurve.QExpModelBaseChange

theorem solution
    {κ : Type u} [Field κ] [IsAlgClosed κ] {k : Type u} [Field k] [IsAlgClosed k] (ι : κ →+* k)
    (Γ : Subgroup SL(2, ℤ)) (M₀ : CurveModel κ ↥(qExpFunctionFieldC κ Γ)) :
    ∃ (Mk : CurveModel k ↥(qExpFunctionFieldC k Γ))
      (g : Mk.C ≅ pullback M₀.toBase (Spec.map (CommRingCat.ofHom ι)))
      (_ : g.hom ≫ pullback.snd M₀.toBase (Spec.map (CommRingCat.ofHom ι)) = Mk.toBase)
      (ψ : ↥(qExpFunctionFieldC κ Γ) →+* ↥(qExpFunctionFieldC k Γ))
      (_ : ∀ f : ↥(qExpFunctionFieldC κ Γ),
        ((ψ f : ↥(qExpFunctionFieldC k Γ)) : LaurentSeries k) =
          coeffMap ι ((f : ↥(qExpFunctionFieldC κ Γ)) : LaurentSeries κ)),
      ∀ (U : M₀.C.Opens) [Nonempty (Scheme.Opens.toScheme U)]
        [Nonempty (Scheme.Opens.toScheme
          ((g.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom ι))) ⁻¹ᵁ U))]
        (s : Γ(M₀.C, U)),
        Mk.ffEquiv.symm
            (Mk.C.germToFunctionField
              ((g.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom ι))) ⁻¹ᵁ U)
              (((g.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom ι))).app U).hom s)) =
          ψ (M₀.ffEquiv.symm (M₀.C.germToFunctionField U s)) := by
  classical

  haveI : Smooth M₀.toBase := SmoothOfRelativeDimension.smooth 1 M₀.toBase
  haveI : GeometricallyIntegral M₀.toBase := AlgebraicGeometry.geometricallyIntegral_of_isAlgClosed M₀.toBase
  have hA := AlgebraicGeometry.SmoothProperCurve.exists_curveModel_iso_pullback_of_isAlgClosed κ M₀.toBase k
    (Spec.map (CommRingCat.ofHom ι))
  obtain ⟨L, _instL, _instAlg, _instCurve, _instEft, M', e', he'⟩ := hA

  have hP : IsPullback (e'.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom ι))) M'.toBase M₀.toBase
      (Spec.map (CommRingCat.ofHom ι)) :=
    IsPullback.of_iso_pullback ⟨by rw [Category.assoc, pullback.condition, ← Category.assoc, he']⟩ e' rfl he'
  letI algX : Algebra κ M₀.C.functionField := (baseToFunctionField M₀.toBase).toAlgebra
  letI algY : Algebra k M'.C.functionField := (baseToFunctionField M'.toBase).toAlgebra
  obtain ⟨φ, hφκ, hφgerm, hφli, hφgen⟩ :=
    AlgebraicGeometry.exists_ringHom_functionField_germ_eq_and_linearIndependent_of_isPullback ι M₀.toBase
      M'.toBase (e'.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom ι))) hP

  let Ψ' : ↥(qExpFunctionFieldC κ Γ) →+* M'.C.functionField := φ.comp M₀.ffEquiv.toRingHom
  have hΨ' : ∀ c : κ, Ψ' (algebraMap κ _ c) = algebraMap k M'.C.functionField (ι c) := by
    intro c
    change φ (M₀.ffEquiv (algebraMap κ _ c)) = baseToFunctionField M'.toBase (ι c)
    rw [M₀.ffEquiv_algebraMap]
    exact hφκ c
  have hψ : ∀ c : κ, psi ι Γ (algebraMap κ _ c) = algebraMap k _ (ι c) := psi_algebraMap ι Γ
  let b := Basis.ofVectorSpace κ ↥(qExpFunctionFieldC κ Γ)
  have hli : LinearIndependent k (fun j => psi ι Γ (b j)) := linearIndependent_psi ι Γ b.linearIndependent
  have hli' : LinearIndependent k (fun j => Ψ' (b j)) := by

    letI := M₀.functionFieldAlgebra
    have h1 : LinearIndependent κ (fun j => M₀.ffEquiv (b j)) := by
      have := b.linearIndependent.map' (M₀.ffAlgEquiv.toLinearEquiv.toLinearMap)
        (LinearMap.ker_eq_bot.mpr M₀.ffAlgEquiv.toLinearEquiv.injective)
      exact this
    exact hφli _ h1
  have hgen : ∀ z : ↥(qExpFunctionFieldC k Γ), ∃ u ∈ Algebra.adjoin k (Set.range (psi ι Γ)),
      ∃ v ∈ Algebra.adjoin k (Set.range (psi ι Γ)), v ≠ 0 ∧ z * v = u := psi_gen ι Γ
  have hrange : Set.range Ψ' = Set.range φ := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩; exact ⟨_, rfl⟩
    · rintro ⟨y, rfl⟩
      refine ⟨M₀.ffEquiv.symm y, ?_⟩
      change φ (M₀.ffEquiv (M₀.ffEquiv.symm y)) = φ y
      rw [RingEquiv.apply_symm_apply]
  have hgen' : ∀ z : M'.C.functionField, ∃ u ∈ Algebra.adjoin k (Set.range Ψ'),
      ∃ v ∈ Algebra.adjoin k (Set.range Ψ'), v ≠ 0 ∧ z * v = u := by
    rw [hrange]; exact hφgen

  obtain ⟨θ, hθψ, hθk⟩ := exists_ringEquiv_apply_eq k ι (psi ι Γ) hψ Ψ' hΨ' b hli hli' hgen hgen'

  let Mk : CurveModel k ↥(qExpFunctionFieldC k Γ) := curveModelOfRingEquiv M' θ hθk
  refine ⟨Mk, e', he', psi ι Γ, fun f => rfl, ?_⟩
  intro U hU hU' s
  haveI : Nonempty (Scheme.Opens.toScheme
      ((e'.hom ≫ pullback.fst M₀.toBase (Spec.map (CommRingCat.ofHom ι))) ⁻¹ᵁ U)) := hU'
  have h1 : φ (M₀.C.germToFunctionField U s) = Ψ' (M₀.ffEquiv.symm (M₀.C.germToFunctionField U s)) := by
    change _ = φ (M₀.ffEquiv (M₀.ffEquiv.symm _))
    rw [RingEquiv.apply_symm_apply]
  have h2 := hφgerm U s
  have h3 : θ.symm (φ (M₀.C.germToFunctionField U s)) =
      psi ι Γ (M₀.ffEquiv.symm (M₀.C.germToFunctionField U s)) := by
    rw [h1, ← hθψ, RingEquiv.symm_apply_apply]
  exact ((congrArg θ.symm h2).symm.trans h3)

end
p2m_reactivate "P2MW.S_ModularCurve_exists_curveModel_qExpFunctionFieldC_iso_pullback_germ_eq_coeffMap_of_ringHom.ModularCurve P2MW.S_ModularCurve_exists_curveModel_qExpFunctionFieldC_iso_pullback_germ_eq_coeffMap_of_ringHom.ModularCurve.QExpModelBaseChange"

end S_ModularCurve_exists_curveModel_qExpFunctionFieldC_iso_pullback_germ_eq_coeffMap_of_ringHom
end P2MW
export P2MW.S_ModularCurve_exists_curveModel_qExpFunctionFieldC_iso_pullback_germ_eq_coeffMap_of_ringHom (solution)
