-- Prove2me | solution 1 for ModularCurve.FullLevel.Diamond.exists_moduliHasse_commonChart_nodes_igusaSep_levelField_of_nodes_fixedField_of_algEquiv_of_eq_two_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/1272a424-edcc-5fc6-be5e-1a72c096bc9c

import Mathlib
import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_CoordRing
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_AdicCompletionRingFunctoriality
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_ModularCurve_qExpand_coeffEmb_mem_laurentBaseChange_xHFunctionField_of_mem_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_FullLevel_exists_isLevelAutAt_of_mem_gamma0_of_eq_levelH_inf_ker
import Theorems.Thm_ModularCurve_FullLevel_exists_isLevelAutAt_conj_of_isLevelAutAt_of_isPrimitiveRoot_of_eq_levelH_inf_ker
import Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_finite_and_natCard_dvd_of_eq_closure_isLevelAutAt_gamma_of_dvd
import Theorems.Thm_AlgebraicCurve_Place_exists_restrictAlong_eq_of_finiteDimensional_fieldRange
import Theorems.Thm_ModularCurve_coeffMap_injective
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Theorems.Thm_ModularCurve_FullLevel_jqNModC_mem_fieldBar
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_coeffEmb_jq_ne_zero
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_Diamond_exists_moduliHasse_commonChart_nodes_igusaSep_levelField_of_nodes_fixedField_of_algEquiv_of_eq_two_of_dvd
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 3200000
set_option maxHeartbeats 0

attribute [local instance 10000] SubalgebraClass.toAlgebra Algebra.toSMul Algebra.toModule
attribute [local instance 10001] AdicCompletion.instAlgebra

namespace S3GlueKit
open IsLocalRing

section image
variable {K L : Type*} [Field K] [Field L]

def imS (e : K ≃+* L) (O : Subring K) : Subring L := O.map e.toRingHom

theorem mem_imS_iff {e : K ≃+* L} {O : Subring K} {y : L} : y ∈ imS e O ↔ e.symm y ∈ O := by
  unfold imS
  rw [Subring.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    show e.symm (e x) ∈ O
    rw [e.symm_apply_apply]; exact hx
  · intro h; exact ⟨e.symm y, h, e.apply_symm_apply y⟩

theorem apply_mem_imS_iff {e : K ≃+* L} {O : Subring K} {x : K} : e x ∈ imS e O ↔ x ∈ O := by
  rw [mem_imS_iff, e.symm_apply_apply]

theorem imS_injective (e : K ≃+* L) : Function.Injective (imS e) := by
  intro O O' h
  ext x
  rw [← apply_mem_imS_iff (e := e), h, apply_mem_imS_iff]

theorem card_image_imS [DecidableEq (Subring L)] (e : K ≃+* L) (s : Finset (Subring K)) : (s.image (imS e)).card = s.card :=
  Finset.card_image_of_injective s (imS_injective e)

theorem mem_image_imS_iff [DecidableEq (Subring L)] (e : K ≃+* L) (s : Finset (Subring K)) (O : Subring L) :
    O ∈ s.image (imS e) ↔ ∃ O₀ ∈ s, O = imS e O₀ := by
  rw [Finset.mem_image]
  exact ⟨fun ⟨O₀, h, h'⟩ => ⟨O₀, h, h'.symm⟩, fun ⟨O₀, h, h'⟩ => ⟨O₀, h, h'.symm⟩⟩

def imSEquiv (e : K ≃+* L) (O : Subring K) : O ≃+* imS e O := RingEquiv.subringMap (s := O) e

@[scoped simp] theorem coe_imSEquiv (e : K ≃+* L) (O : Subring K) (x : O) : ((imSEquiv e O x : imS e O) : L) = e x := rfl

theorem imSEquiv_mk (e : K ≃+* L) (O : Subring K) (x : K) (hx : x ∈ O) (hy : e x ∈ imS e O) :
    imSEquiv e O ⟨x, hx⟩ = ⟨e x, hy⟩ := Subtype.ext rfl

theorem isUnit_iff_of_equiv {R S : Type*} [Monoid R] [Monoid S] (f : R ≃* S) (x : R) : IsUnit (f x) ↔ IsUnit x :=
  ⟨fun h => by simpa using h.map f.symm.toMonoidHom, fun h => h.map f.toMonoidHom⟩

theorem isUnit_imS_iff (e : K ≃+* L) (O : Subring K) (x : K) (hx : x ∈ O) (hy : e x ∈ imS e O) :
    IsUnit (⟨e x, hy⟩ : imS e O) ↔ IsUnit (⟨x, hx⟩ : O) := by
  rw [← imSEquiv_mk e O x hx hy]
  exact isUnit_iff_of_equiv (imSEquiv e O).toMulEquiv _

theorem isLocalRing_imS (e : K ≃+* L) (O : Subring K) [IsLocalRing O] : IsLocalRing (imS e O) :=
  (imSEquiv e O).isLocalRing

theorem isNoetherianRing_imS (e : K ≃+* L) (O : Subring K) [IsNoetherianRing O] : IsNoetherianRing (imS e O) :=
  isNoetherianRing_of_ringEquiv O (imSEquiv e O)

end image

section completion
variable {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]

theorem map_maximalIdeal_le (e : R ≃+* S) : (maximalIdeal R).map (e : R →+* S) ≤ maximalIdeal S := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
  rw [mem_maximalIdeal, mem_nonunits_iff] at hx
  intro hu; exact hx (by simpa using hu.map (e.symm : S →* R))

theorem exists_completion_transport (e : R ≃+* S) :
    ∃ Ψ : AdicCompletion (maximalIdeal S) S ≃+* AdicCompletion (maximalIdeal R) R,
      ∀ x : R, Ψ (algebraMap S (AdicCompletion (maximalIdeal S) S) (e x)) =
        algebraMap R (AdicCompletion (maximalIdeal R) R) x := by
  let e' : S ≃ₐ[ℤ] R := AlgEquiv.ofRingEquiv (f := e.symm) (fun n => map_intCast e.symm n)
  have he : (maximalIdeal S).map (e' : S →ₐ[ℤ] R) ≤ maximalIdeal R := by
    have := map_maximalIdeal_le e.symm
    convert this using 2 <;> first | rfl | exact Subsingleton.elim _ _
  have he' : (maximalIdeal R).map (e'.symm : R →ₐ[ℤ] S) ≤ maximalIdeal S := by
    have := map_maximalIdeal_le e
    convert this using 2 <;> first | rfl | exact Subsingleton.elim _ _
  refine ⟨(AdicCompletion.mapAlgEquiv (maximalIdeal S) (maximalIdeal R) e' he he').toRingEquiv, fun x => ?_⟩
  have h1 : (AdicCompletion.mapAlgEquiv _ _ e' he he').toRingEquiv (algebraMap S _ (e x)) =
      AdicCompletion.mapₐ _ _ (e' : S →ₐ[ℤ] R) he (AdicCompletion.of _ S (e x)) := rfl
  rw [h1, AdicCompletion.mapₐ_of, AdicCompletion.algebraMap_apply]
  show AdicCompletion.of (maximalIdeal R) R (e.symm (e x)) = AdicCompletion.of (maximalIdeal R) R x
  rw [e.symm_apply_apply]

end completion

end S3GlueKit
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_moduliHasse_commonChart_nodes_igusaSep_levelField_of_nodes_fixedField_of_algEquiv_of_eq_two_of_dvd.S3GlueKit"

namespace S3GlueKit

open IsLocalRing

variable {K L : Type*} [Field K] [Field L]

def comapEquiv (e : K ≃+* L) (V : ValuationSubring L) : (V.comap (e : K →+* L)) ≃+* V where
  toFun x := ⟨e x, x.2⟩
  invFun y := ⟨e.symm y, by show e (e.symm y) ∈ V; rw [e.apply_symm_apply]; exact y.2⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_mul' x y := by ext; simp
  map_add' x y := by ext; simp

@[scoped simp] theorem coe_comapEquiv (e : K ≃+* L) (V : ValuationSubring L) (x : V.comap (e : K →+* L)) :
    ((comapEquiv e V x : V) : L) = e x := rfl

theorem isDiscreteValuationRing_comap (e : K ≃+* L) (V : ValuationSubring L) [IsDiscreteValuationRing V] :
    IsDiscreteValuationRing (V.comap (e : K →+* L)) :=
  let f := (comapEquiv e V).symm
  { toIsPrincipalIdealRing := IsPrincipalIdealRing.of_surjective f.toRingHom f.surjective
    toIsLocalRing := inferInstance
    not_a_field' := by
      intro h
      apply IsDiscreteValuationRing.not_a_field (R := V)
      rw [eq_bot_iff] at h ⊢
      intro y hy
      have : f y ∈ maximalIdeal _ := by
        rw [mem_maximalIdeal, mem_nonunits_iff] at hy ⊢
        exact fun hu => hy (by simpa using hu.map f.symm.toRingHom)
      have := h this
      rw [Ideal.mem_bot] at this ⊢
      simpa using congrArg f.symm this }

theorem mem_maximalIdeal_comap_iff (e : K ≃+* L) (V : ValuationSubring L) (x : V.comap (e : K →+* L)) :
    x ∈ maximalIdeal (V.comap (e : K →+* L)) ↔ (comapEquiv e V x) ∈ maximalIdeal V := by
  rw [mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, not_iff_not]
  exact ⟨fun h => by simpa using h.map (comapEquiv e V).toRingHom,
    fun h => by simpa using h.map (comapEquiv e V).symm.toRingHom⟩

theorem maximalIdeal_comap_eq_span (e : K ≃+* L) (V : ValuationSubring L) (π : V)
    (h : maximalIdeal V = Ideal.span {π}) :
    maximalIdeal (V.comap (e : K →+* L)) = Ideal.span {(comapEquiv e V).symm π} := by
  apply le_antisymm
  · intro x hx
    rw [mem_maximalIdeal_comap_iff, h, Ideal.mem_span_singleton] at hx
    obtain ⟨c, hc⟩ := hx
    rw [Ideal.mem_span_singleton]
    refine ⟨(comapEquiv e V).symm c, ?_⟩
    apply (comapEquiv e V).injective
    rw [map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
    exact hc
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, mem_maximalIdeal_comap_iff,
      RingEquiv.apply_symm_apply, h]
    exact Ideal.mem_span_singleton_self π

section algEquiv
variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

theorem algEquiv_symm_toRingEquiv_algebraMap (φ : A ≃ₐ[R] B) (x : R) :
    φ.symm.toRingEquiv (algebraMap R B x) = algebraMap R A x := φ.symm.commutes x

theorem algEquiv_symm_toRingEquiv_apply_apply (φ : A ≃ₐ[R] B) (x : A) :
    φ.symm.toRingEquiv (φ x) = x := φ.symm_apply_apply x

end algEquiv
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_moduliHasse_commonChart_nodes_igusaSep_levelField_of_nodes_fixedField_of_algEquiv_of_eq_two_of_dvd.S3GlueKit"

theorem exists_mem_and_maximalIdeal_eq_span {K L : Type*} [Field K] [Field L] (e : K ≃+* L)
    (V : ValuationSubring L) (W : ValuationSubring K) (hW : W = V.comap (e : K →+* L))
    (π : L) (hπV : π ∈ V) (hmax : IsLocalRing.maximalIdeal V = Ideal.span {(⟨π, hπV⟩ : V)})
    (π' : K) (hπ' : e π' = π) :
    ∃ h : π' ∈ W, IsLocalRing.maximalIdeal W = Ideal.span {(⟨π', h⟩ : W)} := by
  subst hW
  have h : π' ∈ V.comap (e : K →+* L) := by show e π' ∈ V; rw [hπ']; exact hπV
  refine ⟨h, ?_⟩
  rw [maximalIdeal_comap_eq_span e V ⟨π, hπV⟩ hmax]
  congr 2
  apply Subtype.ext
  show e.symm π = π'
  rw [← hπ', e.symm_apply_apply]

theorem constants_mem_transport {k E F : Type*} [Field k] [Field E] [Field F] [Algebra k E] [Algebra k F]
    (K₀ : IntermediateField k E) (F₀ : IntermediateField k F) (φ : K₀ ≃ₐ[k] F₀)
    (W₀' : ValuationSubring K₀) (W₀ : ValuationSubring F₀)
    (memW₀ : ∀ f : F₀, f ∈ W₀ ↔ φ.symm.toRingEquiv f ∈ W₀')
    (P : k → Prop) (hK2a' : ∀ x : k, P x ↔ algebraMap k K₀ x ∈ W₀') (x : k) :
    P x ↔ algebraMap k F₀ x ∈ W₀ := by
  rw [hK2a', memW₀, algEquiv_symm_toRingEquiv_algebraMap]

section idealDict
variable {Ab Ak B₀ B : Type*} [CommRing Ab] [IsLocalRing Ab] [CommRing Ak] [IsDomain Ak] [IsLocalRing Ak]
  [CommRing B₀] [Algebra Ak B₀] [CommRing B]

end idealDict
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_moduliHasse_commonChart_nodes_igusaSep_levelField_of_nodes_fixedField_of_algEquiv_of_eq_two_of_dvd.S3GlueKit"

section smoothTransfer
variable {Ab Ak B₀ B : Type*} [CommRing Ab] [CommRing Ak] [CommRing B₀] [Algebra Ak B₀] [CommRing B]

end smoothTransfer
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_moduliHasse_commonChart_nodes_igusaSep_levelField_of_nodes_fixedField_of_algEquiv_of_eq_two_of_dvd.S3GlueKit"

theorem exists_emb (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (m : ℕ) [NeZero m]
    (ξ : ↥k₀) (hξ : IsPrimitiveRoot ξ m) :
    ∃ ι : ↥k₀ →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / m) := by
  haveI hQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    have h := AlgebraicClosure.isAlgebraic ℚ
    convert h <;> first | rfl | exact Subsingleton.elim _ _
  haveI : Algebra.IsAlgebraic ℚ ↥k₀ :=
    Algebra.IsAlgebraic.of_injective (k₀.val) (k₀.val).toRingHom.injective
  have hmin : minpoly ℚ ξ = Polynomial.cyclotomic m ℚ :=
    (Polynomial.cyclotomic_eq_minpoly_rat hξ (Nat.pos_of_ne_zero (NeZero.ne m))).symm
  have hroot : Complex.exp (2 * Real.pi * Complex.I / m) ∈ (minpoly ℚ ξ).rootSet ℂ := by
    rw [hmin, Polynomial.mem_rootSet]
    refine ⟨Polynomial.cyclotomic_ne_zero m ℚ, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact (Polynomial.isRoot_cyclotomic_iff.mpr (Complex.isPrimitiveRoot_exp m (NeZero.ne m))).eq_zero
  rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly ℂ ξ] at hroot
  obtain ⟨ψ, hψ⟩ := hroot
  exact ⟨ψ.toRingHom, hψ⟩

end S3GlueKit
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_moduliHasse_commonChart_nodes_igusaSep_levelField_of_nodes_fixedField_of_algEquiv_of_eq_two_of_dvd.S3GlueKit"

namespace S3GlueKit
open IsLocalRing

section nodeTransport
variable {k E₀ E₁ : Type*} [Field k] [Field E₀] [Field E₁] [Algebra k E₀] [Algebra k E₁]

theorem toRingEquiv_apply' (φ : E₀ ≃ₐ[k] E₁) (x : E₀) : φ.toRingEquiv x = φ x := rfl
theorem toRingEquiv_algebraMap' (φ : E₀ ≃ₐ[k] E₁) (x : k) : φ.toRingEquiv (algebraMap k E₀ x) = algebraMap k E₁ x :=
  φ.commutes x

theorem imS_le_comap (φ : E₀ ≃ₐ[k] E₁) (O₀ : Subring E₀) (W' : ValuationSubring E₀)
    (h : ∀ f : E₀, f ∈ O₀ → f ∈ W') (f : E₁) (hf : f ∈ imS φ.toRingEquiv O₀) :
    f ∈ W'.comap (φ.symm.toRingEquiv : E₁ →+* E₀) := by
  rw [mem_imS_iff] at hf
  exact h _ hf

theorem const_imS (φ : E₀ ≃ₐ[k] E₁) (O₀ : Subring E₀) (PA : k → Prop)
    (h : ∀ x : k, PA x ↔ algebraMap k E₀ x ∈ O₀) (x : k) : PA x ↔ algebraMap k E₁ x ∈ imS φ.toRingEquiv O₀ := by
  rw [h, ← toRingEquiv_algebraMap' φ, apply_mem_imS_iff]

theorem algebraMap_mem_imS (φ : E₀ ≃ₐ[k] E₁) (O₀ : Subring E₀) (x : k) (hx : algebraMap k E₀ x ∈ O₀) :
    algebraMap k E₁ x ∈ imS φ.toRingEquiv O₀ := by
  rw [← toRingEquiv_algebraMap' φ, apply_mem_imS_iff]; exact hx

theorem algebraMap_mem_of_mem_imS (φ : E₀ ≃ₐ[k] E₁) (O₀ : Subring E₀) (x : k) (hx : algebraMap k E₁ x ∈ imS φ.toRingEquiv O₀) :
    algebraMap k E₀ x ∈ O₀ := by
  rw [← toRingEquiv_algebraMap' φ, apply_mem_imS_iff] at hx; exact hx

theorem imSEquiv_algebraMap (φ : E₀ ≃ₐ[k] E₁) (O₀ : Subring E₀) (x : k) (hx : algebraMap k E₀ x ∈ O₀)
    (hx' : algebraMap k E₁ x ∈ imS φ.toRingEquiv O₀) :
    imSEquiv φ.toRingEquiv O₀ ⟨algebraMap k E₀ x, hx⟩ = ⟨algebraMap k E₁ x, hx'⟩ :=
  Subtype.ext (φ.commutes x)

theorem resid_imS (φ : E₀ ≃ₐ[k] E₁) (O₀ : Subring E₀) (PA : k → Prop)
    (h : ∀ (f : E₀) (hf : f ∈ O₀), ∃ (x : k) (hx : algebraMap k E₀ x ∈ O₀), PA x ∧ ¬ IsUnit ((⟨f, hf⟩ : O₀) - ⟨_, hx⟩))
    (f : E₁) (hf : f ∈ imS φ.toRingEquiv O₀) :
    ∃ (x : k) (hx : algebraMap k E₁ x ∈ imS φ.toRingEquiv O₀), PA x ∧ ¬ IsUnit ((⟨f, hf⟩ : imS φ.toRingEquiv O₀) - ⟨_, hx⟩) := by
  have hf₀ : φ.toRingEquiv.symm f ∈ O₀ := mem_imS_iff.mp hf
  obtain ⟨x, hx, hPA, hnu⟩ := h _ hf₀
  refine ⟨x, algebraMap_mem_imS φ O₀ x hx, hPA, fun hu => hnu ?_⟩
  have key : imSEquiv φ.toRingEquiv O₀ ((⟨_, hf₀⟩ : O₀) - ⟨_, hx⟩) =
      (⟨f, hf⟩ : imS φ.toRingEquiv O₀) - ⟨_, algebraMap_mem_imS φ O₀ x hx⟩ := by
    rw [map_sub, imSEquiv_algebraMap φ O₀ x hx (algebraMap_mem_imS φ O₀ x hx)]
    congr 1
    apply Subtype.ext
    show φ.toRingEquiv (φ.toRingEquiv.symm f) = f
    exact φ.toRingEquiv.apply_symm_apply f
  rw [← isUnit_iff_of_equiv (imSEquiv φ.toRingEquiv O₀).toMulEquiv, RingEquiv.toMulEquiv_eq_coe,
    RingEquiv.coe_toMulEquiv, key]
  exact hu

theorem not_isUnit_sub_imS (φ : E₀ ≃ₐ[k] E₁) (O₀ : Subring E₀) (u : E₀) (hu : u ∈ O₀)
    (hu' : φ u ∈ imS φ.toRingEquiv O₀) (c : k) (hc : algebraMap k E₀ c ∈ O₀) (hc' : algebraMap k E₁ c ∈ imS φ.toRingEquiv O₀)
    (h : ¬ IsUnit ((⟨u, hu⟩ : O₀) - ⟨_, hc⟩)) : ¬ IsUnit ((⟨φ u, hu'⟩ : imS φ.toRingEquiv O₀) - ⟨_, hc'⟩) := by
  intro h1; apply h
  have key : imSEquiv φ.toRingEquiv O₀ ((⟨u, hu⟩ : O₀) - ⟨_, hc⟩) = (⟨φ u, hu'⟩ : imS φ.toRingEquiv O₀) - ⟨_, hc'⟩ := by
    rw [map_sub, imSEquiv_algebraMap φ O₀ c hc hc']; rfl
  rw [← isUnit_iff_of_equiv (imSEquiv φ.toRingEquiv O₀).toMulEquiv, RingEquiv.toMulEquiv_eq_coe,
    RingEquiv.coe_toMulEquiv, key]
  exact h1

theorem apply_mem_comap_symm_iff (φ : E₀ ≃ₐ[k] E₁) (W' : ValuationSubring E₀) (u : E₀) :
    φ u ∈ W'.comap (φ.symm.toRingEquiv : E₁ →+* E₀) ↔ u ∈ W' := by
  rw [ValuationSubring.mem_comap]
  show φ.symm.toRingEquiv (φ u) ∈ W' ↔ u ∈ W'
  rw [algEquiv_symm_toRingEquiv_apply_apply]

theorem mk_apply_mem_maximalIdeal_comap_iff (φ : E₀ ≃ₐ[k] E₁) (W' : ValuationSubring E₀) (u : E₀) (hu : u ∈ W')
    (hu' : φ u ∈ W'.comap (φ.symm.toRingEquiv : E₁ →+* E₀)) :
    (⟨φ u, hu'⟩ : W'.comap (φ.symm.toRingEquiv : E₁ →+* E₀)) ∈ maximalIdeal _ ↔ (⟨u, hu⟩ : W') ∈ maximalIdeal _ := by
  rw [mem_maximalIdeal_comap_iff]
  have : comapEquiv φ.symm.toRingEquiv W' ⟨φ u, hu'⟩ = ⟨u, hu⟩ :=
    Subtype.ext (algEquiv_symm_toRingEquiv_apply_apply φ u)
  rw [this]

theorem forall_mem_maximalIdeal_transport (φ : E₀ ≃ₐ[k] E₁) (W' : ValuationSubring E₀) (u : E₀)
    (h : ∀ hu : u ∈ W', (⟨u, hu⟩ : W') ∈ maximalIdeal _)
    (hu' : φ u ∈ W'.comap (φ.symm.toRingEquiv : E₁ →+* E₀)) :
    (⟨φ u, hu'⟩ : W'.comap (φ.symm.toRingEquiv : E₁ →+* E₀)) ∈ maximalIdeal _ := by
  rw [mk_apply_mem_maximalIdeal_comap_iff φ W' u ((apply_mem_comap_symm_iff φ W' u).mp hu') hu']
  exact h _

theorem forall_not_mem_maximalIdeal_transport (φ : E₀ ≃ₐ[k] E₁) (W' : ValuationSubring E₀) (u : E₀)
    (h : ∀ hu : u ∈ W', (⟨u, hu⟩ : W') ∉ maximalIdeal _)
    (hu' : φ u ∈ W'.comap (φ.symm.toRingEquiv : E₁ →+* E₀)) :
    (⟨φ u, hu'⟩ : W'.comap (φ.symm.toRingEquiv : E₁ →+* E₀)) ∉ maximalIdeal _ := by
  rw [mk_apply_mem_maximalIdeal_comap_iff φ W' u ((apply_mem_comap_symm_iff φ W' u).mp hu') hu']
  exact h _

theorem resTrans_transport (φ : E₀ ≃ₐ[k] E₁) (W' : ValuationSubring E₀) (PA : k → Prop)
    (t : W')
    (h : ∀ p : Polynomial k, (∀ n, PA (p.coeff n)) →
      (∃ hm : Polynomial.aeval (t : E₀) p ∈ W', (⟨_, hm⟩ : W') ∈ maximalIdeal _) →
        ∀ n, ∃ hc : algebraMap k E₀ (p.coeff n) ∈ W', (⟨_, hc⟩ : W') ∈ maximalIdeal _) :
    ∃ t' : W'.comap (φ.symm.toRingEquiv : E₁ →+* E₀), ∀ p : Polynomial k, (∀ n, PA (p.coeff n)) →
      (∃ hm : Polynomial.aeval (t' : E₁) p ∈ W'.comap (φ.symm.toRingEquiv : E₁ →+* E₀), (⟨_, hm⟩ : W'.comap (φ.symm.toRingEquiv : E₁ →+* E₀)) ∈ maximalIdeal _) →
        ∀ n, ∃ hc : algebraMap k E₁ (p.coeff n) ∈ W'.comap (φ.symm.toRingEquiv : E₁ →+* E₀), (⟨_, hc⟩ : W'.comap (φ.symm.toRingEquiv : E₁ →+* E₀)) ∈ maximalIdeal _ := by
  refine ⟨⟨φ (t : E₀), (apply_mem_comap_symm_iff φ W' _).mpr t.2⟩, fun p hp hm n => ?_⟩
  obtain ⟨hm, hmax⟩ := hm
  have hae : Polynomial.aeval (φ (t : E₀)) p = φ (Polynomial.aeval (t : E₀) p) :=
    (Polynomial.aeval_algHom_apply (φ : E₀ →ₐ[k] E₁) (t : E₀) p)
  have hm₀ : Polynomial.aeval (t : E₀) p ∈ W' := by
    rw [← apply_mem_comap_symm_iff φ W', ← hae]; exact hm
  have hmax₀ : (⟨_, hm₀⟩ : W') ∈ maximalIdeal _ := by
    have hm' : φ (Polynomial.aeval (t : E₀) p) ∈ W'.comap (φ.symm.toRingEquiv : E₁ →+* E₀) := by rw [← hae]; exact hm
    rw [← mk_apply_mem_maximalIdeal_comap_iff φ W' _ hm₀ hm']
    have : (⟨φ (Polynomial.aeval (t : E₀) p), hm'⟩ : W'.comap (φ.symm.toRingEquiv : E₁ →+* E₀)) = ⟨_, hm⟩ :=
      Subtype.ext hae.symm
    rw [this]; exact hmax
  obtain ⟨hc, hcmax⟩ := h p hp ⟨hm₀, hmax₀⟩ n
  have hc' : algebraMap k E₁ (p.coeff n) ∈ W'.comap (φ.symm.toRingEquiv : E₁ →+* E₀) := by
    rw [← φ.commutes, apply_mem_comap_symm_iff]; exact hc
  refine ⟨hc', ?_⟩
  have : (⟨algebraMap k E₁ (p.coeff n), hc'⟩ : W'.comap (φ.symm.toRingEquiv : E₁ →+* E₀)) =
      ⟨φ (algebraMap k E₀ (p.coeff n)), by rw [apply_mem_comap_symm_iff]; exact hc⟩ := Subtype.ext (φ.commutes _).symm
  rw [this, mk_apply_mem_maximalIdeal_comap_iff φ W' _ hc]
  exact hcmax

end nodeTransport
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_moduliHasse_commonChart_nodes_igusaSep_levelField_of_nodes_fixedField_of_algEquiv_of_eq_two_of_dvd.S3GlueKit"

end S3GlueKit
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_moduliHasse_commonChart_nodes_igusaSep_levelField_of_nodes_fixedField_of_algEquiv_of_eq_two_of_dvd.S3GlueKit"

namespace S3GlueKit
open IsLocalRing

section lawTransport
variable {k E F : Type*} [Field k] [Field E] [Field F] [Algebra k E] [Algebra k F]

theorem law_transport
    (K₀ : IntermediateField k E) (F₀ : IntermediateField k F) (φ : K₀ ≃ₐ[k] F₀)
    (Wx' : ValuationSubring K₀) (O₀ : Subring K₀)
    (PA : k → Prop) (P : ∀ c : k, PA c → Prop) (R0 RS : Prop)
    (y : E)
    (hup : ∃ hF : y ∈ K₀, (⟨y, hF⟩ : K₀) ∈ Wx' ∧
      (∀ hW : (⟨y, hF⟩ : K₀) ∈ Wx', (⟨_, hW⟩ : Wx') ∈ maximalIdeal Wx' ↔ R0) ∧
      (RS → (⟨y, hF⟩ : K₀) ∈ O₀ ∧
        ∀ (hO : (⟨y, hF⟩ : K₀) ∈ O₀) (c : k) (hc : PA c) (hcO : algebraMap k K₀ c ∈ O₀),
          P c hc → ¬ IsUnit ((⟨_, hO⟩ : O₀) - ⟨_, hcO⟩)))
    (v : F) (hv : ∀ hF : y ∈ K₀, ((φ ⟨y, hF⟩ : F₀) : F) = v) :
    ∃ hF : v ∈ F₀, (⟨v, hF⟩ : F₀) ∈ Wx'.comap (φ.symm.toRingEquiv : F₀ →+* K₀) ∧
      (∀ hW : (⟨v, hF⟩ : F₀) ∈ Wx'.comap (φ.symm.toRingEquiv : F₀ →+* K₀),
        (⟨_, hW⟩ : Wx'.comap (φ.symm.toRingEquiv : F₀ →+* K₀)) ∈ maximalIdeal _ ↔ R0) ∧
      (RS → (⟨v, hF⟩ : F₀) ∈ imS φ.toRingEquiv O₀ ∧
        ∀ (hO : (⟨v, hF⟩ : F₀) ∈ imS φ.toRingEquiv O₀) (c : k) (hc : PA c)
          (hcO : algebraMap k F₀ c ∈ imS φ.toRingEquiv O₀),
          P c hc → ¬ IsUnit ((⟨_, hO⟩ : imS φ.toRingEquiv O₀) - ⟨_, hcO⟩)) := by
  obtain ⟨hF', hW', hiff, hreg⟩ := hup
  have hvF : v ∈ F₀ := by rw [← hv hF']; exact (φ _).2
  have hxv : (⟨v, hvF⟩ : F₀) = φ ⟨y, hF'⟩ := Subtype.ext (hv hF').symm
  refine ⟨hvF, ?_, ?_, ?_⟩
  · rw [hxv, apply_mem_comap_symm_iff]; exact hW'
  · intro hW
    have hW1 : φ ⟨y, hF'⟩ ∈ Wx'.comap (φ.symm.toRingEquiv : F₀ →+* K₀) := by rw [← hxv]; exact hW
    have : (⟨_, hW⟩ : Wx'.comap (φ.symm.toRingEquiv : F₀ →+* K₀)) = ⟨φ ⟨y, hF'⟩, hW1⟩ := Subtype.ext hxv
    rw [this, mk_apply_mem_maximalIdeal_comap_iff φ Wx' _ hW' hW1]
    exact hiff hW'
  · intro hRS
    obtain ⟨hO', hunit⟩ := hreg hRS
    have hO1 : φ ⟨y, hF'⟩ ∈ imS φ.toRingEquiv O₀ := (apply_mem_imS_iff (e := φ.toRingEquiv)).mpr hO'
    refine ⟨by rw [hxv]; exact hO1, fun hO c hc hcO hP => ?_⟩
    have hcO₀ : algebraMap k K₀ c ∈ O₀ := algebraMap_mem_of_mem_imS φ O₀ c hcO
    have : (⟨_, hO⟩ : imS φ.toRingEquiv O₀) = ⟨φ ⟨y, hF'⟩, hO1⟩ := Subtype.ext hxv
    rw [this]
    exact not_isUnit_sub_imS φ O₀ _ hO' hO1 c hcO₀ hcO (hunit hO' c hc hcO₀ hP)

theorem coverHyp_transport
    (K₀ : IntermediateField k E) (F₀ : IntermediateField k F) (φ : K₀ ≃ₐ[k] F₀)
    (V : ValuationSubring F₀) (PA : k → Prop) (P : ∀ c : k, PA c → Prop)
    (y : E) (hyK : y ∈ K₀) (v : F) (hv : ((φ ⟨y, hyK⟩ : F₀) : F) = v)
    (hd : ∃ hF : v ∈ F₀, (⟨v, hF⟩ : F₀) ∈ V ∧
      ∀ (c : k) (hc : PA c), P c hc → ∃ hm : (⟨v, hF⟩ : F₀) - algebraMap k F₀ c ∈ V, (⟨_, hm⟩ : V) ∈ maximalIdeal V) :
    (⟨y, hyK⟩ : K₀) ∈ V.comap (φ.toRingEquiv : K₀ →+* F₀) ∧
      ∀ (c : k) (hc : PA c), P c hc →
        ∃ hm : (⟨y, hyK⟩ : K₀) - algebraMap k K₀ c ∈ V.comap (φ.toRingEquiv : K₀ →+* F₀),
          (⟨_, hm⟩ : V.comap (φ.toRingEquiv : K₀ →+* F₀)) ∈ maximalIdeal _ := by
  obtain ⟨hF, hV, hm⟩ := hd
  have hxv : (⟨v, hF⟩ : F₀) = φ ⟨y, hyK⟩ := Subtype.ext hv.symm
  refine ⟨?_, fun c hc hP => ?_⟩
  · show φ.toRingEquiv ⟨y, hyK⟩ ∈ V; rw [toRingEquiv_apply', ← hxv]; exact hV
  · obtain ⟨hm1, hmax⟩ := hm c hc hP
    have heq : φ.toRingEquiv ((⟨y, hyK⟩ : K₀) - algebraMap k K₀ c) = (⟨v, hF⟩ : F₀) - algebraMap k F₀ c := by
      rw [map_sub, toRingEquiv_algebraMap', toRingEquiv_apply', hxv]
    have hm0 : (⟨y, hyK⟩ : K₀) - algebraMap k K₀ c ∈ V.comap (φ.toRingEquiv : K₀ →+* F₀) := by
      show φ.toRingEquiv _ ∈ V; rw [heq]; exact hm1
    refine ⟨hm0, ?_⟩
    rw [mem_maximalIdeal_comap_iff]
    have : comapEquiv φ.toRingEquiv V ⟨_, hm0⟩ = ⟨_, hm1⟩ := Subtype.ext heq
    rw [this]; exact hmax

theorem coverConst_transport (K₀ : IntermediateField k E) (F₀ : IntermediateField k F) (φ : K₀ ≃ₐ[k] F₀)
    (V : ValuationSubring F₀) (PA : k → Prop)
    (h : ∀ x : k, PA x ↔ algebraMap k F₀ x ∈ V) (x : k) :
    PA x ↔ algebraMap k K₀ x ∈ V.comap (φ.toRingEquiv : K₀ →+* F₀) := by
  rw [h, ValuationSubring.mem_comap]
  show _ ↔ φ.toRingEquiv (algebraMap k K₀ x) ∈ V
  rw [toRingEquiv_algebraMap']

theorem coverLeft_transport
    (O : Type*) [CommRing O] [Algebra O E]
    (K₀ : IntermediateField k E) (F₀ : IntermediateField k F) (φ : K₀ ≃ₐ[k] F₀) (B₀ : Subalgebra O E)
    (B : Subring F)
    (hB : ∀ y : F, y ∈ B ↔ ∃ x : K₀, x ∈ B₀.toSubring.comap (algebraMap K₀ E) ∧
      y = ((algebraMap F₀ F).comp φ.toAlgHom.toRingHom) x)
    (V : ValuationSubring F₀)
    (h : ∀ f : E, f ∈ B₀ → ∃ hf : f ∈ K₀, (⟨f, hf⟩ : K₀) ∈ V.comap (φ.toRingEquiv : K₀ →+* F₀))
    (f : F) (hf : f ∈ B) : ∃ hf : f ∈ F₀, (⟨f, hf⟩ : F₀) ∈ V := by
  obtain ⟨x, hx, rfl⟩ := (hB f).mp hf
  obtain ⟨hxK, hxV⟩ := h (x : E) (Subring.mem_comap.mp hx)
  refine ⟨(φ x).2, ?_⟩
  have h1 : (⟨((algebraMap F₀ F).comp φ.toAlgHom.toRingHom) x, (φ x).2⟩ : F₀) = φ x := Subtype.ext rfl
  have h2 : (⟨(x : E), hxK⟩ : K₀) = x := Subtype.ext rfl
  rw [h1]; rw [h2] at hxV; exact hxV

end lawTransport
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_moduliHasse_commonChart_nodes_igusaSep_levelField_of_nodes_fixedField_of_algEquiv_of_eq_two_of_dvd.S3GlueKit"

section coverRight
variable {k E₀ E₁ : Type*} [Field k] [Field E₀] [Field E₁] [Algebra k E₀] [Algebra k E₁]

theorem coverRight_transport (φ : E₀ ≃ₐ[k] E₁) (V : ValuationSubring E₁) (O₀ : Subring E₀)
    (h : ∀ (f : E₀) (hfO : f ∈ O₀), f ∈ V.comap (φ.toRingEquiv : E₀ →+* E₁) ∧
      (¬ IsUnit (⟨f, hfO⟩ : O₀) → ∀ hfV : f ∈ V.comap (φ.toRingEquiv : E₀ →+* E₁),
        (⟨f, hfV⟩ : V.comap (φ.toRingEquiv : E₀ →+* E₁)) ∈ maximalIdeal _))
    (f : E₁) (hfO : f ∈ imS φ.toRingEquiv O₀) :
    f ∈ V ∧ (¬ IsUnit (⟨f, hfO⟩ : imS φ.toRingEquiv O₀) → ∀ hfV : f ∈ V, (⟨f, hfV⟩ : V) ∈ maximalIdeal V) := by
  have hf₀ : φ.toRingEquiv.symm f ∈ O₀ := mem_imS_iff.mp hfO
  obtain ⟨hV₀, hdom⟩ := h _ hf₀
  have hfeq : φ.toRingEquiv (φ.toRingEquiv.symm f) = f := φ.toRingEquiv.apply_symm_apply f
  refine ⟨by have : φ.toRingEquiv (φ.toRingEquiv.symm f) ∈ V := hV₀; rwa [hfeq] at this, fun hnu hfV => ?_⟩
  have hnu₀ : ¬ IsUnit (⟨_, hf₀⟩ : O₀) := by
    intro hu; apply hnu
    have : imSEquiv φ.toRingEquiv O₀ ⟨_, hf₀⟩ = ⟨f, hfO⟩ := Subtype.ext hfeq
    rw [← this]; exact hu.map (imSEquiv φ.toRingEquiv O₀).toMonoidHom
  have h1 := hdom hnu₀ hV₀
  rw [mem_maximalIdeal_comap_iff] at h1
  have : comapEquiv φ.toRingEquiv V ⟨_, hV₀⟩ = ⟨f, hfV⟩ := Subtype.ext hfeq
  rw [this] at h1; exact h1

theorem sep_transport (φ : E₀ ≃ₐ[k] E₁) (O₀ O₀' : Subring E₀)
    (h : O₀ ≠ O₀' → ∃ (f : E₀) (hf : f ∈ O₀) (hf' : f ∈ O₀'), ¬ IsUnit (⟨f, hf⟩ : O₀) ∧ IsUnit (⟨f, hf'⟩ : O₀'))
    (hne : imS φ.toRingEquiv O₀ ≠ imS φ.toRingEquiv O₀') :
    ∃ (f : E₁) (hf : f ∈ imS φ.toRingEquiv O₀) (hf' : f ∈ imS φ.toRingEquiv O₀'),
      ¬ IsUnit (⟨f, hf⟩ : imS φ.toRingEquiv O₀) ∧ IsUnit (⟨f, hf'⟩ : imS φ.toRingEquiv O₀') := by
  obtain ⟨f, hf, hf', hnu, hu⟩ := h (fun heq => hne (by rw [heq]))
  refine ⟨φ.toRingEquiv f, apply_mem_imS_iff.mpr hf, apply_mem_imS_iff.mpr hf', ?_, ?_⟩
  · rw [isUnit_imS_iff]; exact hnu
  · rw [isUnit_imS_iff]; exact hu

theorem exists_iota_transport (φ : E₀ ≃ₐ[k] E₁) (O₀ : Subring E₀) [IsLocalRing O₀]
    (X : Type*) [CommRing X] (ι₀ : AdicCompletion (maximalIdeal O₀) O₀ ≃+* X) :
    letI := isLocalRing_imS φ.toRingEquiv O₀
    ∃ ι : AdicCompletion (maximalIdeal (imS φ.toRingEquiv O₀)) (imS φ.toRingEquiv O₀) ≃+* X,
      ∀ x : O₀, ι (algebraMap _ _ (imSEquiv φ.toRingEquiv O₀ x)) = ι₀ (algebraMap _ _ x) := by
  letI := isLocalRing_imS φ.toRingEquiv O₀
  obtain ⟨Ψ, hΨ⟩ := exists_completion_transport (imSEquiv φ.toRingEquiv O₀)
  exact ⟨Ψ.trans ι₀, fun x => by rw [RingEquiv.trans_apply, hΨ]⟩

theorem prod_transport (φ : E₀ ≃ₐ[k] E₁) (O₀ : Subring E₀) (π : k) (hπ : algebraMap k E₀ π ∈ O₀)
    (hπ' : algebraMap k E₁ π ∈ imS φ.toRingEquiv O₀) (E : ℕ) (cx cy : O₀) (u : O₀ˣ)
    (h : cx * cy = (⟨_, hπ⟩ : O₀) ^ E * (u : O₀)) :
    imSEquiv φ.toRingEquiv O₀ cx * imSEquiv φ.toRingEquiv O₀ cy =
      (⟨_, hπ'⟩ : imS φ.toRingEquiv O₀) ^ E * ((Units.map (imSEquiv φ.toRingEquiv O₀ : O₀ →* imS φ.toRingEquiv O₀) u : (imS φ.toRingEquiv O₀)ˣ) : imS φ.toRingEquiv O₀) := by
  rw [← map_mul, h, map_mul, map_pow, imSEquiv_algebraMap φ O₀ π hπ hπ']; rfl

theorem coe_imSEquiv_mem_comap_iff (φ : E₀ ≃ₐ[k] E₁) (O₀ : Subring E₀) (W' : ValuationSubring E₀) (c : O₀) :
    ((imSEquiv φ.toRingEquiv O₀ c : imS φ.toRingEquiv O₀) : E₁) ∈ W'.comap (φ.symm.toRingEquiv : E₁ →+* E₀) ↔ (c : E₀) ∈ W' := by
  rw [coe_imSEquiv, toRingEquiv_apply', apply_mem_comap_symm_iff]

end coverRight
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_moduliHasse_commonChart_nodes_igusaSep_levelField_of_nodes_fixedField_of_algEquiv_of_eq_two_of_dvd.S3GlueKit"

section chart
variable {k E F : Type*} [Field k] [Field E] [Field F] [Algebra k E] [Algebra k F]

theorem chartB_transport
    (O : Type*) [CommRing O] [Algebra O E]
    (K₀ : IntermediateField k E) (F₀ : IntermediateField k F) (φ : K₀ ≃ₐ[k] F₀) (B₀ : Subalgebra O E)
    (B : Subring F)
    (hB : ∀ y : F, y ∈ B ↔ ∃ x : K₀, x ∈ B₀.toSubring.comap (algebraMap K₀ E) ∧
      y = ((algebraMap F₀ F).comp φ.toAlgHom.toRingHom) x)
    (Bx₀ O₀ : Subring K₀)
    (h : ∀ f : K₀, f ∈ Bx₀ → (f : E) ∈ B₀ ∧ f ∈ O₀)
    (f : F₀) (hf : f ∈ imS φ.toRingEquiv Bx₀) : (f : F) ∈ B ∧ f ∈ imS φ.toRingEquiv O₀ := by
  have hf₀ : φ.toRingEquiv.symm f ∈ Bx₀ := mem_imS_iff.mp hf
  obtain ⟨hB₀, hO₀⟩ := h _ hf₀
  refine ⟨(hB _).mpr ⟨φ.toRingEquiv.symm f, Subring.mem_comap.mpr hB₀, ?_⟩, mem_imS_iff.mpr hO₀⟩
  show (f : F) = ((φ (φ.symm f) : F₀) : F)
  rw [AlgEquiv.apply_symm_apply]

end chart
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_moduliHasse_commonChart_nodes_igusaSep_levelField_of_nodes_fixedField_of_algEquiv_of_eq_two_of_dvd.S3GlueKit"

section chart2
variable {k E₀ E₁ : Type*} [Field k] [Field E₀] [Field E₁] [Algebra k E₀] [Algebra k E₁]

theorem chartLoc_transport (φ : E₀ ≃ₐ[k] E₁) (Bx₀ O₀ : Subring E₀)
    (h : ∀ f : E₀, f ∈ O₀ ↔ ∃ g h : E₀, g ∈ Bx₀ ∧ h ∈ Bx₀ ∧ (∀ hh : h ∈ O₀, IsUnit (⟨h, hh⟩ : O₀)) ∧ f * h = g)
    (f : E₁) :
    f ∈ imS φ.toRingEquiv O₀ ↔ ∃ g h : E₁, g ∈ imS φ.toRingEquiv Bx₀ ∧ h ∈ imS φ.toRingEquiv Bx₀ ∧
      (∀ hh : h ∈ imS φ.toRingEquiv O₀, IsUnit (⟨h, hh⟩ : imS φ.toRingEquiv O₀)) ∧ f * h = g := by
  set e := φ.toRingEquiv with he
  rw [mem_imS_iff, h]
  constructor
  · rintro ⟨g, h', hg, hh', hu, hfh⟩
    refine ⟨e g, e h', apply_mem_imS_iff.mpr hg, apply_mem_imS_iff.mpr hh', fun hh => ?_, ?_⟩
    · rw [isUnit_imS_iff e O₀ h' (apply_mem_imS_iff.mp hh) hh]; exact hu _
    · have := congrArg e hfh; rw [map_mul, e.apply_symm_apply] at this; exact this
  · rintro ⟨g, h', hg, hh', hu, hfh⟩
    refine ⟨e.symm g, e.symm h', mem_imS_iff.mp hg, mem_imS_iff.mp hh', fun hh => ?_, ?_⟩
    · have hh1 : e (e.symm h') ∈ imS e O₀ := by rw [e.apply_symm_apply]; exact mem_imS_iff.mpr hh
      have := (isUnit_imS_iff e O₀ (e.symm h') hh hh1).mp
      have heq : (⟨e (e.symm h'), hh1⟩ : imS e O₀) = ⟨h', mem_imS_iff.mpr hh⟩ := Subtype.ext (e.apply_symm_apply h')
      rw [heq] at this
      exact this (hu _)
    · have := congrArg e.symm hfh; rw [map_mul] at this; exact this

theorem chartFrac_transport (φ : E₀ ≃ₐ[k] E₁) (Bx₀ : Subring E₀)
    (h : ∀ f : E₀, ∃ g h : E₀, g ∈ Bx₀ ∧ h ∈ Bx₀ ∧ h ≠ 0 ∧ f * h = g) (f : E₁) :
    ∃ g h : E₁, g ∈ imS φ.toRingEquiv Bx₀ ∧ h ∈ imS φ.toRingEquiv Bx₀ ∧ h ≠ 0 ∧ f * h = g := by
  set e := φ.toRingEquiv with he
  obtain ⟨g, h', hg, hh', h0, hfh⟩ := h (e.symm f)
  refine ⟨e g, e h', apply_mem_imS_iff.mpr hg, apply_mem_imS_iff.mpr hh', ?_, ?_⟩
  · intro h1; exact h0 (by simpa using congrArg e.symm h1)
  · have := congrArg e hfh; rw [map_mul, e.apply_symm_apply] at this; exact this

theorem chartFG_transport [DecidableEq E₁] (φ : E₀ ≃ₐ[k] E₁) (Bx₀ : Subring E₀) (PA : k → Prop)
    (h : ∃ T : Finset E₀, Bx₀ = Subring.closure ({f : E₀ | ∃ x : k, PA x ∧ f = algebraMap k E₀ x} ∪ (↑T : Set E₀))) :
    ∃ T : Finset E₁, imS φ.toRingEquiv Bx₀ =
      Subring.closure ({f : E₁ | ∃ x : k, PA x ∧ f = algebraMap k E₁ x} ∪ (↑T : Set E₁)) := by
  obtain ⟨T, hT⟩ := h
  refine ⟨T.image φ.toRingEquiv, ?_⟩
  rw [hT]
  unfold imS
  rw [RingHom.map_closure, Set.image_union, Finset.coe_image]
  congr 2
  ext f
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨g, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨x, hx, φ.commutes x⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨algebraMap k E₀ x, ⟨x, hx, rfl⟩, φ.commutes x⟩

end chart2
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_moduliHasse_commonChart_nodes_igusaSep_levelField_of_nodes_fixedField_of_algEquiv_of_eq_two_of_dvd.S3GlueKit"

end S3GlueKit
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_moduliHasse_commonChart_nodes_igusaSep_levelField_of_nodes_fixedField_of_algEquiv_of_eq_two_of_dvd.S3GlueKit"

namespace S3GlueKit
open ModularCurve ModularCurve.FullLevel
open scoped MatrixGroups

section dict
variable (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
  (ℓg : ℕ) (hℓgM' : ℓg ∣ M')
  (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (ξ : ↥k₀) (hξ : IsPrimitiveRoot ξ q)
  (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
  (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)
  (Kℓ : IntermediateField ↥k₀ (LaurentSeries ↥k₀))
  (hKℓ : Kℓ = ModularCurve.laurentBaseChange ↥k₀
      (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
  (K₀ : IntermediateField ↥k₀ ↥Kℓ)
  [Algebra ↥k₀ ↥(fieldBar q M')] (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M')) (φ : ↥K₀ ≃ₐ[↥k₀] ↥F₀)
  (hφ4 :       (∀ (ζ : Idx q) (ξ' : ↥k₀), IsPrimitiveRoot ξ' q → ζ.val = (((ξ' : ↥k₀)) : AlgebraicClosure ℚ) →
        ∀ (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 M' →
        ∀ (τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ),
          ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ' q (q ^ 2 * M') H₁ γ Kℓ τ →
          ∃ hτ : ∀ f : ↥Kℓ, f ∈ K₀ → τ f ∈ K₀,
            ∀ f : ↥K₀, ((φ ⟨τ (f : ↥Kℓ), hτ (f : ↥Kℓ) f.2⟩ : ↥F₀) : ↥(fieldBar q M')) =
              levelAutBar q M' ζ γ ((φ f : ↥F₀) : ↥(fieldBar q M'))))

include hqM' hℓgM' hξ hH₁ hKℓ hφ4

theorem dict_fwd (ζ : Idx q) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M') :
    ∃ (τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ) (γ' : SL(2, ℤ)), γ' ∈ CongruenceSubgroup.Gamma0 M' ∧
      ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ'⁻¹ Kℓ τ ∧
      ∃ hτ : (∀ f : ↥Kℓ, f ∈ K₀ → τ f ∈ K₀), ∀ x : ↥K₀,
        ((φ ⟨τ (x : ↥Kℓ), hτ (x : ↥Kℓ) x.2⟩ : ↥F₀) : ↥(fieldBar q M')) = levelAutBar q M' ζ γ ((φ x : ↥F₀) : ↥(fieldBar q M')) := by
  have hq0 : 0 < q := (Fact.out : q.Prime).pos
  have hξbar : IsPrimitiveRoot ((ξ : ↥k₀) : AlgebraicClosure ℚ) q :=
    hξ.map_of_injective (algebraMap ↥k₀ (AlgebraicClosure ℚ)).injective
  have hζ : IsPrimitiveRoot ζ.val q := (mem_primitiveRoots hq0).mp (ζ : ↥(primitiveRoots q (AlgebraicClosure ℚ))).2
  obtain ⟨b, -, hb⟩ := hξbar.eq_pow_of_pow_eq_one hζ.pow_eq_one
  have hbcop : b.Coprime q := (hξbar.pow_iff_coprime hq0 b).mp (hb ▸ hζ)
  have hξ'prim : IsPrimitiveRoot (ξ ^ b) q := hξ.pow_of_coprime b hbcop
  have hζeq : ζ.val = (((ξ ^ b) : ↥k₀) : AlgebraicClosure ℚ) := by rw [← hb]; push_cast; rfl
  obtain ⟨τ, hτ⟩ := ModularCurve.FullLevel.exists_isLevelAutAt_of_mem_gamma0_of_eq_levelH_inf_ker q M' hqM' ℓg hℓgM'
      ↥k₀ (ξ ^ b) hξ'prim H₁ hH₁ Kℓ hKℓ γ⁻¹ (inv_mem hγ)
  rw [inv_inv] at hτ
  obtain ⟨hτK₀, hστ⟩ := hφ4 ζ (ξ ^ b) hξ'prim hζeq γ hγ τ hτ
  obtain ⟨d, hd⟩ := ModularCurve.FullLevel.exists_isLevelAutAt_conj_of_isLevelAutAt_of_isPrimitiveRoot_of_eq_levelH_inf_ker ↥k₀ q M' hqM'
    ℓg hℓgM' ξ (ξ ^ b) hξ hξ'prim H₁ hH₁ Kℓ
  obtain ⟨γ', hγ'0, -, -, hτ'⟩ := hd γ hγ τ hτ
  exact ⟨τ, γ'⁻¹, inv_mem hγ'0, by rw [inv_inv]; exact hτ', hτK₀, hστ⟩

theorem dict_bwd (ζ : Idx q) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M') (τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ)
    (hτ : ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ) :
    ∃ γ₂ : SL(2, ℤ), γ₂ ∈ CongruenceSubgroup.Gamma0 M' ∧
      ∃ hτ : (∀ f : ↥Kℓ, f ∈ K₀ → τ f ∈ K₀), ∀ x : ↥K₀,
        ((φ ⟨τ (x : ↥Kℓ), hτ (x : ↥Kℓ) x.2⟩ : ↥F₀) : ↥(fieldBar q M')) = levelAutBar q M' ζ γ₂ ((φ x : ↥F₀) : ↥(fieldBar q M')) := by
  have hq0 : 0 < q := (Fact.out : q.Prime).pos
  have hξbar : IsPrimitiveRoot ((ξ : ↥k₀) : AlgebraicClosure ℚ) q :=
    hξ.map_of_injective (algebraMap ↥k₀ (AlgebraicClosure ℚ)).injective
  have hζ : IsPrimitiveRoot ζ.val q := (mem_primitiveRoots hq0).mp (ζ : ↥(primitiveRoots q (AlgebraicClosure ℚ))).2
  obtain ⟨b, -, hb⟩ := hξbar.eq_pow_of_pow_eq_one hζ.pow_eq_one
  have hbcop : b.Coprime q := (hξbar.pow_iff_coprime hq0 b).mp (hb ▸ hζ)
  have hξ'prim : IsPrimitiveRoot (ξ ^ b) q := hξ.pow_of_coprime b hbcop
  have hζeq : ζ.val = (((ξ ^ b) : ↥k₀) : AlgebraicClosure ℚ) := by rw [← hb]; push_cast; rfl
  obtain ⟨d, hd⟩ := ModularCurve.FullLevel.exists_isLevelAutAt_conj_of_isLevelAutAt_of_isPrimitiveRoot_of_eq_levelH_inf_ker ↥k₀ q M' hqM'
    ℓg hℓgM' (ξ ^ b) ξ hξ'prim hξ H₁ hH₁ Kℓ
  obtain ⟨γ', hγ'0, -, -, hτ'⟩ := hd γ⁻¹ (inv_mem hγ) τ hτ
  obtain ⟨hτK₀, hστ⟩ := hφ4 ζ (ξ ^ b) hξ'prim hζeq γ' hγ'0 τ hτ'
  exact ⟨γ', hγ'0, hτK₀, hστ⟩

end dict
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_moduliHasse_commonChart_nodes_igusaSep_levelField_of_nodes_fixedField_of_algEquiv_of_eq_two_of_dvd.S3GlueKit"

section nodesLevel
variable {k E F : Type*} [Field k] [Field E] [Field F] [Algebra k E] [Algebra k F]

theorem nodes_eqv_transport (K₀ : IntermediateField k E) (F₀ : IntermediateField k F) (φ : K₀ ≃ₐ[k] F₀)
    {ι S ΓT : Type*} [SetLike ΓT S] (Γ : ΓT) (Att : S → (E ≃ₐ[k] E) → Prop) (σ : ι → S → F → F)
    (hfwd : ∀ (i : ι) (γ : S), γ ∈ Γ → ∃ (τ : E ≃ₐ[k] E) (γ' : S), γ' ∈ Γ ∧ Att γ' τ ∧
      ∃ hτ : (∀ f : E, f ∈ K₀ → τ f ∈ K₀), ∀ x : K₀, ((φ ⟨τ (x : E), hτ (x : E) x.2⟩ : F₀) : F) = σ i γ ((φ x : F₀) : F))
    (nodes₀ : Finset (Subring K₀)) (nodes : Finset (Subring F₀))
    (hnodes : ∀ O : Subring F₀, O ∈ nodes ↔ ∃ O₀ ∈ nodes₀, ∀ y : F₀, y ∈ O ↔ φ.symm y ∈ O₀)
    (heqv₀ : ∀ γ : S, γ ∈ Γ → ∀ τ : E ≃ₐ[k] E, Att γ τ → ∀ O ∈ nodes₀, ∃ O' ∈ nodes₀,
      ∀ (f : E) (hf : f ∈ K₀) (hf' : τ f ∈ K₀), (⟨f, hf⟩ : K₀) ∈ O ↔ (⟨τ f, hf'⟩ : K₀) ∈ O') :
    ∀ (i : ι) (γ : S), γ ∈ Γ → ∀ O ∈ nodes, ∃ O' ∈ nodes,
      ∀ (f : F) (hf : f ∈ F₀) (hf' : σ i γ f ∈ F₀), (⟨f, hf⟩ : F₀) ∈ O ↔ (⟨σ i γ f, hf'⟩ : F₀) ∈ O' := by
  intro i γ hγ O hO
  obtain ⟨τ, γ', hγ', hatt, hτ, hστ⟩ := hfwd i γ hγ
  obtain ⟨O₀, hO₀, hOO₀⟩ := (hnodes O).mp hO
  obtain ⟨O₀', hO₀', hmove⟩ := heqv₀ γ' hγ' τ hatt O₀ hO₀

  classical

  have hex : ∃ O' ∈ nodes, ∀ y : F₀, y ∈ O' ↔ φ.symm y ∈ O₀' :=
    ⟨O₀'.comap (φ.symm.toRingEquiv : F₀ →+* K₀), (hnodes _).mpr ⟨O₀', hO₀', fun y => Iff.rfl⟩, fun y => Iff.rfl⟩
  obtain ⟨O', hO', hOO'⟩ := hex
  refine ⟨O', hO', fun f hf hf' => ?_⟩
  rw [hOO₀, hOO']
  have h1 : (⟨σ i γ f, hf'⟩ : F₀) = φ ⟨τ ((φ.symm ⟨f, hf⟩ : K₀) : E), hτ _ (φ.symm ⟨f, hf⟩).2⟩ := by
    apply Subtype.ext
    show σ i γ f = ((φ ⟨τ ((φ.symm ⟨f, hf⟩ : K₀) : E), hτ _ (φ.symm ⟨f, hf⟩).2⟩ : F₀) : F)
    rw [hστ, AlgEquiv.apply_symm_apply]
  rw [h1, AlgEquiv.symm_apply_apply]
  have h2 : φ.symm ⟨f, hf⟩ = ⟨((φ.symm ⟨f, hf⟩ : K₀) : E), (φ.symm ⟨f, hf⟩).2⟩ := rfl
  conv_lhs => rw [h2]
  exact hmove _ _ _

theorem nodes_trans_transport (K₀ : IntermediateField k E) (F₀ : IntermediateField k F) (φ : K₀ ≃ₐ[k] F₀)
    {ι S ΓT : Type*} [SetLike ΓT S] (Γ : ΓT) (Att : S → (E ≃ₐ[k] E) → Prop) (σ : ι → S → F → F)
    (hbwd : ∀ (i : ι) (γ : S), γ ∈ Γ → ∀ τ : E ≃ₐ[k] E, Att γ τ → ∃ γ₂ : S, γ₂ ∈ Γ ∧
      ∃ hτ : (∀ f : E, f ∈ K₀ → τ f ∈ K₀), ∀ x : K₀, ((φ ⟨τ (x : E), hτ (x : E) x.2⟩ : F₀) : F) = σ i γ₂ ((φ x : F₀) : F))
    (nodes₀ : Finset (Subring K₀)) (nodes : Finset (Subring F₀))
    (hnodes : ∀ O : Subring F₀, O ∈ nodes ↔ ∃ O₀ ∈ nodes₀, ∀ y : F₀, y ∈ O ↔ φ.symm y ∈ O₀)
    (htrans₀ : ∀ O ∈ nodes₀, ∀ O' ∈ nodes₀, ∃ (γ : S) (_ : γ ∈ Γ) (τ : E ≃ₐ[k] E) (_ : Att γ τ),
      ∀ (f : E) (hf : f ∈ K₀) (hf' : τ f ∈ K₀), (⟨f, hf⟩ : K₀) ∈ O ↔ (⟨τ f, hf'⟩ : K₀) ∈ O') :
    ∀ (i : ι), ∀ O ∈ nodes, ∀ O' ∈ nodes, ∃ γ : S, γ ∈ Γ ∧
      ∀ (f : F) (hf : f ∈ F₀) (hf' : σ i γ f ∈ F₀), (⟨f, hf⟩ : F₀) ∈ O ↔ (⟨σ i γ f, hf'⟩ : F₀) ∈ O' := by
  intro i O hO O' hO'
  obtain ⟨O₀, hO₀, hOO₀⟩ := (hnodes O).mp hO
  obtain ⟨O₀', hO₀', hOO₀'⟩ := (hnodes O').mp hO'
  obtain ⟨γ, hγ, τ, hatt, hmove⟩ := htrans₀ O₀ hO₀ O₀' hO₀'
  obtain ⟨γ₂, hγ₂, hτ, hστ⟩ := hbwd i γ hγ τ hatt
  refine ⟨γ₂, hγ₂, fun f hf hf' => ?_⟩
  rw [hOO₀, hOO₀']
  have h1 : (⟨σ i γ₂ f, hf'⟩ : F₀) = φ ⟨τ ((φ.symm ⟨f, hf⟩ : K₀) : E), hτ _ (φ.symm ⟨f, hf⟩).2⟩ := by
    apply Subtype.ext
    show σ i γ₂ f = ((φ ⟨τ ((φ.symm ⟨f, hf⟩ : K₀) : E), hτ _ (φ.symm ⟨f, hf⟩).2⟩ : F₀) : F)
    rw [hστ, AlgEquiv.apply_symm_apply]
  rw [h1, AlgEquiv.symm_apply_apply]
  have h2 : φ.symm ⟨f, hf⟩ = ⟨((φ.symm ⟨f, hf⟩ : K₀) : E), (φ.symm ⟨f, hf⟩).2⟩ := rfl
  conv_lhs => rw [h2]
  exact hmove _ _ _

end nodesLevel
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_moduliHasse_commonChart_nodes_igusaSep_levelField_of_nodes_fixedField_of_algEquiv_of_eq_two_of_dvd.S3GlueKit"

end S3GlueKit
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_moduliHasse_commonChart_nodes_igusaSep_levelField_of_nodes_fixedField_of_algEquiv_of_eq_two_of_dvd.S3GlueKit"

namespace S3GlueKit
open ModularCurve AlgebraicCurve

theorem isIntegral_laurentBaseChange_of_coeffEmb_mem (X : IntermediateField ℚ (LaurentSeries ℚ))
    (K : Type*) [Field K] [Algebra K ↥(laurentBaseChange (AlgebraicClosure ℚ) X)]
    (F₀ : IntermediateField K ↥(laurentBaseChange (AlgebraicClosure ℚ) X))
    (hF₀ : ∀ (x : LaurentSeries ℚ) (hx : x ∈ X),
      (⟨coeffEmb (AlgebraicClosure ℚ) x, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hx⟩ :
        ↥(laurentBaseChange (AlgebraicClosure ℚ) X)) ∈ F₀) :
    Algebra.IsIntegral ↥F₀ ↥(laurentBaseChange (AlgebraicClosure ℚ) X) := by
  haveI hQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    have h := AlgebraicClosure.isAlgebraic ℚ
    convert h <;> first | rfl | exact Subsingleton.elim _ _
  let S' : Subfield (LaurentSeries (AlgebraicClosure ℚ)) :=
    (algebraicClosure ↥F₀ ↥(laurentBaseChange (AlgebraicClosure ℚ) X)).toSubfield.map (algebraMap ↥(laurentBaseChange (AlgebraicClosure ℚ) X) (LaurentSeries (AlgebraicClosure ℚ)))
  have hle : Subfield.closure (Set.range (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))) ∪
      (⇑(coeffEmb (AlgebraicClosure ℚ)) '' (X : Set (LaurentSeries ℚ)))) ≤ S' := by
    rw [Subfield.closure_le]
    rintro z (⟨c, rfl⟩ | ⟨x, hx, rfl⟩)
    · refine Subfield.mem_map.mpr ⟨algebraMap (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) X) c, ?_, rfl⟩
      rw [IntermediateField.mem_toSubfield, mem_algebraicClosure_iff']
      have hc : IsIntegral ℚ c := (Algebra.IsAlgebraic.isAlgebraic c).isIntegral
      have hc' : IsIntegral ℚ (algebraMap (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) X) c) :=
        hc.map (IsScalarTower.toAlgHom ℚ (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) X))
      exact hc'.tower_top
    · refine Subfield.mem_map.mpr ⟨⟨coeffEmb _ x, coeffEmb_mem_laurentBaseChange _ hx⟩, ?_, rfl⟩
      rw [IntermediateField.mem_toSubfield, mem_algebraicClosure_iff']
      exact isIntegral_algebraMap (A := ↥(laurentBaseChange (AlgebraicClosure ℚ) X)) (x := (⟨_, hF₀ x hx⟩ : ↥F₀))
  refine ⟨fun f => ?_⟩
  have hf : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ S' := hle (mem_laurentBaseChange_iff.mp f.2)
  obtain ⟨g, hg, hgf⟩ := Subfield.mem_map.mp hf
  have : g = f := Subtype.ext hgf
  rw [← this]
  exact mem_algebraicClosure_iff'.mp hg

def placeRestrictScalars {K K' F : Type*} [Field K] [Field K'] [Field F] [Algebra K F] [Algebra K' F]
    (P : Place K' F) (h : ∀ c : K, algebraMap K F c ∈ P.toValuationSubring) : Place K F :=
  ⟨P.toValuationSubring, h, P.ne_top', P.isPrincipalIdealRing'⟩

theorem reg_transport
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    (Kℓ : IntermediateField ↥k₀ (LaurentSeries ↥k₀))
    (Acst : Type) [CommRing Acst] [IsDomain Acst] [Algebra Acst ↥k₀] [IsFractionRing Acst ↥k₀]
    [Algebra Acst ↥Kℓ] [IsScalarTower Acst ↥k₀ ↥Kℓ]
    (jℓ : ↥Kℓ) (hjℓ : ((jℓ : LaurentSeries ↥k₀)) = ModularCurve.coeffEmb ↥k₀ ModularCurve.jq) [Fact (jℓ ≠ 0)]
    (G : Subgroup (↥Kℓ ≃ₐ[↥k₀] ↥Kℓ)) [Finite ↥G]
    (K₀ : IntermediateField ↥k₀ ↥Kℓ) (hK₀ : K₀ = IntermediateField.fixedField G)
    (X : IntermediateField ℚ (LaurentSeries ℚ))
    [Algebra ↥k₀ ↥(laurentBaseChange (AlgebraicClosure ℚ) X)]
    (halg : ∀ c : ↥k₀, algebraMap ↥k₀ ↥(laurentBaseChange (AlgebraicClosure ℚ) X) c =
      algebraMap (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) X) (c : AlgebraicClosure ℚ))
    (F₀ : IntermediateField ↥k₀ ↥(laurentBaseChange (AlgebraicClosure ℚ) X))
    (hint : Algebra.IsIntegral ↥F₀ ↥(laurentBaseChange (AlgebraicClosure ℚ) X))
    (φ : ↥K₀ ≃ₐ[↥k₀] ↥F₀)
    (hφ1 : ∀ f : ↥K₀, coeffMap (algebraMap ↥k₀ (AlgebraicClosure ℚ)) (((f : ↥Kℓ)) : LaurentSeries ↥k₀) =
        ( ((φ f : ↥F₀) : ↥(laurentBaseChange (AlgebraicClosure ℚ) X)) : LaurentSeries (AlgebraicClosure ℚ)))
    (jF : ↥(laurentBaseChange (AlgebraicClosure ℚ) X))
    (hjF : (jF : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) jq) (hjF₀ : jF ∈ F₀)
    (Bx : Subring ↥K₀)
    (hreg : ∀ f : ↥K₀, f ∈ Bx → ∀ P : Place ↥k₀ ↥Kℓ, 0 ≤ P.ord (jℓ : ↥Kℓ) → 0 ≤ P.ord (f : ↥Kℓ)) :
    ∀ f : ↥F₀, f ∈ imS φ.toRingEquiv Bx → ∀ P : Place (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) X),
      0 ≤ P.ord jF → 0 ≤ P.ord (f : ↥(laurentBaseChange (AlgebraicClosure ℚ) X)) := by
  intro f hf P hPj
  by_cases hf0 : f = 0
  · subst hf0; simp
  have hx : φ.symm f ∈ Bx := mem_imS_iff.mp hf

  have hjF0 : jF ≠ 0 := by
    intro h; apply ModularCurve.coeffEmb_jq_ne_zero (AlgebraicClosure ℚ); rw [← hjF, h]; rfl
  have hjP : jF ∈ P.toValuationSubring := (P.mem_iff_ord_nonneg hjF0).mpr hPj

  let Pk : Place ↥k₀ ↥(laurentBaseChange (AlgebraicClosure ℚ) X) := placeRestrictScalars P (fun c => by rw [halg]; exact P.algebraMap_mem' _)
  let ψ : ↥K₀ →ₐ[↥k₀] ↥(laurentBaseChange (AlgebraicClosure ℚ) X) :=
    (IsScalarTower.toAlgHom ↥k₀ ↥F₀ ↥(laurentBaseChange (AlgebraicClosure ℚ) X)).comp (φ : ↥K₀ →ₐ[↥k₀] ↥F₀)
  have hψeq : ψ.toRingHom = (algebraMap ↥F₀ ↥(laurentBaseChange (AlgebraicClosure ℚ) X)).comp φ.toRingEquiv.toRingHom := RingHom.ext fun _ => rfl
  have hψ : ψ.toRingHom.IsIntegral := by
    rw [hψeq]
    exact RingHom.IsIntegral.trans _ _ (RingHom.isIntegral_of_surjective _ φ.toRingEquiv.surjective)
      (fun z => hint.isIntegral z)
  let v : Place ↥k₀ ↥K₀ := Pk.restrictAlong ψ hψ
  have hv : ∀ y : ↥K₀, y ∈ v.toValuationSubring ↔ ((φ y : ↥F₀) : ↥(laurentBaseChange (AlgebraicClosure ℚ) X)) ∈ P.toValuationSubring :=
    fun y => Iff.rfl

  haveI hfd : FiniteDimensional ↥K₀ ↥Kℓ := by
    subst hK₀
    have h : FiniteDimensional (FixedPoints.subfield ↥G ↥Kℓ) ↥Kℓ := inferInstance
    exact h
  haveI hsep : Algebra.IsSeparable ↥K₀ ↥Kℓ := by
    subst hK₀
    have h : Algebra.IsSeparable (FixedPoints.subfield ↥G ↥Kℓ) ↥Kℓ := inferInstance
    exact h
  haveI : FiniteDimensional ↥(K₀.val.fieldRange) ↥Kℓ := by
    rw [IntermediateField.fieldRange_val]; exact hfd
  haveI : Algebra.IsSeparable ↥(K₀.val.fieldRange) ↥Kℓ := by
    rw [IntermediateField.fieldRange_val]; exact hsep
  have hval : K₀.val.toRingHom.IsIntegral :=
    fun z => Algebra.IsIntegral.isIntegral (R := ↥K₀) z
  obtain ⟨w, hw⟩ := AlgebraicCurve.Place.exists_restrictAlong_eq_of_finiteDimensional_fieldRange
    K₀.val hval v
  have hwv : ∀ y : ↥K₀, (y : ↥Kℓ) ∈ w.toValuationSubring ↔ y ∈ v.toValuationSubring := by
    intro y; rw [← hw]; exact Iff.rfl

  set j' : ↥K₀ := φ.symm ⟨jF, hjF₀⟩ with hj'def
  have hφj' : φ j' = ⟨jF, hjF₀⟩ := φ.apply_symm_apply _
  have hj'w : ((j' : ↥K₀) : ↥Kℓ) ∈ w.toValuationSubring := by
    rw [hwv, hv, hφj']; exact hjP
  have hLS : (((j' : ↥K₀) : ↥Kℓ) : LaurentSeries ↥k₀) = coeffEmb ↥k₀ jq := by
    apply ModularCurve.coeffMap_injective (f := algebraMap ↥k₀ (AlgebraicClosure ℚ)) (algebraMap ↥k₀ _).injective
    rw [hφ1 j', hφj', coeffEmb, coeffMap_coeffMap]
    have hrat : (algebraMap ↥k₀ (AlgebraicClosure ℚ)).comp (algebraMap ℚ ↥k₀) = algebraMap ℚ (AlgebraicClosure ℚ) :=
      RingHom.ext_rat _ _
    rw [hrat]
    show (jF : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) jq
    rw [hjF]
  have hjeq : ((j' : ↥K₀) : ↥Kℓ) = jℓ := Subtype.ext (hLS.trans hjℓ.symm)
  have hjw : (jℓ : ↥Kℓ) ∈ w.toValuationSubring := hjeq ▸ hj'w
  have hjord : 0 ≤ w.ord (jℓ : ↥Kℓ) := (w.mem_iff_ord_nonneg Fact.out).mp hjw

  have hxord := hreg _ hx w hjord
  have hx0 : ((φ.symm f : ↥K₀) : ↥Kℓ) ≠ 0 := by
    intro h
    apply hf0
    have : φ.symm f = 0 := Subtype.ext h
    simpa using congrArg φ this
  have hxw := (w.mem_iff_ord_nonneg hx0).mpr hxord
  rw [hwv, hv, AlgEquiv.apply_symm_apply] at hxw
  exact (P.mem_iff_ord_nonneg (by intro h; exact hf0 (Subtype.ext h))).mp hxw

end S3GlueKit
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_moduliHasse_commonChart_nodes_igusaSep_levelField_of_nodes_fixedField_of_algEquiv_of_eq_two_of_dvd.S3GlueKit"

namespace S3GlueKit
open ModularCurve

theorem coeffEmb_mem_of_coeffLaw (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    (Kℓ : IntermediateField ↥k₀ (LaurentSeries ↥k₀)) (K₀ : IntermediateField ↥k₀ ↥Kℓ)
    (X : IntermediateField ℚ (LaurentSeries ℚ)) [Algebra ↥k₀ ↥(laurentBaseChange (AlgebraicClosure ℚ) X)]
    (F₀ : IntermediateField ↥k₀ ↥(laurentBaseChange (AlgebraicClosure ℚ) X)) (φ : ↥K₀ ≃ₐ[↥k₀] ↥F₀)
    (hφ1 : ∀ f : ↥K₀, coeffMap (algebraMap ↥k₀ (AlgebraicClosure ℚ)) (((f : ↥Kℓ)) : LaurentSeries ↥k₀) =
        ( ((φ f : ↥F₀) : ↥(laurentBaseChange (AlgebraicClosure ℚ) X)) : LaurentSeries (AlgebraicClosure ℚ)))
    (g : LaurentSeries ℚ) (v : ↥(laurentBaseChange (AlgebraicClosure ℚ) X))
    (hv : (v : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) g) (hvF₀ : v ∈ F₀)
    (hgK : (coeffEmb ↥k₀ g) ∈ Kℓ) :
    (⟨(coeffEmb ↥k₀ g), hgK⟩ : ↥Kℓ) ∈ K₀ := by
  have hLS : (((φ.symm ⟨v, hvF₀⟩ : ↥K₀) : ↥Kℓ) : LaurentSeries ↥k₀) = coeffEmb ↥k₀ g := by
    apply ModularCurve.coeffMap_injective (f := algebraMap ↥k₀ (AlgebraicClosure ℚ)) (algebraMap ↥k₀ _).injective
    rw [hφ1, AlgEquiv.apply_symm_apply, coeffEmb, coeffMap_coeffMap,
      RingHom.ext_rat ((algebraMap ↥k₀ (AlgebraicClosure ℚ)).comp (algebraMap ℚ ↥k₀)) (algebraMap ℚ (AlgebraicClosure ℚ))]
    show (v : LaurentSeries (AlgebraicClosure ℚ)) = _
    rw [hv]; rfl
  have : (⟨(coeffEmb ↥k₀ g), hgK⟩ : ↥Kℓ) = ((φ.symm ⟨v, hvF₀⟩ : ↥K₀) : ↥Kℓ) :=
    Subtype.ext hLS.symm
  rw [this]; exact (φ.symm ⟨v, hvF₀⟩).2

end S3GlueKit
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_moduliHasse_commonChart_nodes_igusaSep_levelField_of_nodes_fixedField_of_algEquiv_of_eq_two_of_dvd.S3GlueKit"

namespace S3GlueKit
open IsLocalRing

theorem aeval_map_algebraMap_transport {k E₀ E₁ : Type*} [Field k] [Field E₀] [Field E₁] [Algebra k E₀] [Algebra k E₁]
    (φ : E₀ ≃ₐ[k] E₁) (x : E₀) (p : Polynomial k) :
    φ (Polynomial.aeval x (p.map (algebraMap k E₀))) = Polynomial.aeval (φ x) (p.map (algebraMap k E₁)) := by
  rw [Polynomial.coe_aeval_eq_eval, Polynomial.coe_aeval_eq_eval, Polynomial.eval_map, Polynomial.eval_map]
  rw [show (φ : E₀ → E₁) = ((φ : E₀ →ₐ[k] E₁) : E₀ →+* E₁) from rfl, Polynomial.hom_eval₂, AlgHom.comp_algebraMap]

section Ntransport
variable {k L F : Type*} [Field k] [Field L] [Field F] [Algebra k L] [Algebra k F]

theorem N_transport3
    (Kℓ : IntermediateField k L) (K₀ : IntermediateField k ↥Kℓ) (F₀ : IntermediateField k F) (φ : ↥K₀ ≃ₐ[k] ↥F₀)
    (W₀' : ValuationSubring ↥K₀)
    (PA : k → Prop) (π₀ : k) (ncard : ℕ) (Mod : ℕ → Prop)
    (TT : ℕ → Type*) [∀ n, CommRing (TT n)] (Rc : ∀ (n : ℕ) (x : k), PA x → TT n) (RU RV : ∀ n : ℕ, (TT n)ˣ → TT n)
    {ιT S ΓT : Type*} [SetLike ΓT S] (Γ : ΓT) (Att : S → (↥Kℓ ≃ₐ[k] ↥Kℓ) → Prop) (σ : ιT → S → F → F)
    (G₁ : Type*) (MF : G₁ → Prop) (Q : ∀ g : G₁, MF g → Prop) (C RS R0 : ∀ (g : G₁) (hg : MF g), Q g hg → Prop)
    (Pc : ∀ (g : G₁) (hg : MF g), Q g hg → ∀ c : k, PA c → Prop) (yK : G₁ → L) (vF : ∀ g : G₁, MF g → F)
    (Ob : Type*) [CommRing Ob] [Algebra Ob ↥Kℓ] (B₀ : Subalgebra Ob ↥Kℓ) (B : Subring F)
    (hB : ∀ y : F, y ∈ B ↔ ∃ x : ↥K₀, x ∈ B₀.toSubring.comap (algebraMap ↥K₀ ↥Kℓ) ∧
      y = ((algebraMap ↥F₀ F).comp φ.toAlgHom.toRingHom) x)
    (RegUp : ↥Kℓ → Prop) (RegDn : F → Prop)
    (hfwd : ∀ (i : ιT) (γ : S), γ ∈ Γ → ∃ (τ : ↥Kℓ ≃ₐ[k] ↥Kℓ) (γ' : S), γ' ∈ Γ ∧ Att γ' τ ∧
      ∃ hτ : (∀ f : ↥Kℓ, f ∈ K₀ → τ f ∈ K₀), ∀ x : ↥K₀, ((φ ⟨τ (x : ↥Kℓ), hτ (x : ↥Kℓ) x.2⟩ : ↥F₀) : F) = σ i γ ((φ x : ↥F₀) : F))
    (hbwd : ∀ (i : ιT) (γ : S), γ ∈ Γ → ∀ τ : ↥Kℓ ≃ₐ[k] ↥Kℓ, Att γ τ → ∃ γ₂ : S, γ₂ ∈ Γ ∧
      ∃ hτ : (∀ f : ↥Kℓ, f ∈ K₀ → τ f ∈ K₀), ∀ x : ↥K₀, ((φ ⟨τ (x : ↥Kℓ), hτ (x : ↥Kℓ) x.2⟩ : ↥F₀) : F) = σ i γ₂ ((φ x : ↥F₀) : F))
    (hyK : ∀ g : G₁, MF g → yK g ∈ Kℓ) (hyK₀ : ∀ (g : G₁) (hg : MF g), (⟨yK g, hyK g hg⟩ : ↥Kℓ) ∈ K₀)
    (hv : ∀ (g : G₁) (hg : MF g) (hgK : yK g ∈ Kℓ) (hF : (⟨yK g, hgK⟩ : ↥Kℓ) ∈ K₀), ((φ ⟨⟨yK g, hgK⟩, hF⟩ : ↥F₀) : F) = vF g hg)
    (hreg : ∀ Bx₀ : Subring ↥K₀, (∀ f : ↥K₀, f ∈ Bx₀ → RegUp (f : ↥Kℓ)) → ∀ f : ↥F₀, f ∈ imS φ.toRingEquiv Bx₀ → RegDn (f : F))

    (P1 : Prop) (P2 : P1 → Prop) (PJ : Prop) (hPJ : PJ) (a₀F : k) (ha₀F : PA a₀F) (Pin : P1 → ∀ c : k, PA c → Prop)
    (t₀ : ↥Kℓ) (t₁ : PJ → k → F) (ht : ∀ h₀ : t₀ ∈ K₀, ((φ ⟨t₀, h₀⟩ : ↥F₀) : F) = t₁ hPJ a₀F)
    (VV : ∀ n : ℕ, TT n)
    (JK : L) (JF : F) (hJKmem : JK ∈ Kℓ) (hJK₀ : (⟨JK, hJKmem⟩ : ↥Kℓ) ∈ K₀) (hJφ : ((φ ⟨⟨JK, hJKmem⟩, hJK₀⟩ : ↥F₀) : F) = JF)
    (W₀ : ValuationSubring ↥F₀) (hW₀ : W₀ = W₀'.comap (φ.symm.toRingEquiv : ↥F₀ →+* ↥K₀))
    (hN :
        (∃ (hjR : P1) (_ : P2 hjR) (_ : ∀ ha₀ : PA a₀F, Pin hjR a₀F ha₀)
           (nodes : Finset (Subring ↥K₀)),
          nodes.card = ncard ∧
          (∃ Bc : Subring ↥K₀,
            (∃ T : Finset ↥K₀, Bc = Subring.closure
              ({f : ↥K₀ | ∃ x : k, PA x ∧ f = algebraMap k ↥K₀ x} ∪ (↑T : Set ↥K₀))) ∧
            ∀ O ∈ nodes, (∀ f : ↥K₀, f ∈ Bc → f ∈ O) ∧
              (∀ f : ↥K₀, f ∈ O ↔ ∃ g h : ↥K₀, g ∈ Bc ∧ h ∈ Bc ∧ (∀ hh : h ∈ O, IsUnit (⟨h, hh⟩ : ↥O)) ∧ f * h = g)) ∧

          (∀ (γ : S), γ ∈ Γ → ∀ (τ : ↥Kℓ ≃ₐ[k] ↥Kℓ), Att γ τ → ∀ O ∈ nodes, ∃ O' ∈ nodes,
            ∀ (f : ↥Kℓ) (hf : f ∈ K₀) (hf' : τ f ∈ K₀), (⟨f, hf⟩ : ↥K₀) ∈ O ↔ (⟨_, hf'⟩ : ↥K₀) ∈ O') ∧
          (∀ O ∈ nodes, ∀ O' ∈ nodes, ∃ (γ : S) (_ : γ ∈ Γ) (τ : ↥Kℓ ≃ₐ[k] ↥Kℓ) (_ : Att γ τ),
            ∀ (f : ↥Kℓ) (hf : f ∈ K₀) (hf' : τ f ∈ K₀), (⟨f, hf⟩ : ↥K₀) ∈ O ↔ (⟨_, hf'⟩ : ↥K₀) ∈ O') ∧

          (∀ O ∈ nodes, ∀ O' ∈ nodes, O ≠ O' → ∃ (f : ↥K₀) (hf : f ∈ O) (hf' : f ∈ O'),
            ¬ IsUnit (⟨f, hf⟩ : ↥O) ∧ IsUnit (⟨f, hf'⟩ : ↥O')) ∧

          (∀ V : ValuationSubring ↥K₀, (∀ x : k, PA x ↔ algebraMap k ↥K₀ x ∈ V) →
                  (∀ (g : G₁) (hg : MF g)
              (hgi : Q g hg),
              C g hg hgi →
              RS g hg hgi →
                ∀ (hgK : yK g ∈ Kℓ), ∃ hF : (⟨yK g, hgK⟩ : ↥Kℓ) ∈ K₀,
                  (⟨_, hF⟩ : ↥K₀) ∈ V ∧
                  ∀ (c : k) (hc : PA c),
                    Pc g hg hgi c hc →
                    ∃ hm : (⟨_, hF⟩ : ↥K₀) - algebraMap k ↥K₀ c ∈ V, (⟨_, hm⟩ : ↥V) ∈ maximalIdeal ↥V) →
            (∀ f : ↥Kℓ, f ∈ B₀ → ∃ hf : f ∈ K₀, (⟨f, hf⟩ : ↥K₀) ∈ V) ∨
            (∃ O ∈ nodes, ∀ (f : ↥K₀) (hfO : f ∈ O), f ∈ V ∧ (¬ IsUnit (⟨f, hfO⟩ : ↥O) → ∀ hfV : f ∈ V, (⟨f, hfV⟩ : ↥V) ∈ maximalIdeal ↥V))) ∧

          (∀ O ∈ nodes,

            (∀ f : ↥K₀, f ∈ O → f ∈ W₀') ∧ ∃ (_ : IsLocalRing ↥O) (_ : IsNoetherianRing ↥O),
            (∀ x : k, PA x ↔ algebraMap k ↥K₀ x ∈ O) ∧
            (∀ (f : ↥K₀) (hf : f ∈ O), ∃ (x : k) (hx : algebraMap k ↥K₀ x ∈ O), PA x ∧
              ¬ IsUnit ((⟨f, hf⟩ : ↥O) - ⟨_, hx⟩)) ∧

            (∃ (E₀ : ℕ) (_ : 1 ≤ E₀)

               (_ : Mod E₀)
               (hπO : algebraMap k ↥K₀ π₀ ∈ O) (cx cy : ↥O) (u : (↥O)ˣ)
               (ι : (AdicCompletion (maximalIdeal ↥O) ↥O) ≃+* TT E₀)
               (γU γV : (TT E₀)ˣ),
              cx * cy = (⟨_, hπO⟩ : ↥O) ^ E₀ * (u : ↥O) ∧
              (∀ (x : k) (hx : PA x) (hxO : algebraMap k ↥K₀ x ∈ O),
                ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨_, hxO⟩) =
                  Rc E₀ x hx) ∧
              ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) cx) = RU E₀ γU ∧
              ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) cy) = RV E₀ γV ∧
              ((cy : ↥K₀) ∈ W₀') ∧ (∀ hcy : (cy : ↥K₀) ∈ W₀', (⟨(cy : ↥K₀), hcy⟩ : ↥W₀') ∈ maximalIdeal ↥W₀') ∧
              (∀ hcx : (cx : ↥K₀) ∈ W₀', (⟨(cx : ↥K₀), hcx⟩ : ↥W₀') ∉ maximalIdeal ↥W₀') ∧

              (∃ (hjF : t₀ ∈ K₀) (hjO : (⟨_, hjF⟩ : ↥K₀) ∈ O) (e : ℕ) (wV : (TT E₀)ˣ), 1 ≤ e ∧
                ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨_, hjO⟩) = (wV : TT E₀) * (VV E₀) ^ e) ∧

              (∃ Wx : ValuationSubring ↥K₀,
                (∀ f : ↥K₀, f ∈ O → f ∈ Wx) ∧
                (∀ x : k, PA x ↔ algebraMap k ↥K₀ x ∈ Wx) ∧
                IsDiscreteValuationRing ↥Wx ∧
                (∃ hπW : algebraMap k ↥K₀ π₀ ∈ Wx, maximalIdeal ↥Wx = Ideal.span {(⟨_, hπW⟩ : ↥Wx)}) ∧
                (∃ t : ↥Wx, ∀ p : Polynomial k, (∀ n, PA (p.coeff n)) →
                  (∃ hm : Polynomial.aeval (t : ↥K₀) p ∈ Wx, (⟨_, hm⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) →
                    ∀ n, ∃ hc : algebraMap k ↥K₀ (p.coeff n) ∈ Wx, (⟨_, hc⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) ∧
                (∀ hcx : (cx : ↥K₀) ∈ Wx, (⟨(cx : ↥K₀), hcx⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) ∧
                (∀ hcy : (cy : ↥K₀) ∈ Wx, (⟨(cy : ↥K₀), hcy⟩ : ↥Wx) ∉ maximalIdeal ↥Wx) ∧
                (∀ (g : G₁) (hg : MF g)
                  (hgi : Q g hg),
                  C g hg hgi →
                  ∀ (hgK : yK g ∈ Kℓ), ∃ hF : (⟨yK g, hgK⟩ : ↥Kℓ) ∈ K₀,
                    (⟨_, hF⟩ : ↥K₀) ∈ Wx ∧
                    (∀ hW : (⟨_, hF⟩ : ↥K₀) ∈ Wx, (⟨_, hW⟩ : ↥Wx) ∈ maximalIdeal ↥Wx ↔
                      R0 g hg hgi) ∧
                    (RS g hg hgi →
                      (⟨_, hF⟩ : ↥K₀) ∈ O ∧
                      ∀ (hO : (⟨_, hF⟩ : ↥K₀) ∈ O) (c : k) (hc : PA c) (hcO : algebraMap k ↥K₀ c ∈ O),
                        Pc g hg hgi c hc →
                        ¬ IsUnit ((⟨_, hO⟩ : ↥O) - ⟨_, hcO⟩))) ∧
                (∀ O' ∈ nodes, O' ≠ O → ∃ f : ↥K₀, f ∈ O' ∧ f ∉ Wx)) ∧

              (∃ Bx : Subring ↥K₀,
                (∀ f : ↥K₀, f ∈ Bx → (f : ↥Kℓ) ∈ B₀ ∧ f ∈ O) ∧
                (∀ (f : ↥K₀), f ∈ Bx → RegUp (f : ↥Kℓ)) ∧
                (∀ f : ↥K₀, f ∈ O ↔ ∃ g h : ↥K₀, g ∈ Bx ∧ h ∈ Bx ∧ (∀ hh : h ∈ O, IsUnit (⟨h, hh⟩ : ↥O)) ∧ f * h = g) ∧
                (∀ f : ↥K₀, ∃ g h : ↥K₀, g ∈ Bx ∧ h ∈ Bx ∧ h ≠ 0 ∧ f * h = g) ∧
                (∃ T : Finset ↥K₀, Bx = Subring.closure
                  ({f : ↥K₀ | ∃ x : k, PA x ∧ f = algebraMap k ↥K₀ x} ∪ (↑T : Set ↥K₀))) ∧

                (∃ b : ↥K₀, b ∈ Bx ∧ ∀ V : ValuationSubring ↥K₀,
                  (∀ x : k, PA x ↔ algebraMap k ↥K₀ x ∈ V) →
                  (∀ hπV : algebraMap k ↥K₀ π₀ ∈ V, (⟨_, hπV⟩ : ↥V) ∈ maximalIdeal ↥V) →
                  ∀ (hjK' : JK ∈ Kℓ) (hjF : (⟨JK, hjK'⟩ : ↥Kℓ) ∈ K₀) (hjV : (⟨_, hjF⟩ : ↥K₀) ∈ V),
                    (∀ p : Polynomial k, p.Monic → (∀ i : ℕ, PA (p.coeff i)) →
                      ∀ hp : Polynomial.aeval (⟨_, hjF⟩ : ↥K₀) (p.map (algebraMap k ↥K₀)) ∈ V,
                        (⟨_, hp⟩ : ↥V) ∉ maximalIdeal ↥V) →
                  (∃ f : ↥K₀, f ∈ O ∧ f ∉ V) → b ∉ V)))))) :
        (∃ (hjR : P1) (_ : P2 hjR) (hJK : PJ) (a₀ : k) (ha₀ : PA a₀) (_ : Pin hjR a₀ ha₀)
           (nodes : Finset (Subring ↥F₀)),
          nodes.card = ncard ∧
          (∃ Bc : Subring ↥F₀,
            (∃ T : Finset ↥F₀, Bc = Subring.closure
              ({f : ↥F₀ | ∃ x : k, PA x ∧ f = algebraMap k ↥F₀ x} ∪ (↑T : Set ↥F₀))) ∧
            ∀ O ∈ nodes, (∀ f : ↥F₀, f ∈ Bc → f ∈ O) ∧
              (∀ f : ↥F₀, f ∈ O ↔ ∃ g h : ↥F₀, g ∈ Bc ∧ h ∈ Bc ∧ (∀ hh : h ∈ O, IsUnit (⟨h, hh⟩ : ↥O)) ∧ f * h = g)) ∧

          (∀ (ζ : ιT) (γ : S), γ ∈ Γ → ∀ O ∈ nodes, ∃ O' ∈ nodes,
            ∀ (f : F) (hf : f ∈ F₀) (hf' : σ ζ γ f ∈ F₀), (⟨f, hf⟩ : ↥F₀) ∈ O ↔ (⟨_, hf'⟩ : ↥F₀) ∈ O') ∧
          (∀ (ζ : ιT), ∀ O ∈ nodes, ∀ O' ∈ nodes, ∃ γ : S, γ ∈ Γ ∧
            ∀ (f : F) (hf : f ∈ F₀) (hf' : σ ζ γ f ∈ F₀), (⟨f, hf⟩ : ↥F₀) ∈ O ↔ (⟨_, hf'⟩ : ↥F₀) ∈ O') ∧

          (∀ O ∈ nodes, ∀ O' ∈ nodes, O ≠ O' → ∃ (f : ↥F₀) (hf : f ∈ O) (hf' : f ∈ O'),
            ¬ IsUnit (⟨f, hf⟩ : ↥O) ∧ IsUnit (⟨f, hf'⟩ : ↥O')) ∧

          (∀ V : ValuationSubring ↥F₀, (∀ x : k, PA x ↔ algebraMap k ↥F₀ x ∈ V) →
                  (∀ (g : G₁) (hg : MF g)
              (hgi : Q g hg),
              C g hg hgi →
              RS g hg hgi →
                ∃ hF : vF g hg ∈ F₀,
                  (⟨_, hF⟩ : ↥F₀) ∈ V ∧
                  ∀ (c : k) (hc : PA c),
                    Pc g hg hgi c hc →
                    ∃ hm : (⟨_, hF⟩ : ↥F₀) - algebraMap k ↥F₀ c ∈ V, (⟨_, hm⟩ : ↥V) ∈ maximalIdeal ↥V) →
            (∀ f : F, f ∈ B → ∃ hf : f ∈ F₀, (⟨f, hf⟩ : ↥F₀) ∈ V) ∨
            (∃ O ∈ nodes, ∀ (f : ↥F₀) (hfO : f ∈ O), f ∈ V ∧ (¬ IsUnit (⟨f, hfO⟩ : ↥O) → ∀ hfV : f ∈ V, (⟨f, hfV⟩ : ↥V) ∈ maximalIdeal ↥V))) ∧

          (∀ O ∈ nodes,

            (∀ f : ↥F₀, f ∈ O → f ∈ W₀) ∧ ∃ (_ : IsLocalRing ↥O) (_ : IsNoetherianRing ↥O),
            (∀ x : k, PA x ↔ algebraMap k ↥F₀ x ∈ O) ∧
            (∀ (f : ↥F₀) (hf : f ∈ O), ∃ (x : k) (hx : algebraMap k ↥F₀ x ∈ O), PA x ∧
              ¬ IsUnit ((⟨f, hf⟩ : ↥O) - ⟨_, hx⟩)) ∧

            (∃ (E₀ : ℕ) (_ : 1 ≤ E₀)

               (_ : Mod E₀)
               (hπO : algebraMap k ↥F₀ π₀ ∈ O) (cx cy : ↥O) (u : (↥O)ˣ)
               (ι : (AdicCompletion (maximalIdeal ↥O) ↥O) ≃+* TT E₀)
               (γU γV : (TT E₀)ˣ),
              cx * cy = (⟨_, hπO⟩ : ↥O) ^ E₀ * (u : ↥O) ∧
              (∀ (x : k) (hx : PA x) (hxO : algebraMap k ↥F₀ x ∈ O),
                ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨_, hxO⟩) =
                  Rc E₀ x hx) ∧
              ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) cx) = RU E₀ γU ∧
              ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) cy) = RV E₀ γV ∧
              ((cy : ↥F₀) ∈ W₀) ∧ (∀ hcy : (cy : ↥F₀) ∈ W₀, (⟨(cy : ↥F₀), hcy⟩ : ↥W₀) ∈ maximalIdeal ↥W₀) ∧
              (∀ hcx : (cx : ↥F₀) ∈ W₀, (⟨(cx : ↥F₀), hcx⟩ : ↥W₀) ∉ maximalIdeal ↥W₀) ∧

              (∃ (hjF : t₁ hJK a₀ ∈ F₀) (hjO : (⟨_, hjF⟩ : ↥F₀) ∈ O) (e : ℕ) (wV : (TT E₀)ˣ), 1 ≤ e ∧
                ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨_, hjO⟩) = (wV : TT E₀) * (VV E₀) ^ e) ∧

              (∃ Wx : ValuationSubring ↥F₀,
                (∀ f : ↥F₀, f ∈ O → f ∈ Wx) ∧
                (∀ x : k, PA x ↔ algebraMap k ↥F₀ x ∈ Wx) ∧
                IsDiscreteValuationRing ↥Wx ∧
                (∃ hπW : algebraMap k ↥F₀ π₀ ∈ Wx, maximalIdeal ↥Wx = Ideal.span {(⟨_, hπW⟩ : ↥Wx)}) ∧
                (∃ t : ↥Wx, ∀ p : Polynomial k, (∀ n, PA (p.coeff n)) →
                  (∃ hm : Polynomial.aeval (t : ↥F₀) p ∈ Wx, (⟨_, hm⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) →
                    ∀ n, ∃ hc : algebraMap k ↥F₀ (p.coeff n) ∈ Wx, (⟨_, hc⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) ∧
                (∀ hcx : (cx : ↥F₀) ∈ Wx, (⟨(cx : ↥F₀), hcx⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) ∧
                (∀ hcy : (cy : ↥F₀) ∈ Wx, (⟨(cy : ↥F₀), hcy⟩ : ↥Wx) ∉ maximalIdeal ↥Wx) ∧
                (∀ (g : G₁) (hg : MF g)
                  (hgi : Q g hg),
                  C g hg hgi →
                  ∃ hF : vF g hg ∈ F₀,
                    (⟨_, hF⟩ : ↥F₀) ∈ Wx ∧
                    (∀ hW : (⟨_, hF⟩ : ↥F₀) ∈ Wx, (⟨_, hW⟩ : ↥Wx) ∈ maximalIdeal ↥Wx ↔
                      R0 g hg hgi) ∧
                    (RS g hg hgi →
                      (⟨_, hF⟩ : ↥F₀) ∈ O ∧
                      ∀ (hO : (⟨_, hF⟩ : ↥F₀) ∈ O) (c : k) (hc : PA c) (hcO : algebraMap k ↥F₀ c ∈ O),
                        Pc g hg hgi c hc →
                        ¬ IsUnit ((⟨_, hO⟩ : ↥O) - ⟨_, hcO⟩))) ∧
                (∀ O' ∈ nodes, O' ≠ O → ∃ f : ↥F₀, f ∈ O' ∧ f ∉ Wx)) ∧

              (∃ Bx : Subring ↥F₀,
                (∀ f : ↥F₀, f ∈ Bx → (f : F) ∈ B ∧ f ∈ O) ∧
                (∀ (f : ↥F₀), f ∈ Bx → RegDn (f : F)) ∧
                (∀ f : ↥F₀, f ∈ O ↔ ∃ g h : ↥F₀, g ∈ Bx ∧ h ∈ Bx ∧ (∀ hh : h ∈ O, IsUnit (⟨h, hh⟩ : ↥O)) ∧ f * h = g) ∧
                (∀ f : ↥F₀, ∃ g h : ↥F₀, g ∈ Bx ∧ h ∈ Bx ∧ h ≠ 0 ∧ f * h = g) ∧
                (∃ T : Finset ↥F₀, Bx = Subring.closure
                  ({f : ↥F₀ | ∃ x : k, PA x ∧ f = algebraMap k ↥F₀ x} ∪ (↑T : Set ↥F₀))) ∧

                (∃ b : ↥F₀, b ∈ Bx ∧ ∀ V : ValuationSubring ↥F₀,
                  (∀ x : k, PA x ↔ algebraMap k ↥F₀ x ∈ V) →
                  (∀ hπV : algebraMap k ↥F₀ π₀ ∈ V, (⟨_, hπV⟩ : ↥V) ∈ maximalIdeal ↥V) →
                  ∀ (hjF : JF ∈ F₀) (hjV : (⟨JF, hjF⟩ : ↥F₀) ∈ V),
                    (∀ p : Polynomial k, p.Monic → (∀ i : ℕ, PA (p.coeff i)) →
                      ∀ hp : Polynomial.aeval (⟨JF, hjF⟩ : ↥F₀) (p.map (algebraMap k ↥F₀)) ∈ V,
                        (⟨_, hp⟩ : ↥V) ∉ maximalIdeal ↥V) →
                  (∃ f : ↥F₀, f ∈ O ∧ f ∉ V) → b ∉ V))))) := by
  subst hW₀
  classical
  obtain ⟨hjR, hjs, hpin, nodes₀, hcard₀, ⟨Bc₀, hBcFG, hBcloc⟩, heqv₀, htrans₀, hsep₀, hcover₀, hnode₀⟩ := hN
  have hnodes' : ∀ O : Subring ↥F₀, O ∈ nodes₀.image (imS φ.toRingEquiv) ↔
      ∃ O₀ ∈ nodes₀, ∀ y : ↥F₀, y ∈ O ↔ φ.symm y ∈ O₀ := by
    intro O
    rw [mem_image_imS_iff]
    constructor
    · rintro ⟨O₀, hO₀, rfl⟩
      exact ⟨O₀, hO₀, fun y => mem_imS_iff⟩
    · rintro ⟨O₀, hO₀, h⟩
      exact ⟨O₀, hO₀, SetLike.ext (fun y => by rw [h y]; exact mem_imS_iff.symm)⟩
  refine ⟨hjR, hjs, hPJ, a₀F, ha₀F, hpin ha₀F, nodes₀.image (imS φ.toRingEquiv), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [card_image_imS]; exact hcard₀
  ·
    refine ⟨imS φ.toRingEquiv Bc₀, chartFG_transport φ Bc₀ PA hBcFG, ?_⟩
    intro O hO
    obtain ⟨O₀, hO₀, rfl⟩ := (mem_image_imS_iff _ _ _).mp hO
    obtain ⟨hsub, hlocBc⟩ := hBcloc O₀ hO₀
    exact ⟨fun f hf => mem_imS_iff.mpr (hsub _ (mem_imS_iff.mp hf)), fun f => chartLoc_transport φ Bc₀ O₀ hlocBc f⟩
  · exact nodes_eqv_transport K₀ F₀ φ Γ Att σ hfwd nodes₀ _ hnodes' heqv₀
  · exact nodes_trans_transport K₀ F₀ φ Γ Att σ hbwd nodes₀ _ hnodes' htrans₀
  · intro O hO O' hO' hne
    obtain ⟨O₀, hO₀, rfl⟩ := (mem_image_imS_iff _ _ _).mp hO
    obtain ⟨O₀', hO₀', rfl⟩ := (mem_image_imS_iff _ _ _).mp hO'
    exact sep_transport φ O₀ O₀' (hsep₀ O₀ hO₀ O₀' hO₀') hne
  · intro V hVA hVs
    have hcov := hcover₀ (V.comap (φ.toRingEquiv : ↥K₀ →+* ↥F₀))
      (fun x => coverConst_transport K₀ F₀ φ V PA hVA x)
      (fun g hg hgi hcusp hRs hgK =>
        ⟨hyK₀ g hg, coverHyp_transport K₀ F₀ φ V PA (Pc g hg hgi) _ (hyK₀ g hg) _ (hv g hg hgK (hyK₀ g hg)) (hVs g hg hgi hcusp hRs)⟩)
    rcases hcov with hleft | ⟨O₀, hO₀, hdom⟩
    · left
      exact fun f hf => coverLeft_transport Ob K₀ F₀ φ B₀ B hB V hleft f hf
    · right
      exact ⟨imS φ.toRingEquiv O₀, Finset.mem_image_of_mem _ hO₀, fun f hfO => coverRight_transport φ V O₀ hdom f hfO⟩
  · intro O hO
    obtain ⟨O₀, hO₀, rfl⟩ := (mem_image_imS_iff _ _ _).mp hO
    obtain ⟨hOW, hloc, hnoe, hconst, hresid, E₀, hE₀, hmod, hπO, cx, cy, u, ι, γU, γV, hprod, hconstι, hιcx, hιcy,
      hcyW, hcyWm, hcxW, ⟨hjF₀, hjO₀, e7, wV, he7, hι7⟩, ⟨Wx, hWa, hWb, hWc, hWd, hWe, hWf, hWg, hlaw, hWsep⟩, ⟨Bx, hBa, hBb, hBc, hBd, hBe, ⟨b₀, hb₀Bx, hb₀⟩⟩⟩ := hnode₀ O₀ hO₀
    haveI := hloc
    haveI := hnoe
    have hπO' : algebraMap k ↥F₀ π₀ ∈ imS φ.toRingEquiv O₀ := algebraMap_mem_imS φ O₀ π₀ hπO
    obtain ⟨ι', hι'⟩ := exists_iota_transport φ O₀ _ ι
    refine ⟨fun f hf => imS_le_comap φ O₀ W₀' hOW f hf, isLocalRing_imS φ.toRingEquiv O₀, isNoetherianRing_imS φ.toRingEquiv O₀,
      const_imS φ O₀ PA hconst, resid_imS φ O₀ PA hresid,
      E₀, hE₀, hmod, hπO', imSEquiv φ.toRingEquiv O₀ cx, imSEquiv φ.toRingEquiv O₀ cy,
      Units.map (imSEquiv φ.toRingEquiv O₀ : ↥O₀ →* ↥(imS φ.toRingEquiv O₀)) u, ι', γU, γV,
      prod_transport φ O₀ π₀ hπO hπO' E₀ cx cy u hprod, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx hxO
      have hxO₀ := algebraMap_mem_of_mem_imS φ O₀ x hxO
      rw [← imSEquiv_algebraMap φ O₀ x hxO₀ hxO, hι']
      exact hconstι x hx hxO₀
    · rw [hι']; exact hιcx
    · rw [hι']; exact hιcy
    · exact (coe_imSEquiv_mem_comap_iff φ O₀ W₀' cy).mpr hcyW
    · exact forall_mem_maximalIdeal_transport φ W₀' (cy : ↥K₀) hcyWm
    · exact forall_not_mem_maximalIdeal_transport φ W₀' (cx : ↥K₀) hcxW
    ·
      have hjF₁ : t₁ hPJ a₀F ∈ F₀ := by rw [← ht hjF₀]; exact (φ ⟨t₀, hjF₀⟩).2
      have hx7 : (⟨t₁ hPJ a₀F, hjF₁⟩ : ↥F₀) = φ.toRingEquiv ⟨t₀, hjF₀⟩ := Subtype.ext (ht hjF₀).symm
      have hjO₁ : (⟨t₁ hPJ a₀F, hjF₁⟩ : ↥F₀) ∈ imS φ.toRingEquiv O₀ := by rw [hx7]; exact apply_mem_imS_iff.mpr hjO₀
      refine ⟨hjF₁, hjO₁, e7, wV, he7, ?_⟩
      have h7 : (⟨⟨t₁ hPJ a₀F, hjF₁⟩, hjO₁⟩ : ↥(imS φ.toRingEquiv O₀)) = imSEquiv φ.toRingEquiv O₀ ⟨⟨t₀, hjF₀⟩, hjO₀⟩ :=
        Subtype.ext hx7
      rw [h7, hι']; exact hι7
    · refine ⟨Wx.comap (φ.symm.toRingEquiv : ↥F₀ →+* ↥K₀), fun f hf => imS_le_comap φ O₀ Wx hWa f hf,
        fun x => constants_mem_transport K₀ F₀ φ Wx _ (fun f => Iff.rfl) PA hWb x, ?_, ?_, ?_,
        forall_mem_maximalIdeal_transport φ Wx (cx : ↥K₀) hWf,
        forall_not_mem_maximalIdeal_transport φ Wx (cy : ↥K₀) hWg, ?_, ?_⟩
      · haveI := hWc
        exact isDiscreteValuationRing_comap _ _
      · obtain ⟨hπW, hmax⟩ := hWd
        exact exists_mem_and_maximalIdeal_eq_span φ.symm.toRingEquiv Wx _ rfl _ hπW hmax _
          (algEquiv_symm_toRingEquiv_algebraMap φ π₀)
      · obtain ⟨t, ht⟩ := hWe
        exact resTrans_transport φ Wx PA t ht
      · intro g hg hgi hcusp
        exact law_transport K₀ F₀ φ Wx O₀ PA (Pc g hg hgi) (R0 g hg hgi) (RS g hg hgi) _
          (hlaw g hg hgi hcusp (hyK g hg)) _ (fun hF => hv g hg (hyK g hg) hF)
      · intro O' hO' hne
        obtain ⟨O'₀, hO'₀, rfl⟩ := (mem_image_imS_iff _ _ _).mp hO'
        obtain ⟨f₀, hf₀O, hf₀W⟩ := hWsep O'₀ hO'₀ (fun h => hne (by rw [h]))
        exact ⟨φ.toRingEquiv f₀, apply_mem_imS_iff.mpr hf₀O, fun h => hf₀W ((apply_mem_comap_symm_iff φ Wx _).mp h)⟩
    · refine ⟨imS φ.toRingEquiv Bx, fun f hf => chartB_transport Ob K₀ F₀ φ B₀ B hB Bx O₀ hBa f hf,
        hreg Bx hBb, fun f => chartLoc_transport φ Bx O₀ hBc f, fun f => chartFrac_transport φ Bx hBd f,
        chartFG_transport φ Bx PA hBe, ?_⟩

      refine ⟨φ.toRingEquiv b₀, apply_mem_imS_iff.mpr hb₀Bx, ?_⟩
      intro V hVA hVπ hjF hjV hres hfO hbV
      have hJx : (⟨JF, hjF⟩ : ↥F₀) = φ.toRingEquiv ⟨⟨JK, hJKmem⟩, hJK₀⟩ := Subtype.ext hJφ.symm
      refine hb₀ (V.comap (φ.toRingEquiv : ↥K₀ →+* ↥F₀)) (fun x => coverConst_transport K₀ F₀ φ V PA hVA x) ?_ hJKmem hJK₀ ?_ ?_ ?_ hbV
      ·
        intro hπV
        have hπV' : algebraMap k ↥F₀ π₀ ∈ V := by
          have := hπV; rw [ValuationSubring.mem_comap] at this
          rwa [show (φ.toRingEquiv : ↥K₀ →+* ↥F₀) (algebraMap k ↥K₀ π₀) = algebraMap k ↥F₀ π₀ from toRingEquiv_algebraMap' φ π₀] at this
        rw [mem_maximalIdeal_comap_iff]
        have : comapEquiv φ.toRingEquiv V ⟨_, hπV⟩ = ⟨_, hπV'⟩ := Subtype.ext (toRingEquiv_algebraMap' φ π₀)
        rw [this]; exact hVπ hπV'
      ·
        show φ.toRingEquiv ⟨⟨JK, hJKmem⟩, hJK₀⟩ ∈ V
        rw [← hJx]; exact hjV
      ·
        intro p hp hpA hpV
        have hae : φ.toRingEquiv (Polynomial.aeval (⟨⟨JK, hJKmem⟩, hJK₀⟩ : ↥K₀) (p.map (algebraMap k ↥K₀))) =
            Polynomial.aeval (⟨JF, hjF⟩ : ↥F₀) (p.map (algebraMap k ↥F₀)) := by
          rw [hJx, toRingEquiv_apply', toRingEquiv_apply']
          exact aeval_map_algebraMap_transport φ _ p
        have hpV' : Polynomial.aeval (⟨JF, hjF⟩ : ↥F₀) (p.map (algebraMap k ↥F₀)) ∈ V := by
          rw [← hae]; exact hpV
        rw [mem_maximalIdeal_comap_iff]
        have : comapEquiv φ.toRingEquiv V ⟨_, hpV⟩ = ⟨_, hpV'⟩ := Subtype.ext hae
        rw [this]; exact hres p hp hpA hpV'
      ·
        obtain ⟨f, hfO, hfV⟩ := hfO
        refine ⟨φ.toRingEquiv.symm f, mem_imS_iff.mp hfO, fun hf => hfV ?_⟩
        have hf' : φ.toRingEquiv (φ.toRingEquiv.symm f) ∈ V := hf
        rwa [RingEquiv.apply_symm_apply] at hf'

end Ntransport
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_moduliHasse_commonChart_nodes_igusaSep_levelField_of_nodes_fixedField_of_algEquiv_of_eq_two_of_dvd.S3GlueKit"

end S3GlueKit
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_Diamond_exists_moduliHasse_commonChart_nodes_igusaSep_levelField_of_nodes_fixedField_of_algEquiv_of_eq_two_of_dvd.S3GlueKit"

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup AlgebraicCurve.TwoChartIntegralModel
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem solution
    (q : ℕ)
    [Fact q.Prime]
    (hq2 : q = 2)
    (M' : ℕ)
    [NeZero M']

    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (s : ↥W)
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    (π₀ : ↥k₀)
    (hπ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (ℓ : ℕ)
    (ζ₀ : ↥k₀)
    (ϖt : ↥k₀)
    (Kb : IntermediateField ↥k₀ (AlgebraicClosure ℚ))
    (Ab : ValuationSubring ↥Kb)
    (hAb : ∀ x : ↥Kb, x ∈ Ab ↔ (x : (AlgebraicClosure ℚ)) ∈ A)
    (ϖb : ↥Ab)
    (ξ : ↥k₀)
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)
    (Kℓ : IntermediateField ↥k₀ (LaurentSeries ↥k₀))
    [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ]
    [IsScalarTower ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥Kℓ]
    (jℓ : ↥Kℓ)
    [Fact (jℓ ≠ 0)]
    (ϖt' : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (y : Ideal ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ))
    (Bt : Subalgebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ)
    (Wt : ValuationSubring ↥Kℓ)
    (hBW : ∀ f : ↥Kℓ, f ∈ Bt → f ∈ Wt)
    (n : ℕ)
    (γ₀ : SL(2, ℤ))
    (τ₀ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ)
    (m : ℕ)
    (ζc : (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hjK : ModularCurve.jqNModC ↥k₀ q ∈ Kℓ)
    (a₀ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (ends : Finset (Subring ↥Kℓ))
    (hqM' : ¬ q ∣ M')
    (hA : A.LiesOverPrime q)
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
        ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
          ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
            coeffMap (IsLocalRing.residue ↥A) y)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
        Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A)
    (hℓ : ℓ.Prime)
    (hℓ3 : 3 ≤ ℓ)
    (hℓq : ℓ ≠ q)
    (hℓM' : ¬ ℓ ∣ M')
    (hζ₀ : IsPrimitiveRoot ((ζ₀ : ↥k₀) : AlgebraicClosure ℚ) (q * ℓ))
    (hϖtA : (ϖt : AlgebraicClosure ℚ) ∈ A)
    (hϖt : ∃ u : ↥A, IsUnit u ∧ (ϖt : AlgebraicClosure ℚ) ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ) * (u : AlgebraicClosure ℚ))
    (hKb : Kb = ⊥)
    (hϖb : maximalIdeal ↥Ab = Ideal.span {ϖb})
    (hϖb0 : ϖb ≠ 0)
    (htame : IsUnit (((ℓg - 1) / 2 : ℕ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hξ : IsPrimitiveRoot ξ q)
    (hKℓ : Kℓ = ModularCurve.laurentBaseChange ↥k₀
      (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (hjℓ : ((jℓ : LaurentSeries ↥k₀)) = ModularCurve.coeffEmb ↥k₀ ModularCurve.jq)
    (hϖt' : (ϖt' : ↥k₀) = ϖt)
    (hy : y.IsMaximal)
    (hϖy : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) ⟨π₀, hπ⟩ ∈ y)
    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
        (φ : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) →+* Ω), RingHom.ker φ = y → φ (jChartFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) ∈ ModularCurve.ssJSet q Ω)
    (hover : (∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
        (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
        (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) :
            ↥(modularFunctionFieldBar M'))) →
        (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') ∈
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
        ∀ (hgK : (coeffEmb ↥k₀ g) ∈ Kℓ)
          (hgC : (⟨_, hgK⟩ : ↥Kℓ) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ),
        ∀ (c : ↥k₀) (hc : (c : (AlgebraicClosure ℚ)) ∈ A),
          residue A ⟨(c : (AlgebraicClosure ℚ)), hc⟩ =
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩) →
          (⟨⟨_, hgK⟩, hgC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) -
              algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) ⟨c, hc⟩ ∈ y))
    (hOrbit : ∀ y' : Ideal ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), y'.IsMaximal →
        algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) ⟨π₀, hπ⟩ ∈ y' →
          (∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
            (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
            (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
              0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
              0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) :
                ↥(modularFunctionFieldBar M'))) →
            (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') ∈
                (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
            ∀ (hgK : (coeffEmb ↥k₀ g) ∈ Kℓ)
              (hgC : (⟨_, hgK⟩ : ↥Kℓ) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ),
            ∀ (c : ↥k₀) (hc : (c : (AlgebraicClosure ℚ)) ∈ A),
              residue A ⟨(c : (AlgebraicClosure ℚ)), hc⟩ =
                (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩) →
              (⟨⟨_, hgK⟩, hgC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) -
                  algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) ⟨c, hc⟩ ∈ y') →
        ∃ (γ : SL(2, ℤ)) (_ : γ ∈ CongruenceSubgroup.Gamma q) (_ : γ ∈ CongruenceSubgroup.Gamma0 M')
          (τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ),
          ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ ∧
          (∀ f : ↥Kℓ, f ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ →
            τ f ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) ∧
          (∀ (f : ↥Kℓ) (hf : f ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)
            (hf' : τ f ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ),
            (⟨f, hf⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) ∈ y ↔ (⟨τ f, hf'⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) ∈ y'))
    (hS1 :
        chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ ≤ Bt ∧
        (∀ f : ↥Kℓ, ∃ g h : ↥Bt, (h : ↥Kℓ) ≠ 0 ∧ f * (h : ↥Kℓ) = (g : ↥Kℓ)) ∧

        Algebra.FormallySmooth ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bt ∧ Algebra.FinitePresentation ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bt ∧
        Ring.KrullDimLE 1 (↥Bt ⧸ Ideal.span {algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bt ⟨π₀, hπ⟩}) ∧

        (∀ x : ↥k₀, algebraMap ↥k₀ ↥Kℓ x ∈ Wt ↔ ∃ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ a = x) ∧
        maximalIdeal ↥Wt = Ideal.span {(⟨algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩, hBW _ (Bt.algebraMap_mem ⟨π₀, hπ⟩)⟩ : ↥Wt)} ∧
        IsDiscreteValuationRing ↥Wt ∧
        (∀ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), b ∈ y ↔
          ∃ hb : (b : ↥Kℓ) ∈ Wt, (⟨(b : ↥Kℓ), hb⟩ : ↥Wt) ∈ maximalIdeal ↥Wt) ∧
        (∀ f : ↥Kℓ, f ∈ Wt ↔ ∃ g h : ↥Bt, (⟨(h : ↥Kℓ), hBW _ h.2⟩ : ↥Wt) ∉ maximalIdeal ↥Wt ∧ f * (h : ↥Kℓ) = (g : ↥Kℓ)) ∧

        (∀ (inst : Algebra (GaloisField q 2) (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))),
          ∃ (ρ : ↥Bt →+* DrinfeldCurve.CoordRing q (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))),
            Function.Surjective ρ ∧
            (∀ b : ↥Bt, ρ b = 0 ↔ (⟨(b : ↥Kℓ), hBW _ b.2⟩ : ↥Wt) ∈ maximalIdeal ↥Wt) ∧
            (∀ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), ρ (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bt a) = algebraMap (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) (DrinfeldCurve.CoordRing q (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))) (residue ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) a)) ∧
            (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
              ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ →
                (∀ f : ↥Kℓ, f ∈ Wt ↔ τ f ∈ Wt) →
                ∃ (c : (GaloisField q 2)ˣ) (hmem : (ModularCurve.FullLevel.redQ q γ, c) ∈ DrinfeldCurve.hSubgroup q),
                  (∀ (b : ↥Bt) (hb : τ (b : ↥Kℓ) ∈ Bt), ρ ⟨τ (b : ↥Kℓ), hb⟩ = DrinfeldCurve.hAction q (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨_, hmem⟩ (ρ b)) ∧
                  (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥Kℓ, τ k = k) → c ≠ 1) ∧

                  (∃ (γ' : SL(2, ℤ)) (_ : γ' ∈ CongruenceSubgroup.Gamma q) (_ : γ' ∈ CongruenceSubgroup.Gamma0 M') (τ' : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ)
                      (_ : ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ'⁻¹ Kℓ τ') (_ : ∀ f : ↥Kℓ, f ∈ Wt ↔ τ' f ∈ Wt)
                      (hmem' : ((1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)), c) ∈ DrinfeldCurve.hSubgroup q),
                    ∀ (b : ↥Bt) (hb : τ' (b : ↥Kℓ) ∈ Bt), ρ ⟨τ' (b : ↥Kℓ), hb⟩ = DrinfeldCurve.hAction q (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨_, hmem'⟩ (ρ b)))) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ →
            ∀ f : ↥Kℓ, f ∈ Bt → τ f ∈ Bt) ∧
        (∀ Q : Ideal ↥Bt, Q.IsPrime → algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bt ⟨π₀, hπ⟩ ∈ Q →
          ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧
            ∃ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ ∧
              ∀ b : ↥Bt, (⟨(b : ↥Kℓ), hBW _ b.2⟩ : ↥Wt) ∈ maximalIdeal ↥Wt → τ (b : ↥Kℓ) ∈ Bt ∧ ∀ hb : τ (b : ↥Kℓ) ∈ Bt, (⟨τ (b : ↥Kℓ), hb⟩ : ↥Bt) ∈ Q) ∧
        (∀ b : ↥Bt, (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
            ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ →
              ∀ hb : τ (b : ↥Kℓ) ∈ Bt, (⟨τ (b : ↥Kℓ), hBW _ hb⟩ : ↥Wt) ∈ maximalIdeal ↥Wt) →
          algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bt ⟨π₀, hπ⟩ ∣ b))
    (hn1 : 1 ≤ n)
    (hnq : n ∣ q + 1)
    (hγ₀Γ : γ₀ ∈ CongruenceSubgroup.Gamma q)
    (hγ₀Γ0 : γ₀ ∈ CongruenceSubgroup.Gamma0 M')
    (hτ₀ : ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ₀⁻¹ Kℓ τ₀)
    (hτ₀W : ∀ f : ↥Kℓ, f ∈ Wt ↔ τ₀ f ∈ Wt)
    (hm1 : 1 ≤ m)
    (hm : ∃ w : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), IsUnit w ∧ ⟨π₀, hπ⟩ ^ m = ϖt' * w)
    (hζc : ζc ^ n = 1)
    (hζcprim : ∀ k : ℕ, 0 < k → k < n → IsUnit (ζc ^ k - 1))
    (hjC : (⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ : ↥Kℓ) ∈ chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)
    (ha₀y : (⟨(⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ : ↥Kℓ), hjC⟩ : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) - algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) a₀ ∈ y)
    (hR7 : (∀ f : ↥Kℓ, f ∈ Bt → (τ₀ ^ n) f = f) ∧
          (∀ k : ℕ, 0 < k → k < n → ∃ f : ↥Kℓ, f ∈ Bt ∧ (τ₀ ^ k) f ≠ f) ∧
          (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
            ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ →
              (∀ f : ↥Kℓ, f ∈ Wt ↔ τ f ∈ Wt) → ∃ k : ℕ, k < n ∧ ∀ f : ↥Kℓ, f ∈ Bt → τ f = (τ₀ ^ k) f) ∧
          ends.card = q + 1 ∧
          (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
            ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ →
              (∀ f : ↥Kℓ, f ∈ Wt ↔ τ f ∈ Wt) → ∀ O ∈ ends, ∃ O' ∈ ends, ∀ f : ↥Kℓ, f ∈ O ↔ τ f ∈ O') ∧
          (∀ O ∈ ends, ∀ O' ∈ ends, ∃ (γ : SL(2, ℤ)) (_ : γ ∈ CongruenceSubgroup.Gamma0 M') (τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ) (_ : ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ),
            (∀ f : ↥Kℓ, f ∈ Wt ↔ τ f ∈ Wt) ∧ ∀ f : ↥Kℓ, f ∈ O ↔ τ f ∈ O') ∧
          (∀ O ∈ ends, ∀ f : ↥Kℓ, f ∈ O ↔ τ₀ f ∈ O) ∧
          (∀ O ∈ ends, ∀ O' ∈ ends, O ≠ O' → ∃ (f : ↥Kℓ) (hf : f ∈ O) (hf' : f ∈ O'),
            ¬ IsUnit (⟨f, hf⟩ : ↥O) ∧ IsUnit (⟨f, hf'⟩ : ↥O')) ∧

          (∃ Bc : Subalgebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ, Algebra.FiniteType ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bc ∧
            (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
              ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ →
                ∀ f : ↥Kℓ, f ∈ Bc → τ f ∈ Bc) ∧
            ∀ O ∈ ends, (∀ f : ↥Kℓ, f ∈ Bc → f ∈ O) ∧
              (∀ f : ↥Kℓ, f ∈ O ↔ ∃ g h : ↥Kℓ, g ∈ Bc ∧ h ∈ Bc ∧ (∀ hh : h ∈ O, IsUnit (⟨h, hh⟩ : ↥O)) ∧ f * h = g)) ∧

          (∀ O ∈ ends, ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
              ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ →
                (∀ f : ↥Kℓ, f ∈ O → τ f ∈ Wt) → ∀ f : ↥Kℓ, f ∈ Wt ↔ τ f ∈ Wt) ∧
          (∀ O ∈ ends,

            (∀ f : ↥Kℓ, f ∈ O → f ∈ Wt) ∧ ∃ (_ : IsLocalRing ↥O) (_ : IsNoetherianRing ↥O),
            (∀ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), (b : ↥Kℓ) ∈ O) ∧
            (∀ x : ↥k₀, algebraMap ↥k₀ ↥Kℓ x ∈ O ↔ ∃ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ a = x) ∧
            (∀ (f : ↥Kℓ) (hf : f ∈ O), ∃ (a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) (ha : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ a ∈ O), ¬ IsUnit ((⟨f, hf⟩ : ↥O) - ⟨_, ha⟩)) ∧

            (∃ (hϖO : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩ ∈ O) (cx cy : ↥O) (u : (↥O)ˣ) (ι : (AdicCompletion (maximalIdeal ↥O) ↥O) ≃+* (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m)))
               (γU γV : (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m))ˣ) (θ₀ : (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m)) ≃ₐ[(AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))] (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m))) (ζc' : (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))) (_ : ζc * ζc' = 1)
               (_ : IsLocalRing (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m))),
              cx * cy = (⟨_, hϖO⟩ : ↥O) ^ m * (u : ↥O) ∧
              (∀ (a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) (ha : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ a ∈ O), ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨_, ha⟩) = UVCrossingModel.const ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m) (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) a)) ∧
              ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) cx) = (γU : (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m))) * UVCrossingModel.U ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m) ∧
              ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) cy) = (γV : (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m))) * UVCrossingModel.V ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m) ∧
              (∀ hcy : (cy : ↥Kℓ) ∈ Wt, (⟨(cy : ↥Kℓ), hcy⟩ : ↥Wt) ∈ maximalIdeal ↥Wt) ∧
              (∀ hcx : (cx : ↥Kℓ) ∈ Wt, (⟨(cx : ↥Kℓ), hcx⟩ : ↥Wt) ∉ maximalIdeal ↥Wt) ∧

              (∃ (hjaO : (⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ : ↥Kℓ) - algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ a₀ ∈ O) (e : ℕ) (wV : (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m))ˣ), 1 ≤ e ∧
                ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨(⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ : ↥Kℓ) - algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ a₀, hjaO⟩) =
                  (wV : (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m))) * (UVCrossingModel.V ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m)) ^ e) ∧
              (∀ (f : ↥Kℓ) (hf : f ∈ O) (hf' : τ₀ f ∈ O),
                ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨_, hf'⟩) = θ₀ (ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨f, hf⟩))) ∧
              θ₀ (UVCrossingModel.U ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m)) - UVCrossingModel.const ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m) ζc * UVCrossingModel.U ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m) ∈
                (maximalIdeal (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m))) ^ 2 ∧
              θ₀ (UVCrossingModel.V ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m)) - UVCrossingModel.const ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m) ζc' * UVCrossingModel.V ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m) ∈
                (maximalIdeal (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ m))) ^ 2 ∧

              (∃ Wx : ValuationSubring ↥Kℓ,
                (∀ f : ↥Kℓ, f ∈ O → f ∈ Wx) ∧
                (∀ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), (b : ↥Kℓ) ∈ Wx) ∧
                (∀ x : ↥k₀, algebraMap ↥k₀ ↥Kℓ x ∈ Wx ↔ ∃ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ a = x) ∧
                IsDiscreteValuationRing ↥Wx ∧
                (∃ hϖWx : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩ ∈ Wx, maximalIdeal ↥Wx = Ideal.span {(⟨_, hϖWx⟩ : ↥Wx)}) ∧
                (∃ (t : ↥Wx), ∀ p : Polynomial ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))),
                  (∃ hm : Polynomial.aeval (t : ↥Kℓ) (p.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀)) ∈ Wx, (⟨_, hm⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) →
                    ∀ i, p.coeff i ∈ maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ∧

                (∀ p : Polynomial ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))),
                  (∃ hm : Polynomial.aeval (⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ : ↥Kℓ) (p.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀)) ∈ Wx, (⟨_, hm⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) →
                    ∀ i, p.coeff i ∈ maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ∧
                (∀ hcx : (cx : ↥Kℓ) ∈ Wx, (⟨(cx : ↥Kℓ), hcx⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) ∧
                (∀ hcy : (cy : ↥Kℓ) ∈ Wx, (⟨(cy : ↥Kℓ), hcy⟩ : ↥Wx) ∉ maximalIdeal ↥Wx) ∧
                (∀ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), (∀ hb : (b : ↥Kℓ) ∈ Wx, (⟨(b : ↥Kℓ), hb⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) → b ∈ y) ∧
                (∃ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), b ∈ y ∧ ∀ hb : (b : ↥Kℓ) ∈ Wx, (⟨(b : ↥Kℓ), hb⟩ : ↥Wx) ∉ maximalIdeal ↥Wx) ∧

                (∀ O' ∈ ends, O' ≠ O → ∃ f : ↥Kℓ, f ∈ O' ∧ f ∉ Wx) ∧

                (∀ O' ∈ ends, ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
                  ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ →
                    (∀ f : ↥Kℓ, f ∈ O' → τ f ∈ Wx) → O' = O)) ∧

              (∃ Bx : Subalgebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ,
                (∀ f : ↥Kℓ, f ∈ Bx → f ∈ Bt ∧ f ∈ O) ∧
                Algebra.FiniteType ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Bx ∧
                (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
                  ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ →
                    ∀ f : ↥Kℓ, f ∈ Bx → τ f ∈ Bx) ∧
                (∀ f : ↥Kℓ, f ∈ Bx → ∀ P : AlgebraicCurve.Place ↥k₀ ↥Kℓ, 0 ≤ P.ord jℓ → 0 ≤ P.ord f) ∧
                (∀ f : ↥Kℓ, f ∈ O ↔ ∃ g h : ↥Kℓ, g ∈ Bx ∧ h ∈ Bx ∧ (∀ hh : h ∈ O, IsUnit (⟨h, hh⟩ : ↥O)) ∧ f * h = g) ∧

                (∃ b : ↥Kℓ, b ∈ Bx ∧ ∀ V : ValuationSubring ↥Kℓ, (∀ x : ↥k₀, algebraMap ↥k₀ ↥Kℓ x ∈ V ↔ ∃ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ a = x) →
                  (∀ hϖV : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩ ∈ V, (⟨algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩, hϖV⟩ : ↥V) ∈ maximalIdeal ↥V) →
                  (∀ hjV : (jℓ : ↥Kℓ) ∈ V, (∀ p : Polynomial ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), p.Monic →
                      ∀ hp : Polynomial.aeval (jℓ : ↥Kℓ) (p.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ)) ∈ V,
                        (⟨_, hp⟩ : ↥V) ∉ maximalIdeal ↥V) →
                    (∃ f : ↥Kℓ, f ∈ O ∧ f ∉ V) → b ∉ V))))) ∧

          (∀ V : ValuationSubring ↥Kℓ, (∀ x : ↥k₀, algebraMap ↥k₀ ↥Kℓ x ∈ V ↔ ∃ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ a = x) →
            (∀ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), (b : ↥Kℓ) ∈ V) →
            (∀ b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), b ∈ y → ∀ hb : (b : ↥Kℓ) ∈ V, (⟨(b : ↥Kℓ), hb⟩ : ↥V) ∈ maximalIdeal ↥V) →
            (∀ f : ↥Kℓ, f ∈ Bt → f ∈ V) ∨
            (∃ O ∈ ends, ∀ (f : ↥Kℓ) (hfO : f ∈ O), f ∈ V ∧ (¬ IsUnit (⟨f, hfO⟩ : ↥O) → ∀ hfV : f ∈ V, (⟨f, hfV⟩ : ↥V) ∈ maximalIdeal ↥V))))
    (hR9 : (∃ b : ↥Kℓ, b ∈ Bt ∧ ∀ V : ValuationSubring ↥Kℓ, (∀ x : ↥k₀, algebraMap ↥k₀ ↥Kℓ x ∈ V ↔ ∃ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ a = x) →
            (∀ hϖV : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩ ∈ V, (⟨algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ ⟨π₀, hπ⟩, hϖV⟩ : ↥V) ∈ maximalIdeal ↥V) →
            (∀ hjV : (jℓ : ↥Kℓ) ∈ V, (∀ p : Polynomial ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), p.Monic →
                ∀ hp : Polynomial.aeval (jℓ : ↥Kℓ) (p.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ)) ∈ V,
                  (⟨_, hp⟩ : ↥V) ∉ maximalIdeal ↥V) → b ∉ V)))
    (hR10 : (∀ y'' : Ideal ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), y''.IsMaximal → algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ) ⟨π₀, hπ⟩ ∈ y'' →
            (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
              ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ →
                ¬ (∀ (b : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) (hb : τ (b : ↥Kℓ) ∈ chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ),
                    b ∈ y ↔ (⟨τ (b : ↥Kℓ), hb⟩ : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) ∈ y'')) →
            ∃ b : ↥Kℓ, b ∈ Bt ∧ ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
              ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ →
              ∀ V : ValuationSubring ↥Kℓ,
                (∀ c : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ), (c : ↥Kℓ) ∈ V) →
                (∀ (c : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) (hc : τ.symm (c : ↥Kℓ) ∈ chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ),
                    (⟨τ.symm (c : ↥Kℓ), hc⟩ : ↥(chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥Kℓ) jℓ)) ∈ y'' → ∀ hcV : (c : ↥Kℓ) ∈ V, (⟨(c : ↥Kℓ), hcV⟩ : ↥V) ∈ maximalIdeal ↥V) →
                b ∉ V))
    (hn : n = placeWidthChar q M' (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (G : Subgroup (↥Kℓ ≃ₐ[↥k₀] ↥Kℓ))
    (hG : G = Subgroup.closure {τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ | ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧
      ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ})
    (K₀ : IntermediateField ↥k₀ ↥Kℓ)
    (hK₀ : K₀ = IntermediateField.fixedField G)
    (B₀ : Subalgebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ)
    (hB₀ : ∀ f : ↥Kℓ, f ∈ B₀ ↔ f ∈ Bt ∧ ∀ τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ, τ ∈ G → τ f = f)
    (W₀' : ValuationSubring ↥K₀)
    (hW₀' : ∀ f : ↥K₀, f ∈ W₀' ↔ ((f : ↥Kℓ)) ∈ Wt)
    :
    letI : Algebra ↥k₀ ↥(fieldBar q M') :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
    ∀ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M')),

    (∀ f : ↥(fieldBar q M'), f ∈ F₀ ↔ ∀ n : ℤ, ∃ c : ↥k₀, ((f : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)).coeff n = ((c : ↥k₀) : AlgebraicClosure ℚ)) →
    ∀ (φ : ↥K₀ ≃ₐ[↥k₀] ↥F₀),

    (      (∀ f : ↥K₀, coeffMap (algebraMap ↥k₀ (AlgebraicClosure ℚ)) (((f : ↥Kℓ)) : LaurentSeries ↥k₀) =
        ( ((φ f : ↥F₀) : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)))) →

          (∀ (ζ : Idx q) (ξ' : ↥k₀), IsPrimitiveRoot ξ' q → ζ.val = (((ξ' : ↥k₀)) : AlgebraicClosure ℚ) →
        ∀ (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 M' →
        ∀ (τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ),
          ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ' q (q ^ 2 * M') H₁ γ Kℓ τ →
          ∃ hτ : ∀ f : ↥Kℓ, f ∈ K₀ → τ f ∈ K₀,
            ∀ f : ↥K₀, ((φ ⟨τ (f : ↥Kℓ), hτ (f : ↥Kℓ) f.2⟩ : ↥F₀) : ↥(fieldBar q M')) =
              levelAutBar q M' ζ γ ((φ f : ↥F₀) : ↥(fieldBar q M'))) →

          (∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
        (hgK : (coeffEmb ↥k₀ g) ∈ Kℓ) (hgK₀ : (⟨_, hgK⟩ : ↥Kℓ) ∈ K₀),
        ((φ ⟨⟨_, hgK⟩, hgK₀⟩ : ↥F₀) : ↥(fieldBar q M')) =
          IntermediateField.inclusion hle ⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩) →
    ∀ (W₀ : ValuationSubring ↥F₀), W₀ = W₀'.comap (φ.symm.toRingEquiv : ↥F₀ →+* ↥K₀) →
    ∀ (B : Subring ↥(fieldBar q M')),
    (∀ y : ↥(fieldBar q M'), y ∈ B ↔ ∃ x : ↥K₀, x ∈ B₀.toSubring.comap (algebraMap ↥K₀ ↥Kℓ) ∧
      y = ((algebraMap ↥F₀ ↥(fieldBar q M')).comp φ.toAlgHom.toRingHom) x) →

    (
    (∃

           (hjR : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
              ↥(modularFunctionFieldBar M')) ∈ R₀.integers)
           (_ : (R₀.residue ⟨_, hjR⟩ : modularFunctionFieldC (ResidueField A) M') ∈ (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring)
           (_ : ∀ ha₀ : ((a₀ : ↥k₀) : (AlgebraicClosure ℚ)) ∈ A,
              (residue A ⟨((a₀ : ↥k₀) : (AlgebraicClosure ℚ)), ha₀⟩) ^ q = (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hjR⟩))
           (nodes : Finset (Subring ↥K₀)),
          nodes.card = q + 1 ∧

          (∃ Bc : Subring ↥K₀,
            (∃ T : Finset ↥K₀, Bc = Subring.closure
              ({f : ↥K₀ | ∃ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ∧ f = algebraMap ↥k₀ ↥K₀ x} ∪ (↑T : Set ↥K₀))) ∧
            ∀ O ∈ nodes, (∀ f : ↥K₀, f ∈ Bc → f ∈ O) ∧
              (∀ f : ↥K₀, f ∈ O ↔ ∃ g h : ↥K₀, g ∈ Bc ∧ h ∈ Bc ∧ (∀ hh : h ∈ O, IsUnit (⟨h, hh⟩ : ↥O)) ∧ f * h = g)) ∧

          (∀ (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → ∀ (τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ), ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ → ∀ O ∈ nodes, ∃ O' ∈ nodes,
            ∀ (f : ↥Kℓ) (hf : f ∈ K₀) (hf' : τ f ∈ K₀), (⟨f, hf⟩ : ↥K₀) ∈ O ↔ (⟨_, hf'⟩ : ↥K₀) ∈ O') ∧
          (∀ O ∈ nodes, ∀ O' ∈ nodes, ∃ (γ : SL(2, ℤ)) (_ : γ ∈ Gamma0 M') (τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ) (_ : ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ),
            ∀ (f : ↥Kℓ) (hf : f ∈ K₀) (hf' : τ f ∈ K₀), (⟨f, hf⟩ : ↥K₀) ∈ O ↔ (⟨_, hf'⟩ : ↥K₀) ∈ O') ∧

          (∀ O ∈ nodes, ∀ O' ∈ nodes, O ≠ O' → ∃ (f : ↥K₀) (hf : f ∈ O) (hf' : f ∈ O'),
            ¬ IsUnit (⟨f, hf⟩ : ↥O) ∧ IsUnit (⟨f, hf'⟩ : ↥O')) ∧

          (∀ V : ValuationSubring ↥K₀, (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥K₀ x ∈ V) →
                  (∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
              (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
              (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
                0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
                  coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                  ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
                0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) :
                  ↥(modularFunctionFieldBar M'))) →
              (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') ∈
                  (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
                ∀ (hgK : (coeffEmb ↥k₀ g) ∈ Kℓ), ∃ hF : (⟨(coeffEmb ↥k₀ g), hgK⟩ : ↥Kℓ) ∈ K₀,
                  (⟨_, hF⟩ : ↥K₀) ∈ V ∧
                  ∀ (c : ↥k₀) (hc : (c : (AlgebraicClosure ℚ)) ∈ A),
                    residue A ⟨(c : (AlgebraicClosure ℚ)), hc⟩ =
                      (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩) →
                    ∃ hm : (⟨_, hF⟩ : ↥K₀) - algebraMap ↥k₀ ↥K₀ c ∈ V, (⟨_, hm⟩ : ↥V) ∈ maximalIdeal ↥V) →
            (∀ f : ↥Kℓ, f ∈ B₀ → ∃ hf : f ∈ K₀, (⟨f, hf⟩ : ↥K₀) ∈ V) ∨
            (∃ O ∈ nodes, ∀ (f : ↥K₀) (hfO : f ∈ O), f ∈ V ∧ (¬ IsUnit (⟨f, hfO⟩ : ↥O) → ∀ hfV : f ∈ V, (⟨f, hfV⟩ : ↥V) ∈ maximalIdeal ↥V))) ∧

          (∀ O ∈ nodes,

            (∀ f : ↥K₀, f ∈ O → f ∈ W₀') ∧ ∃ (_ : IsLocalRing ↥O) (_ : IsNoetherianRing ↥O),
            (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥K₀ x ∈ O) ∧
            (∀ (f : ↥K₀) (hf : f ∈ O), ∃ (x : ↥k₀) (hx : algebraMap ↥k₀ ↥K₀ x ∈ O), (x : (AlgebraicClosure ℚ)) ∈ A ∧
              ¬ IsUnit ((⟨f, hf⟩ : ↥O) - ⟨_, hx⟩)) ∧

            (∃ (E₀ : ℕ) (_ : 1 ≤ E₀)

               (_ : ∃ v : ↥k₀, (v : (AlgebraicClosure ℚ)) ∈ A ∧ ((v⁻¹ : ↥k₀) : (AlgebraicClosure ℚ)) ∈ A ∧
                  π₀ ^ E₀ = ϖt ^ (placeWidthChar q M' (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M'))) * v)
               (hπO : algebraMap ↥k₀ ↥K₀ π₀ ∈ O) (cx cy : ↥O) (u : (↥O)ˣ)
               (ι : (AdicCompletion (maximalIdeal ↥O) ↥O) ≃+* UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀))
               (γU γV : (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀))ˣ),
              cx * cy = (⟨_, hπO⟩ : ↥O) ^ E₀ * (u : ↥O) ∧
              (∀ (x : ↥k₀) (hx : (x : (AlgebraicClosure ℚ)) ∈ A) (hxO : algebraMap ↥k₀ ↥K₀ x ∈ O),
                ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨_, hxO⟩) =
                  UVCrossingModel.const ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀) (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨x, hx⟩)) ∧
              ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) cx) = (γU : UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀)) * UVCrossingModel.U ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀) ∧
              ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) cy) = (γV : UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀)) * UVCrossingModel.V ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀) ∧
              ((cy : ↥K₀) ∈ W₀') ∧ (∀ hcy : (cy : ↥K₀) ∈ W₀', (⟨(cy : ↥K₀), hcy⟩ : ↥W₀') ∈ maximalIdeal ↥W₀') ∧
              (∀ hcx : (cx : ↥K₀) ∈ W₀', (⟨(cx : ↥K₀), hcx⟩ : ↥W₀') ∉ maximalIdeal ↥W₀') ∧

              (∃ (hjF : (⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ : ↥Kℓ) - algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ a₀ ∈ K₀)
                 (hjO : (⟨_, hjF⟩ : ↥K₀) ∈ O) (e : ℕ) (wV : (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀))ˣ), 1 ≤ e ∧
                ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨_, hjO⟩) =
                  (wV : UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀)) * (UVCrossingModel.V ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀)) ^ e) ∧

              (∃ Wx : ValuationSubring ↥K₀,
                (∀ f : ↥K₀, f ∈ O → f ∈ Wx) ∧
                (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥K₀ x ∈ Wx) ∧
                IsDiscreteValuationRing ↥Wx ∧
                (∃ hπW : algebraMap ↥k₀ ↥K₀ π₀ ∈ Wx, maximalIdeal ↥Wx = Ideal.span {(⟨_, hπW⟩ : ↥Wx)}) ∧
                (∃ t : ↥Wx, ∀ p : Polynomial ↥k₀, (∀ n, ((p.coeff n : ↥k₀) : (AlgebraicClosure ℚ)) ∈ A) →
                  (∃ hm : Polynomial.aeval (t : ↥K₀) p ∈ Wx, (⟨_, hm⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) →
                    ∀ n, ∃ hc : algebraMap ↥k₀ ↥K₀ (p.coeff n) ∈ Wx, (⟨_, hc⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) ∧
                (∀ hcx : (cx : ↥K₀) ∈ Wx, (⟨(cx : ↥K₀), hcx⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) ∧
                (∀ hcy : (cy : ↥K₀) ∈ Wx, (⟨(cy : ↥K₀), hcy⟩ : ↥Wx) ∉ maximalIdeal ↥Wx) ∧
                (∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
                  (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
                  (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
                    0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
                      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                      ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
                    0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) :
                      ↥(modularFunctionFieldBar M'))) →
                  ∀ (hgK : (coeffEmb ↥k₀ g) ∈ Kℓ), ∃ hF : (⟨(coeffEmb ↥k₀ g), hgK⟩ : ↥Kℓ) ∈ K₀,
                    (⟨_, hF⟩ : ↥K₀) ∈ Wx ∧
                    (∀ hW : (⟨_, hF⟩ : ↥K₀) ∈ Wx, (⟨_, hW⟩ : ↥Wx) ∈ maximalIdeal ↥Wx ↔
                      (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') = 0) ∧
                    ((R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') ∈
                        (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
                      (⟨_, hF⟩ : ↥K₀) ∈ O ∧
                      ∀ (hO : (⟨_, hF⟩ : ↥K₀) ∈ O) (c : ↥k₀) (hc : (c : (AlgebraicClosure ℚ)) ∈ A) (hcO : algebraMap ↥k₀ ↥K₀ c ∈ O),
                        residue A ⟨(c : (AlgebraicClosure ℚ)), hc⟩ =
                          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩) →
                        ¬ IsUnit ((⟨_, hO⟩ : ↥O) - ⟨_, hcO⟩))) ∧

                (∀ O' ∈ nodes, O' ≠ O → ∃ f : ↥K₀, f ∈ O' ∧ f ∉ Wx)) ∧

              (∃ Bx : Subring ↥K₀,
                (∀ f : ↥K₀, f ∈ Bx → (f : ↥Kℓ) ∈ B₀ ∧ f ∈ O) ∧
                (∀ (f : ↥K₀), f ∈ Bx → ∀ P : Place ↥k₀ ↥Kℓ,
                  0 ≤ P.ord (jℓ : ↥Kℓ) → 0 ≤ P.ord (f : ↥Kℓ)) ∧
                (∀ f : ↥K₀, f ∈ O ↔ ∃ g h : ↥K₀, g ∈ Bx ∧ h ∈ Bx ∧ (∀ hh : h ∈ O, IsUnit (⟨h, hh⟩ : ↥O)) ∧ f * h = g) ∧
                (∀ f : ↥K₀, ∃ g h : ↥K₀, g ∈ Bx ∧ h ∈ Bx ∧ h ≠ 0 ∧ f * h = g) ∧
                (∃ T : Finset ↥K₀, Bx = Subring.closure
                  ({f : ↥K₀ | ∃ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ∧ f = algebraMap ↥k₀ ↥K₀ x} ∪ (↑T : Set ↥K₀))) ∧

                (∃ b : ↥K₀, b ∈ Bx ∧ ∀ V : ValuationSubring ↥K₀,
                  (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥K₀ x ∈ V) →
                  (∀ hπV : algebraMap ↥k₀ ↥K₀ π₀ ∈ V, (⟨_, hπV⟩ : ↥V) ∈ maximalIdeal ↥V) →
                  ∀ (hjK' : (coeffEmb ↥k₀ jq) ∈ Kℓ) (hjF : (⟨(coeffEmb ↥k₀ jq), hjK'⟩ : ↥Kℓ) ∈ K₀) (hjV : (⟨_, hjF⟩ : ↥K₀) ∈ V),
                    (∀ p : Polynomial ↥k₀, p.Monic → (∀ i : ℕ, ((p.coeff i : ↥k₀) : (AlgebraicClosure ℚ)) ∈ A) →
                      ∀ hp : Polynomial.aeval (⟨_, hjF⟩ : ↥K₀) (p.map (algebraMap ↥k₀ ↥K₀)) ∈ V,
                        (⟨_, hp⟩ : ↥V) ∉ maximalIdeal ↥V) →
                  (∃ f : ↥K₀, f ∈ O ∧ f ∉ V) → b ∉ V)))))) →

    (

        (∃

           (hjR : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
              ↥(modularFunctionFieldBar M')) ∈ R₀.integers)
           (_ : (R₀.residue ⟨_, hjR⟩ : modularFunctionFieldC (ResidueField A) M') ∈
              (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring)
           (hJK : ModularCurve.jqNModC (AlgebraicClosure ℚ) q ∈ fieldBar q M')
           (a₀ : ↥k₀) (ha₀ : (a₀ : (AlgebraicClosure ℚ)) ∈ A)
           (_ : (residue A ⟨(a₀ : (AlgebraicClosure ℚ)), ha₀⟩) ^ q =
              (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hjR⟩))
           (nodes : Finset (Subring ↥F₀)),
          nodes.card = q + 1 ∧

          (∃ Bc : Subring ↥F₀,
            (∃ T : Finset ↥F₀, Bc = Subring.closure
              ({f : ↥F₀ | ∃ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ∧ f = algebraMap ↥k₀ ↥F₀ x} ∪ (↑T : Set ↥F₀))) ∧
            ∀ O ∈ nodes, (∀ f : ↥F₀, f ∈ Bc → f ∈ O) ∧
              (∀ f : ↥F₀, f ∈ O ↔ ∃ g h : ↥F₀, g ∈ Bc ∧ h ∈ Bc ∧ (∀ hh : h ∈ O, IsUnit (⟨h, hh⟩ : ↥O)) ∧ f * h = g)) ∧

          (∀ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → ∀ O ∈ nodes, ∃ O' ∈ nodes,
            ∀ (f : ↥(fieldBar q M')) (hf : f ∈ F₀) (hf' : levelAutBar q M' ζ γ f ∈ F₀), (⟨f, hf⟩ : ↥F₀) ∈ O ↔ (⟨_, hf'⟩ : ↥F₀) ∈ O') ∧
          (∀ (ζ : Idx q), ∀ O ∈ nodes, ∀ O' ∈ nodes, ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧
            ∀ (f : ↥(fieldBar q M')) (hf : f ∈ F₀) (hf' : levelAutBar q M' ζ γ f ∈ F₀), (⟨f, hf⟩ : ↥F₀) ∈ O ↔ (⟨_, hf'⟩ : ↥F₀) ∈ O') ∧

          (∀ O ∈ nodes, ∀ O' ∈ nodes, O ≠ O' → ∃ (f : ↥F₀) (hf : f ∈ O) (hf' : f ∈ O'),
            ¬ IsUnit (⟨f, hf⟩ : ↥O) ∧ IsUnit (⟨f, hf'⟩ : ↥O')) ∧

          (∀ V : ValuationSubring ↥F₀, (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥F₀ x ∈ V) →
                  (∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
              (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
              (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
                0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
                  coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                  ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
                0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) :
                  ↥(modularFunctionFieldBar M'))) →
              (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') ∈
                  (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
                ∃ hF : (IntermediateField.inclusion hle ⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(fieldBar q M')) ∈ F₀,
                  (⟨_, hF⟩ : ↥F₀) ∈ V ∧
                  ∀ (c : ↥k₀) (hc : (c : (AlgebraicClosure ℚ)) ∈ A),
                    residue A ⟨(c : (AlgebraicClosure ℚ)), hc⟩ =
                      (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩) →
                    ∃ hm : (⟨_, hF⟩ : ↥F₀) - algebraMap ↥k₀ ↥F₀ c ∈ V, (⟨_, hm⟩ : ↥V) ∈ maximalIdeal ↥V) →
            (∀ f : ↥(fieldBar q M'), f ∈ B → ∃ hf : f ∈ F₀, (⟨f, hf⟩ : ↥F₀) ∈ V) ∨
            (∃ O ∈ nodes, ∀ (f : ↥F₀) (hfO : f ∈ O), f ∈ V ∧ (¬ IsUnit (⟨f, hfO⟩ : ↥O) → ∀ hfV : f ∈ V, (⟨f, hfV⟩ : ↥V) ∈ maximalIdeal ↥V))) ∧

          (∀ O ∈ nodes,

            (∀ f : ↥F₀, f ∈ O → f ∈ W₀) ∧ ∃ (_ : IsLocalRing ↥O) (_ : IsNoetherianRing ↥O),
            (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥F₀ x ∈ O) ∧
            (∀ (f : ↥F₀) (hf : f ∈ O), ∃ (x : ↥k₀) (hx : algebraMap ↥k₀ ↥F₀ x ∈ O), (x : (AlgebraicClosure ℚ)) ∈ A ∧
              ¬ IsUnit ((⟨f, hf⟩ : ↥O) - ⟨_, hx⟩)) ∧

            (∃ (E₀ : ℕ) (_ : 1 ≤ E₀)

               (_ : ∃ v : ↥k₀, (v : (AlgebraicClosure ℚ)) ∈ A ∧ ((v⁻¹ : ↥k₀) : (AlgebraicClosure ℚ)) ∈ A ∧
                  π₀ ^ E₀ = ϖt ^ (placeWidthChar q M' (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M'))) * v)
               (hπO : algebraMap ↥k₀ ↥F₀ π₀ ∈ O) (cx cy : ↥O) (u : (↥O)ˣ)
               (ι : (AdicCompletion (maximalIdeal ↥O) ↥O) ≃+* UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀))
               (γU γV : (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀))ˣ),
              cx * cy = (⟨_, hπO⟩ : ↥O) ^ E₀ * (u : ↥O) ∧
              (∀ (x : ↥k₀) (hx : (x : (AlgebraicClosure ℚ)) ∈ A) (hxO : algebraMap ↥k₀ ↥F₀ x ∈ O),
                ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨_, hxO⟩) =
                  UVCrossingModel.const ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀) (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨x, hx⟩)) ∧
              ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) cx) = (γU : UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀)) * UVCrossingModel.U ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀) ∧
              ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) cy) = (γV : UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀)) * UVCrossingModel.V ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀) ∧
              ((cy : ↥F₀) ∈ W₀) ∧ (∀ hcy : (cy : ↥F₀) ∈ W₀, (⟨(cy : ↥F₀), hcy⟩ : ↥W₀) ∈ maximalIdeal ↥W₀) ∧
              (∀ hcx : (cx : ↥F₀) ∈ W₀, (⟨(cx : ↥F₀), hcx⟩ : ↥W₀) ∉ maximalIdeal ↥W₀) ∧

              (∃ (hjF : (⟨ModularCurve.jqNModC (AlgebraicClosure ℚ) q, hJK⟩ : ↥(fieldBar q M')) -
                    algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a₀ : (AlgebraicClosure ℚ)) ∈ F₀)
                 (hjO : (⟨_, hjF⟩ : ↥F₀) ∈ O) (e : ℕ) (wV : (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀))ˣ), 1 ≤ e ∧
                ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨_, hjO⟩) =
                  (wV : UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀)) * (UVCrossingModel.V ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀)) ^ e) ∧

              (∃ Wx : ValuationSubring ↥F₀,
                (∀ f : ↥F₀, f ∈ O → f ∈ Wx) ∧
                (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥F₀ x ∈ Wx) ∧
                IsDiscreteValuationRing ↥Wx ∧
                (∃ hπW : algebraMap ↥k₀ ↥F₀ π₀ ∈ Wx, maximalIdeal ↥Wx = Ideal.span {(⟨_, hπW⟩ : ↥Wx)}) ∧
                (∃ t : ↥Wx, ∀ p : Polynomial ↥k₀, (∀ n, ((p.coeff n : ↥k₀) : (AlgebraicClosure ℚ)) ∈ A) →
                  (∃ hm : Polynomial.aeval (t : ↥F₀) p ∈ Wx, (⟨_, hm⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) →
                    ∀ n, ∃ hc : algebraMap ↥k₀ ↥F₀ (p.coeff n) ∈ Wx, (⟨_, hc⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) ∧
                (∀ hcx : (cx : ↥F₀) ∈ Wx, (⟨(cx : ↥F₀), hcx⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) ∧
                (∀ hcy : (cy : ↥F₀) ∈ Wx, (⟨(cy : ↥F₀), hcy⟩ : ↥Wx) ∉ maximalIdeal ↥Wx) ∧
                (∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
                  (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
                  (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
                    0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
                      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                      ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
                    0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) :
                      ↥(modularFunctionFieldBar M'))) →
                  ∃ hF : (IntermediateField.inclusion hle ⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(fieldBar q M')) ∈ F₀,
                    (⟨_, hF⟩ : ↥F₀) ∈ Wx ∧
                    (∀ hW : (⟨_, hF⟩ : ↥F₀) ∈ Wx, (⟨_, hW⟩ : ↥Wx) ∈ maximalIdeal ↥Wx ↔
                      (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') = 0) ∧
                    ((R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') ∈
                        (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
                      (⟨_, hF⟩ : ↥F₀) ∈ O ∧
                      ∀ (hO : (⟨_, hF⟩ : ↥F₀) ∈ O) (c : ↥k₀) (hc : (c : (AlgebraicClosure ℚ)) ∈ A) (hcO : algebraMap ↥k₀ ↥F₀ c ∈ O),
                        residue A ⟨(c : (AlgebraicClosure ℚ)), hc⟩ =
                          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩) →
                        ¬ IsUnit ((⟨_, hO⟩ : ↥O) - ⟨_, hcO⟩))) ∧

                (∀ O' ∈ nodes, O' ≠ O → ∃ f : ↥F₀, f ∈ O' ∧ f ∉ Wx)) ∧

              (∃ Bx : Subring ↥F₀,
                (∀ f : ↥F₀, f ∈ Bx → (f : ↥(fieldBar q M')) ∈ B ∧ f ∈ O) ∧
                (∀ (f : ↥F₀), f ∈ Bx → ∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'),
                  0 ≤ P.ord ((IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
                    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                    ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M'))) → 0 ≤ P.ord (f : ↥(fieldBar q M'))) ∧
                (∀ f : ↥F₀, f ∈ O ↔ ∃ g h : ↥F₀, g ∈ Bx ∧ h ∈ Bx ∧ (∀ hh : h ∈ O, IsUnit (⟨h, hh⟩ : ↥O)) ∧ f * h = g) ∧
                (∀ f : ↥F₀, ∃ g h : ↥F₀, g ∈ Bx ∧ h ∈ Bx ∧ h ≠ 0 ∧ f * h = g) ∧
                (∃ T : Finset ↥F₀, Bx = Subring.closure
                  ({f : ↥F₀ | ∃ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ∧ f = algebraMap ↥k₀ ↥F₀ x} ∪ (↑T : Set ↥F₀))) ∧

                (∃ b : ↥F₀, b ∈ Bx ∧ ∀ V : ValuationSubring ↥F₀,
                  (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥F₀ x ∈ V) →
                  (∀ hπV : algebraMap ↥k₀ ↥F₀ π₀ ∈ V, (⟨_, hπV⟩ : ↥V) ∈ maximalIdeal ↥V) →
                  ∀ (hjF : (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
                    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                    ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) ∈ F₀)
                    (hjV : (⟨(IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
                    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                    ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')), hjF⟩ : ↥F₀) ∈ V),
                    (∀ p : Polynomial ↥k₀, p.Monic → (∀ i : ℕ, ((p.coeff i : ↥k₀) : (AlgebraicClosure ℚ)) ∈ A) →
                      ∀ hp : Polynomial.aeval (⟨(IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
                    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                    ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')), hjF⟩ : ↥F₀) (p.map (algebraMap ↥k₀ ↥F₀)) ∈ V,
                        (⟨_, hp⟩ : ↥V) ∉ maximalIdeal ↥V) →
                  (∃ f : ↥F₀, f ∈ O ∧ f ∉ V) → b ∉ V)))))) := by
  intro F₀ hCHAR φ hφ1 hφ4 hφ5 W₀ hW₀ B hB hN'
  letI : Algebra ↥k₀ ↥(fieldBar q M') :=
    ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
  classical

  have hgKall : ∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M'), (coeffEmb ↥k₀ g) ∈ Kℓ := by
    intro g hg
    have h0 := ModularCurve.qExpand_coeffEmb_mem_laurentBaseChange_xHFunctionField_of_mem_modularFunctionFieldFull ↥k₀ M' 1 (q ^ 2 * M')
        ⟨q ^ 2, by ring⟩ H₁ g hg
    rw [ModularCurve.qExpand_one_apply] at h0
    rw [hKℓ]; exact h0
  have hq0 : 0 < q := (Fact.out : q.Prime).pos
  haveI : NeZero q := ⟨hq0.ne'⟩
  haveI : Fact ℓg.Prime := ⟨hℓg⟩
  have hι' := S3GlueKit.exists_emb k₀ q ξ hξ
  haveI hGfin : Finite ↥G := (ModularCurve.FullLevel.AuxLevelOne.finite_and_natCard_dvd_of_eq_closure_isLevelAutAt_gamma_of_dvd q M' hqM'
    ℓg hℓg12 hℓgM' ↥k₀ ξ hξ hι' H₁ hH₁ Kℓ hKℓ G hG).1
  have hcoef : ∀ (x : LaurentSeries ℚ) (n : ℤ), (coeffEmb (AlgebraicClosure ℚ) x).coeff n =
      ((algebraMap ℚ ↥k₀ (x.coeff n) : ↥k₀) : AlgebraicClosure ℚ) := by
    intro x n
    rw [coeffEmb_coeff]
    exact congrArg (fun f : ℚ →+* AlgebraicClosure ℚ => f (x.coeff n))
      (RingHom.ext_rat (algebraMap ℚ (AlgebraicClosure ℚ)) ((algebraMap ↥k₀ (AlgebraicClosure ℚ)).comp (algebraMap ℚ ↥k₀)))
  have hintF : Algebra.IsIntegral ↥F₀ ↥(fieldBar q M') :=
    S3GlueKit.isIntegral_laurentBaseChange_of_coeffEmb_mem (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))
      ↥k₀ F₀ (fun x hx => (hCHAR _).mpr (fun n => ⟨algebraMap ℚ ↥k₀ (x.coeff n), hcoef x n⟩))
  have hvF₀ : ∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M'),
      (IntermediateField.inclusion hle ⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(fieldBar q M')) ∈ F₀ :=
    fun g hg => (hCHAR _).mpr (fun n => ⟨algebraMap ℚ ↥k₀ (g.coeff n), hcoef g n⟩)
  have hK₀mem : ∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M'),
      (⟨(coeffEmb ↥k₀ g), hgKall g hg⟩ : ↥Kℓ) ∈ K₀ :=
    fun g hg => S3GlueKit.coeffEmb_mem_of_coeffLaw k₀ Kℓ K₀ (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))
      F₀ φ hφ1 g _ rfl (hvF₀ g hg) (hgKall g hg)

  have hJmem : ModularCurve.jqNModC (AlgebraicClosure ℚ) q ∈ fieldBar q M' := ModularCurve.FullLevel.jqNModC_mem_fieldBar q M' hqM'
  have hjOfval : ∀ (hK₀ : (⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ : ↥Kℓ) ∈ K₀),
      (((φ ⟨_, hK₀⟩ : ↥F₀) : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.jqNModC (AlgebraicClosure ℚ) q := by
    intro hK₀
    rw [← hφ1 ⟨_, hK₀⟩]
    show coeffMap (algebraMap ↥k₀ (AlgebraicClosure ℚ)) (ModularCurve.jqNModC ↥k₀ q) = _
    have h1 : coeffMap (algebraMap ↥k₀ (AlgebraicClosure ℚ)) (ModularCurve.jqModC ↥k₀) = ModularCurve.jqModC (AlgebraicClosure ℚ) :=
      ModularCurve.map_jqModC (algebraMap ↥k₀ (AlgebraicClosure ℚ))
    unfold ModularCurve.jqNModC
    rw [ModularCurve.coeffMap_qExpand, h1]
  have ha₀K : algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ a₀ = algebraMap ↥k₀ ↥Kℓ (a₀ : ↥k₀) :=
    IsScalarTower.algebraMap_apply ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥Kℓ a₀
  have ht : ∀ h₀ : ((⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ : ↥Kℓ) - algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ a₀) ∈ K₀,
      ((φ ⟨_, h₀⟩ : ↥F₀) : ↥(fieldBar q M')) =
        (⟨ModularCurve.jqNModC (AlgebraicClosure ℚ) q, hJmem⟩ : ↥(fieldBar q M')) -
          algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a₀ : ↥k₀) : (AlgebraicClosure ℚ)) := by
    intro h₀
    have hK₀' : (⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ : ↥Kℓ) ∈ K₀ := by
      have h1 := K₀.add_mem h₀ (IntermediateField.algebraMap_mem K₀ (a₀ : ↥k₀))
      rwa [ha₀K, sub_add_cancel] at h1
    have hx : (⟨_, h₀⟩ : ↥K₀) = ⟨_, hK₀'⟩ - algebraMap ↥k₀ ↥K₀ (a₀ : ↥k₀) := by
      apply Subtype.ext
      show (⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ : ↥Kℓ) - algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ a₀ = _
      rw [ha₀K]; rfl
    rw [hx, map_sub, AlgEquiv.commutes]
    show ((φ ⟨_, hK₀'⟩ : ↥F₀) : ↥(fieldBar q M')) - ((algebraMap ↥k₀ ↥F₀ (a₀ : ↥k₀) : ↥F₀) : ↥(fieldBar q M')) = _
    congr 1
    exact Subtype.ext (hjOfval hK₀')
  exact S3GlueKit.N_transport3 (k := ↥k₀) (L := LaurentSeries ↥k₀) (F := ↥(fieldBar q M')) Kℓ K₀ F₀ φ W₀'
    (fun c : ↥k₀ => (c : (AlgebraicClosure ℚ)) ∈ A) π₀ (q + 1)
    (fun E₀ : ℕ => ∃ v : ↥k₀, (v : (AlgebraicClosure ℚ)) ∈ A ∧ ((v⁻¹ : ↥k₀) : (AlgebraicClosure ℚ)) ∈ A ∧
      π₀ ^ E₀ = ϖt ^ (placeWidthChar q M' (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M'))) * v)
    (fun E₀ : ℕ => UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀))
    (fun (E₀ : ℕ) (x : ↥k₀) (hx : (x : (AlgebraicClosure ℚ)) ∈ A) => UVCrossingModel.const ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀) (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨x, hx⟩))
    (fun (E₀ : ℕ) (γU : (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀))ˣ) => (γU : UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀)) * UVCrossingModel.U ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀))
    (fun (E₀ : ℕ) (γV : (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀))ˣ) => (γV : UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀)) * UVCrossingModel.V ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀))
    (CongruenceSubgroup.Gamma0 M')
    (fun (γ : SL(2, ℤ)) (τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ) => ModularCurve.FullLevel.IsLevelAutAt ↥k₀ q ξ q (q ^ 2 * M') H₁ γ⁻¹ Kℓ τ)
    (fun (ζ : Idx q) (γ : SL(2, ℤ)) (y : ↥(fieldBar q M')) => levelAutBar q M' ζ γ y)
    (LaurentSeries ℚ) (fun g : LaurentSeries ℚ => g ∈ modularFunctionFieldFull M')
    (fun (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M') =>
      (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers)
    (fun (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
        (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers) =>
      ∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) :
          ↥(modularFunctionFieldBar M')))
    (fun (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
        (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers) =>
      (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') ∈
        (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring)
    (fun (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
        (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers) =>
      (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') = 0)
    (fun (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
        (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers)
        (c : ↥k₀) (hc : (c : (AlgebraicClosure ℚ)) ∈ A) =>
      residue A ⟨(c : (AlgebraicClosure ℚ)), hc⟩ =
        (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩))
    (fun g : LaurentSeries ℚ => (coeffEmb ↥k₀ g))
    (fun (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M') =>
      IntermediateField.inclusion hle ⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩)
    ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) B₀ B hB
    (fun y : ↥Kℓ => ∀ P : Place ↥k₀ ↥Kℓ, 0 ≤ P.ord (jℓ : ↥Kℓ) → 0 ≤ P.ord y)
    (fun y : ↥(fieldBar q M') => ∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'),
      0 ≤ P.ord ((IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
        ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M'))) → 0 ≤ P.ord y)
    (fun ζ γ hγ => S3GlueKit.dict_fwd q M' hqM' ℓg hℓgM' k₀ ξ hξ H₁ hH₁ Kℓ hKℓ K₀ F₀ φ hφ4 ζ γ hγ)
    (fun ζ γ hγ τ hτ => S3GlueKit.dict_bwd q M' hqM' ℓg hℓgM' k₀ ξ hξ H₁ hH₁ Kℓ hKℓ K₀ F₀ φ hφ4 ζ γ hγ τ hτ)
    hgKall hK₀mem (fun g hg hgK hF => hφ5 g hg hgK hF)
    (fun Bx₀ hBx₀ => S3GlueKit.reg_transport k₀ Kℓ ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) jℓ hjℓ G K₀ hK₀
      (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) (fun _ => rfl) F₀ hintF φ hφ1
      (IntermediateField.inclusion hle ⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩) rfl (hvF₀ jq (modularFunctionField_le_full M' (jq_mem M'))) Bx₀ hBx₀)
    ((⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
      ↥(modularFunctionFieldBar M')) ∈ R₀.integers)
    (fun hjR => (R₀.residue ⟨_, hjR⟩ : modularFunctionFieldC (ResidueField A) M') ∈
      (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring)
    (ModularCurve.jqNModC (AlgebraicClosure ℚ) q ∈ fieldBar q M') hJmem
    (a₀ : ↥k₀) a₀.2
    (fun hjR (c : ↥k₀) (hc : (c : (AlgebraicClosure ℚ)) ∈ A) =>
      (residue A ⟨(c : (AlgebraicClosure ℚ)), hc⟩) ^ q =
        (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hjR⟩))
    ((⟨ModularCurve.jqNModC ↥k₀ q, hjK⟩ : ↥Kℓ) - algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥Kℓ a₀)
    (fun (hJK : ModularCurve.jqNModC (AlgebraicClosure ℚ) q ∈ fieldBar q M') (c : ↥k₀) =>
      ((⟨ModularCurve.jqNModC (AlgebraicClosure ℚ) q, hJK⟩ : ↥(fieldBar q M')) -
        algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c : (AlgebraicClosure ℚ)) : ↥(fieldBar q M')))
    ht
    (fun E₀ : ℕ => UVCrossingModel.V ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀))
    ((coeffEmb ↥k₀ jq))
    (IntermediateField.inclusion hle ⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩)
    (hgKall jq (modularFunctionField_le_full M' (jq_mem M'))) (hK₀mem jq (modularFunctionField_le_full M' (jq_mem M')))
    (hφ5 jq (modularFunctionField_le_full M' (jq_mem M')) _ _)
    W₀ hW₀ hN'

end S_ModularCurve_FullLevel_Diamond_exists_moduliHasse_commonChart_nodes_igusaSep_levelField_of_nodes_fixedField_of_algEquiv_of_eq_two_of_dvd
end P2MW
export P2MW.S_ModularCurve_FullLevel_Diamond_exists_moduliHasse_commonChart_nodes_igusaSep_levelField_of_nodes_fixedField_of_algEquiv_of_eq_two_of_dvd (solution)
