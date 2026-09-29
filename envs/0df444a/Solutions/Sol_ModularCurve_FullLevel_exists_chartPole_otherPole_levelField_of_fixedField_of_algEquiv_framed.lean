-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_chartPole_otherPole_levelField_of_fixedField_of_algEquiv_framed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/23ebf265-cf99-5094-80c2-512108fef42a

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
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_RigidDescentHyps
import Mathlib
import Definitions.Def_AdicCompletionRingFunctoriality
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_ModularCurve_qExpand_coeffEmb_mem_laurentBaseChange_xHFunctionField_of_mem_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0_of_exists_ringHom
import Theorems.Thm_ModularCurve_FullLevel_exists_isLevelAutAt_conj_of_isLevelAutAt_of_isPrimitiveRoot
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_finite_and_natCard_dvd_of_eq_closure_isLevelAutAt_gamma
import Theorems.Thm_AlgebraicCurve_Place_exists_restrictAlong_eq_of_finiteDimensional_fieldRange
import Theorems.Thm_ModularCurve_mem_chartAlgFin_and_forall_mem_chartAlgInf_exists_mul_mem_of_coe_eq_coeffEmb_jq_qExpand_of_one_lt
import Theorems.Thm_ModularCurve_coeffEmb_qExpand
import Theorems.Thm_ModularCurve_coeffMap_injective
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Theorems.Thm_ModularCurve_FullLevel_jqNModC_mem_fieldBar
import Theorems.Thm_ModularCurve_coeffEmb_jq_ne_zero
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_chartPole_otherPole_levelField_of_fixedField_of_algEquiv_framed
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 3200000
set_option maxHeartbeats 0

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

theorem imSEquiv_symm_coe (e : K ≃+* L) (O : Subring K) (y : imS e O) :
    (((imSEquiv e O).symm y : O) : K) = e.symm y := by
  have h : imSEquiv e O ((imSEquiv e O).symm y) = y := (imSEquiv e O).apply_symm_apply y
  have h2 : e (((imSEquiv e O).symm y : O) : K) = (y : L) := by
    rw [← coe_imSEquiv e O, h]
  rw [← h2, e.symm_apply_apply]

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
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_chartPole_otherPole_levelField_of_fixedField_of_algEquiv_framed.S3GlueKit"

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

theorem exists_subring_image {R S : Type*} [Ring R] [Ring S] (s : Subring R) (f : R →+* S) :
    ∃ B : Subring S, ∀ y : S, y ∈ B ↔ ∃ x : R, x ∈ s ∧ y = f x :=
  ⟨s.map f, fun y => by
    rw [Subring.mem_map]
    exact ⟨fun ⟨x, hx, h⟩ => ⟨x, hx, h.symm⟩, fun ⟨x, hx, h⟩ => ⟨x, hx, h.symm⟩⟩⟩

theorem exists_namingBlock {k E : Type*} [Field k] [Field E] [Algebra k E]
    (O : Type*) [CommRing O] [Algebra O E] [Algebra O k] [IsScalarTower O k E]
    (S : Set (E ≃ₐ[k] E)) (Bt : Subalgebra O E) (Wt : ValuationSubring E) :
    ∃ (G : Subgroup (E ≃ₐ[k] E)) (K₀ : IntermediateField k E) (B₀ : Subalgebra O E) (W₀' : ValuationSubring K₀),
      G = Subgroup.closure S ∧ K₀ = IntermediateField.fixedField G ∧
      (∀ f : E, f ∈ B₀ ↔ f ∈ Bt ∧ ∀ τ : E ≃ₐ[k] E, τ ∈ G → τ f = f) ∧
      (∀ f : K₀, f ∈ W₀' ↔ ((f : E)) ∈ Wt) := by
  refine ⟨Subgroup.closure S, IntermediateField.fixedField (Subgroup.closure S),
    { carrier := {f : E | f ∈ Bt ∧ ∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.closure S → τ f = f}
      mul_mem' := ?_, one_mem' := ?_, add_mem' := ?_, zero_mem' := ?_, algebraMap_mem' := ?_ },
    Wt.comap (algebraMap _ E), rfl, rfl, fun f => Iff.rfl, fun f => Iff.rfl⟩
  · rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨Bt.mul_mem ha hb, fun τ hτ => by rw [map_mul, ha' τ hτ, hb' τ hτ]⟩
  · exact ⟨Bt.one_mem, fun τ _ => map_one τ⟩
  · rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨Bt.add_mem ha hb, fun τ hτ => by rw [map_add, ha' τ hτ, hb' τ hτ]⟩
  · exact ⟨Bt.zero_mem, fun τ _ => map_zero τ⟩
  · intro a
    exact ⟨Bt.algebraMap_mem a, fun τ _ => by rw [IsScalarTower.algebraMap_apply O k E]; exact τ.commutes _⟩

theorem exists_comap_valuationSubring {K L : Type*} [Field K] [Field L] (e : K ≃+* L) (V : ValuationSubring L) :
    ∃ W : ValuationSubring K, W = V.comap (e : K →+* L) ∧ ∀ f : K, f ∈ W ↔ e f ∈ V :=
  ⟨_, rfl, fun f => Iff.rfl⟩

theorem exists_algebra_of_ringHom {R S : Type*} [CommRing R] [CommRing S] (ψ : R →+* S) :
    ∃ alg : Algebra R S, ∀ a : R, @algebraMap R S _ _ alg a = ψ a :=
  ⟨ψ.toAlgebra, fun a => rfl⟩

theorem coe_comapEquiv_symm {K L : Type*} [Field K] [Field L] (e : K ≃+* L) (V : ValuationSubring L) (y : V) :
    (((comapEquiv e V).symm y : V.comap (e : K →+* L)) : K) = e.symm y := rfl

section algEquiv
variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

theorem algEquiv_symm_toRingEquiv_algebraMap (φ : A ≃ₐ[R] B) (x : R) :
    φ.symm.toRingEquiv (algebraMap R B x) = algebraMap R A x := φ.symm.commutes x

theorem algEquiv_symm_toRingEquiv_symm_algebraMap (φ : A ≃ₐ[R] B) (x : R) :
    φ.symm.toRingEquiv.symm (algebraMap R A x) = algebraMap R B x := φ.commutes x

theorem algEquiv_symm_toRingEquiv_apply_apply (φ : A ≃ₐ[R] B) (x : A) :
    φ.symm.toRingEquiv (φ x) = x := φ.symm_apply_apply x

theorem algEquiv_symm_toRingEquiv_symm_apply (φ : A ≃ₐ[R] B) (x : A) :
    φ.symm.toRingEquiv.symm x = φ x := rfl

end algEquiv
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_chartPole_otherPole_levelField_of_fixedField_of_algEquiv_framed.S3GlueKit"

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

theorem exists_ringHom_of_bot {k F : Type*} [Field k] [Field F] [Algebra k F]
    (Kb : IntermediateField k F) (hKb : Kb = ⊥)
    (A : ValuationSubring F) (Ab : ValuationSubring Kb) (hAb : ∀ x : Kb, x ∈ Ab ↔ (x : F) ∈ A) :
    ∃ ψ : Ab →+* A.comap (algebraMap k F), ∀ a : Ab, algebraMap k F ((ψ a : A.comap (algebraMap k F)) : k) = ((a : Kb) : F) := by
  subst hKb
  have hval : ∀ y : (⊥ : IntermediateField k F), algebraMap k F (IntermediateField.botEquiv k F y) = (y : F) := by
    intro y
    have h := (IntermediateField.botEquiv k F).symm_apply_apply y
    rw [IntermediateField.botEquiv_symm] at h
    exact congrArg (fun z : (⊥ : IntermediateField k F) => (z : F)) h
  let ψ₀ : Ab →+* k := (IntermediateField.botEquiv k F).toAlgHom.toRingHom.comp Ab.subtype
  have hψ₀ : ∀ a : Ab, algebraMap k F (ψ₀ a) = ((a : (⊥ : IntermediateField k F)) : F) := fun a => hval _
  refine ⟨ψ₀.codRestrict (A.comap (algebraMap k F)).toSubring (fun a => ?_), fun a => hψ₀ a⟩
  show algebraMap k F (ψ₀ a) ∈ A
  rw [hψ₀]; exact (hAb _).mp a.2

theorem exists_ringHom_to_image {R K S : Type*} [CommRing R] [Ring K] [Ring S]
    (g : R →+* K) (s : Subring K) (hg : ∀ r : R, g r ∈ s) (f : K →+* S)
    (B : Subring S) (hB : ∀ y : S, y ∈ B ↔ ∃ x : K, x ∈ s ∧ y = f x) :
    ∃ ψ : R →+* B, ∀ r : R, ((ψ r : B) : S) = f (g r) :=
  ⟨(f.comp g).codRestrict B (fun r => (hB _).mpr ⟨g r, hg r, rfl⟩), fun r => rfl⟩

theorem algebraMap_mem_invariants {k E : Type*} [Field k] [Field E] [Algebra k E]
    (O : Type*) [CommRing O] [Algebra O E] [Algebra O k] [IsScalarTower O k E]
    (G : Subgroup (E ≃ₐ[k] E)) (K₀ : IntermediateField k E) (Bt B₀ : Subalgebra O E)
    (hB₀ : ∀ f : E, f ∈ B₀ ↔ f ∈ Bt ∧ ∀ τ : E ≃ₐ[k] E, τ ∈ G → τ f = f) (a : O) :
    ((algebraMap k K₀).comp (algebraMap O k)) a ∈ B₀.toSubring.comap (algebraMap K₀ E) := by
  rw [Subring.mem_comap, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply k K₀ E,
    ← IsScalarTower.algebraMap_apply O k E]
  exact (hB₀ _).mpr ⟨Bt.algebraMap_mem a, fun τ _ => by rw [IsScalarTower.algebraMap_apply O k E]; exact τ.commutes _⟩

theorem constants_law {k L F E : Type*} [Field k] [Field L] [Field F] [Field E]
    [Algebra k L] [Algebra L F] [Algebra k F] [Algebra k E]
    (hkF : ∀ x : k, algebraMap k F x = algebraMap L F (algebraMap k L x))
    (A : ValuationSubring L)
    (K₀ : IntermediateField k E) (F₀ : IntermediateField k F) (φ : K₀ ≃ₐ[k] F₀)
    (Ab : Type*) [CommRing Ab] (coeAb : Ab → L)
    (ψ₁ : Ab →+* A.comap (algebraMap k L))
    (hψ₁ : ∀ a : Ab, algebraMap k L ((ψ₁ a : A.comap (algebraMap k L)) : k) = coeAb a)
    (B : Subring F) (ψ : A.comap (algebraMap k L) →+* B)
    (hψ : ∀ r, ((ψ r : B) : F) = ((algebraMap F₀ F).comp φ.toAlgHom.toRingHom)
      (((algebraMap k K₀).comp (algebraMap (A.comap (algebraMap k L)) k)) r))
    (alg : Algebra Ab B) (halg : ∀ a : Ab, @algebraMap Ab B _ _ alg a = (ψ.comp ψ₁) a) (a : Ab) :
    ((@algebraMap Ab B _ _ alg a : B) : F) = algebraMap L F (coeAb a) := by
  rw [halg, RingHom.comp_apply, hψ, RingHom.comp_apply, RingHom.comp_apply, ← hψ₁, ← hkF]
  show ((φ (algebraMap k K₀ _) : F₀) : F) = _
  rw [AlgEquiv.commutes, IsScalarTower.algebraMap_apply k F₀ F]
  rfl

theorem constants_mem_transport {k E F : Type*} [Field k] [Field E] [Field F] [Algebra k E] [Algebra k F]
    (K₀ : IntermediateField k E) (F₀ : IntermediateField k F) (φ : K₀ ≃ₐ[k] F₀)
    (W₀' : ValuationSubring K₀) (W₀ : ValuationSubring F₀)
    (memW₀ : ∀ f : F₀, f ∈ W₀ ↔ φ.symm.toRingEquiv f ∈ W₀')
    (P : k → Prop) (hK2a' : ∀ x : k, P x ↔ algebraMap k K₀ x ∈ W₀') (x : k) :
    P x ↔ algebraMap k F₀ x ∈ W₀ := by
  rw [hK2a', memW₀, algEquiv_symm_toRingEquiv_algebraMap]

theorem isDiscreteValuationRing_transport {K L : Type*} [Field K] [Field L] (e : K ≃+* L)
    (V : ValuationSubring L) (W : ValuationSubring K) (hW : W = V.comap (e : K →+* L))
    (hV : IsDiscreteValuationRing V) : IsDiscreteValuationRing W := by
  subst hW; exact isDiscreteValuationRing_comap e V

theorem mem_of_mem_adjoin_bot_sup {k L F : Type*} [Field k] [Field L] [Field F]
    [Algebra k L] [Algebra L F] [Algebra k F]
    (hkF : ∀ x : k, algebraMap k F x = algebraMap L F (algebraMap k L x))
    (Kb : IntermediateField k L) (hKb : Kb = ⊥) (F₀ : IntermediateField k F) (f : F)
    (hf : f ∈ IntermediateField.adjoin k (⇑(algebraMap L F) '' (↑Kb : Set L)) ⊔ F₀) : f ∈ F₀ := by
  have hle : IntermediateField.adjoin k (⇑(algebraMap L F) '' (↑Kb : Set L)) ≤ F₀ := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, hy, rfl⟩
    subst hKb
    rw [SetLike.mem_coe, IntermediateField.mem_bot] at hy
    obtain ⟨x, rfl⟩ := hy
    rw [← hkF]
    exact F₀.algebraMap_mem x
  exact (sup_le hle le_rfl) hf

theorem frac_transport {k E F : Type*} [Field k] [Field E] [Field F] [Algebra k E] [Algebra k F]
    (O : Type*) [CommRing O] [Algebra O E]
    (K₀ : IntermediateField k E) (F₀ : IntermediateField k F) (φ : K₀ ≃ₐ[k] F₀) (B₀ : Subalgebra O E)
    (hM0b' : ∀ f : E, f ∈ K₀ → ∃ g h : B₀, (h : E) ≠ 0 ∧ f * (h : E) = (g : E))
    (B : Subring F)
    (hB : ∀ y : F, y ∈ B ↔ ∃ x : K₀, x ∈ B₀.toSubring.comap (algebraMap K₀ E) ∧
      y = ((algebraMap F₀ F).comp φ.toAlgHom.toRingHom) x)
    (hM0a' : ∀ f : E, f ∈ B₀ → f ∈ K₀)
    (f : F) (hf : f ∈ F₀) : ∃ g h : B, (h : F) ≠ 0 ∧ f * (h : F) = (g : F) := by
  obtain ⟨g, h, hh0, hgh⟩ := hM0b' ((φ.symm ⟨f, hf⟩ : K₀) : E) (φ.symm ⟨f, hf⟩).2
  have hgK : (g : E) ∈ K₀ := hM0a' _ g.2
  have hhK : (h : E) ∈ K₀ := hM0a' _ h.2
  have hgB : ((φ ⟨(g : E), hgK⟩ : F₀) : F) ∈ B := (hB _).mpr ⟨⟨(g : E), hgK⟩, Subring.mem_comap.mpr g.2, rfl⟩
  have hhB : ((φ ⟨(h : E), hhK⟩ : F₀) : F) ∈ B := (hB _).mpr ⟨⟨(h : E), hhK⟩, Subring.mem_comap.mpr h.2, rfl⟩
  refine ⟨⟨_, hgB⟩, ⟨_, hhB⟩, ?_, ?_⟩
  · intro h0
    apply hh0
    have h1 : (φ ⟨(h : E), hhK⟩ : F₀) = 0 := Subtype.ext h0
    have h2 : (⟨(h : E), hhK⟩ : K₀) = 0 := by simpa using congrArg φ.symm h1
    exact congrArg (fun z : K₀ => (z : E)) h2
  · have hprod : (φ.symm ⟨f, hf⟩ : K₀) * ⟨(h : E), hhK⟩ = ⟨(g : E), hgK⟩ := Subtype.ext hgh
    have h3 : (⟨f, hf⟩ : F₀) * φ ⟨(h : E), hhK⟩ = φ ⟨(g : E), hgK⟩ := by
      rw [← hprod, map_mul, AlgEquiv.apply_symm_apply]
    exact congrArg (fun z : F₀ => (z : F)) h3

theorem over_transport {k E F : Type*} [Field k] [Field E] [Field F] [Algebra k E] [Algebra k F]
    (K₀ : IntermediateField k E) (F₀ : IntermediateField k F) (φ : K₀ ≃ₐ[k] F₀)
    (W₀' : ValuationSubring K₀) (W₀ : ValuationSubring F₀)
    (hW₀ : W₀ = W₀'.comap (φ.symm.toRingEquiv : F₀ →+* K₀))
    (Q : k → Prop) (P : ∀ c : k, Q c → Prop)
    (u : E)
    (hu : ∃ hF : u ∈ K₀, (⟨u, hF⟩ : K₀) ∈ W₀' ∧
      ∀ (c : k) (hc : Q c), P c hc →
        ∃ hm : (⟨u, hF⟩ : K₀) - algebraMap k K₀ c ∈ W₀', (⟨_, hm⟩ : W₀') ∈ IsLocalRing.maximalIdeal W₀')
    (v : F) (hv : ∀ hF : u ∈ K₀, ((φ ⟨u, hF⟩ : F₀) : F) = v) :
    ∃ hF : v ∈ F₀, (⟨v, hF⟩ : F₀) ∈ W₀ ∧
      ∀ (c : k) (hc : Q c), P c hc →
        ∃ hm : (⟨v, hF⟩ : F₀) - algebraMap k F₀ c ∈ W₀, (⟨_, hm⟩ : W₀) ∈ IsLocalRing.maximalIdeal W₀ := by
  subst hW₀
  obtain ⟨hF', hW', hrest⟩ := hu
  have hvF : v ∈ F₀ := by rw [← hv hF']; exact (φ _).2
  have hxv : (⟨v, hvF⟩ : F₀) = φ ⟨u, hF'⟩ := Subtype.ext (hv hF').symm
  refine ⟨hvF, ?_, ?_⟩
  · show φ.symm.toRingEquiv ⟨v, hvF⟩ ∈ W₀'
    rw [hxv, algEquiv_symm_toRingEquiv_apply_apply]; exact hW'
  · intro c hc hP
    obtain ⟨hm', hmax'⟩ := hrest c hc hP
    have hy : φ.symm.toRingEquiv ((⟨v, hvF⟩ : F₀) - algebraMap k F₀ c) = ⟨u, hF'⟩ - algebraMap k K₀ c := by
      rw [map_sub, hxv, algEquiv_symm_toRingEquiv_apply_apply, algEquiv_symm_toRingEquiv_algebraMap]
    have hm : (⟨v, hvF⟩ : F₀) - algebraMap k F₀ c ∈ W₀'.comap (φ.symm.toRingEquiv : F₀ →+* K₀) := by
      show φ.symm.toRingEquiv _ ∈ W₀'; rw [hy]; exact hm'
    refine ⟨hm, ?_⟩
    rw [mem_maximalIdeal_comap_iff]
    have : comapEquiv φ.symm.toRingEquiv W₀' ⟨_, hm⟩ = ⟨_, hm'⟩ := Subtype.ext hy
    rw [this]; exact hmax'

theorem exists_ringEquiv_of_bot {k F : Type*} [Field k] [Field F] [Algebra k F]
    (Kb : IntermediateField k F) (hKb : Kb = ⊥)
    (A : ValuationSubring F) (Ab : ValuationSubring Kb) (hAb : ∀ x : Kb, x ∈ Ab ↔ (x : F) ∈ A) :
    ∃ ψ : Ab ≃+* A.comap (algebraMap k F), ∀ a : Ab, algebraMap k F ((ψ a : A.comap (algebraMap k F)) : k) = ((a : Kb) : F) := by
  subst hKb
  set e := IntermediateField.botEquiv k F
  have hval : ∀ y : (⊥ : IntermediateField k F), algebraMap k F (e y) = (y : F) := by
    intro y
    have h := e.symm_apply_apply y
    rw [IntermediateField.botEquiv_symm] at h
    exact congrArg (fun z : (⊥ : IntermediateField k F) => (z : F)) h
  have hval' : ∀ x : k, (e.symm x : F) = algebraMap k F x := by
    intro x; rw [IntermediateField.botEquiv_symm]; rfl
  refine ⟨{ toFun := fun a => ⟨e a, show algebraMap k F (e a) ∈ A by rw [hval]; exact (hAb _).mp a.2⟩
            invFun := fun x => ⟨e.symm (x : k), (hAb _).mpr (by rw [hval']; exact x.2)⟩
            left_inv := fun a => by ext; simp
            right_inv := fun x => by ext; simp
            map_mul' := fun a b => by ext; simp
            map_add' := fun a b => by ext; simp }, fun a => hval _⟩

theorem exists_ringEquiv_image {k E F : Type*} [Field k] [Field E] [Field F] [Algebra k E] [Algebra k F]
    (O : Type*) [CommRing O] [Algebra O E]
    (K₀ : IntermediateField k E) (F₀ : IntermediateField k F) (φ : K₀ ≃ₐ[k] F₀) (B₀ : Subalgebra O E)
    (hM0a' : ∀ f : E, f ∈ B₀ → f ∈ K₀)
    (B : Subring F)
    (hB : ∀ y : F, y ∈ B ↔ ∃ x : K₀, x ∈ B₀.toSubring.comap (algebraMap K₀ E) ∧
      y = ((algebraMap F₀ F).comp φ.toAlgHom.toRingHom) x) :
    ∃ eB : B₀ ≃+* B, ∀ b : B₀, ((eB b : B) : F) = ((φ ⟨(b : E), hM0a' _ b.2⟩ : F₀) : F) := by
  classical
  let f : B₀ → B := fun b => ⟨((φ ⟨(b : E), hM0a' _ b.2⟩ : F₀) : F),
    (hB _).mpr ⟨⟨(b : E), hM0a' _ b.2⟩, Subring.mem_comap.mpr b.2, rfl⟩⟩
  have hf : ∀ b, ((f b : B) : F) = ((φ ⟨(b : E), hM0a' _ b.2⟩ : F₀) : F) := fun b => rfl
  have hinj : Function.Injective f := by
    intro a b h
    have h1 : ((φ ⟨(a : E), hM0a' _ a.2⟩ : F₀) : F) = ((φ ⟨(b : E), hM0a' _ b.2⟩ : F₀) : F) := by
      rw [← hf, ← hf, h]
    have h2 := φ.injective (Subtype.ext h1)
    exact Subtype.ext (congrArg (fun z : K₀ => (z : E)) h2)
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, hx, hy⟩ := (hB _).mp y.2
    refine ⟨⟨(x : E), Subring.mem_comap.mp hx⟩, Subtype.ext ?_⟩
    rw [hf, hy]; rfl
  have hK₀mul : ∀ a b : B₀, (⟨((a * b : B₀) : E), hM0a' _ (a * b).2⟩ : K₀) =
      ⟨(a : E), hM0a' _ a.2⟩ * ⟨(b : E), hM0a' _ b.2⟩ := fun a b => Subtype.ext rfl
  have hK₀add : ∀ a b : B₀, (⟨((a + b : B₀) : E), hM0a' _ (a + b).2⟩ : K₀) =
      ⟨(a : E), hM0a' _ a.2⟩ + ⟨(b : E), hM0a' _ b.2⟩ := fun a b => Subtype.ext rfl
  have hmul : ∀ a b : B₀, f (a * b) = f a * f b := fun a b => Subtype.ext (by
    rw [Subring.coe_mul, hf, hf, hf, hK₀mul, map_mul]; rfl)
  have hadd : ∀ a b : B₀, f (a + b) = f a + f b := fun a b => Subtype.ext (by
    rw [Subring.coe_add, hf, hf, hf, hK₀add, map_add]; rfl)
  exact ⟨{ Equiv.ofBijective f ⟨hinj, hsurj⟩ with map_mul' := hmul, map_add' := hadd }, fun b => rfl⟩

section idealDict
variable {Ab Ak B₀ B : Type*} [CommRing Ab] [IsLocalRing Ab] [CommRing Ak] [IsDomain Ak] [IsLocalRing Ak]
  [CommRing B₀] [Algebra Ak B₀] [CommRing B]

theorem exists_unit_mul_eq (ψ : Ab ≃+* Ak) (ϖb : Ab) (hϖb : maximalIdeal Ab = Ideal.span {ϖb})
    (π : Ak) (hπ : maximalIdeal Ak = Ideal.span {π}) : ∃ u : Ak, IsUnit u ∧ ψ ϖb = u * π := by
  have h1 : maximalIdeal Ak = Ideal.span {ψ ϖb} := by
    ext x
    rw [mem_maximalIdeal, mem_nonunits_iff]
    constructor
    · intro hx
      have hx' : ψ.symm x ∈ maximalIdeal Ab := by
        rw [mem_maximalIdeal, mem_nonunits_iff]; intro hu; exact hx (by simpa using hu.map ψ.toRingHom)
      rw [hϖb, Ideal.mem_span_singleton] at hx'
      obtain ⟨c, hc⟩ := hx'
      rw [Ideal.mem_span_singleton]
      exact ⟨ψ c, by rw [← map_mul, ← hc, RingEquiv.apply_symm_apply]⟩
    · intro hx hu
      rw [Ideal.mem_span_singleton] at hx
      obtain ⟨c, rfl⟩ := hx
      have hϖu : IsUnit (ψ ϖb) := isUnit_of_mul_isUnit_left hu
      have : IsUnit ϖb := by simpa using hϖu.map ψ.symm.toRingHom
      have hmem : ϖb ∈ maximalIdeal Ab := by rw [hϖb]; exact Ideal.mem_span_singleton_self ϖb
      exact (mem_maximalIdeal _ |>.mp hmem) this
  rw [h1, Ideal.span_singleton_eq_span_singleton] at hπ
  obtain ⟨u, hu⟩ := hπ.symm
  exact ⟨u, u.isUnit, by rw [← hu, mul_comm]⟩

theorem prime_and_krullDimLE_transport (ψ : Ab ≃+* Ak) (ϖb : Ab) (hϖb : maximalIdeal Ab = Ideal.span {ϖb})
    (π : Ak) (hπ : maximalIdeal Ak = Ideal.span {π}) (eB : B₀ ≃+* B)
    (alg : Algebra Ab B) (halgB : ∀ a : Ab, @algebraMap Ab B _ _ alg a = eB (algebraMap Ak B₀ (ψ a))) :
    (Prime (algebraMap Ak B₀ π) → Prime (@algebraMap Ab B _ _ alg ϖb)) ∧
    (Ideal.span {@algebraMap Ab B _ _ alg ϖb} = (Ideal.span {algebraMap Ak B₀ π}).map eB.toRingHom) ∧
    (∀ n : ℕ, Ring.KrullDimLE n (B₀ ⧸ Ideal.span {algebraMap Ak B₀ π}) →
      Ring.KrullDimLE n (B ⧸ Ideal.span {@algebraMap Ab B _ _ alg ϖb})) := by
  obtain ⟨u, hu, hψ⟩ := exists_unit_mul_eq ψ ϖb hϖb π hπ
  have key : @algebraMap Ab B _ _ alg ϖb = eB (algebraMap Ak B₀ u) * eB (algebraMap Ak B₀ π) := by
    rw [halgB, hψ, map_mul, map_mul]
  have hunit : IsUnit (eB (algebraMap Ak B₀ u)) := (hu.map (algebraMap Ak B₀)).map eB
  have hideal : Ideal.span {@algebraMap Ab B _ _ alg ϖb} = (Ideal.span {algebraMap Ak B₀ π}).map eB.toRingHom := by
    rw [key, Ideal.span_singleton_mul_left_unit hunit, Ideal.map_span, Set.image_singleton]; rfl
  refine ⟨fun hp => ?_, hideal, fun n hn => ?_⟩
  · rw [key, ← (Associated.prime_iff ⟨hunit.unit, by rw [hunit.unit_spec, mul_comm]⟩)]
    exact (MulEquiv.prime_iff eB).mpr hp
  · have e : (B₀ ⧸ Ideal.span {algebraMap Ak B₀ π}) ≃+* (B ⧸ Ideal.span {@algebraMap Ab B _ _ alg ϖb}) :=
      Ideal.quotientEquiv _ _ eB hideal
    rw [Ring.krullDimLE_iff] at hn ⊢
    rw [← ringKrullDim_eq_of_ringEquiv e]; exact hn

end idealDict
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_chartPole_otherPole_levelField_of_fixedField_of_algEquiv_framed.S3GlueKit"

theorem algebraMap_eq_eB {k E F L : Type*} [Field k] [Field E] [Field F] [Field L] [Algebra k E] [Algebra k F] [Algebra k L]
    (A : ValuationSubring L) [Algebra (A.comap (algebraMap k L)) E]
    [IsScalarTower (A.comap (algebraMap k L)) k E]
    (K₀ : IntermediateField k E) (F₀ : IntermediateField k F) (φ : K₀ ≃ₐ[k] F₀)
    (B₀ : Subalgebra (A.comap (algebraMap k L)) E) (hM0a' : ∀ f : E, f ∈ B₀ → f ∈ K₀)
    (B : Subring F)
    (ψ : A.comap (algebraMap k L) →+* B)
    (hψ : ∀ r, ((ψ r : B) : F) = ((algebraMap F₀ F).comp φ.toAlgHom.toRingHom)
      (((algebraMap k K₀).comp (algebraMap (A.comap (algebraMap k L)) k)) r))
    (eB : B₀ ≃+* B) (heB : ∀ b : B₀, ((eB b : B) : F) = ((φ ⟨(b : E), hM0a' _ b.2⟩ : F₀) : F))
    (Ab : Type*) [CommRing Ab] (ψ₁ : Ab ≃+* A.comap (algebraMap k L))
    (alg : Algebra Ab B) (halg : ∀ a : Ab, @algebraMap Ab B _ _ alg a = (ψ.comp ψ₁.toRingHom) a) (a : Ab) :
    @algebraMap Ab B _ _ alg a = eB (algebraMap (A.comap (algebraMap k L)) B₀ (ψ₁ a)) := by
  rw [halg, RingHom.comp_apply]
  apply Subtype.ext
  rw [hψ, heB]
  show ((φ _ : F₀) : F) = ((φ _ : F₀) : F)
  congr 2
  apply Subtype.ext
  show ((algebraMap k K₀ _ : K₀) : E) = ((algebraMap (A.comap (algebraMap k L)) B₀ (ψ₁ a) : B₀) : E)
  rw [Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply (A.comap (algebraMap k L)) k E]
  rfl

section smoothTransfer
variable {Ab Ak B₀ B : Type*} [CommRing Ab] [CommRing Ak] [CommRing B₀] [Algebra Ak B₀] [CommRing B]

theorem formallySmooth_and_finitePresentation_transport (ψ : Ab ≃+* Ak) (eB : B₀ ≃+* B)
    (alg : Algebra Ab B) (halgB : ∀ a : Ab, @algebraMap Ab B _ _ alg a = eB (algebraMap Ak B₀ (ψ a))) :
    (Algebra.FormallySmooth Ak B₀ → @Algebra.FormallySmooth Ab B _ _ alg) ∧
    (Algebra.FinitePresentation Ak B₀ → @Algebra.FinitePresentation Ab B _ _ alg) := by

  letI algAk : Algebra Ab Ak := ψ.toRingHom.toAlgebra
  letI algB₀ : Algebra Ab B₀ := ((algebraMap Ak B₀).comp ψ.toRingHom).toAlgebra
  letI : Algebra Ab B := alg
  haveI : IsScalarTower Ab Ak B₀ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

  let eAk : Ab ≃ₐ[Ab] Ak := AlgEquiv.ofRingEquiv (f := ψ) (fun _ => rfl)
  haveI : Algebra.FormallySmooth Ab Ak := Algebra.FormallySmooth.of_equiv eAk
  haveI : Algebra.FinitePresentation Ab Ak := Algebra.FinitePresentation.equiv eAk

  let eB' : B₀ ≃ₐ[Ab] B := AlgEquiv.ofRingEquiv (f := eB) (fun a => by
    show eB (algebraMap Ak B₀ (ψ a)) = @algebraMap Ab B _ _ alg a
    rw [halgB])
  refine ⟨fun h => ?_, fun h => ?_⟩
  · haveI : Algebra.FormallySmooth Ab B₀ := Algebra.FormallySmooth.comp Ab Ak B₀
    exact Algebra.FormallySmooth.of_equiv eB'
  · haveI : Algebra.FinitePresentation Ab B₀ := Algebra.FinitePresentation.trans Ab Ak B₀
    exact Algebra.FinitePresentation.equiv eB'

end smoothTransfer
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_chartPole_otherPole_levelField_of_fixedField_of_algEquiv_framed.S3GlueKit"

theorem localisation_transport {k E F : Type*} [Field k] [Field E] [Field F] [Algebra k E] [Algebra k F]
    (O : Type*) [CommRing O] [Algebra O E]
    (K₀ : IntermediateField k E) (F₀ : IntermediateField k F) (φ : K₀ ≃ₐ[k] F₀) (B₀ : Subalgebra O E)
    (hM0a' : ∀ f : E, f ∈ B₀ → f ∈ K₀)
    (W₀' : ValuationSubring K₀) (W₀ : ValuationSubring F₀)
    (memW₀ : ∀ f : F₀, f ∈ W₀ ↔ φ.symm.toRingEquiv f ∈ W₀')
    (B : Subring F) (eB : B₀ ≃+* B) (heB : ∀ b : B₀, ((eB b : B) : F) = ((φ ⟨(b : E), hM0a' _ b.2⟩ : F₀) : F))
    (π₀ : B₀) (ϖ : B) (hdvd : ∀ h : B₀, π₀ ∣ h ↔ ϖ ∣ eB h)
    (hM2c' : ∀ f : K₀, f ∈ W₀' ↔ ∃ g h : B₀, ¬ (π₀ ∣ h) ∧ (f : E) * (h : E) = (g : E)) (f : F₀) :
    f ∈ W₀ ↔ ∃ g h : B, ¬ (ϖ ∣ h) ∧ (f : F) * (h : F) = (g : F) := by
  have key : ∀ (x : K₀) (g h : B₀), ((x : E) * (h : E) = (g : E)) ↔ ((φ x : F₀) : F) * ((eB h : B) : F) = ((eB g : B) : F) := by
    intro x g h
    rw [heB, heB, ← IntermediateField.coe_mul, ← map_mul]
    constructor
    · intro hx
      have : x * ⟨(h : E), hM0a' _ h.2⟩ = ⟨(g : E), hM0a' _ g.2⟩ := Subtype.ext hx
      rw [this]
    · intro hx
      have h1 := φ.injective (Subtype.ext hx : φ (x * ⟨(h : E), hM0a' _ h.2⟩) = φ ⟨(g : E), hM0a' _ g.2⟩)
      exact congrArg (fun z : K₀ => (z : E)) h1
  rw [memW₀, hM2c']
  have hφ : ((φ (φ.symm.toRingEquiv f) : F₀) : F) = (f : F) := by
    show ((φ (φ.symm f) : F₀) : F) = (f : F); rw [AlgEquiv.apply_symm_apply]
  constructor
  · rintro ⟨g, h, hnd, hgh⟩
    refine ⟨eB g, eB h, fun hd => hnd ((hdvd h).mpr hd), ?_⟩
    rw [← hφ]; exact (key _ g h).mp hgh
  · rintro ⟨g, h, hnd, hgh⟩
    refine ⟨eB.symm g, eB.symm h, fun hd => hnd (by simpa using (hdvd (eB.symm h)).mp hd), ?_⟩
    rw [key, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, hφ]; exact hgh

theorem dvd_iff_dvd_of_span_eq_map {B₀ B : Type*} [CommRing B₀] [CommRing B] (eB : B₀ ≃+* B) (π : B₀) (ϖ : B)
    (hideal : Ideal.span {ϖ} = (Ideal.span {π}).map eB.toRingHom) (h : B₀) :
    π ∣ h ↔ ϖ ∣ eB h := by
  rw [← Ideal.mem_span_singleton, ← Ideal.mem_span_singleton, hideal, Ideal.map_span, Set.image_singleton,
    Ideal.mem_span_singleton, Ideal.mem_span_singleton]
  show π ∣ h ↔ eB π ∣ eB h
  constructor
  · rintro ⟨c, rfl⟩; exact ⟨eB c, by rw [map_mul]⟩
  · rintro ⟨c, hc⟩; exact ⟨eB.symm c, by apply eB.injective; rw [map_mul, RingEquiv.apply_symm_apply]; exact hc⟩

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

theorem pow_eq_pow_mod_of_pow_eq_one {M : Type*} [Monoid M] (x : M) (q : ℕ) (hx : x ^ q = 1) (b : ℕ) :
    x ^ b = x ^ (b % q) := by
  conv_lhs => rw [← Nat.div_add_mod b q, pow_add, pow_mul, hx, one_pow, one_mul]

theorem exists_primitiveRoot_pow_eq {K : Type*} [CommRing K] [IsDomain K] {q ℓ : ℕ} (hq : 0 < q) (hℓ : 0 < ℓ)
    (hcop : q.Coprime ℓ) (ξ : K) (hξ : IsPrimitiveRoot ξ (q * ℓ)) (ζ : K) (hζ : IsPrimitiveRoot ζ q) :
    ∃ b : ℕ, IsPrimitiveRoot (ξ ^ b) (q * ℓ) ∧ (ξ ^ b) ^ ℓ = ζ := by
  haveI : NeZero q := ⟨hq.ne'⟩
  have hξℓ : IsPrimitiveRoot (ξ ^ ℓ) q := hξ.pow (Nat.mul_pos hq hℓ) (Nat.mul_comm q ℓ)
  obtain ⟨i, -, hi⟩ := hξℓ.eq_pow_of_pow_eq_one hζ.pow_eq_one
  have hicop : i.Coprime q := (hξℓ.pow_iff_coprime hq i).mp (hi ▸ hζ)
  obtain ⟨b, hbq, hbℓ⟩ := Nat.chineseRemainder hcop i 1
  have hbq' : b.Coprime q := by
    unfold Nat.Coprime at hicop ⊢; rw [Nat.ModEq.gcd_eq hbq]; exact hicop
  have hbℓ' : b.Coprime ℓ := by
    unfold Nat.Coprime; rw [Nat.ModEq.gcd_eq hbℓ]; exact Nat.gcd_one_left ℓ
  refine ⟨b, hξ.pow_of_coprime b (Nat.Coprime.mul_right hbq' hbℓ'), ?_⟩
  rw [← pow_mul, Nat.mul_comm b ℓ, pow_mul, pow_eq_pow_mod_of_pow_eq_one _ q hξℓ.pow_eq_one b,
    show b % q = i % q from hbq, ← pow_eq_pow_mod_of_pow_eq_one _ q hξℓ.pow_eq_one i, hi]

theorem levelStab_transport {k E F : Type*} [Field k] [Field E] [Field F] [Algebra k E] [Algebra k F]
    (K₀ : IntermediateField k E) (F₀ : IntermediateField k F) (φ : K₀ ≃ₐ[k] F₀)
    (W₀' : ValuationSubring K₀) (W₀ : ValuationSubring F₀)
    (memW₀ : ∀ f : F₀, f ∈ W₀ ↔ φ.symm.toRingEquiv f ∈ W₀')
    (τ : E ≃ₐ[k] E) (hτ : ∀ f : E, f ∈ K₀ → τ f ∈ K₀)
    (σ : F → F)
    (hστ : ∀ x : K₀, ((φ ⟨τ (x : E), hτ (x : E) x.2⟩ : F₀) : F) = σ ((φ x : F₀) : F))
    (hup : ∀ (f : E) (hf : f ∈ K₀) (hf' : τ f ∈ K₀), (⟨f, hf⟩ : K₀) ∈ W₀' ↔ (⟨τ f, hf'⟩ : K₀) ∈ W₀')
    (f : F) (hf : f ∈ F₀) (hf' : σ f ∈ F₀) :
    (⟨f, hf⟩ : F₀) ∈ W₀ ↔ (⟨σ f, hf'⟩ : F₀) ∈ W₀ := by
  set x : K₀ := φ.symm ⟨f, hf⟩ with hx
  have hφx : φ x = ⟨f, hf⟩ := by rw [hx, AlgEquiv.apply_symm_apply]
  have h1 : (⟨σ f, hf'⟩ : F₀) = φ ⟨τ (x : E), hτ (x : E) x.2⟩ := by
    apply Subtype.ext
    show σ f = ((φ ⟨τ (x : E), hτ (x : E) x.2⟩ : F₀) : F)
    rw [hστ, hφx]
  rw [memW₀, memW₀, h1, algEquiv_symm_toRingEquiv_apply_apply]
  have h2 : φ.symm.toRingEquiv ⟨f, hf⟩ = x := rfl
  rw [h2]
  have h3 : x = ⟨(x : E), x.2⟩ := rfl
  conv_lhs => rw [h3]
  exact hup (x : E) x.2 (hτ (x : E) x.2)

theorem levelStabB_transport {k E F : Type*} [Field k] [Field E] [Field F] [Algebra k E] [Algebra k F]
    (O : Type*) [CommRing O] [Algebra O E]
    (K₀ : IntermediateField k E) (F₀ : IntermediateField k F) (φ : K₀ ≃ₐ[k] F₀) (B₀ : Subalgebra O E)
    (B : Subring F)
    (hB : ∀ y : F, y ∈ B ↔ ∃ x : K₀, x ∈ B₀.toSubring.comap (algebraMap K₀ E) ∧
      y = ((algebraMap F₀ F).comp φ.toAlgHom.toRingHom) x)
    (τ : E ≃ₐ[k] E) (hτ : ∀ f : E, f ∈ K₀ → τ f ∈ K₀)
    (σ : F → F)
    (hστ : ∀ x : K₀, ((φ ⟨τ (x : E), hτ (x : E) x.2⟩ : F₀) : F) = σ ((φ x : F₀) : F))
    (hupB : ∀ f : E, f ∈ B₀ → τ f ∈ B₀)
    (f : F) (hf : f ∈ B) : σ f ∈ B := by
  obtain ⟨x, hx, rfl⟩ := (hB f).mp hf
  rw [(hB _)]
  refine ⟨⟨τ (x : E), hτ (x : E) x.2⟩, Subring.mem_comap.mpr (hupB _ (Subring.mem_comap.mp hx)), ?_⟩
  show σ ((φ x : F₀) : F) = ((φ ⟨τ (x : E), hτ (x : E) x.2⟩ : F₀) : F)
  rw [hστ]

end S3GlueKit
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_chartPole_otherPole_levelField_of_fixedField_of_algEquiv_framed.S3GlueKit"

namespace S3GlueKit
open IsLocalRing

section nodeTransport
variable {k E₀ E₁ : Type*} [Field k] [Field E₀] [Field E₁] [Algebra k E₀] [Algebra k E₁]

theorem toRingEquiv_apply' (φ : E₀ ≃ₐ[k] E₁) (x : E₀) : φ.toRingEquiv x = φ x := rfl
theorem toRingEquiv_symm_apply' (φ : E₀ ≃ₐ[k] E₁) (y : E₁) : φ.toRingEquiv.symm y = φ.symm y := rfl
theorem toRingEquiv_algebraMap' (φ : E₀ ≃ₐ[k] E₁) (x : k) : φ.toRingEquiv (algebraMap k E₀ x) = algebraMap k E₁ x :=
  φ.commutes x
theorem toRingEquiv_symm_algebraMap' (φ : E₀ ≃ₐ[k] E₁) (x : k) : φ.toRingEquiv.symm (algebraMap k E₁ x) = algebraMap k E₀ x :=
  φ.symm.commutes x

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

theorem mem_comap_symm_iff (φ : E₀ ≃ₐ[k] E₁) (W' : ValuationSubring E₀) (f : E₁) :
    f ∈ W'.comap (φ.symm.toRingEquiv : E₁ →+* E₀) ↔ φ.symm f ∈ W' := Iff.rfl

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
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_chartPole_otherPole_levelField_of_fixedField_of_algEquiv_framed.S3GlueKit"

end S3GlueKit
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_chartPole_otherPole_levelField_of_fixedField_of_algEquiv_framed.S3GlueKit"

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
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_chartPole_otherPole_levelField_of_fixedField_of_algEquiv_framed.S3GlueKit"

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

theorem coe_imSEquiv_eq (φ : E₀ ≃ₐ[k] E₁) (O₀ : Subring E₀) (c : O₀) :
    ((imSEquiv φ.toRingEquiv O₀ c : imS φ.toRingEquiv O₀) : E₁) = φ (c : E₀) := rfl

end coverRight
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_chartPole_otherPole_levelField_of_fixedField_of_algEquiv_framed.S3GlueKit"

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
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_chartPole_otherPole_levelField_of_fixedField_of_algEquiv_framed.S3GlueKit"

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
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_chartPole_otherPole_levelField_of_fixedField_of_algEquiv_framed.S3GlueKit"

end S3GlueKit
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_chartPole_otherPole_levelField_of_fixedField_of_algEquiv_framed.S3GlueKit"

namespace S3GlueKit
open ModularCurve ModularCurve.FullLevel
open scoped MatrixGroups

section dict
variable (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
  (ℓ' : ℕ) [Fact ℓ'.Prime] (hℓ'3 : 3 ≤ ℓ') (hℓ'q : ℓ' ≠ q) (hℓ'M : ¬ ℓ' ∣ M')
  (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (ξ : ↥k₀) (hξ : IsPrimitiveRoot ξ (q * ℓ'))
  (Kℓ : IntermediateField ↥k₀ (LaurentSeries ↥k₀))
  (hKℓ : Kℓ = ModularCurve.laurentBaseChange ↥k₀
      (ModularCurve.xHFunctionField ((q * ℓ') ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ') M')))
  (K₀ : IntermediateField ↥k₀ ↥Kℓ)
  [Algebra ↥k₀ ↥(fieldBar q M')] (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M')) (φ : ↥K₀ ≃ₐ[↥k₀] ↥F₀)
  (hφ4 :       (∀ (ζ : Idx q) (ξ' : ↥k₀), IsPrimitiveRoot ξ' (q * ℓ') → ζ.val = (((ξ' ^ ℓ' : ↥k₀)) : AlgebraicClosure ℚ) →
        ∀ (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 M' →
        ∀ (τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ),
          ModularCurve.FullLevel.IsLevelAutAt ↥k₀ (q * ℓ') ξ' (q * ℓ') ((q * ℓ') ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ') M') γ Kℓ τ →
          ∃ hτ : ∀ f : ↥Kℓ, f ∈ K₀ → τ f ∈ K₀,
            ∀ f : ↥K₀, ((φ ⟨τ (f : ↥Kℓ), hτ (f : ↥Kℓ) f.2⟩ : ↥F₀) : ↥(fieldBar q M')) =
              levelAutBar q M' ζ γ ((φ f : ↥F₀) : ↥(fieldBar q M'))))

include hq hqM' hℓ'3 hℓ'q hℓ'M hξ hKℓ hφ4

theorem dict_fwd (ζ : Idx q) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M') :
    ∃ (τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ) (γ' : SL(2, ℤ)), γ' ∈ CongruenceSubgroup.Gamma0 M' ∧
      ModularCurve.FullLevel.IsLevelAutAt ↥k₀ (q * ℓ') ξ (q * ℓ') ((q * ℓ') ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ') M') γ'⁻¹ Kℓ τ ∧
      ∃ hτ : (∀ f : ↥Kℓ, f ∈ K₀ → τ f ∈ K₀), ∀ x : ↥K₀,
        ((φ ⟨τ (x : ↥Kℓ), hτ (x : ↥Kℓ) x.2⟩ : ↥F₀) : ↥(fieldBar q M')) = levelAutBar q M' ζ γ ((φ x : ↥F₀) : ↥(fieldBar q M')) := by
  have hq0 : 0 < q := (Fact.out : q.Prime).pos
  have hℓ0 : 0 < ℓ' := (Fact.out : ℓ'.Prime).pos
  haveI : NeZero (q * ℓ') := ⟨Nat.mul_ne_zero hq0.ne' hℓ0.ne'⟩
  have hcop : q.Coprime ℓ' := (Nat.coprime_primes Fact.out Fact.out).mpr (Ne.symm hℓ'q)
  have hmM : Nat.Coprime (q * ℓ') M' :=
    Nat.Coprime.mul ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hqM') ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hℓ'M)
  have hξbar : IsPrimitiveRoot ((ξ : ↥k₀) : AlgebraicClosure ℚ) (q * ℓ') :=
    hξ.map_of_injective (algebraMap ↥k₀ (AlgebraicClosure ℚ)).injective
  have hζ : IsPrimitiveRoot ζ.val q := (mem_primitiveRoots hq0).mp (ζ : ↥(primitiveRoots q (AlgebraicClosure ℚ))).2
  obtain ⟨b, hb, hbζ⟩ := exists_primitiveRoot_pow_eq hq0 hℓ0 hcop _ hξbar _ hζ
  have hξ'prim : IsPrimitiveRoot (ξ ^ b) (q * ℓ') :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap ↥k₀ (AlgebraicClosure ℚ)) (by rw [map_pow]; exact hb)
      (algebraMap ↥k₀ (AlgebraicClosure ℚ)).injective
  have hζeq : ζ.val = (((ξ ^ b) ^ ℓ' : ↥k₀) : AlgebraicClosure ℚ) := by rw [← hbζ]; push_cast; rfl
  have hι' := exists_emb k₀ (q * ℓ') (ξ ^ b) hξ'prim
  obtain ⟨τ, hτ⟩ := ModularCurve.FullLevel.AuxLevel.exists_isLevelAutAt_of_mem_gamma0_of_exists_ringHom q hq M' hqM' ℓ' hℓ'3 hℓ'q hℓ'M
      ↥k₀ (ξ ^ b) hξ'prim (by simpa only [Nat.cast_mul] using hι') Kℓ hKℓ γ⁻¹ (inv_mem hγ)
  rw [inv_inv] at hτ
  obtain ⟨hτK₀, hστ⟩ := hφ4 ζ (ξ ^ b) hξ'prim hζeq γ hγ τ hτ
  obtain ⟨d, hd⟩ := ModularCurve.FullLevel.exists_isLevelAutAt_conj_of_isLevelAutAt_of_isPrimitiveRoot ↥k₀ q M' (q * ℓ')
    (Dvd.intro ℓ' rfl) hmM ξ (ξ ^ b) hξ hξ'prim Kℓ
  obtain ⟨γ', hγ'0, -, -, hτ'⟩ := hd γ hγ τ hτ
  exact ⟨τ, γ'⁻¹, inv_mem hγ'0, by rw [inv_inv]; exact hτ', hτK₀, hστ⟩

theorem dict_bwd (ζ : Idx q) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M') (τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ)
    (hτ : ModularCurve.FullLevel.IsLevelAutAt ↥k₀ (q * ℓ') ξ (q * ℓ') ((q * ℓ') ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ') M') γ⁻¹ Kℓ τ) :
    ∃ γ₂ : SL(2, ℤ), γ₂ ∈ CongruenceSubgroup.Gamma0 M' ∧
      ∃ hτ : (∀ f : ↥Kℓ, f ∈ K₀ → τ f ∈ K₀), ∀ x : ↥K₀,
        ((φ ⟨τ (x : ↥Kℓ), hτ (x : ↥Kℓ) x.2⟩ : ↥F₀) : ↥(fieldBar q M')) = levelAutBar q M' ζ γ₂ ((φ x : ↥F₀) : ↥(fieldBar q M')) := by
  have hq0 : 0 < q := (Fact.out : q.Prime).pos
  have hℓ0 : 0 < ℓ' := (Fact.out : ℓ'.Prime).pos
  haveI : NeZero (q * ℓ') := ⟨Nat.mul_ne_zero hq0.ne' hℓ0.ne'⟩
  have hcop : q.Coprime ℓ' := (Nat.coprime_primes Fact.out Fact.out).mpr (Ne.symm hℓ'q)
  have hmM : Nat.Coprime (q * ℓ') M' :=
    Nat.Coprime.mul ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hqM') ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hℓ'M)
  have hξbar : IsPrimitiveRoot ((ξ : ↥k₀) : AlgebraicClosure ℚ) (q * ℓ') :=
    hξ.map_of_injective (algebraMap ↥k₀ (AlgebraicClosure ℚ)).injective
  have hζ : IsPrimitiveRoot ζ.val q := (mem_primitiveRoots hq0).mp (ζ : ↥(primitiveRoots q (AlgebraicClosure ℚ))).2
  obtain ⟨b, hb, hbζ⟩ := exists_primitiveRoot_pow_eq hq0 hℓ0 hcop _ hξbar _ hζ
  have hξ'prim : IsPrimitiveRoot (ξ ^ b) (q * ℓ') :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap ↥k₀ (AlgebraicClosure ℚ)) (by rw [map_pow]; exact hb)
      (algebraMap ↥k₀ (AlgebraicClosure ℚ)).injective
  have hζeq : ζ.val = (((ξ ^ b) ^ ℓ' : ↥k₀) : AlgebraicClosure ℚ) := by rw [← hbζ]; push_cast; rfl
  obtain ⟨d, hd⟩ := ModularCurve.FullLevel.exists_isLevelAutAt_conj_of_isLevelAutAt_of_isPrimitiveRoot ↥k₀ q M' (q * ℓ')
    (Dvd.intro ℓ' rfl) hmM (ξ ^ b) ξ hξ'prim hξ Kℓ
  obtain ⟨γ', hγ'0, -, -, hτ'⟩ := hd γ⁻¹ (inv_mem hγ) τ hτ
  obtain ⟨hτK₀, hστ⟩ := hφ4 ζ (ξ ^ b) hξ'prim hζeq γ' hγ'0 τ hτ'
  exact ⟨γ', hγ'0, hτK₀, hστ⟩

end dict
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_chartPole_otherPole_levelField_of_fixedField_of_algEquiv_framed.S3GlueKit"

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
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_chartPole_otherPole_levelField_of_fixedField_of_algEquiv_framed.S3GlueKit"

end S3GlueKit
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_chartPole_otherPole_levelField_of_fixedField_of_algEquiv_framed.S3GlueKit"

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
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (ℓ' : ℕ) [NeZero ℓ'] (hℓ' : 1 < ℓ')
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
        ModularCurve.qExpand (AlgebraicClosure ℚ) ℓ' (((φ f : ↥F₀) : ↥(laurentBaseChange (AlgebraicClosure ℚ) X)) : LaurentSeries (AlgebraicClosure ℚ)))
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
  have hLS : (((j' : ↥K₀) : ↥Kℓ) : LaurentSeries ↥k₀) =
      coeffEmb ↥k₀ (ModularCurve.qExpand ℚ ℓ' jq) := by
    apply ModularCurve.coeffMap_injective (f := algebraMap ↥k₀ (AlgebraicClosure ℚ)) (algebraMap ↥k₀ _).injective
    rw [hφ1 j', hφj', coeffEmb, coeffMap_coeffMap]
    have hrat : (algebraMap ↥k₀ (AlgebraicClosure ℚ)).comp (algebraMap ℚ ↥k₀) = algebraMap ℚ (AlgebraicClosure ℚ) :=
      RingHom.ext_rat _ _
    rw [hrat]
    show ModularCurve.qExpand (AlgebraicClosure ℚ) ℓ' (jF : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ ℓ' jq)
    rw [hjF, ModularCurve.coeffEmb_qExpand]
  have hJ0 : ((j' : ↥K₀) : ↥Kℓ) ≠ 0 := by
    intro h
    have h1 : coeffEmb ↥k₀ (ModularCurve.qExpand ℚ ℓ' jq) = 0 := by
      rw [← hLS, h]; rfl
    rw [ModularCurve.coeffEmb_qExpand] at h1
    exact ModularCurve.coeffEmb_jq_ne_zero ↥k₀ (ModularCurve.qExpand_injective ℓ' (h1.trans (map_zero _).symm))
  haveI : Fact (((j' : ↥K₀) : ↥Kℓ) ≠ 0) := ⟨hJ0⟩
  have hcusp := (ModularCurve.mem_chartAlgFin_and_forall_mem_chartAlgInf_exists_mul_mem_of_coe_eq_coeffEmb_jq_qExpand_of_one_lt
    ℓ' hℓ' ↥k₀ Kℓ Acst jℓ hjℓ ((j' : ↥K₀) : ↥Kℓ) hLS).2.1

  let Wsub : Subalgebra Acst ↥Kℓ :=
    { carrier := w.toValuationSubring
      mul_mem' := fun ha hb => w.toValuationSubring.mul_mem _ _ ha hb
      one_mem' := w.toValuationSubring.one_mem
      add_mem' := fun ha hb => w.toValuationSubring.add_mem _ _ ha hb
      zero_mem' := w.toValuationSubring.zero_mem
      algebraMap_mem' := fun a => by
        show algebraMap Acst ↥Kℓ a ∈ w.toValuationSubring
        rw [IsScalarTower.algebraMap_apply Acst ↥k₀ ↥Kℓ]; exact w.algebraMap_mem' _ }
  have hadjW : Algebra.adjoin Acst {((j' : ↥K₀) : ↥Kℓ)} ≤ Wsub :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr hj'w)
  have hadj : (Algebra.adjoin Acst {((j' : ↥K₀) : ↥Kℓ)}).toSubring ≤
      w.toValuationSubring.toSubring := fun z hz => hadjW hz
  letI alg : Algebra ↥(Algebra.adjoin Acst {((j' : ↥K₀) : ↥Kℓ)}) ↥w.toValuationSubring :=
    (Subring.inclusion hadj).toAlgebra
  letI : IsScalarTower ↥(Algebra.adjoin Acst {((j' : ↥K₀) : ↥Kℓ)}) ↥w.toValuationSubring ↥Kℓ :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hint' : IsIntegral ↥w.toValuationSubring (jℓ : ↥Kℓ) :=
    ((AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff Acst ↥Kℓ).mp hcusp).tower_top
  obtain ⟨yj, hyj⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint'
  have hjw : (jℓ : ↥Kℓ) ∈ w.toValuationSubring := hyj ▸ yj.2
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
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_chartPole_otherPole_levelField_of_fixedField_of_algEquiv_framed.S3GlueKit"

namespace S3GlueKit
open ModularCurve

theorem qExpand_coeffEmb_mem_of_coeffLaw (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (ℓ' : ℕ) [NeZero ℓ']
    (Kℓ : IntermediateField ↥k₀ (LaurentSeries ↥k₀)) (K₀ : IntermediateField ↥k₀ ↥Kℓ)
    (X : IntermediateField ℚ (LaurentSeries ℚ)) [Algebra ↥k₀ ↥(laurentBaseChange (AlgebraicClosure ℚ) X)]
    (F₀ : IntermediateField ↥k₀ ↥(laurentBaseChange (AlgebraicClosure ℚ) X)) (φ : ↥K₀ ≃ₐ[↥k₀] ↥F₀)
    (hφ1 : ∀ f : ↥K₀, coeffMap (algebraMap ↥k₀ (AlgebraicClosure ℚ)) (((f : ↥Kℓ)) : LaurentSeries ↥k₀) =
        ModularCurve.qExpand (AlgebraicClosure ℚ) ℓ' (((φ f : ↥F₀) : ↥(laurentBaseChange (AlgebraicClosure ℚ) X)) : LaurentSeries (AlgebraicClosure ℚ)))
    (g : LaurentSeries ℚ) (v : ↥(laurentBaseChange (AlgebraicClosure ℚ) X))
    (hv : (v : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) g) (hvF₀ : v ∈ F₀)
    (hgK : ModularCurve.qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ g) ∈ Kℓ) :
    (⟨ModularCurve.qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ g), hgK⟩ : ↥Kℓ) ∈ K₀ := by
  have hLS : (((φ.symm ⟨v, hvF₀⟩ : ↥K₀) : ↥Kℓ) : LaurentSeries ↥k₀) = ModularCurve.qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ g) := by
    apply ModularCurve.coeffMap_injective (f := algebraMap ↥k₀ (AlgebraicClosure ℚ)) (algebraMap ↥k₀ _).injective
    rw [hφ1, AlgEquiv.apply_symm_apply, ModularCurve.coeffMap_qExpand, coeffEmb, coeffMap_coeffMap,
      RingHom.ext_rat ((algebraMap ↥k₀ (AlgebraicClosure ℚ)).comp (algebraMap ℚ ↥k₀)) (algebraMap ℚ (AlgebraicClosure ℚ))]
    show ModularCurve.qExpand (AlgebraicClosure ℚ) ℓ' (v : LaurentSeries (AlgebraicClosure ℚ)) = _
    rw [hv]; rfl
  have : (⟨ModularCurve.qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ g), hgK⟩ : ↥Kℓ) = ((φ.symm ⟨v, hvF₀⟩ : ↥K₀) : ↥Kℓ) :=
    Subtype.ext hLS.symm
  rw [this]; exact (φ.symm ⟨v, hvF₀⟩).2

end S3GlueKit
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_chartPole_otherPole_levelField_of_fixedField_of_algEquiv_framed.S3GlueKit"

namespace S3GlueKit
open IsLocalRing

theorem aeval_map_algebraMap_transport {k E₀ E₁ : Type*} [Field k] [Field E₀] [Field E₁] [Algebra k E₀] [Algebra k E₁]
    (φ : E₀ ≃ₐ[k] E₁) (x : E₀) (p : Polynomial k) :
    φ (Polynomial.aeval x (p.map (algebraMap k E₀))) = Polynomial.aeval (φ x) (p.map (algebraMap k E₁)) := by
  rw [Polynomial.coe_aeval_eq_eval, Polynomial.coe_aeval_eq_eval, Polynomial.eval_map, Polynomial.eval_map]
  rw [show (φ : E₀ → E₁) = ((φ : E₀ →ₐ[k] E₁) : E₀ →+* E₁) from rfl, Polynomial.hom_eval₂, AlgHom.comp_algebraMap]

section Etransport
variable {k L F : Type*} [Field k] [Field L] [Field F] [Algebra k L] [Algebra k F]

theorem igusaPole_transport
    (Kℓ : IntermediateField k L) (K₀ : IntermediateField k ↥Kℓ) (F₀ : IntermediateField k F) (φ : ↥K₀ ≃ₐ[k] ↥F₀)
    (PA : k → Prop) (π₀ : k)
    (Ob : Type*) [CommRing Ob] [Algebra Ob ↥Kℓ] (B₀ : Subalgebra Ob ↥Kℓ) (B : Subring F)
    (hB : ∀ y : F, y ∈ B ↔ ∃ x : ↥K₀, x ∈ B₀.toSubring.comap (algebraMap ↥K₀ ↥Kℓ) ∧
      y = ((algebraMap ↥F₀ F).comp φ.toAlgHom.toRingHom) x)
    (JK : L) (JF : F) (hJKmem : JK ∈ Kℓ) (hJK₀ : (⟨JK, hJKmem⟩ : ↥Kℓ) ∈ K₀) (hJφ : ((φ ⟨⟨JK, hJKmem⟩, hJK₀⟩ : ↥F₀) : F) = JF)
    (hE1 : ∃ b : ↥K₀, (b : ↥Kℓ) ∈ B₀ ∧ ∀ V : ValuationSubring ↥K₀,
          (∀ x : k, PA x ↔ algebraMap k ↥K₀ x ∈ V) →
          (∀ hπV : algebraMap k ↥K₀ π₀ ∈ V, (⟨_, hπV⟩ : ↥V) ∈ maximalIdeal ↥V) →
          ∀ (hjK' : JK ∈ Kℓ) (hjF : (⟨JK, hjK'⟩ : ↥Kℓ) ∈ K₀) (hjV : (⟨_, hjF⟩ : ↥K₀) ∈ V),
            (∀ p : Polynomial k, p.Monic → (∀ i : ℕ, PA (p.coeff i)) →
              ∀ hp : Polynomial.aeval (⟨_, hjF⟩ : ↥K₀) (p.map (algebraMap k ↥K₀)) ∈ V,
                (⟨_, hp⟩ : ↥V) ∉ maximalIdeal ↥V) →
          b ∉ V) :
    ∃ (b : F) (hbF : b ∈ F₀), b ∈ B ∧ ∀ V : ValuationSubring ↥F₀,
          (∀ x : k, PA x ↔ algebraMap k ↥F₀ x ∈ V) →
          (∀ hπV : algebraMap k ↥F₀ π₀ ∈ V, (⟨_, hπV⟩ : ↥V) ∈ maximalIdeal ↥V) →
          ∀ (hjF : JF ∈ F₀) (hjV : (⟨JF, hjF⟩ : ↥F₀) ∈ V),
            (∀ p : Polynomial k, p.Monic → (∀ i : ℕ, PA (p.coeff i)) →
              ∀ hp : Polynomial.aeval (⟨JF, hjF⟩ : ↥F₀) (p.map (algebraMap k ↥F₀)) ∈ V,
                (⟨_, hp⟩ : ↥V) ∉ maximalIdeal ↥V) →
          (⟨b, hbF⟩ : ↥F₀) ∉ V := by
  obtain ⟨b₀, hb₀B, hb₀⟩ := hE1
  refine ⟨((φ b₀ : ↥F₀) : F), (φ b₀).2, (hB _).mpr ⟨b₀, Subring.mem_comap.mpr hb₀B, rfl⟩, ?_⟩
  intro V hVA hVπ hjF hjV hres hbV
  have hJx : (⟨JF, hjF⟩ : ↥F₀) = φ.toRingEquiv ⟨⟨JK, hJKmem⟩, hJK₀⟩ := Subtype.ext hJφ.symm
  have hb : (⟨((φ b₀ : ↥F₀) : F), (φ b₀).2⟩ : ↥F₀) = φ.toRingEquiv b₀ := Subtype.ext rfl
  refine hb₀ (V.comap (φ.toRingEquiv : ↥K₀ →+* ↥F₀)) (fun x => coverConst_transport K₀ F₀ φ V PA hVA x) ?_ hJKmem hJK₀ ?_ ?_ ?_
  · intro hπV
    have hπV' : algebraMap k ↥F₀ π₀ ∈ V := by
      have h1 : φ.toRingEquiv (algebraMap k ↥K₀ π₀) ∈ V := hπV
      rwa [toRingEquiv_algebraMap'] at h1
    rw [mem_maximalIdeal_comap_iff]
    have : comapEquiv φ.toRingEquiv V ⟨_, hπV⟩ = ⟨_, hπV'⟩ := Subtype.ext (toRingEquiv_algebraMap' φ π₀)
    rw [this]; exact hVπ hπV'
  · show φ.toRingEquiv ⟨⟨JK, hJKmem⟩, hJK₀⟩ ∈ V
    rw [← hJx]; exact hjV
  · intro p hp hpA hpV
    have hae : φ.toRingEquiv (Polynomial.aeval (⟨⟨JK, hJKmem⟩, hJK₀⟩ : ↥K₀) (p.map (algebraMap k ↥K₀))) =
        Polynomial.aeval (⟨JF, hjF⟩ : ↥F₀) (p.map (algebraMap k ↥F₀)) := by
      rw [hJx, toRingEquiv_apply', toRingEquiv_apply']
      exact aeval_map_algebraMap_transport φ _ p
    have hpV' : Polynomial.aeval (⟨JF, hjF⟩ : ↥F₀) (p.map (algebraMap k ↥F₀)) ∈ V := by
      rw [← hae]; exact hpV
    rw [mem_maximalIdeal_comap_iff]
    have : comapEquiv φ.toRingEquiv V ⟨_, hpV⟩ = ⟨_, hpV'⟩ := Subtype.ext hae
    rw [this]; exact hres p hp hpA hpV'
  · show φ.toRingEquiv b₀ ∈ V
    rw [← hb]; exact hbV

theorem overPole_transport
    (Kℓ : IntermediateField k L) (K₀ : IntermediateField k ↥Kℓ) (F₀ : IntermediateField k F) (φ : ↥K₀ ≃ₐ[k] ↥F₀)
    (PA : k → Prop)
    (Ob : Type*) [CommRing Ob] [Algebra Ob ↥Kℓ] (B₀ : Subalgebra Ob ↥Kℓ) (B : Subring F)
    (hB : ∀ y : F, y ∈ B ↔ ∃ x : ↥K₀, x ∈ B₀.toSubring.comap (algebraMap ↥K₀ ↥Kℓ) ∧
      y = ((algebraMap ↥F₀ F).comp φ.toAlgHom.toRingHom) x)
    {SS : Type*} (s₀ : SS)
    (G₁ : Type*) (MF : G₁ → Prop) (Q : ∀ g : G₁, MF g → Prop) (C : ∀ (g : G₁) (hg : MF g), Q g hg → Prop)
    (RS : SS → ∀ (g : G₁) (hg : MF g), Q g hg → Prop)
    (Pc : SS → ∀ (g : G₁) (hg : MF g), Q g hg → ∀ c : k, PA c → Prop) (yK : G₁ → L) (vF : ∀ g : G₁, MF g → F)
    (hyK : ∀ g : G₁, MF g → yK g ∈ Kℓ) (hyK₀ : ∀ (g : G₁) (hg : MF g), (⟨yK g, hyK g hg⟩ : ↥Kℓ) ∈ K₀)
    (hv : ∀ (g : G₁) (hg : MF g) (hgK : yK g ∈ Kℓ) (hF : (⟨yK g, hgK⟩ : ↥Kℓ) ∈ K₀), ((φ ⟨⟨yK g, hgK⟩, hF⟩ : ↥F₀) : F) = vF g hg)
    (hE3 : ∀ s' : SS, s' ≠ s₀ → ∃ b : ↥K₀, (b : ↥Kℓ) ∈ B₀ ∧ ∀ V : ValuationSubring ↥K₀,
          (∀ x : k, PA x ↔ algebraMap k ↥K₀ x ∈ V) →
          (∀ (g : G₁) (hg : MF g) (hgi : Q g hg),
            C g hg hgi →
            RS s' g hg hgi →
              ∀ (hgK : yK g ∈ Kℓ), ∃ hF : (⟨yK g, hgK⟩ : ↥Kℓ) ∈ K₀,
                (⟨_, hF⟩ : ↥K₀) ∈ V ∧
                ∀ (c : k) (hc : PA c),
                  Pc s' g hg hgi c hc →
                  ∃ hm : (⟨_, hF⟩ : ↥K₀) - algebraMap k ↥K₀ c ∈ V, (⟨_, hm⟩ : ↥V) ∈ maximalIdeal ↥V) →
          b ∉ V) :
    ∀ s' : SS, s' ≠ s₀ → ∃ (b : F) (hbF : b ∈ F₀), b ∈ B ∧ ∀ V : ValuationSubring ↥F₀,
          (∀ x : k, PA x ↔ algebraMap k ↥F₀ x ∈ V) →
          (∀ (g : G₁) (hg : MF g) (hgi : Q g hg),
            C g hg hgi →
            RS s' g hg hgi →
              ∃ hF : vF g hg ∈ F₀,
                (⟨_, hF⟩ : ↥F₀) ∈ V ∧
                ∀ (c : k) (hc : PA c),
                  Pc s' g hg hgi c hc →
                  ∃ hm : (⟨_, hF⟩ : ↥F₀) - algebraMap k ↥F₀ c ∈ V, (⟨_, hm⟩ : ↥V) ∈ maximalIdeal ↥V) →
          (⟨b, hbF⟩ : ↥F₀) ∉ V := by
  intro s' hs'
  obtain ⟨b₀, hb₀B, hb₀⟩ := hE3 s' hs'
  refine ⟨((φ b₀ : ↥F₀) : F), (φ b₀).2, (hB _).mpr ⟨b₀, Subring.mem_comap.mpr hb₀B, rfl⟩, ?_⟩
  intro V hVA hVs hbV
  have hb : (⟨((φ b₀ : ↥F₀) : F), (φ b₀).2⟩ : ↥F₀) = φ.toRingEquiv b₀ := Subtype.ext rfl
  refine hb₀ (V.comap (φ.toRingEquiv : ↥K₀ →+* ↥F₀)) (fun x => coverConst_transport K₀ F₀ φ V PA hVA x)
    (fun g hg hgi hC hRS hgK => ⟨hyK₀ g hg, coverHyp_transport K₀ F₀ φ V PA (Pc s' g hg hgi) _ (hyK₀ g hg) _
      (hv g hg hgK (hyK₀ g hg)) (hVs g hg hgi hC hRS)⟩) ?_
  show φ.toRingEquiv b₀ ∈ V
  rw [← hb]; exact hbV

end Etransport
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_chartPole_otherPole_levelField_of_fixedField_of_algEquiv_framed.S3GlueKit"

end S3GlueKit
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_chartPole_otherPole_levelField_of_fixedField_of_algEquiv_framed.S3GlueKit"

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup AlgebraicCurve.TwoChartIntegralModel
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem solution
    (q : ℕ)
    [Fact q.Prime]
    (M' : ℕ)
    [NeZero M']
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
    (ℓ' : ℕ)
    [Fact ℓ'.Prime]
    (ξ : ↥k₀)
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
    (hjK : ModularCurve.jqNModC ↥k₀ (q * ℓ') ∈ Kℓ)
    (a₀ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (ends : Finset (Subring ↥Kℓ))
    (ℱ : ModularCurve.FullLevel.RigidDescentHyps q M' A W hle R₀ s k₀ π₀ hπ ℓ ζ₀ ϖt Kb Ab hAb ϖb ℓ' ξ Kℓ jℓ ϖt' y Bt Wt hBW n γ₀ τ₀ m ζc hjK a₀ ends)
    (G : Subgroup (↥Kℓ ≃ₐ[↥k₀] ↥Kℓ))
    (hG : G = Subgroup.closure {τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ | ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧
      ModularCurve.FullLevel.IsLevelAutAt ↥k₀ (q * ℓ') ξ (q * ℓ') ((q * ℓ') ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ') M') γ⁻¹ Kℓ τ})
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
        ModularCurve.qExpand (AlgebraicClosure ℚ) ℓ' (((φ f : ↥F₀) : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)))) →

          (∀ (ζ : Idx q) (ξ' : ↥k₀), IsPrimitiveRoot ξ' (q * ℓ') → ζ.val = (((ξ' ^ ℓ' : ↥k₀)) : AlgebraicClosure ℚ) →
        ∀ (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 M' →
        ∀ (τ : ↥Kℓ ≃ₐ[↥k₀] ↥Kℓ),
          ModularCurve.FullLevel.IsLevelAutAt ↥k₀ (q * ℓ') ξ' (q * ℓ') ((q * ℓ') ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ') M') γ Kℓ τ →
          ∃ hτ : ∀ f : ↥Kℓ, f ∈ K₀ → τ f ∈ K₀,
            ∀ f : ↥K₀, ((φ ⟨τ (f : ↥Kℓ), hτ (f : ↥Kℓ) f.2⟩ : ↥F₀) : ↥(fieldBar q M')) =
              levelAutBar q M' ζ γ ((φ f : ↥F₀) : ↥(fieldBar q M'))) →

          (∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
        (hgK : ModularCurve.qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ g) ∈ Kℓ) (hgK₀ : (⟨_, hgK⟩ : ↥Kℓ) ∈ K₀),
        ((φ ⟨⟨_, hgK⟩, hgK₀⟩ : ↥F₀) : ↥(fieldBar q M')) =
          IntermediateField.inclusion hle ⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩) →
    ∀ (W₀ : ValuationSubring ↥F₀), W₀ = W₀'.comap (φ.symm.toRingEquiv : ↥F₀ →+* ↥K₀) →
    ∀ (B : Subring ↥(fieldBar q M')),
    (∀ y : ↥(fieldBar q M'), y ∈ B ↔ ∃ x : ↥K₀, x ∈ B₀.toSubring.comap (algebraMap ↥K₀ ↥Kℓ) ∧
      y = ((algebraMap ↥F₀ ↥(fieldBar q M')).comp φ.toAlgHom.toRingHom) x) →

    (∃ b : ↥K₀, (b : ↥Kℓ) ∈ B₀ ∧ ∀ V : ValuationSubring ↥K₀,
          (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥K₀ x ∈ V) →
          (∀ hπV : algebraMap ↥k₀ ↥K₀ π₀ ∈ V, (⟨_, hπV⟩ : ↥V) ∈ maximalIdeal ↥V) →
          ∀ (hjK' : ModularCurve.qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ jq) ∈ Kℓ) (hjF : (⟨ModularCurve.qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ jq), hjK'⟩ : ↥Kℓ) ∈ K₀) (hjV : (⟨_, hjF⟩ : ↥K₀) ∈ V),
            (∀ p : Polynomial ↥k₀, p.Monic → (∀ i : ℕ, ((p.coeff i : ↥k₀) : (AlgebraicClosure ℚ)) ∈ A) →
              ∀ hp : Polynomial.aeval (⟨_, hjF⟩ : ↥K₀) (p.map (algebraMap ↥k₀ ↥K₀)) ∈ V,
                (⟨_, hp⟩ : ↥V) ∉ maximalIdeal ↥V) →
          b ∉ V) →

    (∀ s' : ↥W, s' ≠ s → ∃ b : ↥K₀, (b : ↥Kℓ) ∈ B₀ ∧ ∀ V : ValuationSubring ↥K₀,
          (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥K₀ x ∈ V) →
          (∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
            (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
            (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
              0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
              0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) :
                ↥(modularFunctionFieldBar M'))) →
            (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') ∈
                ((s' : ↥W) : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
              ∀ (hgK : ModularCurve.qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ g) ∈ Kℓ), ∃ hF : (⟨ModularCurve.qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ g), hgK⟩ : ↥Kℓ) ∈ K₀,
                (⟨_, hF⟩ : ↥K₀) ∈ V ∧
                ∀ (c : ↥k₀) (hc : (c : (AlgebraicClosure ℚ)) ∈ A),
                  residue A ⟨(c : (AlgebraicClosure ℚ)), hc⟩ =
                    ((s' : ↥W) : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩) →
                  ∃ hm : (⟨_, hF⟩ : ↥K₀) - algebraMap ↥k₀ ↥K₀ c ∈ V, (⟨_, hm⟩ : ↥V) ∈ maximalIdeal ↥V) →
          b ∉ V) →

    ((∃ (b : ↥(fieldBar q M')) (hbF : b ∈ F₀), b ∈ B ∧ ∀ V : ValuationSubring ↥F₀,
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
          (⟨b, hbF⟩ : ↥F₀) ∉ V) ∧
        (∀ s' : ↥W, s' ≠ s → ∃ (b : ↥(fieldBar q M')) (hbF : b ∈ F₀), b ∈ B ∧ ∀ V : ValuationSubring ↥F₀,
          (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥F₀ x ∈ V) →
          (∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
            (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
            (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
              0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
              0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) :
                ↥(modularFunctionFieldBar M'))) →
            (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') ∈
                ((s' : ↥W) : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
              ∃ hF : (IntermediateField.inclusion hle ⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(fieldBar q M')) ∈ F₀,
                (⟨_, hF⟩ : ↥F₀) ∈ V ∧
                ∀ (c : ↥k₀) (hc : (c : (AlgebraicClosure ℚ)) ∈ A),
                  residue A ⟨(c : (AlgebraicClosure ℚ)), hc⟩ =
                    ((s' : ↥W) : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩) →
                  ∃ hm : (⟨_, hF⟩ : ↥F₀) - algebraMap ↥k₀ ↥F₀ c ∈ V, (⟨_, hm⟩ : ↥V) ∈ maximalIdeal ↥V) →
          (⟨b, hbF⟩ : ↥F₀) ∉ V)):= by
  obtain ⟨hq, hqM', hA, hW, hR₀, hdvr, hunif, hhens, hres, hκ, hℓ, hℓ3, hℓq, hℓM', hζ₀, hϖtA, hϖt, hKb, hϖb, hϖb0, hℓ'3, hℓ'q, hℓ'M, htame, hξ, hKℓ, hjℓ, hϖt', hy, hϖy, hss, hover, hOrbit, hS1, hn1, hnq, hγ₀Γ, hγ₀Γ0, hτ₀, hτ₀W, hm1, hm, hζc, hζcprim, hjC, ha₀y, hR7, hR9, hR10, hn⟩ := ℱ
  intro F₀ hCHAR φ hφ1 hφ4 hφ5 W₀ hW₀ B hB hE1' hE3'
  letI : Algebra ↥k₀ ↥(fieldBar q M') :=
    ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
  classical

  have hgKall : ∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M'), ModularCurve.qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ g) ∈ Kℓ := by
    intro g hg
    have h0 := ModularCurve.qExpand_coeffEmb_mem_laurentBaseChange_xHFunctionField_of_mem_modularFunctionFieldFull ↥k₀ M' ℓ' ((q * ℓ') ^ 2 * M')
        ⟨q ^ 2 * ℓ', by ring⟩ (ModularCurve.FullLevel.levelH (q * ℓ') M') g hg
    rw [hKℓ]; exact h0
  have hℓ'1 : 1 < ℓ' := by omega
  have hq0 : 0 < q := (Fact.out : q.Prime).pos
  have hℓ0 : 0 < ℓ' := (Fact.out : ℓ'.Prime).pos
  haveI : NeZero (q * ℓ') := ⟨Nat.mul_ne_zero hq0.ne' hℓ0.ne'⟩
  have hι' := S3GlueKit.exists_emb k₀ (q * ℓ') ξ hξ
  haveI hGfin : Finite ↥G := (ModularCurve.FullLevel.AuxLevel.finite_and_natCard_dvd_of_eq_closure_isLevelAutAt_gamma q hq M' hqM'
    ℓ' hℓ'3 hℓ'q hℓ'M ↥k₀ ξ hξ (by simpa only [Nat.cast_mul] using hι') Kℓ hKℓ G hG).1
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
      (⟨ModularCurve.qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ g), hgKall g hg⟩ : ↥Kℓ) ∈ K₀ :=
    fun g hg => S3GlueKit.qExpand_coeffEmb_mem_of_coeffLaw k₀ ℓ' Kℓ K₀ (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))
      F₀ φ hφ1 g _ rfl (hvF₀ g hg) (hgKall g hg)
  refine ⟨?_, ?_⟩
  · exact S3GlueKit.igusaPole_transport (k := ↥k₀) (L := LaurentSeries ↥k₀) (F := ↥(fieldBar q M')) Kℓ K₀ F₀ φ
      (fun c : ↥k₀ => (c : (AlgebraicClosure ℚ)) ∈ A) π₀ ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) B₀ B hB
      (ModularCurve.qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ jq))
      (IntermediateField.inclusion hle ⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩)
      (hgKall jq (modularFunctionField_le_full M' (jq_mem M'))) (hK₀mem jq (modularFunctionField_le_full M' (jq_mem M')))
      (hφ5 jq (modularFunctionField_le_full M' (jq_mem M')) _ _) hE1'
  · exact S3GlueKit.overPole_transport (k := ↥k₀) (L := LaurentSeries ↥k₀) (F := ↥(fieldBar q M')) Kℓ K₀ F₀ φ
      (fun c : ↥k₀ => (c : (AlgebraicClosure ℚ)) ∈ A) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) B₀ B hB s
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
      (fun (s' : ↥W) (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
          (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers) =>
        (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          ((s' : ↥W) : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring)
      (fun (s' : ↥W) (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
          (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers)
          (c : ↥k₀) (hc : (c : (AlgebraicClosure ℚ)) ∈ A) =>
        residue A ⟨(c : (AlgebraicClosure ℚ)), hc⟩ =
          ((s' : ↥W) : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩))
      (fun g : LaurentSeries ℚ => ModularCurve.qExpand ↥k₀ ℓ' (coeffEmb ↥k₀ g))
      (fun (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M') =>
        IntermediateField.inclusion hle ⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩)
      hgKall hK₀mem (fun g hg hgK hF => hφ5 g hg hgK hF) hE3'

end S_ModularCurve_FullLevel_exists_chartPole_otherPole_levelField_of_fixedField_of_algEquiv_framed
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_chartPole_otherPole_levelField_of_fixedField_of_algEquiv_framed (solution)
