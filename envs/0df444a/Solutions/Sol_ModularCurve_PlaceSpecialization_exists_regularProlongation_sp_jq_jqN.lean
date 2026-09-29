-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.exists_regularProlongation_sp_jq_jqN
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/8faa4165-dc62-539b-972c-09674aae888b

import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_AlgebraicCurve_RegularProlongation_eq_integers_of_forall_mem_adjoin_iff
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isCuspidal_of_not_isAffineGeomPlace_reduceFst
import Theorems.Thm_AlgebraicCurve_RegularProlongation_mem_adjoin_iff_mem_integers_iff_of_transcendental_residue
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_relfinrank_full_eq_dedekindPsi
import Theorems.Thm_ModularCurve_relfinrank_laurentBaseChange_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_geomAut_atkinLehner_comp_legs
import Theorems.Thm_ModularCurve_exists_isAtkinLehnerAutFull_of_prime_of_not_dvd
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_AlgebraicCurve_fundamentalIdentityAlong
import Theorems.Thm_ModularCurve_finiteAlong_heckeAlphaBar_of_prime
import Theorems.Thm_AlgebraicCurve_separableAlong_of_charZero
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_dedekindPsi_mul_of_coprime
import Theorems.Thm_ModularCurve_dedekindPsi_prime
import Theorems.Thm_AlgebraicCurve_finrankAlong_eq_relfinrank_fieldRange
import Theorems.Thm_ModularCurve_laurentBaseChange_modularFunctionFieldFull_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_relfinrank_modularFunctionFieldFullC_mul_dedekindPsi
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_ModularCurve_exists_place_restrictAlong_heckeAlphaBar_eq_and_hasValue_tInfty
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Theorems.Thm_AlgebraicCurve_Place_smul_restrictAlong
import Theorems.Thm_AlgebraicCurve_Place_ramificationIndexAlong_smul
import Theorems.Thm_ModularCurve_PlaceSpecialization_isStrictFst_atkinLehnerBar_smul_iff
import Theorems.Thm_ModularCurve_PlaceSpecialization_isStrictSnd_atkinLehnerBar_smul_iff
import Theorems.Thm_ModularCurve_PlaceSpecialization_reduceFst_atkinLehnerBar_smul
import Theorems.Thm_ModularCurve_PlaceSpecialization_reduceSnd_atkinLehnerBar_smul
import Theorems.Thm_ModularCurve_finrankAlong_heckeBetaBar
import Theorems.Thm_ModularCurve_finiteAlong_heckeBetaBar_of_prime
import Definitions.Def_ModularCurve_AtkinLehner
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isInftySide_or_isZeroSide_of_isCuspidal
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_not_isInftySide_of_isZeroSide
import Definitions.Def_ModularCurve_CharLFrobeniusGeomLevel
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_FrobeniusModL
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_exists_regularProlongation_sp_jq_jqN
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk"
p2m_attr_erase "simp" "ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option Elab.async false
p2m_open "AlgebraicCurve IsLocalRing ModularCurve~dedekindPsi_pos"

set_option autoImplicit false

namespace RoofB

section Kit

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F F' : Type*} [Field F] [Field F'] [Algebra L F] [Algebra L F']
variable {Fb Fb' : Type*} [Field Fb] [Field Fb']
variable [Algebra (ResidueField A) Fb] [Algebra (ResidueField A) Fb']

private theorem isUnit_mk_iff (V : ValuationSubring F) {x : F} (hx : x ∈ V) :
    IsUnit (⟨x, hx⟩ : V) ↔ x ≠ 0 ∧ x⁻¹ ∈ V := by
  constructor
  · rintro ⟨u, hu⟩
    have key : (⟨x, hx⟩ : V) * ↑u⁻¹ = 1 := by
      rw [← hu]
      exact u.mul_inv
    have keyF := congrArg Subtype.val key
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at keyF
    refine ⟨left_ne_zero_of_mul_eq_one keyF, ?_⟩
    rw [inv_eq_of_mul_eq_one_right keyF]
    exact SetLike.coe_mem _
  · rintro ⟨hne, hinv⟩
    exact ⟨⟨⟨x, hx⟩, ⟨x⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hne),
      Subtype.ext (inv_mul_cancel₀ hne)⟩, rfl⟩

private theorem residue_congr (R : RegularProlongation A F Fb) {x y : R.integers}
    (h : (x : F) = (y : F)) : R.residue x = R.residue y := by
  rw [Subtype.ext h]

private def comapIntegers (φ : F →ₐ[L] F') (R' : RegularProlongation A F' Fb') :
    ValuationSubring F :=
  R'.integers.comap (φ : F →+* F')

private theorem mem_comapIntegers {φ : F →ₐ[L] F'} {R' : RegularProlongation A F' Fb'} {x : F} :
    x ∈ comapIntegers φ R' ↔ φ x ∈ R'.integers :=
  ValuationSubring.mem_comap

private theorem isUnit_comap_iff (φ : F →ₐ[L] F') (R' : RegularProlongation A F' Fb') {x : F}
    (hx : x ∈ comapIntegers φ R') :
    IsUnit (⟨x, hx⟩ : comapIntegers φ R') ↔
      IsUnit (⟨φ x, mem_comapIntegers.mp hx⟩ : R'.integers) := by
  rw [isUnit_mk_iff, isUnit_mk_iff]
  have hinj : Function.Injective φ := fun a b h => (φ : F →+* F').injective h
  constructor
  · rintro ⟨hne, hinv⟩
    exact ⟨fun h => hne (hinj (by rw [h, map_zero])),
      by rw [← map_inv₀]; exact mem_comapIntegers.mp hinv⟩
  · rintro ⟨hne, hinv⟩
    exact ⟨fun h => hne (by rw [h, map_zero]),
      mem_comapIntegers.mpr (by rw [map_inv₀]; exact hinv)⟩

private def toIntegers (φ : F →ₐ[L] F') (R' : RegularProlongation A F' Fb') :
    comapIntegers φ R' →+* R'.integers where
  toFun x := ⟨φ x, mem_comapIntegers.mp x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

private theorem coe_toIntegers (φ : F →ₐ[L] F') (R' : RegularProlongation A F' Fb')
    (x : comapIntegers φ R') : ((toIntegers φ R' x : R'.integers) : F') = φ x := rfl

private scoped instance isLocalHom_toIntegers (φ : F →ₐ[L] F') (R' : RegularProlongation A F' Fb') :
    IsLocalHom (toIntegers φ R') := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨x, hx0⟩ := x
  exact (isUnit_comap_iff φ R' hx0).mpr hx

private def comapConst (φ : F →ₐ[L] F') (R' : RegularProlongation A F' Fb') :
    A →+* comapIntegers φ R' where
  toFun a := ⟨algebraMap L F a, mem_comapIntegers.mpr (by
    rw [AlgHom.commutes]
    exact (R'.algebraMap_mem_iff a).mpr a.2)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

private theorem coe_comapConst (φ : F →ₐ[L] F') (R' : RegularProlongation A F' Fb') (a : A) :
    ((comapConst φ R' a : comapIntegers φ R') : F) = algebraMap L F a := rfl

private scoped instance isLocalHom_comapConst (φ : F →ₐ[L] F') (R' : RegularProlongation A F' Fb') :
    IsLocalHom (comapConst φ R') := by
  refine ⟨fun a ha => ?_⟩
  have ha' := (isUnit_comap_iff φ R' (comapConst φ R' a).2).mp ha
  rw [isUnit_mk_iff] at ha'
  obtain ⟨hne, hinv⟩ := ha'
  rw [coe_comapConst, AlgHom.commutes] at hne hinv
  rw [← map_inv₀, R'.algebraMap_mem_iff] at hinv
  have hne' : (a : L) ≠ 0 := fun h => hne (by rw [h, map_zero])
  have key : IsUnit (⟨(a : L), a.2⟩ : A) := (isUnit_mk_iff A a.2).mpr ⟨hne', hinv⟩
  exact key

private noncomputable scoped instance comapAlgebra (φ : F →ₐ[L] F')
    (R' : RegularProlongation A F' Fb') :
    Algebra (ResidueField A) (ResidueField (comapIntegers φ R')) :=
  (ResidueField.map (comapConst φ R')).toAlgebra

private theorem comapAlgebra_algebraMap (φ : F →ₐ[L] F') (R' : RegularProlongation A F' Fb')
    (a : A) :
    algebraMap (ResidueField A) (ResidueField (comapIntegers φ R')) (residue A a)
      = residue (comapIntegers φ R') (comapConst φ R' a) := by
  show ResidueField.map (comapConst φ R') (residue A a) = _
  rw [ResidueField.map_residue]

private noncomputable def _root_.RoofB.comap (φ : F →ₐ[L] F') (R' : RegularProlongation A F' Fb') :
    RegularProlongation A F (ResidueField (comapIntegers φ R')) where
  integers := comapIntegers φ R'
  residue := IsLocalRing.residue (comapIntegers φ R')
  algebraMap_mem_iff x := by
    rw [mem_comapIntegers, AlgHom.commutes, R'.algebraMap_mem_iff]
  residue_surjective := IsLocalRing.residue_surjective
  ker_residue := IsLocalRing.ker_residue
  residue_algebraMap a := by
    rw [comapAlgebra_algebraMap]
    rfl
  exists_smul_mem f hf := by
    have hf' : φ f ≠ 0 := fun h0 => hf ((φ : F →+* F').injective (by rw [map_zero]; exact h0))
    obtain ⟨c, hc, hres⟩ := R'.exists_smul_mem (φ f) hf'
    have hc' : c • f ∈ comapIntegers φ R' := by
      rw [mem_comapIntegers, map_smul φ c f]
      exact hc
    refine ⟨c, hc', ?_⟩
    rw [residue_ne_zero_iff_isUnit, isUnit_comap_iff]
    have hu := R'.isUnit_of_residue_ne_zero hres
    have heq : (⟨c • φ f, hc⟩ : R'.integers) = ⟨φ (c • f), mem_comapIntegers.mp hc'⟩ :=
      Subtype.ext (map_smul φ c f).symm
    rwa [heq] at hu

p2m_export "RoofB" "comap"
private theorem comap_residue (φ : F →ₐ[L] F') (R' : RegularProlongation A F' Fb')
    (x : comapIntegers φ R') : (comap φ R').residue x = residue (comapIntegers φ R') x := rfl

private noncomputable def residueLift (φ : F →ₐ[L] F') (R' : RegularProlongation A F' Fb') :
    ResidueField (comapIntegers φ R') →ₐ[ResidueField A] Fb' :=
  haveI : IsLocalHom (R'.residue.comp (toIntegers φ R')) :=
    ⟨fun x hx => isUnit_of_map_unit (toIntegers φ R') x
      (R'.isUnit_of_residue_ne_zero (f := toIntegers φ R' x) hx.ne_zero)⟩
  { ResidueField.lift (R'.residue.comp (toIntegers φ R')) with
    commutes' := fun c => by
      obtain ⟨a, rfl⟩ := residue_surjective c
      show ResidueField.lift _ (algebraMap _ _ (residue A a)) = _
      rw [comapAlgebra_algebraMap, ResidueField.lift_residue_apply, RingHom.comp_apply,
        ← R'.residue_algebraMap a]
      exact residue_congr R' (by
        show φ (algebraMap L F (a : L)) = algebraMap L F' (a : L)
        exact φ.commutes _) }

private theorem residueLift_residue (φ : F →ₐ[L] F') (R' : RegularProlongation A F' Fb')
    (x : comapIntegers φ R') :
    residueLift φ R' ((comap φ R').residue x) = R'.residue (toIntegers φ R' x) := rfl

private theorem transcendental_comap_residue (φ : F →ₐ[L] F')
    (R' : RegularProlongation A F' Fb') (x : comapIntegers φ R')
    (h : Transcendental (ResidueField A) (R'.residue (toIntegers φ R' x))) :
    Transcendental (ResidueField A) ((comap φ R').residue x) := by
  intro halg
  apply h
  rw [← residueLift_residue]
  exact halg.algHom (residueLift φ R')

private def transfer (R : RegularProlongation A F Fb) (φ : F →ₐ[L] F')
    (R' : RegularProlongation A F' Fb') (hV : comapIntegers φ R' = R.integers) :
    R.integers →+* R'.integers :=
  (toIntegers φ R').comp
    { toFun := fun x => ⟨x, by rw [hV]; exact x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

private theorem coe_transfer (R : RegularProlongation A F Fb) (φ : F →ₐ[L] F')
    (R' : RegularProlongation A F' Fb') (hV : comapIntegers φ R' = R.integers)
    (x : R.integers) : ((transfer R φ R' hV x : R'.integers) : F') = φ x := rfl

private theorem ker_le_ker_transfer (R : RegularProlongation A F Fb) (φ : F →ₐ[L] F')
    (R' : RegularProlongation A F' Fb') (hV : comapIntegers φ R' = R.integers) :
    RingHom.ker R.residue ≤ RingHom.ker (R'.residue.comp (transfer R φ R' hV)) := by
  intro x hx
  rw [R.ker_residue] at hx
  rw [RingHom.mem_ker, RingHom.comp_apply, ← RingHom.mem_ker, R'.ker_residue]
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
  intro hu
  apply hx
  have hx' : (x : F) ∈ comapIntegers φ R' := by rw [hV]; exact x.2
  have hu' : IsUnit (⟨(x : F), hx'⟩ : comapIntegers φ R') := (isUnit_comap_iff φ R' hx').mpr hu
  rw [isUnit_mk_iff] at hu'
  obtain ⟨hne, hinv⟩ := hu'
  rw [hV] at hinv
  have key : IsUnit (⟨(x : F), x.2⟩ : R.integers) :=
    (isUnit_mk_iff R.integers x.2).mpr ⟨hne, hinv⟩
  exact key

private noncomputable def residueHom (R : RegularProlongation A F Fb) (φ : F →ₐ[L] F')
    (R' : RegularProlongation A F' Fb') (hV : comapIntegers φ R' = R.integers) :
    Fb →ₐ[ResidueField A] Fb' :=
  { (R.residue.liftOfSurjective R.residue_surjective)
      ⟨R'.residue.comp (transfer R φ R' hV), ker_le_ker_transfer R φ R' hV⟩ with
    commutes' := fun c => by
      obtain ⟨a, rfl⟩ := residue_surjective c
      show (R.residue.liftOfSurjective R.residue_surjective) _ (algebraMap _ _ (residue A a)) = _
      rw [← R.residue_algebraMap a, RingHom.liftOfSurjective_comp_apply,
        ← R'.residue_algebraMap a]
      exact residue_congr R' (by
        show φ (algebraMap L F (a : L)) = algebraMap L F' (a : L)
        exact φ.commutes _) }

private theorem residueHom_residue (R : RegularProlongation A F Fb) (φ : F →ₐ[L] F')
    (R' : RegularProlongation A F' Fb') (hV : comapIntegers φ R' = R.integers) (x : R.integers) :
    residueHom R φ R' hV (R.residue x) = R'.residue (transfer R φ R' hV x) :=
  RingHom.liftOfSurjective_comp_apply R.residue R.residue_surjective _ x

end Kit

section Degree

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

private theorem comap_val_adjoin_simple (M : IntermediateField K E) (z : M) :
    (IntermediateField.adjoin K ({(z : E)} : Set E)).comap M.val
      = IntermediateField.adjoin K ({z} : Set M) := by
  ext y
  change (y : E) ∈ IntermediateField.adjoin K ({(z : E)} : Set E) ↔ _
  rw [← IntermediateField.lift_adjoin_simple K M z]
  exact IntermediateField.mem_lift y

private theorem finrank_adjoin_simple_eq_relfinrank (M : IntermediateField K E) (z : M) :
    Module.finrank (IntermediateField.adjoin K ({z} : Set M)) M
      = IntermediateField.relfinrank (IntermediateField.adjoin K ({(z : E)} : Set E)) M := by
  rw [← comap_val_adjoin_simple M z, IntermediateField.finrank_comap,
    IntermediateField.fieldRange_val]

end Degree

section LevelN

private theorem dedekindPsi_pos (N : ℕ) [NeZero N] : 0 < dedekindPsi N := by
  unfold dedekindPsi
  have h1 : (1 : ℕ) ∈ N.divisors.filter Squarefree :=
    Finset.mem_filter.mpr ⟨Nat.one_mem_divisors.mpr (NeZero.ne N), squarefree_one⟩
  have hle : N / 1 ≤ ∑ d ∈ N.divisors with Squarefree d, N / d :=
    Finset.single_le_sum (f := fun d => N / d) (fun _ _ => Nat.zero_le _) h1
  rw [Nat.div_one] at hle
  exact lt_of_lt_of_le (Nat.pos_of_ne_zero (NeZero.ne N)) hle

private noncomputable def jB (N : ℕ) [NeZero N] : modularFunctionFieldBar N :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full N (jq_mem N))⟩

private noncomputable def jNB (N : ℕ) [NeZero N] : modularFunctionFieldBar N :=
  ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N (dvd_refl N))⟩

private theorem coe_jB (N : ℕ) [NeZero N] (A : ValuationSubring (AlgebraicClosure ℚ)) :
    ((jB N : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ))
      = coeffMap A.subtype (jqModC A) := by
  show coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (jqModC ℚ) = _
  rw [coeffMap_jqModC, coeffMap_jqModC]

private theorem coe_jB' (N : ℕ) [NeZero N] :
    ((jB N : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ))
      = jqModC (AlgebraicClosure ℚ) := by
  show coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (jqModC ℚ) = _
  rw [coeffMap_jqModC]

private theorem coe_jNB (N : ℕ) [NeZero N] (A : ValuationSubring (AlgebraicClosure ℚ)) :
    ((jNB N : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ))
      = coeffMap A.subtype (jqNModC A N) := by
  show coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (jqNModC ℚ N) = _
  rw [coeffMap_jqNModC, coeffMap_jqNModC]

private theorem finrank_adjoin_jB (N : ℕ) [NeZero N] :
    Module.finrank (IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({jB N} : Set (modularFunctionFieldBar N))) (modularFunctionFieldBar N)
      = dedekindPsi N := by
  refine (finrank_adjoin_simple_eq_relfinrank (modularFunctionFieldBar N) (jB N)).trans ?_
  change IntermediateField.relfinrank (IntermediateField.adjoin (AlgebraicClosure ℚ)
      ({coeffEmb (AlgebraicClosure ℚ) jq} : Set (LaurentSeries (AlgebraicClosure ℚ))))
    (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) = _
  rw [relfinrank_laurentBaseChange_modularFunctionFieldFull, relfinrank_full_eq_dedekindPsi]

private theorem finrank_adjoin_jqModC (k : Type*) [Field k] (N : ℕ) [NeZero N]
    (p : ℕ) [Fact p.Prime] [CharP k p] (hpN : ¬ p ∣ N) :
    Module.finrank (IntermediateField.adjoin k
        ({(⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N)} :
          Set (modularFunctionFieldC k N))) (modularFunctionFieldC k N)
      = dedekindPsi N := by
  refine (finrank_adjoin_simple_eq_relfinrank (modularFunctionFieldC k N)
    ⟨jqModC k, jqModC_mem k N⟩).trans ?_
  change IntermediateField.relfinrank (IntermediateField.adjoin k
      ({jqModC k} : Set (LaurentSeries k))) (modularFunctionFieldC k N) = _
  exact relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi k N p hpN

private theorem transcendental_jqModC_mem (k : Type*) [Field k] (N : ℕ) [NeZero N] :
    Transcendental k (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) :=
  fun halg => transcendental_jqModC k (halg.algHom (modularFunctionFieldC k N).val)

private theorem transcendental_jqNModC (k : Type*) [Field k] (n : ℕ) [NeZero n] :
    Transcendental k (jqNModC k n) := fun halg =>
  transcendental_jqModC k ((isAlgebraic_algHom_iff (qExpandAlgHomC k n)
    (fun _ _ h => qExpand_injective n h) (a := jqModC k)).mp halg)

end LevelN

section Rigidity

variable (N : ℕ) [NeZero N]
variable (A : ValuationSubring (AlgebraicClosure ℚ))

private theorem comapIntegers_eq
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField ↥A) p] (hpN : ¬ p ∣ N)
    (R₁ : RegularProlongation A (modularFunctionFieldBar N)
      (modularFunctionFieldC (ResidueField ↥A) N))
    (hj : ∃ h : jB N ∈ R₁.integers,
      R₁.residue ⟨_, h⟩ = ⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) N⟩)
    {Fb' : Type*} [Field Fb'] [Algebra (ResidueField ↥A) Fb'] {M : ℕ} [NeZero M]
    (R' : RegularProlongation A (modularFunctionFieldBar M) Fb')
    (φ : modularFunctionFieldBar N →ₐ[AlgebraicClosure ℚ] modularFunctionFieldBar M)
    (hφj : φ (jB N) ∈ R'.integers)
    (htr : Transcendental (ResidueField ↥A) (R'.residue ⟨φ (jB N), hφj⟩)) :
    comapIntegers φ R' = R₁.integers := by
  obtain ⟨hj1, hj2⟩ := hj
  have hf₂ : jB N ∈ (comap φ R').integers := mem_comapIntegers.mpr hφj
  have htr₁ : Transcendental (ResidueField ↥A) (R₁.residue ⟨jB N, hj1⟩) := by
    rw [hj2]
    exact transcendental_jqModC_mem (ResidueField ↥A) N
  have htr₂ : Transcendental (ResidueField ↥A) ((comap φ R').residue ⟨jB N, hf₂⟩) := by
    apply transcendental_comap_residue φ R' ⟨jB N, hf₂⟩
    have e : R'.residue (toIntegers φ R' ⟨jB N, hf₂⟩) = R'.residue ⟨φ (jB N), hφj⟩ :=
      residue_congr R' rfl
    rw [e]
    exact htr
  have hV : ∀ e : modularFunctionFieldBar N,
      e ∈ IntermediateField.adjoin (AlgebraicClosure ℚ) {((⟨jB N, hj1⟩ : R₁.integers) :
        modularFunctionFieldBar N)} → (e ∈ comapIntegers φ R' ↔ e ∈ R₁.integers) :=
    fun e he =>
      (RegularProlongation.mem_adjoin_iff_mem_integers_iff_of_transcendental_residue A R₁
        (comap φ R') (jB N) hj1 hf₂ htr₁ htr₂ e he).symm
  have hdeg1 : Module.finrank (IntermediateField.adjoin (AlgebraicClosure ℚ)
      ({((⟨jB N, hj1⟩ : R₁.integers) : modularFunctionFieldBar N)} :
        Set (modularFunctionFieldBar N))) (modularFunctionFieldBar N) = dedekindPsi N :=
    finrank_adjoin_jB N
  have hdeg2 : Module.finrank (IntermediateField.adjoin (ResidueField ↥A)
      ({R₁.residue ⟨jB N, hj1⟩} : Set (modularFunctionFieldC (ResidueField ↥A) N)))
      (modularFunctionFieldC (ResidueField ↥A) N) = dedekindPsi N := by
    rw [hj2]
    exact finrank_adjoin_jqModC (ResidueField ↥A) N p hpN
  exact RegularProlongation.eq_integers_of_forall_mem_adjoin_iff A R₁ ⟨jB N, hj1⟩ htr₁
    (by rw [hdeg2]; exact dedekindPsi_pos N) (by rw [hdeg1, hdeg2]) (comapIntegers φ R') hV

private theorem residue_map_eq
    (R₁ : RegularProlongation A (modularFunctionFieldBar N)
      (modularFunctionFieldC (ResidueField ↥A) N))
    {Fb' : Type*} [Field Fb'] [Algebra (ResidueField ↥A) Fb'] {M : ℕ} [NeZero M]
    (R' : RegularProlongation A (modularFunctionFieldBar M) Fb')
    (φ : modularFunctionFieldBar N →ₐ[AlgebraicClosure ℚ] modularFunctionFieldBar M)
    (φC : modularFunctionFieldC (ResidueField ↥A) N →ₐ[ResidueField ↥A] Fb')
    (hV : comapIntegers φ R' = R₁.integers)
    (h1 : ∃ (h : jB N ∈ R₁.integers) (h' : φ (jB N) ∈ R'.integers),
      R₁.residue ⟨_, h⟩ = ⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) N⟩ ∧
      R'.residue ⟨_, h'⟩ = φC (R₁.residue ⟨_, h⟩))
    (h2 : ∃ (h : jNB N ∈ R₁.integers) (h' : φ (jNB N) ∈ R'.integers),
      R₁.residue ⟨_, h⟩ = ⟨jqNModC (ResidueField ↥A) N, jqNModC_mem (ResidueField ↥A) N⟩ ∧
      R'.residue ⟨_, h'⟩ = φC (R₁.residue ⟨_, h⟩))
    (f : R₁.integers) :
    ∃ h : φ (f : modularFunctionFieldBar N) ∈ R'.integers,
      R'.residue ⟨_, h⟩ = φC (R₁.residue f) := by
  obtain ⟨hj1, hj1', hjres, hjφ⟩ := h1
  obtain ⟨hn1, hn1', hnres, hnφ⟩ := h2
  have hτ : residueHom R₁ φ R' hV = φC := by
    refine IntermediateField.algHom_ext_of_eq_adjoin (ResidueField ↥A)
      (s := ({jqModC (ResidueField ↥A), jqNModC (ResidueField ↥A) N} :
        Set (LaurentSeries (ResidueField ↥A))))
      rfl (fun x hx => ?_)
    rcases hx with rfl | rfl
    · have e1 : residueHom R₁ φ R' hV (R₁.residue ⟨jB N, hj1⟩) = φC (R₁.residue ⟨jB N, hj1⟩) := by
        rw [residueHom_residue, ← hjφ]
        exact residue_congr R' rfl
      rw [hjres] at e1
      exact e1
    · have e1 : residueHom R₁ φ R' hV (R₁.residue ⟨jNB N, hn1⟩)
          = φC (R₁.residue ⟨jNB N, hn1⟩) := by
        rw [residueHom_residue, ← hnφ]
        exact residue_congr R' rfl
      rw [hnres] at e1
      exact e1
  have hmem : φ (f : modularFunctionFieldBar N) ∈ R'.integers := by
    have : (f : modularFunctionFieldBar N) ∈ comapIntegers φ R' := by rw [hV]; exact f.2
    exact mem_comapIntegers.mp this
  refine ⟨hmem, ?_⟩
  rw [← hτ, residueHom_residue]
  exact residue_congr R' rfl

end Rigidity

section Onto

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F F' : Type*} [Field F] [Field F'] [Algebra L F] [Algebra L F']
variable {Fb Fb' : Type*} [Field Fb] [Field Fb']
variable [Algebra (ResidueField A) Fb']

private noncomputable def res (φ : F →ₐ[L] F') (R' : RegularProlongation A F' Fb')
    (ι : Fb' →+* Fb) : comapIntegers φ R' →+* Fb :=
  ι.comp (R'.residue.comp (toIntegers φ R'))

private theorem res_apply (φ : F →ₐ[L] F') (R' : RegularProlongation A F' Fb') (ι : Fb' →+* Fb)
    (x : comapIntegers φ R') : res φ R' ι x = ι (R'.residue (toIntegers φ R' x)) := rfl

private theorem res_ne_zero_iff (φ : F →ₐ[L] F') (R' : RegularProlongation A F' Fb')
    (ι : Fb' →+* Fb) (x : comapIntegers φ R') : res φ R' ι x ≠ 0 ↔ IsUnit x := by
  rw [res_apply, map_ne_zero_iff ι ι.injective]
  constructor
  · intro h
    exact (isUnit_comap_iff φ R' x.2).mpr (R'.isUnit_of_residue_ne_zero h)
  · intro h
    exact R'.residue_ne_zero_of_isUnit ((isUnit_comap_iff φ R' x.2).mp h)

variable [Algebra (ResidueField A) Fb]

private noncomputable def ontoPro (φ : F →ₐ[L] F') (R' : RegularProlongation A F' Fb')
    (ι : Fb' →+* Fb) (hsurj : Function.Surjective (res φ R' ι))
    (hι : ∀ a : A, ι (algebraMap (ResidueField A) Fb' (residue A a))
      = algebraMap (ResidueField A) Fb (residue A a)) :
    RegularProlongation A F Fb where
  integers := comapIntegers φ R'
  residue := res φ R' ι
  algebraMap_mem_iff x := by
    rw [mem_comapIntegers, AlgHom.commutes, R'.algebraMap_mem_iff]
  residue_surjective := hsurj
  ker_residue := by
    ext x
    rw [RingHom.mem_ker, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      ← res_ne_zero_iff φ R' ι x]
    exact not_not.symm
  residue_algebraMap a := by
    rw [res_apply]
    have e : R'.residue (toIntegers φ R' ⟨algebraMap L F a, by
          rw [mem_comapIntegers, AlgHom.commutes, R'.algebraMap_mem_iff]; exact a.2⟩)
        = R'.residue ⟨algebraMap L F' a, (R'.algebraMap_mem_iff a).mpr a.2⟩ :=
      residue_congr R' (by rw [coe_toIntegers]; exact φ.commutes _)
    rw [e, R'.residue_algebraMap a]
    exact hι a
  exists_smul_mem f hf := by
    have hf' : φ f ≠ 0 := fun h0 => hf ((φ : F →+* F').injective (by rw [map_zero]; exact h0))
    obtain ⟨c, hc, hres⟩ := R'.exists_smul_mem (φ f) hf'
    have hc' : c • f ∈ comapIntegers φ R' := by
      rw [mem_comapIntegers, map_smul φ c f]
      exact hc
    refine ⟨c, hc', ?_⟩
    rw [res_ne_zero_iff, isUnit_comap_iff]
    have hu := R'.isUnit_of_residue_ne_zero hres
    have heq : (⟨c • φ f, hc⟩ : R'.integers) = ⟨φ (c • f), mem_comapIntegers.mp hc'⟩ :=
      Subtype.ext (map_smul φ c f).symm
    rwa [heq] at hu

private theorem ontoPro_integers (φ : F →ₐ[L] F') (R' : RegularProlongation A F' Fb')
    (ι : Fb' →+* Fb) (hsurj : Function.Surjective (res φ R' ι))
    (hι : ∀ a : A, ι (algebraMap (ResidueField A) Fb' (residue A a))
      = algebraMap (ResidueField A) Fb (residue A a)) :
    (ontoPro φ R' ι hsurj hι).integers = comapIntegers φ R' := rfl

private theorem ontoPro_residue (φ : F →ₐ[L] F') (R' : RegularProlongation A F' Fb')
    (ι : Fb' →+* Fb) (hsurj : Function.Surjective (res φ R' ι))
    (hι : ∀ a : A, ι (algebraMap (ResidueField A) Fb' (residue A a))
      = algebraMap (ResidueField A) Fb (residue A a)) (x : (ontoPro φ R' ι hsurj hι).integers) :
    (ontoPro φ R' ι hsurj hι).residue x = ι (R'.residue (toIntegers φ R' x)) := rfl

end Onto

section OntoLevelN

variable (N : ℕ) [NeZero N]
variable (A : ValuationSubring (AlgebraicClosure ℚ))

private theorem res_surjective
    {Fb' : Type*} [Field Fb'] [Algebra (ResidueField ↥A) Fb'] {M : ℕ} [NeZero M]
    (R' : RegularProlongation A (modularFunctionFieldBar M) Fb')
    (φ : modularFunctionFieldBar N →ₐ[AlgebraicClosure ℚ] modularFunctionFieldBar M)
    (ι : Fb' →+* modularFunctionFieldC (ResidueField ↥A) N)
    (hι : ∀ a : A, ι (algebraMap (ResidueField ↥A) Fb' (residue A a))
      = algebraMap (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N) (residue A a))
    (hjφ : φ (jB N) ∈ R'.integers)
    (hjres : ι (R'.residue ⟨φ (jB N), hjφ⟩)
      = ⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) N⟩)
    (hnφ : φ (jNB N) ∈ R'.integers)
    (hnres : ι (R'.residue ⟨φ (jNB N), hnφ⟩)
      = ⟨jqNModC (ResidueField ↥A) N, jqNModC_mem (ResidueField ↥A) N⟩) :
    Function.Surjective (res φ R' ι) := by
  intro x
  suffices key : ∀ (y : LaurentSeries (ResidueField ↥A)),
      y ∈ modularFunctionFieldC (ResidueField ↥A) N →
        ∃ f : comapIntegers φ R',
          ((res φ R' ι f : modularFunctionFieldC (ResidueField ↥A) N)
            : LaurentSeries (ResidueField ↥A)) = y by
    obtain ⟨f, hf⟩ := key x x.2
    exact ⟨f, Subtype.ext hf⟩
  intro y hy
  change y ∈ Subfield.closure (Set.range (algebraMap (ResidueField ↥A)
      (LaurentSeries (ResidueField ↥A))) ∪
    {jqModC (ResidueField ↥A), jqNModC (ResidueField ↥A) N}) at hy
  induction hy using Subfield.closure_induction with
  | mem z hz =>
      rcases hz with ⟨c, rfl⟩ | hz
      ·
        obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
        refine ⟨comapConst φ R' a, ?_⟩
        have e : R'.residue (toIntegers φ R' (comapConst φ R' a))
            = R'.residue ⟨algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar M) a,
                (R'.algebraMap_mem_iff a).mpr a.2⟩ :=
          residue_congr R' (by rw [coe_toIntegers, coe_comapConst]; exact φ.commutes _)
        rw [res_apply, e, R'.residue_algebraMap a, hι a]
        rfl
      · rcases hz with rfl | hz
        ·
          refine ⟨⟨jB N, mem_comapIntegers.mpr hjφ⟩, ?_⟩
          have e : R'.residue (toIntegers φ R' ⟨jB N, mem_comapIntegers.mpr hjφ⟩)
              = R'.residue ⟨φ (jB N), hjφ⟩ := residue_congr R' rfl
          rw [res_apply, e, hjres]
        ·
          rw [Set.mem_singleton_iff] at hz
          subst hz
          refine ⟨⟨jNB N, mem_comapIntegers.mpr hnφ⟩, ?_⟩
          have e : R'.residue (toIntegers φ R' ⟨jNB N, mem_comapIntegers.mpr hnφ⟩)
              = R'.residue ⟨φ (jNB N), hnφ⟩ := residue_congr R' rfl
          rw [res_apply, e, hnres]
  | one => exact ⟨1, by rw [map_one]; rfl⟩
  | add z w _ _ hz hw =>
      obtain ⟨f, hf⟩ := hz
      obtain ⟨g, hg⟩ := hw
      exact ⟨f + g, by rw [map_add, IntermediateField.coe_add, hf, hg]⟩
  | neg z _ hz =>
      obtain ⟨f, hf⟩ := hz
      exact ⟨-f, by rw [map_neg, IntermediateField.coe_neg, hf]⟩
  | inv z _ hz =>
      obtain ⟨f, hf⟩ := hz
      by_cases hz0 : z = 0
      · refine ⟨0, ?_⟩
        rw [map_zero, hz0, inv_zero]
        rfl
      · have hne : res φ R' ι f ≠ 0 := by
          intro h0
          apply hz0
          rw [← hf, h0]
          rfl
        obtain ⟨u, hu⟩ := (res_ne_zero_iff φ R' ι f).mp hne
        refine ⟨(↑u⁻¹ : comapIntegers φ R'), ?_⟩
        have hmul : res φ R' ι (↑u) * res φ R' ι (↑u⁻¹) = 1 := by
          rw [← map_mul, Units.mul_inv, map_one]
        rw [eq_inv_of_mul_eq_one_right hmul, IntermediateField.coe_inv, hu, hf]
  | mul z w _ _ hz hw =>
      obtain ⟨f, hf⟩ := hz
      obtain ⟨g, hg⟩ := hw
      exact ⟨f * g, by rw [map_mul, IntermediateField.coe_mul, hf, hg]⟩

end OntoLevelN

section Fibres

p2m_open "ModularCurve.PlaceSpecialization~IsInftySide~jFun~tInfty~tZero~IsCuspidal~IsZeroSide"

private theorem fibreCount_strictFst {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (hqN : ¬ q ∣ N) (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hV : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.sp V))
      ≠ P.sp V) :
    ∃ W₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      W₀.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα = V ∧
      P.IsStrictFst W₀ ∧
      W₀.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) = 1 ∧
      ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
        W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα = V →
        P.IsStrictFst W → W = W₀ := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

  obtain ⟨σf, hσf⟩ :=
    exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N q (Fact.out : q.Prime) hqN
  have hAL := isAtkinLehnerAutFull_atkinLehnerInvolutionFull N q ⟨σf, hσf⟩
  have hlegs := geomAut_atkinLehner_comp_legs (AlgebraicClosure ℚ) N q
    (atkinLehnerInvolutionFull N q) hAL
  have hwα : ∀ x, ProlongationTuple.atkinLehnerBar N q
        (heckeAlphaBar (AlgebraicClosure ℚ) N q x)
      = heckeBetaBar (AlgebraicClosure ℚ) N q x :=
    fun x => AlgHom.congr_fun hlegs.1 x

  have h₁ : ∀ x, heckeAlphaBar (AlgebraicClosure ℚ) N q ((1 :
        modularFunctionFieldBar N ≃ₐ[AlgebraicClosure ℚ] modularFunctionFieldBar N) x)
      = (ProlongationTuple.atkinLehnerBar N q)⁻¹
          (heckeBetaBar (AlgebraicClosure ℚ) N q x) := by
    intro x
    rw [AlgEquiv.one_apply, ← hwα x]
    exact ((ProlongationTuple.atkinLehnerBar N q).symm_apply_apply _).symm
  have h₂ : ∀ x, heckeBetaBar (AlgebraicClosure ℚ) N q ((1 :
        modularFunctionFieldBar N ≃ₐ[AlgebraicClosure ℚ] modularFunctionFieldBar N) x)
      = ProlongationTuple.atkinLehnerBar N q
          (heckeAlphaBar (AlgebraicClosure ℚ) N q x) := by
    intro x
    rw [AlgEquiv.one_apply]
    exact (hwα x).symm

  obtain ⟨W₀', hWβ, hWsp, hWe, hWu⟩ := P.d2 V hV

  refine ⟨(ProlongationTuple.atkinLehnerBar N q)⁻¹ • W₀', ?_, ?_, ?_, ?_⟩
  ·
    rw [Place.smul_restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q)
      (heckeBetaBar (AlgebraicClosure ℚ) N q) hα hβ
      ((ProlongationTuple.atkinLehnerBar N q)⁻¹) 1 h₁ W₀', hWβ, one_smul]
  ·
    have hSnd : P.IsStrictSnd W₀' := by
      have hrFst : P.reduceFst W₀' = frobOnPlacesGeomLevel k N data hKr (P.sp V) := hWsp
      have hrSnd : P.reduceSnd W₀' = P.sp V := congrArg P.sp hWβ
      refine ⟨?_, ?_⟩
      · show P.reduceFst W₀'
          = frobOnPlacesGeomLevel k N data hKr (P.reduceSnd W₀')
        rw [hrFst, hrSnd]
      · show frobOnPlacesGeomLevel k N data hKr
            (frobOnPlacesGeomLevel k N data hKr (P.reduceSnd W₀')) ≠ P.reduceSnd W₀'
        rw [hrSnd]
        exact hV
    have hiff := isStrictSnd_atkinLehnerBar_smul_iff P hqN
      ((ProlongationTuple.atkinLehnerBar N q)⁻¹ • W₀')
    rw [smul_inv_smul] at hiff
    exact hiff.mp hSnd
  ·
    rw [Place.ramificationIndexAlong_smul (heckeAlphaBar (AlgebraicClosure ℚ) N q)
      (heckeBetaBar (AlgebraicClosure ℚ) N q)
      ((ProlongationTuple.atkinLehnerBar N q)⁻¹) 1 h₁ W₀']
    exact hWe
  ·
    intro W hWα hWstrict
    have hUβ : (ProlongationTuple.atkinLehnerBar N q • W).restrictAlong
        (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ = V := by
      rw [Place.smul_restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q)
        (heckeAlphaBar (AlgebraicClosure ℚ) N q) hβ hα
        (ProlongationTuple.atkinLehnerBar N q) 1 h₂ W, hWα, one_smul]
    have hUsp : P.sp ((ProlongationTuple.atkinLehnerBar N q • W).restrictAlong
        (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα)
        = frobOnPlacesGeomLevel k N data hKr (P.sp V) := by
      have h3 : P.reduceFst (ProlongationTuple.atkinLehnerBar N q • W) = P.reduceSnd W :=
        reduceFst_atkinLehnerBar_smul P hqN W
      have h4 : P.reduceFst W = P.sp V := congrArg P.sp hWα
      have h5 := hWstrict.1
      show P.reduceFst (ProlongationTuple.atkinLehnerBar N q • W)
        = frobOnPlacesGeomLevel k N data hKr (P.sp V)
      rw [h3, ← h5, h4]
    have hU := hWu (ProlongationTuple.atkinLehnerBar N q • W) hUβ hUsp
    have hW0 : ProlongationTuple.atkinLehnerBar N q
        • ((ProlongationTuple.atkinLehnerBar N q)⁻¹ • W₀') = W₀' :=
      smul_inv_smul _ _
    exact MulAction.injective (ProlongationTuple.atkinLehnerBar N q) (hU.trans hW0.symm)

private theorem ord_jQFun_of_inftySide {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hW : ProlongationTuple.IsInftySide P W)
    (hj : ProlongationTuple.jFun N q ≠ 0) :
    W.ord (ProlongationTuple.jQFun N q)
      = (q : ℤ) * W.ord (ProlongationTuple.jFun N q) := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  obtain ⟨-, τ, hτ, hval⟩ := hW
  have hτ0 : (τ : AlgebraicClosure ℚ) ≠ 0 := by
    intro h0
    have hz : τ = 0 := Subtype.ext h0
    rw [hz, map_zero] at hτ
    exact zero_ne_one hτ
  have ht0 : W.ord (ProlongationTuple.tInfty N q) = 0 := hval.ord_eq_zero hτ0
  have htne : ProlongationTuple.tInfty N q ≠ 0 := by
    intro h0
    have hu := (hval.isUnit hτ0).ne_zero
    exact hu (Subtype.ext h0)
  have hfq : ProlongationTuple.jFun N q ^ q ≠ 0 := pow_ne_zero _ hj
  have hfactor : ProlongationTuple.jQFun N q
      = ProlongationTuple.tInfty N q * ProlongationTuple.jFun N q ^ q := by
    rw [show ProlongationTuple.tInfty N q
        = ProlongationTuple.jQFun N q / ProlongationTuple.jFun N q ^ q from rfl,
      div_mul_cancel₀ _ hfq]
  rw [hfactor, Place.ord_mul (v := W) (f := ProlongationTuple.tInfty N q)
      (g := ProlongationTuple.jFun N q ^ q) htne hfq, ht0, zero_add,
    show ProlongationTuple.jFun N q ^ q
      = ProlongationTuple.jFun N q ^ ((q : ℕ) : ℤ) from (zpow_natCast _ _).symm,
    Place.ord_zpow]

private theorem ord_jFun_of_zeroSide {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hW : ProlongationTuple.IsZeroSide P W)
    (hjq : ProlongationTuple.jQFun N q ≠ 0) :
    W.ord (ProlongationTuple.jFun N q)
      = (q : ℤ) * W.ord (ProlongationTuple.jQFun N q) := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  obtain ⟨-, τ, hτ, hval⟩ := hW
  have hτ0 : (τ : AlgebraicClosure ℚ) ≠ 0 := by
    intro h0
    have hz : τ = 0 := Subtype.ext h0
    rw [hz, map_zero] at hτ
    exact zero_ne_one hτ
  have ht0 : W.ord (ProlongationTuple.tZero N q) = 0 := hval.ord_eq_zero hτ0
  have htne : ProlongationTuple.tZero N q ≠ 0 := by
    intro h0
    have hu := (hval.isUnit hτ0).ne_zero
    exact hu (Subtype.ext h0)
  have hfq : ProlongationTuple.jQFun N q ^ q ≠ 0 := pow_ne_zero _ hjq
  have hfactor : ProlongationTuple.jFun N q
      = ProlongationTuple.tZero N q * ProlongationTuple.jQFun N q ^ q := by
    rw [show ProlongationTuple.tZero N q
        = ProlongationTuple.jFun N q / ProlongationTuple.jQFun N q ^ q from rfl,
      div_mul_cancel₀ _ hfq]
  rw [hfactor, Place.ord_mul (v := W) (f := ProlongationTuple.tZero N q)
      (g := ProlongationTuple.jQFun N q ^ q) htne hfq, ht0, zero_add,
    show ProlongationTuple.jQFun N q ^ q
      = ProlongationTuple.jQFun N q ^ ((q : ℕ) : ℤ) from (zpow_natCast _ _).symm,
    Place.ord_zpow]

end Fibres

section Frob

variable (K : Type*) [Field K] (N : ℕ) [NeZero N] {q : ℕ} [Fact q.Prime] [CharP K q]
variable [PerfectField K]
variable (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)

private theorem exists_pow_eq_frobeniusGeomLevel (g : modularFunctionFieldC K N) :
    ∃ h : modularFunctionFieldC K N, frobeniusGeomLevel K N data hKr g = h ^ q := by
  refine ⟨coeffRingAut N (frobeniusEquiv K q).symm g, Subtype.ext ?_⟩
  rw [frobeniusGeomLevel_apply_coe, IntermediateField.coe_pow, coe_coeffRingAut_apply,
    pow_char_eq_coeffMap_frobenius_qExpand q, ← coeffMap_qExpand, coeffMap_coeffMap,
    coeffMap_congr (frobenius_comp_frobeniusEquiv_symm K q), coeffMap_id]

private theorem ord_frobeniusGeomLevel (w : Place K (modularFunctionFieldC K N))
    (g : modularFunctionFieldC K N) :
    w.ord (frobeniusGeomLevel K N data hKr g)
      = q * (frobOnPlacesGeomLevel K N data hKr w).ord g := by
  obtain ⟨e, he0, hediv, hord⟩ := exists_ramification_frobenius K N data hKr w
  have hq : q.Prime := Fact.out
  have hcases : e = 1 ∨ e = q := (Nat.dvd_prime hq).mp (Int.natCast_dvd_natCast.mp hediv)
  rcases hcases with he1 | heq
  · exfalso
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible
      (frobOnPlacesGeomLevel K N data hKr w).toValuationSubring
    have hπ1 : (frobOnPlacesGeomLevel K N data hKr w).ord (π : modularFunctionFieldC K N) = 1 :=
      Place.ord_coe_irreducible _ hπ
    obtain ⟨h, hh⟩ := exists_pow_eq_frobeniusGeomLevel K N data hKr (π : modularFunctionFieldC K N)
    have key := hord (π : modularFunctionFieldC K N)
    rw [he1, hπ1, hh, ← zpow_natCast, Place.ord_zpow] at key

    have hdvd : (q : ℤ) ∣ 1 := ⟨w.ord h, by rw [key]; norm_num⟩
    have hq1 : (q : ℤ) = 1 := Int.eq_one_of_dvd_one (Int.natCast_nonneg q) hdvd
    exact hq.one_lt.ne' (by exact_mod_cast hq1)
  · rw [hord g, heq]

private theorem ord_frobeniusGeomLevel_of_fixed (v : Place K (modularFunctionFieldC K N))
    (hv : frobOnPlacesGeomLevel K N data hKr (frobOnPlacesGeomLevel K N data hKr v) = v)
    (g : modularFunctionFieldC K N) :
    (frobOnPlacesGeomLevel K N data hKr v).ord (frobeniusGeomLevel K N data hKr g)
      = q * v.ord g := by
  rw [ord_frobeniusGeomLevel K N data hKr (frobOnPlacesGeomLevel K N data hKr v) g, hv]

end Frob

section Ctx

variable (N q : ℕ) [NeZero N] [Fact q.Prime]
variable (A : ValuationSubring (AlgebraicClosure ℚ))

private theorem mem_alpha_jB :
    coeffMap A.subtype (jqModC A) ∈ modularFunctionFieldBar (N * q) := by
  rw [← coe_jB N A, ← coe_heckeAlphaBar N q (jB N)]
  exact SetLike.coe_mem _

private theorem mem_alpha_jNB :
    coeffMap A.subtype (jqNModC A N) ∈ modularFunctionFieldBar (N * q) := by
  rw [← coe_jNB N A, ← coe_heckeAlphaBar N q (jNB N)]
  exact SetLike.coe_mem _

private theorem mem_beta_jB :
    coeffMap A.subtype (qExpand A q (jqModC A)) ∈ modularFunctionFieldBar (N * q) := by
  rw [coeffMap_qExpand, ← coe_jB N A, ← coe_heckeBetaBar N q (jB N)]
  exact SetLike.coe_mem _

private theorem alpha_jB_eq : heckeAlphaBar (AlgebraicClosure ℚ) N q (jB N)
    = ⟨coeffMap A.subtype (jqModC A), mem_alpha_jB N q A⟩ :=
  Subtype.ext (by rw [coe_heckeAlphaBar, coe_jB N A])

private theorem alpha_jNB_eq : heckeAlphaBar (AlgebraicClosure ℚ) N q (jNB N)
    = ⟨coeffMap A.subtype (jqNModC A N), mem_alpha_jNB N q A⟩ :=
  Subtype.ext (by rw [coe_heckeAlphaBar, coe_jNB N A])

private theorem beta_jB_eq : heckeBetaBar (AlgebraicClosure ℚ) N q (jB N)
    = ⟨coeffMap A.subtype (qExpand A q (jqModC A)), mem_beta_jB N q A⟩ :=
  Subtype.ext (by
    rw [coe_heckeBetaBar, coe_jB N A]
    exact (coeffMap_qExpand A.subtype q (jqModC A)).symm)

private theorem alpha_jB_eq_jFun :
    heckeAlphaBar (AlgebraicClosure ℚ) N q (jB N)
      = ModularCurve.PlaceSpecialization.ProlongationTuple.jFun N q :=
  Subtype.ext (by rw [coe_heckeAlphaBar]; rfl)

private theorem beta_jB_eq_jQFun :
    heckeBetaBar (AlgebraicClosure ℚ) N q (jB N)
      = ModularCurve.PlaceSpecialization.ProlongationTuple.jQFun N q :=
  Subtype.ext (by
    rw [coe_heckeBetaBar, coe_jB' N]
    show _ = coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (qExpand ℚ q (jqModC ℚ))
    rw [coeffMap_qExpand, coeffMap_jqModC])

variable [CharP (ResidueField ↥A) q]
variable (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
variable (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
variable (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
variable (P : PlaceSpecialization A q N data hKr (ResidueField ↥A) (IsLocalRing.residue ↥A) hα hβ)
variable (R : PlaceSpecialization.ProlongationTuple P)

private theorem hasPrincipalDivisors_bar (M : ℕ) [NeZero M] :
    HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar M) :=
  hasPrincipalDivisors_modularFunctionFieldBar_unconditional M

attribute [local instance] hasPrincipalDivisors_bar

private theorem alpha_jB_mem_residue :
    ∃ h : heckeAlphaBar (AlgebraicClosure ℚ) N q (jB N) ∈ R.R₁.integers,
      ((R.R₁.residue ⟨_, h⟩ : modularFunctionFieldFullC (ResidueField ↥A) N)
        : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A) := by
  obtain ⟨hint, hres⟩ := R.residue₁_coeffMap (jqModC A) (mem_alpha_jB N q A)
  have hmem : heckeAlphaBar (AlgebraicClosure ℚ) N q (jB N) ∈ R.R₁.integers := by
    rw [alpha_jB_eq N q A]
    exact hint
  refine ⟨hmem, ?_⟩
  rw [residue_congr R.R₁ (show ((⟨_, hmem⟩ : R.R₁.integers) : modularFunctionFieldBar (N * q))
      = ((⟨_, hint⟩ : R.R₁.integers) : modularFunctionFieldBar (N * q))
      from alpha_jB_eq N q A), hres, coeffMap_jqModC]

private theorem alpha_jNB_mem_residue :
    ∃ h : heckeAlphaBar (AlgebraicClosure ℚ) N q (jNB N) ∈ R.R₁.integers,
      ((R.R₁.residue ⟨_, h⟩ : modularFunctionFieldFullC (ResidueField ↥A) N)
        : LaurentSeries (ResidueField ↥A)) = jqNModC (ResidueField ↥A) N := by
  obtain ⟨hint, hres⟩ := R.residue₁_coeffMap (jqNModC A N) (mem_alpha_jNB N q A)
  have hmem : heckeAlphaBar (AlgebraicClosure ℚ) N q (jNB N) ∈ R.R₁.integers := by
    rw [alpha_jNB_eq N q A]
    exact hint
  refine ⟨hmem, ?_⟩
  rw [residue_congr R.R₁ (show ((⟨_, hmem⟩ : R.R₁.integers) : modularFunctionFieldBar (N * q))
      = ((⟨_, hint⟩ : R.R₁.integers) : modularFunctionFieldBar (N * q))
      from alpha_jNB_eq N q A), hres, coeffMap_jqNModC]

private theorem beta_jB_mem_residue :
    ∃ h : heckeBetaBar (AlgebraicClosure ℚ) N q (jB N) ∈ R.R₁.integers,
      ((R.R₁.residue ⟨_, h⟩ : modularFunctionFieldFullC (ResidueField ↥A) N)
        : LaurentSeries (ResidueField ↥A))
          = qExpand (ResidueField ↥A) q (jqModC (ResidueField ↥A)) := by
  obtain ⟨hint, hres⟩ := R.residue₁_coeffMap (qExpand A q (jqModC A)) (mem_beta_jB N q A)
  have hmem : heckeBetaBar (AlgebraicClosure ℚ) N q (jB N) ∈ R.R₁.integers := by
    rw [beta_jB_eq N q A]
    exact hint
  refine ⟨hmem, ?_⟩
  rw [residue_congr R.R₁ (show ((⟨_, hmem⟩ : R.R₁.integers) : modularFunctionFieldBar (N * q))
      = ((⟨_, hint⟩ : R.R₁.integers) : modularFunctionFieldBar (N * q))
      from beta_jB_eq N q A), hres, coeffMap_qExpand, coeffMap_jqModC]

private theorem iota_algebraMap (a : A) :
    R.ι (algebraMap (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) N)
        (residue A a))
      = algebraMap (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N) (residue A a) := by
  apply Subtype.ext
  rw [R.ι_coe]
  change coeffMap R.redBar (algebraMap (ResidueField ↥A) (LaurentSeries (ResidueField ↥A))
      (residue A a)) = algebraMap (ResidueField ↥A) (LaurentSeries (ResidueField ↥A)) (residue A a)
  rw [coeffMap_algebraMap, R.redBar_residue]

private theorem iota_residue_alpha_jB :
    R.ι (R.R₁.residue ⟨_, (alpha_jB_mem_residue N q A data hKr hα hβ P R).choose⟩)
      = ⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) N⟩ := by
  apply Subtype.ext
  rw [R.ι_coe, (alpha_jB_mem_residue N q A data hKr hα hβ P R).choose_spec, coeffMap_jqModC]

private theorem iota_residue_alpha_jNB :
    R.ι (R.R₁.residue ⟨_, (alpha_jNB_mem_residue N q A data hKr hα hβ P R).choose⟩)
      = ⟨jqNModC (ResidueField ↥A) N, jqNModC_mem (ResidueField ↥A) N⟩ := by
  apply Subtype.ext
  rw [R.ι_coe, (alpha_jNB_mem_residue N q A data hKr hα hβ P R).choose_spec, coeffMap_jqNModC]

private noncomputable def RN : RegularProlongation A (modularFunctionFieldBar N)
    (modularFunctionFieldC (ResidueField ↥A) N) :=
  ontoPro (heckeAlphaBar (AlgebraicClosure ℚ) N q) R.R₁ R.ι
    (res_surjective N A R.R₁ (heckeAlphaBar (AlgebraicClosure ℚ) N q) R.ι
      (iota_algebraMap N q A data hKr hα hβ P R)
      (alpha_jB_mem_residue N q A data hKr hα hβ P R).choose
      (iota_residue_alpha_jB N q A data hKr hα hβ P R)
      (alpha_jNB_mem_residue N q A data hKr hα hβ P R).choose
      (iota_residue_alpha_jNB N q A data hKr hα hβ P R))
    (iota_algebraMap N q A data hKr hα hβ P R)

private theorem mem_RN_integers (f : modularFunctionFieldBar N) :
    f ∈ (RN N q A data hKr hα hβ P R).integers
      ↔ heckeAlphaBar (AlgebraicClosure ℚ) N q f ∈ R.R₁.integers :=
  mem_comapIntegers

private theorem RN_integers : (RN N q A data hKr hα hβ P R).integers
    = comapIntegers (heckeAlphaBar (AlgebraicClosure ℚ) N q) R.R₁ := rfl

private theorem RN_residue (f : (RN N q A data hKr hα hβ P R).integers) :
    (RN N q A data hKr hα hβ P R).residue f
      = R.ι (R.R₁.residue ⟨heckeAlphaBar (AlgebraicClosure ℚ) N q f,
          (mem_RN_integers N q A data hKr hα hβ P R f).mp f.2⟩) := rfl

private theorem RN_hj : ∃ h : jB N ∈ (RN N q A data hKr hα hβ P R).integers,
    (RN N q A data hKr hα hβ P R).residue ⟨_, h⟩
      = ⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) N⟩ := by
  refine ⟨(mem_RN_integers N q A data hKr hα hβ P R (jB N)).mpr
    (alpha_jB_mem_residue N q A data hKr hα hβ P R).choose, ?_⟩
  rw [RN_residue]
  exact iota_residue_alpha_jB N q A data hKr hα hβ P R

private theorem RN_hjN : ∃ h : jNB N ∈ (RN N q A data hKr hα hβ P R).integers,
    (RN N q A data hKr hα hβ P R).residue ⟨_, h⟩
      = ⟨jqNModC (ResidueField ↥A) N, jqNModC_mem (ResidueField ↥A) N⟩ := by
  refine ⟨(mem_RN_integers N q A data hKr hα hβ P R (jNB N)).mpr
    (alpha_jNB_mem_residue N q A data hKr hα hβ P R).choose, ?_⟩
  rw [RN_residue]
  exact iota_residue_alpha_jNB N q A data hKr hα hβ P R

private noncomputable def betaC : modularFunctionFieldC (ResidueField ↥A) N
    →ₐ[ResidueField ↥A] modularFunctionFieldFullC (ResidueField ↥A) N :=
  (IntermediateField.inclusion (modularFunctionFieldC_le_full (ResidueField ↥A) N)).comp
    (frobeniusGeomLevel (ResidueField ↥A) N data hKr)

private theorem coe_betaC (x : modularFunctionFieldC (ResidueField ↥A) N) :
    ((betaC N q A data hKr x : modularFunctionFieldFullC (ResidueField ↥A) N)
      : LaurentSeries (ResidueField ↥A)) = qExpand (ResidueField ↥A) q x := by
  show ((IntermediateField.inclusion (modularFunctionFieldC_le_full (ResidueField ↥A) N)
    (frobeniusGeomLevel (ResidueField ↥A) N data hKr x) : modularFunctionFieldFullC _ N)
      : LaurentSeries (ResidueField ↥A)) = _
  rw [IntermediateField.coe_inclusion, frobeniusGeomLevel_apply_coe]

private theorem comapIntegers_beta_eq (hqN : ¬ q ∣ N) :
    comapIntegers (heckeBetaBar (AlgebraicClosure ℚ) N q) R.R₁
      = (RN N q A data hKr hα hβ P R).integers := by
  obtain ⟨hφj, hres⟩ := beta_jB_mem_residue N q A data hKr hα hβ P R
  refine comapIntegers_eq N A q hqN (RN N q A data hKr hα hβ P R)
    (RN_hj N q A data hKr hα hβ P R) R.R₁ (heckeBetaBar (AlgebraicClosure ℚ) N q) hφj
    (fun halg => ?_)
  have h2 : IsAlgebraic (ResidueField ↥A)
      (((R.R₁.residue ⟨_, hφj⟩ : modularFunctionFieldFullC (ResidueField ↥A) N))
        : LaurentSeries (ResidueField ↥A)) :=
    halg.algHom (modularFunctionFieldFullC (ResidueField ↥A) N).val
  rw [hres] at h2
  exact transcendental_jqNModC (ResidueField ↥A) q h2

private theorem residue_beta_eq (hqN : ¬ q ∣ N) (f : (RN N q A data hKr hα hβ P R).integers) :
    ∃ h : heckeBetaBar (AlgebraicClosure ℚ) N q (f : modularFunctionFieldBar N) ∈ R.R₁.integers,
      R.R₁.residue ⟨_, h⟩ = betaC N q A data hKr ((RN N q A data hKr hα hβ P R).residue f) := by
  have h1 : ∃ (h : jB N ∈ (RN N q A data hKr hα hβ P R).integers)
      (h' : heckeBetaBar (AlgebraicClosure ℚ) N q (jB N) ∈ R.R₁.integers),
      (RN N q A data hKr hα hβ P R).residue ⟨_, h⟩
          = ⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) N⟩ ∧
        R.R₁.residue ⟨_, h'⟩
          = betaC N q A data hKr ((RN N q A data hKr hα hβ P R).residue ⟨_, h⟩) := by
    obtain ⟨h, hres1⟩ := RN_hj N q A data hKr hα hβ P R
    obtain ⟨h', hres2⟩ := beta_jB_mem_residue N q A data hKr hα hβ P R
    refine ⟨h, h', hres1, ?_⟩
    rw [hres1]
    apply Subtype.ext
    rw [hres2, coe_betaC]
  have h2 : ∃ (h : jNB N ∈ (RN N q A data hKr hα hβ P R).integers)
      (h' : heckeBetaBar (AlgebraicClosure ℚ) N q (jNB N) ∈ R.R₁.integers),
      (RN N q A data hKr hα hβ P R).residue ⟨_, h⟩
          = ⟨jqNModC (ResidueField ↥A) N, jqNModC_mem (ResidueField ↥A) N⟩ ∧
        R.R₁.residue ⟨_, h'⟩
          = betaC N q A data hKr ((RN N q A data hKr hα hβ P R).residue ⟨_, h⟩) := by
    obtain ⟨h, hres1⟩ := RN_hjN N q A data hKr hα hβ P R
    have hn : coeffMap A.subtype (qExpand A q (jqNModC A N)) ∈ modularFunctionFieldBar (N * q) := by
      rw [coeffMap_qExpand, ← coe_jNB N A, ← coe_heckeBetaBar N q (jNB N)]
      exact SetLike.coe_mem _
    obtain ⟨hint, hres⟩ := R.residue₁_coeffMap (qExpand A q (jqNModC A N)) hn
    have e : heckeBetaBar (AlgebraicClosure ℚ) N q (jNB N)
        = ⟨coeffMap A.subtype (qExpand A q (jqNModC A N)), hn⟩ :=
      Subtype.ext (by
        rw [coe_heckeBetaBar, coe_jNB N A]
        exact (coeffMap_qExpand A.subtype q (jqNModC A N)).symm)
    have h' : heckeBetaBar (AlgebraicClosure ℚ) N q (jNB N) ∈ R.R₁.integers := by
      rw [e]
      exact hint
    refine ⟨h, h', hres1, ?_⟩
    rw [hres1]
    apply Subtype.ext
    rw [residue_congr R.R₁ (show ((⟨_, h'⟩ : R.R₁.integers) : modularFunctionFieldBar (N * q))
        = ((⟨_, hint⟩ : R.R₁.integers) : modularFunctionFieldBar (N * q))
        from e), hres, coeffMap_qExpand, coeffMap_jqNModC, coe_betaC]
  exact residue_map_eq N A (RN N q A data hKr hα hβ P R) R.R₁ (heckeBetaBar (AlgebraicClosure ℚ) N q)
    (betaC N q A data hKr) (comapIntegers_beta_eq N q A data hKr hα hβ P R hqN) h1 h2 f

private theorem partI_check (hqN : ¬ q ∣ N) :
    ∃ R₁ : RegularProlongation A (modularFunctionFieldBar N)
        (modularFunctionFieldC (ResidueField ↥A) N),
      (∃ h : jB N ∈ R₁.integers,
        R₁.residue ⟨_, h⟩ = ⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) N⟩) ∧
      (∃ h : jNB N ∈ R₁.integers,
        R₁.residue ⟨_, h⟩ = ⟨jqNModC (ResidueField ↥A) N, jqNModC_mem (ResidueField ↥A) N⟩) ∧
      (∀ f : R₁.integers, heckeAlphaBar (AlgebraicClosure ℚ) N q (f : modularFunctionFieldBar N)
        ∈ R.R₁.integers) ∧
      (∀ f : R₁.integers,
        ∃ h : heckeBetaBar (AlgebraicClosure ℚ) N q (f : modularFunctionFieldBar N)
            ∈ R.R₁.integers,
          ((R.R₁.residue ⟨_, h⟩ : modularFunctionFieldFullC (ResidueField ↥A) N)
              : LaurentSeries (ResidueField ↥A))
            = qExpand (ResidueField ↥A) q ((R₁.residue f : modularFunctionFieldC _ N)
                : LaurentSeries (ResidueField ↥A))) := by
  refine ⟨RN N q A data hKr hα hβ P R, RN_hj N q A data hKr hα hβ P R,
    RN_hjN N q A data hKr hα hβ P R,
    fun f => (mem_RN_integers N q A data hKr hα hβ P R f).mp f.2, fun f => ?_⟩
  obtain ⟨h, e⟩ := residue_beta_eq N q A data hKr hα hβ P R hqN f
  exact ⟨h, by rw [e, coe_betaC]⟩

section Assembly

p2m_open "ModularCurve.PlaceSpecialization~IsInftySide~jFun~tInfty~tZero~IsCuspidal~IsZeroSide ModularCurve.PlaceSpecialization.ProlongationTuple"

open Classical in

private theorem mapDomain_apply_eq_sum {X Y : Type*} (g : X → Y) (D : X →₀ ℤ) (y : Y) :
    Finsupp.mapDomain g D y = ∑ x ∈ D.support with g x = y, D x := by
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finsupp.single_apply]

private theorem atkinLehnerBar_alpha (hqN : ¬ q ∣ N) (f : modularFunctionFieldBar N) :
    ProlongationTuple.atkinLehnerBar N q (heckeAlphaBar (AlgebraicClosure ℚ) N q f)
      = heckeBetaBar (AlgebraicClosure ℚ) N q f := by
  have hq : q.Prime := Fact.out
  have hAL := isAtkinLehnerAutFull_atkinLehnerInvolutionFull N q
    (exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N q hq hqN)
  have h := (geomAut_atkinLehner_comp_legs (AlgebraicClosure ℚ) N q
    (atkinLehnerInvolutionFull N q) hAL).1
  exact AlgHom.congr_fun h f

private theorem alpha_mem₁ (f : (RN N q A data hKr hα hβ P R).integers) :
    heckeAlphaBar (AlgebraicClosure ℚ) N q (f : modularFunctionFieldBar N) ∈ R.R₁.integers :=
  (mem_RN_integers N q A data hKr hα hβ P R f).mp f.2

private theorem alpha_mem₂ (hqN : ¬ q ∣ N) (f : (RN N q A data hKr hα hβ P R).integers) :
    heckeAlphaBar (AlgebraicClosure ℚ) N q (f : modularFunctionFieldBar N) ∈ R.R₂.integers := by
  rw [R.mem_integers₂_iff, atkinLehnerBar_alpha N q hqN]
  exact (residue_beta_eq N q A data hKr hα hβ P R hqN f).choose

private theorem redBar_eq_id : R.redBar = RingHom.id _ :=
  RingHom.ext fun c => by
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
    exact R.redBar_residue a

private theorem coe_iota (y : modularFunctionFieldFullC (ResidueField ↥A) N) :
    ((R.ι y : modularFunctionFieldC (ResidueField ↥A) N) : LaurentSeries (ResidueField ↥A))
      = (y : LaurentSeries (ResidueField ↥A)) := by
  rw [R.ι_coe, redBar_eq_id N q A data hKr hα hβ P R, coeffMap_id]

private theorem residue₁_alpha (f : (RN N q A data hKr hα hβ P R).integers) :
    R.residue₁ ⟨_, alpha_mem₁ N q A data hKr hα hβ P R f⟩
      = (RN N q A data hKr hα hβ P R).residue f := rfl

private theorem residue₂_alpha (hqN : ¬ q ∣ N) (f : (RN N q A data hKr hα hβ P R).integers) :
    R.residue₂ ⟨_, alpha_mem₂ N q A data hKr hα hβ P R hqN f⟩
      = frobeniusGeomLevel (ResidueField ↥A) N data hKr ((RN N q A data hKr hα hβ P R).residue f) := by
  obtain ⟨h, hres⟩ := residue_beta_eq N q A data hKr hα hβ P R hqN f
  have e : R.R₁.residue ⟨ProlongationTuple.atkinLehnerBar N q
        (heckeAlphaBar (AlgebraicClosure ℚ) N q (f : modularFunctionFieldBar N)),
        (R.mem_integersFst_iff _).mpr ((R.mem_integersSnd_iff _).mp
          (alpha_mem₂ N q A data hKr hα hβ P R hqN f))⟩
      = R.R₁.residue ⟨heckeBetaBar (AlgebraicClosure ℚ) N q (f : modularFunctionFieldBar N), h⟩ :=
    residue_congr R.R₁ (atkinLehnerBar_alpha N q hqN f)
  apply Subtype.ext
  rw [residue₂_apply, R.residue₂_eq, e, hres, coe_iota, coe_betaC, frobeniusGeomLevel_apply_coe]

private theorem residue₁_ne (f : (RN N q A data hKr hα hβ P R).integers)
    (hf : (RN N q A data hKr hα hβ P R).residue f ≠ 0) :
    R.R₁.residue ⟨_, alpha_mem₁ N q A data hKr hα hβ P R f⟩ ≠ 0 := by
  intro h0
  apply hf
  show R.ι (R.R₁.residue ⟨_, alpha_mem₁ N q A data hKr hα hβ P R f⟩) = 0
  rw [h0, map_zero]

private theorem residue₂_ne (hqN : ¬ q ∣ N) (f : (RN N q A data hKr hα hβ P R).integers)
    (hf : (RN N q A data hKr hα hβ P R).residue f ≠ 0) :
    R.R₂.residue ⟨_, alpha_mem₂ N q A data hKr hα hβ P R hqN f⟩ ≠ 0 := by
  intro h0
  have h1 : R.residue₂ ⟨_, alpha_mem₂ N q A data hKr hα hβ P R hqN f⟩ = 0 := by
    rw [residue₂_apply, h0, map_zero]
  rw [residue₂_alpha N q A data hKr hα hβ P R hqN f] at h1
  exact hf (frobeniusGeomLevel_injective (ResidueField ↥A) N data hKr (by rw [h1, map_zero]))

private theorem pullbackAlong_div (f : modularFunctionFieldBar N)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hD : ∀ V, D V = V.ord f) :
    ∀ W, Divisor.pullbackAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα D W
      = W.ord (heckeAlphaBar (AlgebraicClosure ℚ) N q f) := by
  intro W
  rw [Divisor.pullbackAlong_apply, hD, Place.ord_restrictAlong (heckeAlphaBar _ N q) hα W f]

open Classical in

private theorem law_generic (hqN : ¬ q ∣ N)
    (fc : ∀ V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      frobOnPlacesGeomLevel (ResidueField ↥A) N data hKr
          (frobOnPlacesGeomLevel (ResidueField ↥A) N data hKr (P.sp V)) ≠ P.sp V →
      ∃ W₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
        W₀.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα = V ∧
        P.IsStrictFst W₀ ∧
        W₀.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) = 1 ∧
        ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
          W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα = V →
          P.IsStrictFst W → W = W₀)
    (f : (RN N q A data hKr hα hβ P R).integers) (hf : (RN N q A data hKr hα hβ P R).residue f ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hD : ∀ V, D V = V.ord (f : modularFunctionFieldBar N))
    (hmodel : R.IsModel)
    (Q : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N))
    (hQ : frobOnPlacesGeomLevel (ResidueField ↥A) N data hKr
      (frobOnPlacesGeomLevel (ResidueField ↥A) N data hKr Q) ≠ Q) :
    Finsupp.mapDomain P.sp D Q = Q.ord ((RN N q A data hKr hα hβ P R).residue f) := by
  have hD' := pullbackAlong_div N q hα (f : modularFunctionFieldBar N) D hD
  have law := hmodel.1 _ (alpha_mem₁ N q A data hKr hα hβ P R f)
    (alpha_mem₂ N q A data hKr hα hβ P R hqN f) (residue₁_ne N q A data hKr hα hβ P R f hf)
    (residue₂_ne N q A data hKr hα hβ P R hqN f hf) _ hD' Q hQ
  rw [residue₁_alpha] at law
  rw [← law, mapDomain_apply_eq_sum, mapDomain_apply_eq_sum]
  symm
  refine Finset.sum_bij (fun W _ => W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα)
    ?_ ?_ ?_ ?_
  ·
    intro W hW
    obtain ⟨hWs, hWQ⟩ := Finset.mem_filter.mp hW
    have hWs' := Finsupp.mem_support_iff.mp hWs
    rw [Finsupp.filter_apply] at hWs'
    by_cases hS : P.IsStrictFst W
    · rw [if_pos hS, hD', Place.ord_restrictAlong (heckeAlphaBar _ N q) hα W] at hWs'
      refine Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr ?_, hWQ⟩
      rw [hD]
      intro h0
      exact hWs' (by rw [h0, mul_zero])
    · exact absurd (if_neg hS) hWs'
  ·
    intro W₁ hW₁ W₂ hW₂ h
    obtain ⟨hW₁s, hW₁Q⟩ := Finset.mem_filter.mp hW₁
    obtain ⟨hW₂s, hW₂Q⟩ := Finset.mem_filter.mp hW₂
    have hS₁ : P.IsStrictFst W₁ := by
      by_contra hS
      exact (Finsupp.mem_support_iff.mp hW₁s) (by rw [Finsupp.filter_apply, if_neg hS])
    have hS₂ : P.IsStrictFst W₂ := by
      by_contra hS
      exact (Finsupp.mem_support_iff.mp hW₂s) (by rw [Finsupp.filter_apply, if_neg hS])
    have hV : frobOnPlacesGeomLevel (ResidueField ↥A) N data hKr
        (frobOnPlacesGeomLevel (ResidueField ↥A) N data hKr
          (P.sp (W₁.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα)))
        ≠ P.sp (W₁.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα) := by
      show frobOnPlacesGeomLevel _ N data hKr (frobOnPlacesGeomLevel _ N data hKr (P.reduceFst W₁))
        ≠ P.reduceFst W₁
      rw [hW₁Q]
      exact hQ
    obtain ⟨W₀, -, -, -, huniq⟩ := fc _ hV
    rw [huniq W₁ rfl hS₁, huniq W₂ h.symm hS₂]
  ·
    intro V hV
    obtain ⟨hVs, hVQ⟩ := Finset.mem_filter.mp hV
    have hV' : frobOnPlacesGeomLevel (ResidueField ↥A) N data hKr
        (frobOnPlacesGeomLevel (ResidueField ↥A) N data hKr (P.sp V)) ≠ P.sp V := by
      rw [hVQ]
      exact hQ
    obtain ⟨W₀, hW₀V, hS₀, he₀, -⟩ := fc V hV'
    refine ⟨W₀, Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr ?_, ?_⟩, hW₀V⟩
    · rw [Finsupp.filter_apply, if_pos hS₀, Divisor.pullbackAlong_apply, he₀, hW₀V, Nat.cast_one,
        one_mul]
      exact Finsupp.mem_support_iff.mp hVs
    · show P.sp (W₀.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα) = Q
      rw [hW₀V, hVQ]
  ·
    intro W hW
    obtain ⟨hWs, hWQ⟩ := Finset.mem_filter.mp hW
    have hS : P.IsStrictFst W := by
      by_contra hS
      exact (Finsupp.mem_support_iff.mp hWs) (by rw [Finsupp.filter_apply, if_neg hS])
    have hV : frobOnPlacesGeomLevel (ResidueField ↥A) N data hKr
        (frobOnPlacesGeomLevel (ResidueField ↥A) N data hKr
          (P.sp (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα)))
        ≠ P.sp (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα) := by
      show frobOnPlacesGeomLevel _ N data hKr (frobOnPlacesGeomLevel _ N data hKr (P.reduceFst W))
        ≠ P.reduceFst W
      rw [hWQ]
      exact hQ
    obtain ⟨W₀, -, -, he₀, huniq⟩ := fc _ hV
    have he : W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) = 1 := by
      rw [huniq W rfl hS]
      exact he₀
    rw [Finsupp.filter_apply, if_pos hS, Divisor.pullbackAlong_apply, he, Nat.cast_one, one_mul]

private theorem val_comp_inclusion_generic {K L : Type*} [Field K] [Field L]
    [Algebra K L] {S T : IntermediateField K L} (h : S ≤ T) :
    T.val.comp (IntermediateField.inclusion h) = S.val :=
  AlgHom.ext fun x => IntermediateField.coe_inclusion h x

private theorem finrankAlong_eq_relfinrank_of_val_comp {K L : Type*} [Field K] [Field L]
    [Algebra K L] {S T : IntermediateField K L} (φ : ↥S →ₐ[K] ↥T)
    (hcomp : T.val.comp φ = S.val) :
    AlgebraicCurve.finrankAlong K φ = IntermediateField.relfinrank S T :=
  (finrankAlong_eq_relfinrank_fieldRange _ _ _).trans
    (congrArg (fun X => IntermediateField.relfinrank X T)
      ((congrArg (fun f => f.fieldRange) hcomp).trans (IntermediateField.fieldRange_val S)))

private theorem finrankAlong_heckeAlphaBar_mul :
    finrankAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N q) * dedekindPsi N
      = dedekindPsi (N * q) := by
  have hNq : ((N * q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne (N * q))
  have h68 : finrankAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N q)
      = IntermediateField.relfinrank (modularFunctionFieldBar N)
          (modularFunctionFieldBar (N * q)) :=
    finrankAlong_eq_relfinrank_of_val_comp (heckeAlphaBar (AlgebraicClosure ℚ) N q)
      (val_comp_inclusion_generic _)
  have e1 : modularFunctionFieldBar N
      = modularFunctionFieldFullC (AlgebraicClosure ℚ) N :=
    laurentBaseChange_modularFunctionFieldFull_eq_modularFunctionFieldFullC
      (AlgebraicClosure ℚ) N
  have e2 : modularFunctionFieldBar (N * q)
      = modularFunctionFieldFullC (AlgebraicClosure ℚ) (N * q) :=
    laurentBaseChange_modularFunctionFieldFull_eq_modularFunctionFieldFullC
      (AlgebraicClosure ℚ) (N * q)
  rw [h68, e1, e2]
  exact (relfinrank_modularFunctionFieldFullC_mul_dedekindPsi (AlgebraicClosure ℚ) N q hNq).1

private theorem finrankAlong_heckeAlphaBar_eq (hqN : ¬ q ∣ N) :
    finrankAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N q) = q + 1 := by
  have hq : q.Prime := Fact.out
  have h := finrankAlong_heckeAlphaBar_mul N q
  rw [dedekindPsi_mul_of_coprime N q ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqN).symm,
    dedekindPsi_prime hq, mul_comm (dedekindPsi N)] at h
  exact Nat.eq_of_mul_eq_mul_right (dedekindPsi_pos N) h

private theorem sum_ramificationIndexAlong_alpha (hqN : ¬ q ∣ N)
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    (∑ W ∈ Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα V,
        (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ)) = q + 1 := by
  have hFI : FundamentalIdentityAlong (AlgebraicClosure ℚ)
      (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα :=
    fundamentalIdentityAlong _ hα (finiteAlong_heckeAlphaBar_of_prime (AlgebraicClosure ℚ) N q)
      (separableAlong_of_charZero _ hα)
  have h := Divisor.degree_pullbackAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα hFI
    (Finsupp.single V 1)
  rw [Divisor.pullbackAlong_single, map_sum] at h
  have h2 : (∑ W ∈ Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα V,
      (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ))
        = finrankAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N q) := by
    simpa [Divisor.degree_single, deg_eq_one_modularFunctionFieldBar] using h
  rw [h2, finrankAlong_heckeAlphaBar_eq N q hqN]
  push_cast
  ring

open Classical in

private theorem law_affine (hqN : ¬ q ∣ N)
    (f : (RN N q A data hKr hα hβ P R).integers) (hf : (RN N q A data hKr hα hβ P R).residue f ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hD : ∀ V, D V = V.ord (f : modularFunctionFieldBar N))
    (hO : R.OrderLawFixed)
    (Q : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N))
    (hQ : frobOnPlacesGeomLevel (ResidueField ↥A) N data hKr
      (frobOnPlacesGeomLevel (ResidueField ↥A) N data hKr Q) = Q)
    (hQa : IsAffineGeomPlace (ResidueField ↥A) N Q) :
    Finsupp.mapDomain P.sp D Q = Q.ord ((RN N q A data hKr hα hβ P R).residue f) := by
  have hD' := pullbackAlong_div N q hα (f : modularFunctionFieldBar N) D hD
  have law := hO _ (alpha_mem₁ N q A data hKr hα hβ P R f)
    (alpha_mem₂ N q A data hKr hα hβ P R hqN f) (residue₁_ne N q A data hKr hα hβ P R f hf)
    (residue₂_ne N q A data hKr hα hβ P R hqN f hf) _ hD' Q hQ hQa
  rw [residue₁_alpha, residue₂_alpha N q A data hKr hα hβ P R hqN f,
    ord_frobeniusGeomLevel_of_fixed _ N data hKr Q hQ] at law

  have key : Finsupp.mapDomain P.reduceFst
        (Divisor.pullbackAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα D) Q
      = (q + 1 : ℤ) * Finsupp.mapDomain P.sp D Q := by
    rw [mapDomain_apply_eq_sum, mapDomain_apply_eq_sum, Finset.mul_sum]
    have hmaps : ∀ W ∈ (Divisor.pullbackAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα
          D).support.filter (fun W => P.reduceFst W = Q),
        W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα
          ∈ D.support.filter (fun V => P.sp V = Q) := by
      intro W hW
      obtain ⟨hWs, hWQ⟩ := Finset.mem_filter.mp hW
      have hWs' := Finsupp.mem_support_iff.mp hWs
      rw [hD', Place.ord_restrictAlong (heckeAlphaBar _ N q) hα W] at hWs'
      refine Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr ?_, hWQ⟩
      rw [hD]
      intro h0
      exact hWs' (by rw [h0, mul_zero])
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl (fun V hV => ?_)
    obtain ⟨hVs, hVQ⟩ := Finset.mem_filter.mp hV

    have hsub : ((Divisor.pullbackAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα
          D).support.filter (fun W => P.reduceFst W = Q)).filter
          (fun W => W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα = V)
        ⊆ Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα V := by
      intro W hW
      exact Place.mem_fiberAlong.mpr (Finset.mem_filter.mp hW).2
    rw [Finset.sum_subset hsub ?_]
    · calc ∑ W ∈ Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα V,
            Divisor.pullbackAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα D W
          = ∑ W ∈ Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα V,
            (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ) * D V := by
              refine Finset.sum_congr rfl (fun W hW => ?_)
              rw [Divisor.pullbackAlong_apply, Place.mem_fiberAlong.mp hW]
        _ = (q + 1 : ℤ) * D V := by
              rw [← Finset.sum_mul, sum_ramificationIndexAlong_alpha N q hα hqN V]
    · intro W hWfib hWnot
      by_contra hne
      apply hWnot
      have hWV := Place.mem_fiberAlong.mp hWfib
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hne, ?_⟩, hWV⟩
      show P.sp (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα) = Q
      rw [hWV, hVQ]
  rw [key] at law
  have hq1 : (q + 1 : ℤ) ≠ 0 := by positivity
  apply mul_left_cancel₀ hq1
  rw [law]
  ring

end Assembly

section Cusps

p2m_open "ModularCurve.PlaceSpecialization~IsInftySide~jFun~tInfty~tZero~IsCuspidal~IsZeroSide ModularCurve.PlaceSpecialization.ProlongationTuple"

open Classical in

private noncomputable def nInf (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) : ℤ :=
  ∑ W ∈ (Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα V).filter
      (fun W => IsInftySide P W),
    (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ)

open Classical in
private theorem nInf_def (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    nInf N q A data hKr hα hβ P V
      = ∑ W ∈ (Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα V).filter
          (fun W => IsInftySide P W),
        (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ) := rfl

open Classical in

private theorem cuspLaw_regroup (hqN : ¬ q ∣ N)
    (f : (RN N q A data hKr hα hβ P R).integers) (hf : (RN N q A data hKr hα hβ P R).residue f ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hD : ∀ V, D V = V.ord (f : modularFunctionFieldBar N))
    (hmodel : R.IsModel)
    (Q : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N))
    (hQc : ¬ IsAffineGeomPlace (ResidueField ↥A) N Q) :
    (∑ V ∈ D.support with P.sp V = Q, D V * nInf N q A data hKr hα hβ P V)
      = Q.ord ((RN N q A data hKr hα hβ P R).residue f) := by
  obtain ⟨⟨c, hc, hcQ⟩, -⟩ :=
    exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace hqN P Q hQc
  have hD' := pullbackAlong_div N q hα (f : modularFunctionFieldBar N) D hD
  have law := hmodel.2.2.1 _ (alpha_mem₁ N q A data hKr hα hβ P R f)
    (alpha_mem₂ N q A data hKr hα hβ P R hqN f) (residue₁_ne N q A data hKr hα hβ P R f hf)
    (residue₂_ne N q A data hKr hα hβ P R hqN f hf) _ hD' c hc
  rw [hcQ, residue₁_alpha] at law
  rw [← law, mapDomain_apply_eq_sum]
  have hmaps : ∀ W ∈ ((Divisor.pullbackAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα D).filter
        (IsInftySide P)).support.filter (fun W => P.reduceFst W = Q),
      W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα
        ∈ D.support.filter (fun V => P.sp V = Q) := by
    intro W hW
    obtain ⟨hWs, hWQ⟩ := Finset.mem_filter.mp hW
    have hWs' := Finsupp.mem_support_iff.mp hWs
    rw [Finsupp.filter_apply] at hWs'
    by_cases hI : IsInftySide P W
    · rw [if_pos hI, hD', Place.ord_restrictAlong (heckeAlphaBar _ N q) hα W] at hWs'
      refine Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr ?_, hWQ⟩
      rw [hD]
      intro h0
      exact hWs' (by rw [h0, mul_zero])
    · exact absurd (if_neg hI) hWs'
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl (fun V hV => ?_)
  obtain ⟨hVs, hVQ⟩ := Finset.mem_filter.mp hV
  rw [nInf_def, Finset.mul_sum]
  symm
  have hsub : (((Divisor.pullbackAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα D).filter
        (IsInftySide P)).support.filter (fun W => P.reduceFst W = Q)).filter
        (fun W => W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα = V)
      ⊆ (Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα V).filter
          (fun W => IsInftySide P W) := by
    intro W hW
    obtain ⟨hWT, hWV⟩ := Finset.mem_filter.mp hW
    obtain ⟨hWs, -⟩ := Finset.mem_filter.mp hWT
    have hI : IsInftySide P W := by
      by_contra hI
      exact (Finsupp.mem_support_iff.mp hWs) (by rw [Finsupp.filter_apply, if_neg hI])
    exact Finset.mem_filter.mpr ⟨Place.mem_fiberAlong.mpr hWV, hI⟩
  calc ∑ W ∈ (((Divisor.pullbackAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα D).filter
          (IsInftySide P)).support.filter (fun W => P.reduceFst W = Q)).filter
          (fun W => W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα = V),
        ((Divisor.pullbackAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα D).filter
          (IsInftySide P)) W
      = ∑ W ∈ (((Divisor.pullbackAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα D).filter
          (IsInftySide P)).support.filter (fun W => P.reduceFst W = Q)).filter
          (fun W => W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα = V),
        D V * (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ) := by
          refine Finset.sum_congr rfl (fun W hW => ?_)
          obtain ⟨hWT, hWV⟩ := Finset.mem_filter.mp hW
          obtain ⟨hWs, -⟩ := Finset.mem_filter.mp hWT
          have hI : IsInftySide P W := by
            by_contra hI
            exact (Finsupp.mem_support_iff.mp hWs) (by rw [Finsupp.filter_apply, if_neg hI])
          rw [Finsupp.filter_apply, if_pos hI, Divisor.pullbackAlong_apply, hWV, mul_comm]
    _ = ∑ W ∈ (Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα V).filter
          (fun W => IsInftySide P W),
        D V * (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ) := by
          refine Finset.sum_subset hsub (fun W hWB hWnot => ?_)
          obtain ⟨hWfib, hI⟩ := Finset.mem_filter.mp hWB
          have hWV := Place.mem_fiberAlong.mp hWfib
          by_contra hne
          apply hWnot
          have hD'W : Divisor.pullbackAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα D W ≠ 0 := by
            rw [Divisor.pullbackAlong_apply, hWV, mul_comm]
            exact hne
          refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr ?_, ?_⟩, hWV⟩
          · rw [Finsupp.filter_apply, if_pos hI]
            exact hD'W
          · show P.sp (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα) = Q
            rw [hWV, hVQ]

open Classical in

private theorem law_cusp (hqN : ¬ q ∣ N)
    (f : (RN N q A data hKr hα hβ P R).integers) (hf : (RN N q A data hKr hα hβ P R).residue f ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hD : ∀ V, D V = V.ord (f : modularFunctionFieldBar N))
    (hmodel : R.IsModel)
    (Q : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N))
    (hQc : ¬ IsAffineGeomPlace (ResidueField ↥A) N Q)
    (hn : ∀ V ∈ D.support, P.sp V = Q → nInf N q A data hKr hα hβ P V = 1) :
    Finsupp.mapDomain P.sp D Q = Q.ord ((RN N q A data hKr hα hβ P R).residue f) := by
  rw [← cuspLaw_regroup N q A data hKr hα hβ P R hqN f hf D hD hmodel Q hQc, mapDomain_apply_eq_sum]
  refine Finset.sum_congr rfl (fun V hV => ?_)
  obtain ⟨hVs, hVQ⟩ := Finset.mem_filter.mp hV
  rw [hn V hVs hVQ, mul_one]

private theorem ord_eq_zero_of_isUnit {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {x : F} {hx : x ∈ v.toValuationSubring}
    (hu : IsUnit (⟨x, hx⟩ : v.toValuationSubring)) : v.ord x = 0 := by
  obtain ⟨u, hu⟩ := hu
  have h := Place.ord_coe_unit v u
  rw [show ((u : v.toValuationSubring) : F) = x from congrArg Subtype.val hu] at h
  exact h

private theorem ord_pos_of_mem_maximalIdeal {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {x : F} (hx : x ∈ v.toValuationSubring) (hx0 : x ≠ 0)
    (hm : (⟨x, hx⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring) :
    0 < v.ord x := by
  rcases lt_trichotomy 0 (v.ord x) with h | h | h
  · exact h
  · exfalso
    have hinv : x⁻¹ ∈ v.toValuationSubring :=
      Place.mem_of_ord_nonneg v (inv_ne_zero hx0) (by rw [Place.ord_inv, ← h, neg_zero])
    have hu : IsUnit (⟨x, hx⟩ : v.toValuationSubring) :=
      ⟨⟨⟨x, hx⟩, ⟨x⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hx0), Subtype.ext (inv_mul_cancel₀ hx0)⟩,
        rfl⟩
    exact (IsLocalRing.mem_maximalIdeal _).mp hm hu
  · exact absurd (Place.ord_nonneg_of_mem v hx) (not_le.mpr h)

private theorem jB_sub_algebraMap_ne_zero (c : AlgebraicClosure ℚ) :
    jB N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c ≠ 0 := by
  intro h
  rw [sub_eq_zero] at h
  refine transcendental_jqModC (AlgebraicClosure ℚ) ?_
  rw [← coe_jB' N, h]
  exact isAlgebraic_algebraMap c

private theorem jB_ne_zero : jB N ≠ 0 := by
  have h := jB_sub_algebraMap_ne_zero N 0
  rw [map_zero, sub_zero] at h
  exact h

private theorem exists_ord_jB_sub_pos (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hV : ¬ V.ord (jB N) < 0) :
    ∃ c : AlgebraicClosure ℚ,
      0 < V.ord (jB N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c) := by
  have hmem : jB N ∈ V.toValuationSubring :=
    Place.mem_of_ord_nonneg V (jB_ne_zero N) (not_lt.mp hV)
  have hsurj : Function.Surjective (algebraMap (AlgebraicClosure ℚ) V.ResidueField) := by
    haveI : Module.Finite (AlgebraicClosure ℚ) V.ResidueField :=
      Module.finite_of_finrank_pos (by
        rw [show Module.finrank (AlgebraicClosure ℚ) V.ResidueField = V.deg from rfl,
          deg_eq_one_modularFunctionFieldBar N V]
        exact Nat.one_pos)
    exact (IsAlgClosed.algebraMap_bijective_of_isIntegral
      (k := AlgebraicClosure ℚ) (K := V.ResidueField)).2
  obtain ⟨c, ⟨hmem', hres⟩, -⟩ := Place.exists_hasValue_of_surjective V hsurj hmem
  refine ⟨c, ?_⟩
  have hsub : jB N - algebraMap _ _ c ∈ V.toValuationSubring := sub_mem hmem (V.algebraMap_mem' c)
  apply ord_pos_of_mem_maximalIdeal V hsub (jB_sub_algebraMap_ne_zero N c)
  rw [← IsLocalRing.residue_eq_zero_iff]
  have e : (⟨jB N - algebraMap _ _ c, hsub⟩ : V.toValuationSubring)
      = ⟨jB N, hmem⟩ - ⟨algebraMap _ _ c, V.algebraMap_mem' c⟩ := rfl
  rw [e, map_sub, sub_eq_zero, hres]
  exact (V.residue_algebraMap c).symm

private theorem cuspidal_of_pole (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hV : V.ord (jB N) < 0) (a : A) :
    V.ord (jB N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
      (a : AlgebraicClosure ℚ)) ≤ 0 := by
  by_contra h
  rw [not_le] at h
  have hmem : jB N - algebraMap _ _ (a : AlgebraicClosure ℚ) ∈ V.toValuationSubring :=
    Place.mem_of_ord_nonneg V (jB_sub_algebraMap_ne_zero N _) h.le
  have hj : jB N ∈ V.toValuationSubring := by
    have e : jB N = (jB N - algebraMap _ _ (a : AlgebraicClosure ℚ))
        + algebraMap _ _ (a : AlgebraicClosure ℚ) := by ring
    rw [e]
    exact add_mem hmem (V.algebraMap_mem' _)
  exact absurd (Place.ord_nonneg_of_mem V hj) (not_le.mpr hV)

private theorem cuspidal_of_ord_sub_pos (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    {c : AlgebraicClosure ℚ} (hc : c ∉ A)
    (hV : 0 < V.ord (jB N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c))
    (a : A) :
    V.ord (jB N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
      (a : AlgebraicClosure ℚ)) ≤ 0 := by
  have hca : c - a ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    exact hc (h ▸ a.2)
  have hmem1 : jB N - algebraMap _ _ c ∈ V.toValuationSubring :=
    Place.mem_of_ord_nonneg V (jB_sub_algebraMap_ne_zero N c) hV.le
  have hmax : (⟨jB N - algebraMap _ _ c, hmem1⟩ : V.toValuationSubring)
      ∈ IsLocalRing.maximalIdeal V.toValuationSubring := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact absurd (ord_eq_zero_of_isUnit V hu) hV.ne'
  have hunit : IsUnit (⟨algebraMap _ _ (c - a), V.algebraMap_mem' (c - a)⟩ : V.toValuationSubring) :=
    ⟨⟨⟨algebraMap _ _ (c - a), V.algebraMap_mem' (c - a)⟩,
      ⟨algebraMap _ _ (c - a)⁻¹, V.algebraMap_mem' (c - a)⁻¹⟩,
      Subtype.ext (by
        show algebraMap _ (modularFunctionFieldBar N) (c - a) * algebraMap _ _ (c - a)⁻¹ = 1
        rw [← map_mul, mul_inv_cancel₀ hca, map_one]),
      Subtype.ext (by
        show algebraMap _ (modularFunctionFieldBar N) (c - a)⁻¹ * algebraMap _ _ (c - a) = 1
        rw [← map_mul, inv_mul_cancel₀ hca, map_one])⟩, rfl⟩
  have hmem2 : jB N - algebraMap _ _ (a : AlgebraicClosure ℚ) ∈ V.toValuationSubring := by
    have e : jB N - algebraMap _ _ (a : AlgebraicClosure ℚ)
        = (jB N - algebraMap _ _ c) + algebraMap _ _ (c - a) := by
      rw [map_sub]; ring
    rw [e]
    exact add_mem hmem1 (V.algebraMap_mem' _)
  have hsum : IsUnit (⟨jB N - algebraMap _ _ (a : AlgebraicClosure ℚ), hmem2⟩ : V.toValuationSubring) := by
    by_contra hnu
    have hm : (⟨jB N - algebraMap _ _ (a : AlgebraicClosure ℚ), hmem2⟩ : V.toValuationSubring)
        ∈ IsLocalRing.maximalIdeal V.toValuationSubring :=
      (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have hdiff := Ideal.sub_mem _ hm hmax
    have e : (⟨jB N - algebraMap _ _ (a : AlgebraicClosure ℚ), hmem2⟩ : V.toValuationSubring)
        - ⟨jB N - algebraMap _ _ c, hmem1⟩
        = ⟨algebraMap _ _ (c - a), V.algebraMap_mem' (c - a)⟩ :=
      Subtype.ext (by
        show (jB N - algebraMap _ (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ))
            - (jB N - algebraMap _ _ c) = algebraMap _ _ (c - a)
        rw [map_sub]; ring)
    rw [e] at hdiff
    exact (IsLocalRing.mem_maximalIdeal _).mp hdiff hunit
  exact (ord_eq_zero_of_isUnit V hsum).le

include hα in

private theorem ramificationIndexAlong_alpha_pos
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    0 < W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) := by
  letI := algebraAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q)
  haveI := isScalarTower_along (heckeAlphaBar (AlgebraicClosure ℚ) N q)
  haveI := isIntegral_along (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα
  exact Place.ramificationIndex_pos (F := modularFunctionFieldBar N) W

private theorem one_le_nInf (hqN : ¬ q ∣ N) (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hV : ∀ a : A, V.ord (jB N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
      (a : AlgebraicClosure ℚ)) ≤ 0) :
    1 ≤ nInf N q A data hKr hα hβ P V := by
  classical
  obtain ⟨c₀, hc₀V, τ, hτ, hval⟩ :=
    exists_place_restrictAlong_heckeAlphaBar_eq_and_hasValue_tInfty q A N (ResidueField ↥A)
      (IsLocalRing.residue ↥A) data hKr hα hqN V hV
  have hcusp : IsCuspidal P c₀ := by
    intro a
    have e : jFun N q - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
          (a : AlgebraicClosure ℚ)
        = heckeAlphaBar (AlgebraicClosure ℚ) N q
            (jB N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
              (a : AlgebraicClosure ℚ)) := by
      rw [map_sub, AlgHom.commutes, alpha_jB_eq_jFun N q]
    rw [e, Place.ord_restrictAlong (heckeAlphaBar _ N q) hα c₀, hc₀V]
    exact mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg _) (hV a)
  have hI : IsInftySide P c₀ := ⟨hcusp, τ, hτ, hval⟩
  rw [nInf_def]
  have hmem : c₀ ∈ (Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα V).filter
      (fun W => IsInftySide P W) :=
    Finset.mem_filter.mpr ⟨Place.mem_fiberAlong.mpr hc₀V, hI⟩
  calc (1 : ℤ) ≤ (c₀.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ) := by
        exact_mod_cast ramificationIndexAlong_alpha_pos N q hα c₀
    _ ≤ _ := Finset.single_le_sum (f := fun W : Place (AlgebraicClosure ℚ)
          (modularFunctionFieldBar (N * q)) =>
            (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ))
          (fun W _ => Int.natCast_nonneg _) hmem

private theorem degree_eq_sum (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    Divisor.degree D = ∑ V ∈ D.support, D V := by
  conv_lhs => rw [← Finsupp.sum_single D]
  rw [Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl (fun V _ => ?_)
  rw [Divisor.degree_single, deg_eq_one_modularFunctionFieldBar N V, Nat.cast_one, mul_one]

open Classical in

private noncomputable def nZero (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) : ℤ :=
  ∑ W ∈ (Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα V).filter
      (fun W => IsZeroSide P W),
    (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ)

open Classical in
private theorem nZero_def (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    nZero N q A data hKr hα hβ P V
      = ∑ W ∈ (Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα V).filter
          (fun W => IsZeroSide P W),
        (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ) := rfl

private theorem jFun_ne_zero : jFun N q ≠ 0 := by
  rw [← alpha_jB_eq_jFun N q]
  intro h
  exact jB_ne_zero N ((heckeAlphaBar (AlgebraicClosure ℚ) N q).toRingHom.injective
    (by rw [map_zero]; exact h))

private theorem jQFun_ne_zero : jQFun N q ≠ 0 := by
  rw [← beta_jB_eq_jQFun N q]
  intro h
  exact jB_ne_zero N ((heckeBetaBar (AlgebraicClosure ℚ) N q).toRingHom.injective
    (by rw [map_zero]; exact h))

private theorem isCuspidal_of_pole (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hV : (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα).ord (jB N) < 0) :
    IsCuspidal P W := by
  intro a
  have e : jFun N q - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
        (a : AlgebraicClosure ℚ)
      = heckeAlphaBar (AlgebraicClosure ℚ) N q
          (jB N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
            (a : AlgebraicClosure ℚ)) := by
    rw [map_sub, AlgHom.commutes, alpha_jB_eq_jFun N q]
  rw [e, Place.ord_restrictAlong (heckeAlphaBar _ N q) hα W]
  exact mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg _) (cuspidal_of_pole N A _ hV a)

private theorem sum_ramificationIndexAlong_beta (hqN : ¬ q ∣ N)
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    (∑ W ∈ Place.fiberAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ V,
        (W.ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) : ℤ)) = q + 1 := by
  have hFI : FundamentalIdentityAlong (AlgebraicClosure ℚ)
      (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ :=
    fundamentalIdentityAlong _ hβ (finiteAlong_heckeBetaBar_of_prime (AlgebraicClosure ℚ) N q)
      (separableAlong_of_charZero _ hβ)
  have h := Divisor.degree_pullbackAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ hFI
    (Finsupp.single V 1)
  rw [Divisor.pullbackAlong_single, map_sum] at h
  have h2 : (∑ W ∈ Place.fiberAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ V,
      (W.ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) : ℤ))
        = finrankAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) N q) := by
    simpa [Divisor.degree_single, deg_eq_one_modularFunctionFieldBar] using h
  rw [h2, finrankAlong_heckeBetaBar (AlgebraicClosure ℚ) N q, if_neg hqN]
  push_cast
  ring

private theorem nInf_add_nZero (hqN : ¬ q ∣ N) (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hV : V.ord (jB N) < 0) :
    nInf N q A data hKr hα hβ P V + nZero N q A data hKr hα hβ P V = q + 1 := by
  classical
  rw [nInf_def, nZero_def, ← sum_ramificationIndexAlong_alpha N q hα hqN V,
    ← Finset.sum_filter_add_sum_filter_not
      (Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα V) (fun W => IsInftySide P W)]
  congr 1
  refine Finset.sum_congr (Finset.filter_congr (fun W hW => ?_)) (fun _ _ => rfl)
  have hWV := Place.mem_fiberAlong.mp hW
  have hcusp : IsCuspidal P W := isCuspidal_of_pole N q A data hKr hα hβ P W (by rw [hWV]; exact hV)
  constructor
  · intro hZ
    exact not_isInftySide_of_isZeroSide P W hZ
  · intro hnI
    rcases isInftySide_or_isZeroSide_of_isCuspidal P hqN W hcusp with hI | hZ
    · exact absurd hI hnI
    · exact hZ

private theorem nInf_eq_one_of_pole (hqN : ¬ q ∣ N)
    (V₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hV₀ : V₀.ord (jB N) < 0) :
    nInf N q A data hKr hα hβ P V₀ = 1 := by
  classical
  obtain ⟨Dj, hDj, -⟩ :=
    HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) (jB N) (jB_ne_zero N)

  set Poles := Dj.support.filter (fun V => Dj V < 0) with hPoles
  have hmemP : ∀ V, V ∈ Poles ↔ V.ord (jB N) < 0 := by
    intro V
    rw [hPoles, Finset.mem_filter, Finsupp.mem_support_iff, hDj]
    exact ⟨fun h => h.2, fun h => ⟨h.ne, h⟩⟩

  set eα : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) → ℤ :=
    fun W => (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ) with heα
  set eβ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) → ℤ :=
    fun W => (W.ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) : ℤ) with heβ
  set g : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) → ℤ :=
    fun W => eβ W * (-Dj (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ)) with hg

  have hF1 : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      W.ord (jFun N q) = eα W * (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα).ord
        (jB N) := fun W => by
    rw [← alpha_jB_eq_jFun N q, Place.ord_restrictAlong (heckeAlphaBar _ N q) hα W]
  have hF2 : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      W.ord (jQFun N q) = eβ W * (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ).ord
        (jB N) := fun W => by
    rw [← beta_jB_eq_jQFun N q, Place.ord_restrictAlong (heckeBetaBar _ N q) hβ W]
  have termI : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      IsInftySide P W →
        eβ W * (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ).ord (jB N)
          = q * (eα W * (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα).ord
            (jB N)) := fun W hI => by
    rw [← hF2, ← hF1]
    exact ord_jQFun_of_inftySide P W hI (jFun_ne_zero N q)
  have termZ : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      IsZeroSide P W →
        (q : ℤ) * (eβ W * (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ).ord (jB N))
          = eα W * (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα).ord (jB N) :=
    fun W hZ => by
    rw [← hF2, ← hF1]
    exact (ord_jFun_of_zeroSide P W hZ (jQFun_ne_zero N q)).symm

  have hsides : ∀ V ∈ Poles, ∀ W ∈ Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα V,
      IsInftySide P W ∨ IsZeroSide P W := by
    intro V hV W hW
    have hWV := Place.mem_fiberAlong.mp hW
    exact isInftySide_or_isZeroSide_of_isCuspidal P hqN W
      (isCuspidal_of_pole N q A data hKr hα hβ P W (by rw [hWV]; exact (hmemP V).mp hV))

  have hsplit : ∀ V ∈ Poles, ∀ φ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) → ℤ,
      (∑ W ∈ Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα V, φ W)
        = (∑ W ∈ (Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα V).filter
              (fun W => IsInftySide P W), φ W)
          + ∑ W ∈ (Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα V).filter
              (fun W => IsZeroSide P W), φ W := by
    intro V hV φ
    rw [← Finset.sum_filter_add_sum_filter_not
      (Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα V) (fun W => IsInftySide P W)]
    congr 1
    refine Finset.sum_congr (Finset.filter_congr (fun W hW => ?_)) (fun _ _ => rfl)
    constructor
    · intro hnI
      rcases hsides V hV W hW with hI | hZ
      · exact absurd hI hnI
      · exact hZ
    · intro hZ
      exact not_isInftySide_of_isZeroSide P W hZ

  have hS1 : (∑ V ∈ Poles, (-Dj V) * nInf N q A data hKr hα hβ P V)
      + (∑ V ∈ Poles, (-Dj V) * nZero N q A data hKr hα hβ P V)
        = (q + 1) * ∑ V ∈ Poles, (-Dj V) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun V hV => ?_)
    rw [← mul_add, nInf_add_nZero N q A data hKr hα hβ P hqN V ((hmemP V).mp hV)]
    ring

  have hS2 : ∀ V ∈ Poles,
      (∑ W ∈ (Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα V).filter
          (fun W => IsInftySide P W), g W)
        = q * ((-Dj V) * nInf N q A data hKr hα hβ P V) := by
    intro V hV
    rw [nInf_def, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun W hW => ?_)
    obtain ⟨hWfib, hI⟩ := Finset.mem_filter.mp hW
    have hWV := Place.mem_fiberAlong.mp hWfib
    have h := termI W hI
    rw [hWV] at h
    rw [← hDj, ← hDj] at h
    simp only [hg, heα, heβ, mul_neg, neg_mul] at h ⊢
    rw [h]
    ring

  have hS2' : ∀ V ∈ Poles,
      (q : ℤ) * (∑ W ∈ (Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα V).filter
          (fun W => IsZeroSide P W), g W)
        = (-Dj V) * nZero N q A data hKr hα hβ P V := by
    intro V hV
    rw [nZero_def, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun W hW => ?_)
    obtain ⟨hWfib, hZ⟩ := Finset.mem_filter.mp hW
    have hWV := Place.mem_fiberAlong.mp hWfib
    have h := termZ W hZ
    rw [hWV] at h
    rw [← hDj, ← hDj] at h
    simp only [hg, heα, heβ, mul_neg, neg_mul] at h ⊢
    rw [h]
    ring

  have hdisjα : (↑Poles : Set (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))).PairwiseDisjoint
      (fun V => Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα V) := by
    intro V _ V' _ hne
    refine Finset.disjoint_left.mpr ?_
    intro W hW hW'
    exact hne ((Place.mem_fiberAlong.mp hW).symm.trans (Place.mem_fiberAlong.mp hW'))
  have hdisjβ : (↑Poles : Set (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))).PairwiseDisjoint
      (fun V => Place.fiberAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ V) := by
    intro V _ V' _ hne
    refine Finset.disjoint_left.mpr ?_
    intro W hW hW'
    exact hne ((Place.mem_fiberAlong.mp hW).symm.trans (Place.mem_fiberAlong.mp hW'))
  have hsub : Poles.biUnion (fun V => Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα V)
      ⊆ Poles.biUnion (fun V => Place.fiberAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ V) := by
    intro W hW
    obtain ⟨V, hV, hWfib⟩ := Finset.mem_biUnion.mp hW
    have hWV := Place.mem_fiberAlong.mp hWfib
    have hVord : V.ord (jB N) < 0 := (hmemP V).mp hV

    have hFneg : W.ord (jFun N q) < 0 := by
      rw [hF1, hWV]
      exact mul_neg_of_pos_of_neg
        (by simp only [heα]; exact_mod_cast ramificationIndexAlong_alpha_pos N q hα W) hVord
    have hneg : W.ord (jQFun N q) < 0 := by
      rcases hsides V hV W hWfib with hI | hZ
      · rw [ord_jQFun_of_inftySide P W hI (jFun_ne_zero N q)]
        exact mul_neg_of_pos_of_neg (by exact_mod_cast (Fact.out : q.Prime).pos) hFneg
      · by_contra hnn
        rw [not_lt] at hnn
        have h := ord_jFun_of_zeroSide P W hZ (jQFun_ne_zero N q)
        have h0 : 0 ≤ W.ord (jFun N q) := by
          rw [h]
          exact mul_nonneg (Int.natCast_nonneg _) hnn
        exact absurd h0 (not_le.mpr hFneg)
    rw [hF2] at hneg
    have hβpole : (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ).ord (jB N) < 0 := by
      by_contra hnn
      rw [not_lt] at hnn
      exact absurd (mul_nonneg (Int.natCast_nonneg _) hnn) (not_le.mpr hneg)
    exact Finset.mem_biUnion.mpr ⟨_, (hmemP _).mpr hβpole, Place.mem_fiberAlong.mpr rfl⟩
  have hLα : (∑ V ∈ Poles, ∑ W ∈ Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα V, g W)
      = ∑ W ∈ Poles.biUnion
          (fun V => Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα V), g W :=
    (Finset.sum_biUnion hdisjα).symm
  have hLβ : (∑ V ∈ Poles, ∑ W ∈ Place.fiberAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ V, g W)
      = ∑ W ∈ Poles.biUnion
          (fun V => Place.fiberAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ V), g W :=
    (Finset.sum_biUnion hdisjβ).symm
  have hR : (q + 1) * (∑ V ∈ Poles, (-Dj V))
      = ∑ V ∈ Poles, ∑ W ∈ Place.fiberAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ V, g W := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun V hV => ?_)
    rw [mul_comm, ← sum_ramificationIndexAlong_beta N q hβ hqN V, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun W hW => ?_)
    simp only [hg, heβ]
    rw [Place.mem_fiberAlong.mp hW]
    ring
  have hS3 : (∑ V ∈ Poles, ∑ W ∈ Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα V, g W)
      ≤ (q + 1) * ∑ V ∈ Poles, (-Dj V) := by
    rw [hR, hLα, hLβ]
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun W hW _ => ?_)
    obtain ⟨V', hV', hWfib⟩ := Finset.mem_biUnion.mp hW
    simp only [hg, heβ]
    refine mul_nonneg (Int.natCast_nonneg _) ?_
    rw [Place.mem_fiberAlong.mp hWfib, neg_nonneg, hDj]
    exact ((hmemP V').mp hV').le

  have hLHS : (∑ V ∈ Poles, ∑ W ∈ Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα V, g W)
      = q * (∑ V ∈ Poles, (-Dj V) * nInf N q A data hKr hα hβ P V)
        + ∑ V ∈ Poles, ∑ W ∈ (Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα V).filter
            (fun W => IsZeroSide P W), g W := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun V hV => ?_)
    rw [hsplit V hV g, hS2 V hV]
  have hqBZ : (q : ℤ) * (∑ V ∈ Poles,
        ∑ W ∈ (Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα V).filter
          (fun W => IsZeroSide P W), g W)
      = ∑ V ∈ Poles, (-Dj V) * nZero N q A data hKr hα hβ P V := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun V hV => hS2' V hV)
  rw [hLHS] at hS3
  have h1 := mul_le_mul_of_nonneg_left hS3 (Int.natCast_nonneg q)
  have h2 : ((q : ℤ) ^ 2 - 1) * (∑ V ∈ Poles, (-Dj V) * nInf N q A data hKr hα hβ P V)
      ≤ ((q : ℤ) ^ 2 - 1) * ∑ V ∈ Poles, (-Dj V) := by
    have e1 : ∀ X Y : ℤ, (q : ℤ) * ((q : ℤ) * X + Y) = (q : ℤ) ^ 2 * X + (q : ℤ) * Y :=
      fun X Y => by ring
    have e2 : ∀ Z : ℤ, (q : ℤ) * (((q : ℤ) + 1) * Z) = (q : ℤ) ^ 2 * Z + (q : ℤ) * Z :=
      fun Z => by ring
    rw [e1, e2, hqBZ] at h1
    have e3 : ∀ X X' : ℤ, ((q : ℤ) ^ 2 - 1) * X = ((q : ℤ) ^ 2 * X + X') - (X + X') :=
      fun X X' => by ring
    have e4 : ∀ Z : ℤ, ((q : ℤ) ^ 2 - 1) * Z = ((q : ℤ) ^ 2 * Z + (q : ℤ) * Z) - ((q : ℤ) + 1) * Z :=
      fun Z => by ring
    rw [e3 _ (∑ V ∈ Poles, (-Dj V) * nZero N q A data hKr hα hβ P V), e4, hS1]
    linarith
  have hq2 : (2 : ℤ) ≤ q := by exact_mod_cast (Fact.out : q.Prime).two_le
  have hpos : (0 : ℤ) < (q : ℤ) ^ 2 - 1 := by
    rw [show ((q : ℤ)) ^ 2 - 1 = ((q : ℤ) - 1) * ((q : ℤ) + 1) by ring]
    exact mul_pos (by linarith) (by linarith)
  have hle : (∑ V ∈ Poles, (-Dj V) * nInf N q A data hKr hα hβ P V) ≤ ∑ V ∈ Poles, (-Dj V) :=
    le_of_mul_le_mul_left h2 hpos
  have hterm : ∀ V ∈ Poles, 0 ≤ (-Dj V) * (nInf N q A data hKr hα hβ P V - 1) := by
    intro V hV
    have hc : 0 < -Dj V := by
      rw [hDj]
      exact neg_pos.mpr ((hmemP V).mp hV)
    have hn := one_le_nInf N q A data hKr hα hβ P hqN V (cuspidal_of_pole N A V ((hmemP V).mp hV))
    exact mul_nonneg hc.le (by linarith)
  have hsum0 : (∑ V ∈ Poles, (-Dj V) * (nInf N q A data hKr hα hβ P V - 1)) = 0 := by
    apply le_antisymm
    · have e : (∑ V ∈ Poles, (-Dj V) * (nInf N q A data hKr hα hβ P V - 1))
          = (∑ V ∈ Poles, (-Dj V) * nInf N q A data hKr hα hβ P V) - ∑ V ∈ Poles, (-Dj V) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun V _ => by ring)
      rw [e]
      linarith
    · exact Finset.sum_nonneg hterm
  have hV₀P : V₀ ∈ Poles := (hmemP V₀).mpr hV₀
  have h5 := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hsum0 V₀ hV₀P
  have hc : 0 < -Dj V₀ := by
    rw [hDj]
    exact neg_pos.mpr hV₀
  rcases mul_eq_zero.mp h5 with h | h
  · exact absurd h hc.ne'
  · linarith

private noncomputable def fc (c : AlgebraicClosure ℚ) : modularFunctionFieldBar N :=
  1 - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c⁻¹ * jB N

private theorem fc_eq_smul {c : AlgebraicClosure ℚ} (hc0 : c ≠ 0) :
    fc N c = (-c⁻¹) • (jB N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c) := by
  rw [fc, Algebra.smul_def, map_neg, mul_sub, neg_mul, neg_mul, ← map_mul, inv_mul_cancel₀ hc0,
    map_one]
  ring

private theorem coe_fc {c : AlgebraicClosure ℚ} (hb : c⁻¹ ∈ A) :
    ((fc N c : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ))
      = coeffMap A.subtype (1 - HahnSeries.single 0 (⟨c⁻¹, hb⟩ : A) * jqModC A) := by
  rw [map_sub, map_one, map_mul, coeffMap_single, coeffMap_jqModC]
  show ((1 : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ))
      - ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c⁻¹ : modularFunctionFieldBar N)
          : LaurentSeries (AlgebraicClosure ℚ)) * (jB N : LaurentSeries (AlgebraicClosure ℚ)) = _
  rw [coe_jB' N, show ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c⁻¹
      : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ))
        = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) c⁻¹ from rfl,
    algebraMap_laurentSeries_eq_single]
  rfl

omit [CharP (ResidueField ↥A) q] in
private theorem mem_alpha_fc {c : AlgebraicClosure ℚ} (hb : c⁻¹ ∈ A) :
    coeffMap A.subtype (1 - HahnSeries.single 0 (⟨c⁻¹, hb⟩ : A) * jqModC A)
      ∈ modularFunctionFieldBar (N * q) := by
  rw [← coe_fc N A hb, ← coe_heckeAlphaBar N q (fc N c)]
  exact SetLike.coe_mem _

omit [CharP (ResidueField ↥A) q] in
private theorem alpha_fc_eq {c : AlgebraicClosure ℚ} (hb : c⁻¹ ∈ A) :
    heckeAlphaBar (AlgebraicClosure ℚ) N q (fc N c)
      = ⟨coeffMap A.subtype (1 - HahnSeries.single 0 (⟨c⁻¹, hb⟩ : A) * jqModC A),
          mem_alpha_fc N q A hb⟩ :=
  Subtype.ext (by rw [coe_heckeAlphaBar, coe_fc N A hb])

private theorem fc_mem_residue {c : AlgebraicClosure ℚ} (hc : c ∉ A) :
    ∃ h : fc N c ∈ (RN N q A data hKr hα hβ P R).integers,
      (RN N q A data hKr hα hβ P R).residue ⟨fc N c, h⟩ = 1 := by
  have hb : c⁻¹ ∈ A := (A.mem_or_inv_mem c).resolve_left hc
  have hbmax : (⟨c⁻¹, hb⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    apply hc
    have h1 : ((u : A) : AlgebraicClosure ℚ) * (((u⁻¹ : Aˣ) : A) : AlgebraicClosure ℚ) = 1 := by
      have h := congrArg (fun x : A => (x : AlgebraicClosure ℚ)) (Units.mul_inv u)
      exact h
    rw [hu] at h1
    have key : (((u⁻¹ : Aˣ) : A) : AlgebraicClosure ℚ) = c := by
      rw [eq_inv_of_mul_eq_one_right h1]
      exact inv_inv c
    rw [← key]
    exact ((u⁻¹ : Aˣ) : A).2
  have hres0 : IsLocalRing.residue A ⟨c⁻¹, hb⟩ = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).mpr hbmax
  obtain ⟨hint, hres⟩ := R.residue₁_coeffMap
    (1 - HahnSeries.single 0 (⟨c⁻¹, hb⟩ : A) * jqModC A) (mem_alpha_fc N q A hb)
  have hmem : heckeAlphaBar (AlgebraicClosure ℚ) N q (fc N c) ∈ R.R₁.integers := by
    rw [alpha_fc_eq N q A hb]
    exact hint
  refine ⟨(mem_RN_integers N q A data hKr hα hβ P R (fc N c)).mpr hmem, ?_⟩
  rw [RN_residue]
  have e : R.R₁.residue ⟨heckeAlphaBar (AlgebraicClosure ℚ) N q (fc N c),
        (mem_RN_integers N q A data hKr hα hβ P R (fc N c)).mp
          ((mem_RN_integers N q A data hKr hα hβ P R (fc N c)).mpr hmem)⟩
      = R.R₁.residue ⟨_, hint⟩ :=
    residue_congr R.R₁ (alpha_fc_eq N q A hb)
  have h1 : R.R₁.residue ⟨_, hint⟩ = 1 := by
    apply Subtype.ext
    rw [hres, map_sub, map_one, map_mul, coeffMap_single, coeffMap_jqModC, hres0,
      HahnSeries.single_eq_zero, zero_mul, sub_zero]
    rfl
  rw [e, h1, map_one]

open Classical in

private theorem nInf_eq_one_of_value (hqN : ¬ q ∣ N) (hmodel : R.IsModel)
    {c : AlgebraicClosure ℚ} (hc : c ∉ A)
    (V₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hV₀ : 0 < V₀.ord (jB N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c)) :
    nInf N q A data hKr hα hβ P V₀ = 1 := by
  have hc0 : c ≠ 0 := fun h => hc (h ▸ zero_mem A)
  obtain ⟨hfcI, hres1⟩ := fc_mem_residue N q A data hKr hα hβ P R hc
  have hres_ne : (RN N q A data hKr hα hβ P R).residue ⟨fc N c, hfcI⟩ ≠ 0 := by
    rw [hres1]
    exact one_ne_zero
  have hfc0 : fc N c ≠ 0 := by
    intro h0
    apply hres_ne
    rw [show (⟨fc N c, hfcI⟩ : (RN N q A data hKr hα hβ P R).integers) = 0 from Subtype.ext h0,
      map_zero]

  have hord : ∀ V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      V.ord (fc N c) = V.ord (jB N - algebraMap _ _ c) := fun V => by
    rw [fc_eq_smul N hc0]
    exact ConstantReduction.ord_smul V (neg_ne_zero.mpr (inv_ne_zero hc0)) _
  obtain ⟨Dc, hDc, hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) (fc N c) hfc0

  have hzp : ∀ V ∈ Dc.support,
      0 < V.ord (jB N - algebraMap _ _ c) ∨ V.ord (jB N) < 0 := by
    intro V hV
    have h := Finsupp.mem_support_iff.mp hV
    rw [hDc, hord] at h
    rcases lt_or_gt_of_ne h with hlt | hgt
    · right
      by_contra hnp
      have hj : jB N ∈ V.toValuationSubring :=
        Place.mem_of_ord_nonneg V (jB_ne_zero N) (not_lt.mp hnp)
      have hmem : jB N - algebraMap _ _ c ∈ V.toValuationSubring :=
        sub_mem hj (V.algebraMap_mem' c)
      exact absurd (Place.ord_nonneg_of_mem V hmem) (not_le.mpr hlt)
    · left
      exact hgt
  have hcusp : ∀ V ∈ Dc.support, ∀ a : A,
      V.ord (jB N - algebraMap _ _ (a : AlgebraicClosure ℚ)) ≤ 0 := by
    intro V hV a
    rcases hzp V hV with hz | hp
    · exact cuspidal_of_ord_sub_pos N A V hc hz a
    · exact cuspidal_of_pole N A V hp a
  have hnonaff : ∀ V ∈ Dc.support, ¬ IsAffineGeomPlace (ResidueField ↥A) N (P.sp V) := by
    intro V hV haff
    exact absurd (Place.ord_nonneg_of_mem _ haff.1) (not_le.mpr (P.d0_j_pole V (hcusp V hV)))

  have h1 : (∑ V ∈ Dc.support, Dc V * nInf N q A data hKr hα hβ P V) = 0 := by
    have hmaps : ∀ V ∈ Dc.support, P.sp V ∈ Dc.support.image P.sp :=
      fun V hV => Finset.mem_image_of_mem _ hV
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_eq_zero (fun Q hQ => ?_)
    obtain ⟨V, hV, rfl⟩ := Finset.mem_image.mp hQ
    rw [cuspLaw_regroup N q A data hKr hα hβ P R hqN ⟨fc N c, hfcI⟩ hres_ne Dc hDc hmodel
      (P.sp V) (hnonaff V hV), hres1, Place.ord_one]

  have h2 : (∑ V ∈ Dc.support, Dc V) = 0 := by
    rw [← degree_eq_sum N Dc]
    exact hdeg

  have h3 : ∀ V ∈ Dc.support, 0 ≤ Dc V * (nInf N q A data hKr hα hβ P V - 1) := by
    intro V hV
    rcases hzp V hV with hz | hp
    · have hDpos : 0 < Dc V := by rw [hDc, hord]; exact hz
      have hn := one_le_nInf N q A data hKr hα hβ P hqN V (hcusp V hV)
      exact mul_nonneg hDpos.le (by linarith)
    · rw [nInf_eq_one_of_pole N q A data hKr hα hβ P hqN V hp, sub_self, mul_zero]
  have h4 : (∑ V ∈ Dc.support, Dc V * (nInf N q A data hKr hα hβ P V - 1)) = 0 := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, h1, h2, sub_zero]
  have hV₀mem : V₀ ∈ Dc.support := by
    rw [Finsupp.mem_support_iff, hDc, hord]
    exact hV₀.ne'
  have h5 := (Finset.sum_eq_zero_iff_of_nonneg h3).mp h4 V₀ hV₀mem
  have hDpos : 0 < Dc V₀ := by rw [hDc, hord]; exact hV₀
  rcases mul_eq_zero.mp h5 with h | h
  · exact absurd h hDpos.ne'
  · linarith

private theorem nInf_eq_one (hqN : ¬ q ∣ N) (hmodel : R.IsModel)
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hVQ : ¬ IsAffineGeomPlace (ResidueField ↥A) N (P.sp V)) :
    nInf N q A data hKr hα hβ P V = 1 := by
  by_cases hp : V.ord (jB N) < 0
  · exact nInf_eq_one_of_pole N q A data hKr hα hβ P hqN V hp
  · obtain ⟨c, hcpos⟩ := exists_ord_jB_sub_pos N V hp
    have hc : c ∉ A := by
      intro hcA

      apply hVQ

      have hsum := sum_ramificationIndexAlong_alpha N q hα hqN V
      obtain ⟨W, hW, -⟩ : ∃ W ∈ Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα V,
          (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ) ≠ 0 := by
        apply Finset.exists_ne_zero_of_sum_ne_zero
        rw [hsum]
        positivity
      have hWV := Place.mem_fiberAlong.mp hW
      by_contra hnaff
      have hnaff' : ¬ IsAffineGeomPlace (ResidueField ↥A) N (P.reduceFst W) := by
        show ¬ IsAffineGeomPlace (ResidueField ↥A) N
          (P.sp (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα))
        rw [hWV]
        exact hnaff
      have hcuspW := isCuspidal_of_not_isAffineGeomPlace_reduceFst P W hnaff' ⟨c, hcA⟩
      have e : jFun N q - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) c
          = heckeAlphaBar (AlgebraicClosure ℚ) N q
              (jB N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c) := by
        rw [map_sub, AlgHom.commutes, alpha_jB_eq_jFun N q]
      have hcuspW' : W.ord (heckeAlphaBar (AlgebraicClosure ℚ) N q
          (jB N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c)) ≤ 0 := by
        rw [← e]
        exact hcuspW
      rw [Place.ord_restrictAlong (heckeAlphaBar _ N q) hα W, hWV] at hcuspW'
      have hpos : 0 < (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ)
          * V.ord (jB N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c) :=
        mul_pos (by exact_mod_cast ramificationIndexAlong_alpha_pos N q hα W) hcpos
      exact absurd hcuspW' (not_le.mpr hpos)
    exact nInf_eq_one_of_value N q A data hKr hα hβ P R hqN hmodel hc V hcpos

end Cusps

end Ctx

section Construct

p2m_open "ModularCurve.PlaceSpecialization~IsInftySide~jFun~tInfty~tZero~IsCuspidal~IsZeroSide ModularCurve.PlaceSpecialization.ProlongationTuple"

private theorem construct (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := heckeModuleBar (N * q)
    letI := heckeModuleBar N
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
      (R : PlaceSpecialization.ProlongationTuple P) (hmodel : R.IsModel) (hO : R.OrderLawFixed),
      ∃ R₁ : RegularProlongation A (modularFunctionFieldBar N)
          (modularFunctionFieldC (ResidueField A) N),
        (∀ f : R₁.integers, R₁.residue f ≠ 0 →
          ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
            (∀ V, D V = V.ord (f : modularFunctionFieldBar N)) →
          ∀ Q, Finsupp.mapDomain P.sp D Q = Q.ord (R₁.residue f))
        ∧ (∃ h : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
            ∈ R₁.integers,
          R₁.residue ⟨_, h⟩
            = ⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩)
        ∧ ∃ h : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full N (dvd_refl N))⟩ : modularFunctionFieldBar N)
            ∈ R₁.integers,
          R₁.residue ⟨_, h⟩
            = ⟨jqNModC (ResidueField A) N, jqNModC_mem (ResidueField A) N⟩ := by
  classical
  intro data hKr hα hβ P R hmodel hO
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField ↥A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  refine ⟨RN N q A data hKr hα hβ P R, ?_, RN_hj N q A data hKr hα hβ P R,
    RN_hjN N q A data hKr hα hβ P R⟩
  intro f hf D hD Q
  by_cases hQ : frobOnPlacesGeomLevel (ResidueField ↥A) N data hKr
      (frobOnPlacesGeomLevel (ResidueField ↥A) N data hKr Q) = Q
  · by_cases hQa : IsAffineGeomPlace (ResidueField ↥A) N Q
    · exact law_affine N q A data hKr hα hβ P R hqN f hf D hD hO Q hQ hQa
    · exact law_cusp N q A data hKr hα hβ P R hqN f hf D hD hmodel Q hQa
        (fun V _ hVQ => nInf_eq_one N q A data hKr hα hβ P R hqN hmodel V (by rw [hVQ]; exact hQa))
  · exact law_generic N q A data hKr hα hβ P R hqN (fun V hV => fibreCount_strictFst hqN P V hV)
      f hf D hD hmodel Q hQ

end Construct

end RoofB
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_exists_regularProlongation_sp_jq_jqN.RoofB"

theorem solution (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := heckeModuleBar (N * q)
    letI := heckeModuleBar N
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
      (R : PlaceSpecialization.ProlongationTuple P) (hmodel : R.IsModel) (hO : R.OrderLawFixed),
      ∃ R₁ : RegularProlongation A (modularFunctionFieldBar N)
          (modularFunctionFieldC (ResidueField A) N),
        (∀ f : R₁.integers, R₁.residue f ≠ 0 →
          ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
            (∀ V, D V = V.ord (f : modularFunctionFieldBar N)) →
          ∀ Q, Finsupp.mapDomain P.sp D Q = Q.ord (R₁.residue f))
        ∧ (∃ h : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
            ∈ R₁.integers,
          R₁.residue ⟨_, h⟩
            = ⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩)
        ∧ ∃ h : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full N (dvd_refl N))⟩ : modularFunctionFieldBar N)
            ∈ R₁.integers,
          R₁.residue ⟨_, h⟩
            = ⟨jqNModC (ResidueField A) N, jqNModC_mem (ResidueField A) N⟩ := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI := heckeModuleBar (N * q)
  letI := heckeModuleBar N
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  exact RoofB.construct N q hq hqN A hA

end S_ModularCurve_PlaceSpecialization_exists_regularProlongation_sp_jq_jqN
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_exists_regularProlongation_sp_jq_jqN (solution)
