-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.sp_eq_spPlace_of_isModel_of_orderLawFixed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/1a9ca041-afbe-56c0-9516-937080a49eca

import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ModularCurve_FibreModelCuspChart
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_regularProlongation_sp_jq_jqN
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_spPlace_eq_of_forall_residue_sub_mem_nonunits
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_spPlace_eq_of_forall_residue_sub_mem_nonunits_jInv
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_AlgebraicCurve_RegularProlongation_eq_integers_of_forall_mem_adjoin_iff
import Theorems.Thm_AlgebraicCurve_RegularProlongation_mem_adjoin_iff_mem_integers_iff_of_transcendental_residue
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_relfinrank_full_eq_dedekindPsi
import Theorems.Thm_ModularCurve_relfinrank_laurentBaseChange_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_exists_regularProlongation_modularFunctionFieldBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_sp_eq_spPlace_of_isModel_of_orderLawFixed
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL"
p2m_attr_erase "simp" "ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option Elab.async false
set_option autoImplicit false
p2m_open "AlgebraicCurve IsLocalRing ModularCurve~dedekindPsi_pos P2MW.S_ModularCurve_PlaceSpecialization_sp_eq_spPlace_of_isModel_of_orderLawFixed.ModularCurve"

namespace RigidIdent

section Preliminaries

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

private noncomputable def _root_.RigidIdent.comap (φ : F →ₐ[L] F') (R' : RegularProlongation A F' Fb') :
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

p2m_export "RigidIdent" "comap"
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

end Preliminaries

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

section Glue

variable (N : ℕ) [NeZero N] (A : ValuationSubring (AlgebraicClosure ℚ))

private noncomputable def inclC :
    modularFunctionFieldC (ResidueField ↥A) N →ₐ[ResidueField ↥A] modularFunctionFieldFullC (ResidueField ↥A) N :=
  IntermediateField.inclusion (modularFunctionFieldC_le_full (ResidueField ↥A) N)

private theorem coe_inclC (x : modularFunctionFieldC (ResidueField ↥A) N) :
    ((inclC N A x : modularFunctionFieldFullC (ResidueField ↥A) N) : LaurentSeries (ResidueField ↥A)) = x :=
  IntermediateField.coe_inclusion (modularFunctionFieldC_le_full (ResidueField ↥A) N) x

private theorem jB_eq_mk :
    jB N = ⟨coeffMap A.subtype (jqModC ↥A),
      (coe_jB N A).symm ▸ (jB N).2⟩ :=
  Subtype.ext (coe_jB N A)

private theorem jNB_eq_mk :
    jNB N = ⟨coeffMap A.subtype (jqNModC ↥A N),
      (coe_jNB N A).symm ▸ (jNB N).2⟩ :=
  Subtype.ext (coe_jNB N A)

private theorem hspec_of_residue_jB_jNB
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField ↥A) p] (hpN : ¬ p ∣ N) (hA : A.LiesOverPrime p)
    (R₁ : RegularProlongation A (modularFunctionFieldBar N) (modularFunctionFieldC (ResidueField ↥A) N))
    (hj : ∃ h : jB N ∈ R₁.integers,
      R₁.residue ⟨_, h⟩ = ⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) N⟩)
    (hjN : ∃ h : jNB N ∈ R₁.integers,
      R₁.residue ⟨_, h⟩ = ⟨jqNModC (ResidueField ↥A) N, jqNModC_mem (ResidueField ↥A) N⟩) :
    ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar N),
      ∃ hint : (⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar N) ∈ R₁.integers,
        ((R₁.residue ⟨_, hint⟩ : modularFunctionFieldC (ResidueField ↥A) N) : LaurentSeries (ResidueField ↥A))
          = coeffMap (IsLocalRing.residue ↥A) y := by
  obtain ⟨R', hspec'⟩ := exists_regularProlongation_modularFunctionFieldBar N hpN A hA

  obtain ⟨hj', hjres'⟩ := hspec' (jqModC ↥A) ((coe_jB N A) ▸ (jB N).2)
  obtain ⟨hn', hnres'⟩ := hspec' (jqNModC ↥A N) ((coe_jNB N A) ▸ (jNB N).2)
  have hjB' : jB N ∈ R'.integers := by rw [jB_eq_mk N A]; exact hj'
  have hjNB' : jNB N ∈ R'.integers := by rw [jNB_eq_mk N A]; exact hn'
  have hresj' : ((R'.residue ⟨jB N, hjB'⟩ : modularFunctionFieldFullC (ResidueField ↥A) N) :
      LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A) := by
    have e := residue_congr R' (x := ⟨jB N, hjB'⟩) (y := ⟨_, hj'⟩) (jB_eq_mk N A)
    rw [e, hjres', coeffMap_jqModC]
  have hresn' : ((R'.residue ⟨jNB N, hjNB'⟩ : modularFunctionFieldFullC (ResidueField ↥A) N) :
      LaurentSeries (ResidueField ↥A)) = jqNModC (ResidueField ↥A) N := by
    have e := residue_congr R' (x := ⟨jNB N, hjNB'⟩) (y := ⟨_, hn'⟩) (jNB_eq_mk N A)
    rw [e, hnres', coeffMap_jqNModC]

  let φ : modularFunctionFieldBar N →ₐ[AlgebraicClosure ℚ] modularFunctionFieldBar N :=
    AlgHom.id (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
  have hφj : φ (jB N) ∈ R'.integers := hjB'
  have htr : Transcendental (ResidueField ↥A) (R'.residue ⟨φ (jB N), hφj⟩) := by
    have e : R'.residue ⟨φ (jB N), hφj⟩ = R'.residue ⟨jB N, hjB'⟩ := residue_congr R' rfl
    rw [e]
    intro halg
    apply transcendental_jqModC (ResidueField ↥A)
    have h2 := halg.algHom (modularFunctionFieldFullC (ResidueField ↥A) N).val
    change IsAlgebraic (ResidueField ↥A)
      ((R'.residue ⟨jB N, hjB'⟩ : modularFunctionFieldFullC (ResidueField ↥A) N) :
        LaurentSeries (ResidueField ↥A)) at h2
    rwa [hresj'] at h2
  have hV : comapIntegers φ R' = R₁.integers := comapIntegers_eq N A p hpN R₁ hj R' φ hφj htr
  have hV' : ∀ x : modularFunctionFieldBar N, x ∈ R'.integers ↔ x ∈ R₁.integers := by
    intro x
    rw [← hV]
    exact (mem_comapIntegers (φ := φ) (R' := R') (x := x)).symm

  obtain ⟨hj1, hjres⟩ := hj
  obtain ⟨hn1, hnres⟩ := hjN
  have h1 : ∃ (h : jB N ∈ R₁.integers) (h' : φ (jB N) ∈ R'.integers),
      R₁.residue ⟨_, h⟩ = ⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) N⟩ ∧
      R'.residue ⟨_, h'⟩ = inclC N A (R₁.residue ⟨_, h⟩) :=
    ⟨hj1, hjB', hjres, Subtype.ext (by rw [coe_inclC, hjres]; exact hresj')⟩
  have h2 : ∃ (h : jNB N ∈ R₁.integers) (h' : φ (jNB N) ∈ R'.integers),
      R₁.residue ⟨_, h⟩ = ⟨jqNModC (ResidueField ↥A) N, jqNModC_mem (ResidueField ↥A) N⟩ ∧
      R'.residue ⟨_, h'⟩ = inclC N A (R₁.residue ⟨_, h⟩) :=
    ⟨hn1, hjNB', hnres, Subtype.ext (by rw [coe_inclC, hnres]; exact hresn')⟩
  intro y hy
  obtain ⟨hint', hres'⟩ := hspec' y hy
  have hint : (⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar N) ∈ R₁.integers := (hV' _).mp hint'
  refine ⟨hint, ?_⟩
  obtain ⟨hmem, hmap⟩ := residue_map_eq N A R₁ R' φ (inclC N A) hV h1 h2 ⟨_, hint⟩
  have e : R'.residue ⟨_, hmem⟩ = R'.residue ⟨_, hint'⟩ := residue_congr R' rfl
  have hval : ((R'.residue ⟨_, hmem⟩ : modularFunctionFieldFullC (ResidueField ↥A) N) :
        LaurentSeries (ResidueField ↥A))
      = ((inclC N A (R₁.residue ⟨_, hint⟩) : modularFunctionFieldFullC (ResidueField ↥A) N) :
        LaurentSeries (ResidueField ↥A)) :=
    congrArg Subtype.val hmap
  rw [coe_inclC] at hval
  rw [← hval, e, hres']

end Glue

section LiesOver

private theorem liesOverPrime_of_charP (q : ℕ) [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (ResidueField ↥A) q] : A.LiesOverPrime q := by
  have h : ((q : ↥A) : AlgebraicClosure ℚ) ∈ A.nonunits := by
    rw [ValuationSubring.coe_mem_nonunits_iff, ← IsLocalRing.residue_eq_zero_iff, map_natCast]
    exact CharP.cast_eq_zero (ResidueField ↥A) q
  unfold ValuationSubring.LiesOverPrime
  simpa using h

end LiesOver

end RigidIdent
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_sp_eq_spPlace_of_isModel_of_orderLawFixed.RigidIdent"

namespace ModularCurve
p2m_export "ModularCurve" "modularFunctionFieldBar qExpand qExpand_injective jq dedekindPsi ModularPolynomialData jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffMap coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC jqNModC modularFunctionFieldC jqModC_mem jqNModC_mem HeckeAlphaBarIntegral HeckeBetaBarIntegral PlaceSpecialization KroneckerCongruence transcendental_jqNModC transcendental_jqModC coeffMap_jqModC coeffMap_jqNModC qExpandAlgHomC modularFunctionFieldFullC modularFunctionFieldC_le_full CharPModel.jBar CharPModel.FibreModel PlaceSpecialization.exists_regularProlongation_sp_jq_jqN CharPModel.FibreModel.spPlace_eq_of_forall_residue_sub_mem_nonunits CharPModel.FibreModel.spPlace_eq_of_forall_residue_sub_mem_nonunits_jInv hasPrincipalDivisors_modularFunctionFieldBar_unconditional relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi relfinrank_full_eq_dedekindPsi relfinrank_laurentBaseChange_modularFunctionFieldFull exists_regularProlongation_modularFunctionFieldBar"
namespace RigidResidueB
p2m_open "ModularCurve~dedekindPsi_pos"

section PlaceFurniture

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)

private theorem mem_nonunits_of_ord_pos {f : F} (hf : f ≠ 0) (h : 0 < w.ord f) :
    f ∈ w.toValuationSubring.nonunits := by
  have hmem : f ∈ w.toValuationSubring := w.mem_of_ord_nonneg hf h.le
  have h' := (w.mem_maximalIdeal_iff_ord_pos hf hmem).mpr h
  rw [← ValuationSubring.coe_mem_nonunits_iff] at h'
  exact h'

private theorem ord_pos_of_mem_nonunits {f : F} (hf : f ≠ 0) (h : f ∈ w.toValuationSubring.nonunits) :
    0 < w.ord f := by
  have hmem : f ∈ w.toValuationSubring := w.toValuationSubring.nonunits_subset h
  have h' : ((⟨f, hmem⟩ : w.toValuationSubring) : F) ∈ w.toValuationSubring.nonunits := h
  rw [ValuationSubring.coe_mem_nonunits_iff] at h'
  exact (w.mem_maximalIdeal_iff_ord_pos hf hmem).mp h'

private theorem zero_mem_nonunits : (0 : F) ∈ w.toValuationSubring.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff, map_zero]
  exact zero_lt_one

private theorem ne_zero_of_ord_pos {f : F} (h : 0 < w.ord f) : f ≠ 0 := by
  rintro rfl
  rw [w.ord_zero] at h
  exact lt_irrefl _ h

private theorem ne_zero_of_ord_neg {f : F} (h : w.ord f < 0) : f ≠ 0 := by
  rintro rfl
  rw [w.ord_zero] at h
  exact lt_irrefl _ h

private theorem mem_of_isIntegral_adjoin {x : F} (hx : x ∈ w.toValuationSubring) {h : F}
    (hint : IsIntegral (Algebra.adjoin K ({x} : Set F)) h) : h ∈ w.toValuationSubring := by
  let O : Subalgebra K F :=
    { carrier := w.toValuationSubring
      mul_mem' := fun ha hb => mul_mem ha hb
      one_mem' := one_mem _
      add_mem' := fun ha hb => add_mem ha hb
      zero_mem' := zero_mem _
      algebraMap_mem' := fun a => w.algebraMap_mem' a }
  have hle : Algebra.adjoin K ({x} : Set F) ≤ O :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr hx)
  obtain ⟨p, hp, hpx⟩ := hint
  refine w.mem_of_eval_monic_eq_zero (P := p.map (algebraMap (Algebra.adjoin K ({x} : Set F)) F))
    (hp.map _) (fun i => ?_) ?_
  · rw [Polynomial.coeff_map]
    exact hle (p.coeff i).2
  · rwa [Polynomial.eval_map]

end PlaceFurniture
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_sp_eq_spPlace_of_isModel_of_orderLawFixed.RigidIdent"

private theorem le_mapDomain_of_nonneg {X Y : Type*} (r : X → Y) (D : X →₀ ℤ) (x₀ : X)
    (h : ∀ x, r x = r x₀ → 0 ≤ D x) : D x₀ ≤ Finsupp.mapDomain r D (r x₀) := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply]
  simp only [Finsupp.sum, Finsupp.single_apply]
  have hterm : ∀ x ∈ D.support, (0 : ℤ) ≤ if r x = r x₀ then D x else 0 := fun x _ => by
    split_ifs with hx
    · exact h x hx
    · exact le_rfl
  by_cases hx₀ : x₀ ∈ D.support
  · calc D x₀ = (if r x₀ = r x₀ then D x₀ else 0) := by rw [if_pos rfl]
      _ ≤ _ := Finset.single_le_sum (f := fun x => if r x = r x₀ then D x else 0) hterm hx₀
  · rw [Finsupp.notMem_support_iff.mp hx₀]
    exact Finset.sum_nonneg hterm

section Clause

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  [CharP (ResidueField A) q]

private theorem one_le_mapDomain_sp
    (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
    (U : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (g : modularFunctionFieldBar N) (hg : g ≠ 0)
    (hU : g ∈ U.toValuationSubring.nonunits)
    (hfib : ∀ V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), P.sp V = P.sp U →
      g ∈ V.toValuationSubring)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hD : ∀ V, D V = V.ord g) :
    1 ≤ Finsupp.mapDomain P.sp D (P.sp U) := by
  have hU1 : 1 ≤ D U := by
    rw [hD]
    exact ord_pos_of_mem_nonunits U hg hU
  exact le_trans hU1 (le_mapDomain_of_nonneg P.sp D U fun V hV => by
    rw [hD]
    exact V.ord_nonneg_of_mem (hfib V hV))

private theorem residue_sub_mem_nonunits
    (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
    (R₁ : RegularProlongation A (modularFunctionFieldBar N) (modularFunctionFieldC (ResidueField A) N))
    (hmass : ∀ f : R₁.integers, R₁.residue f ≠ 0 →
      ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
        (∀ V, D V = V.ord (f : modularFunctionFieldBar N)) →
      ∀ Q, Finsupp.mapDomain P.sp D Q = Q.ord (R₁.residue f))
    (U : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (h : R₁.integers)
    (hfib : ∀ V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), P.sp V = P.sp U →
      (h : modularFunctionFieldBar N) ∈ V.toValuationSubring)
    (a : A) (hU : (h : modularFunctionFieldBar N) -
      algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) a ∈ U.toValuationSubring.nonunits) :
    R₁.residue h - algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
        (IsLocalRing.residue A a) ∈ (P.sp U).toValuationSubring.nonunits := by
  haveI := hasPrincipalDivisors_modularFunctionFieldBar_unconditional N
  set c : R₁.integers := ⟨algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) a,
    (R₁.algebraMap_mem_iff a).mpr a.2⟩ with hc
  have hres : R₁.residue (h - c) = R₁.residue h - algebraMap (ResidueField A)
      (modularFunctionFieldC (ResidueField A) N) (IsLocalRing.residue A a) := by
    rw [map_sub, hc, R₁.residue_algebraMap]
  have hval : ((h - c : R₁.integers) : modularFunctionFieldBar N) =
      (h : modularFunctionFieldBar N) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) a := by
    rw [AddSubgroupClass.coe_sub, hc]
  rw [← hres]
  rcases eq_or_ne (R₁.residue (h - c)) 0 with h0 | h0
  · rw [h0]
    exact zero_mem_nonunits _
  have hg0 : ((h - c : R₁.integers) : modularFunctionFieldBar N) ≠ 0 := fun h00 => h0 (by
    rw [show h - c = 0 from Subtype.ext h00, map_zero])
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ)
    ((h - c : R₁.integers) : modularFunctionFieldBar N) hg0
  have hm := hmass (h - c) h0 D hD (P.sp U)
  have hfib' : ∀ V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), P.sp V = P.sp U →
      ((h - c : R₁.integers) : modularFunctionFieldBar N) ∈ V.toValuationSubring := fun V hV => by
    rw [hval]
    exact sub_mem (hfib V hV) (V.algebraMap_mem' _)
  have h1 := one_le_mapDomain_sp P U _ hg0 (by rw [hval]; exact hU) hfib' D hD
  rw [hm] at h1
  exact mem_nonunits_of_ord_pos _ h0 (by omega)

private theorem jBar_mem_of_sp_eq
    (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
    (U : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hU : ∃ a : A, CharPModel.jBar N -
      algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) a ∈ U.toValuationSubring.nonunits)
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hV : P.sp V = P.sp U) :
    CharPModel.jBar N ∈ V.toValuationSubring := by
  obtain ⟨a, ha⟩ := hU
  by_cases hja0 : CharPModel.jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) a = 0
  · rw [sub_eq_zero.mp hja0]
    exact V.algebraMap_mem' _

  have hU' := P.d0_j U a (ord_pos_of_mem_nonunits U hja0 ha)
  have hjt : (⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) N⟩ :
      modularFunctionFieldC (ResidueField A) N) ∈ (P.sp U).toValuationSubring := by
    have hmem := (P.sp U).mem_of_ord_nonneg (ne_zero_of_ord_pos _ hU') hU'.le
    have := add_mem hmem ((P.sp U).algebraMap_mem' (IsLocalRing.residue A a))
    rwa [sub_add_cancel] at this

  by_contra hjV
  have hpole : ∀ b : A, V.ord (CharPModel.jBar N -
      algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) b) ≤ 0 := fun b => by
    by_contra hb
    push Not at hb
    have hmem := V.mem_of_ord_nonneg (ne_zero_of_ord_pos _ hb) hb.le
    have := add_mem hmem (V.algebraMap_mem' (b : AlgebraicClosure ℚ))
    rw [sub_add_cancel] at this
    exact hjV this
  have hlt := P.d0_j_pole V hpole
  rw [hV] at hlt
  exact absurd ((P.sp U).ord_nonneg_of_mem hjt) (not_le.mpr hlt)

private theorem jBar_inv_mem_of_sp_eq
    (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
    (U : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hU : ∀ a : A, U.ord (CharPModel.jBar N -
      algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) a) ≤ 0)
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hV : P.sp V = P.sp U) :
    (CharPModel.jBar N)⁻¹ ∈ V.toValuationSubring := by
  by_cases hj0 : CharPModel.jBar N = 0
  · rw [hj0, inv_zero]
    exact zero_mem _
  have hlt := P.d0_j_pole U hU

  have hle : V.ord (CharPModel.jBar N) ≤ 0 := by
    by_contra hpos
    push Not at hpos
    have h0 := P.d0_j V 0
    simp only [ZeroMemClass.coe_zero, map_zero, sub_zero] at h0
    rw [hV] at h0
    exact absurd (h0 hpos) (not_lt.mpr hlt.le)
  refine V.mem_of_ord_nonneg (inv_ne_zero hj0) ?_
  rw [V.ord_inv]
  omega

private theorem forall_ord_le_zero_of_not_exists
    (U : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hU : ¬ ∃ a : A, CharPModel.jBar N -
      algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) a ∈ U.toValuationSubring.nonunits) :
    ∀ a : A, U.ord (CharPModel.jBar N -
      algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) a) ≤ 0 := fun a => by
  by_contra h
  push Not at h
  exact hU ⟨a, mem_nonunits_of_ord_pos U (ne_zero_of_ord_pos _ h) h⟩

end Clause
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_sp_eq_spPlace_of_isModel_of_orderLawFixed.RigidIdent"

end ModularCurve.RigidResidueB
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_sp_eq_spPlace_of_isModel_of_orderLawFixed.RigidIdent"
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_sp_eq_spPlace_of_isModel_of_orderLawFixed.RigidIdent"

open ModularCurve.PlaceSpecialization ModularCurve.RigidResidueB in

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    [CharP (IsLocalRing.ResidueField ↥A) q]
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr (IsLocalRing.ResidueField ↥A) (IsLocalRing.residue ↥A) hα hβ}
    (R : ProlongationTuple P) (hqN : ¬ q ∣ N)
    (hmodel : R.IsModel) (hO : R.OrderLawFixed)
    (fm : CharPModel.FibreModel N A q (IsLocalRing.ResidueField ↥A) (IsLocalRing.residue ↥A)) (hc : fm.CuspChart)
    (hred : Function.Surjective (IsLocalRing.residue ↥A))
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom (IsLocalRing.ResidueField ↥A)))).map
      (algebraMap (Polynomial (IsLocalRing.ResidueField ↥A)) (RatFunc (IsLocalRing.ResidueField ↥A)))).Separable) :
    P.sp = fm.spPlace hred dataAll hsep := by
  have hq : q.Prime := Fact.out
  have hA : A.LiesOverPrime q := RigidIdent.liesOverPrime_of_charP q A
  obtain ⟨R₁, hmass, hjq, hjqN⟩ :=
    PlaceSpecialization.exists_regularProlongation_sp_jq_jqN N q hq hqN A hA data hKr hα hβ P R hmodel hO
  have hspec := RigidIdent.hspec_of_residue_jB_jNB N A q hqN hA R₁ hjq hjqN
  funext U
  by_cases hJ : ∃ a : A, CharPModel.jBar N -
      algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) a ∈ U.toValuationSubring.nonunits
  · exact (CharPModel.FibreModel.spPlace_eq_of_forall_residue_sub_mem_nonunits N q A fm dataAll hsep R₁
      hspec U hJ (P.sp U) fun h hint a ha => residue_sub_mem_nonunits P R₁ hmass U h
        (fun V hV => mem_of_isIntegral_adjoin V (jBar_mem_of_sp_eq P U hJ V hV) hint) a ha).symm
  · have hpole := forall_ord_le_zero_of_not_exists U hJ
    exact (CharPModel.FibreModel.spPlace_eq_of_forall_residue_sub_mem_nonunits_jInv N q A fm hc dataAll hsep
      R₁ hspec U hpole (P.sp U) fun h hint a ha => residue_sub_mem_nonunits P R₁ hmass U h
        (fun V hV => mem_of_isIntegral_adjoin V (jBar_inv_mem_of_sp_eq P U hpole V hV) hint) a ha).symm

end S_ModularCurve_PlaceSpecialization_sp_eq_spPlace_of_isModel_of_orderLawFixed
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_sp_eq_spPlace_of_isModel_of_orderLawFixed (solution)
