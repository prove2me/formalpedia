-- Prove2me | solution 1 for ModularCurve.regularProlongation_integers_eq_and_coe_residue_eq_of_residue_jq_jqN
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/1437064f-9740-53a0-93a2-a53a17e9c7dc

import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_WeierstrassCurve_ReductionMap
import Theorems.Thm_AlgebraicCurve_RegularProlongation_eq_integers_of_forall_mem_adjoin_iff
import Theorems.Thm_AlgebraicCurve_RegularProlongation_mem_adjoin_iff_mem_integers_iff_of_transcendental_residue
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_relfinrank_full_eq_dedekindPsi
import Theorems.Thm_ModularCurve_relfinrank_laurentBaseChange_modularFunctionFieldFull
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_regularProlongation_integers_eq_and_coe_residue_eq_of_residue_jq_jqN
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

open ModularCurve ValuationSubring AlgebraicCurve IsLocalRing

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option Elab.async false

namespace ProlRigid

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

private noncomputable def _root_.ProlRigid.comap (φ : F →ₐ[L] F') (R' : RegularProlongation A F' Fb') :
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

p2m_export "ProlRigid" "comap"
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
  rw [IsLocalRing.mem_maximalIdeal, _root_.mem_nonunits_iff] at hx ⊢
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

end LevelN

theorem integers_eq_and_residue_eq_of_forall_mem_exists_residue_eq
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {E : Type*} [Field E] [Algebra (IsLocalRing.ResidueField A) E]
    {S : IntermediateField (IsLocalRing.ResidueField A) E} {s : Set E}
    (hS : S = IntermediateField.adjoin (IsLocalRing.ResidueField A) s)
    (R R' : RegularProlongation A F S)
    (x : F) (hx : x ∈ R.integers) (hx' : x ∈ R'.integers)
    (hxres : R'.residue ⟨x, hx'⟩ = R.residue ⟨x, hx⟩)
    (htr : Transcendental (IsLocalRing.ResidueField A) (R.residue ⟨x, hx⟩))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue ⟨x, hx⟩} : Set S)) S)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({x} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue ⟨x, hx⟩} : Set S)) S)
    (hpin : ∀ b ∈ s, ∃ (y : F) (h : y ∈ R.integers) (h' : y ∈ R'.integers),
      (R.residue ⟨y, h⟩ : E) = b ∧ (R'.residue ⟨y, h'⟩ : E) = b) :
    R.integers = R'.integers ∧
      ∀ (f : F) (h : f ∈ R.integers) (h' : f ∈ R'.integers),
        R.residue ⟨f, h⟩ = R'.residue ⟨f, h'⟩ := by

  have htr' : Transcendental (IsLocalRing.ResidueField A) (R'.residue ⟨x, hx'⟩) := by
    rw [hxres]
    exact htr
  have hV : ∀ e : F, e ∈ IntermediateField.adjoin L ({x} : Set F) →
      (e ∈ R'.integers ↔ e ∈ R.integers) := fun e he =>
    (RegularProlongation.mem_adjoin_iff_mem_integers_iff_of_transcendental_residue A R R' x hx
      hx' htr htr' e he).symm
  have hint : R'.integers = R.integers :=
    RegularProlongation.eq_integers_of_forall_mem_adjoin_iff A R ⟨x, hx⟩ htr hfin hdeg
      R'.integers hV
  refine ⟨hint.symm, ?_⟩

  have hVc : comapIntegers (AlgHom.id L F) R' = R.integers := by
    rw [← hint]
    ext e
    exact mem_comapIntegers
  have hτ : ∀ y : R.integers,
      residueHom R (AlgHom.id L F) R' hVc (R.residue y) = R'.residue ⟨(y : F), hint.symm ▸ y.2⟩ :=
    fun y => by
    rw [residueHom_residue]
    exact residue_congr R' rfl
  have hτid : residueHom R (AlgHom.id L F) R' hVc = AlgHom.id (IsLocalRing.ResidueField A) S := by
    refine IntermediateField.algHom_ext_of_eq_adjoin (IsLocalRing.ResidueField A) hS (fun b hb => ?_)
    obtain ⟨y, h, h', hyb, hyb'⟩ := hpin b hb
    have e1 : (⟨b, hS.ge (IntermediateField.subset_adjoin _ _ hb)⟩ : S) = R.residue ⟨y, h⟩ :=
      Subtype.ext hyb.symm
    rw [AlgHom.id_apply, e1, hτ ⟨y, h⟩]
    apply Subtype.ext
    rw [hyb]
    exact hyb'
  intro f h h'
  have key := hτ ⟨f, h⟩
  rw [hτid, AlgHom.id_apply] at key
  exact key

end ProlRigid
p2m_reactivate "P2MW.S_ModularCurve_regularProlongation_integers_eq_and_coe_residue_eq_of_residue_jq_jqN.ProlRigid"

theorem solution
    (M q : ℕ) [NeZero M] (hq : q.Prime) (hqM : ¬ q ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    {S S' : IntermediateField (ResidueField ↥A) (LaurentSeries (ResidueField ↥A))}
    (hS : S = modularFunctionFieldC (ResidueField ↥A) M)
    (hS' : S' = modularFunctionFieldC (ResidueField ↥A) M)
    (R : RegularProlongation A (modularFunctionFieldBar M) S)
    (R' : RegularProlongation A (modularFunctionFieldBar M) S')
    (hj : ∃ h : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full M (jq_mem M))⟩ : modularFunctionFieldBar M)
        ∈ R.integers,
      (R.residue ⟨_, h⟩ : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A))
    (hjM : ∃ h : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ M jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (jqd_mem_full M (dvd_refl M))⟩ : modularFunctionFieldBar M)
        ∈ R.integers,
      (R.residue ⟨_, h⟩ : LaurentSeries (ResidueField ↥A)) = jqNModC (ResidueField ↥A) M)
    (hj' : ∃ h : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full M (jq_mem M))⟩ : modularFunctionFieldBar M)
        ∈ R'.integers,
      (R'.residue ⟨_, h⟩ : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A))
    (hjM' : ∃ h : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ M jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (jqd_mem_full M (dvd_refl M))⟩ : modularFunctionFieldBar M)
        ∈ R'.integers,
      (R'.residue ⟨_, h⟩ : LaurentSeries (ResidueField ↥A)) = jqNModC (ResidueField ↥A) M) :
    R.integers = R'.integers ∧
      ∀ (f : modularFunctionFieldBar M) (h : f ∈ R.integers) (h' : f ∈ R'.integers),
        (R.residue ⟨f, h⟩ : LaurentSeries (ResidueField ↥A))
          = (R'.residue ⟨f, h'⟩ : LaurentSeries (ResidueField ↥A)) := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField ↥A) q :=
    ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  subst hS
  subst hS'
  obtain ⟨hj1, hj2⟩ := hj
  obtain ⟨hn1, hn2⟩ := hjM
  obtain ⟨hj1', hj2'⟩ := hj'
  obtain ⟨hn1', hn2'⟩ := hjM'

  have hjS : R.residue ⟨ProlRigid.jB M, hj1⟩
      = ⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) M⟩ := Subtype.ext hj2
  have hxres : R'.residue ⟨ProlRigid.jB M, hj1'⟩ = R.residue ⟨ProlRigid.jB M, hj1⟩ :=
    Subtype.ext (hj2'.trans hj2.symm)
  have htr : Transcendental (ResidueField ↥A) (R.residue ⟨ProlRigid.jB M, hj1⟩) := by
    rw [hjS]
    exact ProlRigid.transcendental_jqModC_mem (ResidueField ↥A) M
  have hdeg2 : Module.finrank (IntermediateField.adjoin (ResidueField ↥A)
      ({R.residue ⟨ProlRigid.jB M, hj1⟩} : Set (modularFunctionFieldC (ResidueField ↥A) M)))
      (modularFunctionFieldC (ResidueField ↥A) M) = dedekindPsi M := by
    rw [hjS]
    exact ProlRigid.finrank_adjoin_jqModC (ResidueField ↥A) M q hqM
  have hfin : 0 < Module.finrank (IntermediateField.adjoin (ResidueField ↥A)
      ({R.residue ⟨ProlRigid.jB M, hj1⟩} : Set (modularFunctionFieldC (ResidueField ↥A) M)))
      (modularFunctionFieldC (ResidueField ↥A) M) := by
    rw [hdeg2]
    exact ProlRigid.dedekindPsi_pos M
  have hdeg : Module.finrank (IntermediateField.adjoin (AlgebraicClosure ℚ)
      ({((⟨ProlRigid.jB M, hj1⟩ : R.integers) : modularFunctionFieldBar M)} :
        Set (modularFunctionFieldBar M))) (modularFunctionFieldBar M)
      = Module.finrank (IntermediateField.adjoin (ResidueField ↥A)
      ({R.residue ⟨ProlRigid.jB M, hj1⟩} : Set (modularFunctionFieldC (ResidueField ↥A) M)))
      (modularFunctionFieldC (ResidueField ↥A) M) := by
    rw [hdeg2]
    exact ProlRigid.finrank_adjoin_jB M
  have hpin : ∀ b ∈ ({jqModC (ResidueField ↥A), jqNModC (ResidueField ↥A) M} :
      Set (LaurentSeries (ResidueField ↥A))),
      ∃ (y : modularFunctionFieldBar M) (h : y ∈ R.integers) (h' : y ∈ R'.integers),
        (R.residue ⟨y, h⟩ : LaurentSeries (ResidueField ↥A)) = b
          ∧ (R'.residue ⟨y, h'⟩ : LaurentSeries (ResidueField ↥A)) = b := by
    intro b hb
    rcases hb with rfl | hb
    · exact ⟨ProlRigid.jB M, hj1, hj1', hj2, hj2'⟩
    · rw [Set.mem_singleton_iff] at hb
      subst hb
      exact ⟨ProlRigid.jNB M, hn1, hn1', hn2, hn2'⟩
  have key := ProlRigid.integers_eq_and_residue_eq_of_forall_mem_exists_residue_eq A
    (S := modularFunctionFieldC (ResidueField ↥A) M)
    (s := ({jqModC (ResidueField ↥A), jqNModC (ResidueField ↥A) M} :
      Set (LaurentSeries (ResidueField ↥A)))) rfl R R'
    (ProlRigid.jB M) hj1 hj1' hxres htr hfin hdeg hpin
  exact ⟨key.1, fun f h h' => congrArg Subtype.val (key.2 f h h')⟩

end S_ModularCurve_regularProlongation_integers_eq_and_coe_residue_eq_of_residue_jq_jqN
end P2MW
export P2MW.S_ModularCurve_regularProlongation_integers_eq_and_coe_residue_eq_of_residue_jq_jqN (solution)
