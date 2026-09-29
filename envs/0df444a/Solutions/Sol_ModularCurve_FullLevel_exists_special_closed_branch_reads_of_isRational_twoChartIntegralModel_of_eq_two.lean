-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_special_closed_branch_reads_of_isRational_twoChartIntegralModel_of_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/ca6e0b06-f5f8-56ce-8ad7-d4c0af931372

import Mathlib
import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_ModularCurve_FullLevel_isProper_toBase_twoChartIntegralModel_levelField_of_eq_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_special_closed_branch_reads_of_isRational_twoChartIntegralModel_of_eq_two
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

namespace T2Aux

section CompositeValuation

variable {K F : Type} [Field K] [Field F] [Algebra K F]

theorem inv_mem_of_isUnit {O : ValuationSubring F} {f : F} (hf : f ∈ O) (hu : IsUnit (⟨f, hf⟩ : ↥O)) : f⁻¹ ∈ O := by
  obtain ⟨u, hu⟩ := hu
  have h1 : ((u⁻¹ : (↥O)ˣ) : ↥O).1 * f = 1 := by
    have h := congrArg Subtype.val (u.inv_mul)
    rw [hu] at h
    exact h
  have h2 : ((u⁻¹ : (↥O)ˣ) : ↥O).1 = f⁻¹ := eq_inv_of_mul_eq_one_left h1
  exact h2 ▸ ((u⁻¹ : (↥O)ˣ) : ↥O).2

theorem mem_maximalIdeal_inv_of_not_mem {O : ValuationSubring F} {f : F} (hf : f ∉ O) :
    ∃ hfi : f⁻¹ ∈ O, (⟨f⁻¹, hfi⟩ : ↥O) ∈ maximalIdeal ↥O := by
  have hfi : f⁻¹ ∈ O := (O.mem_or_inv_mem f).resolve_left hf
  refine ⟨hfi, ?_⟩
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  exact hf (inv_inv f ▸ inv_mem_of_isUnit hfi hu)

theorem ne_zero_of_isUnit_mk {O : ValuationSubring F} {f : F} (hf : f ∈ O) (hu : IsUnit (⟨f, hf⟩ : ↥O)) : f ≠ 0 := by
  rintro rfl
  exact not_isUnit_zero ((show (⟨(0 : F), hf⟩ : ↥O) = 0 from rfl) ▸ hu)

noncomputable def resEquiv (P : Place K F) (hP : P.IsRational) : K ≃+* P.ResidueField :=
  RingEquiv.ofBijective (algebraMap K P.ResidueField) ⟨P.algebraMap_residueField_injective, hP⟩

noncomputable def ev (P : Place K F) (hP : P.IsRational) : ↥P.toValuationSubring →+* K :=
  (resEquiv P hP).symm.toRingHom.comp (IsLocalRing.residue ↥P.toValuationSubring)

theorem ev_eq_evalAt (P : Place K F) (hP : P.IsRational) (f : F) (hf : f ∈ P.toValuationSubring) :
    ev P hP ⟨f, hf⟩ = P.evalAt f := by
  apply P.algebraMap_residueField_injective
  rw [P.algebraMap_evalAt hP hf]
  change (resEquiv P hP) ((resEquiv P hP).symm (IsLocalRing.residue _ ⟨f, hf⟩)) = _
  rw [RingEquiv.apply_symm_apply]

theorem evalAt_algebraMap (P : Place K F) (hP : P.IsRational) (a : K) :
    P.evalAt (algebraMap K F a) = a := by
  rw [← ev_eq_evalAt P hP _ (P.algebraMap_mem' a)]
  apply P.algebraMap_residueField_injective
  change (resEquiv P hP) ((resEquiv P hP).symm (IsLocalRing.residue _ _)) = _
  rw [RingEquiv.apply_symm_apply]
  rfl

theorem ev_eq_zero_iff (P : Place K F) (hP : P.IsRational) (f : ↥P.toValuationSubring) :
    ev P hP f = 0 ↔ f ∈ maximalIdeal ↥P.toValuationSubring := by
  rw [← IsLocalRing.residue_eq_zero_iff]
  change (resEquiv P hP).symm _ = 0 ↔ _
  rw [map_eq_zero_iff _ (resEquiv P hP).symm.injective]

theorem evalAt_mul (P : Place K F) (hP : P.IsRational) {f g : F} (hf : f ∈ P.toValuationSubring) (hg : g ∈ P.toValuationSubring) :
    P.evalAt (f * g) = P.evalAt f * P.evalAt g := by
  rw [← ev_eq_evalAt P hP f hf, ← ev_eq_evalAt P hP g hg, ← ev_eq_evalAt P hP (f * g) (mul_mem hf hg), ← map_mul]; rfl

theorem evalAt_add (P : Place K F) (hP : P.IsRational) {f g : F} (hf : f ∈ P.toValuationSubring) (hg : g ∈ P.toValuationSubring) :
    P.evalAt (f + g) = P.evalAt f + P.evalAt g := by
  rw [← ev_eq_evalAt P hP f hf, ← ev_eq_evalAt P hP g hg, ← ev_eq_evalAt P hP (f + g) (add_mem hf hg), ← map_add]; rfl

theorem evalAt_neg (P : Place K F) (hP : P.IsRational) {f : F} (hf : f ∈ P.toValuationSubring) :
    P.evalAt (-f) = -P.evalAt f := by
  rw [← ev_eq_evalAt P hP f hf, ← ev_eq_evalAt P hP (-f) (neg_mem hf), ← map_neg]; rfl

theorem evalAt_sub (P : Place K F) (hP : P.IsRational) {f g : F} (hf : f ∈ P.toValuationSubring) (hg : g ∈ P.toValuationSubring) :
    P.evalAt (f - g) = P.evalAt f - P.evalAt g := by
  rw [← ev_eq_evalAt P hP f hf, ← ev_eq_evalAt P hP g hg, ← ev_eq_evalAt P hP (f - g) (sub_mem hf hg), ← map_sub]; rfl

theorem evalAt_eq_zero_iff (P : Place K F) (hP : P.IsRational) {f : F} (hf : f ∈ P.toValuationSubring) :
    P.evalAt f = 0 ↔ (⟨f, hf⟩ : ↥P.toValuationSubring) ∈ maximalIdeal ↥P.toValuationSubring := by
  rw [← ev_eq_evalAt P hP f hf, ev_eq_zero_iff]

variable (P : Place K F) (hP : P.IsRational) (A : ValuationSubring K)

noncomputable def compVal : ValuationSubring F where
  carrier := {f | f ∈ P.toValuationSubring ∧ P.evalAt f ∈ A}
  mul_mem' := by
    rintro f g ⟨hf, hfA⟩ ⟨hg, hgA⟩
    exact ⟨mul_mem hf hg, by rw [evalAt_mul P hP hf hg]; exact mul_mem hfA hgA⟩
  one_mem' := ⟨one_mem _, by rw [Place.evalAt_one]; exact one_mem _⟩
  add_mem' := by
    rintro f g ⟨hf, hfA⟩ ⟨hg, hgA⟩
    exact ⟨add_mem hf hg, by rw [evalAt_add P hP hf hg]; exact add_mem hfA hgA⟩
  zero_mem' := ⟨zero_mem _, by
    have : P.evalAt (0 : F) = 0 := by
      rw [← ev_eq_evalAt P hP 0 (zero_mem _)]
      exact (ev_eq_zero_iff P hP _).mpr (by
        have : (⟨(0 : F), zero_mem _⟩ : ↥P.toValuationSubring) = 0 := rfl
        rw [this]; exact (maximalIdeal ↥P.toValuationSubring).zero_mem)
    rw [this]; exact zero_mem _⟩
  neg_mem' := by
    rintro f ⟨hf, hfA⟩
    exact ⟨neg_mem hf, by rw [evalAt_neg P hP hf]; exact neg_mem hfA⟩
  mem_or_inv_mem' := by
    intro f
    by_cases hf : f ∈ P.toValuationSubring
    · by_cases hfm : (⟨f, hf⟩ : ↥P.toValuationSubring) ∈ maximalIdeal ↥P.toValuationSubring
      · left
        exact ⟨hf, by rw [(evalAt_eq_zero_iff P hP hf).mpr hfm]; exact zero_mem _⟩
      · have hfu : IsUnit (⟨f, hf⟩ : ↥P.toValuationSubring) := by
          rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hfm
        have hfi : f⁻¹ ∈ P.toValuationSubring := inv_mem_of_isUnit hf hfu
        have hf0 : f ≠ 0 := ne_zero_of_isUnit_mk hf hfu
        have hprod : P.evalAt f * P.evalAt f⁻¹ = 1 := by
          rw [← evalAt_mul P hP hf hfi, mul_inv_cancel₀ hf0, Place.evalAt_one]
        rcases A.mem_or_inv_mem (P.evalAt f) with hA | hA
        · left; exact ⟨hf, hA⟩
        · right
          refine ⟨hfi, ?_⟩
          rw [eq_inv_of_mul_eq_one_right hprod]
          exact hA
    · right
      obtain ⟨hfi, hm⟩ := mem_maximalIdeal_inv_of_not_mem hf
      exact ⟨hfi, by rw [(evalAt_eq_zero_iff P hP hfi).mpr hm]; exact zero_mem _⟩

theorem mem_compVal_iff {f : F} : f ∈ compVal P hP A ↔ f ∈ P.toValuationSubring ∧ P.evalAt f ∈ A :=
  ⟨fun h => h, fun h => h⟩

theorem algebraMap_mem_compVal {a : K} (ha : a ∈ A) : algebraMap K F a ∈ compVal P hP A :=
  ⟨P.algebraMap_mem' a, by rw [evalAt_algebraMap P hP]; exact ha⟩

theorem isUnit_compVal_iff (f : F) (hf : f ∈ compVal P hP A) :
    IsUnit (⟨f, hf⟩ : ↥(compVal P hP A)) ↔ IsUnit (⟨P.evalAt f, hf.2⟩ : ↥A) := by
  constructor
  · intro hu
    have hfi : f⁻¹ ∈ compVal P hP A := inv_mem_of_isUnit hf hu
    have hf0 : f ≠ 0 := ne_zero_of_isUnit_mk hf hu
    have hprod : P.evalAt f * P.evalAt f⁻¹ = 1 := by
      rw [← evalAt_mul P hP hf.1 hfi.1, mul_inv_cancel₀ hf0, Place.evalAt_one]
    exact isUnit_iff_exists_inv.mpr ⟨⟨P.evalAt f⁻¹, hfi.2⟩, Subtype.ext hprod⟩
  · intro hu
    have hne : P.evalAt f ≠ 0 := ne_zero_of_isUnit_mk hf.2 hu
    have hfm : (⟨f, hf.1⟩ : ↥P.toValuationSubring) ∉ maximalIdeal ↥P.toValuationSubring :=
      fun h => hne ((evalAt_eq_zero_iff P hP hf.1).mpr h)
    have hfu : IsUnit (⟨f, hf.1⟩ : ↥P.toValuationSubring) := by
      rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hfm
    have hfiP : f⁻¹ ∈ P.toValuationSubring := inv_mem_of_isUnit hf.1 hfu
    have hf0 : f ≠ 0 := ne_zero_of_isUnit_mk hf.1 hfu
    have hprod : P.evalAt f * P.evalAt f⁻¹ = 1 := by
      rw [← evalAt_mul P hP hf.1 hfiP, mul_inv_cancel₀ hf0, Place.evalAt_one]
    have hfiA : P.evalAt f⁻¹ ∈ A := by
      rw [eq_inv_of_mul_eq_one_right hprod]
      exact inv_mem_of_isUnit _ hu
    exact isUnit_iff_exists_inv.mpr ⟨⟨f⁻¹, hfiP, hfiA⟩, Subtype.ext (mul_inv_cancel₀ hf0)⟩

theorem coe_mem_nonunits_compVal_iff (f : F) (hf : f ∈ compVal P hP A) :
    f ∈ (compVal P hP A).nonunits ↔ P.evalAt f ∈ A.nonunits := by
  have h1 : f ∈ (compVal P hP A).nonunits ↔ (⟨f, hf⟩ : ↥(compVal P hP A)) ∈ maximalIdeal _ :=
    ValuationSubring.coe_mem_nonunits_iff (a := (⟨f, hf⟩ : ↥(compVal P hP A)))
  have h2 : P.evalAt f ∈ A.nonunits ↔ (⟨P.evalAt f, hf.2⟩ : ↥A) ∈ maximalIdeal _ :=
    ValuationSubring.coe_mem_nonunits_iff (a := (⟨P.evalAt f, hf.2⟩ : ↥A))
  rw [h1, h2, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_compVal_iff, ← mem_nonunits_iff,
    ← IsLocalRing.mem_maximalIdeal]

theorem valuation_evalAt_lt_one_iff (f : F) (hf : f ∈ compVal P hP A) :
    A.valuation (P.evalAt f) < 1 ↔ f ∈ (compVal P hP A).nonunits := by
  rw [coe_mem_nonunits_compVal_iff P hP A f hf, ValuationSubring.mem_nonunits_iff]

end CompositeValuation

end T2Aux

namespace T2Aux

section ChartFactor

theorem chart_factor {KF : Type} [Field KF] {X : Scheme.{0}} {C : Type} [CommRing C] (cK : C →+* KF)
    (ι : Spec (CommRingCat.of C) ⟶ X) [IsOpenImmersion ι]
    (V : ValuationSubring KF) (l : Spec (CommRingCat.of ↥V) ⟶ X)
    (hgen : Spec.map (CommRingCat.ofHom (algebraMap ↥V KF)) ≫ l = Spec.map (CommRingCat.ofHom cK) ≫ ι)
    (y : ↥(Spec (CommRingCat.of C))) (hy : ι.base y = l.base (closedPoint ↥V)) :
    (∀ c : C, cK c ∈ V) ∧ (∀ c : C, c ∈ y.asIdeal ↔ cK c ∈ V.nonunits) := by
  classical

  have hrange : Set.range l.base ⊆ Set.range ι.base := by
    rintro _ ⟨v, rfl⟩
    have hsp : l.base v ⤳ l.base (closedPoint ↥V) :=
      (IsLocalRing.specializes_closedPoint v).map l.base.hom.continuous
    rw [← hy] at hsp
    exact hsp.mem_open ι.isOpenEmbedding.isOpen_range ⟨y, rfl⟩
  let l' : Spec (CommRingCat.of ↥V) ⟶ Spec (CommRingCat.of C) := IsOpenImmersion.lift ι l hrange
  have hfac : l' ≫ ι = l := IsOpenImmersion.lift_fac ι l hrange
  let φ : CommRingCat.of C ⟶ CommRingCat.of ↥V := Spec.preimage l'
  have hφ : Spec.map φ = l' := Spec.map_preimage l'

  have hcomp : φ ≫ CommRingCat.ofHom (algebraMap ↥V KF) = CommRingCat.ofHom cK := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, ← cancel_mono ι, Category.assoc, hfac, hgen]
  have hφc : ∀ c : C, ((φ.hom c : ↥V) : KF) = cK c := fun c => by
    have h := congrArg (fun g : CommRingCat.of C ⟶ CommRingCat.of KF => g.hom c) hcomp
    simpa using h

  have hy' : y = l'.base (closedPoint ↥V) := by
    apply ι.isOpenEmbedding.injective
    rw [hy, ← hfac]
    rfl
  have hyI : ∀ c : C, c ∈ y.asIdeal ↔ φ.hom c ∈ maximalIdeal ↥V := by
    intro c
    rw [hy', ← hφ]
    rfl
  refine ⟨fun c => (hφc c) ▸ (φ.hom c).2, fun c => ?_⟩
  rw [hyI, ← ValuationSubring.coe_mem_nonunits_iff, hφc]

end ChartFactor

section TwoChart

variable (R : Type) [CommRing R] (F : Type) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]

open AlgebraicCurve.TwoChartIntegralModel in

theorem specMap_chartAlgInf_comp_ιInf :
    Spec.map (CommRingCat.ofHom (algebraMap ↥(chartAlgInf R F j) F)) ≫ ιInf R F j =
      Spec.map (CommRingCat.ofHom (algebraMap ↥(chartAlgFin R F j) F)) ≫ ιFin R F j := by
  have e1 : CommRingCat.ofHom (algebraMap ↥(chartAlgFin R F j) F) =
      CommRingCat.ofHom (inclFin R F j).toRingHom ≫ CommRingCat.ofHom (algebraMap ↥(chartAlgMid R F j) F) := by
    ext c; rfl
  have e2 : CommRingCat.ofHom (algebraMap ↥(chartAlgInf R F j) F) =
      CommRingCat.ofHom (inclInf R F j).toRingHom ≫ CommRingCat.ofHom (algebraMap ↥(chartAlgMid R F j) F) := by
    ext c; rfl
  rw [e1, e2, Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc]
  change Spec.map _ ≫ (fInf R F j ≫ ιInf R F j) = Spec.map _ ≫ (fFin R F j ≫ ιFin R F j)
  rw [glue_condition]

end TwoChart

end T2Aux

namespace E140CR

noncomputable def compValRes {F Fbar : Type*} [Field F] [Field Fbar] (O : ValuationSubring F) (res : O →+* Fbar)
    (hker : RingHom.ker res = IsLocalRing.maximalIdeal O) (V : ValuationSubring Fbar) : ValuationSubring F where
  carrier := {f | ∃ h : f ∈ O, res ⟨f, h⟩ ∈ V}
  mul_mem' := by
    rintro a b ⟨ha, haV⟩ ⟨hb, hbV⟩
    refine ⟨O.mul_mem _ _ ha hb, ?_⟩
    have : (⟨a * b, O.mul_mem _ _ ha hb⟩ : O) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
    rw [this, map_mul]; exact V.mul_mem _ _ haV hbV
  one_mem' := ⟨O.one_mem, by
    have : (⟨(1 : F), O.one_mem⟩ : O) = 1 := rfl
    rw [this, map_one]; exact V.one_mem⟩
  add_mem' := by
    rintro a b ⟨ha, haV⟩ ⟨hb, hbV⟩
    refine ⟨O.add_mem _ _ ha hb, ?_⟩
    have : (⟨a + b, O.add_mem _ _ ha hb⟩ : O) = ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
    rw [this, map_add]; exact V.add_mem _ _ haV hbV
  zero_mem' := ⟨O.zero_mem, by
    have : (⟨(0 : F), O.zero_mem⟩ : O) = 0 := rfl
    rw [this, map_zero]; exact V.zero_mem⟩
  neg_mem' := by
    rintro a ⟨ha, haV⟩
    refine ⟨O.neg_mem _ ha, ?_⟩
    have : (⟨-a, O.neg_mem _ ha⟩ : O) = -⟨a, ha⟩ := rfl
    rw [this, map_neg]; exact V.neg_mem _ haV
  mem_or_inv_mem' := by
    intro f
    classical
    by_cases hfO : f ∈ O
    · by_cases hres : res ⟨f, hfO⟩ ∈ V
      · exact Or.inl ⟨hfO, hres⟩
      ·
        right
        have hne : res ⟨f, hfO⟩ ≠ 0 := fun h0 => hres (h0.symm ▸ V.zero_mem)
        have hunit : IsUnit (⟨f, hfO⟩ : O) := by
          by_contra hu
          apply hne
          have : (⟨f, hfO⟩ : O) ∈ RingHom.ker res := by
            rw [hker]; exact (IsLocalRing.mem_maximalIdeal _).mpr hu
          exact this
        obtain ⟨u, hu⟩ := hunit
        have hinvO : f⁻¹ ∈ O := by
          have h1 : ((u⁻¹ : Oˣ) : O).1 = f⁻¹ := by
            apply eq_inv_of_mul_eq_one_left
            have := congrArg (fun o : O => (o : F)) u.inv_mul
            simpa [hu] using this
          exact h1 ▸ ((u⁻¹ : Oˣ) : O).2
        refine ⟨hinvO, ?_⟩
        have hprod : res ⟨f, hfO⟩ * res ⟨f⁻¹, hinvO⟩ = 1 := by
          rw [← map_mul]
          have hf0 : f ≠ 0 := by
            rintro rfl
            apply hne
            have : (⟨(0 : F), hfO⟩ : O) = 0 := rfl
            rw [this, map_zero]
          have : (⟨f, hfO⟩ * ⟨f⁻¹, hinvO⟩ : O) = 1 := Subtype.ext (mul_inv_cancel₀ hf0)
          rw [this, map_one]
        have : res ⟨f⁻¹, hinvO⟩ = (res ⟨f, hfO⟩)⁻¹ := (eq_inv_of_mul_eq_one_right hprod)
        rw [this]
        exact (V.mem_or_inv_mem _).resolve_left hres
    ·
      right
      have hinv : f⁻¹ ∈ O := (O.mem_or_inv_mem f).resolve_left hfO
      refine ⟨hinv, ?_⟩
      have hmax : (⟨f⁻¹, hinv⟩ : O) ∈ IsLocalRing.maximalIdeal O := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        apply hfO
        obtain ⟨u, hu⟩ := hu
        have h1 : ((u⁻¹ : Oˣ) : O).1 = f := by
          rw [← inv_inv f]
          apply eq_inv_of_mul_eq_one_left
          have := congrArg (fun o : O => (o : F)) u.inv_mul
          simpa [hu] using this
        exact h1 ▸ ((u⁻¹ : Oˣ) : O).2
      rw [← hker, RingHom.mem_ker] at hmax
      rw [hmax]; exact V.zero_mem

theorem mem_compValRes_iff {F Fbar : Type*} [Field F] [Field Fbar] (O : ValuationSubring F) (res : O →+* Fbar)
    (hker : RingHom.ker res = IsLocalRing.maximalIdeal O) (V : ValuationSubring Fbar) (f : F) :
    f ∈ compValRes O res hker V ↔ ∃ h : f ∈ O, res ⟨f, h⟩ ∈ V := Iff.rfl

end E140CR

namespace E140CR

open IsLocalRing

theorem isUnit_compValRes_iff {F Fbar : Type*} [Field F] [Field Fbar] (O : ValuationSubring F) (res : O →+* Fbar)
    (hker : RingHom.ker res = IsLocalRing.maximalIdeal O) (V : ValuationSubring Fbar) (f : F)
    (hfO : f ∈ O) (hfV : res ⟨f, hfO⟩ ∈ V) :
    IsUnit (⟨f, ⟨hfO, hfV⟩⟩ : compValRes O res hker V) ↔ IsUnit (⟨res ⟨f, hfO⟩, hfV⟩ : V) := by
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨hgO, hgV⟩ := ((u⁻¹ : (compValRes O res hker V)ˣ) : compValRes O res hker V).2
    have hmul : f * ((u⁻¹ : (compValRes O res hker V)ˣ) : compValRes O res hker V).1 = 1 := by
      have := congrArg (fun w : compValRes O res hker V => (w : F)) u.mul_inv
      simpa [hu] using this
    refine IsUnit.of_mul_eq_one ⟨res ⟨_, hgO⟩, hgV⟩ (Subtype.ext ?_)
    change res ⟨f, hfO⟩ * res ⟨_, hgO⟩ = 1
    rw [← map_mul]
    have : (⟨f, hfO⟩ * ⟨_, hgO⟩ : O) = 1 := Subtype.ext hmul
    rw [this, map_one]
  · intro hu
    have hne : res ⟨f, hfO⟩ ≠ 0 := by
      intro h0
      have : (⟨res ⟨f, hfO⟩, hfV⟩ : V) = 0 := Subtype.ext h0
      rw [this] at hu; exact not_isUnit_zero hu
    have hunitO : IsUnit (⟨f, hfO⟩ : O) := by
      by_contra hnu
      apply hne
      have : (⟨f, hfO⟩ : O) ∈ RingHom.ker res := by rw [hker]; exact (mem_maximalIdeal _).mpr hnu
      exact this
    obtain ⟨w, hw⟩ := hunitO
    have hinvO : f⁻¹ ∈ O := by
      have h1 : ((w⁻¹ : Oˣ) : O).1 = f⁻¹ := by
        apply eq_inv_of_mul_eq_one_left
        have := congrArg (fun o : O => (o : F)) w.inv_mul
        simpa [hw] using this
      exact h1 ▸ ((w⁻¹ : Oˣ) : O).2
    have hf0 : f ≠ 0 := by
      rintro rfl; apply hne
      have : (⟨(0 : F), hfO⟩ : O) = 0 := rfl
      rw [this, map_zero]
    have hresinv : res ⟨f⁻¹, hinvO⟩ = (res ⟨f, hfO⟩)⁻¹ := by
      apply eq_inv_of_mul_eq_one_right
      rw [← map_mul]
      have : (⟨f, hfO⟩ * ⟨f⁻¹, hinvO⟩ : O) = 1 := Subtype.ext (mul_inv_cancel₀ hf0)
      rw [this, map_one]
    have hinvV : (res ⟨f, hfO⟩)⁻¹ ∈ V := by
      obtain ⟨u, hu'⟩ := hu
      have h1 : ((u⁻¹ : Vˣ) : V).1 = (res ⟨f, hfO⟩)⁻¹ := by
        apply eq_inv_of_mul_eq_one_left
        have := congrArg (fun o : V => (o : Fbar)) u.inv_mul
        simpa [hu'] using this
      exact h1 ▸ ((u⁻¹ : Vˣ) : V).2
    have hmem : f⁻¹ ∈ compValRes O res hker V := ⟨hinvO, hresinv ▸ hinvV⟩
    exact IsUnit.of_mul_eq_one ⟨f⁻¹, hmem⟩ (Subtype.ext (mul_inv_cancel₀ hf0))

theorem coe_mem_nonunits_compValRes_iff {F Fbar : Type*} [Field F] [Field Fbar] (O : ValuationSubring F) (res : O →+* Fbar)
    (hker : RingHom.ker res = IsLocalRing.maximalIdeal O) (V : ValuationSubring Fbar) (f : F)
    (hfO : f ∈ O) (hfV : res ⟨f, hfO⟩ ∈ V) :
    f ∈ (compValRes O res hker V).nonunits ↔ res ⟨f, hfO⟩ ∈ V.nonunits := by
  rw [ValuationSubring.coe_mem_nonunits_iff (a := (⟨f, ⟨hfO, hfV⟩⟩ : compValRes O res hker V)),
    ValuationSubring.coe_mem_nonunits_iff (a := (⟨res ⟨f, hfO⟩, hfV⟩ : V)),
    mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, isUnit_compValRes_iff]

theorem algebraMap_mem_compValRes {L F Fbar : Type*} [Field L] [Field F] [Algebra L F] [Field Fbar]
    {A : ValuationSubring L} [Algebra (IsLocalRing.ResidueField ↥A) Fbar]
    (R : AlgebraicCurve.RegularProlongation A F Fbar) (V : ValuationSubring Fbar)
    (hV : ∀ c : IsLocalRing.ResidueField ↥A, algebraMap _ Fbar c ∈ V) (a : ↥A) :
    algebraMap L F a ∈ compValRes R.integers R.residue R.ker_residue V :=
  ⟨(R.algebraMap_mem_iff a).mpr a.2, by rw [R.residue_algebraMap a]; exact hV _⟩

end E140CR

set_option maxHeartbeats 0 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (ζ : Idx q)
    (OIg : CuspidalType.ProjLine q → ValuationSubring (fieldBar q M'))
    (OSS : ↥W → ValuationSubring (fieldBar q M'))

    (hIg_inf : ∀ f : fieldBar q M', f ∈ OIg (lineInfty q) ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hIg : ∀ ℓ, ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ redQ q γ • lineInfty q = ℓ ∧
      OIg ℓ = (OIg (lineInfty q)).comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom)
    (hIg_inj : Function.Injective OIg)
    (hIg_perm : ∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      ∃ σ : Equiv.Perm (CuspidalType.ProjLine q),
        ∀ ℓ, (OIg ℓ).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OIg (σ ℓ))

    (hSS_A : ∀ s (x : AlgebraicClosure ℚ), algebraMap (AlgebraicClosure ℚ) (fieldBar q M') x ∈ OSS s ↔ x ∈ A)
    (hSS_over : ∀ (s : ↥W) (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
      (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
        (IntermediateField.inclusion hle f : fieldBar q M') ∈ OSS s ∧
        ∀ a : A, residue A a =
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
          ∃ h : (IntermediateField.inclusion hle f : fieldBar q M')
              - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s,
            (⟨_, h⟩ : OSS s) ∈ maximalIdeal (OSS s))
    (hSS_fix : ∀ (s : ↥W) (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      (OSS s).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OSS s)

    (hSS_tr : ∀ s : ↥W, ∃ t : fieldBar q M', t ∈ OSS s ∧ ∀ a : A,
      ∃ h : t - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s, IsUnit (⟨_, h⟩ : OSS s))
    (R : RegularProlongation A (fieldBar q M') (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))) (hR : R.integers = OIg (lineInfty q))
    (hR₀O : ∀ f : ↥(modularFunctionFieldBar M'), f ∈ R₀.integers ↔
      (IntermediateField.inclusion hle f : fieldBar q M') ∈ OIg (lineInfty q))

    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπP : π ∈ A)

    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ₀ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
      Ideal.span {(⟨π₀, hπ₀⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A)

    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (ζ₀ : ↥k₀) (hζ₀ : IsPrimitiveRoot ((ζ₀ : ↥k₀) : AlgebraicClosure ℚ) (q * ℓ))
    (ϖt : ↥k₀) (hϖtA : (ϖt : AlgebraicClosure ℚ) ∈ A)
    (hϖt : ∃ u : ↥A, IsUnit u ∧ (ϖt : AlgebraicClosure ℚ) ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ) * (u : AlgebraicClosure ℚ))

    (K₁ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (hK₁ : FiniteDimensional ↥k₀ ↥K₁)
    (A₁ : ValuationSubring ↥K₁) (hA₁ : ∀ x : ↥K₁, x ∈ A₁ ↔ (x : AlgebraicClosure ℚ) ∈ A)
    [IsDiscreteValuationRing ↥A₁] [HenselianLocalRing ↥A₁] :
    letI : Algebra ↥k₀ ↥(fieldBar q M') :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra

    ∀ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M')),
      (IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) ⊔ F₀ = ⊤) →
      (∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → ∀ f : ↥(fieldBar q M'), f ∈ F₀ → levelAutBar q M' ζ' γ f ∈ F₀) →
      (∀ (K' : IntermediateField ↥k₀ (AlgebraicClosure ℚ)), FiniteDimensional ↥k₀ ↥K' →
        ∀ (m : ℕ) (c : Fin m → AlgebraicClosure ℚ) (a : Fin m → ↥(fieldBar q M')), (∀ i, a i ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K' : Set (AlgebraicClosure ℚ))) ⊔ F₀) →
          LinearIndependent ↥K' c → ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c i) * a i = 0 → ∀ i, a i = 0) →
      (∀ f : ↥(fieldBar q M'), (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ Set.range ⇑(coeffEmb (AlgebraicClosure ℚ)) → f ∈ F₀) →

    ∀ [Algebra ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)],
      (∀ a : ↥A₁, ((algebraMap ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) a : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) =
        algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥K₁) : AlgebraicClosure ℚ)) →
    ∀ (j₁ : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)),
      ((j₁ : ↥(fieldBar q M')) = IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M'))) →
    ∀ [Fact (j₁ ≠ 0)],

    ∀ (NIg : Finset (Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')))),
      (∃ j : modularFunctionFieldC (ResidueField A) M' →+* xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'),
        (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
          ∃ hC : (IntermediateField.inclusion hle f : fieldBar q M') ∈ R.integers, R.residue ⟨_, hC⟩ = j (R₀.residue ⟨f, hf⟩)) ∧
        ∀ Q, Q ∈ NIg ↔ ∃ s : ↥W, ∀ g : modularFunctionFieldC (ResidueField A) M',
          g ∈ (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring ↔
            j g ∈ Q.toValuationSubring) →

    let InStalk : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) → Prop := fun x f =>
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∃ g h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), h ∉ y.asIdeal ∧ f * (h : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) = (g : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀))) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∃ g h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), h ∉ y.asIdeal ∧ f * (h : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) = (g : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)))
    let InMax : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) → Prop := fun x f =>
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∃ g h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), h ∉ y.asIdeal ∧ g ∈ y.asIdeal ∧ f * (h : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) = (g : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀))) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∃ g h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), h ∉ y.asIdeal ∧ g ∈ y.asIdeal ∧ f * (h : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) = (g : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)))
    let Centred : Place (AlgebraicClosure ℚ) ↥(fieldBar q M') → ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → Prop := fun P x =>
      P.IsRational ∧ ∀ f : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀), InStalk x f →
        (f : ↥(fieldBar q M')) ∈ P.toValuationSubring ∧ P.evalAt (f : ↥(fieldBar q M')) ∈ A ∧
          (A.valuation (P.evalAt (f : ↥(fieldBar q M'))) < 1 ↔ InMax x f)

    let GoodPt : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → Prop := fun x =>
      (AlgebraicCurve.TwoChartIntegralModel.toBase ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base x = closedPoint ↥A₁ ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), x ⤳ y → y = x) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), ((b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ R.integers.nonunits → b ∈ y.asIdeal) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), ((b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ R.integers.nonunits → b ∈ y.asIdeal) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
          (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) →+* Ω), RingHom.ker φ = y.asIdeal →
            φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) ∉ ModularCurve.ssJSet q Ω)

    let Reads : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) → Prop := fun x Q =>
      ∀ f : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀), InStalk x f →
        ∃ hR : (f : ↥(fieldBar q M')) ∈ R.integers, R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ Q.toValuationSubring ∧
          (R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ Q.toValuationSubring.nonunits ↔ InMax x f)

    let OffBranch : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) → Prop := fun x =>
      ∀ ℓ : CuspidalType.ProjLine q, ℓ ≠ lineInfty q →
        (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
          ∃ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), ((b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ (OIg ℓ).nonunits ∧ b ∉ y.asIdeal) ∧
        (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
          ∃ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), ((b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ (OIg ℓ).nonunits ∧ b ∉ y.asIdeal)

    ∀ Q : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')), Q.IsRational → ∃ x : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁),
      (AlgebraicCurve.TwoChartIntegralModel.toBase ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base x = closedPoint ↥A₁ ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), x ⤳ y → y = x) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), ((b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ R.integers.nonunits → b ∈ y.asIdeal) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
        ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), ((b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) ∈ R.integers.nonunits → b ∈ y.asIdeal) ∧
      Reads x Q := by
  classical
  letI instk₀ : Algebra ↥k₀ ↥(fieldBar q M') :=
    ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
  intro F₀ hK1 hstab hLD hRAT instAlg hconst j₁ hj₁ instFact NIg hN
  intro InStalk InMax Centred GoodPt Reads OffBranch P hPrat
  have hproper := ModularCurve.FullLevel.isProper_toBase_twoChartIntegralModel_levelField_of_eq_two q hq2 M' hqM' A hA W hW hle R₀ hR₀ ζ OIg OSS hIg_inf hIg hIg_inj hIg_perm hSS_A hSS_over hSS_fix hSS_tr R hR hR₀O π hπ hπP k₀ π₀ hπ₀ hdvr hunif hhens hres hκ ℓ hℓ hℓ3 hℓq hℓM' ζ₀ hζ₀ ϖt hϖtA hϖt K₁ hK₁ A₁ hA₁ F₀ hK1 hstab hLD hRAT hconst j₁ hj₁

  let VF : ValuationSubring ↥(fieldBar q M') := E140CR.compValRes R.integers R.residue R.ker_residue P.toValuationSubring
  let V : ValuationSubring ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) := VF.comap (algebraMap ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) ↥(fieldBar q M'))
  have hVmem : ∀ f : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀), f ∈ V ↔ (f : ↥(fieldBar q M')) ∈ VF := fun f => ValuationSubring.mem_comap
  have hVunit : ∀ (f : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) (hf : f ∈ V), IsUnit (⟨f, hf⟩ : ↥V) ↔ IsUnit (⟨(f : ↥(fieldBar q M')), (hVmem f).mp hf⟩ : ↥VF) := by
    intro f hf
    have hf' : (f : ↥(fieldBar q M')) ∈ VF := (hVmem f).mp hf
    constructor
    · intro hu
      have hfi : f⁻¹ ∈ V := T2Aux.inv_mem_of_isUnit hf hu
      have hf0 : f ≠ 0 := T2Aux.ne_zero_of_isUnit_mk hf hu
      have hfiF : ((f : ↥(fieldBar q M')))⁻¹ ∈ VF := by have := (hVmem _).mp hfi; push_cast at this; exact this
      have hf0F : (f : ↥(fieldBar q M')) ≠ 0 := fun h0 => hf0 (by exact_mod_cast h0)
      exact isUnit_iff_exists_inv.mpr ⟨⟨_, hfiF⟩, Subtype.ext (mul_inv_cancel₀ hf0F)⟩
    · intro hu
      have hfi : ((f : ↥(fieldBar q M')))⁻¹ ∈ VF := T2Aux.inv_mem_of_isUnit hf' hu
      have hf0 : (f : ↥(fieldBar q M')) ≠ 0 := T2Aux.ne_zero_of_isUnit_mk hf' hu
      have hf0' : f ≠ 0 := fun h0 => hf0 (by rw [h0]; rfl)
      have hfiV : f⁻¹ ∈ V := by rw [hVmem]; push_cast; exact hfi
      exact isUnit_iff_exists_inv.mpr ⟨⟨f⁻¹, hfiV⟩, Subtype.ext (mul_inv_cancel₀ hf0')⟩
  have hVnu : ∀ (f : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) (hf : f ∈ V), f ∈ V.nonunits ↔ (f : ↥(fieldBar q M')) ∈ VF.nonunits := by
    intro f hf
    rw [ValuationSubring.coe_mem_nonunits_iff (a := (⟨f, hf⟩ : ↥V)),
      ValuationSubring.coe_mem_nonunits_iff (a := (⟨(f : ↥(fieldBar q M')), (hVmem f).mp hf⟩ : ↥VF)),
      IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, hVunit]

  have hcoe : ∀ a : ↥A₁, ((algebraMap ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) a : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) : ↥(fieldBar q M')) =
      algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥K₁) : AlgebraicClosure ℚ) := hconst
  have hA₁V : ∀ a : ↥A₁, algebraMap ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) a ∈ V := fun a => by
    rw [hVmem, hcoe]
    exact E140CR.algebraMap_mem_compValRes R P.toValuationSubring (fun c => P.algebraMap_mem' c) ⟨((a : ↥K₁) : AlgebraicClosure ℚ), (hA₁ a).mp a.2⟩
  let ψ : ↥A₁ →+* ↥V := (algebraMap ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)).codRestrict V hA₁V
  have hψ : ∀ a : ↥A₁, ((ψ a : ↥V) : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) = algebraMap ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) a := fun a => rfl
  haveI hψloc : IsLocalHom ψ := by
    constructor
    intro a hu

    have huF := (hVunit _ (ψ a).2).mp (by rw [Subtype.coe_eta]; exact hu)
    have hh : (ψ a).1.1 = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') a.1.1 := hcoe a
    have hmemVF : (ψ a).1.1 ∈ VF := (hVmem _).mp (ψ a).2
    have hinvVF : ((ψ a).1.1)⁻¹ ∈ VF := T2Aux.inv_mem_of_isUnit _ huF
    obtain ⟨hinvR, -⟩ := (E140CR.mem_compValRes_iff _ _ _ _ _).mp hinvVF
    have hne : (ψ a).1.1 ≠ 0 := T2Aux.ne_zero_of_isUnit_mk _ huF
    have ha0 : a.1 ≠ 0 := by
      intro h0; apply hne; rw [hh, h0]; exact map_zero _
    have hainv : (a.1.1)⁻¹ ∈ A := by
      rw [hh, ← map_inv₀] at hinvR
      exact (R.algebraMap_mem_iff _).mp hinvR
    have hainv' : a.1⁻¹ ∈ A₁ := (hA₁ _).mpr hainv
    have hv1 : A₁.valuation a.1 ≤ 1 := (A₁.valuation_le_one_iff _).mpr a.2
    have hv0 : A₁.valuation a.1 ≠ 0 := (Valuation.ne_zero_iff _).mpr ha0
    have hv2 : (A₁.valuation a.1)⁻¹ ≤ 1 := by
      have := (A₁.valuation_le_one_iff _).mpr hainv'
      rwa [map_inv₀] at this
    have hv3 : 1 ≤ A₁.valuation a.1 := (inv_le_one₀ (zero_lt_iff.mpr hv0)).mp hv2
    exact (ValuationSubring.valuation_eq_one_iff A₁ a).mpr (le_antisymm hv1 hv3)

  have hVC : ValuativeCriterion (AlgebraicCurve.TwoChartIntegralModel.toBase ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) := by
    have h := hproper
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1
  let i₁ : Spec (CommRingCat.of ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) ⟶ AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁ :=
    Spec.map (CommRingCat.ofHom (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀))) ≫ AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁
  let i₂ : Spec (CommRingCat.of ↥V) ⟶ Spec (CommRingCat.of ↥A₁) := Spec.map (CommRingCat.ofHom ψ)
  have hsq : i₁ ≫ AlgebraicCurve.TwoChartIntegralModel.toBase ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁ = Spec.map (CommRingCat.ofHom (algebraMap ↥V ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀))) ≫ i₂ := by
    change (Spec.map _ ≫ AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) ≫ _ = Spec.map _ ≫ Spec.map _
    rw [Category.assoc, AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase, ← Spec.map_comp, ← Spec.map_comp]
    rfl
  let Sq : ValuativeCommSq (AlgebraicCurve.TwoChartIntegralModel.toBase ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) :=
    { R := ↥V, K := ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀), i₁ := i₁, i₂ := i₂, commSq := ⟨hsq⟩ }
  obtain ⟨l, hl₁, hl₂⟩ := (hVC.existence Sq).exists_lift

  have hgenF : Spec.map (CommRingCat.ofHom (algebraMap ↥V ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀))) ≫ l =
      Spec.map (CommRingCat.ofHom (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀))) ≫ AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁ := hl₁
  have hgenI : Spec.map (CommRingCat.ofHom (algebraMap ↥V ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀))) ≫ l =
      Spec.map (CommRingCat.ofHom (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀))) ≫ AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁ :=
    hl₁.trans (T2Aux.specMap_chartAlgInf_comp_ιInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).symm

  have key : ∀ (C : Subalgebra ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) (ι : Spec (CommRingCat.of ↥C) ⟶ AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) [IsOpenImmersion ι],
      Spec.map (CommRingCat.ofHom (algebraMap ↥V ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀))) ≫ l = Spec.map (CommRingCat.ofHom (algebraMap ↥C ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀))) ≫ ι →
      ∀ (y : ↥(Spec (CommRingCat.of ↥C))), ι.base y = l.base (closedPoint ↥V) →
        (∀ c : ↥C, (c : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) ∈ V) ∧ (∀ c : ↥C, c ∈ y.asIdeal ↔ (c : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) ∈ V.nonunits) :=
    fun C ι _ hgen y hy => T2Aux.chart_factor (algebraMap ↥C ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) ι V l hgen y hy

  have step : ∀ (C : Subalgebra ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) (ι : Spec (CommRingCat.of ↥C) ⟶ AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) [IsOpenImmersion ι],
      Spec.map (CommRingCat.ofHom (algebraMap ↥V ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀))) ≫ l = Spec.map (CommRingCat.ofHom (algebraMap ↥C ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀))) ≫ ι →
      ∀ (y : ↥(Spec (CommRingCat.of ↥C))), ι.base y = l.base (closedPoint ↥V) →
      ∀ (f : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) (g h : ↥C), h ∉ y.asIdeal → f * (h : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) = (g : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) →
        f ∈ V ∧ (f ∈ V.nonunits ↔ g ∈ y.asIdeal) := by
    intro C ι _ hgen y hy f g h hh hfg
    obtain ⟨hall, hiff⟩ := key C ι hgen y hy
    have hhV : (h : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) ∈ V := hall h
    have hgV : (g : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) ∈ V := hall g
    have hhu : IsUnit (⟨(h : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)), hhV⟩ : ↥V) := by
      have : (h : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) ∉ V.nonunits := fun hn => hh ((hiff h).mpr hn)
      rwa [ValuationSubring.coe_mem_nonunits_iff (a := (⟨(h : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)), hhV⟩ : ↥V)), IsLocalRing.mem_maximalIdeal,
        mem_nonunits_iff, not_not] at this
    have hh0 : (h : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) ≠ 0 := T2Aux.ne_zero_of_isUnit_mk hhV hhu
    have hfeq : f = (g : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) * ((h : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)))⁻¹ := by
      rw [← hfg, mul_assoc, mul_inv_cancel₀ hh0, mul_one]
    have hfV : f ∈ V := by
      rw [hfeq]; exact mul_mem hgV (T2Aux.inv_mem_of_isUnit hhV hhu)
    refine ⟨hfV, ?_⟩
    rw [hiff g, ValuationSubring.coe_mem_nonunits_iff (a := (⟨f, hfV⟩ : ↥V)),
      ValuationSubring.coe_mem_nonunits_iff (a := (⟨(g : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)), hgV⟩ : ↥V))]
    have hprod : (⟨f, hfV⟩ : ↥V) * ⟨(h : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)), hhV⟩ = ⟨(g : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)), hgV⟩ := Subtype.ext hfg
    rw [← hprod]
    exact (Ideal.mul_unit_mem_iff_mem _ hhu).symm
  refine ⟨l.base (closedPoint ↥V), ?_, ?_, ?_, ?_, ?_⟩
  ·
    have h := congrArg (fun g => g.base (closedPoint ↥V)) hl₂
    change (l ≫ AlgebraicCurve.TwoChartIntegralModel.toBase ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base (closedPoint ↥V) = (Spec.map (CommRingCat.ofHom ψ)).base (closedPoint ↥V) at h
    change (AlgebraicCurve.TwoChartIntegralModel.toBase ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base (l.base (closedPoint ↥V)) = _ at h
    rw [h]
    exact IsLocalRing.comap_closedPoint ψ
  ·
    have maxOf : ∀ (C : Subalgebra ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) (ι : Spec (CommRingCat.of ↥C) ⟶ AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) [IsOpenImmersion ι],
        Spec.map (CommRingCat.ofHom (algebraMap ↥V ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀))) ≫ l = Spec.map (CommRingCat.ofHom (algebraMap ↥C ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀))) ≫ ι →
        ∀ (yc : ↥(Spec (CommRingCat.of ↥C))), ι.base yc = l.base (closedPoint ↥V) → yc.asIdeal.IsMaximal := by
      intro C ι _ hgen yc hyc
      obtain ⟨hall, hiff⟩ := key C ι hgen yc hyc

      have hsub : ∀ c : ↥C, ∃ a : ↥A₁, c - algebraMap ↥A₁ ↥C a ∈ yc.asIdeal := by
        intro c
        have hcV : (c : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) ∈ V := hall c
        have hcVF : (c : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)).1 ∈ VF := (hVmem _).mp hcV
        obtain ⟨hcR, hcQ⟩ := (E140CR.mem_compValRes_iff _ _ _ _ _).mp hcVF
        obtain ⟨a₀, ha₀⟩ := IsLocalRing.residue_surjective (P.evalAt (R.residue ⟨_, hcR⟩))
        obtain ⟨c₀, hc₀A, hdiff, hdiffm⟩ := hκ _ a₀.2
        let a : ↥A₁ := ⟨algebraMap ↥k₀ ↥K₁ c₀, (hA₁ _).mpr hc₀A⟩
        refine ⟨a, ?_⟩
        rw [hiff]
        have hmem : ((c - algebraMap ↥A₁ ↥C a : ↥C) : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) ∈ V := hall _
        have hmemF : ((c - algebraMap ↥A₁ ↥C a : ↥C) : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)).1 ∈ VF := (hVmem _).mp hmem
        obtain ⟨hdR, hdQ⟩ := (E140CR.mem_compValRes_iff _ _ _ _ _).mp hmemF
        rw [hVnu _ hmem, E140CR.coe_mem_nonunits_compValRes_iff _ _ _ _ _ hdR hdQ]

        have ha : a.1.1 = (c₀ : AlgebraicClosure ℚ) := rfl
        have e1 : ((c - algebraMap ↥A₁ ↥C a : ↥C) : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)).1 = (c : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)).1 - algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') a.1.1 := by
          have : ((algebraMap ↥A₁ ↥C a : ↥C) : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)).1 = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') a.1.1 := hcoe a
          change (c : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)).1 - ((algebraMap ↥A₁ ↥C a : ↥C) : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)).1 = _
          rw [this]
        have hc₀R : algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') a.1.1 ∈ R.integers := (R.algebraMap_mem_iff _).mpr hc₀A
        have e2 : (⟨((c - algebraMap ↥A₁ ↥C a : ↥C) : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)).1, hdR⟩ : ↥R.integers) =
            ⟨(c : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)).1, hcR⟩ - ⟨algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((⟨(c₀ : AlgebraicClosure ℚ), hc₀A⟩ : ↥A) : AlgebraicClosure ℚ), (R.algebraMap_mem_iff _).mpr hc₀A⟩ :=
          Subtype.ext e1
        rw [e2, map_sub, R.residue_algebraMap]

        have hmemP : R.residue ⟨(c : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)).1, hcR⟩ - algebraMap (ResidueField ↥A) _ (IsLocalRing.residue ↥A ⟨(c₀ : AlgebraicClosure ℚ), hc₀A⟩) ∈ P.toValuationSubring :=
          P.toValuationSubring.sub_mem hcQ (P.algebraMap_mem' _)
        rw [ValuationSubring.coe_mem_nonunits_iff (a := ⟨_, hmemP⟩),
          ← T2Aux.evalAt_eq_zero_iff P hPrat hmemP,
          T2Aux.evalAt_sub P hPrat hcQ (P.algebraMap_mem' _), T2Aux.evalAt_algebraMap P hPrat, ← ha₀, ← map_sub,
          IsLocalRing.residue_eq_zero_iff]
        convert hdiffm using 2 <;> first | rfl | exact Subtype.ext rfl | simp only [AddSubgroupClass.coe_sub]

      have hker : ∀ a : ↥A₁, algebraMap ↥A₁ ↥C a ∈ yc.asIdeal ↔ a ∈ maximalIdeal ↥A₁ := by
        intro a
        rw [hiff, show ((algebraMap ↥A₁ ↥C a : ↥C) : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) = ((ψ a : ↥V) : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)) from rfl,
          ValuationSubring.coe_mem_nonunits_iff (a := ψ a), IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal,
          mem_nonunits_iff, mem_nonunits_iff]
        exact ⟨fun hn hu => hn (hu.map ψ), fun hn hu => hn (IsLocalHom.map_nonunit a hu)⟩

      let g : ↥A₁ →+* ↥C ⧸ yc.asIdeal := (Ideal.Quotient.mk yc.asIdeal).comp (algebraMap ↥A₁ ↥C)
      have hgsurj : Function.Surjective g := by
        intro t
        obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective t
        obtain ⟨a, ha⟩ := hsub c
        refine ⟨a, ?_⟩
        change Ideal.Quotient.mk yc.asIdeal (algebraMap ↥A₁ ↥C a) = Ideal.Quotient.mk yc.asIdeal c
        rw [Ideal.Quotient.eq]
        rw [← neg_sub]; exact yc.asIdeal.neg_mem_iff.mpr ha
      have hgker : RingHom.ker g = maximalIdeal ↥A₁ := by
        ext a
        rw [RingHom.mem_ker, ← hker]
        exact Ideal.Quotient.eq_zero_iff_mem
      apply Ideal.Quotient.maximal_of_isField
      let e : (↥A₁ ⧸ RingHom.ker g) ≃+* ↥C ⧸ yc.asIdeal := RingHom.quotientKerEquivOfSurjective hgsurj
      let e' : (↥A₁ ⧸ maximalIdeal ↥A₁) ≃+* ↥C ⧸ yc.asIdeal := (Ideal.quotEquivOfEq hgker.symm).trans e
      exact MulEquiv.isField (Field.toIsField (ResidueField ↥A₁)) e'.symm.toMulEquiv
    intro y' hsp
    rcases AlgebraicCurve.TwoChartIntegralModel.mem_range_ιFin_or_mem_range_ιInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁ y' with ⟨yc', hyc'⟩ | ⟨yc', hyc'⟩
    · obtain ⟨xc, hxc⟩ : l.base (closedPoint ↥V) ∈ Set.range (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base :=
        hsp.mem_open (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).isOpenEmbedding.isOpen_range ⟨yc', hyc'⟩
      have hmax := maxOf _ (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) hgenF xc hxc
      have hsp' : xc ⤳ yc' := ((AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).isOpenEmbedding.isInducing.specializes_iff).mp (by rw [hxc, hyc']; exact hsp)
      have hle : xc.asIdeal ≤ yc'.asIdeal := (PrimeSpectrum.le_iff_specializes xc yc').mpr hsp'
      have heq : xc = yc' := PrimeSpectrum.ext (hmax.eq_of_le yc'.isPrime.ne_top hle)
      exact hyc'.symm.trans ((congrArg _ heq).symm.trans hxc)
    · obtain ⟨xc, hxc⟩ : l.base (closedPoint ↥V) ∈ Set.range (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base :=
        hsp.mem_open (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).isOpenEmbedding.isOpen_range ⟨yc', hyc'⟩
      have hmax := maxOf _ (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) hgenI xc hxc
      have hsp' : xc ⤳ yc' := ((AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).isOpenEmbedding.isInducing.specializes_iff).mp (by rw [hxc, hyc']; exact hsp)
      have hle : xc.asIdeal ≤ yc'.asIdeal := (PrimeSpectrum.le_iff_specializes xc yc').mpr hsp'
      have heq : xc = yc' := PrimeSpectrum.ext (hmax.eq_of_le yc'.isPrime.ne_top hle)
      exact hyc'.symm.trans ((congrArg _ heq).symm.trans hxc)
  ·
    intro y hy b hb
    obtain ⟨hall, hiff⟩ := key _ (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) hgenF y hy
    rw [hiff]
    have hbV := hall b
    have hbVF := (hVmem _).mp hbV
    obtain ⟨hbR, hbQ⟩ := (E140CR.mem_compValRes_iff _ _ _ _ _).mp hbVF
    rw [hVnu _ hbV, E140CR.coe_mem_nonunits_compValRes_iff _ _ _ _ _ hbR hbQ]
    have h0 : R.residue ⟨_, hbR⟩ = 0 := by
      have : (⟨_, hbR⟩ : ↥R.integers) ∈ RingHom.ker R.residue := by
        rw [R.ker_residue]
        exact (ValuationSubring.coe_mem_nonunits_iff (a := (⟨_, hbR⟩ : ↥R.integers))).mp hb
      exact this
    rw [ValuationSubring.mem_nonunits_iff, h0, map_zero]
    exact zero_lt_one
  ·
    intro y hy b hb
    obtain ⟨hall, hiff⟩ := key _ (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) hgenI y hy
    rw [hiff]
    have hbV := hall b
    have hbVF := (hVmem _).mp hbV
    obtain ⟨hbR, hbQ⟩ := (E140CR.mem_compValRes_iff _ _ _ _ _).mp hbVF
    rw [hVnu _ hbV, E140CR.coe_mem_nonunits_compValRes_iff _ _ _ _ _ hbR hbQ]
    have h0 : R.residue ⟨_, hbR⟩ = 0 := by
      have : (⟨_, hbR⟩ : ↥R.integers) ∈ RingHom.ker R.residue := by
        rw [R.ker_residue]
        exact (ValuationSubring.coe_mem_nonunits_iff (a := (⟨_, hbR⟩ : ↥R.integers))).mp hb
      exact this
    rw [ValuationSubring.mem_nonunits_iff, h0, map_zero]
    exact zero_lt_one
  ·
    refine fun f hIn => ?_
    have hfV : f ∈ V ∧ (f ∈ V.nonunits ↔ InMax (l.base (closedPoint ↥V)) f) := by
      rcases AlgebraicCurve.TwoChartIntegralModel.mem_range_ιFin_or_mem_range_ιInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁ (l.base (closedPoint ↥V)) with ⟨y, hy⟩ | ⟨y, hy⟩
      · obtain ⟨g, h, hh, hfg⟩ := hIn.1 y hy
        obtain ⟨hfV, hiff⟩ := step _ (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) hgenF y hy f g h hh hfg
        refine ⟨hfV, ⟨fun hfn => ⟨fun y' hy' => ?_, fun y' hy' => ?_⟩, fun hMax => ?_⟩⟩
        · obtain ⟨g', h', hh', hfg'⟩ := hIn.1 y' hy'
          exact ⟨g', h', hh', ((step _ (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) hgenF y' hy' f g' h' hh' hfg').2).mp hfn, hfg'⟩
        · obtain ⟨g', h', hh', hfg'⟩ := hIn.2 y' hy'
          exact ⟨g', h', hh', ((step _ (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) hgenI y' hy' f g' h' hh' hfg').2).mp hfn, hfg'⟩
        · obtain ⟨g', h', hh', hg', hfg'⟩ := hMax.1 y hy
          exact ((step _ (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) hgenF y hy f g' h' hh' hfg').2).mpr hg'
      · obtain ⟨g, h, hh, hfg⟩ := hIn.2 y hy
        obtain ⟨hfV, hiff⟩ := step _ (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) hgenI y hy f g h hh hfg
        refine ⟨hfV, ⟨fun hfn => ⟨fun y' hy' => ?_, fun y' hy' => ?_⟩, fun hMax => ?_⟩⟩
        · obtain ⟨g', h', hh', hfg'⟩ := hIn.1 y' hy'
          exact ⟨g', h', hh', ((step _ (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) hgenF y' hy' f g' h' hh' hfg').2).mp hfn, hfg'⟩
        · obtain ⟨g', h', hh', hfg'⟩ := hIn.2 y' hy'
          exact ⟨g', h', hh', ((step _ (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) hgenI y' hy' f g' h' hh' hfg').2).mp hfn, hfg'⟩
        · obtain ⟨g', h', hh', hg', hfg'⟩ := hMax.2 y hy
          exact ((step _ (AlgebraicCurve.TwoChartIntegralModel.ιInf ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) hgenI y hy f g' h' hh' hfg').2).mpr hg'
    obtain ⟨hfV, hiff⟩ := hfV
    have hfVF : f.1 ∈ VF := (hVmem f).mp hfV
    obtain ⟨hfR, hfQ⟩ := (E140CR.mem_compValRes_iff _ _ _ _ _).mp hfVF
    exact ⟨hfR, hfQ, (E140CR.coe_mem_nonunits_compValRes_iff _ _ _ _ _ hfR hfQ).symm.trans ((hVnu f hfV).symm.trans hiff)⟩

end S_ModularCurve_FullLevel_exists_special_closed_branch_reads_of_isRational_twoChartIntegralModel_of_eq_two
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_special_closed_branch_reads_of_isRational_twoChartIntegralModel_of_eq_two (solution)
