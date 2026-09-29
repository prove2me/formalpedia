-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.forall_mem_iff_residueFst_eq_zero_or_forall_mem_iff_residueSnd_eq_zero_of_height_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/08c97e73-5f95-5bac-ab25-b8d27620e136

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ModularCurve_jIntegralClosure_isNoetherianRing_and_isIntegrallyClosed_level
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_Localization_AtPrime_isDiscreteValuationRing_of_height_eq_one
import Theorems.Thm_ModularCurve_NodeLocalized_coeffSubring_eq_or_isDiscreteValuationRing
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_residue_jFun_sub_jQFun_sub
import Theorems.Thm_ModularCurve_exists_regularProlongation_pair_valuationSubring_eq_or_eq_of_not_dvd
import Theorems.Thm_ValuationSubring_exists_integral_mul_eq_of_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_forall_mem_iff_residueFst_eq_zero_or_forall_mem_iff_residueSnd_eq_zero_of_height_one
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo"
p2m_attr_erase "simp" "ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.NodeLocalized
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

namespace C1bGlue

theorem jRing_le_fieldOver (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (N : ℕ) [NeZero N] :
    jRing A K ≤ (fieldOver N K).toSubring := by
  rw [jRing, Subring.closure_le]
  rintro x (⟨c, rfl⟩ | hx)
  · exact Subfield.subset_closure (Or.inl ⟨⟨(c : AlgebraicClosure ℚ), (c.2).2⟩, rfl⟩)
  · rw [Set.mem_singleton_iff] at hx; subst hx
    exact Subfield.subset_closure (Or.inr (Or.inl rfl))

theorem jRing_le_jIntegralClosure (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (N : ℕ) [NeZero N] :
    jRing A K ≤ jIntegralClosure N A K := fun x hx =>
  ⟨jRing_le_fieldOver A K N hx, isIntegral_algebraMap (R := ↥(jRing A K)) (A := LaurentSeries (AlgebraicClosure ℚ)) (x := ⟨x, hx⟩)⟩

theorem fieldOver_le_bar (M : ℕ) [NeZero M] (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    {x : LaurentSeries (AlgebraicClosure ℚ)} (hx : x ∈ fieldOver M K) :
    x ∈ modularFunctionFieldBar M := by
  have hle : fieldOver M K ≤ (modularFunctionFieldBar M).toSubfield := by
    unfold fieldOver
    rw [Subfield.closure_le]
    rintro y (⟨c, rfl⟩ | hy)
    · exact (modularFunctionFieldBar M).algebraMap_mem (c : AlgebraicClosure ℚ)
    · rcases hy with rfl | rfl
      · have h : jqModC (AlgebraicClosure ℚ) = coeffEmb (AlgebraicClosure ℚ) jq := by
          rw [← jqModC_rat, coeffEmb, coeffMap_jqModC]
        rw [h]
        exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M (jq_mem M))
      · have h : jqNModC (AlgebraicClosure ℚ) M = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ M jq) := by
          rw [jqNModC, ← jqModC_rat, coeffEmb, coeffMap_qExpand, coeffMap_jqModC]
        rw [h]
        exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full M (dvd_refl M))
  exact hle hx

noncomputable def toBar (M : ℕ) [NeZero M] (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    ↥(fieldOver M K) →+* ↥(modularFunctionFieldBar M) where
  toFun x := ⟨(x : LaurentSeries (AlgebraicClosure ℚ)), fieldOver_le_bar M K x.2⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

@[scoped simp] theorem coe_toBar (M : ℕ) [NeZero M] (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (x : ↥(fieldOver M K)) :
    ((toBar M K x : ↥(modularFunctionFieldBar M)) : LaurentSeries (AlgebraicClosure ℚ)) = x := rfl

theorem mem_nonunits_comap_iff {K L : Type*} [Field K] [Field L] (A : ValuationSubring L) (f : K →+* L) (x : K) :
    x ∈ (A.comap f).nonunits ↔ f x ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_comap,
    map_inv₀, map_eq_zero]

theorem mem_nonunits_iff_residue {L : Type*} [Field L] (V : ValuationSubring L) {κ : Type*} [Field κ]
    (res : ↥V →+* κ) (hres : ∀ y : ↥V, res y ≠ 0 → IsUnit y) (x : L) :
    x ∈ V.nonunits ↔ ∃ h : x ∈ V, res ⟨x, h⟩ = 0 := by
  constructor
  · intro hx
    have hxV : x ∈ V := (V.valuation_le_one_iff x).mp (le_of_lt hx)
    refine ⟨hxV, ?_⟩
    by_contra hne
    have hu := hres ⟨x, hxV⟩ hne
    have hmax : (⟨x, hxV⟩ : ↥V) ∈ maximalIdeal ↥V := ValuationSubring.coe_mem_nonunits_iff.mp hx
    exact hmax hu
  · rintro ⟨hxV, h0⟩
    have : (⟨x, hxV⟩ : ↥V) ∈ maximalIdeal ↥V := fun hu => (hu.map res).ne_zero h0
    exact (ValuationSubring.coe_mem_nonunits_iff (a := ⟨x, hxV⟩)).mpr this

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

variable (R : ProlongationTuple P) (K : IntermediateField ℚ (AlgebraicClosure ℚ))

noncomputable def V₁ : ValuationSubring ↥(fieldOver (N * q) K) := (R.R₁.integers).comap (toBar (N * q) K)

noncomputable def V₂ : ValuationSubring ↥(fieldOver (N * q) K) := (R.R₂.integers).comap (toBar (N * q) K)

theorem jIntegralClosure_le_fieldOver : jIntegralClosure (N * q) A K ≤ (fieldOver (N * q) K).toSubring :=
  fun _ hx => hx.1

@[reducible] noncomputable def algCF : Algebra ↥(jIntegralClosure (N * q) A K) ↥(fieldOver (N * q) K) :=
  (Subring.inclusion (jIntegralClosure_le_fieldOver (A := A) (N := N) (q := q) K)).toAlgebra

attribute [local instance] algCF

theorem algebraMap_CF_apply (c : ↥(jIntegralClosure (N * q) A K)) :
    ((algebraMap ↥(jIntegralClosure (N * q) A K) ↥(fieldOver (N * q) K) c : ↥(fieldOver (N * q) K)) :
      LaurentSeries (AlgebraicClosure ℚ)) = c := rfl

variable [FiniteDimensional ℚ K]

theorem isFractionRing_CF : IsFractionRing ↥(jIntegralClosure (N * q) A K) ↥(fieldOver (N * q) K) := by
  obtain ⟨dataNq⟩ := ModularCurve.nonempty_modularPolynomialData (N * q)
  obtain ⟨-, -, hfrac, -⟩ := ModularCurve.jIntegralClosure_isNoetherianRing_and_isIntegrallyClosed_level A N dataNq K
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨y, hy⟩
    have hy0 : (y : LaurentSeries (AlgebraicClosure ℚ)) ≠ 0 := fun h => nonZeroDivisors.ne_zero hy (Subtype.ext h)
    exact isUnit_iff_ne_zero.mpr (fun h => hy0 (congrArg Subtype.val h))
  · intro z
    obtain ⟨c, s, hc, hs, hs0, hzs⟩ := hfrac z.1 z.2
    have hsC : s ∈ jIntegralClosure (N * q) A K := jRing_le_jIntegralClosure A K (N * q) hs
    refine ⟨⟨⟨c, hc⟩, ⟨⟨s, hsC⟩, mem_nonZeroDivisors_of_ne_zero (fun h => hs0 (congrArg Subtype.val h))⟩⟩, ?_⟩
    exact Subtype.ext hzs
  · intro x y hxy
    refine ⟨1, ?_⟩
    have : (x : LaurentSeries (AlgebraicClosure ℚ)) = y :=
      congrArg (fun z : ↥(fieldOver (N * q) K) => (z : LaurentSeries (AlgebraicClosure ℚ))) hxy
    rw [Subtype.ext this]

theorem exists_W (𝔭 : Ideal ↥(jIntegralClosure (N * q) A K)) [𝔭.IsPrime] (h𝔭 : 𝔭.height = 1) :
    ∃ W : ValuationSubring ↥(fieldOver (N * q) K), ∀ x : ↥(fieldOver (N * q) K),
      x ∈ W ↔ ∃ r s : ↥(jIntegralClosure (N * q) A K), s ∉ 𝔭 ∧
        x * algebraMap _ ↥(fieldOver (N * q) K) s = algebraMap _ ↥(fieldOver (N * q) K) r := by
  classical
  obtain ⟨dataNq⟩ := ModularCurve.nonempty_modularPolynomialData (N * q)
  obtain ⟨hnoeth, hic, -, -⟩ := ModularCurve.jIntegralClosure_isNoetherianRing_and_isIntegrallyClosed_level A N dataNq K
  haveI := hnoeth; haveI := hic
  haveI := isFractionRing_CF (A := A) (N := N) (q := q) K
  haveI : IsDiscreteValuationRing (Localization.AtPrime 𝔭) :=
    Localization.AtPrime.isDiscreteValuationRing_of_height_eq_one 𝔭 h𝔭

  have hle : 𝔭.primeCompl ≤ nonZeroDivisors ↥(jIntegralClosure (N * q) A K) := 𝔭.primeCompl_le_nonZeroDivisors
  letI : Algebra (Localization.AtPrime 𝔭) ↥(fieldOver (N * q) K) :=
    (IsLocalization.lift (M := 𝔭.primeCompl) (S := Localization.AtPrime 𝔭) (g := algebraMap _ ↥(fieldOver (N * q) K))
      (fun y => IsUnit.mk0 _ (fun h => nonZeroDivisors.ne_zero (hle y.2)
        ((FaithfulSMul.algebraMap_injective _ ↥(fieldOver (N * q) K)) (by rw [h, map_zero]))))).toAlgebra
  haveI : IsScalarTower ↥(jIntegralClosure (N * q) A K) (Localization.AtPrime 𝔭) ↥(fieldOver (N * q) K) :=
    IsScalarTower.of_algebraMap_eq (fun c =>
      (IsLocalization.lift_eq (M := 𝔭.primeCompl) (S := Localization.AtPrime 𝔭) _ c).symm)
  haveI : IsFractionRing (Localization.AtPrime 𝔭) ↥(fieldOver (N * q) K) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization 𝔭.primeCompl (Localization.AtPrime 𝔭) _
  let W : ValuationSubring ↥(fieldOver (N * q) K) :=
    ValuationSubring.ofSubring (algebraMap (Localization.AtPrime 𝔭) ↥(fieldOver (N * q) K)).range (by
      intro x
      rcases ValuationRing.isInteger_or_isInteger (Localization.AtPrime 𝔭) x with ⟨y, hy⟩ | ⟨y, hy⟩
      · exact Or.inl ⟨y, hy⟩
      · exact Or.inr ⟨y, hy⟩)
  refine ⟨W, fun x => ?_⟩
  show x ∈ (algebraMap (Localization.AtPrime 𝔭) ↥(fieldOver (N * q) K)).range ↔ _
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj 𝔭.primeCompl y
    refine ⟨r, s, s.2, ?_⟩
    have := congrArg (algebraMap (Localization.AtPrime 𝔭) ↥(fieldOver (N * q) K)) hrs
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at this
    exact this
  · rintro ⟨r, s, hs, hx⟩
    refine ⟨IsLocalization.mk' (Localization.AtPrime 𝔭) r ⟨s, Ideal.mem_primeCompl_iff.mpr hs⟩, ?_⟩
    have hs0 : algebraMap _ ↥(fieldOver (N * q) K) s ≠ 0 := fun h => nonZeroDivisors.ne_zero (hle hs)
      ((FaithfulSMul.algebraMap_injective _ ↥(fieldOver (N * q) K)) (by rw [h, map_zero]))
    apply mul_right_cancel₀ hs0
    rw [hx]
    have := IsLocalization.mk'_spec (Localization.AtPrime 𝔭) r ⟨s, Ideal.mem_primeCompl_iff.mpr hs⟩
    have := congrArg (algebraMap (Localization.AtPrime 𝔭) ↥(fieldOver (N * q) K)) this
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at this
    exact this

theorem mem_iff_mem_nonunits (𝔭 : Ideal ↥(jIntegralClosure (N * q) A K)) [𝔭.IsPrime]
    (W : ValuationSubring ↥(fieldOver (N * q) K))
    (hWmem : ∀ x : ↥(fieldOver (N * q) K), x ∈ W ↔ ∃ r s : ↥(jIntegralClosure (N * q) A K), s ∉ 𝔭 ∧
        x * algebraMap _ ↥(fieldOver (N * q) K) s = algebraMap _ ↥(fieldOver (N * q) K) r)
    (t : ↥(jIntegralClosure (N * q) A K)) :
    t ∈ 𝔭 ↔ algebraMap _ ↥(fieldOver (N * q) K) t ∈ W.nonunits := by
  have hinj : Function.Injective (algebraMap ↥(jIntegralClosure (N * q) A K) ↥(fieldOver (N * q) K)) :=
    fun a b h => Subtype.ext (congrArg (fun z : ↥(fieldOver (N * q) K) => (z : LaurentSeries (AlgebraicClosure ℚ))) h)
  rw [ValuationSubring.mem_nonunits_iff_or]
  constructor
  · intro ht
    by_cases ht0 : algebraMap _ ↥(fieldOver (N * q) K) t = 0
    · exact Or.inl ht0
    · refine Or.inr (fun hinv => ?_)
      obtain ⟨r, s, hs, hrs⟩ := (hWmem _).mp hinv
      apply hs
      have hsrt : s = r * t := by
        apply hinj
        rw [map_mul, ← hrs]
        field_simp
      rw [hsrt]
      exact 𝔭.mul_mem_left r ht
  · rintro (h0 | hinv)
    · have : t = 0 := hinj (by rw [h0, map_zero])
      rw [this]; exact 𝔭.zero_mem
    · by_contra ht
      apply hinv
      refine (hWmem _).mpr ⟨1, t, ht, ?_⟩
      have ht0 : algebraMap _ ↥(fieldOver (N * q) K) t ≠ 0 := by
        intro h0; apply ht
        have : t = 0 := hinj (by rw [h0, map_zero])
        rw [this]; exact 𝔭.zero_mem
      rw [inv_mul_cancel₀ ht0, map_one]

theorem c1b_of_W_eq (hqN : ¬ q ∣ N)
    (𝔭 : Ideal ↥(jIntegralClosure (N * q) A K)) [𝔭.IsPrime]
    (W : ValuationSubring ↥(fieldOver (N * q) K))
    (hWmem : ∀ x : ↥(fieldOver (N * q) K), x ∈ W ↔ ∃ r s : ↥(jIntegralClosure (N * q) A K), s ∉ 𝔭 ∧
        x * algebraMap _ ↥(fieldOver (N * q) K) s = algebraMap _ ↥(fieldOver (N * q) K) r)
    (hW : W = V₁ R K ∨ W = V₂ R K) :
    (∀ (t : ↥(modularFunctionFieldBar (N * q))) (ht : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K),
        (⟨(t : LaurentSeries (AlgebraicClosure ℚ)), ht⟩ : ↥(jIntegralClosure (N * q) A K)) ∈ 𝔭 ↔
          ∃ h₁ : t ∈ R.R₁.integers, R.residue₁ ⟨t, h₁⟩ = 0) ∨
    (∀ (t : ↥(modularFunctionFieldBar (N * q))) (ht : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K),
        (⟨(t : LaurentSeries (AlgebraicClosure ℚ)), ht⟩ : ↥(jIntegralClosure (N * q) A K)) ∈ 𝔭 ↔
          ∃ h₂ : t ∈ R.R₂.integers, R.residue₂ ⟨t, h₂⟩ = 0) := by
  have key : ∀ (t : ↥(modularFunctionFieldBar (N * q))) (ht : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K),
      toBar (N * q) K (algebraMap _ ↥(fieldOver (N * q) K) (⟨(t : LaurentSeries (AlgebraicClosure ℚ)), ht⟩ : ↥(jIntegralClosure (N * q) A K))) = t :=
    fun t ht => Subtype.ext rfl
  rcases hW with rfl | rfl
  · left
    intro t ht
    rw [mem_iff_mem_nonunits K 𝔭 _ hWmem, V₁, mem_nonunits_comap_iff, key t ht,
      mem_nonunits_iff_residue R.R₁.integers R.R₁.residue (fun y hy => R.R₁.isUnit_of_residue_ne_zero hy)]
    constructor
    · rintro ⟨h₁, h0⟩; exact ⟨h₁, by rw [residue₁_apply, h0, map_zero]⟩
    · rintro ⟨h₁, h0⟩
      refine ⟨h₁, ?_⟩
      rw [residue₁_apply] at h0
      exact (map_eq_zero_iff _ R.ι.injective).mp h0
  · right
    intro t ht
    rw [mem_iff_mem_nonunits K 𝔭 _ hWmem, V₂, mem_nonunits_comap_iff, key t ht,
      mem_nonunits_iff_residue R.R₂.integers R.R₂.residue (fun y hy => R.R₂.isUnit_of_residue_ne_zero hy)]
    constructor
    · rintro ⟨h₂, h0⟩; exact ⟨h₂, by rw [residue₂_apply, h0, map_zero]⟩
    · rintro ⟨h₂, h0⟩
      refine ⟨h₂, ?_⟩
      rw [residue₂_apply] at h0
      exact (map_eq_zero_iff _ R.ι.injective).mp h0

theorem c1b_of_vert (hqN : ¬ q ∣ N)
    (𝔭 : Ideal ↥(jIntegralClosure (N * q) A K)) [𝔭.IsPrime]
    (W : ValuationSubring ↥(fieldOver (N * q) K))
    (hWmem : ∀ x : ↥(fieldOver (N * q) K), x ∈ W ↔ ∃ r s : ↥(jIntegralClosure (N * q) A K), s ∉ 𝔭 ∧
        x * algebraMap _ ↥(fieldOver (N * q) K) s = algebraMap _ ↥(fieldOver (N * q) K) r)
    {O : Type*} [CommRing O] [IsLocalRing O] [Algebra O ↥(fieldOver (N * q) K)]
    (hVERT : ∀ V' : ValuationSubring ↥(fieldOver (N * q) K), V' ≠ ⊤ →
      (∀ x : O, algebraMap O ↥(fieldOver (N * q) K) x ∈ V') →
      (∀ x ∈ maximalIdeal O, algebraMap O ↥(fieldOver (N * q) K) x ∈ V'.nonunits) →
      V' = V₁ R K ∨ V' = V₂ R K)
    (hWtop : W ≠ ⊤) (hOW : ∀ x : O, algebraMap O ↥(fieldOver (N * q) K) x ∈ W)
    (hdomW : ∀ x ∈ maximalIdeal O, algebraMap O ↥(fieldOver (N * q) K) x ∈ W.nonunits) :
    (∀ (t : ↥(modularFunctionFieldBar (N * q))) (ht : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K),
        (⟨(t : LaurentSeries (AlgebraicClosure ℚ)), ht⟩ : ↥(jIntegralClosure (N * q) A K)) ∈ 𝔭 ↔
          ∃ h₁ : t ∈ R.R₁.integers, R.residue₁ ⟨t, h₁⟩ = 0) ∨
    (∀ (t : ↥(modularFunctionFieldBar (N * q))) (ht : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K),
        (⟨(t : LaurentSeries (AlgebraicClosure ℚ)), ht⟩ : ↥(jIntegralClosure (N * q) A K)) ∈ 𝔭 ↔
          ∃ h₂ : t ∈ R.R₂.integers, R.residue₂ ⟨t, h₂⟩ = 0) :=
  c1b_of_W_eq R K hqN 𝔭 W hWmem (hVERT W hWtop hOW hdomW)

end C1bGlue
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_forall_mem_iff_residueFst_eq_zero_or_forall_mem_iff_residueSnd_eq_zero_of_height_one.C1bGlue"

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.NodeLocalized
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

namespace RoadA

local notation "Lb" => AlgebraicClosure ℚ

section Extend

variable {K₀ L₀ : Type*} [Field K₀] [Field L₀] (ι : K₀ →+* L₀)

theorem exists_comap_eq (W₀ : ValuationSubring K₀) : ∃ W : ValuationSubring L₀, W.comap ι = W₀ := by
  obtain ⟨W, hmem, hloc⟩ := IsLocalRing.exists_factor_valuationRing (ι.comp W₀.subtype)
  refine ⟨W, le_antisymm ?_ ?_⟩
  ·
    apply ValuationSubring.nonunits_le_nonunits.mp
    intro x hx

    have hxW₀ : x ∈ W₀ := (W₀.valuation_le_one_iff x).mp (le_of_lt hx)
    have hmax : (⟨x, hxW₀⟩ : ↥W₀) ∈ IsLocalRing.maximalIdeal ↥W₀ := ValuationSubring.coe_mem_nonunits_iff.mp hx

    have himg : ((ι.comp W₀.subtype).codRestrict W.toSubring hmem ⟨x, hxW₀⟩) ∈
        IsLocalRing.maximalIdeal ↥W := by
      intro hu
      exact hmax (hloc.map_nonunit _ hu)
    have hn : ι x ∈ W.nonunits := ValuationSubring.coe_mem_nonunits_iff.mpr himg

    rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_comap, map_inv₀]
    rw [ValuationSubring.mem_nonunits_iff_or] at hn
    rcases hn with h0 | hinv
    · exact Or.inl ((map_eq_zero ι).mp h0)
    · exact Or.inr hinv
  · intro x hx
    exact hmem ⟨x, hx⟩

end Extend
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_forall_mem_iff_residueFst_eq_zero_or_forall_mem_iff_residueSnd_eq_zero_of_height_one.C1bGlue"

section Twist

variable (M : ℕ) [NeZero M]

noncomputable abbrev τ (σ : Lb ≃ₐ[ℚ] Lb) : ↥(modularFunctionFieldBar M) ≃+* ↥(modularFunctionFieldBar M) :=
  arithmeticRingAut (modularFunctionFieldFull M) σ

theorem coe_τ (σ : Lb ≃ₐ[ℚ] Lb) (x : ↥(modularFunctionFieldBar M)) :
    ((τ M σ x : ↥(modularFunctionFieldBar M)) : LaurentSeries Lb) = coeffMap (σ : Lb →+* Lb) (x : LaurentSeries Lb) := rfl

theorem τ_algebraMap (σ : Lb ≃ₐ[ℚ] Lb) (a : Lb) :
    τ M σ (algebraMap Lb ↥(modularFunctionFieldBar M) a) = algebraMap Lb ↥(modularFunctionFieldBar M) (σ a) :=
  arithmeticRingAut_algebraMap (modularFunctionFieldFull M) σ a

noncomputable def fixedSubfield (σ : Lb ≃ₐ[ℚ] Lb) : Subfield (LaurentSeries Lb) where
  carrier := {x | coeffMap (σ : Lb →+* Lb) x = x}
  mul_mem' {a b} ha hb := by
    show coeffMap (σ : Lb →+* Lb) (a * b) = a * b
    rw [map_mul, show coeffMap (σ : Lb →+* Lb) a = a from ha, show coeffMap (σ : Lb →+* Lb) b = b from hb]
  one_mem' := by show coeffMap (σ : Lb →+* Lb) 1 = 1; rw [map_one]
  add_mem' {a b} ha hb := by
    show coeffMap (σ : Lb →+* Lb) (a + b) = a + b
    rw [map_add, show coeffMap (σ : Lb →+* Lb) a = a from ha, show coeffMap (σ : Lb →+* Lb) b = b from hb]
  zero_mem' := by show coeffMap (σ : Lb →+* Lb) 0 = 0; rw [map_zero]
  neg_mem' {a} ha := by
    show coeffMap (σ : Lb →+* Lb) (-a) = -a
    rw [map_neg, show coeffMap (σ : Lb →+* Lb) a = a from ha]
  inv_mem' a ha := by
    show coeffMap (σ : Lb →+* Lb) a⁻¹ = a⁻¹
    rw [map_inv₀, show coeffMap (σ : Lb →+* Lb) a = a from ha]

theorem mem_fixedSubfield_iff (σ : Lb ≃ₐ[ℚ] Lb) (x : LaurentSeries Lb) :
    x ∈ fixedSubfield σ ↔ coeffMap (σ : Lb →+* Lb) x = x := Iff.rfl

theorem fieldOver_le_fixedSubfield (K : IntermediateField ℚ Lb) (σ : Lb ≃ₐ[ℚ] Lb) (hσ : ∀ c : ↥K, σ c = c) :
    fieldOver M K ≤ fixedSubfield σ := by
  unfold fieldOver
  rw [Subfield.closure_le]
  rintro y (⟨c, rfl⟩ | hy)
  · show coeffMap (σ : Lb →+* Lb) (CharPReduction.constSeries K.toSubalgebra.toSubring c) = _
    show coeffMap (σ : Lb →+* Lb) (algebraMap Lb (LaurentSeries Lb) (c : Lb)) = algebraMap Lb (LaurentSeries Lb) (c : Lb)
    rw [coeffMap_algebraMap]
    congr 1
    exact hσ ⟨c, c.2⟩
  · rcases hy with rfl | rfl
    · show coeffMap (σ : Lb →+* Lb) (jqModC Lb) = jqModC Lb
      rw [coeffMap_jqModC]
    · show coeffMap (σ : Lb →+* Lb) (jqNModC Lb M) = jqNModC Lb M
      rw [jqNModC, coeffMap_qExpand, coeffMap_jqModC]

theorem τ_eq_self_of_mem_fieldOver (K : IntermediateField ℚ Lb) (σ : Lb ≃ₐ[ℚ] Lb) (hσ : ∀ c : ↥K, σ c = c)
    (t : ↥(modularFunctionFieldBar M)) (ht : (t : LaurentSeries Lb) ∈ fieldOver M K) : τ M σ t = t :=
  Subtype.ext (fieldOver_le_fixedSubfield M K σ hσ ht)

noncomputable def twist (σ : Lb ≃ₐ[ℚ] Lb) (W : ValuationSubring ↥(modularFunctionFieldBar M)) :
    ValuationSubring ↥(modularFunctionFieldBar M) :=
  W.comap (τ M σ.symm).toRingHom

theorem mem_twist_iff (σ : Lb ≃ₐ[ℚ] Lb) (W : ValuationSubring ↥(modularFunctionFieldBar M)) (x : ↥(modularFunctionFieldBar M)) :
    x ∈ twist M σ W ↔ τ M σ.symm x ∈ W := Iff.rfl

theorem algebraMap_mem_twist_iff (σ : Lb ≃ₐ[ℚ] Lb) (W : ValuationSubring ↥(modularFunctionFieldBar M)) (a : Lb) :
    algebraMap Lb ↥(modularFunctionFieldBar M) a ∈ twist M σ W ↔ algebraMap Lb ↥(modularFunctionFieldBar M) (σ.symm a) ∈ W := by
  rw [mem_twist_iff, τ_algebraMap]

theorem mem_twist_iff_of_mem_fieldOver (K : IntermediateField ℚ Lb) (σ : Lb ≃ₐ[ℚ] Lb) (hσ : ∀ c : ↥K, σ c = c)
    (W : ValuationSubring ↥(modularFunctionFieldBar M))
    (t : ↥(modularFunctionFieldBar M)) (ht : (t : LaurentSeries Lb) ∈ fieldOver M K) :
    t ∈ twist M σ W ↔ t ∈ W := by
  rw [mem_twist_iff, τ_eq_self_of_mem_fieldOver M K σ.symm (fun c => ?_) t ht]
  have := hσ c
  exact σ.symm_apply_eq.mpr this.symm

end Twist
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_forall_mem_iff_residueFst_eq_zero_or_forall_mem_iff_residueSnd_eq_zero_of_height_one.C1bGlue"

end RoadA
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_forall_mem_iff_residueFst_eq_zero_or_forall_mem_iff_residueSnd_eq_zero_of_height_one.C1bGlue"

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

namespace JLine

open Polynomial

variable {L : Type*} [Field L] (A : ValuationSubring L) {E : Type*} [Field E] [Algebra L E] (J : E)

structure GaussLike (U : ValuationSubring E) : Prop where
  const : ∀ a : L, algebraMap L E a ∈ U ↔ a ∈ A
  mem : J ∈ U
  unit : ∀ p : Polynomial ↥A, p.map (IsLocalRing.residue ↥A) ≠ 0 →
    U.valuation (aeval J (p.map (algebraMap ↥A L))) = 1

theorem exists_map_eq_C_mul {r : Polynomial L} {b : L} (hb : b ≠ 0)
    (h : ∀ n, A.valuation (r.coeff n) ≤ A.valuation b) :
    ∃ r' : Polynomial ↥A, r'.map (algebraMap ↥A L) = C b⁻¹ * r := by
  have hl : C b⁻¹ * r ∈ Polynomial.lifts (algebraMap ↥A L) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_C_mul]
    have hle : A.valuation (b⁻¹ * r.coeff n) ≤ 1 := by
      rw [map_mul, map_inv₀]
      have hvb : A.valuation b ≠ 0 := (Valuation.ne_zero_iff _).mpr hb
      calc (A.valuation b)⁻¹ * A.valuation (r.coeff n) ≤ (A.valuation b)⁻¹ * A.valuation b :=
            mul_le_mul_right (h n) _
        _ = 1 := inv_mul_cancel₀ hvb
    exact ⟨⟨_, (A.valuation_le_one_iff _).mp hle⟩, rfl⟩
  exact (Polynomial.mem_lifts _).mp hl

theorem exists_rescale (r s : Polynomial L) (h : r ≠ 0 ∨ s ≠ 0) :
    ∃ (c : L) (r' s' : Polynomial ↥A), c ≠ 0 ∧ r'.map (algebraMap ↥A L) = C c * r ∧ s'.map (algebraMap ↥A L) = C c * s ∧
      (r'.map (IsLocalRing.residue ↥A) ≠ 0 ∨ s'.map (IsLocalRing.residue ↥A) ≠ 0) := by
  classical

  let T : Finset (Bool × ℕ) := (r.support.map ⟨fun n => (true, n), fun a b h => by simpa using h⟩) ∪
    (s.support.map ⟨fun n => (false, n), fun a b h => by simpa using h⟩)
  let f : Bool × ℕ → L := fun t => if t.1 then r.coeff t.2 else s.coeff t.2
  have hT : T.Nonempty := by
    rcases h with hr | hs
    · obtain ⟨n, hn⟩ := Polynomial.support_nonempty.mpr hr
      exact ⟨(true, n), Finset.mem_union_left _ (Finset.mem_map_of_mem _ hn)⟩
    · obtain ⟨n, hn⟩ := Polynomial.support_nonempty.mpr hs
      exact ⟨(false, n), Finset.mem_union_right _ (Finset.mem_map_of_mem _ hn)⟩
  obtain ⟨t₀, ht₀, hmax⟩ := Finset.exists_max_image T (fun t => A.valuation (f t)) hT
  set b := f t₀ with hb

  have hb0 : b ≠ 0 := by
    rcases Finset.mem_union.mp ht₀ with h1 | h1
    · obtain ⟨n, hn, rfl⟩ := Finset.mem_map.mp h1
      simpa [hb, f, Polynomial.mem_support_iff] using hn
    · obtain ⟨n, hn, rfl⟩ := Finset.mem_map.mp h1
      simpa [hb, f, Polynomial.mem_support_iff] using hn

  have hr : ∀ n, A.valuation (r.coeff n) ≤ A.valuation b := by
    intro n
    by_cases hn : n ∈ r.support
    · have := hmax (true, n) (Finset.mem_union_left _ (Finset.mem_map_of_mem _ hn))
      simpa [f] using this
    · rw [Polynomial.notMem_support_iff.mp hn, map_zero]; exact zero_le'
  have hs : ∀ n, A.valuation (s.coeff n) ≤ A.valuation b := by
    intro n
    by_cases hn : n ∈ s.support
    · have := hmax (false, n) (Finset.mem_union_right _ (Finset.mem_map_of_mem _ hn))
      simpa [f] using this
    · rw [Polynomial.notMem_support_iff.mp hn, map_zero]; exact zero_le'
  obtain ⟨r', hr'⟩ := exists_map_eq_C_mul A hb0 hr
  obtain ⟨s', hs'⟩ := exists_map_eq_C_mul A hb0 hs
  refine ⟨b⁻¹, r', s', inv_ne_zero hb0, hr', hs', ?_⟩

  have key : ∀ (p : Polynomial L) (p' : Polynomial ↥A) (n : ℕ), p'.map (algebraMap ↥A L) = C b⁻¹ * p → p.coeff n = b →
      p'.map (IsLocalRing.residue ↥A) ≠ 0 := by
    intro p p' n hp hn h0
    have h1 : (p'.map (IsLocalRing.residue ↥A)).coeff n = 0 := by rw [h0, Polynomial.coeff_zero]
    rw [Polynomial.coeff_map] at h1
    have h2 : algebraMap ↥A L (p'.coeff n) = 1 := by
      have := congrArg (fun z => Polynomial.coeff z n) hp
      simp only [Polynomial.coeff_map, Polynomial.coeff_C_mul] at this
      rw [this, hn, inv_mul_cancel₀ hb0]
    have h3 : p'.coeff n = 1 := (FaithfulSMul.algebraMap_injective ↥A L) (by rw [h2, map_one])
    rw [h3, map_one] at h1
    exact one_ne_zero h1
  rcases Finset.mem_union.mp ht₀ with h1 | h1
  · obtain ⟨n, hn, hn'⟩ := Finset.mem_map.mp h1
    left
    refine key r r' n hr' ?_
    have : t₀ = (true, n) := hn'.symm
    simp [hb, f, this]
  · obtain ⟨n, hn, hn'⟩ := Finset.mem_map.mp h1
    right
    refine key s s' n hs' ?_
    have : t₀ = (false, n) := hn'.symm
    simp [hb, f, this]

variable {A J}

theorem aeval_mem {U : ValuationSubring E} (hU : GaussLike A J U) (p : Polynomial ↥A) :
    aeval J (p.map (algebraMap ↥A L)) ∈ U := by
  rw [Polynomial.aeval_map_algebraMap, Polynomial.aeval_eq_sum_range]
  refine U.toSubring.sum_mem (fun n _ => ?_)
  rw [Algebra.smul_def, IsScalarTower.algebraMap_apply ↥A L E]
  exact U.mul_mem _ _ ((hU.const _).mpr (p.coeff n).2) (U.pow_mem hU.mem n)

theorem aeval_mem_nonunits {U : ValuationSubring E} (hU : GaussLike A J U) (p : Polynomial ↥A)
    (hp : p.map (IsLocalRing.residue ↥A) = 0) : aeval J (p.map (algebraMap ↥A L)) ∈ U.nonunits := by
  rw [Polynomial.aeval_map_algebraMap, Polynomial.aeval_eq_sum_range]

  have hterm : ∀ n, p.coeff n • J ^ n ∈ U.nonunits := by
    intro n
    have hc : (p.coeff n) ∈ IsLocalRing.maximalIdeal ↥A := by
      rw [← IsLocalRing.residue_eq_zero_iff]
      have := congrArg (fun z => Polynomial.coeff z n) hp
      simpa [Polynomial.coeff_map] using this
    rw [Algebra.smul_def, IsScalarTower.algebraMap_apply ↥A L E, ValuationSubring.mem_nonunits_iff]
    rw [map_mul]
    have h1 : U.valuation (algebraMap L E (p.coeff n : L)) < 1 := by
      rw [← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or]
      by_cases h0 : ((p.coeff n : ↥A) : L) = 0
      · left; rw [h0, map_zero]
      · right
        rw [← map_inv₀, hU.const]
        intro hinv

        have : IsUnit (p.coeff n) := ⟨⟨p.coeff n, ⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ h0),
          Subtype.ext (inv_mul_cancel₀ h0)⟩, rfl⟩
        exact hc this
    have h2 : U.valuation (J ^ n) ≤ 1 := (U.valuation_le_one_iff _).mpr (U.pow_mem hU.mem n)
    calc U.valuation (algebraMap L E (p.coeff n : L)) * U.valuation (J ^ n)
        ≤ U.valuation (algebraMap L E (p.coeff n : L)) * 1 := mul_le_mul_right h2 _
      _ < 1 := by rw [mul_one]; exact h1
  refine Finset.sum_induction _ (fun x => x ∈ U.nonunits) (fun a b ha hb => U.nonunits.add_mem ha hb)
    U.nonunits.zero_mem (fun n _ => hterm n)

theorem div_mem_iff {U : ValuationSubring E} (hU : GaussLike A J U) (r' s' : Polynomial ↥A)
    (hprim : r'.map (IsLocalRing.residue ↥A) ≠ 0 ∨ s'.map (IsLocalRing.residue ↥A) ≠ 0) :
    aeval J (r'.map (algebraMap ↥A L)) / aeval J (s'.map (algebraMap ↥A L)) ∈ U ↔
      (s'.map (IsLocalRing.residue ↥A) ≠ 0 ∨ aeval J (s'.map (algebraMap ↥A L)) = 0) := by
  set R := aeval J (r'.map (algebraMap ↥A L)) with hR
  set S := aeval J (s'.map (algebraMap ↥A L)) with hS
  constructor
  · intro hmem
    by_contra hcon
    push Not at hcon
    obtain ⟨hs0, hS0⟩ := hcon

    have hr : r'.map (IsLocalRing.residue ↥A) ≠ 0 := hprim.resolve_right (not_not.mpr hs0)
    have hRu : U.valuation R = 1 := hU.unit r' hr
    have hSn : S ∈ U.nonunits := aeval_mem_nonunits hU s' hs0

    have hR0 : R ≠ 0 := fun h => by rw [h, map_zero] at hRu; exact zero_ne_one hRu
    have hval : U.valuation (R / S) ≤ 1 := (U.valuation_le_one_iff _).mpr hmem
    rw [map_div₀, hRu, one_div, inv_le_one₀ ((Valuation.pos_iff _).mpr hS0)] at hval
    exact (not_le.mpr (U.mem_nonunits_iff.mp hSn)) hval
  · rintro (hs | hS0)
    · have hSu : U.valuation S = 1 := hU.unit s' hs
      have hS0 : S ≠ 0 := fun h => by rw [h, map_zero] at hSu; exact zero_ne_one hSu
      apply (U.valuation_le_one_iff _).mp
      rw [map_div₀, hSu, div_one]
      exact (U.valuation_le_one_iff _).mpr (aeval_mem hU r')
    · rw [hS0, div_zero]; exact U.zero_mem

theorem mem_iff_mem_of_mem_adjoin {U U' : ValuationSubring E} (hU : GaussLike A J U) (hU' : GaussLike A J U')
    {e : E} (he : e ∈ IntermediateField.adjoin L {J}) : e ∈ U ↔ e ∈ U' := by
  obtain ⟨r, s, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff (F := L) e).mp he
  by_cases h0 : r = 0 ∧ s = 0
  · obtain ⟨rfl, rfl⟩ := h0
    simp [U.zero_mem, U'.zero_mem]
  have h : r ≠ 0 ∨ s ≠ 0 := by tauto
  obtain ⟨c, r', s', hc, hr', hs', hprim⟩ := exists_rescale A r s h

  have hc' : algebraMap L E c ≠ 0 := by rw [map_ne_zero_iff _ (algebraMap L E).injective]; exact hc
  have heq : aeval J r / aeval J s = aeval J (r'.map (algebraMap ↥A L)) / aeval J (s'.map (algebraMap ↥A L)) := by
    rw [hr', hs', map_mul, map_mul, Polynomial.aeval_C, mul_div_mul_left _ _ hc']
  rw [heq, div_mem_iff hU r' s' hprim, div_mem_iff hU' r' s' hprim]

end JLine
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_forall_mem_iff_residueFst_eq_zero_or_forall_mem_iff_residueSnd_eq_zero_of_height_one.C1bGlue"

namespace GaussID

local notation "Lb" => AlgebraicClosure ℚ

theorem inv_mem_of_isUnit {F : Type*} [Field F] (V : ValuationSubring F) {x : F} (hx : x ∈ V)
    (hu : IsUnit (⟨x, hx⟩ : ↥V)) : x⁻¹ ∈ V := by
  obtain ⟨u, hu⟩ := hu
  have hcoe : ((u : ↥V) : F) = x := by rw [hu]
  have hinv : (((u⁻¹ : (↥V)ˣ) : ↥V) : F) = x⁻¹ := by
    have h1 : x * (((u⁻¹ : (↥V)ˣ) : ↥V) : F) = 1 := by
      rw [← hcoe, ← MulMemClass.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, OneMemClass.coe_one]
    exact (inv_eq_of_mul_eq_one_right h1).symm
  rw [← hinv]
  exact SetLike.coe_mem _

theorem jqModC_eq_coeffEmb : jqModC (AlgebraicClosure ℚ) = coeffEmb (AlgebraicClosure ℚ) jq := by
  rw [← jqModC_rat, coeffEmb, coeffMap_jqModC]

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

variable (R : ProlongationTuple P) (hqN : ¬ q ∣ N)

def IntExp (f : ↥(modularFunctionFieldBar (N * q))) : Prop :=
  ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
    (f : LaurentSeries Lb) * coeffMap A.subtype y = coeffMap A.subtype x

def IntExpAL (f : ↥(modularFunctionFieldBar (N * q))) : Prop :=
  ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
    ((atkinLehnerBar N q f : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries Lb) * coeffMap A.subtype y
      = coeffMap A.subtype x

include hqN in
theorem residue₁_const (a : ↥A) :
    ∃ h : algebraMap Lb ↥(modularFunctionFieldBar (N * q)) (a : Lb) ∈ R.R₁.integers,
      R.residue₁ ⟨_, h⟩ = algebraMap k ↥(modularFunctionFieldC k N) (red a) := by
  obtain ⟨h₁, -, -, -, e1, -, -, -⟩ := R.residue_jFun_sub_jQFun_sub hqN (0 : A)
  obtain ⟨h₁', -, -, -, e1', -, -, -⟩ := R.residue_jFun_sub_jQFun_sub hqN a
  have hmem : algebraMap Lb ↥(modularFunctionFieldBar (N * q)) (a : Lb) ∈ R.R₁.integers :=
    (R.R₁.algebraMap_mem_iff (a : Lb)).mpr a.2
  refine ⟨hmem, ?_⟩
  have hx : (⟨_, hmem⟩ : ↥R.R₁.integers) = ⟨_, h₁⟩ - ⟨_, h₁'⟩ := by
    apply Subtype.ext
    show algebraMap Lb ↥(modularFunctionFieldBar (N * q)) (a : Lb) = _
    simp only [AddSubgroupClass.coe_sub, ZeroMemClass.coe_zero, map_zero, sub_zero, sub_sub_cancel]
  rw [hx, map_sub, e1, e1', map_zero, map_zero, sub_zero, sub_sub_cancel]

include hqN in
theorem residue₂_const (a : ↥A) :
    ∃ h : algebraMap Lb ↥(modularFunctionFieldBar (N * q)) (a : Lb) ∈ R.R₂.integers,
      R.residue₂ ⟨_, h⟩ = algebraMap k ↥(modularFunctionFieldC k N) (red a) := by
  obtain ⟨-, h₂, -, -, -, e2, -, -⟩ := R.residue_jFun_sub_jQFun_sub hqN (0 : A)
  obtain ⟨-, h₂', -, -, -, e2', -, -⟩ := R.residue_jFun_sub_jQFun_sub hqN a
  have hmem : algebraMap Lb ↥(modularFunctionFieldBar (N * q)) (a : Lb) ∈ R.R₂.integers :=
    (R.R₂.algebraMap_mem_iff (a : Lb)).mpr a.2
  refine ⟨hmem, ?_⟩
  have hx : (⟨_, hmem⟩ : ↥R.R₂.integers) = ⟨_, h₂⟩ - ⟨_, h₂'⟩ := by
    apply Subtype.ext
    show algebraMap Lb ↥(modularFunctionFieldBar (N * q)) (a : Lb) = _
    simp only [AddSubgroupClass.coe_sub, ZeroMemClass.coe_zero, map_zero, sub_zero, sub_sub_cancel]
  rw [hx, map_sub, e2, e2', map_zero, map_zero, sub_zero, sub_sub_cancel]

include hqN in
theorem residue₁_jFun :
    ∃ h : ProlongationTuple.jFun N q ∈ R.R₁.integers, R.residue₁ ⟨_, h⟩ = jGeomGen k N := by
  obtain ⟨h₁, -, -, -, e1, -, -, -⟩ := R.residue_jFun_sub_jQFun_sub hqN (0 : A)
  have hmem : ProlongationTuple.jFun N q ∈ R.R₁.integers := by
    have := h₁; simpa using this
  refine ⟨hmem, ?_⟩
  have hx : (⟨_, hmem⟩ : ↥R.R₁.integers) = ⟨_, h₁⟩ := Subtype.ext (by simp)
  rw [hx, e1, map_zero, map_zero, sub_zero]

include hqN in
theorem residue₂_jFun :
    ∃ h : ProlongationTuple.jFun N q ∈ R.R₂.integers, R.residue₂ ⟨_, h⟩ = jGeomGen k N ^ q := by
  obtain ⟨-, h₂, -, -, -, e2, -, -⟩ := R.residue_jFun_sub_jQFun_sub hqN (0 : A)
  have hmem : ProlongationTuple.jFun N q ∈ R.R₂.integers := by
    have := h₂; simpa using this
  refine ⟨hmem, ?_⟩
  have hx : (⟨_, hmem⟩ : ↥R.R₂.integers) = ⟨_, h₂⟩ := Subtype.ext (by simp)
  rw [hx, e2, map_zero, map_zero, sub_zero]

omit [CharP k q] in
theorem aeval_jGeomGen_pow_ne_zero {n : ℕ} (hn : n ≠ 0) {p : Polynomial k} (hp : p ≠ 0) :
    Polynomial.aeval (jGeomGen k N ^ n) p ≠ 0 := by
  intro h
  apply hp
  refine transcendental_iff.mp ((transcendental_jqModC k).pow (Nat.pos_of_ne_zero hn)) p ?_
  have hc := congrArg (fun z : ↥(modularFunctionFieldC k N) => (z : LaurentSeries k)) h
  simp only [ZeroMemClass.coe_zero] at hc
  have h2 := Polynomial.aeval_algHom_apply (modularFunctionFieldC k N).val (jGeomGen k N ^ n) p

  have h3 : ((modularFunctionFieldC k N).val (jGeomGen k N ^ n) : LaurentSeries k) = jqModC k ^ n := by
    rw [map_pow]; rfl
  rw [h3] at h2
  rw [h2]
  exact hc

omit [CharP k q] in
variable (N k) in

theorem jGeomGen_sub_pow_ne_zero' : jGeomGen k N - (jGeomGen k N ^ q) ^ q ≠ 0 := by
  intro h
  have hq : 1 < q ^ 2 := Nat.one_lt_pow (by norm_num) (Fact.out : q.Prime).one_lt
  apply FiniteField.X_pow_card_sub_X_ne_zero k hq
  refine transcendental_iff.mp (transcendental_jqModC k) _ ?_
  have hc := congrArg (fun z : ↥(modularFunctionFieldC k N) => (z : LaurentSeries k)) h
  simp only [AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, coe_jGeomGen, ZeroMemClass.coe_zero] at hc
  have hc' : (jqModC k ^ q) ^ q = jqModC k := (sub_eq_zero.mp hc).symm
  rw [map_sub, map_pow, Polynomial.aeval_X, pow_two, pow_mul, hc', sub_self]

include R hqN in
theorem map_red_ne_zero {p : Polynomial ↥A} (hp : p.map (IsLocalRing.residue ↥A) ≠ 0) : p.map red ≠ 0 := by
  have hred : red = R.redBar.comp (IsLocalRing.residue ↥A) := RingHom.ext (fun a => (R.redBar_residue a).symm)
  rw [hred, ← Polynomial.map_map]
  exact fun h => hp (Polynomial.map_injective _ R.redBar.injective (by rw [h, Polynomial.map_zero]))

include hqN in

theorem valuation_integersFst_aeval_jFun (p : Polynomial ↥A) (hp : p.map (IsLocalRing.residue ↥A) ≠ 0) :
    R.R₁.integers.valuation (Polynomial.aeval (ProlongationTuple.jFun N q) (p.map (algebraMap ↥A Lb))) = 1 := by
  classical
  obtain ⟨hJ, eJ⟩ := residue₁_jFun R hqN
  let φ : ↥A →+* ↥R.R₁.integers := ((algebraMap Lb ↥(modularFunctionFieldBar (N * q))).comp A.subtype).codRestrict
    R.R₁.integers.toSubring (fun a => (R.R₁.algebraMap_mem_iff (a : Lb)).mpr a.2)
  let X : ↥R.R₁.integers := Polynomial.eval₂ φ ⟨_, hJ⟩ p
  have hX : (X : ↥(modularFunctionFieldBar (N * q))) = Polynomial.aeval (ProlongationTuple.jFun N q) (p.map (algebraMap ↥A Lb)) := by
    show R.R₁.integers.toSubring.subtype (Polynomial.eval₂ φ ⟨_, hJ⟩ p) = _
    rw [Polynomial.hom_eval₂, Polynomial.aeval_def, Polynomial.eval₂_map]
    rfl
  have hres : R.residue₁ X = Polynomial.aeval (jGeomGen k N) (p.map red) := by
    show R.residue₁ (Polynomial.eval₂ φ ⟨_, hJ⟩ p) = _
    rw [Polynomial.hom_eval₂, eJ, Polynomial.aeval_def, Polynomial.eval₂_map]
    congr 1
    refine RingHom.ext (fun a => ?_)
    obtain ⟨ha, ea⟩ := residue₁_const R hqN a
    exact ea
  have hne : R.residue₁ X ≠ 0 := by
    rw [hres, ← pow_one (jGeomGen k N)]
    exact aeval_jGeomGen_pow_ne_zero one_ne_zero (map_red_ne_zero R hqN hp)
  have hunit : IsUnit X := by
    apply R.R₁.isUnit_of_residue_ne_zero
    intro h0; apply hne
    rw [residue₁_apply, h0, map_zero]
  rw [← hX]
  exact (R.R₁.integers.valuation_eq_one_iff X).mp hunit

include hqN in

theorem valuation_integersSnd_aeval_jFun (p : Polynomial ↥A) (hp : p.map (IsLocalRing.residue ↥A) ≠ 0) :
    R.R₂.integers.valuation (Polynomial.aeval (ProlongationTuple.jFun N q) (p.map (algebraMap ↥A Lb))) = 1 := by
  classical
  obtain ⟨hJ, eJ⟩ := residue₂_jFun R hqN
  let φ : ↥A →+* ↥R.R₂.integers := ((algebraMap Lb ↥(modularFunctionFieldBar (N * q))).comp A.subtype).codRestrict
    R.R₂.integers.toSubring (fun a => (R.R₂.algebraMap_mem_iff (a : Lb)).mpr a.2)
  let X : ↥R.R₂.integers := Polynomial.eval₂ φ ⟨_, hJ⟩ p
  have hX : (X : ↥(modularFunctionFieldBar (N * q))) = Polynomial.aeval (ProlongationTuple.jFun N q) (p.map (algebraMap ↥A Lb)) := by
    show R.R₂.integers.toSubring.subtype (Polynomial.eval₂ φ ⟨_, hJ⟩ p) = _
    rw [Polynomial.hom_eval₂, Polynomial.aeval_def, Polynomial.eval₂_map]
    rfl
  have hres : R.residue₂ X = Polynomial.aeval (jGeomGen k N ^ q) (p.map red) := by
    show R.residue₂ (Polynomial.eval₂ φ ⟨_, hJ⟩ p) = _
    rw [Polynomial.hom_eval₂, eJ, Polynomial.aeval_def, Polynomial.eval₂_map]
    congr 1
    refine RingHom.ext (fun a => ?_)
    obtain ⟨ha, ea⟩ := residue₂_const R hqN a
    exact ea
  have hne : R.residue₂ X ≠ 0 := by
    rw [hres]
    exact aeval_jGeomGen_pow_ne_zero (Fact.out : q.Prime).ne_zero (map_red_ne_zero R hqN hp)
  have hunit : IsUnit X := by
    apply R.R₂.isUnit_of_residue_ne_zero
    intro h0; apply hne
    rw [residue₂_apply, h0, map_zero]
  rw [← hX]
  exact (R.R₂.integers.valuation_eq_one_iff X).mp hunit

include R hqN in

theorem liesOverPrime : A.LiesOverPrime q := by
  show ((q : ℕ) : Lb) ∈ A.nonunits
  have hq : ((q : ℕ) : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
    rw [← IsLocalRing.residue_eq_zero_iff, ← map_eq_zero_iff _ R.redBar.injective, R.redBar_residue, map_natCast]
    exact CharP.cast_eq_zero k q
  have := (ValuationSubring.coe_mem_nonunits_iff (a := ((q : ℕ) : ↥A))).mpr hq
  simpa using this

include hqN in
theorem integersFst_ne_integersSnd : R.R₁.integers ≠ R.R₂.integers := by
  obtain ⟨h₁, h₂, h₃, h₄, e1, e2, e3, e4⟩ := R.residue_jFun_sub_jQFun_sub hqN (0 : A)

  set g : ↥(modularFunctionFieldBar (N * q)) :=
    (ProlongationTuple.jQFun N q - algebraMap Lb _ ((0 : A) : Lb)) - (ProlongationTuple.jFun N q - algebraMap Lb _ ((0 : A) : Lb)) ^ q
    with hg
  have hg₁ : g ∈ R.R₁.integers := sub_mem h₃ (pow_mem h₁ q)
  have hg₂ : g ∈ R.R₂.integers := sub_mem h₄ (pow_mem h₂ q)
  have hres₁ : R.residue₁ ⟨g, hg₁⟩ = 0 := by
    have : (⟨g, hg₁⟩ : ↥R.R₁.integers) = ⟨_, h₃⟩ - ⟨_, h₁⟩ ^ q := Subtype.ext rfl
    rw [this, map_sub, map_pow, e3, e1]
    simp only [map_zero, sub_zero, sub_self]
  have hres₂ : R.residue₂ ⟨g, hg₂⟩ ≠ 0 := by
    have : (⟨g, hg₂⟩ : ↥R.R₂.integers) = ⟨_, h₄⟩ - ⟨_, h₂⟩ ^ q := Subtype.ext rfl
    rw [this, map_sub, map_pow, e4, e2]
    simp only [map_zero, sub_zero]
    exact jGeomGen_sub_pow_ne_zero' N k
  have hunit₂ : IsUnit (⟨g, hg₂⟩ : ↥R.R₂.integers) := by
    apply R.R₂.isUnit_of_residue_ne_zero
    intro h0; apply hres₂; rw [residue₂_apply, h0, map_zero]
  have hg0 : g ≠ 0 := fun h0 => hres₂ (by
    have : (⟨g, hg₂⟩ : ↥R.R₂.integers) = 0 := Subtype.ext h0
    rw [this, map_zero])
  have hinv₂ : g⁻¹ ∈ R.R₂.integers := inv_mem_of_isUnit _ hg₂ hunit₂
  intro heq
  have hinv₁ : g⁻¹ ∈ R.R₁.integers := heq ▸ hinv₂
  have h1 : R.residue₁ (⟨g, hg₁⟩ * ⟨g⁻¹, hinv₁⟩) = 1 := by
    have : (⟨g, hg₁⟩ * ⟨g⁻¹, hinv₁⟩ : ↥R.R₁.integers) = 1 := Subtype.ext (mul_inv_cancel₀ hg0)
    rw [this, map_one]
  rw [map_mul, hres₁, zero_mul] at h1
  exact zero_ne_one h1

include hqN in
theorem gaussLike_integersFst : JLine.GaussLike A (ProlongationTuple.jFun N q) R.R₁.integers :=
  ⟨fun a => R.R₁.algebraMap_mem_iff a, (residue₁_jFun R hqN).1, valuation_integersFst_aeval_jFun R hqN⟩

include hqN in
theorem gaussLike_integersSnd : JLine.GaussLike A (ProlongationTuple.jFun N q) R.R₂.integers :=
  ⟨fun a => R.R₂.algebraMap_mem_iff a, (residue₂_jFun R hqN).1, valuation_integersSnd_aeval_jFun R hqN⟩

omit [Fact q.Prime] [NeZero N] [CharP k q] in
theorem algebraMap_laurentSeries_eq_single' {R₀ : Type*} [CommRing R₀] (c : R₀) :
    algebraMap R₀ (LaurentSeries R₀) c = HahnSeries.single 0 c := by
  have h1 : algebraMap R₀ (PowerSeries R₀) c = PowerSeries.C c := by simp
  rw [HahnSeries.algebraMap_apply', h1, HahnSeries.ofPowerSeries_C]
  rfl

omit [Fact q.Prime] [NeZero N] [CharP k q] in
theorem coeffMap_algebraMap' {R₀ S₀ : Type*} [CommRing R₀] [CommRing S₀] (f : R₀ →+* S₀) (r : R₀) :
    coeffMap f (algebraMap R₀ (LaurentSeries R₀) r) = algebraMap S₀ (LaurentSeries S₀) (f r) := by
  rw [algebraMap_laurentSeries_eq_single', algebraMap_laurentSeries_eq_single', coeffMap_single]

omit [CharP k q] in

theorem coeffMap_subtype_algebraMap (a : ↥A) :
    coeffMap A.subtype (algebraMap ↥A (LaurentSeries ↥A) a) = algebraMap Lb (LaurentSeries Lb) (a : Lb) :=
  coeffMap_algebraMap' A.subtype a

theorem gaussLike_of_forall_mem_iff_integralExpansion
    (G : ValuationSubring ↥(modularFunctionFieldBar (N * q)))
    (hG : ∀ f : ↥(modularFunctionFieldBar (N * q)), f ∈ G ↔
      ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
        (f : LaurentSeries Lb) * coeffMap A.subtype y = coeffMap A.subtype x) :
    JLine.GaussLike A (ProlongationTuple.jFun N q) G := by
  classical
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  refine ⟨fun a => ?_, ?_, fun p hp => ?_⟩
  ·
    rw [hG]
    constructor
    · rintro ⟨x, y, hy, hxy⟩

      have : ∃ n, (coeffMap (IsLocalRing.residue ↥A) y).coeff n ≠ 0 := by
        by_contra hall; push Not at hall
        exact hy (HahnSeries.ext (funext hall))
      obtain ⟨n, hn⟩ := this
      rw [coeffMap_coeff] at hn
      have hu : IsUnit (y.coeff n) := (IsLocalRing.residue_ne_zero_iff_isUnit _).mp hn
      have hcoeff := congrArg (fun z : LaurentSeries Lb => z.coeff n) hxy
      beta_reduce at hcoeff
      have hlhs : ((algebraMap Lb ↥(modularFunctionFieldBar (N * q)) a : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries Lb)
          = algebraMap Lb (LaurentSeries Lb) a := rfl
      rw [hlhs, algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_zero_mul, coeffMap_coeff, coeffMap_coeff] at hcoeff

      have hy0 : ((y.coeff n : ↥A) : Lb) ≠ 0 := fun h => hu.ne_zero (Subtype.ext h)
      have hinv : ((y.coeff n : ↥A) : Lb)⁻¹ ∈ A := inv_mem_of_isUnit A (y.coeff n).2 (by simpa using hu)
      have ha : a = (x.coeff n : Lb) * ((y.coeff n : ↥A) : Lb)⁻¹ := by
        rw [eq_mul_inv_iff_mul_eq₀ hy0]; exact hcoeff
      rw [ha]
      exact A.mul_mem _ _ (x.coeff n).2 hinv
    · intro ha
      refine ⟨algebraMap ↥A (LaurentSeries ↥A) ⟨a, ha⟩, 1, by rw [map_one]; exact one_ne_zero, ?_⟩
      rw [map_one, mul_one, coeffMap_subtype_algebraMap]
      rfl
  ·
    rw [hG]
    refine ⟨jqModC ↥A, 1, by rw [map_one]; exact one_ne_zero, ?_⟩
    rw [map_one, mul_one, coeffMap_jqModC]
    exact jqModC_eq_coeffEmb.symm
  ·
    set y : LaurentSeries ↥A := Polynomial.eval₂ (algebraMap ↥A (LaurentSeries ↥A)) (jqModC ↥A) p with hy
    set f : ↥(modularFunctionFieldBar (N * q)) := Polynomial.aeval (ProlongationTuple.jFun N q) (p.map (algebraMap ↥A Lb)) with hf
    have hcoe : (f : LaurentSeries Lb) = coeffMap A.subtype y := by
      rw [hf, hy, Polynomial.hom_eval₂, coeffMap_jqModC]
      have h1 : (f : LaurentSeries Lb) = Polynomial.aeval ((ProlongationTuple.jFun N q : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries Lb)
          (p.map (algebraMap ↥A Lb)) := by
        rw [hf]
        exact (Polynomial.aeval_algHom_apply (modularFunctionFieldBar (N * q)).val (ProlongationTuple.jFun N q) _).symm
      rw [hf] at h1
      rw [h1, Polynomial.aeval_def, Polynomial.eval₂_map]
      have hJ : ((ProlongationTuple.jFun N q : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries Lb) = jqModC Lb :=
        jqModC_eq_coeffEmb.symm
      rw [hJ]
      congr 1
      exact RingHom.ext (fun a => (coeffMap_subtype_algebraMap a).symm)
    have hybar : coeffMap (IsLocalRing.residue ↥A) y ≠ 0 := by
      rw [hy, Polynomial.hom_eval₂, coeffMap_jqModC]
      have : ((coeffMap (IsLocalRing.residue ↥A)).comp (algebraMap ↥A (LaurentSeries ↥A)))
          = (algebraMap (IsLocalRing.ResidueField ↥A) (LaurentSeries (IsLocalRing.ResidueField ↥A))).comp (IsLocalRing.residue ↥A) := by
        exact RingHom.ext (fun a => coeffMap_algebraMap' (IsLocalRing.residue ↥A) a)
      rw [this, ← Polynomial.eval₂_map, ← Polynomial.aeval_def]
      exact fun h0 => hp (transcendental_iff.mp (transcendental_jqModC (IsLocalRing.ResidueField ↥A)) _ h0)
    have hy0 : coeffMap A.subtype y ≠ 0 := by
      intro h0
      apply hybar
      have : y = 0 := by
        apply HahnSeries.ext; funext n
        have := congrArg (fun z : LaurentSeries Lb => z.coeff n) h0
        simp only [coeffMap_coeff, HahnSeries.coeff_zero] at this
        exact Subtype.ext this
      rw [this, map_zero]
    have hf0 : f ≠ 0 := fun h => hy0 (by rw [← hcoe, h]; rfl)
    have hfG : f ∈ G := (hG f).mpr ⟨y, 1, by rw [map_one]; exact one_ne_zero, by rw [map_one, mul_one, hcoe]⟩
    have hfiG : f⁻¹ ∈ G := (hG f⁻¹).mpr ⟨1, y, hybar, by
      rw [map_one]
      change (f : LaurentSeries Lb)⁻¹ * coeffMap A.subtype y = 1
      rw [hcoe, inv_mul_cancel₀ hy0]⟩
    have hu : IsUnit (⟨f, hfG⟩ : ↥G) :=
      ⟨⟨⟨f, hfG⟩, ⟨f⁻¹, hfiG⟩, Subtype.ext (mul_inv_cancel₀ hf0), Subtype.ext (inv_mul_cancel₀ hf0)⟩, rfl⟩
    exact (G.valuation_eq_one_iff ⟨f, hfG⟩).mp hu

include hqN in

theorem eq_integersFst_or_eq_integersSnd_of_gaussLike (W : ValuationSubring ↥(modularFunctionFieldBar (N * q)))
    (hW : JLine.GaussLike A (ProlongationTuple.jFun N q) W) :
    W = R.R₁.integers ∨ W = R.R₂.integers := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hA := liesOverPrime R hqN
  obtain ⟨Rp, h1, -, -, -, -, -, h5⟩ :=
    ModularCurve.exists_regularProlongation_pair_valuationSubring_eq_or_eq_of_not_dvd N q hqN A hA
  have hG0 : JLine.GaussLike A (ProlongationTuple.jFun N q) (Rp 0).integers :=
    gaussLike_of_forall_mem_iff_integralExpansion (Rp 0).integers h1
  have key : ∀ U : ValuationSubring ↥(modularFunctionFieldBar (N * q)), JLine.GaussLike A (ProlongationTuple.jFun N q) U →
      U = (Rp 0).integers ∨ U = (Rp 1).integers := fun U hU =>
    h5 U (fun e he => JLine.mem_iff_mem_of_mem_adjoin hU hG0 he)
  have k1 := key _ (gaussLike_integersFst R hqN)
  have k2 := key _ (gaussLike_integersSnd R hqN)
  have kW := key _ hW
  have hne := integersFst_ne_integersSnd R hqN
  rcases k1 with k1 | k1 <;> rcases k2 with k2 | k2
  · exact absurd (k1.trans k2.symm) hne
  · rcases kW with kW | kW
    · exact Or.inl (kW.trans k1.symm)
    · exact Or.inr (kW.trans k2.symm)
  · rcases kW with kW | kW
    · exact Or.inr (kW.trans k2.symm)
    · exact Or.inl (kW.trans k1.symm)
  · exact absurd (k1.trans k2.symm) hne

end GaussID
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_forall_mem_iff_residueFst_eq_zero_or_forall_mem_iff_residueSnd_eq_zero_of_height_one.C1bGlue"

open Polynomial IsLocalRing ModularCurve ModularCurve.NodeLocalized ModularCurve.CharPReduction

namespace P5

local notation "Lb" => AlgebraicClosure ℚ

section LinearFactor

variable {E : Type*} [Field E] [Algebra Lb E] (U : ValuationSubring E) (J : E)

noncomputable abbrev consts : ValuationSubring Lb := U.comap (algebraMap Lb E)

theorem mem_consts_iff (b : Lb) : b ∈ consts U ↔ algebraMap Lb E b ∈ U := Iff.rfl

theorem mem_nonunits_consts_iff (b : Lb) : b ∈ (consts U).nonunits ↔ algebraMap Lb E b ∈ U.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, mem_consts_iff, map_inv₀,
    map_eq_zero]

variable {U J}

theorem aeval_mem (hJ : J ∈ U) (p : Polynomial ↥(consts U)) : aeval J (p.map (algebraMap ↥(consts U) Lb)) ∈ U := by
  rw [Polynomial.aeval_map_algebraMap, Polynomial.aeval_eq_sum_range]
  refine U.toSubring.sum_mem (fun n _ => ?_)
  rw [Algebra.smul_def, IsScalarTower.algebraMap_apply ↥(consts U) Lb E]
  exact U.mul_mem _ _ (p.coeff n).2 (U.pow_mem hJ n)

theorem aeval_mem_nonunits (hJ : J ∈ U) (p : Polynomial ↥(consts U)) (hp : p.map (IsLocalRing.residue ↥(consts U)) = 0) :
    aeval J (p.map (algebraMap ↥(consts U) Lb)) ∈ U.nonunits := by
  rw [Polynomial.aeval_map_algebraMap, Polynomial.aeval_eq_sum_range]
  have hterm : ∀ n, p.coeff n • J ^ n ∈ U.nonunits := by
    intro n
    have hc : (p.coeff n) ∈ IsLocalRing.maximalIdeal ↥(consts U) := by
      rw [← IsLocalRing.residue_eq_zero_iff]
      have := congrArg (fun z => Polynomial.coeff z n) hp
      simpa [Polynomial.coeff_map] using this
    have h1 : algebraMap Lb E (p.coeff n : Lb) ∈ U.nonunits :=
      (mem_nonunits_consts_iff U _).mp (ValuationSubring.coe_mem_nonunits_iff.mpr hc)
    rw [Algebra.smul_def, IsScalarTower.algebraMap_apply ↥(consts U) Lb E, ValuationSubring.mem_nonunits_iff, map_mul]
    have h2 : U.valuation (J ^ n) ≤ 1 := (U.valuation_le_one_iff _).mpr (U.pow_mem hJ n)
    calc U.valuation (algebraMap Lb E (p.coeff n : Lb)) * U.valuation (J ^ n)
        ≤ U.valuation (algebraMap Lb E (p.coeff n : Lb)) * 1 := mul_le_mul_right h2 _
      _ < 1 := by rw [mul_one]; exact U.mem_nonunits_iff.mp h1
  refine Finset.sum_induction _ (fun x => x ∈ U.nonunits) (fun a b ha hb => U.nonunits.add_mem ha hb)
    U.nonunits.zero_mem (fun n _ => hterm n)

theorem exists_sub_algebraMap_mem_nonunits (hJ : J ∈ U) (p : Polynomial ↥(consts U))
    (hp : p.map (IsLocalRing.residue ↥(consts U)) ≠ 0)
    (hx : aeval J (p.map (algebraMap ↥(consts U) Lb)) ∈ U.nonunits) :
    ∃ β : ↥(consts U), J - algebraMap Lb E (β : Lb) ∈ U.nonunits := by
  classical
  haveI : IsAlgClosed (IsLocalRing.ResidueField ↥(consts U)) :=
    ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat (consts U)
  set pbar := p.map (IsLocalRing.residue ↥(consts U)) with hpbar

  have hfac := (IsAlgClosed.splits pbar).eq_prod_roots
  choose lift hlift using fun a : IsLocalRing.ResidueField ↥(consts U) => IsLocalRing.residue_surjective a
  set c : ↥(consts U) := lift pbar.leadingCoeff with hc
  set Q : Polynomial ↥(consts U) := C c * (pbar.roots.map (fun a => X - C (lift a))).prod with hQ
  have hQbar : Q.map (IsLocalRing.residue ↥(consts U)) = pbar := by
    rw [hQ, Polynomial.map_mul, Polynomial.map_C, hlift, Polynomial.map_multiset_prod, Multiset.map_map]
    conv_rhs => rw [hfac]
    congr 2
    refine Multiset.map_congr rfl (fun a _ => ?_)
    simp [hlift]

  have hdiff : aeval J ((p - Q).map (algebraMap ↥(consts U) Lb)) ∈ U.nonunits :=
    aeval_mem_nonunits hJ (p - Q) (by rw [Polynomial.map_sub, hQbar, hpbar, sub_self])
  have hQval : aeval J (Q.map (algebraMap ↥(consts U) Lb)) ∈ U.nonunits := by
    have : aeval J (Q.map (algebraMap ↥(consts U) Lb)) =
        aeval J (p.map (algebraMap ↥(consts U) Lb)) - aeval J ((p - Q).map (algebraMap ↥(consts U) Lb)) := by
      rw [Polynomial.map_sub, map_sub, sub_sub_cancel]
    rw [this]
    exact U.nonunits.sub_mem hx hdiff

  have hQeval : aeval J (Q.map (algebraMap ↥(consts U) Lb)) =
      algebraMap Lb E (c : Lb) * (pbar.roots.map (fun a => J - algebraMap Lb E (lift a : Lb))).prod := by
    rw [hQ, Polynomial.map_mul, Polynomial.map_C, map_mul, Polynomial.aeval_C, Polynomial.map_multiset_prod,
      map_multiset_prod, Multiset.map_map, Multiset.map_map]
    congr 1
    refine congrArg _ (Multiset.map_congr rfl (fun a _ => ?_))
    simp

  have hp0 : pbar.leadingCoeff ≠ 0 := fun h => hp (Polynomial.leadingCoeff_eq_zero.mp h)
  have hcu : algebraMap Lb E (c : Lb) ∉ U.nonunits := by
    rw [← mem_nonunits_consts_iff, ValuationSubring.coe_mem_nonunits_iff, ← IsLocalRing.residue_eq_zero_iff, hc, hlift]
    exact hp0

  have hprod : (pbar.roots.map (fun a => J - algebraMap Lb E (lift a : Lb))).prod ∈ U.nonunits := by
    rw [hQeval] at hQval
    rw [ValuationSubring.mem_nonunits_iff] at hQval hcu ⊢
    rw [map_mul] at hQval
    have hc1 : U.valuation (algebraMap Lb E (c : Lb)) = 1 := by
      have hle : U.valuation (algebraMap Lb E (c : Lb)) ≤ 1 := (U.valuation_le_one_iff _).mpr c.2
      exact le_antisymm hle (not_lt.mp hcu)
    rwa [hc1, one_mul] at hQval

  by_contra hall
  push Not at hall
  have hone : U.valuation (pbar.roots.map (fun a => J - algebraMap Lb E (lift a : Lb))).prod = 1 := by
    rw [map_multiset_prod, Multiset.map_map]
    apply Multiset.prod_eq_one
    intro v hv
    obtain ⟨a, -, rfl⟩ := Multiset.mem_map.mp hv
    simp only [Function.comp_apply]
    have hmem : J - algebraMap Lb E (lift a : Lb) ∈ U := U.toSubring.sub_mem hJ (lift a).2
    have hle : U.valuation (J - algebraMap Lb E (lift a : Lb)) ≤ 1 := (U.valuation_le_one_iff _).mpr hmem
    have hnot := hall (lift a)
    rw [ValuationSubring.mem_nonunits_iff, not_lt] at hnot
    exact le_antisymm hle hnot
  rw [ValuationSubring.mem_nonunits_iff, hone] at hprod
  exact lt_irrefl _ hprod

end LinearFactor
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_forall_mem_iff_residueFst_eq_zero_or_forall_mem_iff_residueSnd_eq_zero_of_height_one.C1bGlue"

section Port

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {M : ℕ} [NeZero M]
  (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "LS" => LaurentSeries (AlgebraicClosure ℚ)
local notation "jj" => jqModC (AlgebraicClosure ℚ)

variable (A) in

noncomputable def inclA : coeffSubring A K →+* A where
  toFun a := ⟨a, a.2.1⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[scoped simp] theorem coe_inclA (a : coeffSubring A K) : ((inclA A K a : A) : ℚ̄) = a := rfl

theorem isDiscreteValuationRing_coeffSubring (hq : A.LiesOverPrime q) :
    IsDiscreteValuationRing (coeffSubring A K) := by
  rcases coeffSubring_eq_or_isDiscreteValuationRing A K with h | h
  · exfalso

    have hinvK : ((q : ℚ̄))⁻¹ ∈ K := inv_mem (_root_.natCast_mem K q)
    have hinvA0 : ((q : ℚ̄))⁻¹ ∈ coeffSubring A K := by rw [h]; exact hinvK
    have hinvA : ((q : ℚ̄))⁻¹ ∈ A := hinvA0.1
    have hq0 : (q : ℚ̄) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero

    rw [ValuationSubring.LiesOverPrime, ValuationSubring.mem_nonunits_iff] at hq
    have h1 := (A.valuation_le_one_iff _).mpr hinvA
    rw [map_inv₀, inv_le_one₀ (by rw [Valuation.pos_iff]; exact hq0)] at h1
    exact absurd hq (not_lt.mpr h1)
  · exact h

variable (A) in

noncomputable def e₀ : (coeffSubring A K)[X] →+* LS := eval₂RingHom (constSeries (coeffSubring A K)) jj

theorem e₀_eq_aeval (t : (coeffSubring A K)[X]) :
    e₀ A K t = aeval (jj : LS) (t.map (coeffSubring A K).subtype) := by
  rw [aeval_def, eval₂_map]; rfl

theorem e₀_C (a : coeffSubring A K) : e₀ A K (C a) = algebraMap ℚ̄ LS (a : ℚ̄) := by
  rw [e₀, coe_eval₂RingHom, eval₂_C]; rfl

theorem e₀_X : e₀ A K X = jj := by rw [e₀, coe_eval₂RingHom, eval₂_X]

theorem e₀_mem_jRing (t : (coeffSubring A K)[X]) : e₀ A K t ∈ jRing A K := by
  rw [e₀, coe_eval₂RingHom, eval₂_eq_sum, Polynomial.sum_def]
  refine Subring.sum_mem _ fun n _ => Subring.mul_mem _ ?_ (Subring.pow_mem _ ?_ _)
  · exact Subring.subset_closure (Or.inl ⟨_, rfl⟩)
  · exact Subring.subset_closure (Or.inr (Set.mem_singleton _))

theorem jRing_le_fieldOver : jRing A K ≤ (fieldOver M K).toSubring := by
  rw [jRing, Subring.closure_le]
  rintro x (⟨a, rfl⟩ | hx)
  · exact Subfield.subset_closure (Or.inl ⟨⟨a, a.2.2⟩, rfl⟩)
  · rw [Set.mem_singleton_iff.mp hx]
    exact Subfield.subset_closure (Or.inr (Set.mem_insert _ _))

theorem exists_e₀_eq {z : LS} (hz : z ∈ jRing A K) : ∃ t : (coeffSubring A K)[X], e₀ A K t = z := by
  refine Subring.closure_induction (fun x hx => ?_) ⟨0, map_zero _⟩ ⟨1, map_one _⟩
    (fun _ _ _ _ ⟨t, ht⟩ ⟨u, hu⟩ => ⟨t + u, by rw [map_add, ht, hu]⟩)
    (fun _ _ ⟨t, ht⟩ => ⟨-t, by rw [map_neg, ht]⟩)
    (fun _ _ _ _ ⟨t, ht⟩ ⟨u, hu⟩ => ⟨t * u, by rw [map_mul, ht, hu]⟩) hz
  rcases hx with ⟨a, rfl⟩ | hx
  · exact ⟨C a, e₀_C K a⟩
  · exact ⟨X, by rw [e₀_X, Set.mem_singleton_iff.mp hx]⟩

theorem e₀_mem_C (t : (coeffSubring A K)[X]) : e₀ A K t ∈ jIntegralClosure M A K := by
  refine ⟨jRing_le_fieldOver K (e₀_mem_jRing K t), ?_⟩
  have : e₀ A K t = algebraMap (jRing A K) LS ⟨e₀ A K t, e₀_mem_jRing K t⟩ := rfl
  rw [this]; exact isIntegral_algebraMap

variable (A) in

noncomputable def toC : (coeffSubring A K)[X] →+* jIntegralClosure M A K :=
  (e₀ A K).codRestrict _ (e₀_mem_C K)

@[scoped simp] theorem coe_toC (t : (coeffSubring A K)[X]) :
    ((toC (M := M) A K t : jIntegralClosure M A K) : LS) = e₀ A K t := rfl

theorem e₀_injective : Function.Injective (e₀ A K) := by
  intro t u h
  rw [e₀_eq_aeval, e₀_eq_aeval] at h
  have h0 : aeval (jj : LS) ((t - u).map (coeffSubring A K).subtype) = 0 := by
    rw [Polynomial.map_sub, map_sub, h, sub_self]
  have := (transcendental_iff.mp (ModularCurve.transcendental_jqModC ℚ̄)) _ h0
  rw [Polynomial.map_eq_zero_iff Subtype.val_injective] at this
  exact sub_eq_zero.mp this

theorem toC_injective : Function.Injective (toC (M := M) A K) := fun t u h =>
  e₀_injective K (congrArg (fun x : jIntegralClosure M A K => (x : LS)) h)

theorem isIntegral_toC (y : jIntegralClosure M A K) :
    letI := (toC (M := M) A K).toAlgebra
    IsIntegral (coeffSubring A K)[X] y := by
  letI := (toC (M := M) A K).toAlgebra
  obtain ⟨p, hpm, hp0⟩ := y.2.2

  let ψ : (coeffSubring A K)[X] →+* jRing A K := (e₀ A K).codRestrict _ (e₀_mem_jRing K)
  have hψ : Function.Surjective ψ := by
    rintro ⟨z, hz⟩
    obtain ⟨t, ht⟩ := exists_e₀_eq K hz
    exact ⟨t, Subtype.ext ht⟩
  obtain ⟨P, hP, -, hPm⟩ := lifts_and_natDegree_eq_and_monic (map_surjective ψ hψ p) hpm
  refine ⟨P, hPm, Subtype.ext ?_⟩

  show (jIntegralClosure M A K).subtype (eval₂ (algebraMap _ _) y P)
    = ((0 : jIntegralClosure M A K) : LS)
  rw [hom_eval₂, ZeroMemClass.coe_zero, ← hp0, ← hP, eval₂_map]
  congr 1

end Port
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_forall_mem_iff_residueFst_eq_zero_or_forall_mem_iff_residueSnd_eq_zero_of_height_one.C1bGlue"

section GoingDown

open Ideal

theorem eq_of_le_of_height_eq_one {R : Type*} [CommRing R] [IsDomain R]
    (p : Ideal R) [hp : p.IsPrime] (hh : p.height = 1)
    (q : Ideal R) (hq : q.IsPrime) (hq0 : q ≠ ⊥) (hqp : q ≤ p) : q = p := by
  set S := Localization.AtPrime p
  have hdim : ringKrullDim S = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p S, hh]
    norm_cast
  have hKDL : Ring.KrullDimLE 1 S :=
    Ring.krullDimLE_iff.mpr (le_of_eq (by rw [hdim, Nat.cast_one]))
  have hmax : ∀ P : Ideal S, P ≠ ⊥ → P.IsPrime → P.IsMaximal :=
    Ring.krullDimLE_one_iff_of_noZeroDivisors.mp hKDL
  have hdisj : Disjoint (p.primeCompl : Set R) q :=
    Set.disjoint_left.mpr fun x hx hxq => hx (hqp hxq)
  have hqS : (Ideal.map (algebraMap R S) q).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint p.primeCompl S q hq hdisj
  have hqS0 : Ideal.map (algebraMap R S) q ≠ ⊥ := by
    obtain ⟨b, hbq, hb⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hq0
    intro hbot
    have hbS : algebraMap R S b ∈ Ideal.map (algebraMap R S) q := Ideal.mem_map_of_mem _ hbq
    rw [hbot, Ideal.mem_bot] at hbS
    exact hb ((IsLocalization.injective S p.primeCompl_le_nonZeroDivisors) (by rw [hbS, map_zero]))
  have hqmax : Ideal.map (algebraMap R S) q = IsLocalRing.maximalIdeal S :=
    IsLocalRing.eq_maximalIdeal (hmax _ hqS0 hqS)
  rw [← IsLocalization.comap_map_of_isPrime_disjoint p.primeCompl S hq hdisj, hqmax,
    Localization.AtPrime.comap_maximalIdeal]

theorem under_eq_of_height_eq_one {R S : Type*} [CommRing R] [CommRing S] [IsDomain S] [Algebra R S]
    [FaithfulSMul R S] [Algebra.HasGoingDown R S]
    (𝔭 : Ideal S) [𝔭.IsPrime] (h𝔭 : 𝔭.height = 1)
    (P₀ : Ideal R) [P₀.IsPrime] (hP₀ : P₀ ≠ ⊥) (hle : P₀ ≤ 𝔭.under R) :
    𝔭.under R = P₀ := by
  by_contra hne
  have hlt : P₀ < 𝔭.under R := lt_of_le_of_ne hle (Ne.symm hne)

  obtain ⟨𝔮, h𝔮𝔭, h𝔮prime, h𝔮over⟩ := Ideal.exists_ideal_lt_liesOver_of_lt 𝔭 hlt
  have h𝔮ne : 𝔮 ≠ ⊥ := by
    rintro rfl
    apply hP₀
    rw [h𝔮over.over, Ideal.under_def, Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective R S)]
  exact h𝔮𝔭.ne (eq_of_le_of_height_eq_one 𝔭 h𝔭 𝔮 h𝔮prime h𝔮ne h𝔮𝔭.le)

end GoingDown
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_forall_mem_iff_residueFst_eq_zero_or_forall_mem_iff_residueSnd_eq_zero_of_height_one.C1bGlue"

section Annihilator

local notation "ℚ̄" => AlgebraicClosure ℚ

section Rescale
variable {L : Type*} [Field L] (A : ValuationSubring L)

theorem exists_map_eq_C_mul {r : Polynomial L} {b : L} (hb : b ≠ 0)
    (h : ∀ n, A.valuation (r.coeff n) ≤ A.valuation b) :
    ∃ r' : Polynomial ↥A, r'.map (algebraMap ↥A L) = C b⁻¹ * r := by
  have hl : C b⁻¹ * r ∈ Polynomial.lifts (algebraMap ↥A L) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_C_mul]
    have hle : A.valuation (b⁻¹ * r.coeff n) ≤ 1 := by
      rw [map_mul, map_inv₀]
      have hvb : A.valuation b ≠ 0 := (Valuation.ne_zero_iff _).mpr hb
      calc (A.valuation b)⁻¹ * A.valuation (r.coeff n) ≤ (A.valuation b)⁻¹ * A.valuation b :=
            mul_le_mul_right (h n) _
        _ = 1 := inv_mul_cancel₀ hvb
    exact ⟨⟨_, (A.valuation_le_one_iff _).mp hle⟩, rfl⟩
  exact (Polynomial.mem_lifts _).mp hl

theorem exists_rescale (r s : Polynomial L) (h : r ≠ 0 ∨ s ≠ 0) :
    ∃ (c : L) (r' s' : Polynomial ↥A), c ≠ 0 ∧ r'.map (algebraMap ↥A L) = C c * r ∧ s'.map (algebraMap ↥A L) = C c * s ∧
      (r'.map (IsLocalRing.residue ↥A) ≠ 0 ∨ s'.map (IsLocalRing.residue ↥A) ≠ 0) := by
  classical

  let T : Finset (Bool × ℕ) := (r.support.map ⟨fun n => (true, n), fun a b h => by simpa using h⟩) ∪
    (s.support.map ⟨fun n => (false, n), fun a b h => by simpa using h⟩)
  let f : Bool × ℕ → L := fun t => if t.1 then r.coeff t.2 else s.coeff t.2
  have hT : T.Nonempty := by
    rcases h with hr | hs
    · obtain ⟨n, hn⟩ := Polynomial.support_nonempty.mpr hr
      exact ⟨(true, n), Finset.mem_union_left _ (Finset.mem_map_of_mem _ hn)⟩
    · obtain ⟨n, hn⟩ := Polynomial.support_nonempty.mpr hs
      exact ⟨(false, n), Finset.mem_union_right _ (Finset.mem_map_of_mem _ hn)⟩
  obtain ⟨t₀, ht₀, hmax⟩ := Finset.exists_max_image T (fun t => A.valuation (f t)) hT
  set b := f t₀ with hb

  have hb0 : b ≠ 0 := by
    rcases Finset.mem_union.mp ht₀ with h1 | h1
    · obtain ⟨n, hn, rfl⟩ := Finset.mem_map.mp h1
      simpa [hb, f, Polynomial.mem_support_iff] using hn
    · obtain ⟨n, hn, rfl⟩ := Finset.mem_map.mp h1
      simpa [hb, f, Polynomial.mem_support_iff] using hn

  have hr : ∀ n, A.valuation (r.coeff n) ≤ A.valuation b := by
    intro n
    by_cases hn : n ∈ r.support
    · have := hmax (true, n) (Finset.mem_union_left _ (Finset.mem_map_of_mem _ hn))
      simpa [f] using this
    · rw [Polynomial.notMem_support_iff.mp hn, map_zero]; exact zero_le'
  have hs : ∀ n, A.valuation (s.coeff n) ≤ A.valuation b := by
    intro n
    by_cases hn : n ∈ s.support
    · have := hmax (false, n) (Finset.mem_union_right _ (Finset.mem_map_of_mem _ hn))
      simpa [f] using this
    · rw [Polynomial.notMem_support_iff.mp hn, map_zero]; exact zero_le'
  obtain ⟨r', hr'⟩ := exists_map_eq_C_mul A hb0 hr
  obtain ⟨s', hs'⟩ := exists_map_eq_C_mul A hb0 hs
  refine ⟨b⁻¹, r', s', inv_ne_zero hb0, hr', hs', ?_⟩

  have key : ∀ (p : Polynomial L) (p' : Polynomial ↥A) (n : ℕ), p'.map (algebraMap ↥A L) = C b⁻¹ * p → p.coeff n = b →
      p'.map (IsLocalRing.residue ↥A) ≠ 0 := by
    intro p p' n hp hn h0
    have h1 : (p'.map (IsLocalRing.residue ↥A)).coeff n = 0 := by rw [h0, Polynomial.coeff_zero]
    rw [Polynomial.coeff_map] at h1
    have h2 : algebraMap ↥A L (p'.coeff n) = 1 := by
      have := congrArg (fun z => Polynomial.coeff z n) hp
      simp only [Polynomial.coeff_map, Polynomial.coeff_C_mul] at this
      rw [this, hn, inv_mul_cancel₀ hb0]
    have h3 : p'.coeff n = 1 := (FaithfulSMul.algebraMap_injective ↥A L) (by rw [h2, map_one])
    rw [h3, map_one] at h1
    exact one_ne_zero h1
  rcases Finset.mem_union.mp ht₀ with h1 | h1
  · obtain ⟨n, hn, hn'⟩ := Finset.mem_map.mp h1
    left
    refine key r r' n hr' ?_
    have : t₀ = (true, n) := hn'.symm
    simp [hb, f, this]
  · obtain ⟨n, hn, hn'⟩ := Finset.mem_map.mp h1
    right
    refine key s s' n hs' ?_
    have : t₀ = (false, n) := hn'.symm
    simp [hb, f, this]

end Rescale
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_forall_mem_iff_residueFst_eq_zero_or_forall_mem_iff_residueSnd_eq_zero_of_height_one.C1bGlue"

theorem isAlgebraic_Qbar : Algebra.IsAlgebraic ℚ ℚ̄ := by
  have h : @Algebra.IsAlgebraic ℚ ℚ̄ _ _ (AlgebraicClosure.instAlgebra ℚ) := inferInstance
  exact h

noncomputable abbrev AK (A : ValuationSubring ℚ̄) (K : IntermediateField ℚ ℚ̄) : ValuationSubring ↥K :=
  A.comap (algebraMap ↥K ℚ̄)

theorem exists_primitive_aeval_eq_zero (A : ValuationSubring ℚ̄) (K : IntermediateField ℚ ℚ̄) (β : ℚ̄) :
    ∃ m₀ : Polynomial ↥(AK A K), m₀.map (IsLocalRing.residue ↥(AK A K)) ≠ 0 ∧
      aeval β ((m₀.map (algebraMap ↥(AK A K) ↥K)).map (algebraMap ↥K ℚ̄)) = 0 := by
  haveI := isAlgebraic_Qbar
  have hint : IsIntegral ℚ β := Algebra.IsIntegral.isIntegral β
  set m : Polynomial ↥K := (minpoly ℚ β).map (algebraMap ℚ ↥K) with hm
  have hm0 : m ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap ℚ ↥K).injective).mpr (minpoly.ne_zero hint)
  obtain ⟨c, m₀, m₁, hc, hm₀, hm₁, hprim⟩ := exists_rescale (AK A K) m m (Or.inl hm0)

  have heq : m₁ = m₀ := Polynomial.map_injective _ (FaithfulSMul.algebraMap_injective ↥(AK A K) ↥K) (by rw [hm₀, hm₁])
  refine ⟨m₀, ?_, ?_⟩
  · rcases hprim with h | h
    · exact h
    · rw [heq] at h; exact h
  · rw [hm₀, Polynomial.map_mul, Polynomial.map_C, map_mul, hm, Polynomial.map_map]
    have : (algebraMap ↥K ℚ̄).comp (algebraMap ℚ ↥K) = algebraMap ℚ ℚ̄ := RingHom.ext (fun x => by simp)
    rw [this, Polynomial.aeval_map_algebraMap, minpoly.aeval, mul_zero]

end Annihilator
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_forall_mem_iff_residueFst_eq_zero_or_forall_mem_iff_residueSnd_eq_zero_of_height_one.C1bGlue"

theorem fieldOver_le_bar (M : ℕ) [NeZero M] (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    {x : LaurentSeries (AlgebraicClosure ℚ)} (hx : x ∈ fieldOver M K) :
    x ∈ modularFunctionFieldBar M := by
  have hle : fieldOver M K ≤ (modularFunctionFieldBar M).toSubfield := by
    unfold fieldOver
    rw [Subfield.closure_le]
    rintro y (⟨c, rfl⟩ | hy)
    · exact (modularFunctionFieldBar M).algebraMap_mem (c : AlgebraicClosure ℚ)
    · rcases hy with rfl | rfl
      · have h : jqModC (AlgebraicClosure ℚ) = coeffEmb (AlgebraicClosure ℚ) jq := by
          rw [← jqModC_rat, coeffEmb, coeffMap_jqModC]
        rw [h]
        exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M (jq_mem M))
      · have h : jqNModC (AlgebraicClosure ℚ) M = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ M jq) := by
          rw [jqNModC, ← jqModC_rat, coeffEmb, coeffMap_qExpand, coeffMap_jqModC]
        rw [h]
        exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full M (dvd_refl M))
  exact hle hx

section Main

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "LS" => LaurentSeries (AlgebraicClosure ℚ)

noncomputable def toBar' : ↥(fieldOver (N * q) K) →+* ↥(modularFunctionFieldBar (N * q)) where
  toFun x := ⟨(x : LS), fieldOver_le_bar (N * q) K x.2⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

noncomputable def eAK : ↥(AK A K) ≃+* ↥(coeffSubring A K) where
  toFun x := ⟨((x : ↥K) : ℚ̄), x.2, (x : ↥K).2⟩
  invFun y := ⟨⟨(y : ℚ̄), y.2.2⟩, y.2.1⟩
  left_inv x := rfl
  right_inv y := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

@[scoped simp] theorem coe_eAK (x : ↥(AK A K)) : ((eAK K x : ↥(coeffSubring A K)) : ℚ̄) = ((x : ↥K) : ℚ̄) := rfl

variable {K}

theorem valuation_aeval_jFun_eq_one (hA : A.LiesOverPrime q)
    (𝔭 : Ideal ↥(jIntegralClosure (N * q) A K)) [𝔭.IsPrime] (h𝔭 : 𝔭.height = 1) (hq : ((q : ℕ) : ↥(jIntegralClosure (N * q) A K)) ∈ 𝔭)
    [Algebra ↥(jIntegralClosure (N * q) A K) ↥(fieldOver (N * q) K)] (halg : ∀ c : ↥(jIntegralClosure (N * q) A K), ((algebraMap ↥(jIntegralClosure (N * q) A K) ↥(fieldOver (N * q) K) c : ↥(fieldOver (N * q) K)) : LS) = (c : LS))
    (W₀ : ValuationSubring ↥(fieldOver (N * q) K))
    (hWmem : ∀ x : ↥(fieldOver (N * q) K), x ∈ W₀ ↔ ∃ r s : ↥(jIntegralClosure (N * q) A K), s ∉ 𝔭 ∧ x * algebraMap ↥(jIntegralClosure (N * q) A K) ↥(fieldOver (N * q) K) s = algebraMap ↥(jIntegralClosure (N * q) A K) ↥(fieldOver (N * q) K) r)
    (W : ValuationSubring ↥(modularFunctionFieldBar (N * q))) (hcomap : W.comap (toBar' K) = W₀)
    (p : Polynomial ↥(consts W)) (hp : p.map (IsLocalRing.residue ↥(consts W)) ≠ 0) :
    W.valuation (aeval (ModularCurve.PlaceSpecialization.ProlongationTuple.jFun N q) (p.map (algebraMap ↥(consts W) ℚ̄))) = 1 := by
  classical
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  haveI hdvr : IsDiscreteValuationRing ↥(coeffSubring A K) := isDiscreteValuationRing_coeffSubring K hA
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥(coeffSubring A K)

  have hCW₀ : ∀ c : ↥(jIntegralClosure (N * q) A K), algebraMap ↥(jIntegralClosure (N * q) A K) ↥(fieldOver (N * q) K) c ∈ W₀ := fun c =>
    (hWmem _).mpr ⟨c, 1, fun h => (Ideal.ne_top_iff_one 𝔭).mp (Ideal.IsPrime.ne_top inferInstance) h,
      by rw [map_one, mul_one]⟩
  have hW₀W : ∀ x : ↥(fieldOver (N * q) K), x ∈ W₀ ↔ toBar' K x ∈ W := fun x => by
    rw [← hcomap]; rfl
  have hCW : ∀ c : ↥(jIntegralClosure (N * q) A K), (⟨(c : LS), fieldOver_le_bar (N * q) K c.2.1⟩ : ↥(modularFunctionFieldBar (N * q))) ∈ W := by
    intro c
    have := (hW₀W _).mp (hCW₀ c)
    convert this using 1
    exact Subtype.ext (halg c).symm

  have hJ : (ModularCurve.PlaceSpecialization.ProlongationTuple.jFun N q : ↥(modularFunctionFieldBar (N * q))) ∈ W := by
    have h := hCW (toC (M := N * q) A K X)
    convert h using 1
    apply Subtype.ext
    show coeffEmb ℚ̄ jq = ((toC (M := N * q) A K X : ↥(jIntegralClosure (N * q) A K)) : LS)
    rw [coe_toC, e₀_X, ← jqModC_rat, coeffEmb, coeffMap_jqModC]

  have hA₀W : ∀ a : ↥(coeffSubring A K), algebraMap ℚ̄ ↥(modularFunctionFieldBar (N * q)) (a : ℚ̄) ∈ W := by
    intro a
    have h := hCW (toC (M := N * q) A K (Polynomial.C a))
    convert h using 1
    apply Subtype.ext
    show ((algebraMap ℚ̄ ↥(modularFunctionFieldBar (N * q)) (a : ℚ̄) : ↥(modularFunctionFieldBar (N * q))) : LS) = ((toC (M := N * q) A K (Polynomial.C a) : ↥(jIntegralClosure (N * q) A K)) : LS)
    rw [coe_toC, e₀_C]
    rfl

  by_contra hne
  have hmem : aeval (ModularCurve.PlaceSpecialization.ProlongationTuple.jFun N q) (p.map (algebraMap ↥(consts W) ℚ̄)) ∈ W := aeval_mem hJ p
  have hx : aeval (ModularCurve.PlaceSpecialization.ProlongationTuple.jFun N q) (p.map (algebraMap ↥(consts W) ℚ̄)) ∈ W.nonunits := by
    rw [ValuationSubring.mem_nonunits_iff]
    exact lt_of_le_of_ne ((W.valuation_le_one_iff _).mpr hmem) hne

  obtain ⟨β, hβ⟩ := exists_sub_algebraMap_mem_nonunits hJ p hp hx
  obtain ⟨m₀, hm₀prim, hm₀β⟩ := exists_primitive_aeval_eq_zero A K (β : ℚ̄)
  set P : Polynomial ↥(coeffSubring A K) := m₀.map (eAK K).toRingHom with hP

  let φ : ↥(coeffSubring A K) →+* ↥W := ((algebraMap ℚ̄ ↥(modularFunctionFieldBar (N * q))).comp (coeffSubring A K).subtype).codRestrict W.toSubring (fun a => hA₀W a)
  let JW : ↥W := ⟨_, hJ⟩
  let βW : ↥W := ⟨algebraMap ℚ̄ ↥(modularFunctionFieldBar (N * q)) (β : ℚ̄), β.2⟩
  have hdvd := Polynomial.sub_dvd_eval_sub JW βW (P.map φ)
  have hevalβ : (P.map φ).eval βW = 0 := by
    apply Subtype.ext
    show W.subtype ((P.map φ).eval βW) = ((0 : ↥W) : ↥(modularFunctionFieldBar (N * q)))
    rw [Polynomial.eval_map, Polynomial.hom_eval₂, hP, Polynomial.eval₂_map, ZeroMemClass.coe_zero]

    have hcomp : (W.subtype.comp φ).comp (eAK K).toRingHom
        = (algebraMap ℚ̄ ↥(modularFunctionFieldBar (N * q))).comp ((algebraMap ↥K ℚ̄).comp (algebraMap ↥(AK A K) ↥K)) :=
      RingHom.ext (fun a => rfl)
    rw [hcomp, show W.subtype βW = algebraMap ℚ̄ ↥(modularFunctionFieldBar (N * q)) (β : ℚ̄) from rfl,
      ← Polynomial.hom_eval₂, ← Polynomial.eval₂_map]
    have hev : Polynomial.eval₂ (algebraMap ↥K ℚ̄) (β : ℚ̄) (m₀.map (algebraMap ↥(AK A K) ↥K))
        = aeval (β : ℚ̄) ((m₀.map (algebraMap ↥(AK A K) ↥K)).map (algebraMap ↥K ℚ̄)) := by
      have hc : (algebraMap ℚ̄ ℚ̄).comp (algebraMap ↥K ℚ̄) = algebraMap ↥K ℚ̄ := RingHom.ext (fun x => rfl)
      rw [Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.eval₂_map, Polynomial.eval₂_map, hc]
    rw [hev, hm₀β, map_zero]
  rw [hevalβ, sub_zero] at hdvd

  have hmaxJ : JW - βW ∈ IsLocalRing.maximalIdeal ↥W := ValuationSubring.coe_mem_nonunits_iff.mp hβ
  have hPJ : (P.map φ).eval JW ∈ IsLocalRing.maximalIdeal ↥W := by
    obtain ⟨c, hc⟩ := hdvd
    rw [hc]; exact Ideal.mul_mem_right _ _ hmaxJ
  have hPJ' : (((P.map φ).eval JW : ↥W) : ↥(modularFunctionFieldBar (N * q))) ∈ W.nonunits :=
    ValuationSubring.coe_mem_nonunits_iff.mpr hPJ

  have hPJeq : (((P.map φ).eval JW : ↥W) : ↥(modularFunctionFieldBar (N * q)))
      = toBar' K (algebraMap _ ↥(fieldOver (N * q) K) (toC (M := N * q) A K P)) := by
    apply Subtype.ext
    show (((W.subtype ((P.map φ).eval JW)) : ↥(modularFunctionFieldBar (N * q))) : LS) = ((algebraMap _ ↥(fieldOver (N * q) K) (toC (M := N * q) A K P) : ↥(fieldOver (N * q) K)) : LS)
    rw [halg, coe_toC, Polynomial.eval_map, e₀, Polynomial.coe_eval₂RingHom]

    have h1 := Polynomial.hom_eval₂ P φ (((modularFunctionFieldBar (N * q)).val.toRingHom).comp W.subtype) JW
    have h2 : (((modularFunctionFieldBar (N * q)).val.toRingHom).comp W.subtype) JW = jqModC ℚ̄ := by
      show coeffEmb ℚ̄ jq = jqModC ℚ̄
      rw [← jqModC_rat, coeffEmb, coeffMap_jqModC]
    have h3 : ((((modularFunctionFieldBar (N * q)).val.toRingHom).comp W.subtype).comp φ) = constSeries (coeffSubring A K) :=
      RingHom.ext (fun a => rfl)
    rw [h2, h3] at h1
    exact h1
  have hnu : algebraMap _ ↥(fieldOver (N * q) K) (toC (M := N * q) A K P) ∈ W₀.nonunits := by
    rw [ValuationSubring.mem_nonunits_iff_or, hW₀W, map_inv₀]
    rw [hPJeq, ValuationSubring.mem_nonunits_iff_or] at hPJ'
    rcases hPJ' with h0 | h0
    · exact Or.inl ((map_eq_zero (toBar' K)).mp h0)
    · exact Or.inr h0

  have hinj : Function.Injective (algebraMap ↥(jIntegralClosure (N * q) A K) ↥(fieldOver (N * q) K)) := by
    intro a b h
    apply Subtype.ext
    rw [← halg a, ← halg b, h]
  have hP𝔭 : toC (M := N * q) A K P ∈ 𝔭 := by
    by_contra ht
    rw [ValuationSubring.mem_nonunits_iff_or] at hnu
    rcases hnu with h0 | hinv
    · apply ht
      have : toC (M := N * q) A K P = 0 := hinj (by rw [h0, map_zero])
      rw [this]; exact 𝔭.zero_mem
    · apply hinv
      refine (hWmem _).mpr ⟨1, toC (M := N * q) A K P, ht, ?_⟩
      have h0 : algebraMap _ ↥(fieldOver (N * q) K) (toC (M := N * q) A K P) ≠ 0 := by
        intro h0; apply ht
        have : toC (M := N * q) A K P = 0 := hinj (by rw [h0, map_zero])
        rw [this]; exact 𝔭.zero_mem
      rw [inv_mul_cancel₀ h0, map_one]

  letI alg : Algebra (Polynomial ↥(coeffSubring A K)) ↥(jIntegralClosure (N * q) A K) := (toC (M := N * q) A K).toAlgebra
  haveI : FaithfulSMul (Polynomial ↥(coeffSubring A K)) ↥(jIntegralClosure (N * q) A K) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (toC_injective K)
  haveI : Algebra.IsIntegral (Polynomial ↥(coeffSubring A K)) ↥(jIntegralClosure (N * q) A K) := ⟨isIntegral_toC K⟩
  have hϖC : Prime (C ϖ : Polynomial ↥(coeffSubring A K)) := Polynomial.prime_C_iff.mpr hϖ.prime
  haveI : (Ideal.span {(C ϖ : Polynomial ↥(coeffSubring A K))}).IsPrime := (Ideal.span_singleton_prime hϖC.ne_zero).mpr hϖC
  have hqϖ : (toC (M := N * q) A K) (C ϖ) ∈ 𝔭 := by
    have hq0 : ((q : ℕ) : ↥(coeffSubring A K)) ≠ 0 := by
      intro h; apply (Fact.out : q.Prime).ne_zero
      have := congrArg (fun z : ↥(coeffSubring A K) => (z : ℚ̄)) h
      simpa using this
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hq0 hϖ
    have hmem : (toC (M := N * q) A K) (C (ϖ ^ n)) ∈ 𝔭 := by
      have hq' : (toC (M := N * q) A K) (C ((q : ℕ) : ↥(coeffSubring A K))) = ((q : ℕ) : ↥(jIntegralClosure (N * q) A K)) :=
        Subtype.ext (by rw [coe_toC, e₀_C]; simp)
      rw [← hu, C_mul, map_mul, hq']
      exact 𝔭.mul_mem_right _ hq
    rw [C_pow, map_pow] at hmem
    exact Ideal.IsPrime.mem_of_pow_mem inferInstance n hmem
  have hunder : 𝔭.under (Polynomial ↥(coeffSubring A K)) = Ideal.span {C ϖ} := by
    refine under_eq_of_height_eq_one 𝔭 h𝔭 (Ideal.span {C ϖ}) ?_ ?_
    · rw [Ne, Ideal.span_singleton_eq_bot]; exact hϖC.ne_zero
    · rw [Ideal.span_le, Set.singleton_subset_iff]; exact hqϖ

  have hPunder : P ∈ 𝔭.under (Polynomial ↥(coeffSubring A K)) := hP𝔭
  rw [hunder, Ideal.mem_span_singleton] at hPunder
  obtain ⟨P', hP'⟩ := hPunder
  apply hm₀prim
  apply Polynomial.ext; intro n
  rw [Polynomial.coeff_map, Polynomial.coeff_zero, IsLocalRing.residue_eq_zero_iff]
  have hcoeff : P.coeff n = ϖ * P'.coeff n := by rw [hP', Polynomial.coeff_C_mul]
  have hPn : P.coeff n = (eAK K) (m₀.coeff n) := by rw [hP, Polynomial.coeff_map]; rfl

  intro hu
  have hu' : IsUnit (P.coeff n) := by rw [hPn]; exact hu.map (eAK K)
  rw [hcoeff] at hu'
  exact hϖ.not_isUnit (isUnit_of_mul_isUnit_left hu')

theorem algebraMap_mem_nonunits_of_mem_maximalIdeal (hA : A.LiesOverPrime q)
    (𝔭 : Ideal ↥(jIntegralClosure (N * q) A K)) [𝔭.IsPrime] (hq : ((q : ℕ) : ↥(jIntegralClosure (N * q) A K)) ∈ 𝔭)
    [Algebra ↥(jIntegralClosure (N * q) A K) ↥(fieldOver (N * q) K)]
    (halg : ∀ c : ↥(jIntegralClosure (N * q) A K), ((algebraMap ↥(jIntegralClosure (N * q) A K) ↥(fieldOver (N * q) K) c : ↥(fieldOver (N * q) K)) : LS) = (c : LS))
    (W₀ : ValuationSubring ↥(fieldOver (N * q) K))
    (hWmem : ∀ x : ↥(fieldOver (N * q) K), x ∈ W₀ ↔ ∃ r s : ↥(jIntegralClosure (N * q) A K), s ∉ 𝔭 ∧
      x * algebraMap ↥(jIntegralClosure (N * q) A K) ↥(fieldOver (N * q) K) s = algebraMap ↥(jIntegralClosure (N * q) A K) ↥(fieldOver (N * q) K) r)
    (W : ValuationSubring ↥(modularFunctionFieldBar (N * q))) (hcomap : W.comap (toBar' K) = W₀)
    (a : ↥(coeffSubring A K)) (ha0 : ¬ IsUnit a) :
    algebraMap ℚ̄ ↥(modularFunctionFieldBar (N * q)) (a : ℚ̄) ∈ W.nonunits := by
  classical
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  haveI hdvr : IsDiscreteValuationRing ↥(coeffSubring A K) := isDiscreteValuationRing_coeffSubring K hA
  have ha : a ∈ IsLocalRing.maximalIdeal ↥(coeffSubring A K) := ha0
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥(coeffSubring A K)
  have hqϖ : (toC (M := N * q) A K) (C ϖ) ∈ 𝔭 := by
    have hq0 : ((q : ℕ) : ↥(coeffSubring A K)) ≠ 0 := by
      intro h; apply (Fact.out : q.Prime).ne_zero
      have := congrArg (fun z : ↥(coeffSubring A K) => (z : ℚ̄)) h
      simpa using this
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hq0 hϖ
    have hmem : (toC (M := N * q) A K) (C (ϖ ^ n)) ∈ 𝔭 := by
      have hq' : (toC (M := N * q) A K) (C ((q : ℕ) : ↥(coeffSubring A K))) = ((q : ℕ) : ↥(jIntegralClosure (N * q) A K)) :=
        Subtype.ext (by rw [coe_toC, e₀_C]; simp)
      rw [← hu, C_mul, map_mul, hq']
      exact 𝔭.mul_mem_right _ hq
    rw [C_pow, map_pow] at hmem
    exact Ideal.IsPrime.mem_of_pow_mem inferInstance n hmem

  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at ha
  obtain ⟨a', rfl⟩ := ha
  have ht : (toC (M := N * q) A K) (C (ϖ * a')) ∈ 𝔭 := by
    rw [C_mul, map_mul]; exact 𝔭.mul_mem_right _ hqϖ

  have hinj : Function.Injective (algebraMap ↥(jIntegralClosure (N * q) A K) ↥(fieldOver (N * q) K)) := by
    intro x y h; apply Subtype.ext; rw [← halg x, ← halg y, h]
  set t := (toC (M := N * q) A K) (C (ϖ * a')) with htdef
  have hnu : algebraMap _ ↥(fieldOver (N * q) K) t ∈ W₀.nonunits := by
    rw [ValuationSubring.mem_nonunits_iff_or]
    by_cases h0 : algebraMap _ ↥(fieldOver (N * q) K) t = 0
    · exact Or.inl h0
    · refine Or.inr (fun hinv => ?_)
      obtain ⟨r, s, hs, hrs⟩ := (hWmem _).mp hinv
      apply hs
      have hsrt : s = r * t := by
        apply hinj
        rw [map_mul, ← hrs]
        field_simp
      rw [hsrt]
      exact 𝔭.mul_mem_left r ht

  have hW₀W : ∀ x : ↥(fieldOver (N * q) K), x ∈ W₀.nonunits ↔ toBar' K x ∈ W.nonunits := by
    intro x
    rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, ← hcomap, ValuationSubring.mem_comap,
      map_inv₀, map_eq_zero]
  have := (hW₀W _).mp hnu
  convert this using 1
  apply Subtype.ext
  show ((algebraMap ℚ̄ ↥(modularFunctionFieldBar (N * q)) ((ϖ * a' : ↥(coeffSubring A K)) : ℚ̄) : ↥(modularFunctionFieldBar (N * q))) : LS) = _
  rw [show ((toBar' K (algebraMap _ ↥(fieldOver (N * q) K) t) : ↥(modularFunctionFieldBar (N * q))) : LS)
      = ((algebraMap _ ↥(fieldOver (N * q) K) t : ↥(fieldOver (N * q) K)) : LS) from rfl, halg, htdef, coe_toC, e₀_C]
  rfl

end Main
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_forall_mem_iff_residueFst_eq_zero_or_forall_mem_iff_residueSnd_eq_zero_of_height_one.C1bGlue"

end P5
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_forall_mem_iff_residueFst_eq_zero_or_forall_mem_iff_residueSnd_eq_zero_of_height_one.C1bGlue P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_forall_mem_iff_residueFst_eq_zero_or_forall_mem_iff_residueSnd_eq_zero_of_height_one.P5"

section P3sec

set_option autoImplicit false

open scoped Pointwise

local notation "ℚ̄" => AlgebraicClosure ℚ

namespace PlaceTransitivityK

noncomputable abbrev Zbar : Subalgebra ℤ ℚ̄ := integralClosure ℤ ℚ̄

local notation "ℤ̄" => Zbar

private theorem _root_.PlaceTransitivityK.coe_mem (A : ValuationSubring ℚ̄) (b : ℤ̄) : (b : ℚ̄) ∈ A := by
  have hb : IsIntegral ℤ (b : ℚ̄) := b.2
  have hbA : IsIntegral A (b : ℚ̄) := by
    obtain ⟨p, hp, hpb⟩ := hb
    refine ⟨p.map (Int.castRingHom A), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have : (algebraMap A ℚ̄).comp (Int.castRingHom A) = algebraMap ℤ ℚ̄ := RingHom.ext_int _ _
    rw [this]
    exact hpb
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := ℚ̄)).mp hbA
  rw [← hy]
  exact y.2

p2m_export "PlaceTransitivityK" "coe_mem"
noncomputable def toPlace (A : ValuationSubring ℚ̄) : ℤ̄ →+* A :=
  ((Subalgebra.val ℤ̄).toRingHom).codRestrict A.toSubring (coe_mem A)

@[scoped simp] theorem coe_toPlace (A : ValuationSubring ℚ̄) (b : ℤ̄) : (toPlace A b : ℚ̄) = b := rfl

noncomputable def center (A : ValuationSubring ℚ̄) : Ideal ℤ̄ :=
  Ideal.comap (toPlace A) (IsLocalRing.maximalIdeal A)

theorem mem_center_iff {A : ValuationSubring ℚ̄} {b : ℤ̄} :
    b ∈ center A ↔ (b : ℚ̄) ∈ A.nonunits := by
  rw [center, Ideal.mem_comap, ← ValuationSubring.coe_mem_nonunits_iff, coe_toPlace]

scoped instance center_isPrime (A : ValuationSubring ℚ̄) : (center A).IsPrime :=
  Ideal.comap_isPrime _ _

theorem mem_smul_nonunits_iff {K L : Type*} [Field K] [Field L] [Algebra K L]
    {τ : L ≃ₐ[K] L} {A : ValuationSubring L} {x : L} :
    x ∈ (τ • A).nonunits ↔ τ.symm x ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or]
  have e0 : x = 0 ↔ τ.symm x = 0 := by
    constructor
    · intro h; rw [h, _root_.map_zero]
    · intro h; simpa using congrArg τ h
  have e1 : x⁻¹ ∈ τ • A ↔ (τ.symm x)⁻¹ ∈ A := by
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    have : (τ⁻¹ : L ≃ₐ[K] L) • x⁻¹ = (τ.symm x)⁻¹ := by
      show τ.symm x⁻¹ = (τ.symm x)⁻¹
      exact map_inv₀ _ _
    rw [this]
  rw [e0, e1]

theorem le_of_forall_not_mem_nonunits {q : ℕ} (hq : q.Prime) {V W : ValuationSubring ℚ̄}
    (hV : V.LiesOverPrime q)
    (h : ∀ s : ℤ̄, (s : ℚ̄) ∉ V.nonunits → (s : ℚ̄) ∉ W.nonunits) : V ≤ W := by
  intro x hx
  obtain ⟨x', s, hs, hxs⟩ :=
    ValuationSubring.exists_integral_mul_eq_of_liesOverPrime V hq hV x hx
  have hsW : (s : ℚ̄) ∉ W.nonunits := h s hs
  rw [ValuationSubring.mem_nonunits_iff_or, not_or, not_not] at hsW
  obtain ⟨hs0, hsinv⟩ := hsW
  have hx_eq : x = (x' : ℚ̄) * (s : ℚ̄)⁻¹ := by
    rw [← hxs, mul_assoc, mul_inv_cancel₀ hs0, mul_one]
  rw [hx_eq]
  exact W.mul_mem _ _ (coe_mem W x') hsinv

theorem mem_nonunits_iff_of_forall_mem_iff {K : IntermediateField ℚ ℚ̄} {A A' : ValuationSubring ℚ̄}
    (hK : ∀ x : ↥K, (x : ℚ̄) ∈ A ↔ (x : ℚ̄) ∈ A') (x : ↥K) :
    (x : ℚ̄) ∈ A.nonunits ↔ (x : ℚ̄) ∈ A'.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or]
  have hinv : ((x : ℚ̄))⁻¹ = ((x⁻¹ : ↥K) : ℚ̄) := by simp
  rw [hinv, hK]

section Bundle

variable (K : IntermediateField ℚ ℚ̄)

theorem isGalois_Qbar : IsGalois ℚ ℚ̄ := by
  have h : @IsGalois ℚ _ ℚ̄ _ (AlgebraicClosure.instAlgebra ℚ) := inferInstance
  exact h

theorem isAlgebraic_Qbar : Algebra.IsAlgebraic ℚ ℚ̄ := by
  have h : @Algebra.IsAlgebraic ℚ ℚ̄ _ _ (AlgebraicClosure.instAlgebra ℚ) := inferInstance
  exact h

scoped instance smulCommClass_int_K : SMulCommClass (ℚ̄ ≃ₐ[↥K] ℚ̄) ℤ ℚ̄ :=
  ⟨fun g n x => by
    change g (n • x) = n • g x
    exact map_zsmul g n x⟩

noncomputable scoped instance mulSemiringAction_Zbar_K : MulSemiringAction (ℚ̄ ≃ₐ[↥K] ℚ̄) ℤ̄ :=
  @instMulSemiringActionSubtypeMemSubalgebraIntegralClosure (ℚ̄ ≃ₐ[↥K] ℚ̄) ℤ ℚ̄ _ _ _ _ _ (smulCommClass_int_K K)

theorem coe_smul_Zbar (g : ℚ̄ ≃ₐ[↥K] ℚ̄) (b : ℤ̄) : ((g • b : ℤ̄) : ℚ̄) = g (b : ℚ̄) := rfl

theorem isGalois_K : IsGalois (↥K) ℚ̄ := by
  haveI := isGalois_Qbar
  exact IsGalois.tower_top_of_isGalois ℚ (↥K) ℚ̄

theorem isIntegral_K : Algebra.IsIntegral (↥K) ℚ̄ := by
  haveI := isAlgebraic_Qbar
  haveI : Algebra.IsIntegral ℚ ℚ̄ := Algebra.isAlgebraic_iff_isIntegral.mp inferInstance
  exact Algebra.IsIntegral.tower_top (R := ℚ)

noncomputable def OK : Subalgebra ℤ ℚ̄ where
  carrier := {x | IsIntegral ℤ x ∧ x ∈ K}
  mul_mem' ha hb := ⟨ha.1.mul hb.1, mul_mem ha.2 hb.2⟩
  add_mem' ha hb := ⟨ha.1.add hb.1, add_mem ha.2 hb.2⟩
  algebraMap_mem' n := ⟨isIntegral_algebraMap, by simp⟩

theorem OK_le_Zbar : OK K ≤ ℤ̄ := fun _ hx => hx.1

noncomputable scoped instance algOK : Algebra ↥(OK K) ℤ̄ := (Subalgebra.inclusion (OK_le_Zbar K)).toRingHom.toAlgebra

theorem algebraMap_OK_coe (x : ↥(OK K)) : ((algebraMap ↥(OK K) ℤ̄ x : ℤ̄) : ℚ̄) = (x : ℚ̄) := rfl

end Bundle
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_forall_mem_iff_residueFst_eq_zero_or_forall_mem_iff_residueSnd_eq_zero_of_height_one.C1bGlue P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_forall_mem_iff_residueFst_eq_zero_or_forall_mem_iff_residueSnd_eq_zero_of_height_one.P5"

theorem exists_smul_center_eq {q : ℕ} (hq : q.Prime) (K : IntermediateField ℚ ℚ̄) [FiniteDimensional ℚ ↥K]
    {A A₀ : ValuationSubring ℚ̄} (hA : A.LiesOverPrime q) (hA₀ : A₀.LiesOverPrime q)
    (hK : ∀ x : ↥K, (x : ℚ̄) ∈ A ↔ (x : ℚ̄) ∈ A₀) :
    ∃ g : ℚ̄ ≃ₐ[↥K] ℚ̄, center A₀ = g • center A := by
  classical
  haveI := isGalois_K K
  haveI := isIntegral_K K
  letI : TopologicalSpace ℤ̄ := ⊥
  haveI : DiscreteTopology ℤ̄ := ⟨rfl⟩
  haveI : ContinuousSMul (ℚ̄ ≃ₐ[↥K] ℚ̄) ℤ̄ := by
    refine continuousSMul_iff_stabilizer_isOpen.mpr fun b => ?_
    haveI : FiniteDimensional (↥K) (IntermediateField.adjoin (↥K) {(b : ℚ̄)}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (b : ℚ̄))
    refine Subgroup.isOpen_mono ?_
      (IntermediateField.fixingSubgroup_isOpen (IntermediateField.adjoin (↥K) {(b : ℚ̄)}))
    intro g hg
    rw [MulAction.mem_stabilizer_iff]
    apply Subtype.ext
    rw [coe_smul_Zbar]
    rw [IntermediateField.mem_fixingSubgroup_iff] at hg
    exact hg _ (IntermediateField.mem_adjoin_simple_self (↥K) (b : ℚ̄))
  haveI : SMulCommClass (ℚ̄ ≃ₐ[↥K] ℚ̄) ↥(OK K) ℤ̄ := ⟨fun g x b => by
    apply Subtype.ext
    change g ((x : ℚ̄) * (b : ℚ̄)) = (x : ℚ̄) * g (b : ℚ̄)
    rw [map_mul]
    congr 1
    exact g.commutes (⟨(x : ℚ̄), x.2.2⟩ : ↥K)⟩
  haveI : Algebra.IsInvariant ↥(OK K) ℤ̄ (ℚ̄ ≃ₐ[↥K] ℚ̄) := ⟨fun b hb => by
    have hb' : (b : ℚ̄) ∈ Set.range (algebraMap (↥K) ℚ̄) := by
      rw [InfiniteGalois.mem_range_algebraMap_iff_fixed]
      intro g
      have h := congrArg (fun z : ℤ̄ => (z : ℚ̄)) (hb g)
      simpa [coe_smul_Zbar] using h
    obtain ⟨r, hr⟩ := hb'
    refine ⟨⟨(b : ℚ̄), b.2, ?_⟩, Subtype.ext rfl⟩
    rw [← hr]
    exact r.2⟩
  have hu : (center A).under ↥(OK K) = (center A₀).under ↥(OK K) := by
    ext x
    rw [Ideal.mem_comap, Ideal.mem_comap, mem_center_iff, mem_center_iff, algebraMap_OK_coe]
    exact mem_nonunits_iff_of_forall_mem_iff hK ⟨(x : ℚ̄), x.2.2⟩
  exact Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite
    (A := ↥(OK K)) (G := ℚ̄ ≃ₐ[↥K] ℚ̄) (center A) (center A₀) hu

theorem exists_smul_eq {q : ℕ} (hq : q.Prime) (K : IntermediateField ℚ ℚ̄) [FiniteDimensional ℚ ↥K]
    (A A₀ : ValuationSubring ℚ̄) (hA : A.LiesOverPrime q) (hA₀ : A₀.LiesOverPrime q)
    (hK : ∀ x : ↥K, (x : ℚ̄) ∈ A ↔ (x : ℚ̄) ∈ A₀) :
    ∃ g : ℚ̄ ≃ₐ[↥K] ℚ̄, g • A = A₀ := by
  classical
  letI : MulSemiringAction (ℚ̄ ≃ₐ[↥K] ℚ̄) ℤ̄ := mulSemiringAction_Zbar_K K
  obtain ⟨g, hg⟩ := exists_smul_center_eq hq K hA hA₀ hK
  refine ⟨g, ?_⟩
  have key : ∀ s : Zbar, (s : ℚ̄) ∈ (g • A).nonunits ↔ (s : ℚ̄) ∈ A₀.nonunits := by
    intro s
    rw [mem_smul_nonunits_iff, ← mem_center_iff (A := A₀), hg,
      Ideal.mem_pointwise_smul_iff_inv_smul_mem, mem_center_iff]
    have : ((g⁻¹ • s : Zbar) : ℚ̄) = g.symm s := by
      rw [coe_smul_Zbar, AlgEquiv.aut_inv]
    rw [this]
  have hgA : (g • A).LiesOverPrime q := by
    show (q : ℚ̄) ∈ (g • A).nonunits
    rw [mem_smul_nonunits_iff, map_natCast]
    exact hA
  apply le_antisymm
  · exact le_of_forall_not_mem_nonunits hq hgA fun s hs => fun h => hs ((key s).mpr h)
  · exact le_of_forall_not_mem_nonunits hq hA₀ fun s hs => fun h => hs ((key s).mp h)

end PlaceTransitivityK
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_forall_mem_iff_residueFst_eq_zero_or_forall_mem_iff_residueSnd_eq_zero_of_height_one.C1bGlue P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_forall_mem_iff_residueFst_eq_zero_or_forall_mem_iff_residueSnd_eq_zero_of_height_one.P5 P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_forall_mem_iff_residueFst_eq_zero_or_forall_mem_iff_residueSnd_eq_zero_of_height_one.PlaceTransitivityK"

open PlaceTransitivityK in

theorem exists_algEquiv_smul_eq_of_forall_mem_iff {q : ℕ} (hq : q.Prime)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (A A' : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) (hA' : A'.LiesOverPrime q)
    (hK : ∀ x : ↥K, (x : AlgebraicClosure ℚ) ∈ A ↔ (x : AlgebraicClosure ℚ) ∈ A') :
    ∃ σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ), (∀ c : ↥K, σ c = c) ∧ σ • A' = A := by
  classical
  obtain ⟨g, hg⟩ := exists_smul_eq hq K A' A hA' hA (fun x => (hK x).symm)
  refine ⟨g.restrictScalars ℚ, fun c => g.commutes c, ?_⟩
  rw [← hg]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

end P3sec
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_forall_mem_iff_residueFst_eq_zero_or_forall_mem_iff_residueSnd_eq_zero_of_height_one.C1bGlue P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_forall_mem_iff_residueFst_eq_zero_or_forall_mem_iff_residueSnd_eq_zero_of_height_one.P5 P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_forall_mem_iff_residueFst_eq_zero_or_forall_mem_iff_residueSnd_eq_zero_of_height_one.PlaceTransitivityK"

namespace RoadAssembly

open AlgebraicCurve IsLocalRing ModularCurve Polynomial
open ModularCurve.NodeLocalized
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple
open scoped Pointwise

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "LS" => LaurentSeries (AlgebraicClosure ℚ)

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

theorem W₀_eq_V₁_or_V₂ (R : ProlongationTuple P) (hqN : ¬ q ∣ N)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (𝔭 : Ideal ↥(jIntegralClosure (N * q) A K)) [𝔭.IsPrime] (h𝔭 : 𝔭.height = 1)
    (hq : ((q : ℕ) : ↥(jIntegralClosure (N * q) A K)) ∈ 𝔭)
    (W₀ : ValuationSubring ↥(fieldOver (N * q) K))
    (hWmem : letI := C1bGlue.algCF (A := A) (N := N) (q := q) K
      ∀ x : ↥(fieldOver (N * q) K), x ∈ W₀ ↔ ∃ r s : ↥(jIntegralClosure (N * q) A K), s ∉ 𝔭 ∧
        x * algebraMap _ ↥(fieldOver (N * q) K) s = algebraMap _ ↥(fieldOver (N * q) K) r) :
    W₀ = C1bGlue.V₁ R K ∨ W₀ = C1bGlue.V₂ R K := by
  classical
  letI := C1bGlue.algCF (A := A) (N := N) (q := q) K
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have halg : ∀ c : ↥(jIntegralClosure (N * q) A K),
      ((algebraMap ↥(jIntegralClosure (N * q) A K) ↥(fieldOver (N * q) K) c : ↥(fieldOver (N * q) K)) : LS) = (c : LS) := fun c => rfl

  obtain ⟨W, hcomap⟩ := RoadA.exists_comap_eq (C1bGlue.toBar (N * q) K) W₀
  have hcomap' : W.comap (P5.toBar' K) = W₀ := hcomap
  have hW₀W : ∀ x : ↥(fieldOver (N * q) K), x ∈ W₀ ↔ C1bGlue.toBar (N * q) K x ∈ W := fun x => by rw [← hcomap]; rfl

  have hA : A.LiesOverPrime q := GaussID.liesOverPrime R hqN
  set B : ValuationSubring ℚ̄ := P5.consts W with hB
  have hCW₀ : ∀ c : ↥(jIntegralClosure (N * q) A K), algebraMap _ ↥(fieldOver (N * q) K) c ∈ W₀ := fun c =>
    (hWmem _).mpr ⟨c, 1, fun h => (Ideal.ne_top_iff_one 𝔭).mp (Ideal.IsPrime.ne_top inferInstance) h, by rw [map_one, mul_one]⟩
  have hA₀W : ∀ a : ↥(coeffSubring A K), algebraMap ℚ̄ ↥(modularFunctionFieldBar (N * q)) (a : ℚ̄) ∈ W := by
    intro a
    have h := (hW₀W _).mp (hCW₀ (P5.toC (M := N * q) A K (Polynomial.C a)))
    convert h using 1
    apply Subtype.ext
    show ((algebraMap ℚ̄ ↥(modularFunctionFieldBar (N * q)) (a : ℚ̄) : ↥(modularFunctionFieldBar (N * q))) : LS)
      = ((P5.toC (M := N * q) A K (Polynomial.C a) : ↥(jIntegralClosure (N * q) A K)) : LS)
    rw [P5.coe_toC, P5.e₀_C]
    rfl

  have hnonunit : ∀ a : ↥(coeffSubring A K), ¬ IsUnit a → algebraMap ℚ̄ ↥(modularFunctionFieldBar (N * q)) (a : ℚ̄) ∈ W.nonunits :=
    fun a ha => P5.algebraMap_mem_nonunits_of_mem_maximalIdeal hA 𝔭 hq halg W₀ hWmem W hcomap' a ha
  have hBK : ∀ x : ↥K, (x : ℚ̄) ∈ A ↔ (x : ℚ̄) ∈ B := by
    intro x
    constructor
    · intro hx
      exact hA₀W ⟨(x : ℚ̄), hx, x.2⟩
    · intro hxB
      by_contra hxA

      have hx0 : (x : ℚ̄) ≠ 0 := fun h => hxA (by rw [h]; exact A.zero_mem)
      have hinvA : (x : ℚ̄)⁻¹ ∈ A := by
        rcases A.mem_or_inv_mem (x : ℚ̄) with h | h
        · exact absurd h hxA
        · exact h
      let y : ↥(coeffSubring A K) := ⟨(x : ℚ̄)⁻¹, hinvA, K.inv_mem x.2⟩
      have hy : ¬ IsUnit y := by
        intro hu
        obtain ⟨u, hu⟩ := hu
        apply hxA
        have : (((u⁻¹ : (↥(coeffSubring A K))ˣ) : ↥(coeffSubring A K)) : ℚ̄) = (x : ℚ̄) := by
          have h1 := congrArg (fun z : ↥(coeffSubring A K) => (z : ℚ̄)) u.inv_mul
          rw [hu] at h1
          simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at h1

          have := eq_inv_of_mul_eq_one_left h1
          rw [inv_inv] at this
          exact this
        rw [← this]
        exact ((u⁻¹ : (↥(coeffSubring A K))ˣ) : ↥(coeffSubring A K)).2.1
      have hnu := hnonunit y hy

      have hxW : algebraMap ℚ̄ ↥(modularFunctionFieldBar (N * q)) (x : ℚ̄) ∈ W := hxB
      have h1 : W.valuation (algebraMap ℚ̄ ↥(modularFunctionFieldBar (N * q)) ((y : ℚ̄) * (x : ℚ̄))) < 1 := by
        rw [map_mul, map_mul]
        calc W.valuation (algebraMap ℚ̄ _ (y : ℚ̄)) * W.valuation (algebraMap ℚ̄ _ (x : ℚ̄))
            ≤ W.valuation (algebraMap ℚ̄ _ (y : ℚ̄)) * 1 := mul_le_mul_right ((W.valuation_le_one_iff _).mpr hxW) _
          _ < 1 := by rw [mul_one]; exact W.mem_nonunits_iff.mp hnu
      have : ((y : ℚ̄) * (x : ℚ̄)) = 1 := inv_mul_cancel₀ hx0
      rw [this, map_one, map_one] at h1
      exact lt_irrefl _ h1
  have hBq : B.LiesOverPrime q := by
    show ((q : ℕ) : ℚ̄) ∈ B.nonunits
    rw [P5.mem_nonunits_consts_iff]
    have hqA : ¬ IsUnit ((q : ℕ) : ↥(coeffSubring A K)) := by
      intro hu

      have : IsUnit ((q : ℕ) : ↥A) := by
        have := hu.map (P5.inclA A K)
        simpa using this
      have hqn : ((q : ℕ) : ℚ̄) ∈ A.nonunits := hA
      rw [show ((q : ℕ) : ℚ̄) = (((q : ℕ) : ↥A) : ℚ̄) by simp, ValuationSubring.coe_mem_nonunits_iff] at hqn
      exact hqn this
    have := hnonunit _ hqA
    simpa using this
  obtain ⟨σ, hσK, hσB⟩ := exists_algEquiv_smul_eq_of_forall_mem_iff (Fact.out : q.Prime) K A B hA hBq hBK

  set W' := RoadA.twist (N * q) σ W with hW'
  have hjF₀ : jqModC ℚ̄ ∈ fieldOver (N * q) K := Subfield.subset_closure (Or.inr (Set.mem_insert _ _))
  have hJexp : ((ProlongationTuple.jFun N q : ↥(modularFunctionFieldBar (N * q))) : LS) ∈ fieldOver (N * q) K := by
    have : ((ProlongationTuple.jFun N q : ↥(modularFunctionFieldBar (N * q))) : LS) = jqModC ℚ̄ := GaussID.jqModC_eq_coeffEmb.symm
    rw [this]; exact hjF₀
  have hJW : (ProlongationTuple.jFun N q : ↥(modularFunctionFieldBar (N * q))) ∈ W := by
    have h := (hW₀W _).mp (hCW₀ (P5.toC (M := N * q) A K X))
    convert h using 1
    apply Subtype.ext
    show coeffEmb ℚ̄ jq = ((P5.toC (M := N * q) A K X : ↥(jIntegralClosure (N * q) A K)) : LS)
    rw [P5.coe_toC, P5.e₀_X, ← jqModC_rat, coeffEmb, coeffMap_jqModC]
  have hσA : ∀ a : ℚ̄, a ∈ A ↔ σ.symm a ∈ B := by
    intro a
    rw [← hσB, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    rfl
  have hGL : JLine.GaussLike A (ProlongationTuple.jFun N q) W' := by
    refine ⟨fun a => ?_, ?_, fun p hp => ?_⟩
    · rw [hW', RoadA.algebraMap_mem_twist_iff, hσA]; rfl
    · rw [hW', RoadA.mem_twist_iff_of_mem_fieldOver (N * q) K σ hσK W _ hJexp]; exact hJW
    ·
      set y := aeval (ProlongationTuple.jFun N q) (p.map (algebraMap ↥A ℚ̄)) with hy
      let e : ↥A →+* ↥B := (((σ.symm : ℚ̄ ≃ₐ[ℚ] ℚ̄) : ℚ̄ →+* ℚ̄).comp A.subtype).codRestrict B.toSubring
        (fun a => (hσA (a : ℚ̄)).mp a.2)
      set p' : Polynomial ↥B := p.map e with hp'
      have hp'prim : p'.map (IsLocalRing.residue ↥B) ≠ 0 := by
        obtain ⟨n, hn⟩ : ∃ n, (p.map (IsLocalRing.residue ↥A)).coeff n ≠ 0 := by
          by_contra h; push Not at h; exact hp (Polynomial.ext (fun n => by simpa using h n))
        rw [Polynomial.coeff_map] at hn
        intro h0
        have h1 := congrArg (fun r => Polynomial.coeff r n) h0
        simp only [Polynomial.coeff_map, Polynomial.coeff_zero, hp'] at h1
        have hu : IsUnit (p.coeff n) := (IsLocalRing.residue_ne_zero_iff_isUnit _).mp hn
        exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr (hu.map e) h1
      have hval := P5.valuation_aeval_jFun_eq_one hA 𝔭 h𝔭 hq halg W₀ hWmem W hcomap' p' hp'prim
      have hσK' : ∀ c : ↥K, σ.symm c = c := fun c => σ.symm_apply_eq.mpr (hσK c).symm
      have hτy : RoadA.τ (N * q) σ.symm y = aeval (ProlongationTuple.jFun N q) (p'.map (algebraMap ↥B ℚ̄)) := by
        rw [hy, Polynomial.aeval_def, Polynomial.eval₂_map, hp', Polynomial.aeval_def, Polynomial.map_map, Polynomial.eval₂_map]
        rw [show (RoadA.τ (N * q) σ.symm) (Polynomial.eval₂ ((algebraMap ℚ̄ ↥(modularFunctionFieldBar (N * q))).comp (algebraMap ↥A ℚ̄))
            (ProlongationTuple.jFun N q) p) = (RoadA.τ (N * q) σ.symm).toRingHom (Polynomial.eval₂ _ _ p) from rfl,
          Polynomial.hom_eval₂]
        have hJfix : (RoadA.τ (N * q) σ.symm).toRingHom (ProlongationTuple.jFun N q) = ProlongationTuple.jFun N q :=
          RoadA.τ_eq_self_of_mem_fieldOver (N * q) K σ.symm hσK' _ hJexp
        rw [hJfix]
        congr 1
        refine RingHom.ext (fun a => ?_)
        show RoadA.τ (N * q) σ.symm (algebraMap ℚ̄ _ (a : ℚ̄)) = algebraMap ℚ̄ _ (((e a : ↥B)) : ℚ̄)
        rw [RoadA.τ_algebraMap]
        rfl

      have hmemW : RoadA.τ (N * q) σ.symm y ∈ W := by
        rw [hτy]; exact (W.valuation_le_one_iff _).mp hval.le
      have hnotnu : RoadA.τ (N * q) σ.symm y ∉ W.nonunits := by
        rw [hτy, ValuationSubring.mem_nonunits_iff, hval]; exact lt_irrefl _
      have hmem' : y ∈ W' := hmemW
      have hnotnu' : y ∉ W'.nonunits := by
        rw [hW', RoadA.twist, C1bGlue.mem_nonunits_comap_iff]; exact hnotnu
      rw [ValuationSubring.mem_nonunits_iff, not_lt] at hnotnu'
      exact le_antisymm ((W'.valuation_le_one_iff _).mpr hmem') hnotnu'

  have hW'id := GaussID.eq_integersFst_or_eq_integersSnd_of_gaussLike R hqN W' hGL

  have key : ∀ (x : ↥(fieldOver (N * q) K)), x ∈ W₀ ↔ C1bGlue.toBar (N * q) K x ∈ W' := by
    intro x
    rw [hW₀W, hW', RoadA.mem_twist_iff_of_mem_fieldOver (N * q) K σ hσK W _ x.2]
  rcases hW'id with h | h
  · left; ext x; rw [key, h]; rfl
  · right; ext x; rw [key, h]; rfl

end RoadAssembly
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_forall_mem_iff_residueFst_eq_zero_or_forall_mem_iff_residueSnd_eq_zero_of_height_one.C1bGlue P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_forall_mem_iff_residueFst_eq_zero_or_forall_mem_iff_residueSnd_eq_zero_of_height_one.P5 P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_forall_mem_iff_residueFst_eq_zero_or_forall_mem_iff_residueSnd_eq_zero_of_height_one.PlaceTransitivityK"

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.NodeLocalized
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P) (hqN : ¬ q ∣ N)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (𝔭 : Ideal ↥(jIntegralClosure (N * q) A K)) [𝔭.IsPrime] (h𝔭 : 𝔭.height = 1)
    (hq : ((q : ℕ) : ↥(jIntegralClosure (N * q) A K)) ∈ 𝔭) :
    (∀ (t : ↥(modularFunctionFieldBar (N * q))) (ht : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K),
        (⟨(t : LaurentSeries (AlgebraicClosure ℚ)), ht⟩ : ↥(jIntegralClosure (N * q) A K)) ∈ 𝔭 ↔
          ∃ h₁ : t ∈ R.R₁.integers, R.residue₁ ⟨t, h₁⟩ = 0) ∨
    (∀ (t : ↥(modularFunctionFieldBar (N * q))) (ht : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K),
        (⟨(t : LaurentSeries (AlgebraicClosure ℚ)), ht⟩ : ↥(jIntegralClosure (N * q) A K)) ∈ 𝔭 ↔
          ∃ h₂ : t ∈ R.R₂.integers, R.residue₂ ⟨t, h₂⟩ = 0) := by
  classical
  obtain ⟨W₀, hWmem⟩ := C1bGlue.exists_W (A := A) (N := N) (q := q) K 𝔭 h𝔭
  exact C1bGlue.c1b_of_W_eq R K hqN 𝔭 W₀ hWmem (RoadAssembly.W₀_eq_V₁_or_V₂ R hqN K 𝔭 h𝔭 hq W₀ hWmem)

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_forall_mem_iff_residueFst_eq_zero_or_forall_mem_iff_residueSnd_eq_zero_of_height_one
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_forall_mem_iff_residueFst_eq_zero_or_forall_mem_iff_residueSnd_eq_zero_of_height_one (solution)
