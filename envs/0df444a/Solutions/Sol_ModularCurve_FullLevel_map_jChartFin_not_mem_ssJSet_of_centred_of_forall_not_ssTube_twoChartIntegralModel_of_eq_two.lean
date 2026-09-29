-- Prove2me | solution 1 for ModularCurve.FullLevel.map_jChartFin_not_mem_ssJSet_of_centred_of_forall_not_ssTube_twoChartIntegralModel_of_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/243f2e2a-476e-54c0-a454-0243439438c0

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_SupersingularModuli
import Theorems.Thm_ModularCurve_FullLevel_inStalk_and_inMax_iff_mem_asIdeal_chartAlg_twoChartIntegralModel_of_eq_two
import Theorems.Thm_ModularCurve_FullLevel_exists_ssTube_of_residue_evalAt_mem_ssJSet_of_eq_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_map_jChartFin_not_mem_ssJSet_of_centred_of_forall_not_ssTube_twoChartIntegralModel_of_eq_two
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.qExpandAlgHomC_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left"
p2m_attr_erase "simp" "ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar"

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

namespace N2Aux

theorem mem_ssJSet_of_map_mem {K Ω : Type} [Field K] [DecidableEq K] [Field Ω] [DecidableEq Ω]
    (q : ℕ) (ι : K →+* Ω) (x : K) (h : ι x ∈ ModularCurve.ssJSet q Ω) : x ∈ ModularCurve.ssJSet q K := by
  rw [ModularCurve.mem_ssJSet_iff] at h ⊢
  intro W _ hWj P hP
  letI : Algebra K Ω := ι.toAlgebra
  haveI hE : (W.baseChange Ω).IsElliptic := (inferInstance : (W.map (algebraMap K Ω)).IsElliptic)
  have hj' : (W.baseChange Ω).j = ι x := by
    change (W.map (algebraMap K Ω)).j = _
    rw [WeierstrassCurve.map_j, hWj]; rfl
  let f : (W.baseChange K).toAffine.Point →+ (W.baseChange Ω).toAffine.Point :=
    WeierstrassCurve.Affine.Point.map (W' := W) (Algebra.ofId K Ω)
  have hinj : Function.Injective f := WeierstrassCurve.Affine.Point.map_injective (W' := W) (Algebra.ofId K Ω)
  have hP' : q • f (P : (W.baseChange K).toAffine.Point) = 0 := by
    rw [← map_nsmul]
    change f (q • P) = 0
    rw [hP]; exact map_zero f
  have h0 : f (P : (W.baseChange K).toAffine.Point) = 0 := h (W.baseChange Ω) hj' _ hP'
  exact hinj (h0.trans (map_zero f).symm)

theorem exists_comp_eq_of_ker_eq {C K Ω : Type} [CommRing C] [Field K] [Field Ω]
    (ρ : C →+* K) (hρ : Function.Surjective ρ) (φ : C →+* Ω) (hker : RingHom.ker φ = RingHom.ker ρ) :
    ∃ ι : K →+* Ω, ∀ c, φ c = ι (ρ c) := by
  let e : (C ⧸ RingHom.ker ρ) ≃+* K := RingHom.quotientKerEquivOfSurjective hρ
  let φbar : C ⧸ RingHom.ker ρ →+* Ω := Ideal.Quotient.lift (RingHom.ker ρ) φ (fun c hc => by rwa [← hker] at hc)
  refine ⟨φbar.comp e.symm.toRingHom, fun c => ?_⟩
  have he : e (Ideal.Quotient.mk (RingHom.ker ρ) c) = ρ c := RingHom.quotientKerEquivOfSurjective_apply_mk hρ c
  have hs : e.symm (ρ c) = Ideal.Quotient.mk (RingHom.ker ρ) c := by
    rw [← he, RingEquiv.symm_apply_apply]
  change φ c = φbar (e.symm (ρ c))
  rw [hs]
  rfl

end N2Aux

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

    ∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), P.IsRational →
      (∀ s : ↥W, ¬ (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
                (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
                  0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
                    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                    ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
                (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
                    (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
                  ∀ a : A, residue A a =
                      (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
                    ∃ h : P.evalAt (IntermediateField.inclusion hle f : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A,
                      (⟨_, h⟩ : A) ∈ maximalIdeal A)) →
      ∀ x : ↥(AlgebraicCurve.TwoChartIntegralModel ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), Centred P x →
        ∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (AlgebraicCurve.TwoChartIntegralModel.ιFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).base y = x →
          ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
            (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) →+* Ω), RingHom.ker φ = y.asIdeal →
              φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) ∉ ModularCurve.ssJSet q Ω := by
  classical
  letI instk₀ : Algebra ↥k₀ ↥(fieldBar q M') :=
    ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
  intro F₀ hK1 hstab hLD hRAT instAlg hconst j₁ hj₁ instFact
  intro InStalk InMax Centred GoodPt P hPrat hnotube x hcen y hy Ω _i1 _i2 _i3 _i4 φ hφ hss
  obtain ⟨hN5F, -⟩ := ModularCurve.FullLevel.inStalk_and_inMax_iff_mem_asIdeal_chartAlg_twoChartIntegralModel_of_eq_two q hq2 M' hqM' A hA W hW hle R₀ hR₀ ζ OIg OSS hIg_inf hIg hIg_inj hIg_perm hSS_A hSS_over hSS_fix hSS_tr R hR hR₀O π hπ hπP k₀ π₀ hπ₀ hdvr hunif hhens hres hκ ℓ hℓ hℓ3 hℓq hℓM' ζ₀ hζ₀ ϖt hϖtA hϖt K₁ hK₁ A₁ hA₁ F₀ hK1 hstab hLD hRAT hconst j₁ hj₁
  subst hy
  have hC : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁), (b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)).1 ∈ P.toValuationSubring ∧ P.evalAt (b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)).1 ∈ A ∧
      (A.valuation (P.evalAt (b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)).1) < 1 ↔ b ∈ y.asIdeal) := by
    intro b
    obtain ⟨hst, hmx⟩ := hN5F y b
    obtain ⟨h1, h2, h3⟩ := hcen.2 _ hst
    exact ⟨h1, h2, h3.trans hmx⟩

  let toP : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) →+* ↥P.toValuationSubring :=
    ((algebraMap ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) ↥(fieldBar q M')).comp (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁).val.toRingHom).codRestrict P.toValuationSubring (fun b => (hC b).1)
  have htoP : ∀ b, toP b = ⟨(b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)).1, (hC b).1⟩ := fun b => rfl
  let evA : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) →+* ↥A := ((T2Aux.ev P hPrat).comp toP).codRestrict A (fun b => by
    change T2Aux.ev P hPrat (toP b) ∈ A
    rw [htoP, T2Aux.ev_eq_evalAt]; exact (hC b).2.1)
  let ρ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) →+* ResidueField ↥A := (IsLocalRing.residue ↥A).comp evA
  have hρ : ∀ b, ρ b = IsLocalRing.residue ↥A ⟨P.evalAt (b : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)).1, (hC b).2.1⟩ := by
    intro b
    change IsLocalRing.residue ↥A (evA b) = _
    congr 1
    apply Subtype.ext
    change T2Aux.ev P hPrat (toP b) = _
    rw [htoP, T2Aux.ev_eq_evalAt]
  have hker : RingHom.ker ρ = y.asIdeal := by
    ext b
    rw [RingHom.mem_ker, hρ, IsLocalRing.residue_eq_zero_iff]
    exact (ValuationSubring.valuation_lt_one_iff A _).trans (hC b).2.2
  have hsurj : Function.Surjective ρ := by
    intro r
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective (R := ↥A) r
    obtain ⟨c₀, hc₀A, hdiff, hdiffm⟩ := hκ a.1 a.2
    let a' : ↥A₁ := ⟨algebraMap ↥k₀ ↥K₁ c₀, (hA₁ _).mpr hc₀A⟩
    refine ⟨algebraMap ↥A₁ ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) a', ?_⟩
    rw [hρ]

    have hcoe : ((algebraMap ↥A₁ ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) a' : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁)) : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)).1 = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c₀ : AlgebraicClosure ℚ) :=
      hconst a'
    have hval : P.evalAt ((algebraMap ↥A₁ ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) a' : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁)) : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)).1 = (c₀ : AlgebraicClosure ℚ) :=
      (congrArg P.evalAt hcoe).trans (T2Aux.evalAt_algebraMap P hPrat _)

    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    have : (⟨P.evalAt ((algebraMap ↥A₁ ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁) a' : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁)) : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀)).1, (hC _).2.1⟩ : ↥A) - a = -⟨a.1 - c₀, hdiff⟩ := by
      apply Subtype.ext
      change P.evalAt _ - a.1 = -(a.1 - (c₀ : AlgebraicClosure ℚ))
      rw [hval]; ring
    rw [this]
    exact (maximalIdeal ↥A).neg_mem_iff.mpr hdiffm
  obtain ⟨ι, hι⟩ := N2Aux.exists_comp_eq_of_ker_eq ρ hsurj φ (hφ.trans hker.symm)

  have hjss : IsLocalRing.residue ↥A ⟨P.evalAt ((AlgebraicCurve.TwoChartIntegralModel.jChartFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁ : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀))).1, (hC _).2.1⟩ ∈ ModularCurve.ssJSet q (ResidueField ↥A) := by
    apply N2Aux.mem_ssJSet_of_map_mem q ι
    rw [← hρ, ← hι]; exact hss

  have ej : ((AlgebraicCurve.TwoChartIntegralModel.jChartFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁ : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀))).1 = (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) := hj₁
  have hjA : P.evalAt (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) ∈ A := (congrArg (fun t => P.evalAt t ∈ A) ej).mp (hC (AlgebraicCurve.TwoChartIntegralModel.jChartFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁)).2.1
  have ea : (⟨P.evalAt (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')), hjA⟩ : ↥A) = ⟨P.evalAt ((AlgebraicCurve.TwoChartIntegralModel.jChartFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁ : ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀))).1, (hC (AlgebraicCurve.TwoChartIntegralModel.jChartFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁)).2.1⟩ :=
    Subtype.ext (congrArg P.evalAt ej.symm)
  have hss' : IsLocalRing.residue ↥A ⟨P.evalAt (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')), hjA⟩ ∈ ModularCurve.ssJSet q (ResidueField ↥A) := by
    rw [ea]; exact hjss
  have hjP : (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) ∈ P.toValuationSubring := (congrArg (fun t => t ∈ P.toValuationSubring) ej).mp (hC (AlgebraicCurve.TwoChartIntegralModel.jChartFin ↥A₁ ↥(IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K₁ : Set (AlgebraicClosure ℚ))) ⊔ F₀) j₁)).1
  obtain ⟨s, hs⟩ := ModularCurve.FullLevel.exists_ssTube_of_residue_evalAt_mem_ssJSet_of_eq_two q hq2 M' hqM' A hA W hW hle R₀ hR₀ P hPrat hjP hjA hss'
  exact hnotube s hs

end S_ModularCurve_FullLevel_map_jChartFin_not_mem_ssJSet_of_centred_of_forall_not_ssTube_twoChartIntegralModel_of_eq_two
end P2MW
export P2MW.S_ModularCurve_FullLevel_map_jChartFin_not_mem_ssJSet_of_centred_of_forall_not_ssTube_twoChartIntegralModel_of_eq_two (solution)
