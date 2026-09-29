-- Prove2me | solution 1 for ModularCurve.FullLevel.supersingularProlongation_not_mem_ends_iff_affine_and_exists_levelAut_smul_ne_of_eq_two_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/d0a2478c-81c4-58b5-b8e2-5f72fd2b4d88

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Theorems.Thm_DrinfeldCurve_placesAtInfinity_census
import Theorems.Thm_AlgebraicCurve_Place_exists_restrict_eq
import Theorems.Thm_AlgebraicCurve_Place_exists_algEquiv_smul_eq_of_restrict_eq
import Theorems.Thm_DrinfeldCurve_exists_eq_smul_one_of_comap_hFunctionFieldAction_eq_of_affine_of_sq_eq_one
import Theorems.Thm_CongruenceSubgroup_exists_mem_Gamma_map_eq_of_not_dvd
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Theorems.Thm_DrinfeldCurve_exists_sl_hFunctionFieldAction_smul_eq_of_not_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_supersingularProlongation_not_mem_ends_iff_affine_and_exists_levelAut_smul_ne_of_eq_two_of_dvd
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

open scoped Pointwise

namespace S1Kit

open AlgebraicCurve DrinfeldCurve

section Drinfeld

variable (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsDomain (CoordRing q k)]

abbrev xL : drinfeldFunctionField q k := algebraMap (CoordRing q k) (drinfeldFunctionField q k) (x q k)

abbrev yL : drinfeldFunctionField q k := algebraMap (CoordRing q k) (drinfeldFunctionField q k) (y q k)

theorem relL : xL q k * yL q k ^ q - xL q k ^ q * yL q k = 1 := by
  have h := congrArg (algebraMap (CoordRing q k) (drinfeldFunctionField q k)) (relation q k)
  simpa only [map_sub, map_mul, map_pow, map_one] using h

theorem yL_ne_zero : yL q k ≠ 0 := by
  intro h
  have h1 := relL q k
  have hq2 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  rw [h, zero_pow hq2, mul_zero, mul_zero, sub_zero] at h1
  exact zero_ne_one h1

theorem xL_ne_zero : xL q k ≠ 0 := by
  intro h
  have h1 := relL q k
  have hq2 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  rw [h, zero_pow hq2, zero_mul, zero_mul, sub_zero] at h1
  exact zero_ne_one h1

variable (C : Subgroup (rootsOfUnity (q + 1) (GaloisField q 2)))

def gen (ζ : ↥C) : drinfeldFunctionField q k ≃ₐ[k] drinfeldFunctionField q k :=
  hFunctionFieldAction q k ⟨(1, ((ζ : rootsOfUnity (q + 1) (GaloisField q 2)) : (GaloisField q 2)ˣ)),
    one_mem_hSubgroup_of_mem q ζ⟩

def G : Subgroup (drinfeldFunctionField q k ≃ₐ[k] drinfeldFunctionField q k) :=
  Subgroup.closure (Set.range (gen q k C))

theorem quotField_eq : quotField q k C = IntermediateField.fixedField (G q k C) := rfl

theorem mem_quotField_iff (z : drinfeldFunctionField q k) :
    z ∈ quotField q k C ↔ ∀ σ ∈ G q k C, σ z = z :=
  IntermediateField.mem_fixedField_iff (G q k C) z

theorem mem_quotField_of_gen (z : drinfeldFunctionField q k) (h : ∀ ζ : ↥C, gen q k C ζ z = z) :
    z ∈ quotField q k C := by
  rw [mem_quotField_iff]
  intro σ hσ
  induction hσ using Subgroup.closure_induction with
  | mem σ hσ =>
    obtain ⟨ζ, rfl⟩ := hσ
    exact h ζ
  | one => rfl
  | mul σ τ _ _ hσ hτ => rw [AlgEquiv.mul_apply, hτ, hσ]
  | inv σ _ hσ =>
    rw [AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq]
    exact hσ.symm

def sc (ζ : ↥C) : drinfeldFunctionField q k :=
  algebraMap k (drinfeldFunctionField q k)
    (scalarOf q k ((ζ : rootsOfUnity (q + 1) (GaloisField q 2)) : (GaloisField q 2)ˣ))

theorem sc_pow (ζ : ↥C) : sc q k C ζ ^ (q + 1) = 1 := by
  rw [sc, ← map_pow, scalarOf_pow_of_mem q k (ζ : rootsOfUnity (q + 1) (GaloisField q 2)).2, map_one]

theorem sc_ne_zero (ζ : ↥C) : sc q k C ζ ≠ 0 := by
  apply ne_zero_pow (Nat.succ_ne_zero q)
  rw [sc_pow]
  exact one_ne_zero

theorem gen_eq (ζ : ↥C) : gen q k C ζ = IsFractionRing.algEquivOfAlgEquiv (muAction q k ζ) := by
  rw [gen]
  exact hFunctionFieldAction_mu q k ζ

theorem gen_x (ζ : ↥C) : gen q k C ζ (xL q k) = sc q k C ζ * xL q k := by
  rw [gen_eq, xL, IsFractionRing.algEquivOfAlgEquiv_algebraMap, muAction_x, map_mul,
    ← IsScalarTower.algebraMap_apply]
  rfl

theorem gen_y (ζ : ↥C) : gen q k C ζ (yL q k) = sc q k C ζ * yL q k := by
  rw [gen_eq, yL, IsFractionRing.algEquivOfAlgEquiv_algebraMap, muAction_y, map_mul,
    ← IsScalarTower.algebraMap_apply]
  rfl

theorem xpow_mem : xL q k ^ (q + 1) ∈ quotField q k C :=
  mem_quotField_of_gen q k C _ fun ζ => by
    rw [map_pow, gen_x, mul_pow, sc_pow, one_mul]

theorem ypow_mem : yL q k ^ (q + 1) ∈ quotField q k C :=
  mem_quotField_of_gen q k C _ fun ζ => by
    rw [map_pow, gen_y, mul_pow, sc_pow, one_mul]

theorem u_mem : xL q k / yL q k ∈ quotField q k C :=
  mem_quotField_of_gen q k C _ fun ζ => by
    rw [map_div₀, gen_x, gen_y, mul_div_mul_left _ _ (sc_ne_zero q k C ζ)]

theorem gen_one : gen q k C 1 = 1 := by
  have : (⟨(1, (((1 : ↥C) : rootsOfUnity (q + 1) (GaloisField q 2)) : (GaloisField q 2)ˣ)),
      one_mem_hSubgroup_of_mem q _⟩ : ↥(hSubgroup q)) = 1 := rfl
  rw [gen, this, map_one]

theorem gen_mul (ζ η : ↥C) : gen q k C (ζ * η) = gen q k C ζ * gen q k C η := by
  rw [gen, gen, gen, ← map_mul]
  congr 1
  apply Subtype.ext
  change ((1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)),
      (((ζ * η : ↥C) : rootsOfUnity (q + 1) (GaloisField q 2)) : (GaloisField q 2)ˣ)) =
    ((1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)) * 1,
      ((ζ : rootsOfUnity (q + 1) (GaloisField q 2)) : (GaloisField q 2)ˣ) *
        ((η : rootsOfUnity (q + 1) (GaloisField q 2)) : (GaloisField q 2)ˣ))
  rw [mul_one]
  rfl

def genHom : ↥C →* (drinfeldFunctionField q k ≃ₐ[k] drinfeldFunctionField q k) where
  toFun := gen q k C
  map_one' := gen_one q k C
  map_mul' := gen_mul q k C

theorem G_eq_range : G q k C = (genHom q k C).range := by
  rw [G]
  have : Set.range (gen q k C) = ((genHom q k C).range : Set _) := rfl
  rw [this, Subgroup.closure_eq]

scoped instance finite_G : Finite ↥(G q k C) := by
  rw [G_eq_range]
  exact Finite.of_surjective _ (MonoidHom.rangeRestrict_surjective (genHom q k C))

scoped instance finiteDimensional_quotField :
    FiniteDimensional ↥(quotField q k C) (drinfeldFunctionField q k) :=
  (inferInstance : FiniteDimensional (FixedPoints.subfield ↥(G q k C) (drinfeldFunctionField q k))
    (drinfeldFunctionField q k))

scoped instance isSeparable_quotField :
    Algebra.IsSeparable ↥(quotField q k C) (drinfeldFunctionField q k) :=
  (inferInstance : Algebra.IsSeparable (FixedPoints.subfield ↥(G q k C) (drinfeldFunctionField q k))
    (drinfeldFunctionField q k))

theorem mem_of_pow_mem (O : ValuationSubring (drinfeldFunctionField q k)) {z : drinfeldFunctionField q k}
    {n : ℕ} (hn : n ≠ 0) (h : z ^ n ∈ O) : z ∈ O := by
  by_contra hz
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact hz O.zero_mem
  have hinv : z⁻¹ ∈ O := (O.mem_or_inv_mem z).resolve_left hz
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have : z = z ^ (m + 1) * z⁻¹ ^ m := by
    rw [pow_succ', mul_assoc, ← mul_pow, mul_inv_cancel₀ hz0, one_pow, mul_one]
  exact hz (this ▸ mul_mem h (pow_mem hinv m))

theorem algebraMap_mem_of (v : Place k (drinfeldFunctionField q k)) (hx : xL q k ∈ v.toValuationSubring)
    (hy : yL q k ∈ v.toValuationSubring) (a : CoordRing q k) :
    algebraMap (CoordRing q k) (drinfeldFunctionField q k) a ∈ v.toValuationSubring := by
  obtain ⟨p, rfl⟩ := mk_surjective q k a
  induction p using MvPolynomial.induction_on with
  | C c =>
    have : mk q k (MvPolynomial.C c) = algebraMap k (CoordRing q k) c := (mk q k).commutes c
    rw [this, ← IsScalarTower.algebraMap_apply]
    exact v.algebraMap_mem' c
  | add p₁ p₂ h₁ h₂ =>
    rw [map_add, map_add]
    exact add_mem h₁ h₂
  | mul_X p i hp =>
    rw [map_mul, map_mul]
    refine mul_mem hp ?_
    fin_cases i
    · exact hx
    · exact hy

def Pint (Q' : Place k ↥(quotField q k C)) : Prop :=
  ∀ z : ↥(quotField q k C), (z : drinfeldFunctionField q k) ∈
    Set.range (algebraMap (CoordRing q k) (drinfeldFunctionField q k)) → z ∈ Q'.toValuationSubring

theorem pint_restrict_iff (v : Place k (drinfeldFunctionField q k)) :
    Pint q k C (v.restrict ↥(quotField q k C)) ↔
      (xL q k ∈ v.toValuationSubring ∧ yL q k ∈ v.toValuationSubring) := by
  constructor
  · intro h
    have hx : (⟨xL q k ^ (q + 1), xpow_mem q k C⟩ : ↥(quotField q k C)) ∈
        (v.restrict ↥(quotField q k C)).toValuationSubring :=
      h _ ⟨x q k ^ (q + 1), by rw [map_pow]⟩
    have hy : (⟨yL q k ^ (q + 1), ypow_mem q k C⟩ : ↥(quotField q k C)) ∈
        (v.restrict ↥(quotField q k C)).toValuationSubring :=
      h _ ⟨y q k ^ (q + 1), by rw [map_pow]⟩
    rw [Place.mem_restrict_iff] at hx hy
    exact ⟨mem_of_pow_mem q k _ (Nat.succ_ne_zero q) hx, mem_of_pow_mem q k _ (Nat.succ_ne_zero q) hy⟩
  · rintro ⟨hx, hy⟩ z ⟨a, ha⟩
    rw [Place.mem_restrict_iff]
    change (z : drinfeldFunctionField q k) ∈ v.toValuationSubring
    rw [← ha]
    exact algebraMap_mem_of q k v hx hy a

variable [IsAlgClosed k]

theorem eq_of_restrict_eq {v w : Place k (drinfeldFunctionField q k)}
    (hv : xL q k ∉ v.toValuationSubring ∨ yL q k ∉ v.toValuationSubring)
    (h : v.restrict ↥(quotField q k C) = w.restrict ↥(quotField q k C)) : v = w := by
  have census := DrinfeldCurve.placesAtInfinity_census q k
  obtain ⟨hdir, -, huniq_a, huniq_inf⟩ := census
  rcases (hdir v).mp hv with hvU | ⟨a, ha, hva⟩
  · have hwU : xL q k / yL q k ∉ w.toValuationSubring := by
      intro hmem
      apply hvU
      have h1 : (⟨xL q k / yL q k, u_mem q k C⟩ : ↥(quotField q k C)) ∈
          (w.restrict ↥(quotField q k C)).toValuationSubring := hmem
      rw [← h] at h1
      exact h1
    exact huniq_inf.unique hvU hwU
  · let z : ↥(quotField q k C) := ⟨xL q k / yL q k - algebraMap k _ a,
      sub_mem (u_mem q k C) ((quotField q k C).algebraMap_mem a)⟩
    have key : ∀ u : Place k (drinfeldFunctionField q k),
        0 < u.ord (xL q k / yL q k - algebraMap k _ a) ↔ 0 < (u.restrict ↥(quotField q k C)).ord z := by
      intro u
      have e1 := u.ord_restrict (F := ↥(quotField q k C)) z
      change u.ord (xL q k / yL q k - algebraMap k _ a) = _ at e1
      rw [e1]
      exact mul_pos_iff_of_pos_left (by exact_mod_cast u.ramificationIndex_pos (F := ↥(quotField q k C)))
    have hwa : 0 < w.ord (xL q k / yL q k - algebraMap k _ a) := by
      rw [key, ← h]
      exact (key v).mp hva
    exact (huniq_a a ha).unique hva hwa

theorem natCard_notPint :
    Nat.card {Q' : Place k ↥(quotField q k C) // ¬ Pint q k C Q'} = q + 1 := by
  have census := DrinfeldCurve.placesAtInfinity_census q k
  obtain ⟨-, hcard, -, -⟩ := census
  let r : {v : Place k (drinfeldFunctionField q k) //
      xL q k ∉ v.toValuationSubring ∨ yL q k ∉ v.toValuationSubring} →
      {Q' : Place k ↥(quotField q k C) // ¬ Pint q k C Q'} := fun v =>
    ⟨v.1.restrict ↥(quotField q k C), fun hP => by
      have h2 := (pint_restrict_iff q k C v.1).mp hP
      rcases v.2 with h | h
      · exact h h2.1
      · exact h h2.2⟩
  have hinj : Function.Injective r := by
    rintro ⟨v, hv⟩ ⟨w, hw⟩ hrw
    exact Subtype.ext (eq_of_restrict_eq q k C hv (congrArg Subtype.val hrw))
  have hsurj : Function.Surjective r := by
    rintro ⟨Q', hQ'⟩
    obtain ⟨W, hW⟩ := AlgebraicCurve.Place.exists_restrict_eq (M := drinfeldFunctionField q k) Q'
    refine ⟨⟨W, ?_⟩, Subtype.ext hW⟩
    by_contra hcon
    rw [not_or, not_not, not_not] at hcon
    exact hQ' (hW ▸ (pint_restrict_iff q k C W).mpr hcon)
  rw [← hcard]
  exact (Nat.card_congr (Equiv.ofBijective r ⟨hinj, hsurj⟩)).symm

theorem exists_finset : ∃ N' : Finset (Place k ↥(quotField q k C)),
    N'.card = q + 1 ∧ ∀ Q', Q' ∉ N' ↔ Pint q k C Q' := by
  have hc := natCard_notPint q k C
  have hfin : Set.Finite {Q' : Place k ↥(quotField q k C) | ¬ Pint q k C Q'} := by
    have : Finite {Q' : Place k ↥(quotField q k C) // ¬ Pint q k C Q'} :=
      Nat.finite_of_card_ne_zero (by rw [hc]; omega)
    exact Set.finite_coe_iff.mp this
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · rw [← hc, ← Set.ncard_eq_toFinset_card _ hfin]
    exact (Nat.card_coe_set_eq _).symm
  · intro Q'
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not]

end Drinfeld

end S1Kit
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_supersingularProlongation_not_mem_ends_iff_affine_and_exists_levelAut_smul_ne_of_eq_two_of_dvd.S1Kit"

namespace S1Kit

open AlgebraicCurve DrinfeldCurve

section More

variable (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsDomain (CoordRing q k)]
variable (C : Subgroup (rootsOfUnity (q + 1) (GaloisField q 2)))

scoped instance isGalois_quotField : IsGalois ↥(quotField q k C) (drinfeldFunctionField q k) :=
  (inferInstance : IsGalois (FixedPoints.subfield ↥(G q k C) (drinfeldFunctionField q k)) (drinfeldFunctionField q k))

theorem card_aut_le :
    Nat.card (drinfeldFunctionField q k ≃ₐ[↥(quotField q k C)] drinfeldFunctionField q k) ≤ q + 1 := by
  classical
  letI : Fintype ↥(G q k C) := Fintype.ofFinite _
  have h1 : Nat.card (drinfeldFunctionField q k ≃ₐ[↥(quotField q k C)] drinfeldFunctionField q k) =
      Module.finrank ↥(quotField q k C) (drinfeldFunctionField q k) :=
    IsGalois.card_aut_eq_finrank ↥(quotField q k C) (drinfeldFunctionField q k)
  have h2 : Module.finrank ↥(quotField q k C) (drinfeldFunctionField q k) = Fintype.card ↥(G q k C) :=
    FixedPoints.finrank_eq_card ↥(G q k C) (drinfeldFunctionField q k)
  have h3 : Fintype.card ↥(G q k C) ≤ Nat.card ↥C := by
    rw [← Nat.card_eq_fintype_card, G_eq_range]
    exact Nat.card_le_card_of_surjective _ (MonoidHom.rangeRestrict_surjective (genHom q k C))
  have h4 : Nat.card ↥C ≤ Nat.card ↥(rootsOfUnity (q + 1) (GaloisField q 2)) :=
    Nat.card_le_card_of_injective (fun c : ↥C => (c : ↥(rootsOfUnity (q + 1) (GaloisField q 2))))
      (fun a b h => Subtype.ext h)
  have h5 : Nat.card ↥(rootsOfUnity (q + 1) (GaloisField q 2)) ≤ q + 1 := by
    exact card_rootsOfUnity _ _
  omega

def slEmb : Matrix.SpecialLinearGroup (Fin 2) (ZMod q) →* ↥(hSubgroup q) where
  toFun g := ⟨(Matrix.SpecialLinearGroup.toGL g, (1 : (GaloisField q 2)ˣ)), toGL_one_mem_hSubgroup q g⟩
  map_one' := Subtype.ext (Prod.ext (map_one _) rfl)
  map_mul' g g' := Subtype.ext (Prod.ext (map_mul _ g g') (by simp))

def hS : Matrix.SpecialLinearGroup (Fin 2) (ZMod q) →* (drinfeldFunctionField q k ≃ₐ[k] drinfeldFunctionField q k) :=
  (hFunctionFieldAction q k).comp (slEmb q)

theorem hS_apply (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod q)) :
    hS q k g = hFunctionFieldAction q k ⟨(Matrix.SpecialLinearGroup.toGL g, (1 : (GaloisField q 2)ˣ)),
      toGL_one_mem_hSubgroup q g⟩ := rfl

theorem comap_eq_of_smul_eq {σ : drinfeldFunctionField q k ≃ₐ[k] drinfeldFunctionField q k}
    {w : Place k (drinfeldFunctionField q k)} (h : σ • w = w) :
    w.toValuationSubring.comap σ.toAlgHom.toRingHom = w.toValuationSubring := by
  ext z
  rw [ValuationSubring.mem_comap]
  change σ z ∈ w.toValuationSubring ↔ z ∈ w.toValuationSubring
  have hO : (σ • w).toValuationSubring = w.toValuationSubring := by rw [h]
  rw [Place.smul_toValuationSubring] at hO
  conv_lhs => rw [← hO]
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, AlgEquiv.aut_inv,
    AlgEquiv.symm_apply_apply]

variable [IsAlgClosed k]

theorem eq_one_of_smul_eq {g : Matrix.SpecialLinearGroup (Fin 2) (ZMod q)} {w : Place k (drinfeldFunctionField q k)}
    (hx : xL q k ∈ w.toValuationSubring) (hy : yL q k ∈ w.toValuationSubring) (h : hS q k g • w = w) : g = 1 := by
  have hfix := comap_eq_of_smul_eq q k h
  rw [hS_apply] at hfix
  obtain ⟨ε, hε2, hmat, hsc⟩ :=
    DrinfeldCurve.exists_eq_smul_one_of_comap_hFunctionFieldAction_eq_of_affine_of_sq_eq_one q k
      ⟨(Matrix.SpecialLinearGroup.toGL g, (1 : (GaloisField q 2)ˣ)), toGL_one_mem_hSubgroup q g⟩
      (by simp) w hx hy hfix
  have hε : ε = 1 := by
    apply (algebraMap (ZMod q) (GaloisField q 2)).injective
    rw [map_one, ← hsc]; rfl
  apply Subtype.ext
  change (g : Matrix (Fin 2) (Fin 2) (ZMod q)) = 1
  have : ((Matrix.SpecialLinearGroup.toGL g : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)) :
      Matrix (Fin 2) (Fin 2) (ZMod q)) = (g : Matrix (Fin 2) (Fin 2) (ZMod q)) := rfl
  rw [← this]
  change (((⟨(Matrix.SpecialLinearGroup.toGL g, (1 : (GaloisField q 2)ˣ)), toGL_one_mem_hSubgroup q g⟩ :
      ↥(hSubgroup q)) : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ).1 :
        Matrix (Fin 2) (Fin 2) (ZMod q)) = 1
  rw [hmat, hε, one_smul]

theorem smul_injective {w : Place k (drinfeldFunctionField q k)}
    (hx : xL q k ∈ w.toValuationSubring) (hy : yL q k ∈ w.toValuationSubring) :
    Function.Injective (fun g : Matrix.SpecialLinearGroup (Fin 2) (ZMod q) => hS q k g • w) := by
  intro g g' hgg'
  have h1 : hS q k (g'⁻¹ * g) • w = w := by
    rw [map_mul, map_inv, mul_smul]
    have := congrArg (fun v => (hS q k g')⁻¹ • v) hgg'
    simpa only [inv_smul_smul] using this
  have := eq_one_of_smul_eq q k hx hy h1
  exact (inv_mul_eq_one.mp this).symm

end More
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_supersingularProlongation_not_mem_ends_iff_affine_and_exists_levelAut_smul_ne_of_eq_two_of_dvd.S1Kit"

def fam (q : ℕ) (t : (ZMod q)ˣ × ZMod q × ZMod q) : Matrix.SpecialLinearGroup (Fin 2) (ZMod q) :=
  ⟨!![(t.1 : ZMod q), t.2.1; t.2.2, (1 + t.2.1 * t.2.2) * ((t.1⁻¹ : (ZMod q)ˣ) : ZMod q)], by
    rw [Matrix.det_fin_two_of]
    have : (t.1 : ZMod q) * ((t.1⁻¹ : (ZMod q)ˣ) : ZMod q) = 1 := Units.mul_inv t.1
    linear_combination (1 + t.2.1 * t.2.2) * this⟩

theorem fam_apply00 (q : ℕ) (t : (ZMod q)ˣ × ZMod q × ZMod q) :
    (fam q t : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0 = (t.1 : ZMod q) := rfl
theorem fam_apply01 (q : ℕ) (t : (ZMod q)ˣ × ZMod q × ZMod q) :
    (fam q t : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 1 = t.2.1 := rfl
theorem fam_apply10 (q : ℕ) (t : (ZMod q)ˣ × ZMod q × ZMod q) :
    (fam q t : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 = t.2.2 := rfl

theorem fam_injective (q : ℕ) : Function.Injective (fam q) := by
  rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
  have h' : (fam q (a, b, c) : Matrix (Fin 2) (Fin 2) (ZMod q)) = (fam q (a', b', c') : Matrix (Fin 2) (Fin 2) (ZMod q)) :=
    congrArg Subtype.val h
  have ha : (a : ZMod q) = a' := by
    have := congrFun (congrFun h' 0) 0
    rwa [fam_apply00, fam_apply00] at this
  have hb : b = b' := by
    have := congrFun (congrFun h' 0) 1
    rwa [fam_apply01, fam_apply01] at this
  have hc : c = c' := by
    have := congrFun (congrFun h' 1) 0
    rwa [fam_apply10, fam_apply10] at this
  rw [Units.ext ha, hb, hc]

theorem card_sl_ge (q : ℕ) [Fact q.Prime] :
    (q - 1) * q * q ≤ Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod q)) := by
  classical
  have h := Nat.card_le_card_of_injective (fam q) (fam_injective q)
  rw [Nat.card_prod, Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ZMod.card_units,
    ZMod.card] at h
  simpa [mul_assoc] using h

theorem key_ineq (q : ℕ) (hq2 : q = 2) (n : ℕ) (hn : n ≤ 1) : ¬ ((q - 1) * q * q ≤ n * (q + 1)) := by
  subst hq2
  omega

end S1Kit
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_supersingularProlongation_not_mem_ends_iff_affine_and_exists_levelAut_smul_ne_of_eq_two_of_dvd.S1Kit"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_supersingularProlongation_not_mem_ends_iff_affine_and_exists_levelAut_smul_ne_of_eq_two_of_dvd.S1Kit"

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups Pointwise

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (FSS : Type) [Field FSS] [Algebra (ResidueField A) FSS]
    (R : RegularProlongation A (fieldBar q M') FSS)
    (N : Finset (Place (ResidueField ↥A) FSS))
    (h2 : (∀ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
        R.integers.comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom = R.integers))
    (hcard : N.card = q + 1)
    (heqv : ∀ τ ∈ Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
            ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ},
          ∀ (hτ : ∀ f : ↥(fieldBar q M'), τ f ∈ R.integers ↔ f ∈ R.integers) (Q : Place (ResidueField ↥A) FSS),
            (R.resAut τ hτ • Q ∈ N ↔ Q ∈ N))
    (inst : Algebra (GaloisField q 2) (ResidueField ↥A)) (hdom : IsDomain (DrinfeldCurve.CoordRing q (ResidueField ↥A)))
    (ζ : Idx q) (Cs : Subgroup (rootsOfUnity (q + 1) (GaloisField q 2)))
    (e : FSS ≃ₐ[ResidueField ↥A] ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs))
    (hlaw : ∀ (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      ∀ (hτ : ∀ f : ↥(fieldBar q M'), levelAutBar q M' ζ γ⁻¹ f ∈ R.integers ↔ f ∈ R.integers)
        (hmem : (redQ q γ, (1 : (GaloisField q 2)ˣ)) ∈ DrinfeldCurve.hSubgroup q),
        ∀ x : FSS,
          ((e (R.resAut (levelAutBar q M' ζ γ⁻¹) hτ x) : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) :
              DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) =
            DrinfeldCurve.hFunctionFieldAction q (ResidueField ↥A) ⟨_, hmem⟩
              ((e x : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A))) :
    (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N ↔
      ∀ z : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs),
        (z : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) ∈
          Set.range (algebraMap (DrinfeldCurve.CoordRing q (ResidueField ↥A)) (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A))) →
        e.symm z ∈ Q.toValuationSubring) ∧
    (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N →
      ∃ (γ : SL(2, ℤ)) (_ : γ ∈ Gamma0 M')
        (hτ : ∀ f : ↥(fieldBar q M'), levelAutBar q M' ζ γ f ∈ R.integers ↔ f ∈ R.integers),
        R.resAut (levelAutBar q M' ζ γ) hτ • Q ≠ Q) := by
  classical
  haveI hκ : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A

  let eR : FSS ≃+* ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs) := e.toRingEquiv
  have heR : ∀ a : ResidueField ↥A, eR (algebraMap (ResidueField ↥A) FSS a) =
      algebraMap (ResidueField ↥A) ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs) a := fun a => e.commutes a
  let Φ := AlgebraicCurve.Place.congrEquiv eR heR
  have memΦ : ∀ (Q : Place (ResidueField ↥A) FSS) (z : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)),
      z ∈ (Φ Q).toValuationSubring ↔ e.symm z ∈ Q.toValuationSubring := fun Q z => by
    change z ∈ (AlgebraicCurve.Place.congrRingEquiv eR heR Q).toValuationSubring ↔ _
    rw [AlgebraicCurve.Place.congrRingEquiv_toValuationSubring, ValuationSubring.mem_comap]
    rfl

  have pint_iff : ∀ Q : Place (ResidueField ↥A) FSS, S1Kit.Pint q (ResidueField ↥A) Cs (Φ Q) ↔
      ∀ z : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs),
        (z : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) ∈
          Set.range (algebraMap (DrinfeldCurve.CoordRing q (ResidueField ↥A)) (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A))) →
        e.symm z ∈ Q.toValuationSubring := by
    intro Q
    simp only [S1Kit.Pint, memΦ]

  obtain ⟨N', hN'card, hN'iff⟩ := S1Kit.exists_finset q (ResidueField ↥A) Cs

  obtain ⟨hred, -, -⟩ := CongruenceSubgroup.exists_mem_Gamma_map_eq_of_not_dvd M' q hqM'
  choose γ_ hγΓ hγmap using hred
  have hγ0 : ∀ g, γ_ g ∈ Gamma0 M' := fun g => by
    rw [CongruenceSubgroup.Gamma0_mem]
    exact (CongruenceSubgroup.Gamma_mem.mp (hγΓ g)).2.2.1
  have hτ_ : ∀ g, ∀ f : ↥(fieldBar q M'), levelAutBar q M' ζ (γ_ g)⁻¹ f ∈ R.integers ↔ f ∈ R.integers := by
    intro g f
    have := SetLike.ext_iff.mp (h2 ζ (γ_ g)⁻¹ (inv_mem (hγ0 g))) f
    rw [ValuationSubring.mem_comap] at this
    exact this
  let σ_ : Matrix.SpecialLinearGroup (Fin 2) (ZMod q) → (FSS ≃ₐ[ResidueField ↥A] FSS) :=
    fun g => R.resAut (levelAutBar q M' ζ (γ_ g)⁻¹) (hτ_ g)
  have hσN : ∀ g (Q : Place (ResidueField ↥A) FSS), σ_ g • Q ∈ N ↔ Q ∈ N := fun g Q =>
    heqv _ (Subgroup.subset_closure ⟨ζ, (γ_ g)⁻¹, inv_mem (hγ0 g), rfl⟩) (hτ_ g) Q
  have hmem_ : ∀ g, (redQ q (γ_ g), (1 : (GaloisField q 2)ˣ)) ∈ DrinfeldCurve.hSubgroup q := fun g =>
    DrinfeldCurve.toGL_one_mem_hSubgroup q _
  have helt : ∀ g, (⟨(redQ q (γ_ g), (1 : (GaloisField q 2)ˣ)), hmem_ g⟩ : ↥(DrinfeldCurve.hSubgroup q)) =
      S1Kit.slEmb q g := by
    intro g
    apply Subtype.ext
    refine Prod.ext ?_ ?_
    · change Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)) (γ_ g)) =
        Matrix.SpecialLinearGroup.toGL g
      rw [hγmap]
    · rfl
  have law : ∀ g (y : FSS), ((e (σ_ g y) : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) :
      DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) =
        S1Kit.hS q (ResidueField ↥A) g ((e y : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) :
          DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) := by
    intro g y
    have := hlaw (γ_ g) (hγ0 g) (hτ_ g) (hmem_ g) y
    rw [helt] at this
    exact this

  have transport : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod q)) (Q : Place (ResidueField ↥A) FSS)
      (v : Place (ResidueField ↥A) (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A))),
      v.restrict ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs) = Φ Q →
      (S1Kit.hS q (ResidueField ↥A) g • v).restrict ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs) = Φ (σ_ g • Q) := by
    intro g Q v hv
    have hQmem : ∀ y : FSS, y ∈ Q.toValuationSubring ↔
        ((e y : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) ∈
          v.toValuationSubring := by
      intro y
      have h1 := memΦ Q (e y)
      rw [AlgEquiv.symm_apply_apply, ← hv] at h1
      exact h1.symm.trans (v.mem_restrict_iff (F := ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)))
    apply AlgebraicCurve.Place.ext
    ext z
    change (z : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) ∈
        (S1Kit.hS q (ResidueField ↥A) g • v).toValuationSubring ↔ z ∈ (Φ (σ_ g • Q)).toValuationSubring
    rw [AlgebraicCurve.Place.smul_toValuationSubring, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      AlgEquiv.smul_def, AlgEquiv.aut_inv, memΦ, AlgebraicCurve.Place.smul_toValuationSubring,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, AlgEquiv.aut_inv, hQmem]
    have key : ((e ((σ_ g).symm (e.symm z)) : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) :
        DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) =
          (S1Kit.hS q (ResidueField ↥A) g).symm (z : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) := by
      rw [AlgEquiv.eq_symm_apply, ← law, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
    rw [key]

  have count : ∀ (Q : Place (ResidueField ↥A) FSS) (S : Finset (Place (ResidueField ↥A) FSS)),
      S1Kit.Pint q (ResidueField ↥A) Cs (Φ Q) → (∀ g, σ_ g • Q ∈ S) → (q - 1) * q * q ≤ S.card * (q + 1) := by
    intro Q S hP hS

    obtain ⟨v, hv⟩ := AlgebraicCurve.Place.exists_restrict_eq
      (M := DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) (Φ Q)
    obtain ⟨hvx, hvy⟩ := (S1Kit.pint_restrict_iff q (ResidueField ↥A) Cs v).mp (hv ▸ hP)

    let fib : Place (ResidueField ↥A) ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs) →
        Finset (Place (ResidueField ↥A) (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A))) := fun P =>
      if h : ∃ w : Place (ResidueField ↥A) (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)),
          w.restrict ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs) = P then
        (Finset.univ : Finset (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A) ≃ₐ[↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)]
            DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A))).image
          (fun σ => SemilinearAut.ofAlgAut (σ.restrictScalars (ResidueField ↥A)) • h.choose)
      else ∅
    have fib_card : ∀ P, (fib P).card ≤ q + 1 := by
      intro P
      simp only [fib]
      split_ifs with h
      · refine Finset.card_image_le.trans ?_
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
        exact S1Kit.card_aut_le q (ResidueField ↥A) Cs
      · simp
    have mem_fib : ∀ (w : Place (ResidueField ↥A) (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A))),
        w ∈ fib (w.restrict ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) := by
      intro w
      have h : ∃ w' : Place (ResidueField ↥A) (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)),
          w'.restrict ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs) =
            w.restrict ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs) := ⟨w, rfl⟩
      simp only [fib, dif_pos h]
      obtain ⟨σ, hσ⟩ := AlgebraicCurve.Place.exists_algEquiv_smul_eq_of_restrict_eq
        (F' := ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) h.choose w h.choose_spec.symm
      exact Finset.mem_image.mpr ⟨σ, Finset.mem_univ _, hσ⟩
    let T := (S.image Φ).biUnion fib
    have hT : ∀ g, S1Kit.hS q (ResidueField ↥A) g • v ∈ T := by
      intro g
      refine Finset.mem_biUnion.mpr ⟨Φ (σ_ g • Q), Finset.mem_image.mpr ⟨_, hS g, rfl⟩, ?_⟩
      rw [← transport g Q v hv]
      exact mem_fib _
    have hTcard : T.card ≤ S.card * (q + 1) :=
      (Finset.card_biUnion_le_card_mul _ _ _ (fun P _ => fib_card P)).trans
        (Nat.mul_le_mul_right _ Finset.card_image_le)
    have hinj := S1Kit.smul_injective q (ResidueField ↥A) hvx hvy
    let f : Matrix.SpecialLinearGroup (Fin 2) (ZMod q) → ↥T := fun g => ⟨_, hT g⟩
    have hf : Function.Injective f := fun g g' h => hinj (congrArg Subtype.val h)
    have h1 := Nat.card_le_card_of_injective f hf
    rw [Nat.card_eq_fintype_card (α := ↥T), Fintype.card_coe] at h1
    exact (S1Kit.card_sl_ge q).trans (h1.trans hTcard)

  have one_act : ∀ P : Place (ResidueField ↥A) FSS, σ_ 1 • P = P := by
    intro P
    obtain ⟨w, hw⟩ := AlgebraicCurve.Place.exists_restrict_eq (M := (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A))) (Φ P)
    have h := transport 1 P w hw
    rw [map_one, one_smul, hw] at h
    exact (Φ.injective h).symm
  have mul_act : ∀ (g h : (Matrix.SpecialLinearGroup (Fin 2) (ZMod q))) (P : Place (ResidueField ↥A) FSS), σ_ g • (σ_ h • P) = σ_ (g * h) • P := by
    intro g h P
    obtain ⟨w, hw⟩ := AlgebraicCurve.Place.exists_restrict_eq (M := (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A))) (Φ P)
    have h1 := transport h P w hw
    have h2 := transport g (σ_ h • P) _ h1
    have h3 := transport (g * h) P w hw
    rw [map_mul, mul_smul] at h3
    exact Φ.injective (h2.symm.trans h3)

  have ofAlgAut_place : ∀ (τ : (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) ≃ₐ[(ResidueField ↥A)] (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A))) (w : Place (ResidueField ↥A) (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A))), SemilinearAut.ofAlgAut τ • w = τ • w := by
    intro τ w
    apply AlgebraicCurve.Place.ext
    rw [SemilinearAut.smul_toValuationSubring, AlgebraicCurve.Place.smul_toValuationSubring]
    ext z
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      ← map_inv, SemilinearAut.ofAlgAut_smul, AlgEquiv.smul_def]

  have hGpow : ∀ τ ∈ S1Kit.G q (ResidueField ↥A) Cs, τ ^ (q + 1) = 1 := by
    intro τ hτ
    rw [S1Kit.G_eq_range] at hτ
    obtain ⟨c, rfl⟩ := hτ
    have hc : c ^ (q + 1) = 1 := by
      apply Subtype.ext; apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_pow, Subgroup.coe_one, Subgroup.coe_one]
      have := (c : ↥(rootsOfUnity (q + 1) (GaloisField q 2))).2
      rw [mem_rootsOfUnity] at this
      exact this
    rw [← map_pow, hc, map_one]
  have cube : ∀ β : (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) ≃ₐ[↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)] (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)), β ^ 3 = 1 := by
    classical
    letI : Fintype ↥(S1Kit.G q (ResidueField ↥A) Cs) := Fintype.ofFinite _
    have h1 : Nat.card ((DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) ≃ₐ[↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)] (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A))) = Module.finrank ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs) (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) :=
      IsGalois.card_aut_eq_finrank ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs) (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A))
    have h2 : Module.finrank ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs) (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) = Fintype.card ↥(S1Kit.G q (ResidueField ↥A) Cs) :=
      FixedPoints.finrank_eq_card ↥(S1Kit.G q (ResidueField ↥A) Cs) (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A))
    have hle : Nat.card ((DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) ≃ₐ[↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)] (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A))) ≤ q + 1 := S1Kit.card_aut_le q (ResidueField ↥A) Cs
    have hne2 : Fintype.card ↥(S1Kit.G q (ResidueField ↥A) Cs) ≠ 2 := by
      intro h2'
      obtain ⟨τ, hτ⟩ := exists_prime_orderOf_dvd_card (G := ↥(S1Kit.G q (ResidueField ↥A) Cs)) 2 (by rw [h2'])
      have h3 : (τ : (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) ≃ₐ[(ResidueField ↥A)] (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A))) ^ (q + 1) = 1 := hGpow τ τ.2
      have h3' : τ ^ (q + 1) = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact h3)
      have hd : orderOf τ ∣ q + 1 := orderOf_dvd_of_pow_eq_one h3'
      rw [hτ] at hd
      omega
    intro β
    have hpos : 0 < Nat.card ((DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) ≃ₐ[↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)] (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A))) := Nat.card_pos
    have hc : Nat.card ((DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) ≃ₐ[↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)] (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A))) = 1 ∨ Nat.card ((DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) ≃ₐ[↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)] (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A))) = 3 := by
      rw [h1, h2] at hle hpos ⊢; omega
    rcases hc with hc | hc
    · haveI := (Nat.card_eq_one_iff_unique.mp hc).1
      exact Subsingleton.elim _ _
    · rw [← hc]; exact pow_card_eq_one'

  have invol_free : ∀ (Q : Place (ResidueField ↥A) FSS), S1Kit.Pint q (ResidueField ↥A) Cs (Φ Q) →
      ∀ g : (Matrix.SpecialLinearGroup (Fin 2) (ZMod q)), g * g = 1 → σ_ g • Q = Q → g = 1 := by
    intro Q hP g hgg hfix
    obtain ⟨v, hv⟩ := AlgebraicCurve.Place.exists_restrict_eq (M := (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A))) (Φ Q)
    have aff : ∀ w : Place (ResidueField ↥A) (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)), w.restrict ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs) = Φ Q →
        S1Kit.xL q (ResidueField ↥A) ∈ w.toValuationSubring ∧ S1Kit.yL q (ResidueField ↥A) ∈ w.toValuationSubring := by
      intro w hw
      have : S1Kit.Pint q (ResidueField ↥A) Cs (w.restrict ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) := by rw [hw]; exact hP
      exact (S1Kit.pint_restrict_iff q (ResidueField ↥A) Cs w).mp this
    have Tlift : ∀ w : Place (ResidueField ↥A) (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)), w.restrict ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs) = Φ Q → (S1Kit.hS q (ResidueField ↥A) g • w).restrict ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs) = Φ Q := by
      intro w hw; rw [transport g Q w hw, hfix]
    have TT : ∀ w : Place (ResidueField ↥A) (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)), S1Kit.hS q (ResidueField ↥A) g • (S1Kit.hS q (ResidueField ↥A) g • w) = w := by
      intro w; rw [← mul_smul, ← map_mul, hgg, map_one, one_smul]
    have Tinj : ∀ w w' : Place (ResidueField ↥A) (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)), S1Kit.hS q (ResidueField ↥A) g • w = S1Kit.hS q (ResidueField ↥A) g • w' → w = w' := by
      intro w w' h; have := congrArg (fun u => S1Kit.hS q (ResidueField ↥A) g • u) h; simpa only [TT] using this
    have Tfix : ∀ w : Place (ResidueField ↥A) (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)), w.restrict ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs) = Φ Q → S1Kit.hS q (ResidueField ↥A) g • w = w → g = 1 :=
      fun w hw h => S1Kit.eq_one_of_smul_eq q (ResidueField ↥A) (aff w hw).1 (aff w hw).2 h

    let S : ((DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) ≃ₐ[↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)] (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A))) → ((DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) ≃ₐ[(ResidueField ↥A)] (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A))) := fun β => β.restrictScalars (ResidueField ↥A)
    have S_mul : ∀ β γ : (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) ≃ₐ[↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)] (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)), S (β * γ) = S β * S γ := fun _ _ => rfl
    have S_one : S 1 = 1 := rfl
    have S_pow3 : ∀ β : (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) ≃ₐ[↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)] (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)), S β • (S β • (S β • v)) = v := by
      intro β; rw [← mul_smul, ← mul_smul, ← S_mul, ← S_mul, ← pow_three', cube, S_one, one_smul]
    have lifts : ∀ w : Place (ResidueField ↥A) (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)), w.restrict ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs) = Φ Q → ∃ β : (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) ≃ₐ[↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)] (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)), S β • v = w := by
      intro w hw
      obtain ⟨β, hβ⟩ := AlgebraicCurve.Place.exists_algEquiv_smul_eq_of_restrict_eq (F' := ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) v w (hw.trans hv.symm)
      exact ⟨β, by rw [← ofAlgAut_place]; exact hβ⟩
    have Slift : ∀ (β : (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) ≃ₐ[↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)] (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A))) (w : Place (ResidueField ↥A) (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A))), w.restrict ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs) = Φ Q → (S β • w).restrict ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs) = Φ Q := by
      intro β w hw
      rw [← hw]
      apply AlgebraicCurve.Place.ext
      ext f
      rw [AlgebraicCurve.Place.mem_restrict_iff, AlgebraicCurve.Place.mem_restrict_iff, AlgebraicCurve.Place.smul_toValuationSubring,
        ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, AlgEquiv.aut_inv]
      have key : (S β).symm (algebraMap ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs) (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) f) = algebraMap ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs) (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) f := β.symm.commutes f
      rw [key]

    obtain ⟨β, hβ⟩ := lifts (S1Kit.hS q (ResidueField ↥A) g • v) (Tlift v hv)
    by_cases hβ1 : β = 1
    · exact Tfix v hv (by rw [← hβ, hβ1, S_one, one_smul])
    classical
    have hle : Nat.card ((DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) ≃ₐ[↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)] (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A))) ≤ q + 1 := S1Kit.card_aut_le q (ResidueField ↥A) Cs
    have hβ2 : β ^ 2 ≠ 1 := by
      intro h; apply hβ1
      have : β = β ^ 3 * (β ^ 2)⁻¹ := by group
      rw [this, cube, h, inv_one, one_mul]
    have hβ12 : β ^ 2 ≠ β := by
      intro h; apply hβ1
      have : β = β ^ 2 * β⁻¹ := by group
      rw [this, h, mul_inv_cancel]
    have all3 : ∀ γ : (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) ≃ₐ[↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)] (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)), γ = 1 ∨ γ = β ∨ γ = β ^ 2 := by
      intro γ
      have hs : ({1, β, β ^ 2} : Finset ((DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) ≃ₐ[↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)] (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)))).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
        · rw [Finset.mem_singleton]; exact fun h => hβ12 h.symm
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨fun h => hβ1 h.symm, fun h => hβ2 h.symm⟩
      have huniv : ({1, β, β ^ 2} : Finset ((DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) ≃ₐ[↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)] (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)))) = Finset.univ := by
        apply Finset.eq_univ_of_card
        apply le_antisymm (Finset.card_le_univ _)
        rw [hs, ← Nat.card_eq_fintype_card]; omega
      have : γ ∈ ({1, β, β ^ 2} : Finset ((DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) ≃ₐ[↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)] (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)))) := by rw [huniv]; exact Finset.mem_univ _
      simpa only [Finset.mem_insert, Finset.mem_singleton] using this
    have hv2 : (S (β ^ 2) • v).restrict ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs) = Φ Q := Slift _ v hv
    obtain ⟨γ, hγ⟩ := lifts (S1Kit.hS q (ResidueField ↥A) g • (S (β ^ 2) • v)) (Tlift _ hv2)
    have hTB : S1Kit.hS q (ResidueField ↥A) g • (S β • v) = v := by rw [hβ, TT]
    obtain hγ1 | hγ1 | hγ1 := all3 γ <;> rw [hγ1] at hγ
    ·
      rw [S_one, one_smul] at hγ
      have e1 : S (β ^ 2) • v = S β • v := Tinj _ _ (hγ.symm.trans hTB.symm)
      rw [pow_two, S_mul, mul_smul] at e1
      have e3 := congrArg (fun u => S β • u) e1
      beta_reduce at e3
      rw [S_pow3, e1] at e3
      exact Tfix v hv (by rw [← hβ, ← e3])
    ·
      have e1 : S (β ^ 2) • v = v := Tinj _ _ (hγ.symm.trans hβ)
      rw [pow_two, S_mul, mul_smul] at e1
      have e3 := congrArg (fun u => S β • u) e1
      beta_reduce at e3
      rw [S_pow3] at e3
      exact Tfix v hv (by rw [← hβ, ← e3])
    ·
      exact Tfix _ hv2 hγ.symm

  have nonaff_all : ∀ P ∈ N, ¬ S1Kit.Pint q (ResidueField ↥A) Cs (Φ P) → ∀ P' : Place (ResidueField ↥A) FSS, ¬ S1Kit.Pint q (ResidueField ↥A) Cs (Φ P') → P' ∈ N := by
    intro P hPN hP P' hP'
    obtain ⟨w, hw⟩ := AlgebraicCurve.Place.exists_restrict_eq (M := (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A))) (Φ P)
    obtain ⟨w', hw'⟩ := AlgebraicCurve.Place.exists_restrict_eq (M := (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A))) (Φ P')
    have naff : ∀ (u : Place (ResidueField ↥A) (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A))) (P₀ : Place (ResidueField ↥A) FSS), u.restrict ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs) = Φ P₀ → ¬ S1Kit.Pint q (ResidueField ↥A) Cs (Φ P₀) →
        (S1Kit.xL q (ResidueField ↥A) ∉ u.toValuationSubring ∨ S1Kit.yL q (ResidueField ↥A) ∉ u.toValuationSubring) := by
      intro u P₀ hu h0
      by_contra hc
      rw [not_or, not_not, not_not] at hc
      exact h0 (hu ▸ (S1Kit.pint_restrict_iff q (ResidueField ↥A) Cs u).mpr hc)
    obtain ⟨g, hg⟩ := DrinfeldCurve.exists_sl_hFunctionFieldAction_smul_eq_of_not_mem q (ResidueField ↥A) w w'
      (naff w P hw hP) (naff w' P' hw' hP')
    have h1 := transport g P w hw
    rw [S1Kit.hS_apply] at h1
    rw [hg, hw'] at h1
    have : P' = σ_ g • P := Φ.injective h1
    rw [this]
    exact (hσN g P).mpr hPN

  have noaff : ∀ Q ∈ N, ¬ S1Kit.Pint q (ResidueField ↥A) Cs (Φ Q) := by
    intro Q hQ hP

    have allaff : ∀ P ∈ N, S1Kit.Pint q (ResidueField ↥A) Cs (Φ P) := by
      intro P hPN
      by_contra hPa
      have hsub : N' ⊆ N.map Φ.toEmbedding := by
        intro P' hP'
        rw [Finset.mem_map_equiv]
        have hP'na : ¬ S1Kit.Pint q (ResidueField ↥A) Cs P' := fun h => ((hN'iff P').mpr h) hP'
        exact nonaff_all P hPN hPa (Φ.symm P') (by rw [Equiv.apply_symm_apply]; exact hP'na)
      have heq : N' = N.map Φ.toEmbedding :=
        Finset.eq_of_subset_of_card_le hsub (by rw [hN'card, Finset.card_map, hcard])
      have hQ' : Φ Q ∈ N' := by rw [heq, Finset.mem_map_equiv, Equiv.symm_apply_apply]; exact hQ
      exact ((hN'iff (Φ Q)).mpr hP) hQ'

    have h2z : (2 : ZMod q) = 0 := by
      have h : ((2 : ℕ) : ZMod q) = 0 := by rw [← hq2]; exact ZMod.natCast_self q
      rwa [Nat.cast_ofNat] at h
    obtain ⟨t, htt, ht1⟩ : ∃ t : (Matrix.SpecialLinearGroup (Fin 2) (ZMod q)), t * t = 1 ∧ t ≠ 1 := by
      refine ⟨⟨!![1, 1; 0, 1], by rw [Matrix.det_fin_two_of]; ring⟩, ?_, ?_⟩
      · apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two, h2z, one_add_one_eq_two]
      · intro h
        have := congrArg (fun m : (Matrix.SpecialLinearGroup (Fin 2) (ZMod q)) => (m : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 1) h
        simp at this
    classical
    let f : ↥N → ↥N := fun P => ⟨σ_ t • (P : Place (ResidueField ↥A) FSS), (hσN t P).mpr P.2⟩
    have hf : Function.Involutive f := by
      intro P; apply Subtype.ext; show σ_ t • (σ_ t • (P : Place (ResidueField ↥A) FSS)) = P; rw [mul_act, htt, one_act]
    have hfix : ∀ P, f P ≠ P := by
      intro P h
      exact ht1 (invol_free P (allaff P P.2) t htt (congrArg Subtype.val h))

    let F : Function.End ↥N := f
    have hF : F ^ 2 ^ 1 = 1 := by
      rw [pow_one, sq]; funext P; change f (f P) = P; exact hf P
    have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 2) (n := 1) hF
    change Fintype.card ↥N ≡ Fintype.card ↑(Function.fixedPoints f) [MOD 2] at hmod
    have h0 : Fintype.card ↑(Function.fixedPoints f) = 0 := by
      rw [Fintype.card_eq_zero_iff]; exact ⟨fun P => hfix P.1 P.2⟩
    rw [h0, Fintype.card_coe, hcard, hq2] at hmod
    revert hmod; decide

  have hsub : N.map Φ.toEmbedding ⊆ N' := by
    intro P hP
    rw [Finset.mem_map_equiv] at hP
    have := noaff _ hP
    rw [Equiv.apply_symm_apply] at this
    by_contra hP'
    exact this ((hN'iff P).mp hP')
  have heq : N.map Φ.toEmbedding = N' :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hN'card, Finset.card_map, hcard])
  have part1 : ∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N ↔
      ∀ z : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs),
        (z : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) ∈
          Set.range (algebraMap (DrinfeldCurve.CoordRing q (ResidueField ↥A)) (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A))) →
        e.symm z ∈ Q.toValuationSubring := by
    intro Q
    rw [← pint_iff, ← hN'iff, ← heq, Finset.mem_map_equiv, Equiv.symm_apply_apply]
  refine ⟨part1, ?_⟩

  intro Q hQ
  have hP : S1Kit.Pint q (ResidueField ↥A) Cs (Φ Q) := (pint_iff Q).mpr ((part1 Q).mp hQ)
  by_contra hall
  push_neg at hall
  have hfix : ∀ g, σ_ g • Q ∈ ({Q} : Finset (Place (ResidueField ↥A) FSS)) := by
    intro g
    rw [Finset.mem_singleton]
    exact hall (γ_ g)⁻¹ (inv_mem (hγ0 g)) (hτ_ g)
  have := count Q {Q} hP hfix
  rw [Finset.card_singleton] at this
  exact S1Kit.key_ineq q hq2 1 (by omega) this

end S_ModularCurve_FullLevel_supersingularProlongation_not_mem_ends_iff_affine_and_exists_levelAut_smul_ne_of_eq_two_of_dvd
end P2MW
export P2MW.S_ModularCurve_FullLevel_supersingularProlongation_not_mem_ends_iff_affine_and_exists_levelAut_smul_ne_of_eq_two_of_dvd (solution)
