-- Prove2me | solution 1 for ModularCurve.FullLevel.supersingularProlongation_ends_of_affineChart
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/ebadbe33-8883-5ecb-88db-5fd38a0cc60f

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
import Theorems.Thm_DrinfeldCurve_placesAtInfinity_census
import Theorems.Thm_AlgebraicCurve_Place_exists_restrict_eq
import Theorems.Thm_ModularCurve_FullLevel_levelAutBar_mul
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_supersingularProlongation_ends_of_affineChart
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

noncomputable section

open scoped Pointwise

namespace B3Ends

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
  have hq : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  rw [h, zero_pow hq, mul_zero, mul_zero, sub_zero] at h1
  exact zero_ne_one h1

theorem xL_ne_zero : xL q k ≠ 0 := by
  intro h
  have h1 := relL q k
  have hq : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  rw [h, zero_pow hq, zero_mul, zero_mul, sub_zero] at h1
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

end B3Ends
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_supersingularProlongation_ends_of_affineChart.B3Ends"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_supersingularProlongation_ends_of_affineChart.B3Ends"

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (s : ↥W)
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    (Kb : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (Ab : ValuationSubring ↥Kb) (hAb : ∀ x : ↥Kb, x ∈ Ab ↔ (x : (AlgebraicClosure ℚ)) ∈ A) (ϖb : ↥Ab)
    (inst : Algebra (GaloisField q 2) (ResidueField ↥A)) (hdomC : IsDomain (DrinfeldCurve.CoordRing q (ResidueField ↥A)))
    (B : Subring ↥(fieldBar q M')) (alg : Algebra ↥Ab ↥B)
    (hM5b : (∀ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → ∀ f : ↥(fieldBar q M'), f ∈ B → levelAutBar q M' ζ γ f ∈ B))
    (FSS : Type) [Field FSS] [Algebra (ResidueField ↥A) FSS] (R : RegularProlongation A ↥(fieldBar q M') FSS)
    (hBR : ∀ f : ↥(fieldBar q M'), f ∈ B → f ∈ R.integers)
    (Cs : Subgroup (rootsOfUnity (q + 1) (GaloisField q 2)))
    (ρ : ↥B →+* ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs))
    (hρrange : ∀ z : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs), z ∈ Set.range ρ ↔
      (z : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) ∈ Set.range (algebraMap (DrinfeldCurve.CoordRing q (ResidueField ↥A)) (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A))))
    (e : FSS ≃ₐ[(ResidueField ↥A)] ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) (he : ∀ b : ↥B, e (R.residue ⟨((b : ↥B) : ↥(fieldBar q M')), hBR _ (b).2⟩) = ρ b) :
    ∃ N : Finset (Place (ResidueField ↥A) FSS),
      N.card = q + 1 ∧
      (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N ↔ ∀ b : ↥B, R.residue ⟨((b : ↥B) : ↥(fieldBar q M')), hBR _ (b).2⟩ ∈ Q.toValuationSubring) ∧
      (∀ τ ∈ Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
          ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ},
        ∀ (hτ : ∀ f : ↥(fieldBar q M'), τ f ∈ R.integers ↔ f ∈ R.integers) (Q : Place (ResidueField ↥A) FSS),
          (R.resAut τ hτ • Q ∈ N ↔ Q ∈ N)) := by
  classical
  haveI hκ : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A

  obtain ⟨N', hN'card, hN'iff⟩ := B3Ends.exists_finset q (ResidueField ↥A) Cs

  let eR : FSS ≃+* ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs) := e.toRingEquiv
  have heR : ∀ a : ResidueField ↥A, eR (algebraMap (ResidueField ↥A) FSS a) =
      algebraMap (ResidueField ↥A) ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs) a := fun a => e.commutes a
  let Φ := AlgebraicCurve.Place.congrEquiv eR heR
  have memΦ : ∀ (Q : Place (ResidueField ↥A) FSS) (z : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)),
      z ∈ (Φ Q).toValuationSubring ↔ e.symm z ∈ Q.toValuationSubring := fun Q z => by
    change z ∈ (AlgebraicCurve.Place.congrRingEquiv eR heR Q).toValuationSubring ↔ _
    rw [AlgebraicCurve.Place.congrRingEquiv_toValuationSubring, ValuationSubring.mem_comap]
    rfl
  refine ⟨N'.map Φ.symm.toEmbedding, by rw [Finset.card_map, hN'card], ?_⟩
  have memN : ∀ Q : Place (ResidueField ↥A) FSS, Q ∈ N'.map Φ.symm.toEmbedding ↔ Φ Q ∈ N' := fun Q => by
    rw [Finset.mem_map_equiv, Equiv.symm_symm]

  have iffQ : ∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N'.map Φ.symm.toEmbedding ↔
      ∀ b : ↥B, R.residue ⟨((b : ↥B) : ↥(fieldBar q M')), hBR _ (b).2⟩ ∈ Q.toValuationSubring := by
    intro Q
    rw [memN, hN'iff]
    constructor
    · intro hP b
      have hr : ((ρ b : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) :
          DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) ∈
          Set.range (algebraMap (DrinfeldCurve.CoordRing q (ResidueField ↥A))
            (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A))) := (hρrange (ρ b)).mp ⟨b, rfl⟩
      have h1 := (memΦ Q (ρ b)).mp (hP (ρ b) hr)
      rwa [← he b, AlgEquiv.symm_apply_apply] at h1
    · intro hB z hz
      obtain ⟨b, rfl⟩ := (hρrange z).mpr hz
      rw [memΦ, ← he b, AlgEquiv.symm_apply_apply]
      exact hB b
  refine ⟨iffQ, ?_⟩

  intro τ hτmem

  have stab : (∀ f : ↥(fieldBar q M'), f ∈ B → τ f ∈ B) ∧ (∀ f : ↥(fieldBar q M'), f ∈ B → τ⁻¹ f ∈ B) := by
    induction hτmem using Subgroup.closure_induction with
    | mem σ hσ =>
      obtain ⟨ζ', γ, hγ, rfl⟩ := hσ
      refine ⟨hM5b ζ' γ hγ, ?_⟩
      have hγ' : γ⁻¹ ∈ Gamma0 M' := inv_mem hγ
      have h11 := ModularCurve.FullLevel.levelAutBar_mul q M' hqM' ζ' 1 1 (one_mem _) (one_mem _)
      rw [mul_one] at h11
      have hone : ∀ x : ↥(fieldBar q M'), levelAutBar q M' ζ' 1 x = x := by
        intro x
        have h2 := congrArg (fun σ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') =>
          σ ((levelAutBar q M' ζ' 1).symm x)) h11
        simp only [AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply] at h2
        exact h2.symm
      have hmul := ModularCurve.FullLevel.levelAutBar_mul q M' hqM' ζ' γ γ⁻¹ hγ hγ'
      rw [mul_inv_cancel] at hmul
      have hkey : ∀ x : ↥(fieldBar q M'), levelAutBar q M' ζ' γ⁻¹ (levelAutBar q M' ζ' γ x) = x := by
        intro x
        have h3 := congrArg (fun σ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') => σ x) hmul
        simp only [AlgEquiv.trans_apply] at h3
        rw [← h3]
        exact hone x
      intro f hf
      have h4 : (levelAutBar q M' ζ' γ)⁻¹ f = levelAutBar q M' ζ' γ⁻¹ f := by
        rw [AlgEquiv.aut_inv]
        conv_rhs => rw [← (levelAutBar q M' ζ' γ).apply_symm_apply f]
        exact (hkey _).symm
      rw [h4]
      exact hM5b ζ' γ⁻¹ hγ' f hf
    | one =>
      exact ⟨fun f hf => by rw [AlgEquiv.one_apply]; exact hf,
        fun f hf => by rw [inv_one, AlgEquiv.one_apply]; exact hf⟩
    | mul σ σ' _ _ h h' =>
      exact ⟨fun f hf => by rw [AlgEquiv.mul_apply]; exact h.1 _ (h'.1 f hf),
        fun f hf => by rw [mul_inv_rev, AlgEquiv.mul_apply]; exact h'.2 _ (h.2 f hf)⟩
    | inv σ _ h =>
      exact ⟨fun f hf => h.2 f hf, fun f hf => by rw [inv_inv]; exact h.1 f hf⟩
  intro hτ Q
  have stab2 : ∀ f : ↥(fieldBar q M'), f ∈ B → τ.symm f ∈ B := fun f hf => by
    rw [← AlgEquiv.aut_inv]; exact stab.2 f hf

  have hres : ∀ b : ↥B, (R.resAut τ hτ).symm (R.residue ⟨((b : ↥B) : ↥(fieldBar q M')), hBR _ (b).2⟩) =
      R.residue ⟨τ.symm ((b : ↥B) : ↥(fieldBar q M')), hBR _ (stab2 _ b.2)⟩ := by
    intro b
    rw [AlgEquiv.symm_apply_eq, AlgebraicCurve.RegularProlongation.resAut_residue]
    congr 1
    apply Subtype.ext
    exact (τ.apply_symm_apply _).symm
  suffices key : R.resAut τ hτ • Q ∉ N'.map Φ.symm.toEmbedding ↔ Q ∉ N'.map Φ.symm.toEmbedding from
    not_iff_not.mp key
  rw [iffQ, iffQ]
  constructor
  · intro h b
    have hb' := h ⟨τ ((b : ↥B) : ↥(fieldBar q M')), stab.1 _ b.2⟩
    rw [AlgebraicCurve.Place.smul_toValuationSubring, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      AlgEquiv.smul_def, AlgEquiv.aut_inv, hres] at hb'
    have e1 : (⟨((b : ↥B) : ↥(fieldBar q M')), hBR _ (b).2⟩ : ↥R.integers) =
        ⟨τ.symm (((⟨τ ((b : ↥B) : ↥(fieldBar q M')), stab.1 _ b.2⟩ : ↥B) : ↥(fieldBar q M'))),
          hBR _ (stab2 _ (stab.1 _ b.2))⟩ :=
      Subtype.ext (show ((b : ↥B) : ↥(fieldBar q M')) = τ.symm (τ ((b : ↥B) : ↥(fieldBar q M'))) from
        (τ.symm_apply_apply _).symm)
    rw [e1]
    exact hb'
  · intro h b
    rw [AlgebraicCurve.Place.smul_toValuationSubring, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      AlgEquiv.smul_def, AlgEquiv.aut_inv, hres]
    exact h ⟨τ.symm ((b : ↥B) : ↥(fieldBar q M')), stab2 _ b.2⟩

end S_ModularCurve_FullLevel_supersingularProlongation_ends_of_affineChart
end P2MW
export P2MW.S_ModularCurve_FullLevel_supersingularProlongation_ends_of_affineChart (solution)
