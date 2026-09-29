-- Prove2me | solution 1 for ModularCurve.FullLevel.mem_iff_coe_mem_drinfeldRing_of_affineChart_nodes_cover_of_eq_two_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/ea08e5e5-12d8-5691-8999-a661e5bc80ca

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_ModularCurve_UVCrossingModel

import Theorems.Thm_ValuationSubring_eq_or_eq_top_of_toSubring_le_of_isDiscreteValuationRing
import Theorems.Thm_ValuationSubring_nonempty_ringHom_residueField_of_finite_of_charP
import Theorems.Thm_DrinfeldCurve_isDomain_coordRing_of_ne_one
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_of_isAlgClosed
import Theorems.Thm_DrinfeldCurve_isDedekindDomain_coordRing
import Theorems.Thm_DrinfeldCurve_affinePlaces_census
import Theorems.Thm_DrinfeldCurve_algebraMap_mem_quotField_iff_forall_muAction_eq_and_exists_of_mem_quotField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_mem_iff_coe_mem_drinfeldRing_of_affineChart_nodes_cover_of_eq_two_of_dvd
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

namespace SSIC

open IsLocalRing

theorem isUnit_iff_ne_zero_and_inv_mem {K : Type*} [Field K] (A : ValuationSubring K) (x : K) (hx : x ∈ A) :
    IsUnit (⟨x, hx⟩ : ↥A) ↔ x ≠ 0 ∧ x⁻¹ ∈ A := by
  constructor
  · rintro ⟨u, hu⟩
    have h1 : ((u⁻¹ : (↥A)ˣ) : ↥A) * (⟨x, hx⟩ : ↥A) = 1 := by rw [← hu, Units.inv_mul]
    have h1' : (((u⁻¹ : (↥A)ˣ) : ↥A) : K) * x = 1 := by
      have := congrArg Subtype.val h1
      simpa using this
    have hx0 : x ≠ 0 := by
      intro h0; rw [h0, mul_zero] at h1'; exact zero_ne_one h1'
    refine ⟨hx0, ?_⟩
    have heq : (((u⁻¹ : (↥A)ˣ) : ↥A) : K) = x⁻¹ := eq_inv_of_mul_eq_one_left h1'
    rw [← heq]
    exact ((u⁻¹ : (↥A)ˣ) : ↥A).2
  · rintro ⟨hx0, hinv⟩
    refine isUnit_iff_exists_inv.mpr ⟨⟨x⁻¹, hinv⟩, ?_⟩
    apply Subtype.ext
    show x * x⁻¹ = 1
    exact mul_inv_cancel₀ hx0

theorem isUnit_subring_iff_ne_zero_and_inv_mem {K : Type*} [Field K] (A : Subring K) (x : K) (hx : x ∈ A) :
    IsUnit (⟨x, hx⟩ : ↥A) ↔ x ≠ 0 ∧ x⁻¹ ∈ A := by
  constructor
  · rintro ⟨u, hu⟩
    have h1 : ((u⁻¹ : (↥A)ˣ) : ↥A) * (⟨x, hx⟩ : ↥A) = 1 := by rw [← hu, Units.inv_mul]
    have h1' : (((u⁻¹ : (↥A)ˣ) : ↥A) : K) * x = 1 := by
      have := congrArg Subtype.val h1
      simpa using this
    have hx0 : x ≠ 0 := by
      intro h0; rw [h0, mul_zero] at h1'; exact zero_ne_one h1'
    refine ⟨hx0, ?_⟩
    have heq : (((u⁻¹ : (↥A)ˣ) : ↥A) : K) = x⁻¹ := eq_inv_of_mul_eq_one_left h1'
    rw [← heq]
    exact ((u⁻¹ : (↥A)ˣ) : ↥A).2
  · rintro ⟨hx0, hinv⟩
    refine isUnit_iff_exists_inv.mpr ⟨⟨x⁻¹, hinv⟩, ?_⟩
    apply Subtype.ext
    show x * x⁻¹ = 1
    exact mul_inv_cancel₀ hx0

theorem valuationSubring_eq_top_of_isAlgebraic_of_finite (k K : Type*) [Field k] [Finite k] [Field K]
    [Algebra k K] [Algebra.IsAlgebraic k K] (O : ValuationSubring K) : O = ⊤ := by
  haveI : Module.Finite ℤ k := Module.Finite.of_finite
  haveI : Algebra.IsIntegral ℤ k := Algebra.IsIntegral.of_finite ℤ k
  haveI : Algebra.IsIntegral k K := Algebra.IsAlgebraic.isIntegral
  haveI : Algebra.IsIntegral ℤ K := Algebra.IsIntegral.trans k
  ext x
  refine ⟨fun _ => ValuationSubring.mem_top x, fun _ => ?_⟩
  have hx : IsIntegral ℤ x := Algebra.IsIntegral.isIntegral x
  have hx' : IsIntegral ↥O x := hx.tower_top
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥O) (K := K)).mp hx'
  rw [← hy]
  exact y.2

theorem mem_of_pow_mem {K : Type*} [Field K] (O : ValuationSubring K) (x : K) (n : ℕ) (hn : n ≠ 0)
    (h : x ^ n ∈ O) : x ∈ O := by
  have hint : IsIntegral ↥O x := ⟨Polynomial.X ^ n - Polynomial.C ⟨x ^ n, h⟩,
    Polynomial.monic_X_pow_sub_C _ hn, by simp⟩
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥O) (K := K)).mp hint
  rw [← hy]; exact y.2

end SSIC

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 0 in

theorem solution
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (s : ↥W)
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
      Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A)
    (ζ : Idx q)
    (Kb : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (hKb : Kb = ⊥)
    (Ab : ValuationSubring ↥Kb) (hAb : ∀ x : ↥Kb, x ∈ Ab ↔ (x : (AlgebraicClosure ℚ)) ∈ A)
    (ϖb : ↥Ab) (hϖb : maximalIdeal ↥Ab = Ideal.span {ϖb}) (hϖb0 : ϖb ≠ 0)
    (O' : ValuationSubring ↥(fieldBar q M'))
    (hO'_A : ∀ x : AlgebraicClosure ℚ, algebraMap (AlgebraicClosure ℚ) (fieldBar q M') x ∈ O' ↔ x ∈ A)
    (hO'_over : ∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
      (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
        (IntermediateField.inclusion hle f : fieldBar q M') ∈ O' ∧
        ∀ a : A, residue A a =
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
          ∃ h : (IntermediateField.inclusion hle f : fieldBar q M')
              - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ O',
            (⟨_, h⟩ : O') ∈ maximalIdeal (O'))
    (hO'_fix : ∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      O'.comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = O')
    :
    letI : Algebra ↥k₀ ↥(fieldBar q M') :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
    ∀ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M')),

      (∀ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → ∀ f : ↥(fieldBar q M'), f ∈ F₀ → levelAutBar q M' ζ γ f ∈ F₀) →
    ∀ (W₀ : ValuationSubring ↥F₀),

      (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥F₀ x ∈ W₀) →
      IsDiscreteValuationRing ↥W₀ →
      (∃ hπW : algebraMap ↥k₀ ↥F₀ π₀ ∈ W₀, maximalIdeal ↥W₀ = Ideal.span {(⟨_, hπW⟩ : ↥W₀)}) →

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
            (⟨_, hF⟩ : ↥F₀) ∈ W₀ ∧
            ∀ (c : ↥k₀) (hc : (c : (AlgebraicClosure ℚ)) ∈ A),
              residue A ⟨(c : (AlgebraicClosure ℚ)), hc⟩ =
                (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩) →
              ∃ hm : (⟨_, hF⟩ : ↥F₀) - algebraMap ↥k₀ ↥F₀ c ∈ W₀, (⟨_, hm⟩ : ↥W₀) ∈ maximalIdeal ↥W₀) →
    ∀ (B : Subring ↥(fieldBar q M')) (alg : Algebra ↥Ab ↥B),

        (∀ a : ↥Ab, ((@algebraMap ↥Ab ↥B _ _ alg a : ↥B) : ↥(fieldBar q M')) = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥Kb) : (AlgebraicClosure ℚ))) →

        (∀ f : ↥(fieldBar q M'), f ∈ B → ∃ hf : f ∈ F₀, (⟨f, hf⟩ : ↥F₀) ∈ W₀) →
        Prime (@algebraMap ↥Ab ↥B _ _ alg ϖb) →
        (∀ f : ↥F₀, f ∈ W₀ ↔ ∃ g h : ↥B, ¬ (@algebraMap ↥Ab ↥B _ _ alg ϖb ∣ h) ∧ (f : ↥(fieldBar q M')) * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M'))) →

        (∀ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → ∀ f : ↥(fieldBar q M'), f ∈ B → levelAutBar q M' ζ γ f ∈ B) →

        (∀ (inst : Algebra (GaloisField q 2) (ResidueField ↥A)),
          ∀ (_ : IsDomain (DrinfeldCurve.CoordRing q (ResidueField ↥A))),
          ∀ (ζ : Idx q),
          ∃ (Cs : Subgroup (rootsOfUnity (q + 1) (GaloisField q 2)))
            (ρ : ↥B →+* ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)),
            Nat.card Cs = placeWidthChar q M' (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')) ∧
            RingHom.ker ρ = Ideal.span {@algebraMap ↥Ab ↥B _ _ alg ϖb} ∧
            (∀ a : ↥Ab, ρ (@algebraMap ↥Ab ↥B _ _ alg a) =
              algebraMap (ResidueField ↥A) ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs) (IsLocalRing.residue ↥A ⟨((a : ↥Kb) : (AlgebraicClosure ℚ)), (hAb a).mp a.2⟩)) ∧
            (∀ z : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs), ∃ g h : ↥B, ρ h ≠ 0 ∧ z * ρ h = ρ g) ∧
            (∀ z : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs), z ∈ Set.range ρ ↔
              (z : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) ∈ Set.range (algebraMap (DrinfeldCurve.CoordRing q (ResidueField ↥A)) (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)))) ∧
            (∀ (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
              ∀ (hmem : (redQ q γ, (1 : (GaloisField q 2)ˣ)) ∈ DrinfeldCurve.hSubgroup q)
                (f : ↥B) (hf' : levelAutBar q M' ζ γ⁻¹ (f : ↥(fieldBar q M')) ∈ B),
                ((ρ ⟨_, hf'⟩ : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) =
                  DrinfeldCurve.hFunctionFieldAction q (ResidueField ↥A) ⟨_, hmem⟩ ((ρ f : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)))) →
    ∀ (nodes : Finset (Subring ↥F₀)),
          nodes.card = q + 1 →

          (∀ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → ∀ O ∈ nodes, ∃ O' ∈ nodes,
            ∀ (f : ↥(fieldBar q M')) (hf : f ∈ F₀) (hf' : levelAutBar q M' ζ γ f ∈ F₀), (⟨f, hf⟩ : ↥F₀) ∈ O ↔ (⟨_, hf'⟩ : ↥F₀) ∈ O') →
          (∀ (ζ : Idx q), ∀ O ∈ nodes, ∀ O' ∈ nodes, ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧
            ∀ (f : ↥(fieldBar q M')) (hf : f ∈ F₀) (hf' : levelAutBar q M' ζ γ f ∈ F₀), (⟨f, hf⟩ : ↥F₀) ∈ O ↔ (⟨_, hf'⟩ : ↥F₀) ∈ O') →

          (∀ O ∈ nodes, ∀ O' ∈ nodes, O ≠ O' → ∃ (f : ↥F₀) (hf : f ∈ O) (hf' : f ∈ O'),
            ¬ IsUnit (⟨f, hf⟩ : ↥O) ∧ IsUnit (⟨f, hf'⟩ : ↥O')) →

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
            (∃ O ∈ nodes, ∀ (f : ↥F₀) (hfO : f ∈ O), f ∈ V ∧ (¬ IsUnit (⟨f, hfO⟩ : ↥O) → ∀ hfV : f ∈ V, (⟨f, hfV⟩ : ↥V) ∈ maximalIdeal ↥V))) →
    ∀ f : ↥F₀, f ∈ W₀ ↔ (f : ↥(fieldBar q M')) ∈ O' := by
  classical
  letI algk₀F : Algebra ↥k₀ ↥(fieldBar q M') :=
    ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
  intro F₀ hSTAB W₀ hK2a hK2dvr hK2unif hK4 B alg hM1 hM2a hM2prime hM2loc hM5aut hM3 nodes hcard hEQV1 hEQV2
    hSEP hCOVER

  let V : ValuationSubring ↥F₀ := O'.comap (algebraMap ↥F₀ ↥(fieldBar q M'))
  have hV : ∀ f : ↥F₀, f ∈ V ↔ (f : ↥(fieldBar q M')) ∈ O' := fun f => ValuationSubring.mem_comap
  suffices hWV : ∀ f : ↥F₀, f ∈ W₀ ↔ f ∈ V by intro f; rw [hWV f, hV f]

  have hconst : ∀ x : ↥k₀, ((algebraMap ↥k₀ ↥F₀ x : ↥F₀) : ↥(fieldBar q M')) =
      algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (x : AlgebraicClosure ℚ) := fun _ => rfl

  have hπ₀max : (⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ∈
      maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) := by
    rw [hunif]; exact Ideal.mem_span_singleton_self _
  have hπ₀0 : (π₀ : AlgebraicClosure ℚ) ≠ 0 := by
    intro h0
    haveI := hdvr
    apply IsDiscreteValuationRing.not_a_field' (R := ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    rw [hunif, Ideal.span_singleton_eq_bot]
    exact Subtype.ext (Subtype.ext h0)
  have hπ₀invA : (π₀ : AlgebraicClosure ℚ)⁻¹ ∉ A := by
    intro h
    apply (mem_maximalIdeal _).mp hπ₀max
    refine (SSIC.isUnit_iff_ne_zero_and_inv_mem _ π₀ hπ).mpr ⟨fun h0 => hπ₀0 (by rw [h0]; rfl), ?_⟩
    show algebraMap ↥k₀ (AlgebraicClosure ℚ) π₀⁻¹ ∈ A
    rw [map_inv₀, IntermediateField.algebraMap_apply]; exact h
  have hVtop : V ≠ ⊤ := by
    intro htop
    have hmem : (algebraMap ↥k₀ ↥F₀ π₀)⁻¹ ∈ V := by rw [htop]; exact ValuationSubring.mem_top _
    rw [hV] at hmem
    apply hπ₀invA
    rw [← hO'_A, map_inv₀, ← hconst]; exact hmem

  have hVunit : ∀ (f : ↥F₀) (hfV : f ∈ V) (hfO : (f : ↥(fieldBar q M')) ∈ O'),
      IsUnit (⟨f, hfV⟩ : ↥V) ↔ IsUnit (⟨(f : ↥(fieldBar q M')), hfO⟩ : ↥O') := by
    intro f hfV hfO
    rw [SSIC.isUnit_iff_ne_zero_and_inv_mem V f hfV, SSIC.isUnit_iff_ne_zero_and_inv_mem O' _ hfO, hV]
    constructor
    · rintro ⟨h0, hinv⟩
      exact ⟨fun h => h0 (Subtype.ext (by rw [h]; rfl)), by simpa using hinv⟩
    · rintro ⟨h0, hinv⟩
      exact ⟨fun h => h0 (by rw [h]; rfl), by simpa using hinv⟩

  have hVk : ∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥F₀ x ∈ V := by
    intro x; rw [hV, hconst, hO'_A]

  have hVover : ∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
      (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ :
        ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M'))) →
      (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
        ∃ hF : (IntermediateField.inclusion hle ⟨coeffEmb (AlgebraicClosure ℚ) g,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(fieldBar q M')) ∈ F₀,
          (⟨_, hF⟩ : ↥F₀) ∈ V ∧
          ∀ (c : ↥k₀) (hc : (c : (AlgebraicClosure ℚ)) ∈ A),
            residue A ⟨(c : (AlgebraicClosure ℚ)), hc⟩ =
              (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩) →
            ∃ hm : (⟨_, hF⟩ : ↥F₀) - algebraMap ↥k₀ ↥F₀ c ∈ V, (⟨_, hm⟩ : ↥V) ∈ maximalIdeal ↥V := by
    intro g hg hgi hcusp hreg
    obtain ⟨hF, -, -⟩ := hK4 g hg hgi hcusp hreg
    obtain ⟨hgO, hover⟩ := hO'_over _ hgi hcusp hreg
    refine ⟨hF, (hV _).mpr hgO, fun c hc hres => ?_⟩
    obtain ⟨hm, hmm⟩ := hover ⟨(c : AlgebraicClosure ℚ), hc⟩ hres
    have hmV : (⟨_, hF⟩ : ↥F₀) - algebraMap ↥k₀ ↥F₀ c ∈ V := by
      rw [hV]; exact hm
    refine ⟨hmV, ?_⟩
    rw [mem_maximalIdeal, mem_nonunits_iff] at hmm ⊢
    rw [hVunit _ hmV hm]; exact hmm

  have hVfix : ∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      ∀ (f : ↥(fieldBar q M')) (hf : f ∈ F₀) (hf' : levelAutBar q M' ζ' γ f ∈ F₀),
        ((⟨f, hf⟩ : ↥F₀) ∈ V ↔ (⟨_, hf'⟩ : ↥F₀) ∈ V) := by
    intro ζ' γ hγ f hf hf'
    rw [hV, hV]
    show f ∈ O' ↔ levelAutBar q M' ζ' γ f ∈ O'
    conv_lhs => rw [← hO'_fix ζ' γ hγ]
    exact ValuationSubring.mem_comap
  have hVfixmax : ∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      ∀ (f : ↥(fieldBar q M')) (hf : f ∈ F₀) (hf' : levelAutBar q M' ζ' γ f ∈ F₀)
        (hfV : (⟨f, hf⟩ : ↥F₀) ∈ V) (hfV' : (⟨_, hf'⟩ : ↥F₀) ∈ V),
        ((⟨_, hfV⟩ : ↥V) ∈ maximalIdeal ↥V ↔ (⟨_, hfV'⟩ : ↥V) ∈ maximalIdeal ↥V) := by
    intro ζ' γ hγ f hf hf' hfV hfV'
    rw [mem_maximalIdeal, mem_nonunits_iff, mem_maximalIdeal, mem_nonunits_iff, not_iff_not,
      SSIC.isUnit_iff_ne_zero_and_inv_mem, SSIC.isUnit_iff_ne_zero_and_inv_mem]
    have hfi : f⁻¹ ∈ F₀ := inv_mem hf
    have hfi' : levelAutBar q M' ζ' γ f⁻¹ ∈ F₀ := hSTAB ζ' γ hγ _ hfi
    have key := hVfix ζ' γ hγ f⁻¹ hfi hfi'
    constructor
    · rintro ⟨h0, hinv⟩
      refine ⟨fun h => h0 (Subtype.ext ?_), ?_⟩
      · have := congrArg Subtype.val h
        simpa using this
      · have h1 : (⟨f⁻¹, hfi⟩ : ↥F₀) ∈ V := by exact hinv
        have h2 := key.mp h1
        have h3 : (⟨levelAutBar q M' ζ' γ f⁻¹, hfi'⟩ : ↥F₀) = (⟨levelAutBar q M' ζ' γ f, hf'⟩ : ↥F₀)⁻¹ :=
          Subtype.ext (by simp [map_inv₀])
        rw [h3] at h2; exact h2
    · rintro ⟨h0, hinv⟩
      refine ⟨fun h => h0 (Subtype.ext ?_), ?_⟩
      · have := congrArg Subtype.val h
        simp only [ZeroMemClass.coe_zero] at this ⊢
        rw [this, map_zero]
      · have h3 : (⟨levelAutBar q M' ζ' γ f⁻¹, hfi'⟩ : ↥F₀) = (⟨levelAutBar q M' ζ' γ f, hf'⟩ : ↥F₀)⁻¹ :=
          Subtype.ext (by simp [map_inv₀])
        have h2 : (⟨levelAutBar q M' ζ' γ f⁻¹, hfi'⟩ : ↥F₀) ∈ V := by rw [h3]; exact hinv
        have h1 := key.mpr h2
        have h4 : (⟨f⁻¹, hfi⟩ : ↥F₀) = (⟨f, hf⟩ : ↥F₀)⁻¹ := Subtype.ext (by simp)
        rw [h4] at h1; exact h1

  rcases hCOVER V hVk hVover with hBV | ⟨O, hO, hdom⟩
  swap
  ·
    exfalso
    have h2 : 1 < nodes.card := by
      rw [hcard]; have := (Fact.out : q.Prime).two_le; omega
    obtain ⟨O₂, hO₂, hne⟩ := Finset.exists_mem_ne h2 O
    obtain ⟨γ, hγ, hγO⟩ := hEQV2 ζ O₂ hO₂ O hO

    have hdom₂ : ∀ (f : ↥F₀) (hfO : f ∈ O₂), f ∈ V ∧
        (¬ IsUnit (⟨f, hfO⟩ : ↥O₂) → ∀ hfV : f ∈ V, (⟨f, hfV⟩ : ↥V) ∈ maximalIdeal ↥V) := by
      intro f hfO₂
      have hf' : levelAutBar q M' ζ γ (f : ↥(fieldBar q M')) ∈ F₀ := hSTAB ζ γ hγ _ f.2
      have hff : (⟨(f : ↥(fieldBar q M')), f.2⟩ : ↥F₀) = f := Subtype.ext rfl
      have hτfO : (⟨_, hf'⟩ : ↥F₀) ∈ O := (hγO (f : ↥(fieldBar q M')) f.2 hf').mp (by rw [hff]; exact hfO₂)
      obtain ⟨hτfV, hτfmax⟩ := hdom _ hτfO
      have hfV : f ∈ V := by rw [← hff]; exact (hVfix ζ γ hγ _ f.2 hf').mpr hτfV
      refine ⟨hfV, fun hnu hfV₁ => ?_⟩

      have hnu' : ¬ IsUnit (⟨(⟨_, hf'⟩ : ↥F₀), hτfO⟩ : ↥O) := by
        intro hu; apply hnu
        rw [SSIC.isUnit_subring_iff_ne_zero_and_inv_mem] at hu ⊢
        obtain ⟨h0, hinv⟩ := hu
        have hf0 : f ≠ 0 := by
          intro h; apply h0; apply Subtype.ext
          show levelAutBar q M' ζ γ (f : ↥(fieldBar q M')) = ((0 : ↥F₀) : ↥(fieldBar q M'))
          rw [h]; simp
        refine ⟨hf0, ?_⟩
        have hfi' : levelAutBar q M' ζ γ ((f⁻¹ : ↥F₀) : ↥(fieldBar q M')) ∈ F₀ := hSTAB ζ γ hγ _ (f⁻¹).2
        have h3 : (⟨_, hfi'⟩ : ↥F₀) = (⟨levelAutBar q M' ζ γ (f : ↥(fieldBar q M')), hf'⟩ : ↥F₀)⁻¹ :=
          Subtype.ext (by simp [map_inv₀])
        have := (hγO ((f⁻¹ : ↥F₀) : ↥(fieldBar q M')) (f⁻¹).2 hfi').mpr (by rw [h3]; exact hinv)
        have hff' : (⟨((f⁻¹ : ↥F₀) : ↥(fieldBar q M')), (f⁻¹).2⟩ : ↥F₀) = f⁻¹ := Subtype.ext rfl
        rw [hff'] at this; exact this
      have hm := hτfmax hnu' hτfV
      have hfV₂ : (⟨(f : ↥(fieldBar q M')), f.2⟩ : ↥F₀) ∈ V := by rw [hff]; exact hfV₁
      have := (hVfixmax ζ γ hγ (f : ↥(fieldBar q M')) f.2 hf' hfV₂ hτfV).mpr hm

      have heq : (⟨(⟨(f : ↥(fieldBar q M')), f.2⟩ : ↥F₀), hfV₂⟩ : ↥V) = ⟨f, hfV₁⟩ := Subtype.ext hff
      rw [heq] at this; exact this
    obtain ⟨f, hfO, hfO₂, hnuO, huO₂⟩ := hSEP O hO O₂ hO₂ (Ne.symm hne)
    obtain ⟨hfV, hfmax⟩ := hdom f hfO
    have hm := hfmax hnuO hfV
    apply (mem_maximalIdeal _).mp hm
    obtain ⟨hf0, hfinv⟩ := (SSIC.isUnit_subring_iff_ne_zero_and_inv_mem O₂ f hfO₂).mp huO₂
    exact (SSIC.isUnit_iff_ne_zero_and_inv_mem V f hfV).mpr ⟨hf0, (hdom₂ _ hfinv).1⟩

  have hBO' : ∀ b : ↥B, (b : ↥(fieldBar q M')) ∈ O' := by
    intro b
    obtain ⟨hf, h⟩ := hBV (b : ↥(fieldBar q M')) b.2
    exact (hV _).mp h

  let ιO : ↥B →+* ↥O' := B.subtype.codRestrict O' hBO'
  have hιO : ∀ b : ↥B, ιO b = ⟨(b : ↥(fieldBar q M')), hBO' b⟩ := fun _ => rfl
  let 𝔮 : Ideal ↥B := (maximalIdeal ↥O').comap ιO
  have h𝔮 : ∀ b : ↥B, b ∈ 𝔮 ↔ ¬ IsUnit (⟨(b : ↥(fieldBar q M')), hBO' b⟩ : ↥O') := by
    intro b
    show ιO b ∈ maximalIdeal ↥O' ↔ _
    rw [hιO, mem_maximalIdeal, mem_nonunits_iff]
  by_cases hgen : ∀ b : ↥B, b ∈ 𝔮 → @algebraMap ↥Ab ↥B _ _ alg ϖb ∣ b
  ·
    have hWV : ∀ f : ↥F₀, f ∈ W₀ → f ∈ V := by
      intro f hf
      obtain ⟨g, h, hndvd, hfh⟩ := (hM2loc f).mp hf
      have hhu : IsUnit (⟨(h : ↥(fieldBar q M')), hBO' h⟩ : ↥O') := by
        by_contra hnu; exact hndvd (hgen h ((h𝔮 h).mpr hnu))
      obtain ⟨hh0, hhinv⟩ := (SSIC.isUnit_iff_ne_zero_and_inv_mem O' _ (hBO' h)).mp hhu
      rw [hV]
      have : (f : ↥(fieldBar q M')) = (g : ↥(fieldBar q M')) * ((h : ↥(fieldBar q M')))⁻¹ := by
        rw [← hfh, mul_assoc, mul_inv_cancel₀ hh0, mul_one]
      rw [this]
      exact O'.mul_mem _ _ (hBO' g) hhinv
    haveI := hK2dvr
    rcases ValuationSubring.eq_or_eq_top_of_toSubring_le_of_isDiscreteValuationRing W₀ V.toSubring
        (fun f hf => hWV f hf) with h | h
    · intro f
      have := SetLike.ext_iff.mp h f
      exact ⟨fun hf => hWV f hf, fun hf => this.mp hf⟩
    · exfalso; apply hVtop
      ext f
      exact ⟨fun _ => ValuationSubring.mem_top _, fun _ => (SetLike.ext_iff.mp h f).mpr (Subring.mem_top f)⟩

  exfalso
  push Not at hgen
  obtain ⟨b₀, hb₀𝔮, hb₀⟩ := hgen

  obtain ⟨ιG⟩ := ValuationSubring.nonempty_ringHom_residueField_of_finite_of_charP q A hA (GaloisField q 2)
  letI instG : Algebra (GaloisField q 2) (ResidueField ↥A) := ιG.toAlgebra
  haveI hdomC : IsDomain (DrinfeldCurve.CoordRing q (ResidueField ↥A)) :=
    DrinfeldCurve.isDomain_coordRing_of_ne_one q (Fact.out : q.Prime).one_lt.ne' (ResidueField ↥A)
  haveI halgc : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_of_isAlgClosed A
  haveI hDed : IsDedekindDomain (DrinfeldCurve.CoordRing q (ResidueField ↥A)) :=
    DrinfeldCurve.isDedekindDomain_coordRing q (ResidueField ↥A)
  obtain ⟨Cs, ρ, -, hker, hρconst, -, hrange, hE1⟩ := hM3 instG hdomC ζ

  have hφinj : Function.Injective (algebraMap (DrinfeldCurve.CoordRing q (ResidueField ↥A))
      (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A))) := IsFractionRing.injective _ _

  have hρR : ∀ f : ↥B, ∃ r : DrinfeldCurve.CoordRing q (ResidueField ↥A),
      algebraMap _ (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) r =
        ((ρ f : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) :=
    fun f => (hrange (ρ f)).mp ⟨f, rfl⟩
  choose θf hθf using hρR
  let θ : ↥B →+* DrinfeldCurve.CoordRing q (ResidueField ↥A) :=
    { toFun := θf
      map_one' := hφinj (by rw [hθf, map_one, map_one]; rfl)
      map_mul' := fun a b => hφinj (by rw [map_mul, hθf, hθf, hθf, map_mul]; rfl)
      map_zero' := hφinj (by rw [hθf, map_zero, map_zero]; rfl)
      map_add' := fun a b => hφinj (by rw [map_add, hθf, hθf, hθf, map_add]; rfl) }
  have hθ : ∀ f : ↥B, algebraMap _ (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) (θ f) =
      ((ρ f : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) :=
    hθf
  have hθ0 : ∀ f : ↥B, θ f = 0 ↔ @algebraMap ↥Ab ↥B _ _ alg ϖb ∣ f := by
    intro f
    rw [← Ideal.mem_span_singleton, ← hker, RingHom.mem_ker]
    constructor
    · intro h
      have h1 := hθ f
      rw [h, map_zero] at h1
      exact Subtype.ext h1.symm
    · intro h
      apply hφinj
      rw [hθ, h, map_zero]; rfl
  have hθb₀ : θ b₀ ≠ 0 := fun h => hb₀ ((hθ0 b₀).mp h)

  have hθconst : ∀ c : ResidueField ↥A, ∃ f : ↥B,
      θ f = algebraMap (ResidueField ↥A) (DrinfeldCurve.CoordRing q (ResidueField ↥A)) c := by
    intro c
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
    obtain ⟨c', hc'A, hsub, hmax⟩ := hκ (a : AlgebraicClosure ℚ) a.2
    have hc'Kb : (c' : AlgebraicClosure ℚ) ∈ Kb := by
      rw [hKb, IntermediateField.mem_bot]; exact ⟨c', rfl⟩
    let a' : ↥Ab := ⟨⟨(c' : AlgebraicClosure ℚ), hc'Kb⟩, (hAb _).mpr hc'A⟩
    have hres : IsLocalRing.residue ↥A ⟨((a' : ↥Kb) : AlgebraicClosure ℚ), (hAb a').mp a'.2⟩ = IsLocalRing.residue ↥A a := by
      have h1 : a - ⟨(c' : AlgebraicClosure ℚ), hc'A⟩ = ⟨(a : AlgebraicClosure ℚ) - c', hsub⟩ := Subtype.ext rfl
      have h2 : IsLocalRing.residue ↥A (a - ⟨(c' : AlgebraicClosure ℚ), hc'A⟩) = 0 := by
        rw [h1]; exact (IsLocalRing.residue_eq_zero_iff _).mpr hmax
      rw [map_sub, sub_eq_zero] at h2
      exact h2.symm
    refine ⟨@algebraMap ↥Ab ↥B _ _ alg a', hφinj ?_⟩
    rw [hθ, hρconst a', hres, ← IsScalarTower.algebraMap_apply (ResidueField ↥A) (DrinfeldCurve.CoordRing q (ResidueField ↥A))
      (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A))]
    rfl

  have hinv_mem : ∀ r : DrinfeldCurve.CoordRing q (ResidueField ↥A),
      (∀ ζ' : ↥Cs, DrinfeldCurve.muAction q (ResidueField ↥A) (ζ' : rootsOfUnity (q + 1) (GaloisField q 2)) r = r) →
      ∃ f : ↥B, θ f = r := by
    intro r hr
    have hQ : algebraMap _ (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) r ∈
        DrinfeldCurve.quotField q (ResidueField ↥A) Cs :=
      ((DrinfeldCurve.algebraMap_mem_quotField_iff_forall_muAction_eq_and_exists_of_mem_quotField q (ResidueField ↥A) Cs).1 r).mpr hr
    obtain ⟨f, hf⟩ := (hrange ⟨_, hQ⟩).mpr ⟨r, rfl⟩
    exact ⟨f, hφinj (by rw [hθ, hf])⟩
  have hXpow : ∃ fX : ↥B, θ fX = DrinfeldCurve.x q (ResidueField ↥A) ^ (q + 1) :=
    hinv_mem _ (fun ζ' => by
      rw [map_pow, DrinfeldCurve.muAction_x, mul_pow, ← map_pow,
        DrinfeldCurve.scalarOf_pow_of_mem q (ResidueField ↥A) (ζ' : rootsOfUnity (q + 1) (GaloisField q 2)).2, map_one, one_mul])
  have hYpow : ∃ fY : ↥B, θ fY = DrinfeldCurve.y q (ResidueField ↥A) ^ (q + 1) :=
    hinv_mem _ (fun ζ' => by
      rw [map_pow, DrinfeldCurve.muAction_y, mul_pow, ← map_pow,
        DrinfeldCurve.scalarOf_pow_of_mem q (ResidueField ↥A) (ζ' : rootsOfUnity (q + 1) (GaloisField q 2)).2, map_one, one_mul])
  obtain ⟨fX, hfX⟩ := hXpow
  obtain ⟨fY, hfY⟩ := hYpow

  letI algθ : Algebra ↥B (DrinfeldCurve.CoordRing q (ResidueField ↥A)) := θ.toAlgebra
  have hθalg : ∀ f : ↥B, algebraMap ↥B (DrinfeldCurve.CoordRing q (ResidueField ↥A)) f = θ f := fun _ => rfl
  have hintX : IsIntegral ↥B (DrinfeldCurve.x q (ResidueField ↥A)) := by
    refine ⟨Polynomial.X ^ (q + 1) - Polynomial.C fX, Polynomial.monic_X_pow_sub_C fX (Nat.succ_ne_zero q), ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, hθalg, hfX, sub_self]
  have hintY : IsIntegral ↥B (DrinfeldCurve.y q (ResidueField ↥A)) := by
    refine ⟨Polynomial.X ^ (q + 1) - Polynomial.C fY, Polynomial.monic_X_pow_sub_C fY (Nat.succ_ne_zero q), ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, hθalg, hfY, sub_self]
  haveI : Algebra.IsIntegral ↥B (DrinfeldCurve.CoordRing q (ResidueField ↥A)) := by
    refine ⟨fun r => ?_⟩
    obtain ⟨p, rfl⟩ := DrinfeldCurve.mk_surjective q (ResidueField ↥A) r
    refine MvPolynomial.induction_on (motive := fun p => IsIntegral ↥B (DrinfeldCurve.mk q (ResidueField ↥A) p)) p ?_ ?_ ?_
    · intro c
      obtain ⟨f, hf⟩ := hθconst c
      have : DrinfeldCurve.mk q (ResidueField ↥A) (MvPolynomial.C c) =
          algebraMap (ResidueField ↥A) (DrinfeldCurve.CoordRing q (ResidueField ↥A)) c := by
        rw [← MvPolynomial.algebraMap_eq]; exact (DrinfeldCurve.mk q (ResidueField ↥A)).commutes c
      rw [this, ← hf, ← hθalg]; exact isIntegral_algebraMap
    · intro p₁ p₂ h₁ h₂; rw [map_add]; exact h₁.add h₂
    · intro p₁ i h₁
      rw [map_mul]
      refine h₁.mul ?_
      fin_cases i
      · exact hintX
      · exact hintY
  haveI h𝔮p : 𝔮.IsPrime := Ideal.comap_isPrime ιO (maximalIdeal ↥O')

  have hϖb𝔮 : @algebraMap ↥Ab ↥B _ _ alg ϖb ∈ 𝔮 := by
    rw [h𝔮, SSIC.isUnit_iff_ne_zero_and_inv_mem]
    rintro ⟨-, hinv⟩
    rw [hM1, ← map_inv₀, hO'_A] at hinv
    have hmem : ϖb ∈ maximalIdeal ↥Ab := by rw [hϖb]; exact Ideal.mem_span_singleton_self _
    apply (mem_maximalIdeal _).mp hmem
    have hϖ0 : ((ϖb : ↥Kb) : AlgebraicClosure ℚ) ≠ 0 := fun h => hϖb0 (Subtype.ext (Subtype.ext h))
    refine (SSIC.isUnit_iff_ne_zero_and_inv_mem Ab (ϖb : ↥Kb) ϖb.2).mpr ⟨fun h => hϖ0 (by rw [h]; rfl), ?_⟩
    rw [hAb]; push_cast; exact hinv
  have hkerle : Ideal.comap (algebraMap ↥B (DrinfeldCurve.CoordRing q (ResidueField ↥A))) ⊥ ≤ 𝔮 := by
    intro f hf
    rw [Ideal.mem_comap, Ideal.mem_bot, hθalg, hθ0] at hf
    obtain ⟨g, rfl⟩ := hf
    exact 𝔮.mul_mem_right _ hϖb𝔮
  obtain ⟨𝔐, -, h𝔐p, h𝔐c⟩ := Ideal.exists_ideal_over_prime_of_isIntegral 𝔮 ⊥ hkerle
  have hθ𝔐 : ∀ f : ↥B, f ∈ 𝔮 ↔ θ f ∈ 𝔐 := by
    intro f; rw [← h𝔐c, Ideal.mem_comap, hθalg]
  have h𝔐0 : 𝔐 ≠ ⊥ := by
    intro h0
    apply hθb₀
    have := (hθ𝔐 b₀).mp hb₀𝔮
    rw [h0, Ideal.mem_bot] at this
    exact this

  let vM : IsDedekindDomain.HeightOneSpectrum (DrinfeldCurve.CoordRing q (ResidueField ↥A)) := ⟨𝔐, h𝔐p, h𝔐0⟩
  let w : Place (ResidueField ↥A) (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) :=
    AlgebraicCurve.Place.ofHeightOneSpectrum (K := ResidueField ↥A) vM
  have hw : w.toValuationSubring = (vM.valuation (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A))).valuationSubring := rfl
  have hRw : ∀ r : DrinfeldCurve.CoordRing q (ResidueField ↥A),
      algebraMap _ (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) r ∈ w.toValuationSubring := by
    intro r
    rw [hw, Valuation.mem_valuationSubring_iff]
    exact vM.valuation_le_one r

  have hnu𝔐 : ∀ r : DrinfeldCurve.CoordRing q (ResidueField ↥A),
      algebraMap _ (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) r ∈ w.toValuationSubring.nonunits → r ∈ 𝔐 := by
    intro r hr
    by_contra hrM
    have hr' := (ValuationSubring.coe_mem_nonunits_iff (a := ⟨_, hRw r⟩)).mp hr
    apply (mem_maximalIdeal _).mp hr'
    have hv1 : vM.intValuation r = 1 := by
      rcases (vM.intValuation_le_one r).lt_or_eq with h | h
      · exact absurd ((vM.intValuation_lt_one_iff_mem r).mp h) hrM
      · exact h
    have hr0 : r ≠ 0 := by rintro rfl; exact hrM 𝔐.zero_mem
    refine (SSIC.isUnit_iff_ne_zero_and_inv_mem _ _ (hRw r)).mpr ⟨(map_ne_zero_iff _ hφinj).mpr hr0, ?_⟩
    rw [hw, Valuation.mem_valuationSubring_iff, map_inv₀, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, hv1, inv_one]
  obtain ⟨a, b, hab, hXa, hYb⟩ := (DrinfeldCurve.affinePlaces_census q (ResidueField ↥A)).2 w (hRw _) (hRw _)
  have hxa : DrinfeldCurve.x q (ResidueField ↥A) - algebraMap (ResidueField ↥A) _ a ∈ 𝔐 := by
    apply hnu𝔐
    rw [map_sub, ← IsScalarTower.algebraMap_apply]; exact hXa
  have hyb : DrinfeldCurve.y q (ResidueField ↥A) - algebraMap (ResidueField ↥A) _ b ∈ 𝔐 := by
    apply hnu𝔐
    rw [map_sub, ← IsScalarTower.algebraMap_apply]; exact hYb

  have h𝔮τ : ∀ (γ' : SL(2, ℤ)) (hγ' : γ' ∈ Gamma0 M') (f : ↥B)
      (hf' : levelAutBar q M' ζ γ' (f : ↥(fieldBar q M')) ∈ B), f ∈ 𝔮 → (⟨_, hf'⟩ : ↥B) ∈ 𝔮 := by
    intro γ' hγ' f hf' hf
    rw [h𝔮] at hf ⊢
    intro hu; apply hf
    rw [SSIC.isUnit_iff_ne_zero_and_inv_mem] at hu ⊢
    obtain ⟨h0, hinv⟩ := hu
    refine ⟨fun h => h0 (by show levelAutBar q M' ζ γ' (f : ↥(fieldBar q M')) = 0; rw [h, map_zero]), ?_⟩
    have := (hO'_fix ζ γ' hγ').symm ▸ hinv
    rw [← map_inv₀] at hinv
    have h2 : ((f : ↥(fieldBar q M')))⁻¹ ∈ O'.comap (levelAutBar q M' ζ γ').toAlgHom.toRingHom :=
      ValuationSubring.mem_comap.mpr hinv
    rw [hO'_fix ζ γ' hγ'] at h2; exact h2
  have hT : ∀ n : ℕ, ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ (γ : Matrix (Fin 2) (Fin 2) ℤ) = !![1, (n : ℤ); 0, 1] := fun n =>
    ⟨⟨!![1, (n : ℤ); 0, 1], by simp [Matrix.det_fin_two_of]⟩, by simp [CongruenceSubgroup.Gamma0_mem], rfl⟩
  have hstep : ∀ n : ℕ, ((n : ResidueField ↥A) * a + b) ^ (q + 1) = b ^ (q + 1) := by
    intro n
    obtain ⟨γ, hγ, hγmat⟩ := hT n
    let g : Matrix.SpecialLinearGroup (Fin 2) (ZMod q) := Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)) γ
    have hg01 : (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 1 = (n : ZMod q) := by simp [g, hγmat]
    have hg11 : (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 1 = 1 := by simp [g, hγmat]
    have hmem : (redQ q γ, (1 : (GaloisField q 2)ˣ)) ∈ DrinfeldCurve.hSubgroup q := DrinfeldCurve.toGL_one_mem_hSubgroup q g
    have hEl : DrinfeldCurve.hFunctionFieldAction q (ResidueField ↥A) ⟨_, hmem⟩ =
        IsFractionRing.algEquivOfAlgEquiv (DrinfeldCurve.slAction q (ResidueField ↥A) g) :=
      DrinfeldCurve.hFunctionFieldAction_sl q (ResidueField ↥A) g

    have hσ𝔐 : ∀ f : ↥B, f ∈ 𝔮 → DrinfeldCurve.slAction q (ResidueField ↥A) g (θ f) ∈ 𝔐 := by
      intro f hf
      have hf' : levelAutBar q M' ζ γ⁻¹ (f : ↥(fieldBar q M')) ∈ B := hM5aut ζ γ⁻¹ (inv_mem hγ) _ f.2
      have hf'𝔮 : (⟨_, hf'⟩ : ↥B) ∈ 𝔮 := h𝔮τ γ⁻¹ (inv_mem hγ) f hf' hf
      have key := hE1 γ hγ hmem f hf'
      rw [hEl, ← hθ, ← hθ, IsFractionRing.algEquivOfAlgEquiv_algebraMap] at key
      rw [← hφinj key]
      exact (hθ𝔐 _).mp hf'𝔮
    obtain ⟨fb, hfb⟩ := hθconst (b ^ (q + 1))
    have hfN : fY - fb ∈ 𝔮 := by
      rw [hθ𝔐, map_sub, hfY, hfb, map_pow]
      obtain ⟨d, hd⟩ := sub_dvd_pow_sub_pow (DrinfeldCurve.y q (ResidueField ↥A)) (algebraMap (ResidueField ↥A) _ b) (q + 1)
      rw [hd]; exact 𝔐.mul_mem_right _ hyb
    have h1 := hσ𝔐 _ hfN
    simp only [map_sub, map_pow, hfY, hfb, DrinfeldCurve.slAction_y, AlgEquiv.commutes, hg01, hg11, map_one, one_mul,
      map_natCast] at h1

    have h2 : (n : DrinfeldCurve.CoordRing q (ResidueField ↥A)) * DrinfeldCurve.x q (ResidueField ↥A) + DrinfeldCurve.y q (ResidueField ↥A)
        - algebraMap (ResidueField ↥A) _ ((n : ResidueField ↥A) * a + b) ∈ 𝔐 := by
      have : (n : DrinfeldCurve.CoordRing q (ResidueField ↥A)) * DrinfeldCurve.x q (ResidueField ↥A) + DrinfeldCurve.y q (ResidueField ↥A)
          - algebraMap (ResidueField ↥A) _ ((n : ResidueField ↥A) * a + b) =
          (n : DrinfeldCurve.CoordRing q (ResidueField ↥A)) * (DrinfeldCurve.x q (ResidueField ↥A) - algebraMap (ResidueField ↥A) _ a) +
            (DrinfeldCurve.y q (ResidueField ↥A) - algebraMap (ResidueField ↥A) _ b) := by
        rw [map_add, map_mul, map_natCast]; ring
      rw [this]; exact 𝔐.add_mem (𝔐.mul_mem_left _ hxa) hyb
    obtain ⟨d, hd⟩ := sub_dvd_pow_sub_pow ((n : DrinfeldCurve.CoordRing q (ResidueField ↥A)) * DrinfeldCurve.x q (ResidueField ↥A) +
      DrinfeldCurve.y q (ResidueField ↥A)) (algebraMap (ResidueField ↥A) _ ((n : ResidueField ↥A) * a + b)) (q + 1)
    have h3 : ((n : DrinfeldCurve.CoordRing q (ResidueField ↥A)) * DrinfeldCurve.x q (ResidueField ↥A) + DrinfeldCurve.y q (ResidueField ↥A)) ^ (q + 1)
        - algebraMap (ResidueField ↥A) _ (((n : ResidueField ↥A) * a + b) ^ (q + 1)) ∈ 𝔐 := by
      rw [map_pow, hd]; exact 𝔐.mul_mem_right _ h2
    have h4 : algebraMap (ResidueField ↥A) (DrinfeldCurve.CoordRing q (ResidueField ↥A))
        (((n : ResidueField ↥A) * a + b) ^ (q + 1) - b ^ (q + 1)) ∈ 𝔐 := by
      have := 𝔐.sub_mem h1 h3
      convert this using 1
      simp only [map_sub, map_pow, map_add, map_mul, map_natCast]
      ring
    by_contra hne
    exact h𝔐p.ne_top (Ideal.eq_top_of_isUnit_mem 𝔐 h4 ((IsUnit.mk0 _ (sub_ne_zero.mpr hne)).map _))

  haveI : CharP (ResidueField ↥A) q := charP_of_injective_algebraMap (algebraMap (GaloisField q 2) (ResidueField ↥A)).injective q
  have frob : ∀ n : ℕ, ((n : ResidueField ↥A) * a + b) ^ (q + 1) =
      (n : ResidueField ↥A) ^ 2 * a ^ (q + 1) + (n : ResidueField ↥A) * (a ^ q * b + a * b ^ q) + b ^ (q + 1) := by
    intro n
    have hn : ((n : ResidueField ↥A)) ^ q = n := by
      have := DrinfeldCurve.ofZMod_pow_card q (ResidueField ↥A) (n : ZMod q)
      rwa [map_natCast] at this
    rw [pow_succ, add_pow_char ((n : ResidueField ↥A) * a) b q, mul_pow, hn, pow_succ, pow_succ]
    ring

  have hXYinv : ∃ fXY : ↥B, θ fXY = DrinfeldCurve.x q (ResidueField ↥A) ^ q * DrinfeldCurve.y q (ResidueField ↥A) :=
    hinv_mem _ (fun ζ' => by
      rw [map_mul, map_pow, DrinfeldCurve.muAction_x, DrinfeldCurve.muAction_y, mul_pow, mul_mul_mul_comm, ← pow_succ, ← map_pow,
        DrinfeldCurve.scalarOf_pow_of_mem q (ResidueField ↥A) (ζ' : rootsOfUnity (q + 1) (GaloisField q 2)).2, map_one, one_mul])
  obtain ⟨fXY, hfXY⟩ := hXYinv
  have hstepXY : a ^ q * (a + b) = a ^ q * b := by
    obtain ⟨γ, hγ, hγmat⟩ := hT 1
    let g : Matrix.SpecialLinearGroup (Fin 2) (ZMod q) := Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)) γ
    have hg00 : (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0 = 1 := by simp [g, hγmat]
    have hg10 : (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 = 0 := by simp [g, hγmat]
    have hg01 : (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 1 = 1 := by simp [g, hγmat]
    have hg11 : (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 1 = 1 := by simp [g, hγmat]
    have hmem : (redQ q γ, (1 : (GaloisField q 2)ˣ)) ∈ DrinfeldCurve.hSubgroup q := DrinfeldCurve.toGL_one_mem_hSubgroup q g
    have hEl : DrinfeldCurve.hFunctionFieldAction q (ResidueField ↥A) ⟨_, hmem⟩ =
        IsFractionRing.algEquivOfAlgEquiv (DrinfeldCurve.slAction q (ResidueField ↥A) g) :=
      DrinfeldCurve.hFunctionFieldAction_sl q (ResidueField ↥A) g
    have hσ𝔐 : ∀ f : ↥B, f ∈ 𝔮 → DrinfeldCurve.slAction q (ResidueField ↥A) g (θ f) ∈ 𝔐 := by
      intro f hf
      have hf' : levelAutBar q M' ζ γ⁻¹ (f : ↥(fieldBar q M')) ∈ B := hM5aut ζ γ⁻¹ (inv_mem hγ) _ f.2
      have hf'𝔮 : (⟨_, hf'⟩ : ↥B) ∈ 𝔮 := h𝔮τ γ⁻¹ (inv_mem hγ) f hf' hf
      have key := hE1 γ hγ hmem f hf'
      rw [hEl, ← hθ, ← hθ, IsFractionRing.algEquivOfAlgEquiv_algebraMap] at key
      rw [← hφinj key]
      exact (hθ𝔐 _).mp hf'𝔮
    obtain ⟨fc, hfc⟩ := hθconst (a ^ q * b)
    have hfN : fXY - fc ∈ 𝔮 := by
      rw [hθ𝔐, map_sub, hfXY, hfc]
      have hrw : DrinfeldCurve.x q (ResidueField ↥A) ^ q * DrinfeldCurve.y q (ResidueField ↥A) - algebraMap (ResidueField ↥A) (DrinfeldCurve.CoordRing q (ResidueField ↥A)) (a ^ q * b) =
          DrinfeldCurve.x q (ResidueField ↥A) ^ q * (DrinfeldCurve.y q (ResidueField ↥A) - algebraMap (ResidueField ↥A) (DrinfeldCurve.CoordRing q (ResidueField ↥A)) b) + (DrinfeldCurve.x q (ResidueField ↥A) ^ q - (algebraMap (ResidueField ↥A) (DrinfeldCurve.CoordRing q (ResidueField ↥A)) a) ^ q) * algebraMap (ResidueField ↥A) (DrinfeldCurve.CoordRing q (ResidueField ↥A)) b := by
        rw [map_mul, map_pow]; ring
      rw [hrw]
      obtain ⟨d, hd⟩ := sub_dvd_pow_sub_pow (DrinfeldCurve.x q (ResidueField ↥A)) (algebraMap (ResidueField ↥A) (DrinfeldCurve.CoordRing q (ResidueField ↥A)) a) q
      rw [hd]
      exact 𝔐.add_mem (𝔐.mul_mem_left _ hyb) (𝔐.mul_mem_right _ (𝔐.mul_mem_right _ hxa))
    have h1 := hσ𝔐 _ hfN
    simp only [map_sub, map_mul, map_pow, map_add, hfXY, hfc, DrinfeldCurve.slAction_x, DrinfeldCurve.slAction_y, AlgEquiv.commutes,
      hg00, hg10, hg01, hg11, map_one, map_zero, one_mul, zero_mul, add_zero] at h1

    have h2 : DrinfeldCurve.x q (ResidueField ↥A) ^ q * (DrinfeldCurve.x q (ResidueField ↥A) + DrinfeldCurve.y q (ResidueField ↥A)) - algebraMap (ResidueField ↥A) (DrinfeldCurve.CoordRing q (ResidueField ↥A)) (a ^ q * (a + b)) ∈ 𝔐 := by
      have hrw : DrinfeldCurve.x q (ResidueField ↥A) ^ q * (DrinfeldCurve.x q (ResidueField ↥A) + DrinfeldCurve.y q (ResidueField ↥A)) - algebraMap (ResidueField ↥A) (DrinfeldCurve.CoordRing q (ResidueField ↥A)) (a ^ q * (a + b)) =
          (DrinfeldCurve.x q (ResidueField ↥A) ^ q - (algebraMap (ResidueField ↥A) (DrinfeldCurve.CoordRing q (ResidueField ↥A)) a) ^ q) * (DrinfeldCurve.x q (ResidueField ↥A) + DrinfeldCurve.y q (ResidueField ↥A)) +
            (algebraMap (ResidueField ↥A) (DrinfeldCurve.CoordRing q (ResidueField ↥A)) a) ^ q * ((DrinfeldCurve.x q (ResidueField ↥A) - algebraMap (ResidueField ↥A) (DrinfeldCurve.CoordRing q (ResidueField ↥A)) a) + (DrinfeldCurve.y q (ResidueField ↥A) - algebraMap (ResidueField ↥A) (DrinfeldCurve.CoordRing q (ResidueField ↥A)) b)) := by
        rw [map_mul, map_pow, map_add]; ring
      rw [hrw]
      obtain ⟨d, hd⟩ := sub_dvd_pow_sub_pow (DrinfeldCurve.x q (ResidueField ↥A)) (algebraMap (ResidueField ↥A) (DrinfeldCurve.CoordRing q (ResidueField ↥A)) a) q
      rw [hd]
      exact 𝔐.add_mem (𝔐.mul_mem_right _ (𝔐.mul_mem_right _ hxa)) (𝔐.mul_mem_left _ (𝔐.add_mem hxa hyb))
    have h4 : algebraMap (ResidueField ↥A) (DrinfeldCurve.CoordRing q (ResidueField ↥A)) (a ^ q * (a + b) - a ^ q * b) ∈ 𝔐 := by
      have := 𝔐.sub_mem h1 h2
      convert this using 1
      simp only [map_sub, map_pow, map_add, map_mul]
      ring
    by_contra hne
    exact h𝔐p.ne_top (Ideal.eq_top_of_isUnit_mem 𝔐 h4 ((IsUnit.mk0 _ (sub_ne_zero.mpr hne)).map _))
  have ha0 : a = 0 := by
    have hpow : a ^ (q + 1) = 0 := by rw [pow_succ]; linear_combination hstepXY
    exact pow_eq_zero_iff (Nat.succ_ne_zero q) |>.mp hpow
  rw [ha0, zero_mul, zero_pow (Fact.out : q.Prime).ne_zero, zero_mul, sub_zero] at hab
  exact zero_ne_one hab

end S_ModularCurve_FullLevel_mem_iff_coe_mem_drinfeldRing_of_affineChart_nodes_cover_of_eq_two_of_dvd
end P2MW
export P2MW.S_ModularCurve_FullLevel_mem_iff_coe_mem_drinfeldRing_of_affineChart_nodes_cover_of_eq_two_of_dvd (solution)
