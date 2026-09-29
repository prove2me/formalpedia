-- Prove2me | solution 1 for ModularCurve.FullLevel.klevel_supersingularDVR_baseSmoothPointStalks_of_affineChart_chart
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/a41721b8-38dd-5f05-ba4c-25207b0ad35c

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Theorems.Thm_ModularCurve_FullLevel_supersingularProlongation_residue_surjective_ker_of_affineChart
import Theorems.Thm_RingHom_exists_algEquiv_comp_eq_of_ker_eq_of_forall_exists_mul_eq
import Theorems.Thm_ModularCurve_FullLevel_supersingularProlongation_ends_of_affineChart
import Theorems.Thm_ModularCurve_FullLevel_supersingularProlongation_smoothPointStalk_of_affineChart
import Theorems.Thm_ModularCurve_FullLevel_supersingularProlongation_discRiders_of_affineChart
import Theorems.Thm_DrinfeldCurve_isDomain_coordRing_of_ne_one
import Theorems.Thm_ModularCurve_FullLevel_supersingularProlongation_existDL_of_affineChart
import Theorems.Thm_DrinfeldCurve_exists_muAction_eq_and_algebraMap_eq_of_mem_quotField_of_forall_place
import Theorems.Thm_DrinfeldCurve_coe_algEquiv_mem_range_algebraMap_of_forall_place_quotField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_klevel_supersingularDVR_baseSmoothPointStalks_of_affineChart_chart
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 16000000

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem KL5.exists_mem_chart_residue_eq_of_forall_not_mem_ends
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (inst : Algebra (GaloisField q 2) (ResidueField ↥A)) (hdomC : IsDomain (DrinfeldCurve.CoordRing q (ResidueField ↥A)))
    (halgc : IsAlgClosed (ResidueField ↥A))
    (B : Subring ↥(fieldBar q M'))
    (FSS : Type) [Field FSS] [Algebra (ResidueField ↥A) FSS] (R : RegularProlongation A ↥(fieldBar q M') FSS)
    (hBR : ∀ f : ↥(fieldBar q M'), f ∈ B → f ∈ R.integers)
    (Cs : Subgroup (rootsOfUnity (q + 1) (GaloisField q 2)))
    (ρ : ↥B →+* ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs))
    (hρrange : ∀ z : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs), z ∈ Set.range ρ ↔
      (z : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) ∈ Set.range (algebraMap (DrinfeldCurve.CoordRing q (ResidueField ↥A)) (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A))))
    (e : FSS ≃ₐ[(ResidueField ↥A)] ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) (he : ∀ b : ↥B, e (R.residue ⟨((b : ↥B) : ↥(fieldBar q M')), hBR _ (b).2⟩) = ρ b)
    (N : Finset (Place (ResidueField ↥A) FSS))
    (hNiff : ∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N ↔ ∀ b : ↥B, R.residue ⟨((b : ↥B) : ↥(fieldBar q M')), hBR _ (b).2⟩ ∈ Q.toValuationSubring) :
    ∀ z : FSS, (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N → z ∈ Q.toValuationSubring) →
      ∃ (f : ↥(fieldBar q M')) (_ : f ∈ B) (hfR : f ∈ R.integers), R.residue ⟨f, hfR⟩ = z := by
  intro z hz

  have key := DrinfeldCurve.coe_algEquiv_mem_range_algebraMap_of_forall_place_quotField q (ResidueField ↥A) Cs FSS e z (by
    intro Q hQ
    apply hz Q
    rw [hNiff]
    intro b
    obtain ⟨c, hc⟩ := (hρrange (ρ b)).mp ⟨b, rfl⟩
    have hmem := hQ c (ρ b) hc.symm
    rwa [← he b, AlgEquiv.symm_apply_apply] at hmem)

  obtain ⟨b, hb⟩ := (hρrange (e z)).mpr key
  refine ⟨((b : ↥B) : ↥(fieldBar q M')), b.2, hBR _ b.2, ?_⟩
  apply e.injective
  rw [he b, hb]

namespace EndsStalksReduce

theorem glue_resSurj (A : ValuationSubring (AlgebraicClosure ℚ)) (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A)
    (K' : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (A' : ValuationSubring ↥K')
    (hA' : ∀ x : ↥K', x ∈ A' ↔ (x : AlgebraicClosure ℚ) ∈ A) :
    Function.Surjective (fun a : ↥A' => IsLocalRing.residue ↥A ⟨((a : ↥K') : AlgebraicClosure ℚ), (hA' a).mp a.2⟩) := by
  intro r
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
  obtain ⟨c, hcA, hsub, hm⟩ := hκ a a.2
  refine ⟨⟨⟨(c : AlgebraicClosure ℚ), K'.algebraMap_mem c⟩, (hA' _).mpr hcA⟩, ?_⟩
  change IsLocalRing.residue ↥A ⟨(c : AlgebraicClosure ℚ), hcA⟩ = IsLocalRing.residue ↥A a
  rw [eq_comm, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  exact hm

end EndsStalksReduce

open EndsStalksReduce in
theorem EBS2
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (s : ↥W)
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
      Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A)
    (halgc : IsAlgClosed (ResidueField ↥A))
    (inst : Algebra (GaloisField q 2) (ResidueField ↥A)) (hdomC : IsDomain (DrinfeldCurve.CoordRing q (ResidueField ↥A))) (ζix : Idx q)

    (Kb : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (hKb : Kb = ⊥) (Ab : ValuationSubring ↥Kb) (hAb : ∀ x : ↥Kb, x ∈ Ab ↔ (x : (AlgebraicClosure ℚ)) ∈ A)
    (hdvrb : IsDiscreteValuationRing ↥Ab) (hhensb : HenselianLocalRing ↥Ab)
    (ϖb : ↥Ab) (hϖb : maximalIdeal ↥Ab = Ideal.span {ϖb}) (hϖb0 : ϖb ≠ 0) :
    letI : Algebra ↥k₀ ↥(fieldBar q M') :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
    ∀ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M')) (W₀ : ValuationSubring ↥F₀),
      (IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) ⊔ F₀ = ⊤) → (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥F₀ x ∈ W₀) → IsDiscreteValuationRing ↥W₀ →
      (∃ hπW : algebraMap ↥k₀ ↥F₀ π₀ ∈ W₀, maximalIdeal ↥W₀ = Ideal.span {(⟨_, hπW⟩ : ↥W₀)}) →
      (∀ (K' : IntermediateField ↥k₀ (AlgebraicClosure ℚ)), FiniteDimensional ↥k₀ ↥K' →
        ∀ (m : ℕ) (c : Fin m → (AlgebraicClosure ℚ)) (a : Fin m → ↥(fieldBar q M')), (∀ i, a i ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K' : Set (AlgebraicClosure ℚ))) ⊔ F₀) →
          LinearIndependent ↥K' c → ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c i) * a i = 0 → ∀ i, a i = 0) →
      ∀ (B : Subring ↥(fieldBar q M')) (alg : Algebra ↥Ab ↥B),
        (∀ a : ↥Ab, ((@algebraMap ↥Ab ↥B _ _ alg a : ↥B) : ↥(fieldBar q M')) = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥Kb) : (AlgebraicClosure ℚ))) → (∀ f : ↥(fieldBar q M'), f ∈ B → f ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑Kb : Set (AlgebraicClosure ℚ))) ⊔ F₀) →
        (∀ f : ↥(fieldBar q M'), f ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑Kb : Set (AlgebraicClosure ℚ))) ⊔ F₀ → ∃ g h : ↥B, (h : ↥(fieldBar q M')) ≠ 0 ∧ f * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M'))) →
        @Algebra.FormallySmooth ↥Ab ↥B _ _ alg → @Algebra.FinitePresentation ↥Ab ↥B _ _ alg →
        Ring.KrullDimLE 1 (↥B ⧸ Ideal.span {@algebraMap ↥Ab ↥B _ _ alg ϖb}) →
        (∀ f : ↥(fieldBar q M'), f ∈ B → ∃ hf : f ∈ F₀, (⟨f, hf⟩ : ↥F₀) ∈ W₀) → Prime (@algebraMap ↥Ab ↥B _ _ alg ϖb) →
        (∀ f : ↥F₀, f ∈ W₀ ↔ ∃ g h : ↥B, ¬ (@algebraMap ↥Ab ↥B _ _ alg ϖb ∣ h) ∧ (f : ↥(fieldBar q M')) * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M'))) →
        ((IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                ↥(modularFunctionFieldBar M')) : fieldBar q M') ∈ B) →
        (∀ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → ∀ f : ↥(fieldBar q M'), f ∈ B → levelAutBar q M' ζ γ f ∈ B) →
        (∀ (inst : Algebra (GaloisField q 2) (ResidueField ↥A)),
          ∀ (_ : IsDomain (DrinfeldCurve.CoordRing q (ResidueField ↥A))),
          ∀ (ζ : Idx q),
          ∃ (Cs : Subgroup (rootsOfUnity (q + 1) (GaloisField q 2)))
            (ρ : ↥B →+* ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)),
            Nat.card Cs = 2 * placeWidthChar q M' (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')) ∧
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
      ∀ (FSS : Type) [Field FSS] [Algebra (ResidueField ↥A) FSS] (R : RegularProlongation A ↥(fieldBar q M') FSS),
        (∀ f : ↥F₀, ((f : ↥(fieldBar q M')) ∈ R.integers ↔ f ∈ W₀)) →
        ∃ (N : Finset (Place (ResidueField ↥A) FSS))
          (Sb : Place (ResidueField ↥A) FSS → Subring ↥(fieldBar q M'))
          (φb : (Q : Place (ResidueField ↥A) FSS) → (Polynomial ↥Ab →+* ↥(Sb Q)))
          (χb : (Q : Place (ResidueField ↥A) FSS) → (↥(Sb Q) →+* ResidueField ↥A))
          (Db : Place (ResidueField ↥A) FSS → Set (Place (AlgebraicClosure ℚ) ↥(fieldBar q M'))),
          N.card = q + 1 ∧

          (∃ B : Subring ↥(fieldBar q M'),
            (∀ f : ↥(fieldBar q M'), f ∈ B → f ∈ R.integers) ∧
            (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N → ∀ f : ↥(fieldBar q M'), f ∈ B → f ∈ Sb Q) ∧
            (∀ z : FSS, (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N → z ∈ Q.toValuationSubring) →
              ∃ (f : ↥(fieldBar q M')) (_ : f ∈ B) (hfR : f ∈ R.integers), R.residue ⟨f, hfR⟩ = z)) ∧
          (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N →

            (
              (∀ a : ↥Ab, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥Kb) : (AlgebraicClosure ℚ)) ∈ Sb Q) ∧

              (∀ a : ↥Ab, ((φb Q (Polynomial.C a) : ↥(Sb Q)) : ↥(fieldBar q M')) = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥Kb) : (AlgebraicClosure ℚ))) ∧
              (∀ a : ↥Ab, χb Q (φb Q (Polynomial.C a)) = IsLocalRing.residue ↥A ⟨((a : ↥Kb) : (AlgebraicClosure ℚ)), (hAb a).mp a.2⟩) ∧
              χb Q (φb Q Polynomial.X) = 0 ∧

              (∃ _ : IsLocalRing ↥(Sb Q), RingHom.ker (χb Q) = maximalIdeal ↥(Sb Q)) ∧

              (∀ f : ↥(fieldBar q M'), f ∈ Sb Q → f ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑Kb : Set (AlgebraicClosure ℚ))) ⊔ F₀) ∧
              (∀ f : ↥(fieldBar q M'), f ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑Kb : Set (AlgebraicClosure ℚ))) ⊔ F₀ → ∃ g h : ↥(Sb Q), (h : ↥(fieldBar q M')) ≠ 0 ∧ f * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M'))) ∧

              (φb Q).FormallySmooth ∧ (φb Q).FormallyUnramified ∧ (φb Q).EssFiniteType ∧

              (∃ hSR : ∀ f : ↥(Sb Q), (f : ↥(fieldBar q M')) ∈ R.integers,
                ∀ f : ↥(Sb Q), (⟨(f : ↥(fieldBar q M')), hSR f⟩ : ↥R.integers) ∈ maximalIdeal ↥R.integers ↔ φb Q (Polynomial.C ϖb) ∣ f) ∧

              (∀ f : ↥(Sb Q), ∃ hR : (f : ↥(fieldBar q M')) ∈ R.integers, ∃ hm : R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ Q.toValuationSubring,
                IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : ↥(fieldBar q M')), hR⟩, hm⟩ =
                  algebraMap (ResidueField ↥A) Q.ResidueField (χb Q f)) ∧

              (∃ hR : ((φb Q Polynomial.X : ↥(Sb Q)) : ↥(fieldBar q M')) ∈ R.integers,
                Q.ord (R.residue ⟨((φb Q Polynomial.X : ↥(Sb Q)) : ↥(fieldBar q M')), hR⟩) = 1) ∧

              (∀ P, P ∈ Db Q ↔ (P.IsRational ∧
                (∀ f : ↥(Sb Q), (f : ↥(fieldBar q M')) ∈ P.toValuationSubring ∧ P.evalAt (f : ↥(fieldBar q M')) ∈ A) ∧
                (∀ f : ↥(Sb Q), A.valuation (P.evalAt (f : ↥(fieldBar q M'))) < 1 ↔ χb Q f = 0))) )) ∧

          (∀ Q Q' : Place (ResidueField ↥A) FSS, Q ∉ N → Q' ∉ N → ∀ (P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M')), P ∈ Db Q → P ∈ Db Q' → Q = Q') ∧

          (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N → ∀ P ∈ Db Q,
            0 ≤ P.ord (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                ↥(modularFunctionFieldBar M')) : fieldBar q M')) ∧

          (∀ τ ∈ Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
              ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ},
            ∀ (hτ : ∀ f : ↥(fieldBar q M'), τ f ∈ R.integers ↔ f ∈ R.integers) (Q : Place (ResidueField ↥A) FSS),
              (R.resAut τ hτ • Q ∈ N ↔ Q ∈ N) ∧
              (Q ∉ N → AlgebraicCurve.RegularProlongation.smulDisc τ (Db Q) = Db (R.resAut τ hτ • Q))) := by
  letI instAlg : Algebra ↥k₀ ↥(fieldBar q M') :=
    ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
  intro F₀ W₀ h1 h2a h2b h2c hLD B alg hM1 hM0a hM0b hM4a hM4b hM4c hM2a hM2b hM2c hM5a hM5b hM3 FSS _ _ R hRW
  obtain ⟨Cs, ρ, hCs, hker, hρC, hρfrac, hρrange, hρE1⟩ := hM3 inst hdomC ζix
  have hBR : ∀ f : ↥(fieldBar q M'), f ∈ B → f ∈ R.integers := fun f hf => by
    obtain ⟨hf0, hw⟩ := hM2a f hf
    exact (hRW ⟨f, hf0⟩).mpr hw
  obtain ⟨hfracR, hkerR⟩ := ModularCurve.FullLevel.supersingularProlongation_residue_surjective_ker_of_affineChart q hq M' hqM' A hA W hW hle s k₀ π₀ hπ hdvr hunif hhens hres hκ
    Kb hKb Ab hAb hdvrb hhensb ϖb hϖb hϖb0 F₀ W₀ h1 h2a h2b h2c B alg hM1 hM2a hM2c FSS R hRW hBR
  let red : ↥B →+* FSS := R.residue.comp (B.subtype.codRestrict R.integers (fun b => hBR _ b.2))
  have hred : ∀ b : ↥B, red b = R.residue ⟨((b : ↥B) : ↥(fieldBar q M')), hBR _ b.2⟩ := fun b => rfl
  have hfracR' : ∀ x : FSS, ∃ g h : ↥B, red h ≠ 0 ∧ x * red h = red g := hfracR
  have hkerEq : RingHom.ker red = RingHom.ker ρ := by
    ext b
    rw [RingHom.mem_ker, hred, hkerR, hker, Ideal.mem_span_singleton]
  have hκb := glue_resSurj A k₀ hκ Kb Ab hAb
  have hc1 : ∀ a : ↥Ab, red (@algebraMap ↥Ab ↥B _ _ alg a) =
      algebraMap (ResidueField ↥A) FSS (IsLocalRing.residue ↥A ⟨((a : ↥Kb) : (AlgebraicClosure ℚ)), (hAb a).mp a.2⟩) := by
    intro a
    rw [hred]
    have hmem : algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥Kb) : (AlgebraicClosure ℚ)) ∈ R.integers := (R.algebraMap_mem_iff _).mpr ((hAb a).mp a.2)
    have : (⟨((@algebraMap ↥Ab ↥B _ _ alg a : ↥B) : ↥(fieldBar q M')), hBR _ (@algebraMap ↥Ab ↥B _ _ alg a).2⟩ : ↥R.integers) =
        ⟨algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥Kb) : (AlgebraicClosure ℚ)), hmem⟩ := Subtype.ext (hM1 a)
    rw [this]
    exact R.residue_algebraMap ⟨((a : ↥Kb) : (AlgebraicClosure ℚ)), (hAb a).mp a.2⟩
  obtain ⟨e, he⟩ := RingHom.exists_algEquiv_comp_eq_of_ker_eq_of_forall_exists_mul_eq red ρ hkerEq hfracR' hρfrac
    (@algebraMap ↥Ab ↥B _ _ alg) (fun a : ↥Ab => IsLocalRing.residue ↥A ⟨((a : ↥Kb) : (AlgebraicClosure ℚ)), (hAb a).mp a.2⟩) hκb hc1 hρC
  have he' : ∀ b : ↥B, e (R.residue ⟨((b : ↥B) : ↥(fieldBar q M')), hBR _ (b).2⟩) = ρ b := he
  obtain ⟨N, hcard, hNiff, hNeqv⟩ := ModularCurve.FullLevel.supersingularProlongation_ends_of_affineChart q hq M' hqM' A hA W hW hle s k₀ Kb Ab hAb ϖb inst hdomC B alg hM5b
    FSS R hBR Cs ρ hρrange e he'

  have tot : ∀ Q : Place (ResidueField ↥A) FSS, ∃ (S : Subring ↥(fieldBar q M')) (φ : Polynomial ↥Ab →+* ↥S) (χ : ↥S →+* ResidueField ↥A),
      Q ∉ N →

        (∀ a : ↥Ab, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥Kb) : (AlgebraicClosure ℚ)) ∈ S) ∧
        (∀ a : ↥Ab, ((φ (Polynomial.C a) : ↥S) : ↥(fieldBar q M')) = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥Kb) : (AlgebraicClosure ℚ))) ∧
        (∀ a : ↥Ab, χ (φ (Polynomial.C a)) = IsLocalRing.residue ↥A ⟨((a : ↥Kb) : (AlgebraicClosure ℚ)), (hAb a).mp a.2⟩) ∧
        χ (φ Polynomial.X) = 0 ∧

        (∃ _ : IsLocalRing ↥S, RingHom.ker χ = maximalIdeal ↥S) ∧

        (∀ f : ↥(fieldBar q M'), f ∈ S → f ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑Kb : Set (AlgebraicClosure ℚ))) ⊔ F₀) ∧
        (∀ f : ↥(fieldBar q M'), f ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑Kb : Set (AlgebraicClosure ℚ))) ⊔ F₀ → ∃ g h : ↥S, (h : ↥(fieldBar q M')) ≠ 0 ∧ f * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M'))) ∧

        (φ).FormallySmooth ∧ (φ).FormallyUnramified ∧ (φ).EssFiniteType ∧

        (∃ hSR : ∀ f : ↥S, (f : ↥(fieldBar q M')) ∈ R.integers,
          ∀ f : ↥S, (⟨(f : ↥(fieldBar q M')), hSR f⟩ : ↥R.integers) ∈ maximalIdeal ↥R.integers ↔ φ (Polynomial.C ϖb) ∣ f) ∧

        (∀ f : ↥S, ∃ hR : (f : ↥(fieldBar q M')) ∈ R.integers, ∃ hm : R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ Q.toValuationSubring,
          IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : ↥(fieldBar q M')), hR⟩, hm⟩ =
            algebraMap (ResidueField ↥A) Q.ResidueField (χ f)) ∧
        (∃ hR : ((φ Polynomial.X : ↥S) : ↥(fieldBar q M')) ∈ R.integers,
          Q.ord (R.residue ⟨((φ Polynomial.X : ↥S) : ↥(fieldBar q M')), hR⟩) = 1) ∧

        (∀ f : ↥(fieldBar q M'), f ∈ B → f ∈ S) ∧
        (∀ f : ↥(fieldBar q M'), f ∈ S ↔ ∃ g h : ↥B, (∃ hm : R.residue ⟨((h : ↥B) : ↥(fieldBar q M')), hBR _ (h).2⟩ ∈ Q.toValuationSubring,
            IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨((h : ↥B) : ↥(fieldBar q M')), hBR _ (h).2⟩, hm⟩ ≠ 0) ∧ f * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M'))) := by
    intro Q
    by_cases hQN : Q ∈ N
    · refine ⟨(A.toSubring).map (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')), ?_, ?_, fun h => (h hQN).elim⟩
      · exact Polynomial.eval₂RingHom
          (((A.toSubring).equivMapOfInjective (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).injective).toRingHom.comp
            (((algebraMap ↥Kb (AlgebraicClosure ℚ)).comp Ab.subtype).codRestrict A.toSubring (fun x => (hAb x).mp x.2))) 0
      · exact (IsLocalRing.residue ↥A).comp
          ((A.toSubring).equivMapOfInjective (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).injective).symm.toRingHom
    · obtain ⟨S, φ, χ, hspec⟩ := ModularCurve.FullLevel.supersingularProlongation_smoothPointStalk_of_affineChart q hq M' hqM' A hA W hW hle s k₀ hκ halgc Kb hKb Ab hAb hdvrb hhensb ϖb hϖb hϖb0
        F₀ W₀ h1 hLD B alg hM1 hM0a hM0b hM4a hM4b hM4c hM2a hM2b hM2c FSS R hRW hBR hfracR Q ((hNiff Q).mp hQN)
      exact ⟨S, φ, χ, fun _ => hspec⟩
  choose Sb φb χb hS using tot
  obtain ⟨hdisj, hcusp, heqv⟩ := ModularCurve.FullLevel.supersingularProlongation_discRiders_of_affineChart q hq M' hqM' A hA W hW hle s k₀ Kb Ab hAb hdvrb ϖb hϖb F₀ B alg hM5a hM5b FSS R hBR
    hfracR N hNiff hNeqv Sb φb χb hS
    (fun Q => {P | (P.IsRational ∧
        (∀ f : ↥(Sb Q), (f : ↥(fieldBar q M')) ∈ P.toValuationSubring ∧ P.evalAt (f : ↥(fieldBar q M')) ∈ A) ∧
        (∀ f : ↥(Sb Q), A.valuation (P.evalAt (f : ↥(fieldBar q M'))) < 1 ↔ χb Q f = 0))}) (fun Q P => Iff.rfl)
  have hBsurj := KL5.exists_mem_chart_residue_eq_of_forall_not_mem_ends q M' A inst hdomC halgc B FSS R hBR Cs ρ hρrange e he' N hNiff
  refine ⟨N, Sb, φb, χb, fun Q => {P | (P.IsRational ∧
        (∀ f : ↥(Sb Q), (f : ↥(fieldBar q M')) ∈ P.toValuationSubring ∧ P.evalAt (f : ↥(fieldBar q M')) ∈ A) ∧
        (∀ f : ↥(Sb Q), A.valuation (P.evalAt (f : ↥(fieldBar q M'))) < 1 ↔ χb Q f = 0))}, hcard, ?_, ?_, hdisj, hcusp, heqv⟩
  · refine ⟨B, hBR, fun Q hQN f hf => ?_, hBsurj⟩
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, a14, -⟩ := hS Q hQN
    exact a14 f hf
  intro Q hQN
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, -, -⟩ := hS Q hQN
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, fun P => Iff.rfl⟩

namespace KLevelGeomCoreReduce

theorem SmoothOfModel
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (s : ↥W)
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
      Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A)
    (halgc : IsAlgClosed (ResidueField ↥A))
    (inst : Algebra (GaloisField q 2) (ResidueField ↥A)) (hdomC : IsDomain (DrinfeldCurve.CoordRing q (ResidueField ↥A))) (ζix : Idx q)

    (Kb : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (hKb : Kb = ⊥) (Ab : ValuationSubring ↥Kb) (hAb : ∀ x : ↥Kb, x ∈ Ab ↔ (x : (AlgebraicClosure ℚ)) ∈ A)
    (hdvrb : IsDiscreteValuationRing ↥Ab) (hhensb : HenselianLocalRing ↥Ab)
    (ϖb : ↥Ab) (hϖb : maximalIdeal ↥Ab = Ideal.span {ϖb}) (hϖb0 : ϖb ≠ 0) :
    letI : Algebra ↥k₀ ↥(fieldBar q M') :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
    ∀ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M')) (W₀ : ValuationSubring ↥F₀),
      (IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) ⊔ F₀ = ⊤) → (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥F₀ x ∈ W₀) → IsDiscreteValuationRing ↥W₀ →
      (∃ hπW : algebraMap ↥k₀ ↥F₀ π₀ ∈ W₀, maximalIdeal ↥W₀ = Ideal.span {(⟨_, hπW⟩ : ↥W₀)}) →
      (∀ (K' : IntermediateField ↥k₀ (AlgebraicClosure ℚ)), FiniteDimensional ↥k₀ ↥K' →
        ∀ (m : ℕ) (c : Fin m → (AlgebraicClosure ℚ)) (a : Fin m → ↥(fieldBar q M')), (∀ i, a i ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K' : Set (AlgebraicClosure ℚ))) ⊔ F₀) →
          LinearIndependent ↥K' c → ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c i) * a i = 0 → ∀ i, a i = 0) →

      (∃ (B : Subring ↥(fieldBar q M')) (alg : Algebra ↥Ab ↥B),

        (∀ a : ↥Ab, ((@algebraMap ↥Ab ↥B _ _ alg a : ↥B) : ↥(fieldBar q M')) = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥Kb) : (AlgebraicClosure ℚ))) ∧

        (∀ f : ↥(fieldBar q M'), f ∈ B → f ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑Kb : Set (AlgebraicClosure ℚ))) ⊔ F₀) ∧
        (∀ f : ↥(fieldBar q M'), f ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑Kb : Set (AlgebraicClosure ℚ))) ⊔ F₀ → ∃ g h : ↥B, (h : ↥(fieldBar q M')) ≠ 0 ∧ f * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M'))) ∧

        @Algebra.FormallySmooth ↥Ab ↥B _ _ alg ∧ @Algebra.FinitePresentation ↥Ab ↥B _ _ alg ∧
        Ring.KrullDimLE 1 (↥B ⧸ Ideal.span {@algebraMap ↥Ab ↥B _ _ alg ϖb}) ∧

        (∀ f : ↥(fieldBar q M'), f ∈ B → ∃ hf : f ∈ F₀, (⟨f, hf⟩ : ↥F₀) ∈ W₀) ∧
        Prime (@algebraMap ↥Ab ↥B _ _ alg ϖb) ∧
        (∀ f : ↥F₀, f ∈ W₀ ↔ ∃ g h : ↥B, ¬ (@algebraMap ↥Ab ↥B _ _ alg ϖb ∣ h) ∧ (f : ↥(fieldBar q M')) * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M'))) ∧

        ((IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                ↥(modularFunctionFieldBar M')) : fieldBar q M') ∈ B) ∧
        (∀ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → ∀ f : ↥(fieldBar q M'), f ∈ B → levelAutBar q M' ζ γ f ∈ B) ∧

        (∀ (inst : Algebra (GaloisField q 2) (ResidueField ↥A)),
          ∀ (_ : IsDomain (DrinfeldCurve.CoordRing q (ResidueField ↥A))),
          ∀ (ζ : Idx q),
          ∃ (Cs : Subgroup (rootsOfUnity (q + 1) (GaloisField q 2)))
            (ρ : ↥B →+* ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)),
            Nat.card Cs = 2 * placeWidthChar q M' (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')) ∧
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
                  DrinfeldCurve.hFunctionFieldAction q (ResidueField ↥A) ⟨_, hmem⟩ ((ρ f : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A))))) →
      ∀ (FSS : Type) [Field FSS] [Algebra (ResidueField ↥A) FSS] (R : RegularProlongation A ↥(fieldBar q M') FSS),
        (∀ f : ↥F₀, ((f : ↥(fieldBar q M')) ∈ R.integers ↔ f ∈ W₀)) →
        (∀ (inst : Algebra (GaloisField q 2) (ResidueField ↥A)),
          ∀ (_ : IsDomain (DrinfeldCurve.CoordRing q (ResidueField ↥A))),
          ∀ (ζ : Idx q),
          ∃ (Cs : Subgroup (rootsOfUnity (q + 1) (GaloisField q 2)))
            (e : FSS ≃ₐ[ResidueField ↥A] ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)),
            Nat.card Cs = 2 * placeWidthChar q M' (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')) ∧
            (∀ (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
              ∀ (hτ : ∀ f : ↥(fieldBar q M'), levelAutBar q M' ζ γ⁻¹ f ∈ R.integers ↔ f ∈ R.integers)
                (hmem : (redQ q γ, (1 : (GaloisField q 2)ˣ)) ∈ DrinfeldCurve.hSubgroup q),
                ∀ x : FSS,
                  ((e (R.resAut (levelAutBar q M' ζ γ⁻¹) hτ x) : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) =
                    DrinfeldCurve.hFunctionFieldAction q (ResidueField ↥A) ⟨_, hmem⟩ ((e x : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)))) ∧
        ∃ (N : Finset (Place (ResidueField ↥A) FSS))
          (Sb : Place (ResidueField ↥A) FSS → Subring ↥(fieldBar q M'))
          (φb : (Q : Place (ResidueField ↥A) FSS) → (Polynomial ↥Ab →+* ↥(Sb Q)))
          (χb : (Q : Place (ResidueField ↥A) FSS) → (↥(Sb Q) →+* ResidueField ↥A))
          (Db : Place (ResidueField ↥A) FSS → Set (Place (AlgebraicClosure ℚ) ↥(fieldBar q M'))),
          N.card = q + 1 ∧

          (∃ B : Subring ↥(fieldBar q M'),
            (∀ f : ↥(fieldBar q M'), f ∈ B → f ∈ R.integers) ∧
            (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N → ∀ f : ↥(fieldBar q M'), f ∈ B → f ∈ Sb Q) ∧
            (∀ z : FSS, (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N → z ∈ Q.toValuationSubring) →
              ∃ (f : ↥(fieldBar q M')) (_ : f ∈ B) (hfR : f ∈ R.integers), R.residue ⟨f, hfR⟩ = z)) ∧
          (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N →

            (
              (∀ a : ↥Ab, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥Kb) : (AlgebraicClosure ℚ)) ∈ Sb Q) ∧

              (∀ a : ↥Ab, ((φb Q (Polynomial.C a) : ↥(Sb Q)) : ↥(fieldBar q M')) = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥Kb) : (AlgebraicClosure ℚ))) ∧
              (∀ a : ↥Ab, χb Q (φb Q (Polynomial.C a)) = IsLocalRing.residue ↥A ⟨((a : ↥Kb) : (AlgebraicClosure ℚ)), (hAb a).mp a.2⟩) ∧
              χb Q (φb Q Polynomial.X) = 0 ∧

              (∃ _ : IsLocalRing ↥(Sb Q), RingHom.ker (χb Q) = maximalIdeal ↥(Sb Q)) ∧

              (∀ f : ↥(fieldBar q M'), f ∈ Sb Q → f ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑Kb : Set (AlgebraicClosure ℚ))) ⊔ F₀) ∧
              (∀ f : ↥(fieldBar q M'), f ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑Kb : Set (AlgebraicClosure ℚ))) ⊔ F₀ → ∃ g h : ↥(Sb Q), (h : ↥(fieldBar q M')) ≠ 0 ∧ f * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M'))) ∧

              (φb Q).FormallySmooth ∧ (φb Q).FormallyUnramified ∧ (φb Q).EssFiniteType ∧

              (∃ hSR : ∀ f : ↥(Sb Q), (f : ↥(fieldBar q M')) ∈ R.integers,
                ∀ f : ↥(Sb Q), (⟨(f : ↥(fieldBar q M')), hSR f⟩ : ↥R.integers) ∈ maximalIdeal ↥R.integers ↔ φb Q (Polynomial.C ϖb) ∣ f) ∧

              (∀ f : ↥(Sb Q), ∃ hR : (f : ↥(fieldBar q M')) ∈ R.integers, ∃ hm : R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ Q.toValuationSubring,
                IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : ↥(fieldBar q M')), hR⟩, hm⟩ =
                  algebraMap (ResidueField ↥A) Q.ResidueField (χb Q f)) ∧

              (∃ hR : ((φb Q Polynomial.X : ↥(Sb Q)) : ↥(fieldBar q M')) ∈ R.integers,
                Q.ord (R.residue ⟨((φb Q Polynomial.X : ↥(Sb Q)) : ↥(fieldBar q M')), hR⟩) = 1) ∧

              (∀ P, P ∈ Db Q ↔ (P.IsRational ∧
                (∀ f : ↥(Sb Q), (f : ↥(fieldBar q M')) ∈ P.toValuationSubring ∧ P.evalAt (f : ↥(fieldBar q M')) ∈ A) ∧
                (∀ f : ↥(Sb Q), A.valuation (P.evalAt (f : ↥(fieldBar q M'))) < 1 ↔ χb Q f = 0))) )) ∧

          (∀ Q Q' : Place (ResidueField ↥A) FSS, Q ∉ N → Q' ∉ N → ∀ (P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M')), P ∈ Db Q → P ∈ Db Q' → Q = Q') ∧

          (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N → ∀ P ∈ Db Q,
            0 ≤ P.ord (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                ↥(modularFunctionFieldBar M')) : fieldBar q M')) ∧

          (∀ τ ∈ Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
              ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ},
            ∀ (hτ : ∀ f : ↥(fieldBar q M'), τ f ∈ R.integers ↔ f ∈ R.integers) (Q : Place (ResidueField ↥A) FSS),
              (R.resAut τ hτ • Q ∈ N ↔ Q ∈ N) ∧
              (Q ∉ N → AlgebraicCurve.RegularProlongation.smulDisc τ (Db Q) = Db (R.resAut τ hτ • Q))) := by
  intro F₀ W₀ h1 h2 h3 h4 hLD hM FSS _ _ R hRW
  obtain ⟨B, alg, hM1, hM0a, hM0b, hM4a, hM4b, hM4c, hM2a, hM2b, hM2c, hM5a, hM5b, hM3⟩ := hM
  exact ⟨ModularCurve.FullLevel.supersingularProlongation_existDL_of_affineChart q hq M' hqM' A hA W hW hle s k₀ π₀ hπ hdvr hunif hhens hres hκ Kb hKb Ab hAb hdvrb hhensb ϖb hϖb hϖb0
      F₀ W₀ h1 h2 h3 h4 B alg hM1 hM2a hM2c hM3 hM5b FSS R hRW,
    EBS2 q hq M' hqM' A hA W hW hle s k₀ π₀ hπ hdvr hunif hhens hres hκ halgc inst hdomC ζix Kb hKb Ab hAb hdvrb hhensb ϖb hϖb hϖb0
      F₀ W₀ h1 h2 h3 h4 hLD B alg hM1 hM0a hM0b hM4a hM4b hM4c hM2a hM2b hM2c hM5a hM5b hM3 FSS R hRW⟩

theorem isUnit_iff_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) (x : R) :
    IsUnit (e x) ↔ IsUnit x := by
  constructor
  · intro h
    have := h.map e.symm
    simpa using this
  · intro h
    exact h.map e

theorem henselian_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] [hR : HenselianLocalRing R]
    (e : R ≃+* S) : HenselianLocalRing S := by
  haveI : Nontrivial S := e.symm.toEquiv.nontrivial
  haveI : IsLocalRing S := IsLocalRing.of_surjective' (e : R →+* S) e.surjective
  refine ⟨fun f hf a₀ h₁ h₂ => ?_⟩
  set g : Polynomial R := f.map (e.symm : S →+* R) with hg
  have hgm : g.Monic := hf.map _
  have hev : ∀ x : S, g.eval (e.symm x) = e.symm (f.eval x) := by
    intro x
    rw [hg, Polynomial.eval_map]
    exact Polynomial.eval₂_at_apply (e.symm : S →+* R) x
  have hevd : ∀ x : S, g.derivative.eval (e.symm x) = e.symm (f.derivative.eval x) := by
    intro x
    rw [hg, Polynomial.derivative_map, Polynomial.eval_map]
    exact Polynomial.eval₂_at_apply (e.symm : S →+* R) x
  have h₁' : g.eval (e.symm a₀) ∈ maximalIdeal R := by
    rw [hev, mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_of_ringEquiv e.symm]
    exact h₁
  have h₂' : IsUnit (g.derivative.eval (e.symm a₀)) := by
    rw [hevd, isUnit_iff_of_ringEquiv e.symm]
    exact h₂
  obtain ⟨a, ha, hamem⟩ := HenselianLocalRing.is_henselian g hgm (e.symm a₀) h₁' h₂'
  refine ⟨e a, ?_, ?_⟩
  · have : e.symm (f.eval (e a)) = 0 := by
      rw [← hev, e.symm_apply_apply]
      exact ha
    simpa using congrArg e this
  · have hm : e.symm (e a - a₀) ∈ maximalIdeal R := by
      simpa using hamem
    rw [mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_of_ringEquiv e.symm] at hm
    exact hm

theorem glue_base {L : Type} [Field L] (k₀ : Type) [Field k₀] [Algebra k₀ L] (A : ValuationSubring L)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap k₀ L)))
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap k₀ L))) :
    IsDiscreteValuationRing ↥(A.comap (algebraMap ↥(⊥ : IntermediateField k₀ L) L)) ∧
    HenselianLocalRing ↥(A.comap (algebraMap ↥(⊥ : IntermediateField k₀ L) L)) ∧
    ∃ ϖ : ↥(A.comap (algebraMap ↥(⊥ : IntermediateField k₀ L) L)),
      maximalIdeal ↥(A.comap (algebraMap ↥(⊥ : IntermediateField k₀ L) L)) = Ideal.span {ϖ} ∧ ϖ ≠ 0 := by
  let e := IntermediateField.botEquiv k₀ L
  have key : ∀ x : ↥(⊥ : IntermediateField k₀ L), algebraMap k₀ L (e x) = (x : L) := by
    intro x
    have h := IsScalarTower.algebraMap_apply ↥(⊥ : IntermediateField k₀ L) k₀ L x
    rw [IntermediateField.coe_algebraMap_over_bot] at h
    exact h.symm
  have memiff : ∀ x : ↥(⊥ : IntermediateField k₀ L),
      x ∈ A.comap (algebraMap ↥(⊥ : IntermediateField k₀ L) L) ↔ e x ∈ A.comap (algebraMap k₀ L) := by
    intro x
    rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap, key]
    rfl
  have hmap : (A.comap (algebraMap ↥(⊥ : IntermediateField k₀ L) L)).toSubring.map e.toRingEquiv.toRingHom =
      (A.comap (algebraMap k₀ L)).toSubring := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (memiff x).mp hx
    · intro hy
      refine ⟨e.symm y, (memiff _).mpr ?_, e.apply_symm_apply y⟩
      rw [e.apply_symm_apply]; exact hy
  let Φ : ↥(A.comap (algebraMap ↥(⊥ : IntermediateField k₀ L) L)) ≃+* ↥(A.comap (algebraMap k₀ L)) :=
    RingEquiv.trans e.toRingEquiv.subringMap (RingEquiv.subringCongr hmap)
  haveI := hdvr
  haveI := hhens
  have hd : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥(⊥ : IntermediateField k₀ L) L)) :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing Φ.symm
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥(A.comap (algebraMap ↥(⊥ : IntermediateField k₀ L) L))
  exact ⟨hd, henselian_of_ringEquiv Φ.symm, ϖ, hϖ.maximalIdeal_eq, hϖ.ne_zero⟩

theorem glue_resAlgClosed_gen {K L : Type} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) (k₀ : IntermediateField K L)
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ L))))
    (hκ : ∀ a : L, a ∈ A → ∃ c : ↥k₀, (c : L) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A) :
    IsAlgClosed (ResidueField ↥A) := by
  let f : ↥(A.comap (algebraMap ↥k₀ L)) →+* ↥A :=
    ((algebraMap ↥k₀ L).comp (A.comap (algebraMap ↥k₀ L)).subtype).codRestrict A.toSubring
      (fun x => ValuationSubring.mem_comap.mp x.2)
  let g : ↥(A.comap (algebraMap ↥k₀ L)) →+* ResidueField ↥A := (residue ↥A).comp f
  have hg : Function.Surjective g := by
    intro r
    obtain ⟨a, rfl⟩ := residue_surjective r
    obtain ⟨c, hcA, hsub, hm⟩ := hκ a a.2
    refine ⟨⟨c, ValuationSubring.mem_comap.mpr hcA⟩, ?_⟩
    have hfc : f ⟨c, ValuationSubring.mem_comap.mpr hcA⟩ = ⟨(c : L), hcA⟩ := Subtype.ext rfl
    change residue ↥A (f ⟨c, _⟩) = residue ↥A a
    rw [hfc, eq_comm, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact hm
  have hmax : RingHom.ker g = maximalIdeal ↥(A.comap (algebraMap ↥k₀ L)) :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective g hg)
  let e : ResidueField ↥(A.comap (algebraMap ↥k₀ L)) ≃+* ResidueField ↥A :=
    (Ideal.quotEquivOfEq hmax.symm).trans (RingHom.quotientKerEquivOfSurjective hg)
  exact IsAlgClosed.of_ringEquiv (ResidueField ↥(A.comap (algebraMap ↥k₀ L))) (ResidueField ↥A) e

theorem glue_charP (q : ℕ) [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    CharP (ResidueField ↥A) q := by
  have hq : ((q : ↥A) : AlgebraicClosure ℚ) = (q : AlgebraicClosure ℚ) := by norm_cast
  have hmem : (q : ↥A) ∈ maximalIdeal ↥A := by
    rw [← ValuationSubring.coe_mem_nonunits_iff, hq]; exact hA
  have h0 : ((q : ℕ) : ResidueField ↥A) = 0 := by
    rw [← map_natCast (IsLocalRing.residue ↥A), IsLocalRing.residue_eq_zero_iff]; exact hmem
  exact (CharP.charP_iff_prime_eq_zero (Fact.out : q.Prime)).mpr h0

theorem glue_nonempty_algebra_galoisField (q : ℕ) [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime q) (halgc : IsAlgClosed (ResidueField ↥A)) :
    Nonempty (Algebra (GaloisField q 2) (ResidueField ↥A)) := by
  haveI := glue_charP q A hA
  haveI := halgc
  letI : Algebra (ZMod q) (ResidueField ↥A) := ZMod.algebra _ q
  exact ⟨(IsAlgClosed.lift (M := ResidueField ↥A) (R := ZMod q) (S := GaloisField q 2)).toRingHom.toAlgebra⟩

theorem glue_isDomain_coordRing (q : ℕ) [Fact q.Prime] (κ : Type) [Field κ] : IsDomain (DrinfeldCurve.CoordRing q κ) :=
  DrinfeldCurve.isDomain_coordRing_of_ne_one q (Fact.out : q.Prime).ne_one κ

noncomputable def glue_idx (q : ℕ) [Fact q.Prime] (ℓ : ℕ) (hℓ : ℓ.Prime) (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    (ζ₀ : ↥k₀) (hζ₀ : IsPrimitiveRoot ((ζ₀ : ↥k₀) : AlgebraicClosure ℚ) (q * ℓ)) : Idx q :=
  Idx.mk (((ζ₀ : ↥k₀) : AlgebraicClosure ℚ) ^ ℓ)
    (hζ₀.pow (Nat.mul_pos (Fact.out : q.Prime).pos hℓ.pos) (mul_comm q ℓ))

end KLevelGeomCoreReduce

open KLevelGeomCoreReduce in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
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
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A)

    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (ζ₀ : ↥k₀) (hζ₀ : IsPrimitiveRoot ((ζ₀ : ↥k₀) : AlgebraicClosure ℚ) (q * ℓ))
    (ϖt : ↥k₀) (hϖtA : (ϖt : AlgebraicClosure ℚ) ∈ A)
    (hϖt : ∃ u : ↥A, IsUnit u ∧ (ϖt : AlgebraicClosure ℚ) ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ) * (u : AlgebraicClosure ℚ))

    (Kb : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (hKb : Kb = ⊥)
    (Ab : ValuationSubring ↥Kb) (hAb : ∀ x : ↥Kb, x ∈ Ab ↔ (x : (AlgebraicClosure ℚ)) ∈ A)
    (ϖb : ↥Ab) (hϖb : maximalIdeal ↥Ab = Ideal.span {ϖb}) (hϖb0 : ϖb ≠ 0) :
    letI : Algebra ↥k₀ ↥(fieldBar q M') :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
    ∀ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M')) (W₀ : ValuationSubring ↥F₀),
      (

      (IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) ⊔ F₀ = ⊤) ∧

      (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥F₀ x ∈ W₀) ∧
      IsDiscreteValuationRing ↥W₀ ∧
      (∃ hπW : algebraMap ↥k₀ ↥F₀ π₀ ∈ W₀, maximalIdeal ↥W₀ = Ideal.span {(⟨_, hπW⟩ : ↥W₀)}) ∧

      (∃ t : ↥W₀, ∀ p : Polynomial ↥k₀, (∀ n, ((p.coeff n : ↥k₀) : (AlgebraicClosure ℚ)) ∈ A) →
        (∃ hm : Polynomial.aeval (t : ↥F₀) p ∈ W₀, (⟨_, hm⟩ : ↥W₀) ∈ maximalIdeal ↥W₀) →
          ∀ n, ∃ hc : algebraMap ↥k₀ ↥F₀ (p.coeff n) ∈ W₀, (⟨_, hc⟩ : ↥W₀) ∈ maximalIdeal ↥W₀) ∧

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
              ∃ hm : (⟨_, hF⟩ : ↥F₀) - algebraMap ↥k₀ ↥F₀ c ∈ W₀, (⟨_, hm⟩ : ↥W₀) ∈ maximalIdeal ↥W₀) ∧

      (∀ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
        (∀ f : ↥(fieldBar q M'), f ∈ F₀ → levelAutBar q M' ζ γ f ∈ F₀) ∧
        (∀ (f : ↥(fieldBar q M')) (hf : f ∈ F₀) (hf' : levelAutBar q M' ζ γ f ∈ F₀),
          (⟨f, hf⟩ : ↥F₀) ∈ W₀ ↔ (⟨_, hf'⟩ : ↥F₀) ∈ W₀)) ∧

      (∀ (K' : IntermediateField ↥k₀ (AlgebraicClosure ℚ)), FiniteDimensional ↥k₀ ↥K' →
        ∀ (m : ℕ) (c : Fin m → (AlgebraicClosure ℚ)) (a : Fin m → ↥(fieldBar q M')), (∀ i, a i ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K' : Set (AlgebraicClosure ℚ))) ⊔ F₀) →
          LinearIndependent ↥K' c → ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c i) * a i = 0 → ∀ i, a i = 0) ∧

      (∃ (B : Subring ↥(fieldBar q M')) (alg : Algebra ↥Ab ↥B),

        (∀ a : ↥Ab, ((@algebraMap ↥Ab ↥B _ _ alg a : ↥B) : ↥(fieldBar q M')) = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥Kb) : (AlgebraicClosure ℚ))) ∧

        (∀ f : ↥(fieldBar q M'), f ∈ B → f ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑Kb : Set (AlgebraicClosure ℚ))) ⊔ F₀) ∧
        (∀ f : ↥(fieldBar q M'), f ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑Kb : Set (AlgebraicClosure ℚ))) ⊔ F₀ → ∃ g h : ↥B, (h : ↥(fieldBar q M')) ≠ 0 ∧ f * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M'))) ∧

        @Algebra.FormallySmooth ↥Ab ↥B _ _ alg ∧ @Algebra.FinitePresentation ↥Ab ↥B _ _ alg ∧
        Ring.KrullDimLE 1 (↥B ⧸ Ideal.span {@algebraMap ↥Ab ↥B _ _ alg ϖb}) ∧

        (∀ f : ↥(fieldBar q M'), f ∈ B → ∃ hf : f ∈ F₀, (⟨f, hf⟩ : ↥F₀) ∈ W₀) ∧
        Prime (@algebraMap ↥Ab ↥B _ _ alg ϖb) ∧
        (∀ f : ↥F₀, f ∈ W₀ ↔ ∃ g h : ↥B, ¬ (@algebraMap ↥Ab ↥B _ _ alg ϖb ∣ h) ∧ (f : ↥(fieldBar q M')) * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M'))) ∧

        ((IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                ↥(modularFunctionFieldBar M')) : fieldBar q M') ∈ B) ∧
        (∀ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → ∀ f : ↥(fieldBar q M'), f ∈ B → levelAutBar q M' ζ γ f ∈ B) ∧

        (∀ (inst : Algebra (GaloisField q 2) (ResidueField ↥A)),
          ∀ (_ : IsDomain (DrinfeldCurve.CoordRing q (ResidueField ↥A))),
          ∀ (ζ : Idx q),
          ∃ (Cs : Subgroup (rootsOfUnity (q + 1) (GaloisField q 2)))
            (ρ : ↥B →+* ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)),
            Nat.card Cs = 2 * placeWidthChar q M' (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')) ∧
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
                  DrinfeldCurve.hFunctionFieldAction q (ResidueField ↥A) ⟨_, hmem⟩ ((ρ f : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)))))) →
      (

      (IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) ⊔ F₀ = ⊤) ∧

      (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥F₀ x ∈ W₀) ∧
      IsDiscreteValuationRing ↥W₀ ∧
      (∃ hπW : algebraMap ↥k₀ ↥F₀ π₀ ∈ W₀, maximalIdeal ↥W₀ = Ideal.span {(⟨_, hπW⟩ : ↥W₀)}) ∧

      (∃ t : ↥W₀, ∀ p : Polynomial ↥k₀, (∀ n, ((p.coeff n : ↥k₀) : (AlgebraicClosure ℚ)) ∈ A) →
        (∃ hm : Polynomial.aeval (t : ↥F₀) p ∈ W₀, (⟨_, hm⟩ : ↥W₀) ∈ maximalIdeal ↥W₀) →
          ∀ n, ∃ hc : algebraMap ↥k₀ ↥F₀ (p.coeff n) ∈ W₀, (⟨_, hc⟩ : ↥W₀) ∈ maximalIdeal ↥W₀) ∧

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
              ∃ hm : (⟨_, hF⟩ : ↥F₀) - algebraMap ↥k₀ ↥F₀ c ∈ W₀, (⟨_, hm⟩ : ↥W₀) ∈ maximalIdeal ↥W₀) ∧

      (∀ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
        (∀ f : ↥(fieldBar q M'), f ∈ F₀ → levelAutBar q M' ζ γ f ∈ F₀) ∧
        (∀ (f : ↥(fieldBar q M')) (hf : f ∈ F₀) (hf' : levelAutBar q M' ζ γ f ∈ F₀),
          (⟨f, hf⟩ : ↥F₀) ∈ W₀ ↔ (⟨_, hf'⟩ : ↥F₀) ∈ W₀)) ∧

      (∀ (K' : IntermediateField ↥k₀ (AlgebraicClosure ℚ)), FiniteDimensional ↥k₀ ↥K' →
        ∀ (m : ℕ) (c : Fin m → (AlgebraicClosure ℚ)) (a : Fin m → ↥(fieldBar q M')), (∀ i, a i ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K' : Set (AlgebraicClosure ℚ))) ⊔ F₀) →
          LinearIndependent ↥K' c → ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c i) * a i = 0 → ∀ i, a i = 0) ∧

      (∀ (FSS : Type) [Field FSS] [Algebra (ResidueField ↥A) FSS] (R : RegularProlongation A ↥(fieldBar q M') FSS),
        (∀ f : ↥F₀, ((f : ↥(fieldBar q M')) ∈ R.integers ↔ f ∈ W₀)) →
        (∀ (inst : Algebra (GaloisField q 2) (ResidueField ↥A)),
          ∀ (_ : IsDomain (DrinfeldCurve.CoordRing q (ResidueField ↥A))),
          ∀ (ζ : Idx q),
          ∃ (Cs : Subgroup (rootsOfUnity (q + 1) (GaloisField q 2)))
            (e : FSS ≃ₐ[ResidueField ↥A] ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)),
            Nat.card Cs = 2 * placeWidthChar q M' (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')) ∧
            (∀ (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
              ∀ (hτ : ∀ f : ↥(fieldBar q M'), levelAutBar q M' ζ γ⁻¹ f ∈ R.integers ↔ f ∈ R.integers)
                (hmem : (redQ q γ, (1 : (GaloisField q 2)ˣ)) ∈ DrinfeldCurve.hSubgroup q),
                ∀ x : FSS,
                  ((e (R.resAut (levelAutBar q M' ζ γ⁻¹) hτ x) : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) =
                    DrinfeldCurve.hFunctionFieldAction q (ResidueField ↥A) ⟨_, hmem⟩ ((e x : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)))) ∧
        ∃ (N : Finset (Place (ResidueField ↥A) FSS))
          (Sb : Place (ResidueField ↥A) FSS → Subring ↥(fieldBar q M'))
          (φb : (Q : Place (ResidueField ↥A) FSS) → (Polynomial ↥Ab →+* ↥(Sb Q)))
          (χb : (Q : Place (ResidueField ↥A) FSS) → (↥(Sb Q) →+* ResidueField ↥A))
          (Db : Place (ResidueField ↥A) FSS → Set (Place (AlgebraicClosure ℚ) ↥(fieldBar q M'))),
          N.card = q + 1 ∧

          (∃ B : Subring ↥(fieldBar q M'),
            (∀ f : ↥(fieldBar q M'), f ∈ B → f ∈ R.integers) ∧
            (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N → ∀ f : ↥(fieldBar q M'), f ∈ B → f ∈ Sb Q) ∧
            (∀ z : FSS, (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N → z ∈ Q.toValuationSubring) →
              ∃ (f : ↥(fieldBar q M')) (_ : f ∈ B) (hfR : f ∈ R.integers), R.residue ⟨f, hfR⟩ = z)) ∧
          (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N →

            (
              (∀ a : ↥Ab, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥Kb) : (AlgebraicClosure ℚ)) ∈ Sb Q) ∧

              (∀ a : ↥Ab, ((φb Q (Polynomial.C a) : ↥(Sb Q)) : ↥(fieldBar q M')) = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥Kb) : (AlgebraicClosure ℚ))) ∧
              (∀ a : ↥Ab, χb Q (φb Q (Polynomial.C a)) = IsLocalRing.residue ↥A ⟨((a : ↥Kb) : (AlgebraicClosure ℚ)), (hAb a).mp a.2⟩) ∧
              χb Q (φb Q Polynomial.X) = 0 ∧

              (∃ _ : IsLocalRing ↥(Sb Q), RingHom.ker (χb Q) = maximalIdeal ↥(Sb Q)) ∧

              (∀ f : ↥(fieldBar q M'), f ∈ Sb Q → f ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑Kb : Set (AlgebraicClosure ℚ))) ⊔ F₀) ∧
              (∀ f : ↥(fieldBar q M'), f ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑Kb : Set (AlgebraicClosure ℚ))) ⊔ F₀ → ∃ g h : ↥(Sb Q), (h : ↥(fieldBar q M')) ≠ 0 ∧ f * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M'))) ∧

              (φb Q).FormallySmooth ∧ (φb Q).FormallyUnramified ∧ (φb Q).EssFiniteType ∧

              (∃ hSR : ∀ f : ↥(Sb Q), (f : ↥(fieldBar q M')) ∈ R.integers,
                ∀ f : ↥(Sb Q), (⟨(f : ↥(fieldBar q M')), hSR f⟩ : ↥R.integers) ∈ maximalIdeal ↥R.integers ↔ φb Q (Polynomial.C ϖb) ∣ f) ∧

              (∀ f : ↥(Sb Q), ∃ hR : (f : ↥(fieldBar q M')) ∈ R.integers, ∃ hm : R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ Q.toValuationSubring,
                IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : ↥(fieldBar q M')), hR⟩, hm⟩ =
                  algebraMap (ResidueField ↥A) Q.ResidueField (χb Q f)) ∧

              (∃ hR : ((φb Q Polynomial.X : ↥(Sb Q)) : ↥(fieldBar q M')) ∈ R.integers,
                Q.ord (R.residue ⟨((φb Q Polynomial.X : ↥(Sb Q)) : ↥(fieldBar q M')), hR⟩) = 1) ∧

              (∀ P, P ∈ Db Q ↔ (P.IsRational ∧
                (∀ f : ↥(Sb Q), (f : ↥(fieldBar q M')) ∈ P.toValuationSubring ∧ P.evalAt (f : ↥(fieldBar q M')) ∈ A) ∧
                (∀ f : ↥(Sb Q), A.valuation (P.evalAt (f : ↥(fieldBar q M'))) < 1 ↔ χb Q f = 0))) )) ∧

          (∀ Q Q' : Place (ResidueField ↥A) FSS, Q ∉ N → Q' ∉ N → ∀ (P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M')), P ∈ Db Q → P ∈ Db Q' → Q = Q') ∧

          (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N → ∀ P ∈ Db Q,
            0 ≤ P.ord (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                ↥(modularFunctionFieldBar M')) : fieldBar q M')) ∧

          (∀ τ ∈ Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
              ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ},
            ∀ (hτ : ∀ f : ↥(fieldBar q M'), τ f ∈ R.integers ↔ f ∈ R.integers) (Q : Place (ResidueField ↥A) FSS),
              (R.resAut τ hτ • Q ∈ N ↔ Q ∈ N) ∧
              (Q ∉ N → AlgebraicCurve.RegularProlongation.smulDisc τ (Db Q) = Db (R.resAut τ hτ • Q))))) := by
  letI instAlg : Algebra ↥k₀ ↥(fieldBar q M') :=
    ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
  intro F₀ W₀ hR
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, hLD, hM⟩ := hR
  refine ⟨h1, h2, h3, h4, h5, h6, h7, hLD, ?_⟩
  intro FSS _ _ R hRW

  subst hKb
  have hAbeq : Ab = A.comap (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ)) := by
    ext x; rw [hAb, ValuationSubring.mem_comap]; rfl
  obtain ⟨hd0, hh0, -⟩ := glue_base (L := (AlgebraicClosure ℚ)) ↥k₀ A hdvr hhens
  have hdvrb : IsDiscreteValuationRing ↥Ab := hAbeq.symm ▸ hd0
  have hhensb : HenselianLocalRing ↥Ab := hAbeq.symm ▸ hh0
  have halgc : IsAlgClosed (ResidueField ↥A) := glue_resAlgClosed_gen A k₀ hres hκ
  obtain ⟨instG⟩ := glue_nonempty_algebra_galoisField q A hA halgc
  have hdomC : IsDomain (DrinfeldCurve.CoordRing q (ResidueField ↥A)) := glue_isDomain_coordRing q (ResidueField ↥A)
  exact SmoothOfModel q hq M' hqM' A hA W hW hle s k₀ π₀ hπ hdvr hunif hhens hres hκ halgc instG hdomC (glue_idx q ℓ hℓ k₀ ζ₀ hζ₀)
    ⊥ rfl Ab hAb hdvrb hhensb ϖb hϖb hϖb0 F₀ W₀ h1 h2 h3 h4 hLD hM FSS R hRW

end S_ModularCurve_FullLevel_klevel_supersingularDVR_baseSmoothPointStalks_of_affineChart_chart
end P2MW
export P2MW.S_ModularCurve_FullLevel_klevel_supersingularDVR_baseSmoothPointStalks_of_affineChart_chart (solution)
