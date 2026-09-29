-- Prove2me | solution 1 for ModularCurve.FullLevel.supersingularProlongation_ends_baseSmoothPointStalks_localization_of_affineChart_of_eq_three_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/9b595ba6-d9f7-5e26-a052-5b8dabe9a3f0

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Theorems.Thm_ModularCurve_FullLevel_supersingularProlongation_residue_surjective_ker_of_affineChart_of_eq_three
import Theorems.Thm_RingHom_exists_algEquiv_comp_eq_of_ker_eq_of_forall_exists_mul_eq
import Theorems.Thm_ModularCurve_FullLevel_supersingularProlongation_ends_of_affineChart_of_eq_three
import Theorems.Thm_ModularCurve_FullLevel_supersingularProlongation_smoothPointStalk_of_affineChart_of_eq_three
import Theorems.Thm_ModularCurve_FullLevel_supersingularProlongation_discRiders_of_affineChart_of_eq_three
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_supersingularProlongation_ends_baseSmoothPointStalks_localization_of_affineChart_of_eq_three_of_dvd
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
theorem solution
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
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

          (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N ↔
            ∀ (b : ↥B) (hb : ((b : ↥B) : ↥(fieldBar q M')) ∈ R.integers), R.residue ⟨((b : ↥B) : ↥(fieldBar q M')), hb⟩ ∈ Q.toValuationSubring) ∧
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

              (∀ f : ↥(fieldBar q M'), f ∈ B → f ∈ Sb Q) ∧
              (∀ f : ↥(fieldBar q M'), f ∈ Sb Q ↔ ∃ g h : ↥B,
                (∀ hh : ((h : ↥B) : ↥(fieldBar q M')) ∈ R.integers, ∃ hm : R.residue ⟨((h : ↥B) : ↥(fieldBar q M')), hh⟩ ∈ Q.toValuationSubring,
                  IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨((h : ↥B) : ↥(fieldBar q M')), hh⟩, hm⟩ ≠ 0) ∧
                f * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M'))) ∧

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
  obtain ⟨hfracR, hkerR⟩ := ModularCurve.FullLevel.supersingularProlongation_residue_surjective_ker_of_affineChart_of_eq_three q hq3 M' hqM' A hA W hW hle s k₀ π₀ hπ hdvr hunif hhens hres hκ
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
  obtain ⟨N, hcard, hNiff, hNeqv⟩ := ModularCurve.FullLevel.supersingularProlongation_ends_of_affineChart_of_eq_three q hq3 M' hqM' A hA W hW hle s k₀ Kb Ab hAb ϖb inst hdomC B alg hM5b
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
    · obtain ⟨S, φ, χ, hspec⟩ := ModularCurve.FullLevel.supersingularProlongation_smoothPointStalk_of_affineChart_of_eq_three q hq3 M' hqM' A hA W hW hle s k₀ hκ halgc Kb hKb Ab hAb hdvrb hhensb ϖb hϖb hϖb0
        F₀ W₀ h1 hLD B alg hM1 hM0a hM0b hM4a hM4b hM4c hM2a hM2b hM2c FSS R hRW hBR hfracR Q ((hNiff Q).mp hQN)
      exact ⟨S, φ, χ, fun _ => hspec⟩
  choose Sb φb χb hS using tot
  obtain ⟨hdisj, hcusp, heqv⟩ := ModularCurve.FullLevel.supersingularProlongation_discRiders_of_affineChart_of_eq_three q hq3 M' hqM' A hA W hW hle s k₀ Kb Ab hAb hdvrb ϖb hϖb F₀ B alg hM5a hM5b FSS R hBR
    hfracR N hNiff hNeqv Sb φb χb hS
    (fun Q => {P | (P.IsRational ∧
        (∀ f : ↥(Sb Q), (f : ↥(fieldBar q M')) ∈ P.toValuationSubring ∧ P.evalAt (f : ↥(fieldBar q M')) ∈ A) ∧
        (∀ f : ↥(Sb Q), A.valuation (P.evalAt (f : ↥(fieldBar q M'))) < 1 ↔ χb Q f = 0))}) (fun Q P => Iff.rfl)
  refine ⟨N, Sb, φb, χb, fun Q => {P | (P.IsRational ∧
        (∀ f : ↥(Sb Q), (f : ↥(fieldBar q M')) ∈ P.toValuationSubring ∧ P.evalAt (f : ↥(fieldBar q M')) ∈ A) ∧
        (∀ f : ↥(Sb Q), A.valuation (P.evalAt (f : ↥(fieldBar q M'))) < 1 ↔ χb Q f = 0))}, hcard, ?_, ?_, hdisj, hcusp, heqv⟩
  ·
    intro Q
    rw [hNiff Q]
    constructor
    · intro h b hb
      exact h b
    · intro h b
      exact h b (hBR _ b.2)
  intro Q hQN
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩ := hS Q hQN
  refine ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, ?_, fun P => Iff.rfl⟩

  intro f
  rw [a15 f]
  constructor
  · rintro ⟨g, h, ⟨hm, hne⟩, hf⟩
    exact ⟨g, h, fun hh => ⟨hm, hne⟩, hf⟩
  · rintro ⟨g, h, hall, hf⟩
    obtain ⟨hm, hne⟩ := hall (hBR _ h.2)
    exact ⟨g, h, ⟨hm, hne⟩, hf⟩

end S_ModularCurve_FullLevel_supersingularProlongation_ends_baseSmoothPointStalks_localization_of_affineChart_of_eq_three_of_dvd
end P2MW
export P2MW.S_ModularCurve_FullLevel_supersingularProlongation_ends_baseSmoothPointStalks_localization_of_affineChart_of_eq_three_of_dvd (solution)
