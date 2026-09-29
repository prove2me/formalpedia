-- Prove2me | solution 1 for ModularCurve.FullLevel.supersingularProlongation_exists_annulusPair_of_nodePresentation_of_eq_two_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/733fb691-3d8d-5d12-81f9-899570295ef5

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_AlgebraicCurve_NodeAnnulusEngine_ord_residue_nonneg_and_finsum_ord_eq_ord_residue_add_of_ringEquiv_uvCrossingModel_layers
import Theorems.Thm_AlgebraicCurve_exists_annulusPair_isAttached_of_ringEquiv_uvCrossingModel_of_nodeCoordinates
import Theorems.Thm_ValuationSubring_exists_two_mem_maximalIdeal_dvd_valuation_ne_of_isAlgClosed
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_ValuationSubring_mulArchimedean_valueGroup_of_isAlgebraic_of_valuation_natCast_lt_one
import Theorems.Thm_ValuationSubring_mulArchimedean_valueGroup_iff_forall_exists_pow_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_supersingularProlongation_exists_annulusPair_of_nodePresentation_of_eq_two_of_dvd
p2m_attr_erase "instance" "AlgebraicCurve.GaussReduction.isLocalHom_constToGauss AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt instTopologicallyFGOfFiniteType AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup ModularCurve.UVCrossingModel
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

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
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπP : π ∈ A)
    (FSS : Type) [Field FSS] [Algebra (ResidueField A) FSS]
    (R : RegularProlongation A (fieldBar q M') FSS)
    (N : Finset (Place (ResidueField ↥A) FSS))

    (FIx : Place (ResidueField A) FSS → Type) [∀ x, Field (FIx x)] [∀ x, Algebra (ResidueField A) (FIx x)]
    (Rx : ∀ x : Place (ResidueField A) FSS, RegularProlongation A (fieldBar q M') (FIx x))
    (bx : ∀ x : Place (ResidueField A) FSS, Place (ResidueField A) (FIx x))

    (Λ : Type) (C' : Λ → Subring (AlgebraicClosure ℚ)) (hC'A : ∀ (l : Λ) (c : AlgebraicClosure ℚ), c ∈ C' l → c ∈ A)
    [∀ l, IsDomain ↥(C' l)] [∀ l, IsDiscreteValuationRing ↥(C' l)]
    (ϖ' : ∀ l, ↥(C' l)) (l₀ : Λ)
    (Wc : Λ → Type) [∀ l, CommRing (Wc l)] [∀ l, IsDomain (Wc l)] [∀ l, IsDiscreteValuationRing (Wc l)]
    [∀ l, IsAdicComplete (maximalIdeal (Wc l)) (Wc l)]
    (πW : ∀ l, Wc l) (E : Λ → ℕ) (E₀ : ℕ)

    (S : Place (ResidueField A) FSS → Set (Place (AlgebraicClosure ℚ) (fieldBar q M')))
    (𝒩 : Place (ResidueField A) FSS → Subring (fieldBar q M'))
    (𝒩₀ : Place (ResidueField A) FSS → Λ → Subring (fieldBar q M'))
    (hloc : ∀ nd l, IsLocalRing ↥(𝒩₀ nd l)) (hnoe : ∀ nd l, IsNoetherianRing ↥(𝒩₀ nd l))
    (cx cy cu : Place (ResidueField A) FSS → fieldBar q M')
    (hnodes :

          (∀ (l : Λ) (d : ↥(C' l)), IsLocalRing.residue A ⟨(d : AlgebraicClosure ℚ), hC'A l d d.2⟩ = 0 ↔ ∃ d' : ↥(C' l), d = ϖ' l * d') ∧
          (∀ l, C' l₀ ≤ C' l) ∧
          ((ϖ' l₀ : ↥(C' l₀)) : AlgebraicClosure ℚ) ≠ 0 ∧
          (∀ a : AlgebraicClosure ℚ, a ∈ A → IsAlgebraic ↥(C' l₀) a) ∧
          (∀ l, Irreducible (πW l)) ∧ (∀ l, 1 ≤ E l) ∧

          (∀ τ ∈ A.inertiaSubgroupIn ℚ, A.tameCharacter π τ = 1 →
            τ ((ϖ' l₀ : ↥(C' l₀)) : AlgebraicClosure ℚ) = ((ϖ' l₀ : ↥(C' l₀)) : AlgebraicClosure ℚ)) ∧

          (∃ w : ℕ, 1 ≤ w ∧ ∃ v : (↥A)ˣ,
            (⟨((ϖ' l₀ : ↥(C' l₀)) : AlgebraicClosure ℚ), hC'A l₀ _ (ϖ' l₀).2⟩ : ↥A) ^ E₀ = (v : ↥A) * ⟨π, hπP⟩ ^ w) ∧

          (∀ nd ∈ N,

            (bx nd).IsRational ∧ nd.IsRational ∧ (∀ P ∈ S nd, P.IsRational) ∧

            (∀ f : fieldBar q M', f ∈ 𝒩 nd ↔ f ∈ (Rx nd).integers ∧ f ∈ R.integers ∧ ∀ P ∈ S nd, f ∈ P.toValuationSubring) ∧
            (∀ f ∈ 𝒩 nd, ∀ P ∈ S nd, P.evalAt f ∈ A) ∧

            cx nd * cy nd = algebraMap (AlgebraicClosure ℚ) (fieldBar q M') ((ϖ' l₀ : ↥(C' l₀)) : AlgebraicClosure ℚ) ^ E₀ * cu nd ∧
            (∀ h₁ : cx nd ∈ (Rx nd).integers, (Rx nd).residue ⟨cx nd, h₁⟩ = 0) ∧
            (∀ h₂ : cx nd ∈ R.integers, nd.ord (R.residue ⟨cx nd, h₂⟩) = 1) ∧
            (∀ h₂ : cy nd ∈ R.integers, R.residue ⟨cy nd, h₂⟩ = 0) ∧
            (∀ h₁ : cy nd ∈ (Rx nd).integers, (bx nd).ord ((Rx nd).residue ⟨cy nd, h₁⟩) = 1) ∧

            (∀ τ ∈ A.inertiaSubgroupIn ℚ, A.tameCharacter π τ = 1 →
              let g := ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ
              (∀ P : Place (AlgebraicClosure ℚ) (fieldBar q M'), P ∈ S nd ↔ g • P ∈ S nd) ∧ g • cx nd = cx nd ∧ g • cy nd = cy nd) ∧

            (∀ f : fieldBar q M', ∃ (l : Λ) (a b : ↥(𝒩₀ nd l)), (b : fieldBar q M') ≠ 0 ∧ f * (b : fieldBar q M') = (a : fieldBar q M')) ∧

            (∀ f : fieldBar q M', ∃ (n : ℕ) (c : Fin n → AlgebraicClosure ℚ) (a : Fin n → ↥(𝒩₀ nd l₀)) (b : ↥(𝒩₀ nd l₀)),
              (b : fieldBar q M') ≠ 0 ∧ f * (b : fieldBar q M') = ∑ i, c i • ((a i : ↥(𝒩₀ nd l₀)) : fieldBar q M')) ∧

            (∀ l, letI : IsLocalRing ↥(𝒩₀ nd l) := hloc nd l;
              𝒩₀ nd l₀ ≤ 𝒩₀ nd l ∧ 𝒩₀ nd l ≤ 𝒩 nd ∧
              (∀ P : Place (AlgebraicClosure ℚ) (fieldBar q M'), P ∈ S nd ↔
                (∀ f : fieldBar q M', f ∈ 𝒩₀ nd l → f ∈ P.toValuationSubring) ∧
                (∀ f : ↥(𝒩₀ nd l), ¬ IsUnit f → ∃ h : P.evalAt (f : fieldBar q M') ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A)) ∧
              (∀ c : AlgebraicClosure ℚ, c ∈ C' l → algebraMap (AlgebraicClosure ℚ) (fieldBar q M') c ∈ 𝒩₀ nd l) ∧
              (∀ g : ↥(𝒩₀ nd l), ∃ (o : ↥(C' l)) (h : algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (o : AlgebraicClosure ℚ) ∈ 𝒩₀ nd l), ¬ IsUnit (g - ⟨_, h⟩)) ∧
              (∀ (n : ℕ) (c : Fin n → AlgebraicClosure ℚ) (a : Fin n → ↥(𝒩₀ nd l)), LinearIndependent ↥(C' l) c →
                ∑ i, c i • ((a i : ↥(𝒩₀ nd l)) : fieldBar q M') = 0 → ∀ i, a i = 0) ∧
              cx nd ∈ 𝒩₀ nd l ∧ cy nd ∈ 𝒩₀ nd l ∧ (∃ hu : cu nd ∈ 𝒩₀ nd l, IsUnit (⟨cu nd, hu⟩ : ↥(𝒩₀ nd l))) ∧
              ∃ (σ : Wc l →+* AdicCompletion (maximalIdeal ↥(𝒩₀ nd l)) ↥(𝒩₀ nd l))
                (ι : AdicCompletion (maximalIdeal ↥(𝒩₀ nd l)) ↥(𝒩₀ nd l) ≃+* UVCrossingModel (Wc l) (πW l ^ E l)),
                (∀ h : algebraMap (AlgebraicClosure ℚ) (fieldBar q M') ((ϖ' l : ↥(C' l)) : AlgebraicClosure ℚ) ∈ 𝒩₀ nd l,
                  σ (πW l) = algebraMap ↥(𝒩₀ nd l) (AdicCompletion (maximalIdeal ↥(𝒩₀ nd l)) ↥(𝒩₀ nd l)) ⟨_, h⟩) ∧
                (∀ o : Wc l, ι (σ o) = const (πW l ^ E l) o) ∧
                (∀ (c : ↥(C' l)) (h : algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (c : AlgebraicClosure ℚ) ∈ 𝒩₀ nd l),
                  ∃ o : Wc l, σ o = algebraMap ↥(𝒩₀ nd l) (AdicCompletion (maximalIdeal ↥(𝒩₀ nd l)) ↥(𝒩₀ nd l)) ⟨_, h⟩) ∧
                (∀ (f : ↥(𝒩₀ nd l)) (n : ℕ) (h₁ : f.1 ∈ (Rx nd).integers), (Rx nd).residue ⟨f.1, h₁⟩ ≠ 0 →
                  (bx nd).ord ((Rx nd).residue ⟨f.1, h₁⟩) = (n : ℤ) →
                    ∃ γ : UVCrossingModel (Wc l) (πW l ^ E l), IsUnit γ ∧
                      ι (algebraMap ↥(𝒩₀ nd l) (AdicCompletion (maximalIdeal ↥(𝒩₀ nd l)) ↥(𝒩₀ nd l)) f) - γ * V (πW l ^ E l) ^ n ∈
                        Ideal.span {const (πW l ^ E l) (πW l), U (πW l ^ E l)}) ∧
                (∀ (f : ↥(𝒩₀ nd l)) (n : ℕ) (h₂ : f.1 ∈ R.integers), R.residue ⟨f.1, h₂⟩ ≠ 0 →
                  nd.ord (R.residue ⟨f.1, h₂⟩) = (n : ℤ) →
                    ∃ γ : UVCrossingModel (Wc l) (πW l ^ E l), IsUnit γ ∧
                      ι (algebraMap ↥(𝒩₀ nd l) (AdicCompletion (maximalIdeal ↥(𝒩₀ nd l)) ↥(𝒩₀ nd l)) f) - γ * U (πW l ^ E l) ^ n ∈
                        Ideal.span {const (πW l ^ E l) (πW l), V (πW l ^ E l)}))) ∧

          (∀ nd ∈ N, ∀ nd' ∈ N, ∀ P, P ∈ S nd → P ∈ S nd' → nd = nd') ∧

          (∀ nd ∈ N, ∀ P ∈ S nd, ∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
            (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
              0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
            (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
                (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
              ∀ a : A, residue A a =
                  (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
                ∃ h : P.evalAt (IntermediateField.inclusion hle f : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A,
                  (⟨_, h⟩ : A) ∈ maximalIdeal A) ∧

          (∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → ∃ τN : Place (ResidueField A) FSS → Place (ResidueField A) FSS,
            ∀ nd ∈ N, τN nd ∈ N ∧
              (∀ P : Place (AlgebraicClosure ℚ) (fieldBar q M'), (levelAutBar q M' ζ' γ) • P ∈ S nd ↔ P ∈ S (τN nd)) ∧
              ((Rx nd).integers).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = (Rx (τN nd)).integers) ∧

          (∀ τ ∈ Subgroup.closure {τ : (fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] (fieldBar q M') |
                ∃ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ' γ},
            ∀ (hτ : ∀ f : fieldBar q M', τ f ∈ R.integers ↔ f ∈ R.integers), ∀ nd ∈ N,
              R.resAut τ hτ • nd ∈ N ∧
              AlgebraicCurve.RegularProlongation.smulDisc τ (S nd) = S (R.resAut τ hτ • nd)) ∧
          (∀ nd ∈ N, ∀ f : ↥(modularFunctionFieldBar M'), f ∈ R₀.integers →
            (IntermediateField.inclusion hle f : ↥(fieldBar q M')) ∈ (Rx nd).integers) ∧
          (∀ nd ∈ N, ∃ j : modularFunctionFieldC (ResidueField A) M' →+* FIx nd,
            (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
              ∃ hC : (IntermediateField.inclusion hle f : fieldBar q M') ∈ (Rx nd).integers,
                (Rx nd).residue ⟨_, hC⟩ = j (R₀.residue ⟨f, hf⟩)) ∧
            ∀ g : modularFunctionFieldC (ResidueField A) M',
              g ∈ (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring ↔
                j g ∈ (bx nd).toValuationSubring)) :
    ∀ nd ∈ N, ∃ An An' : Annulus A ↥(fieldBar q M'),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), P ∈ An.dom ↔ P ∈ S nd) ∧
      An'.dom = An.dom ∧ An'.modulus = An.modulus ∧
      (((An.modulus : ↥A) : AlgebraicClosure ℚ) = ((ϖ' l₀ : ↥(C' l₀)) : AlgebraicClosure ℚ) ^ E₀) ∧ (((An.modulus : ↥A) : AlgebraicClosure ℚ) ≠ 0) ∧
      An.param = cy nd ∧
      An'.param * An.param = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((An.modulus : ↥A) : AlgebraicClosure ℚ) ∧

      (∃ hz : An.param ∈ (Rx nd).integers, (bx nd).ord ((Rx nd).residue ⟨An.param, hz⟩) = 1 ∧
        ∀ (f : ↥(fieldBar q M')) (hf : f ∈ (Rx nd).integers), (Rx nd).residue ⟨f, hf⟩ ≠ 0 → (∀ P ∈ An.dom, P.ord f = 0) →
          ∀ P ∈ An.dom,
            ∃ h : P.evalAt f * (P.evalAt An.param) ^ (-((bx nd).ord ((Rx nd).residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧

      (∃ hz : An'.param ∈ R.integers, nd.ord (R.residue ⟨An'.param, hz⟩) = 1 ∧
        ∀ (f : ↥(fieldBar q M')) (hf : f ∈ R.integers), R.residue ⟨f, hf⟩ ≠ 0 → (∀ P ∈ An'.dom, P.ord f = 0) →
          ∀ P ∈ An'.dom,
            ∃ h : P.evalAt f * (P.evalAt An'.param) ^ (-(nd.ord (R.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧

      (∃ P ∈ An.dom, ∃ P' ∈ An.dom, A.valuation (P.evalAt An.param) ≠ A.valuation (P'.evalAt An.param)) ∧

      ((An.modulus : ↥A) ∈ maximalIdeal ↥A) := by
  classical
  intro nd hnd
  obtain ⟨hϖ', hl₀, hϖ0, halg, hπW, hE, -, -, hnode, -, -, -, -, -, -⟩ := hnodes
  obtain ⟨hbxr, hndr, hSr, h𝒩, hval, hxy, x_fst, x_snd, y_snd, y_fst, -, hgen, hgen₀, hlay⟩ := hnode nd hnd

  obtain ⟨hcurve, hfin⟩ :=
    ModularCurve.isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField (AlgebraicClosure ℚ) (q ^ 2 * M') (levelH q M')
  haveI : IsCurveOver (AlgebraicClosure ℚ) ↥(fieldBar q M') := hcurve
  haveI : Algebra.EssFiniteType (AlgebraicClosure ℚ) ↥(fieldBar q M') := hfin
  have hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n := by
    have hq1 : A.valuation ((q : ℕ) : AlgebraicClosure ℚ) < 1 := (ValuationSubring.mem_nonunits_iff A).mp hA
    haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
    have hMA : MulArchimedean A.ValueGroup :=
      ValuationSubring.mulArchimedean_valueGroup_of_isAlgebraic_of_valuation_natCast_lt_one A (Fact.out) hq1
    have key := (ValuationSubring.mulArchimedean_valueGroup_iff_forall_exists_pow_le A).mp hMA
    intro a b ha hb
    have hb' : (b : AlgebraicClosure ℚ) ≠ 0 := fun h => hb (Subtype.ext (by simpa using h))
    obtain ⟨n, hn⟩ := key (b : AlgebraicClosure ℚ) hb' a ha
    have hmem : (a : AlgebraicClosure ℚ) ^ n / b ∈ A := by
      rw [← ValuationSubring.valuation_le_one_iff, map_div₀]
      exact div_le_one_of_le₀ hn zero_le'
    refine ⟨n, ⟨(a : AlgebraicClosure ℚ) ^ n / b, hmem⟩, ?_⟩
    apply Subtype.ext
    show ((a ^ n : ↥A) : AlgebraicClosure ℚ) = (b : AlgebraicClosure ℚ) * ((a : AlgebraicClosure ℚ) ^ n / b)
    rw [mul_comm, div_mul_cancel₀ _ hb']
    simp

  haveI hLoc : ∀ l, IsLocalRing ↥(𝒩₀ nd l) := hloc nd
  haveI hNoe : ∀ l, IsNoetherianRing ↥(𝒩₀ nd l) := hnoe nd
  have hlay2 : ∀ l, ∃ (σ : Wc l →+* AdicCompletion (maximalIdeal ↥(𝒩₀ nd l)) ↥(𝒩₀ nd l))
      (ι : AdicCompletion (maximalIdeal ↥(𝒩₀ nd l)) ↥(𝒩₀ nd l) ≃+* UVCrossingModel (Wc l) (πW l ^ E l)),
      𝒩₀ nd l₀ ≤ 𝒩₀ nd l ∧ 𝒩₀ nd l ≤ 𝒩 nd ∧
      (∀ P : Place (AlgebraicClosure ℚ) (fieldBar q M'), P ∈ S nd ↔
        (∀ f : fieldBar q M', f ∈ 𝒩₀ nd l → f ∈ P.toValuationSubring) ∧
        (∀ f : ↥(𝒩₀ nd l), ¬ IsUnit f → ∃ h : P.evalAt (f : fieldBar q M') ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A)) ∧
      (∀ c : AlgebraicClosure ℚ, c ∈ C' l → algebraMap (AlgebraicClosure ℚ) (fieldBar q M') c ∈ 𝒩₀ nd l) ∧
      (∀ g : ↥(𝒩₀ nd l), ∃ (o : ↥(C' l)) (h : algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (o : AlgebraicClosure ℚ) ∈ 𝒩₀ nd l), ¬ IsUnit (g - ⟨_, h⟩)) ∧
      (∀ (n : ℕ) (c : Fin n → AlgebraicClosure ℚ) (a : Fin n → ↥(𝒩₀ nd l)), LinearIndependent ↥(C' l) c →
        ∑ i, c i • ((a i : ↥(𝒩₀ nd l)) : fieldBar q M') = 0 → ∀ i, a i = 0) ∧
      cx nd ∈ 𝒩₀ nd l ∧ cy nd ∈ 𝒩₀ nd l ∧ (∃ hu : cu nd ∈ 𝒩₀ nd l, IsUnit (⟨cu nd, hu⟩ : ↥(𝒩₀ nd l))) ∧
      (∀ h : algebraMap (AlgebraicClosure ℚ) (fieldBar q M') ((ϖ' l : ↥(C' l)) : AlgebraicClosure ℚ) ∈ 𝒩₀ nd l,
        σ (πW l) = algebraMap ↥(𝒩₀ nd l) (AdicCompletion (maximalIdeal ↥(𝒩₀ nd l)) ↥(𝒩₀ nd l)) ⟨_, h⟩) ∧
      (∀ o : Wc l, ι (σ o) = const (πW l ^ E l) o) ∧
      (∀ (c : ↥(C' l)) (h : algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (c : AlgebraicClosure ℚ) ∈ 𝒩₀ nd l),
        ∃ o : Wc l, σ o = algebraMap ↥(𝒩₀ nd l) (AdicCompletion (maximalIdeal ↥(𝒩₀ nd l)) ↥(𝒩₀ nd l)) ⟨_, h⟩) ∧
      (∀ (f : ↥(𝒩₀ nd l)) (n : ℕ) (h₁ : f.1 ∈ (Rx nd).integers), (Rx nd).residue ⟨f.1, h₁⟩ ≠ 0 →
        (bx nd).ord ((Rx nd).residue ⟨f.1, h₁⟩) = (n : ℤ) →
          ∃ γ : UVCrossingModel (Wc l) (πW l ^ E l), IsUnit γ ∧
            ι (algebraMap ↥(𝒩₀ nd l) (AdicCompletion (maximalIdeal ↥(𝒩₀ nd l)) ↥(𝒩₀ nd l)) f) - γ * V (πW l ^ E l) ^ n ∈
              Ideal.span {const (πW l ^ E l) (πW l), U (πW l ^ E l)}) ∧
      (∀ (f : ↥(𝒩₀ nd l)) (n : ℕ) (h₂ : f.1 ∈ R.integers), R.residue ⟨f.1, h₂⟩ ≠ 0 →
        nd.ord (R.residue ⟨f.1, h₂⟩) = (n : ℤ) →
          ∃ γ : UVCrossingModel (Wc l) (πW l ^ E l), IsUnit γ ∧
            ι (algebraMap ↥(𝒩₀ nd l) (AdicCompletion (maximalIdeal ↥(𝒩₀ nd l)) ↥(𝒩₀ nd l)) f) - γ * U (πW l ^ E l) ^ n ∈
              Ideal.span {const (πW l ^ E l) (πW l), V (πW l ^ E l)}) := by
    intro l
    obtain ⟨hmono, h𝒩₀, hS, hCmem, hres, hld, hxm, hym, hu, σ, ι, hσπ, hconst, hCW, hres₁, hres₂⟩ := hlay l
    exact ⟨σ, ι, hmono, h𝒩₀, hS, hCmem, hres, hld, hxm, hym, hu, hσπ, hconst, hCW, hres₁, hres₂⟩
  choose σ ι hL using hlay2
  have hmono : ∀ l, 𝒩₀ nd l₀ ≤ 𝒩₀ nd l := fun l => (hL l).1
  have h𝒩₀ : ∀ l, 𝒩₀ nd l ≤ 𝒩 nd := fun l => (hL l).2.1
  have hS := fun l => (hL l).2.2.1
  have hCmem := fun l => (hL l).2.2.2.1
  have hres := fun l => (hL l).2.2.2.2.1
  have hld := fun l => (hL l).2.2.2.2.2.1
  have hxm : ∀ l, cx nd ∈ 𝒩₀ nd l := fun l => (hL l).2.2.2.2.2.2.1
  have hym : ∀ l, cy nd ∈ 𝒩₀ nd l := fun l => (hL l).2.2.2.2.2.2.2.1
  have hu' := fun l => (hL l).2.2.2.2.2.2.2.2.1
  have hσπ := fun l => (hL l).2.2.2.2.2.2.2.2.2.1
  have hconst := fun l => (hL l).2.2.2.2.2.2.2.2.2.2.1
  have hCW := fun l => (hL l).2.2.2.2.2.2.2.2.2.2.2.1
  have hres₁ := fun l => (hL l).2.2.2.2.2.2.2.2.2.2.2.2.1
  have hres₂ := fun l => (hL l).2.2.2.2.2.2.2.2.2.2.2.2.2
  have hum : ∀ l, cu nd ∈ 𝒩₀ nd l := fun l => (hu' l).elim fun h _ => h
  have hu : ∀ l, IsUnit (⟨cu nd, hum l⟩ : ↥(𝒩₀ nd l)) := fun l => by obtain ⟨h, hh⟩ := hu' l; exact hh

  obtain ⟨hreg, hlaw⟩ :=
    AlgebraicCurve.NodeAnnulusEngine.ord_residue_nonneg_and_finsum_ord_eq_ord_residue_add_of_ringEquiv_uvCrossingModel_layers
      A (Rx nd) R (bx nd) nd (S nd) hSr (𝒩 nd) h𝒩 hval hrk hbxr hndr C' hC'A ϖ' hϖ' l₀ hl₀ hϖ0 halg
      (cx nd) (cy nd) (cu nd) E₀ hxy (𝒩₀ nd) h𝒩₀ hS hgen hmono hgen₀ hCmem
      (fun l g => by obtain ⟨o, h, hh⟩ := hres l g; exact ⟨o, hh⟩)
      hld hxm hym hum hu Wc πW hπW σ (fun l => hσπ l _) E hE ι hconst
      (fun l c => hCW l c _)
      (fun l f n hne hord => hres₁ l f n _ hne hord)
      (fun l f n hne hord => hres₂ l f n _ hne hord)
      x_fst x_snd y_snd y_fst

  have hord : ∀ (f : ↥(fieldBar q M')) (h₁ : f ∈ (Rx nd).integers) (h₂ : f ∈ R.integers),
      (Rx nd).residue ⟨f, h₁⟩ ≠ 0 → R.residue ⟨f, h₂⟩ ≠ 0 →
        {P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M') | P ∈ S nd ∧ P.ord f ≠ 0}.Finite ∧
        ∑ᶠ P ∈ S nd, P.ord f = (bx nd).ord ((Rx nd).residue ⟨f, h₁⟩) + nd.ord (R.residue ⟨f, h₂⟩) := by
    intro f h₁ h₂ hne₁ hne₂
    have h₁' : (1 : AlgebraicClosure ℚ) • f ∈ (Rx nd).integers := by rwa [one_smul]
    have h₂' : (1 : AlgebraicClosure ℚ) • f ∈ R.integers := by rwa [one_smul]
    have e₁ : (⟨(1 : AlgebraicClosure ℚ) • f, h₁'⟩ : ↥(Rx nd).integers) = ⟨f, h₁⟩ := Subtype.ext (one_smul _ _)
    have e₂ : (⟨(1 : AlgebraicClosure ℚ) • f, h₂'⟩ : ↥R.integers) = ⟨f, h₂⟩ := Subtype.ext (one_smul _ _)
    have := hlaw f 1 1 h₁' h₂' (by rw [e₁]; exact hne₁) (by rw [e₂]; exact hne₂)
    rw [e₁, e₂] at this
    exact this

  have hxy₀ : (⟨cx nd, hxm l₀⟩ : ↥(𝒩₀ nd l₀)) * ⟨cy nd, hym l₀⟩ =
      ⟨algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((ϖ' l₀ : ↥(C' l₀)) : AlgebraicClosure ℚ), hCmem l₀ _ (ϖ' l₀).2⟩ ^ E₀ *
        ⟨cu nd, hum l₀⟩ := by
    apply Subtype.ext
    simp only [Subring.coe_mul, SubmonoidClass.coe_pow, map_pow]
    exact hxy

  obtain ⟨An, An', hdomS, hdom, hmod, hmodϖ, hmod0, hparam, hrec, hfar, hnear⟩ :=
    AlgebraicCurve.exists_annulusPair_isAttached_of_ringEquiv_uvCrossingModel_of_nodeCoordinates
      A (Rx nd) R (bx nd) nd (S nd) hSr (𝒩 nd) h𝒩 hval hreg hord (𝒩₀ nd l₀) (h𝒩₀ l₀) (hS l₀) hgen₀
      (C' l₀) (hC'A l₀) (hCmem l₀) (ϖ' l₀) (hϖ' l₀) hϖ0 halg hrk hbxr hndr
      (fun g => by obtain ⟨o, h, hh⟩ := hres l₀ g; exact ⟨o, hh⟩)
      (πW l₀) (hπW l₀) (σ l₀) (hσπ l₀ _) (E l₀) (hE l₀) (ι l₀) (hconst l₀)
      (fun f n hne hord' => hres₁ l₀ f n _ hne hord')
      (fun f n hne hord' => hres₂ l₀ f n _ hne hord')
      ⟨cx nd, hxm l₀⟩ ⟨cy nd, hym l₀⟩ (x_fst _) (x_snd _) (y_snd _) (y_fst _) E₀ ⟨cu nd, hum l₀⟩ (hu l₀) hxy₀
  refine ⟨An, An', hdomS, hdom, hmod, hmodϖ, hmod0, hparam, hrec, hfar, hnear, ?_, An.modulus_mem⟩

  obtain ⟨c₁, c₂, hc₁, hc₂, hc₁0, hc₂0, hd₁, hd₂, hne⟩ :=
    ValuationSubring.exists_two_mem_maximalIdeal_dvd_valuation_ne_of_isAlgClosed A An.modulus An.modulus_mem hmod0
  obtain ⟨P₁, ⟨hP₁, hP₁v⟩, -⟩ := An.existsUnique_evalAt_eq c₁ hc₁ hc₁0 hd₁
  obtain ⟨P₂, ⟨hP₂, hP₂v⟩, -⟩ := An.existsUnique_evalAt_eq c₂ hc₂ hc₂0 hd₂
  exact ⟨P₁, hP₁, P₂, hP₂, by rw [hP₁v, hP₂v]; exact hne⟩

end S_ModularCurve_FullLevel_supersingularProlongation_exists_annulusPair_of_nodePresentation_of_eq_two_of_dvd
end P2MW
export P2MW.S_ModularCurve_FullLevel_supersingularProlongation_exists_annulusPair_of_nodePresentation_of_eq_two_of_dvd (solution)
