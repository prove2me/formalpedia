-- Prove2me | solution 1 for ModularCurve.FullLevel.supersingularProlongation_exists_crossUnit_nodePlaces_of_sep
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/41ec3e22-7d4f-5740-ac47-5e24e6725dd5

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
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Theorems.Thm_ModularCurve_FullLevel_supersingularProlongation_exists_annulusPair_of_nodePresentation
import Theorems.Thm_AlgebraicCurve_NodeAnnulusEngine_ord_residue_nonneg_and_finsum_ord_eq_ord_residue_add_of_ringEquiv_uvCrossingModel_layers
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_ValuationSubring_mulArchimedean_valueGroup_of_isAlgebraic_of_valuation_natCast_lt_one
import Theorems.Thm_ValuationSubring_mulArchimedean_valueGroup_iff_forall_exists_pow_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_supersingularProlongation_exists_crossUnit_nodePlaces_of_sep
p2m_attr_erase "instance" "AlgebraicCurve.GaussReduction.isLocalHom_constToGauss AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt instTopologicallyFGOfFiniteType AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup ModularCurve.UVCrossingModel
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

namespace Ws33
namespace C2e

theorem ord_eq_zero_of_evalAt_ne_zero {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    {f : F} (hf : f ∈ v.toValuationSubring) (hne : v.evalAt f ≠ 0) : v.ord f = 0 := by
  have hunit : IsUnit (⟨f, hf⟩ : ↥v.toValuationSubring) := by
    by_contra hnu
    apply hne
    have hmax : (⟨f, hf⟩ : ↥v.toValuationSubring) ∈ maximalIdeal ↥v.toValuationSubring :=
      (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have h0 : IsLocalRing.residue ↥v.toValuationSubring ⟨f, hf⟩ = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).mpr hmax
    rw [v.evalAt_of_mem hf, h0, ← map_zero (algebraMap K v.ResidueField), v.residueInv_algebraMap]
  obtain ⟨w, hw⟩ := hunit
  rw [show f = ((w : ↥v.toValuationSubring) : F) from congrArg Subtype.val hw.symm]
  exact v.ord_coe_unit w

theorem evalAt_ne_zero_of_mul_eq_one {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring)
    (hfg : f * g = 1) : v.evalAt f ≠ 0 := by
  intro h0
  have h1 : v.evalAt (f * g) = 1 := by rw [hfg, Place.evalAt_one]
  rw [v.evalAt_mul_of_mem hv hf hg, h0, zero_mul] at h1
  exact zero_ne_one h1

end Ws33.C2e

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

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
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπP : π ∈ A)

    (FSS : Type) [Field FSS] [Algebra (ResidueField A) FSS]
    (R : RegularProlongation A (fieldBar q M') FSS)
    (N : Finset (Place (ResidueField ↥A) FSS))
    (Sx : Place (ResidueField ↥A) FSS → Subring ↥(fieldBar q M'))
    (φx : (Q : Place (ResidueField ↥A) FSS) → (Polynomial ↥A →+* ↥(Sx Q)))
    (χ₀x : (Q : Place (ResidueField ↥A) FSS) → (↥(Sx Q) →+* ResidueField ↥A))
    (Dx : Place (ResidueField ↥A) FSS → Set (Place (AlgebraicClosure ℚ) ↥(fieldBar q M')))
    (h0 : (∃ t : FSS, Transcendental (ResidueField A) t))
    (h1 : (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
        (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
        (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
          ∃ hC : (IntermediateField.inclusion hle f : fieldBar q M') ∈ R.integers,
            R.residue ⟨_, hC⟩ = algebraMap (ResidueField A) FSS
              ((s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt
                (R₀.residue ⟨f, hf⟩))))
    (h2 : (∀ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
        R.integers.comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom = R.integers))
    (hcard : N.card = q + 1)
    (hpkg : (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N →

          (∀ a : ↥A, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a : (AlgebraicClosure ℚ)) ∈ Sx Q) ∧
          (φx Q).FormallySmooth ∧ (φx Q).FormallyUnramified ∧
          (∀ a : ↥A, ((φx Q (Polynomial.C a) : ↥(Sx Q)) : ↥(fieldBar q M')) = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a : (AlgebraicClosure ℚ))) ∧
          (∀ a : ↥A, χ₀x Q (φx Q (Polynomial.C a)) = IsLocalRing.residue ↥A a) ∧
          χ₀x Q (φx Q Polynomial.X) = 0 ∧
          (∀ c : ↥A, IsLocalRing.residue ↥A c = 0 →
            ∃! χ : ↥(Sx Q) →+* ↥A, (∀ a : ↥A, χ (φx Q (Polynomial.C a)) = a) ∧
              (∀ f : ↥(Sx Q), IsLocalRing.residue ↥A (χ f) = χ₀x Q f) ∧ χ (φx Q Polynomial.X) = c) ∧
          (∀ f : ↥(Sx Q), ∃ hR : (f : ↥(fieldBar q M')) ∈ R.integers, ∃ hm : R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ Q.toValuationSubring,
            IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : ↥(fieldBar q M')), hR⟩, hm⟩ =
              algebraMap (ResidueField ↥A) Q.ResidueField (χ₀x Q f)) ∧
          (∃ hR : ((φx Q Polynomial.X : ↥(Sx Q)) : ↥(fieldBar q M')) ∈ R.integers,
            Q.ord (R.residue ⟨((φx Q Polynomial.X : ↥(Sx Q)) : ↥(fieldBar q M')), hR⟩) = 1) ∧
          (∀ P, P ∈ Dx Q ↔ (P.IsRational ∧ (∀ f : ↥(Sx Q), (f : ↥(fieldBar q M')) ∈ P.toValuationSubring ∧ P.evalAt (f : ↥(fieldBar q M')) ∈ A) ∧
            (∀ f : ↥(Sx Q), A.valuation (P.evalAt (f : ↥(fieldBar q M'))) < 1 ↔ χ₀x Q f = 0))) ∧
          (∀ χ : ↥(Sx Q) →+* ↥A, (∀ a : ↥A, χ (φx Q (Polynomial.C a)) = a) →
            (∀ f : ↥(Sx Q), IsLocalRing.residue ↥A (χ f) = χ₀x Q f) →
            ∃! P, P ∈ Dx Q ∧ ∀ f : ↥(Sx Q), P.evalAt (f : ↥(fieldBar q M')) = ((χ f : ↥A) : (AlgebraicClosure ℚ))) ∧
          (∀ P ∈ Dx Q, ∀ f : ↥(fieldBar q M'), f ∈ P.toValuationSubring ↔
            ∃ g h : ↥(Sx Q), P.evalAt (h : ↥(fieldBar q M')) ≠ 0 ∧ f * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M'))) ∧
          (∀ f : ↥(fieldBar q M'), f ≠ 0 → (∀ P ∈ Dx Q, P.ord f = 0) →
            ∃ (c : (AlgebraicClosure ℚ)) (u : (↥(Sx Q))ˣ), c ≠ 0 ∧ algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') c * f = ((u : ↥(Sx Q)) : ↥(fieldBar q M'))) ∧
          (∀ f : ↥(fieldBar q M'), f ∈ R.integers → (∀ P ∈ Dx Q, f ∈ P.toValuationSubring) → f ∈ Sx Q)))
    (hdisj : (∀ Q Q' : Place (ResidueField ↥A) FSS, Q ∉ N → Q' ∉ N → ∀ P, P ∈ Dx Q → P ∈ Dx Q' → Q = Q'))
    (hcusp : (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N → ∀ P ∈ Dx Q, 0 ≤ P.ord (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
              ↥(modularFunctionFieldBar M')) : fieldBar q M')))
    (heqv : (∀ τ ∈ Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
            ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ},
          ∀ (hτ : ∀ f : ↥(fieldBar q M'), τ f ∈ R.integers ↔ f ∈ R.integers) (Q : Place (ResidueField ↥A) FSS),
            (R.resAut τ hτ • Q ∈ N ↔ Q ∈ N) ∧
            (Q ∉ N → AlgebraicCurve.RegularProlongation.smulDisc τ (Dx Q) = Dx (R.resAut τ hτ • Q))))

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
                j g ∈ (bx nd).toValuationSubring))

    (hSEP2 : (∀ x ∈ N, ∀ x' ∈ N, x ≠ x' →
            ∃ (g : ↥(fieldBar q M')) (hgx : g ∈ 𝒩₀ x l₀) (hcx : cx x ∈ 𝒩₀ x l₀) (hgx' : g ∈ 𝒩₀ x' l₀),
              (∃ u : (↥(𝒩₀ x l₀))ˣ, (⟨g, hgx⟩ : ↥(𝒩₀ x l₀)) = ⟨cx x, hcx⟩ * (u : ↥(𝒩₀ x l₀))) ∧
              IsUnit (⟨g, hgx'⟩ : ↥(𝒩₀ x' l₀)))) :
          (∀ x ∈ N, ∀ x' ∈ N, x ≠ x' →
            ∃ (g : ↥(fieldBar q M')) (hg : g ∈ R.integers), R.residue ⟨g, hg⟩ ≠ 0 ∧ x.ord (R.residue ⟨g, hg⟩) ≠ 0 ∧
              (∀ P ∈ S x, P.ord g = 0) ∧
              (∀ P ∈ S x', g ∈ P.toValuationSubring ∧ ∃ h : P.evalAt g ∈ A, IsUnit (⟨_, h⟩ : ↥A))) := by
  classical
  intro x hx x' hx' hxx'

  have hPair := ModularCurve.FullLevel.supersingularProlongation_exists_annulusPair_of_nodePresentation
    q hq M' hqM' A hA W hW hle R₀ hR₀ s π hπ hπP FSS R N FIx Rx bx Λ C' hC'A ϖ' l₀ Wc πW E E₀ S 𝒩 𝒩₀ hloc hnoe cx cy cu hnodes x hx
  obtain ⟨An, An', hdomS, hdom, -, hmodϖ, hmod0, hparam, hrec, -, -, -, -⟩ := hPair
  obtain ⟨hϖ', hl₀, hϖ0, halg, hπW, hE, -, -, hnode, -⟩ := hnodes
  obtain ⟨hbxr, hndr, hSr, h𝒩, hval, hxy, x_fst, x_snd, y_snd, y_fst, -, hgen, hgen₀, hlay⟩ := hnode x hx
  obtain ⟨-, -, hSr', h𝒩', hval', -, -, -, -, -, -, -, -, hlay'⟩ := hnode x' hx'
  obtain ⟨-, h𝒩₀', hS', -⟩ := hlay' l₀
  haveI hLoc : ∀ l, IsLocalRing ↥(𝒩₀ x l) := hloc x
  haveI hNoe : ∀ l, IsNoetherianRing ↥(𝒩₀ x l) := hnoe x
  haveI : IsLocalRing ↥(𝒩₀ x' l₀) := hloc x' l₀

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

  have hlay2 : ∀ l, ∃ (σ : Wc l →+* AdicCompletion (maximalIdeal ↥(𝒩₀ x l)) ↥(𝒩₀ x l))
      (ι : AdicCompletion (maximalIdeal ↥(𝒩₀ x l)) ↥(𝒩₀ x l) ≃+* UVCrossingModel (Wc l) (πW l ^ E l)),
      𝒩₀ x l₀ ≤ 𝒩₀ x l ∧ 𝒩₀ x l ≤ 𝒩 x ∧
      (∀ P : Place (AlgebraicClosure ℚ) (fieldBar q M'), P ∈ S x ↔
        (∀ f : fieldBar q M', f ∈ 𝒩₀ x l → f ∈ P.toValuationSubring) ∧
        (∀ f : ↥(𝒩₀ x l), ¬ IsUnit f → ∃ h : P.evalAt (f : fieldBar q M') ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A)) ∧
      (∀ c : AlgebraicClosure ℚ, c ∈ C' l → algebraMap (AlgebraicClosure ℚ) (fieldBar q M') c ∈ 𝒩₀ x l) ∧
      (∀ g : ↥(𝒩₀ x l), ∃ (o : ↥(C' l)) (h : algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (o : AlgebraicClosure ℚ) ∈ 𝒩₀ x l), ¬ IsUnit (g - ⟨_, h⟩)) ∧
      (∀ (n : ℕ) (c : Fin n → AlgebraicClosure ℚ) (a : Fin n → ↥(𝒩₀ x l)), LinearIndependent ↥(C' l) c →
        ∑ i, c i • ((a i : ↥(𝒩₀ x l)) : fieldBar q M') = 0 → ∀ i, a i = 0) ∧
      cx x ∈ 𝒩₀ x l ∧ cy x ∈ 𝒩₀ x l ∧ (∃ hu : cu x ∈ 𝒩₀ x l, IsUnit (⟨cu x, hu⟩ : ↥(𝒩₀ x l))) ∧
      (∀ h : algebraMap (AlgebraicClosure ℚ) (fieldBar q M') ((ϖ' l : ↥(C' l)) : AlgebraicClosure ℚ) ∈ 𝒩₀ x l,
        σ (πW l) = algebraMap ↥(𝒩₀ x l) (AdicCompletion (maximalIdeal ↥(𝒩₀ x l)) ↥(𝒩₀ x l)) ⟨_, h⟩) ∧
      (∀ o : Wc l, ι (σ o) = const (πW l ^ E l) o) ∧
      (∀ (c : ↥(C' l)) (h : algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (c : AlgebraicClosure ℚ) ∈ 𝒩₀ x l),
        ∃ o : Wc l, σ o = algebraMap ↥(𝒩₀ x l) (AdicCompletion (maximalIdeal ↥(𝒩₀ x l)) ↥(𝒩₀ x l)) ⟨_, h⟩) ∧
      (∀ (f : ↥(𝒩₀ x l)) (n : ℕ) (h₁ : f.1 ∈ (Rx x).integers), (Rx x).residue ⟨f.1, h₁⟩ ≠ 0 →
        (bx x).ord ((Rx x).residue ⟨f.1, h₁⟩) = (n : ℤ) →
          ∃ γ : UVCrossingModel (Wc l) (πW l ^ E l), IsUnit γ ∧
            ι (algebraMap ↥(𝒩₀ x l) (AdicCompletion (maximalIdeal ↥(𝒩₀ x l)) ↥(𝒩₀ x l)) f) - γ * V (πW l ^ E l) ^ n ∈
              Ideal.span {const (πW l ^ E l) (πW l), U (πW l ^ E l)}) ∧
      (∀ (f : ↥(𝒩₀ x l)) (n : ℕ) (h₂ : f.1 ∈ R.integers), R.residue ⟨f.1, h₂⟩ ≠ 0 →
        x.ord (R.residue ⟨f.1, h₂⟩) = (n : ℤ) →
          ∃ γ : UVCrossingModel (Wc l) (πW l ^ E l), IsUnit γ ∧
            ι (algebraMap ↥(𝒩₀ x l) (AdicCompletion (maximalIdeal ↥(𝒩₀ x l)) ↥(𝒩₀ x l)) f) - γ * U (πW l ^ E l) ^ n ∈
              Ideal.span {const (πW l ^ E l) (πW l), V (πW l ^ E l)}) := by
    intro l
    obtain ⟨hmono, h𝒩₀, hS, hCmem, hres, hld, hxm, hym, hu, σ, ι, hσπ, hconst, hCW, hres₁, hres₂⟩ := hlay l
    exact ⟨σ, ι, hmono, h𝒩₀, hS, hCmem, hres, hld, hxm, hym, hu, hσπ, hconst, hCW, hres₁, hres₂⟩
  choose σ ι hL using hlay2
  have hmono : ∀ l, 𝒩₀ x l₀ ≤ 𝒩₀ x l := fun l => (hL l).1
  have h𝒩₀ : ∀ l, 𝒩₀ x l ≤ 𝒩 x := fun l => (hL l).2.1
  have hS := fun l => (hL l).2.2.1
  have hCmem := fun l => (hL l).2.2.2.1
  have hres := fun l => (hL l).2.2.2.2.1
  have hld := fun l => (hL l).2.2.2.2.2.1
  have hxm : ∀ l, cx x ∈ 𝒩₀ x l := fun l => (hL l).2.2.2.2.2.2.1
  have hym : ∀ l, cy x ∈ 𝒩₀ x l := fun l => (hL l).2.2.2.2.2.2.2.1
  have hu' := fun l => (hL l).2.2.2.2.2.2.2.2.1
  have hσπ := fun l => (hL l).2.2.2.2.2.2.2.2.2.1
  have hconst := fun l => (hL l).2.2.2.2.2.2.2.2.2.2.1
  have hCW := fun l => (hL l).2.2.2.2.2.2.2.2.2.2.2.1
  have hres₁ := fun l => (hL l).2.2.2.2.2.2.2.2.2.2.2.2.1
  have hres₂ := fun l => (hL l).2.2.2.2.2.2.2.2.2.2.2.2.2
  have hum : ∀ l, cu x ∈ 𝒩₀ x l := fun l => (hu' l).elim fun h _ => h
  have hu : ∀ l, IsUnit (⟨cu x, hum l⟩ : ↥(𝒩₀ x l)) := fun l => by obtain ⟨h, hh⟩ := hu' l; exact hh

  obtain ⟨hreg, -⟩ :=
    AlgebraicCurve.NodeAnnulusEngine.ord_residue_nonneg_and_finsum_ord_eq_ord_residue_add_of_ringEquiv_uvCrossingModel_layers
      A (Rx x) R (bx x) x (S x) hSr (𝒩 x) h𝒩 hval hrk hbxr hndr C' hC'A ϖ' hϖ' l₀ hl₀ hϖ0 halg
      (cx x) (cy x) (cu x) E₀ hxy (𝒩₀ x) h𝒩₀ hS hgen hmono hgen₀ hCmem
      (fun l g => by obtain ⟨o, h, hh⟩ := hres l g; exact ⟨o, hh⟩)
      hld hxm hym hum hu Wc πW hπW σ (fun l => hσπ l _) E hE ι hconst
      (fun l c => hCW l c _)
      (fun l f n hne hord => hres₁ l f n _ hne hord)
      (fun l f n hne hord => hres₂ l f n _ hne hord)
      x_fst x_snd y_snd y_fst

  obtain ⟨g, hg𝒩₀, hcx𝒩₀, hg', ⟨u, hgu⟩, hgunit'⟩ := hSEP2 x hx x' hx' hxx'
  have hgeq : g = cx x * ((u : ↥(𝒩₀ x l₀)) : ↥(fieldBar q M')) := by
    have := congrArg Subtype.val hgu
    simpa using this
  have hmem𝒩 : ∀ f : ↥(fieldBar q M'), f ∈ 𝒩₀ x l₀ → f ∈ (Rx x).integers ∧ f ∈ R.integers ∧ ∀ P ∈ S x, f ∈ P.toValuationSubring :=
    fun f hf => (h𝒩 f).mp (h𝒩₀ l₀ hf)
  have huR : ((u : ↥(𝒩₀ x l₀)) : ↥(fieldBar q M')) ∈ R.integers := (hmem𝒩 _ (u : ↥(𝒩₀ x l₀)).2).2.1
  have huiR : ((u⁻¹ : (↥(𝒩₀ x l₀))ˣ) : ↥(𝒩₀ x l₀)).1 ∈ R.integers := (hmem𝒩 _ ((u⁻¹ : (↥(𝒩₀ x l₀))ˣ) : ↥(𝒩₀ x l₀)).2).2.1
  have hcxR : cx x ∈ R.integers := (hmem𝒩 _ hcx𝒩₀).2.1
  have hgR : g ∈ R.integers := by rw [hgeq]; exact mul_mem hcxR huR

  have huu : ((u : ↥(𝒩₀ x l₀)) : ↥(fieldBar q M')) * ((u⁻¹ : (↥(𝒩₀ x l₀))ˣ) : ↥(𝒩₀ x l₀)).1 = 1 := by
    have h := congrArg Subtype.val u.mul_inv
    rw [MulMemClass.coe_mul, OneMemClass.coe_one] at h
    exact h
  have hresu_mul : R.residue ⟨_, huR⟩ * R.residue ⟨_, huiR⟩ = 1 := by
    rw [← map_mul, ← map_one R.residue]; congr 1; exact Subtype.ext huu
  have hune : R.residue ⟨_, huR⟩ ≠ 0 := fun h0 => by rw [h0, zero_mul] at hresu_mul; exact zero_ne_one hresu_mul
  have huine : R.residue ⟨_, huiR⟩ ≠ 0 := fun h0 => by rw [h0, mul_zero] at hresu_mul; exact zero_ne_one hresu_mul
  have hordu : x.ord (R.residue ⟨_, huR⟩) = 0 := by
    have h1 := (hreg _ (hmem𝒩 _ (u : ↥(𝒩₀ x l₀)).2).1 huR (h𝒩₀ l₀ (u : ↥(𝒩₀ x l₀)).2)).2 hune
    have h2 := (hreg _ (hmem𝒩 _ ((u⁻¹ : (↥(𝒩₀ x l₀))ˣ) : ↥(𝒩₀ x l₀)).2).1 huiR (h𝒩₀ l₀ ((u⁻¹ : (↥(𝒩₀ x l₀))ˣ) : ↥(𝒩₀ x l₀)).2)).2 huine
    have h3 : x.ord (R.residue ⟨_, huR⟩) + x.ord (R.residue ⟨_, huiR⟩) = 0 := by
      rw [← Place.ord_mul _ hune huine, hresu_mul, Place.ord_one]
    linarith
  have hcxres : R.residue ⟨cx x, hcxR⟩ ≠ 0 := by
    intro h0
    have := x_snd hcxR
    rw [h0, Place.ord_zero] at this
    exact zero_ne_one this
  have hgres : R.residue ⟨g, hgR⟩ = R.residue ⟨cx x, hcxR⟩ * R.residue ⟨_, huR⟩ := by
    rw [← map_mul]; congr 1; exact Subtype.ext hgeq
  refine ⟨g, hgR, ?_, ?_, ?_, ?_⟩
  · rw [hgres]; exact mul_ne_zero hcxres hune
  · rw [hgres, Place.ord_mul _ hcxres hune, x_snd hcxR, hordu]; norm_num
  ·
    intro P hP
    have hPdom : P ∈ An.dom := (hdomS P).mpr hP
    have hPdom' : P ∈ An'.dom := by rw [hdom]; exact hPdom
    obtain ⟨hPrat, hzP, -, hz0, -⟩ := An.mem_dom P hPdom
    obtain ⟨-, hz'P, -, hz'0, -⟩ := An'.mem_dom P hPdom'
    obtain ⟨hS𝒪, -⟩ := (hS l₀ P).mp hP
    rw [hparam] at hzP hz0
    have hcy0 : cy x ≠ 0 := by
      intro h; apply hz0
      rw [h, ← map_zero (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')), Place.evalAt_algebraMap_eq]

    have hmodmap : algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((An.modulus : ↥A) : AlgebraicClosure ℚ) =
        algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((ϖ' l₀ : ↥(C' l₀)) : AlgebraicClosure ℚ) ^ E₀ := by
      rw [hmodϖ, map_pow]
    have hfac : cx x = An'.param * cu x := by
      apply mul_right_cancel₀ hcy0
      calc cx x * cy x = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((ϖ' l₀ : ↥(C' l₀)) : AlgebraicClosure ℚ) ^ E₀ * cu x := hxy
        _ = An'.param * An.param * cu x := by rw [hrec, hmodmap]
        _ = An'.param * cu x * cy x := by rw [hparam]; ring

    have hu𝒪 : ((u : ↥(𝒩₀ x l₀)) : ↥(fieldBar q M')) ∈ P.toValuationSubring := hS𝒪 _ (u : ↥(𝒩₀ x l₀)).2
    have hui𝒪 : ((u⁻¹ : (↥(𝒩₀ x l₀))ˣ) : ↥(𝒩₀ x l₀)).1 ∈ P.toValuationSubring := hS𝒪 _ ((u⁻¹ : (↥(𝒩₀ x l₀))ˣ) : ↥(𝒩₀ x l₀)).2
    have hcu𝒪 : cu x ∈ P.toValuationSubring := hS𝒪 _ (hum l₀)
    obtain ⟨wcu, hwcu⟩ := hu l₀
    have hcui𝒪 : ((wcu⁻¹ : (↥(𝒩₀ x l₀))ˣ) : ↥(𝒩₀ x l₀)).1 ∈ P.toValuationSubring := hS𝒪 _ ((wcu⁻¹ : (↥(𝒩₀ x l₀))ˣ) : ↥(𝒩₀ x l₀)).2
    have hcucu : cu x * ((wcu⁻¹ : (↥(𝒩₀ x l₀))ˣ) : ↥(𝒩₀ x l₀)).1 = 1 := by
      have h := congrArg Subtype.val wcu.mul_inv
      rw [MulMemClass.coe_mul, OneMemClass.coe_one, hwcu] at h
      exact h
    have hordz' : P.ord An'.param = 0 := Ws33.C2e.ord_eq_zero_of_evalAt_ne_zero P hz'P hz'0
    have hordcu : P.ord (cu x) = 0 :=
      Ws33.C2e.ord_eq_zero_of_evalAt_ne_zero P hcu𝒪 (Ws33.C2e.evalAt_ne_zero_of_mul_eq_one P hPrat hcu𝒪 hcui𝒪 hcucu)
    have hordu : P.ord ((u : ↥(𝒩₀ x l₀)) : ↥(fieldBar q M')) = 0 :=
      Ws33.C2e.ord_eq_zero_of_evalAt_ne_zero P hu𝒪 (Ws33.C2e.evalAt_ne_zero_of_mul_eq_one P hPrat hu𝒪 hui𝒪 huu)
    have hz'ne : An'.param ≠ 0 := fun h => hz'0 (by rw [h, ← map_zero (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')), Place.evalAt_algebraMap_eq])
    have hcune : cu x ≠ 0 := fun h => by rw [h, zero_mul] at hcucu; exact zero_ne_one hcucu
    have hune' : ((u : ↥(𝒩₀ x l₀)) : ↥(fieldBar q M')) ≠ 0 := fun h => by rw [h, zero_mul] at huu; exact zero_ne_one huu
    rw [hgeq, hfac, Place.ord_mul _ (mul_ne_zero hz'ne hcune) hune', Place.ord_mul _ hz'ne hcune, hordz', hordcu, hordu]
    norm_num
  ·
    intro P hP
    obtain ⟨hS𝒪', -⟩ := (hS' P).mp hP
    have hgP : g ∈ P.toValuationSubring := hS𝒪' g hg'
    obtain ⟨w, hw⟩ := hgunit'
    have hwinv : ((w⁻¹ : (↥(𝒩₀ x' l₀))ˣ) : ↥(𝒩₀ x' l₀)).1 ∈ P.toValuationSubring := hS𝒪' _ ((w⁻¹ : (↥(𝒩₀ x' l₀))ˣ) : ↥(𝒩₀ x' l₀)).2
    have hPrat : P.IsRational := hSr' P hP
    have hgA : P.evalAt g ∈ A := hval' g (h𝒩₀' hg') P hP
    have hgiA : P.evalAt ((w⁻¹ : (↥(𝒩₀ x' l₀))ˣ) : ↥(𝒩₀ x' l₀)).1 ∈ A := hval' _ (h𝒩₀' ((w⁻¹ : (↥(𝒩₀ x' l₀))ˣ) : ↥(𝒩₀ x' l₀)).2) P hP
    have hprod : g * ((w⁻¹ : (↥(𝒩₀ x' l₀))ˣ) : ↥(𝒩₀ x' l₀)).1 = 1 := by
      have := congrArg Subtype.val w.mul_inv
      rw [hw] at this
      simpa using this
    refine ⟨hgP, hgA, isUnit_iff_exists_inv.mpr ⟨⟨_, hgiA⟩, Subtype.ext ?_⟩⟩
    show P.evalAt g * P.evalAt _ = 1
    rw [← P.evalAt_mul_of_mem hPrat hgP hwinv, hprod, Place.evalAt_one]

end S_ModularCurve_FullLevel_supersingularProlongation_exists_crossUnit_nodePlaces_of_sep
end P2MW
export P2MW.S_ModularCurve_FullLevel_supersingularProlongation_exists_crossUnit_nodePlaces_of_sep (solution)
