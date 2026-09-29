-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_ringHom_chartAlgFin_isLevelAutAt_restrict_comp_eq_of_isLevelAutAt_cyclotomic_rigidDataPow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/3c45b107-2aff-5be4-b4ec-cb12c26630d8

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_EllipticCurve_WeilPairingFun
import Theorems.Thm_ModularCurve_laurentBaseChange_eq_adjoin_image_coeffMap_and_exists_ringHom
import Theorems.Thm_ModularCurve_coeffMap_coeffEmb_of_ringHom
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0_of_exists_ringHom
import Theorems.Thm_ModularCurve_FullLevel_map_mem_chartAlgFin_of_isLevelAutAt_of_mem_Gamma0
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_restrict_coeffMap_of_isLevelAutAt
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_isLevelAutAt_unique_mul_one_of_exists_ringHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_ringHom_chartAlgFin_isLevelAutAt_restrict_comp_eq_of_isLevelAutAt_cyclotomic_rigidDataPow
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open CategoryTheory AlgebraicGeometry
open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups Classical

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

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

    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
      Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A)

    (ℓ' : ℕ) [Fact ℓ'.Prime] (hℓ'q : ℓ' ≠ q) (hℓ'3 : 3 ≤ ℓ') (hℓ'M' : ¬ ℓ' ∣ M')
    (ξ : ↥k₀) (hξ : IsPrimitiveRoot ξ (q * ℓ'))
    (hιξ : ∃ ι : ↥k₀ →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ')))
    (K : IntermediateField ↥k₀ (LaurentSeries ↥k₀))
    (hK : K = ModularCurve.laurentBaseChange ↥k₀
      (ModularCurve.xHFunctionField ((q * ℓ') ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ') M')))
    [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥K] [IsScalarTower ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries ↥k₀)) = ModularCurve.coeffEmb ↥k₀ ModularCurve.jq) [Fact (j ≠ 0)]

    (hℓ : ∀ (T : Type) [CommRing T] [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ' D →
        ModularCurve.IsLevelPStructure (C • W) ℓ' (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (𝒢 : GroupLaws ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    (hVC : ∀ (T : Type) [CommRing T] [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (hCO : ∀ (T T' : Type) [CommRing T] [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) T] [CommRing T'] [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) T'] (f : T →ₐ[↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ)

    (L₁ : Type) [Field L₁] [CharZero L₁] [IsCyclotomicExtension {q * ℓ'} ℚ L₁]
    (ζ₁ : L₁) (hζ₁ : IsPrimitiveRoot ζ₁ q)
    (ξ₁ : L₁) (hξ₁ : IsPrimitiveRoot ξ₁ (q * ℓ'))
    (K₁ : IntermediateField L₁ (LaurentSeries L₁))
    (hK₁ : K₁ = ModularCurve.laurentBaseChange L₁
      (ModularCurve.xHFunctionField ((q * ℓ') ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ') M')))
    (A₁ : Type) [CommRing A₁] [IsDomain A₁] [IsDiscreteValuationRing A₁] [Algebra A₁ L₁] [IsFractionRing A₁ L₁]
    (hA₁q : (q : A₁) ∈ IsLocalRing.maximalIdeal A₁) (hζA₁ : ∃ x : A₁, algebraMap A₁ L₁ x = ζ₁)
    [Algebra A₁ ↥K₁] [IsScalarTower A₁ L₁ ↥K₁]
    (j₁ : ↥K₁) (hj₁ : ((j₁ : LaurentSeries L₁)) = ModularCurve.coeffEmb L₁ ModularCurve.jq) [Fact (j₁ ≠ 0)]
    (ϖ₁ : A₁) (hϖ₁ : IsLocalRing.maximalIdeal A₁ = Ideal.span {ϖ₁})
    (z₁ : ↥(AlgebraicCurve.TwoChartIntegralModel A₁ (↥K₁) j₁))
    (ϖz₁ : (AlgebraicCurve.TwoChartIntegralModel A₁ (↥K₁) j₁).presheaf.stalk z₁)
    (hϖz₁ : ϖz₁ = ((AlgebraicCurve.TwoChartIntegralModel A₁ (↥K₁) j₁).presheaf.germ ⊤ z₁ trivial).hom
      (((AlgebraicCurve.TwoChartIntegralModel.toBase A₁ (↥K₁) j₁).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of A₁)).inv.hom ϖ₁)))
    (hz₁ : ϖz₁ ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A₁ (↥K₁) j₁).presheaf.stalk z₁))
    (y₁ : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A₁ (↥K₁) j₁))
    (hy₁ : (AlgebraicCurve.TwoChartIntegralModel.ιFin A₁ (↥K₁) j₁).base y₁ = z₁)
    (hss₁ : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₁ (↥K₁) j₁) →+* Ω),
      RingHom.ker φ = y₁.asIdeal →
        φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A₁ (↥K₁) j₁) ∈ ModularCurve.ssJSet q Ω)

    (ι : L₁ →+* ↥k₀) (hιξ₁ : ι ξ₁ = ξ)
    (hιA : ∀ a : A₁, ((ι (algebraMap A₁ L₁ a) : ↥k₀) : AlgebraicClosure ℚ) ∈ A)
    (hιA' : ∀ x : L₁, ((ι x : ↥k₀) : AlgebraicClosure ℚ) ∈ A → ∃ a : A₁, algebraMap A₁ L₁ a = x) :
    ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
      ∀ τ₁ : ↥K₁ ≃ₐ[L₁] ↥K₁, ModularCurve.FullLevel.IsLevelAutAt L₁ (q * ℓ') ξ₁ (q * ℓ') ((q * ℓ') ^ 2 * M')
          (ModularCurve.FullLevel.levelH (q * ℓ') M') γ⁻¹ K₁ τ₁ →
        ∀ hpres₁ : (∀ a : ↥K₁, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₁ (↥K₁) j₁) → τ₁ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₁ (↥K₁) j₁)),
          ∃ (c : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₁ (↥K₁) j₁) →+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j))
            (τ : ↥K ≃ₐ[↥k₀] ↥K)
            (_ : ModularCurve.FullLevel.IsLevelAutAt ↥k₀ (q * ℓ') ξ (q * ℓ') ((q * ℓ') ^ 2 * M')
              (ModularCurve.FullLevel.levelH (q * ℓ') M') γ⁻¹ K τ)
            (hpres : ∀ f : ↥K, f ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j → τ f ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j),
            (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₁ (↥K₁) j₁), (((c a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j)) : ↥K) : LaurentSeries ↥k₀) =
                ModularCurve.coeffMap ι (((a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₁ (↥K₁) j₁)) : ↥K₁) : LaurentSeries L₁)) ∧
            ((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) hpres).comp c =
              c.comp ((τ₁ : ↥K₁ →+* ↥K₁).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₁ (↥K₁) j₁) (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₁ (↥K₁) j₁) hpres₁) := by
  intro γ hγ0 τ₁ hτ₁ hpres₁
  classical

  obtain ⟨-, cK, hcK⟩ := ModularCurve.laurentBaseChange_eq_adjoin_image_coeffMap_and_exists_ringHom L₁ ↥k₀ ι
    (ModularCurve.xHFunctionField ((q * ℓ') ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ') M')) K₁ hK₁ K hK
  have hcKj : cK j₁ = j := by
    apply Subtype.ext
    rw [hcK, hj₁, hj, ModularCurve.coeffMap_coeffEmb_of_ringHom]

  let ιA : A₁ →+* ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) :=
    (ι.comp (algebraMap A₁ L₁)).codRestrict (A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toSubring (fun a => hιA a)
  have hιA_coe : ∀ a : A₁, ((ιA a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) : ↥k₀) = ι (algebraMap A₁ L₁ a) := fun a => rfl
  have hcKA : ∀ a : A₁, cK (algebraMap A₁ ↥K₁ a) = algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥K (ιA a) := by
    intro a
    apply Subtype.ext
    rw [hcK, IsScalarTower.algebraMap_apply A₁ L₁ ↥K₁, IsScalarTower.algebraMap_apply ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥K]
    show ModularCurve.coeffMap ι (algebraMap L₁ (LaurentSeries L₁) (algebraMap A₁ L₁ a)) =
      algebraMap ↥k₀ (LaurentSeries ↥k₀) (ι (algebraMap A₁ L₁ a))
    rw [ModularCurve.algebraMap_laurentSeries_eq_single, ModularCurve.algebraMap_laurentSeries_eq_single,
      ModularCurve.coeffMap_single]

  have hmem : ∀ x : ↥K₁, x ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₁ (↥K₁) j₁ →
      cK x ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j := by

    have hadj : ∀ r : ↥K₁, r ∈ Algebra.adjoin A₁ ({j₁} : Set ↥K₁) → cK r ∈ Algebra.adjoin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ({j} : Set ↥K) := by
      intro r hr
      rw [Algebra.adjoin_singleton_eq_range_aeval] at hr
      obtain ⟨p, rfl⟩ := hr
      rw [Algebra.adjoin_singleton_eq_range_aeval]
      refine ⟨p.map ιA, ?_⟩
      change Polynomial.aeval j (p.map ιA) = cK (Polynomial.aeval j₁ p)
      rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.hom_eval₂, hcKj]
      congr 1
      exact RingHom.ext fun a => (hcKA a).symm
    let φ : ↥(Algebra.adjoin A₁ ({j₁} : Set ↥K₁)) →+* ↥(Algebra.adjoin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ({j} : Set ↥K)) :=
      (cK.comp (Algebra.adjoin A₁ ({j₁} : Set ↥K₁)).val.toRingHom).codRestrict
        (Algebra.adjoin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ({j} : Set ↥K)).toSubring (fun r => hadj r.1 r.2)
    have hφ : (algebraMap ↥(Algebra.adjoin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ({j} : Set ↥K)) ↥K).comp φ =
        cK.comp (algebraMap ↥(Algebra.adjoin A₁ ({j₁} : Set ↥K₁)) ↥K₁) := RingHom.ext (fun _ => rfl)
    intro x hx
    rw [AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff] at hx ⊢
    exact IsIntegral.map_of_comp_eq φ cK hφ hx
  let c : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₁ (↥K₁) j₁) →+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) :=
    (cK.comp (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₁ (↥K₁) j₁).val.toRingHom).codRestrict
      (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j).toSubring (fun x => hmem x.1 x.2)
  have hc_val : ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₁ (↥K₁) j₁), ((c a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j)) : ↥K) = cK (a : ↥K₁) := fun a => rfl
  have hc_coeff : ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₁ (↥K₁) j₁), (((c a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j)) : ↥K) : LaurentSeries ↥k₀) =
      ModularCurve.coeffMap ι (((a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₁ (↥K₁) j₁)) : ↥K₁) : LaurentSeries L₁) := fun a => by
    rw [hc_val, hcK]

  obtain ⟨τ, hτ⟩ := ModularCurve.FullLevel.AuxLevel.exists_isLevelAutAt_of_mem_gamma0_of_exists_ringHom q hq M' hqM' ℓ' hℓ'3 hℓ'q hℓ'M'
    ↥k₀ ξ hξ hιξ K hK γ hγ0
  have hcop : Nat.Coprime (q * ℓ') M' :=
    Nat.Coprime.mul_left ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hqM') ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hℓ'M')
  have hpres : ∀ f : ↥K, f ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j →
      τ f ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j := fun f hf =>
    ModularCurve.FullLevel.map_mem_chartAlgFin_of_isLevelAutAt_of_mem_Gamma0 (q * ℓ') M' hcop ↥k₀ (q * ℓ') ξ (by simpa using hιξ) K
      ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) j hj γ⁻¹ (inv_mem hγ0) τ hτ f hf

  have hrestrK : ∀ x : ↥K₁, τ (cK x) = cK (τ₁ x) := by
    have hι' : ∃ ι' : ↥k₀ →+* ℂ, ι' (ι ξ₁) = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ')) := by
      obtain ⟨ι', h⟩ := hιξ; exact ⟨ι', by rw [hιξ₁]; exact h⟩
    have hι₁ : ∃ ι' : L₁ →+* ℂ, ι' ξ₁ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ')) := by
      obtain ⟨ι', h⟩ := hι'; exact ⟨ι'.comp ι, h⟩
    obtain ⟨hmemK, hres⟩ := ModularCurve.FullLevel.AuxLevel.exists_isLevelAutAt_restrict_coeffMap_of_isLevelAutAt
      q hq M' hqM' ℓ' hℓ'3 hℓ'q hℓ'M' L₁ ξ₁ hξ₁ ↥k₀ ι hι' K₁ hK₁ K hK
    have hτ' : ModularCurve.FullLevel.IsLevelAutAt ↥k₀ (q * ℓ') (ι ξ₁) (q * ℓ') ((q * ℓ') ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ') M') γ⁻¹ K τ := by rw [hιξ₁]; exact hτ
    obtain ⟨τ₀, hτ₀, hcomp⟩ := hres γ hγ0 τ hτ'
    obtain ⟨huniq, -, -⟩ := ModularCurve.FullLevel.AuxLevel.isLevelAutAt_unique_mul_one_of_exists_ringHom
      q hq M' hqM' ℓ' hℓ'3 hℓ'q hℓ'M' L₁ ξ₁ hξ₁ hι₁ K₁ hK₁
    have hτ₀₁ : τ₀ = τ₁ := huniq γ⁻¹ (inv_mem hγ0) τ₀ τ₁ hτ₀ hτ₁
    intro x
    have hcKx : cK x = ⟨ModularCurve.coeffMap ι ((x : ↥K₁) : LaurentSeries L₁), hmemK x⟩ := Subtype.ext (hcK x)
    apply Subtype.ext
    rw [hcKx, hcomp x (hmemK x), hτ₀₁, hcK]
  have hrestr : ((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j)
        (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) hpres).comp c =
      c.comp ((τ₁ : ↥K₁ →+* ↥K₁).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₁ (↥K₁) j₁)
        (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₁ (↥K₁) j₁) hpres₁) := by
    apply RingHom.ext
    intro a
    apply Subtype.ext
    show τ ((c a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j)) : ↥K) = ((c _ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j)) : ↥K)
    rw [hc_val, hc_val, hrestrK]
    rfl
  exact ⟨c, τ, hτ, hpres, hc_coeff, hrestr⟩

end S_ModularCurve_FullLevel_exists_ringHom_chartAlgFin_isLevelAutAt_restrict_comp_eq_of_isLevelAutAt_cyclotomic_rigidDataPow
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_ringHom_chartAlgFin_isLevelAutAt_restrict_comp_eq_of_isLevelAutAt_cyclotomic_rigidDataPow (solution)
