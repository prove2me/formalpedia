-- Prove2me | solution 1 for ModularCurve.FullLevel.klevel_smoothPointPackages_of_smoothPointStalks_linked_of_eq_two_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/78554cfb-088c-5efd-a458-65eeda13e5f6

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Theorems.Thm_AlgebraicCurve_RegularProlongation_disc_sections_locality_of_smoothPoint
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_ValuationSubring_isPrincipalIdealRing_of_finiteDimensional_adjoin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_klevel_smoothPointPackages_of_smoothPointStalks_linked_of_eq_two_of_dvd
p2m_attr_erase "instance" "AlgebraicCurve.GaussReduction.isLocalHom_constToGauss AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

namespace KLevelPlusReduce

theorem Gamma1_le_GammaH (M : ℕ) (H : Subgroup (ZMod M)ˣ) :
    CongruenceSubgroup.Gamma1 M ≤ CohCarrier.GammaH M H := by
  intro A hA
  rw [CongruenceSubgroup.Gamma1_mem] at hA
  obtain ⟨h00, h11, h10⟩ := hA
  have hA0 : A ∈ CongruenceSubgroup.Gamma0 M := CongruenceSubgroup.Gamma0_mem.mpr h10
  refine CohCarrier.mem_GammaH_iff.mpr ⟨hA0, ?_⟩
  have : CohCarrier.gamma0Units M ⟨A, hA0⟩ = 1 := by
    apply Units.ext
    rw [CohCarrier.val_gamma0Units, Units.val_one]
    exact h11
  rw [this]
  exact one_mem H

theorem finiteIndex_GammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) : (CohCarrier.GammaH M H).FiniteIndex :=
  haveI : (CongruenceSubgroup.Gamma1 M).FiniteIndex := inferInstance
  Subgroup.finiteIndex_of_le (Gamma1_le_GammaH M H)

theorem T_mem_GammaH (M : ℕ) (H : Subgroup (ZMod M)ˣ) : ModularGroup.T ∈ CohCarrier.GammaH M H := by
  apply Gamma1_le_GammaH
  rw [CongruenceSubgroup.Gamma1_mem]
  refine ⟨?_, ?_, ?_⟩ <;> simp [ModularGroup.T]

theorem exists_finiteDimensional_adjoin_fieldBar (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] :
    ∃ x : ↥(fieldBar q M'), FiniteDimensional ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set ↥(fieldBar q M'))) ↥(fieldBar q M') := by
  haveI : (CohCarrier.GammaH (q ^ 2 * M') (levelH q M')).FiniteIndex := finiteIndex_GammaH _ _
  obtain ⟨x, -, hfd⟩ := ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange
    (AlgebraicClosure ℚ) (CohCarrier.GammaH (q ^ 2 * M') (levelH q M')) (T_mem_GammaH _ _)
  exact ⟨x, hfd⟩

theorem fieldBar_dvr (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] :
    ∀ O : ValuationSubring ↥(fieldBar q M'),
      (∀ x : AlgebraicClosure ℚ, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') x ∈ O) → O ≠ ⊤ → IsPrincipalIdealRing ↥O := by
  obtain ⟨x, hfd⟩ := exists_finiteDimensional_adjoin_fieldBar q M'
  intro O hK hO
  haveI := hfd
  exact ValuationSubring.isPrincipalIdealRing_of_finiteDimensional_adjoin x O hK hO

end KLevelPlusReduce

open KLevelPlusReduce in

theorem solution
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
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

    {ι : Type} (K : ι → IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (hKfin : ∀ n, FiniteDimensional ↥k₀ ↥(K n))
    (An : ∀ n, ValuationSubring ↥(K n))
    (hAn : ∀ n (x : ↥(K n)), x ∈ An n ↔ (x : AlgebraicClosure ℚ) ∈ A) :
    letI : Algebra ↥k₀ ↥(fieldBar q M') :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
    ∀ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M')),
      (IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) ⊔ F₀ = ⊤) →
      ∀ (FSS : Type) [Field FSS] [Algebra (ResidueField ↥A) FSS] (R : RegularProlongation A ↥(fieldBar q M') FSS),
        ∀ (N : Finset (Place (ResidueField ↥A) FSS))
          (Sn : Place (ResidueField ↥A) FSS → ι → Subring ↥(fieldBar q M'))
          (φn : (Q : Place (ResidueField ↥A) FSS) → (n : ι) → (Polynomial ↥(An n) →+* ↥(Sn Q n)))
          (χn : (Q : Place (ResidueField ↥A) FSS) → (n : ι) → (↥(Sn Q n) →+* ResidueField ↥A))
          (Dn : Place (ResidueField ↥A) FSS → ι → Set (Place (AlgebraicClosure ℚ) ↥(fieldBar q M'))),
        (N.card = q + 1 ∧
          (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N →

            (∀ n : ι,

              Function.Surjective (fun a : ↥(An n) => IsLocalRing.residue ↥A ⟨((a : ↥(K n)) : AlgebraicClosure ℚ), (hAn n a).mp a.2⟩) ∧

              (∀ a : ↥(An n), algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥(K n)) : AlgebraicClosure ℚ) ∈ Sn Q n) ∧

              (φn Q n).FormallySmooth ∧ (φn Q n).FormallyUnramified ∧

              (∀ a : ↥(An n), ((φn Q n (Polynomial.C a) : ↥(Sn Q n)) : ↥(fieldBar q M')) = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥(K n)) : AlgebraicClosure ℚ)) ∧

              (∀ a : ↥(An n), χn Q n (φn Q n (Polynomial.C a)) = IsLocalRing.residue ↥A ⟨((a : ↥(K n)) : AlgebraicClosure ℚ), (hAn n a).mp a.2⟩) ∧

              χn Q n (φn Q n Polynomial.X) = 0 ∧

              (∀ c : ↥(An n), IsLocalRing.residue ↥A ⟨((c : ↥(K n)) : AlgebraicClosure ℚ), (hAn n c).mp c.2⟩ = 0 →
                ∃! χ : ↥(Sn Q n) →+* ↥(An n), (∀ a : ↥(An n), χ (φn Q n (Polynomial.C a)) = a) ∧
                  (∀ f : ↥(Sn Q n), IsLocalRing.residue ↥A ⟨((χ f : ↥(K n)) : AlgebraicClosure ℚ), (hAn n _).mp (χ f).2⟩ = χn Q n f) ∧
                  χ (φn Q n Polynomial.X) = c) ∧

              (∀ f : ↥(Sn Q n), ∃ hR : (f : ↥(fieldBar q M')) ∈ R.integers, ∃ hm : R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ Q.toValuationSubring,
                IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : ↥(fieldBar q M')), hR⟩, hm⟩ =
                  algebraMap (ResidueField ↥A) Q.ResidueField (χn Q n f)) ∧

              (∃ hR : ((φn Q n Polynomial.X : ↥(Sn Q n)) : ↥(fieldBar q M')) ∈ R.integers,
                Q.ord (R.residue ⟨((φn Q n Polynomial.X : ↥(Sn Q n)) : ↥(fieldBar q M')), hR⟩) = 1) ∧

              (∀ P, P ∈ Dn Q n ↔ (P.IsRational ∧
                (∀ f : ↥(Sn Q n), (f : ↥(fieldBar q M')) ∈ P.toValuationSubring ∧ P.evalAt (f : ↥(fieldBar q M')) ∈ A) ∧
                (∀ f : ↥(Sn Q n), A.valuation (P.evalAt (f : ↥(fieldBar q M'))) < 1 ↔ χn Q n f = 0))) ∧

              (∀ c : ↥(An n), φn Q n Polynomial.X ≠ φn Q n (Polynomial.C c)) ∧

              (∃ (_ : IsLocalRing ↥(Sn Q n)),
                (∀ f : ↥(Sn Q n), f ∈ maximalIdeal ↥(Sn Q n) ↔ χn Q n f = 0) ∧
                IsNoetherianRing ↥(Sn Q n) ∧ UniqueFactorizationMonoid ↥(Sn Q n)) ∧

              (∀ f : ↥(fieldBar q M'), f ∈ Sn Q n → f ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(K n) : Set (AlgebraicClosure ℚ))) ⊔ F₀) ∧
              (∀ f : ↥(fieldBar q M'), f ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(K n) : Set (AlgebraicClosure ℚ))) ⊔ F₀ → ∃ g h : ↥(Sn Q n), (h : ↥(fieldBar q M')) ≠ 0 ∧ f * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M'))) ∧

              (∀ (m : ℕ) (c : Fin m → (AlgebraicClosure ℚ)) (a : Fin m → ↥(fieldBar q M')), (∀ i, a i ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(K n) : Set (AlgebraicClosure ℚ))) ⊔ F₀) →
                LinearIndependent ↥(K n) c → ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c i) * a i = 0 → ∀ i, a i = 0) ∧

              (∀ χ : ↥(Sn Q n) →+* ↥(An n), (∀ a : ↥(An n), χ (φn Q n (Polynomial.C a)) = a) →
                (∀ f : ↥(Sn Q n), IsLocalRing.residue ↥A ⟨((χ f : ↥(K n)) : AlgebraicClosure ℚ), (hAn n _).mp (χ f).2⟩ = χn Q n f) →
                RingHom.ker χ = Ideal.span {φn Q n Polynomial.X - φn Q n (Polynomial.C (χ (φn Q n Polynomial.X)))}) ∧

              (∃ ϖ : ↥(An n), maximalIdeal ↥(An n) = Ideal.span {ϖ} ∧ ϖ ≠ 0 ∧
                Prime (φn Q n (Polynomial.C ϖ)) ∧
                (∀ f : ↥(fieldBar q M'), f ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(K n) : Set (AlgebraicClosure ℚ))) ⊔ F₀ →
                  (f ∈ R.integers ↔ ∃ g h : ↥(Sn Q n), ¬ (φn Q n (Polynomial.C ϖ) ∣ h) ∧ f * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M')))) ∧
                (∀ p : ↥(Sn Q n), Prime p → ¬ Associated p (φn Q n (Polynomial.C ϖ)) →
                  ∀ x : ↥(Sn Q n), ∃ r : Polynomial ↥(An n), r.Monic ∧ p ∣ (r.map ((φn Q n).comp Polynomial.C)).eval x)) ∧

              (∃ G : Finset ↥(fieldBar q M'), ↑G ⊆ (Sn Q n : Set ↥(fieldBar q M')) ∧ ∀ f ∈ Sn Q n, ∃ g h : ↥(fieldBar q M'),
                g ∈ Subring.closure (↑G ∪ ((fun a : ↥(An n) => algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥(K n)) : AlgebraicClosure ℚ)) '' Set.univ)) ∧
                h ∈ Subring.closure (↑G ∪ ((fun a : ↥(An n) => algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥(K n)) : AlgebraicClosure ℚ)) '' Set.univ)) ∧
                (∃ u : (↥(Sn Q n))ˣ, ((u : ↥(Sn Q n)) : ↥(fieldBar q M')) = h) ∧ f * h = g)) ∧

            (∃ hmono : ∀ n n', K n ≤ K n' → Sn Q n ≤ Sn Q n',
              (∀ n n', K n ≤ K n' →
                Sn Q n' ≤ Subring.closure ((Sn Q n : Set ↥(fieldBar q M')) ∪ ((fun a : ↥(An n') => algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥(K n')) : AlgebraicClosure ℚ)) '' Set.univ))) ∧
              (∀ n n', ((φn Q n Polynomial.X : ↥(Sn Q n)) : ↥(fieldBar q M')) = ((φn Q n' Polynomial.X : ↥(Sn Q n')) : ↥(fieldBar q M'))) ∧
              (∀ n n' (h : K n ≤ K n') (f : ↥(Sn Q n)), χn Q n' ⟨(f : ↥(fieldBar q M')), hmono n n' h f.2⟩ = χn Q n f))) ∧

          (∀ Q Q' : Place (ResidueField ↥A) FSS, Q ∉ N → Q' ∉ N → ∀ (n : ι) (P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M')), P ∈ Dn Q n → P ∈ Dn Q' n → Q = Q') ∧

          (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N → ∀ n : ι, ∀ P ∈ Dn Q n,
            0 ≤ P.ord (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                ↥(modularFunctionFieldBar M')) : fieldBar q M')) ∧

          (∀ τ ∈ Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
              ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ},
            ∀ (hτ : ∀ f : ↥(fieldBar q M'), τ f ∈ R.integers ↔ f ∈ R.integers) (Q : Place (ResidueField ↥A) FSS),
              (R.resAut τ hτ • Q ∈ N ↔ Q ∈ N) ∧
              (Q ∉ N → ∀ n : ι, AlgebraicCurve.RegularProlongation.smulDisc τ (Dn Q n) = Dn (R.resAut τ hτ • Q) n))) →
        (N.card = q + 1 ∧
          (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N →

            (∀ n : ι,

              Function.Surjective (fun a : ↥(An n) => IsLocalRing.residue ↥A ⟨((a : ↥(K n)) : AlgebraicClosure ℚ), (hAn n a).mp a.2⟩) ∧

              (∀ a : ↥(An n), algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥(K n)) : AlgebraicClosure ℚ) ∈ Sn Q n) ∧

              (φn Q n).FormallySmooth ∧ (φn Q n).FormallyUnramified ∧

              (∀ a : ↥(An n), ((φn Q n (Polynomial.C a) : ↥(Sn Q n)) : ↥(fieldBar q M')) = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥(K n)) : AlgebraicClosure ℚ)) ∧

              (∀ a : ↥(An n), χn Q n (φn Q n (Polynomial.C a)) = IsLocalRing.residue ↥A ⟨((a : ↥(K n)) : AlgebraicClosure ℚ), (hAn n a).mp a.2⟩) ∧

              χn Q n (φn Q n Polynomial.X) = 0 ∧

              (∀ c : ↥(An n), IsLocalRing.residue ↥A ⟨((c : ↥(K n)) : AlgebraicClosure ℚ), (hAn n c).mp c.2⟩ = 0 →
                ∃! χ : ↥(Sn Q n) →+* ↥(An n), (∀ a : ↥(An n), χ (φn Q n (Polynomial.C a)) = a) ∧
                  (∀ f : ↥(Sn Q n), IsLocalRing.residue ↥A ⟨((χ f : ↥(K n)) : AlgebraicClosure ℚ), (hAn n _).mp (χ f).2⟩ = χn Q n f) ∧
                  χ (φn Q n Polynomial.X) = c) ∧

              (∀ f : ↥(Sn Q n), ∃ hR : (f : ↥(fieldBar q M')) ∈ R.integers, ∃ hm : R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ Q.toValuationSubring,
                IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : ↥(fieldBar q M')), hR⟩, hm⟩ =
                  algebraMap (ResidueField ↥A) Q.ResidueField (χn Q n f)) ∧

              (∃ hR : ((φn Q n Polynomial.X : ↥(Sn Q n)) : ↥(fieldBar q M')) ∈ R.integers,
                Q.ord (R.residue ⟨((φn Q n Polynomial.X : ↥(Sn Q n)) : ↥(fieldBar q M')), hR⟩) = 1) ∧

              (∀ P, P ∈ Dn Q n ↔ (P.IsRational ∧
                (∀ f : ↥(Sn Q n), (f : ↥(fieldBar q M')) ∈ P.toValuationSubring ∧ P.evalAt (f : ↥(fieldBar q M')) ∈ A) ∧
                (∀ f : ↥(Sn Q n), A.valuation (P.evalAt (f : ↥(fieldBar q M'))) < 1 ↔ χn Q n f = 0))) ∧

              (∀ χ : ↥(Sn Q n) →+* ↥(An n), (∀ a : ↥(An n), χ (φn Q n (Polynomial.C a)) = a) →
                (∀ f : ↥(Sn Q n), IsLocalRing.residue ↥A ⟨((χ f : ↥(K n)) : AlgebraicClosure ℚ), (hAn n _).mp (χ f).2⟩ = χn Q n f) →
                ∃! P, P ∈ Dn Q n ∧ ∀ f : ↥(Sn Q n), P.evalAt (f : ↥(fieldBar q M')) = ((χ f : ↥(K n)) : AlgebraicClosure ℚ)) ∧

              (∀ P ∈ Dn Q n, ∀ f : ↥(fieldBar q M'), f ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(K n) : Set (AlgebraicClosure ℚ))) ⊔ F₀ →
                (f ∈ P.toValuationSubring ↔ ∃ g h : ↥(Sn Q n), P.evalAt (h : ↥(fieldBar q M')) ≠ 0 ∧ f * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M')))) ∧

              (∀ f : ↥(fieldBar q M'), f ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(K n) : Set (AlgebraicClosure ℚ))) ⊔ F₀ → f ≠ 0 → (∀ P ∈ Dn Q n, P.ord f = 0) →
                ∃ (c : ↥(K n)) (u : (↥(Sn Q n))ˣ), c ≠ 0 ∧ algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c : AlgebraicClosure ℚ) * f = ((u : ↥(Sn Q n)) : ↥(fieldBar q M'))) ∧

              (∀ f : ↥(fieldBar q M'), f ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(K n) : Set (AlgebraicClosure ℚ))) ⊔ F₀ → f ∈ R.integers → (∀ P ∈ Dn Q n, f ∈ P.toValuationSubring) → f ∈ Sn Q n) ∧

              (∃ G : Finset ↥(fieldBar q M'), ↑G ⊆ (Sn Q n : Set ↥(fieldBar q M')) ∧ ∀ f ∈ Sn Q n, ∃ g h : ↥(fieldBar q M'),
                g ∈ Subring.closure (↑G ∪ ((fun a : ↥(An n) => algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥(K n)) : AlgebraicClosure ℚ)) '' Set.univ)) ∧
                h ∈ Subring.closure (↑G ∪ ((fun a : ↥(An n) => algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥(K n)) : AlgebraicClosure ℚ)) '' Set.univ)) ∧
                (∃ u : (↥(Sn Q n))ˣ, ((u : ↥(Sn Q n)) : ↥(fieldBar q M')) = h) ∧ f * h = g)) ∧

            (∃ hmono : ∀ n n', K n ≤ K n' → Sn Q n ≤ Sn Q n',
              (∀ n n', K n ≤ K n' →
                Sn Q n' ≤ Subring.closure ((Sn Q n : Set ↥(fieldBar q M')) ∪ ((fun a : ↥(An n') => algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥(K n')) : AlgebraicClosure ℚ)) '' Set.univ))) ∧
              (∀ n n', ((φn Q n Polynomial.X : ↥(Sn Q n)) : ↥(fieldBar q M')) = ((φn Q n' Polynomial.X : ↥(Sn Q n')) : ↥(fieldBar q M'))) ∧
              (∀ n n' (h : K n ≤ K n') (f : ↥(Sn Q n)), χn Q n' ⟨(f : ↥(fieldBar q M')), hmono n n' h f.2⟩ = χn Q n f))) ∧

          (∀ Q Q' : Place (ResidueField ↥A) FSS, Q ∉ N → Q' ∉ N → ∀ (n : ι) (P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M')), P ∈ Dn Q n → P ∈ Dn Q' n → Q = Q') ∧

          (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N → ∀ n : ι, ∀ P ∈ Dn Q n,
            0 ≤ P.ord (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                ↥(modularFunctionFieldBar M')) : fieldBar q M')) ∧

          (∀ τ ∈ Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
              ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ},
            ∀ (hτ : ∀ f : ↥(fieldBar q M'), τ f ∈ R.integers ↔ f ∈ R.integers) (Q : Place (ResidueField ↥A) FSS),
              (R.resAut τ hτ • Q ∈ N ↔ Q ∈ N) ∧
              (Q ∉ N → ∀ n : ι, AlgebraicCurve.RegularProlongation.smulDisc τ (Dn Q n) = Dn (R.resAut τ hτ • Q) n))) := by
  letI instAlg : Algebra ↥k₀ ↥(fieldBar q M') :=
    ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
  haveI hQalg : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI halgk : Algebra.IsAlgebraic ↥k₀ (AlgebraicClosure ℚ) := Algebra.IsAlgebraic.tower_top (K := ℚ) ↥k₀
  have halg : ∀ (n : ι) (x : AlgebraicClosure ℚ), IsAlgebraic ↥(K n) x :=
    fun n x => ((halgk.isAlgebraic x).isIntegral.tower_top (A := ↥(K n))).isAlgebraic
  have hcurve : IsCurveOver (AlgebraicClosure ℚ) ↥(fieldBar q M') := by
      exact (ModularCurve.isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
      (AlgebraicClosure ℚ) (q ^ 2 * M') (levelH q M')).1
  intro F₀ h1 FSS _ _ R N Sn φn χn Dn hS
  obtain ⟨hcard, hQ, hdisj, hcusp, heqv⟩ := hS
  refine ⟨hcard, ?_, hdisj, hcusp, heqv⟩
  intro Q hQN
  obtain ⟨hlayer, hcompat⟩ := hQ Q hQN
  refine ⟨fun n => ?_, hcompat⟩
  obtain ⟨hκn, hAS, hφs, hφu, hφC, hχC, hχt, hchart, hres', hordQ, hDn, ht, ⟨hlocal, hmax, hnoeth, hufd⟩, hSF, hfrac,
    hld, hker, ⟨ϖ, hϖ, hϖ0, hprime, hRint, hbranch⟩, hfg⟩ := hlayer n
  obtain ⟨hsec, hval, hloc, hloc'⟩ :=
    @AlgebraicCurve.RegularProlongation.disc_sections_locality_of_smoothPoint
      ↥k₀ (AlgebraicClosure ℚ) ↥(fieldBar q M') _ _ _ _ instAlg _ (IsScalarTower.of_algebraMap_eq (fun _ => rfl)) _ _ hcurve
      F₀ h1 A FSS _ _ R (K n) (halg n) (An n) (hAn n) hκn (Sn Q n) (φn Q n) (χn Q n) (Dn Q n)
      hAS hφC hχC hχt hDn ht hlocal hmax hnoeth hufd hSF hfrac hld (fieldBar_dvr q M')
      ϖ hϖ hϖ0 hprime hRint hker hbranch
  exact ⟨hκn, hAS, hφs, hφu, hφC, hχC, hχt, hchart, hres', hordQ, hDn, hsec, hval, hloc, hloc', hfg⟩

end S_ModularCurve_FullLevel_klevel_smoothPointPackages_of_smoothPointStalks_linked_of_eq_two_of_dvd
end P2MW
export P2MW.S_ModularCurve_FullLevel_klevel_smoothPointPackages_of_smoothPointStalks_linked_of_eq_two_of_dvd (solution)
