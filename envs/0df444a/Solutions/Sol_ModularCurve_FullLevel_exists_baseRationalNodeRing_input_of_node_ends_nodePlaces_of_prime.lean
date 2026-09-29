-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_baseRationalNodeRing_input_of_node_ends_nodePlaces_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/2d685028-ab8d-5deb-8b4f-80cae5f3fbb7

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Theorems.Thm_ModularCurve_FullLevel_exists_place_mem_toValuationSubring_and_evalAt_mem_maximalIdeal_of_ringEquiv_uvCrossingModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_baseRationalNodeRing_input_of_node_ends_nodePlaces_of_prime
p2m_attr_erase "instance" "AdicCompletion.instIsLocalRingMaximalIdeal instTopologicallyFGOfFiniteType AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord"

set_option autoImplicit false
set_option linter.unusedVariables false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup ModularCurve.UVCrossingModel
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

namespace R4S191b
namespace LHyp

section PlaceOrd

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem ord_nonneg_of_mem {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  by_cases hf0 : f = 0
  · simp [hf0]
  · unfold Place.ord
    have h0 : v.adicValuation f ≠ 0 := v.adicValuation_ne_zero hf0
    have hv : v.adicValuation f ≤ 1 := by
      rw [show f = ((⟨f, hf⟩ : v.toValuationSubring) : F) from rfl, v.adicValuation_coe]
      exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _
    have h1 : WithZero.log (v.adicValuation f) ≤ WithZero.log (1 : WithZero (Multiplicative ℤ)) :=
      (WithZero.log_le_log h0 one_ne_zero).2 hv
    rw [WithZero.log_one] at h1
    omega

theorem ord_pos_of_mem_maximalIdeal {f : F} (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0)
    (hm : (⟨f, hf⟩ : v.toValuationSubring) ∈ maximalIdeal v.toValuationSubring) : 0 < v.ord f := by
  unfold Place.ord
  have h0 : v.adicValuation f ≠ 0 := v.adicValuation_ne_zero hf0
  have hv : v.adicValuation f < 1 := by
    rw [show f = ((⟨f, hf⟩ : v.toValuationSubring) : F) from rfl, v.adicValuation_coe]
    exact (IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem _ _).2 hm
  have h1 : WithZero.log (v.adicValuation f) < WithZero.log (1 : WithZero (Multiplicative ℤ)) :=
    (WithZero.log_lt_log h0 one_ne_zero).2 hv
  rw [WithZero.log_one] at h1
  omega

end PlaceOrd

end R4S191b.LHyp

open R4S191b.LHyp

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 12800000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
      Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A) :
    letI : Algebra ↥k₀ ↥(fieldBar q M') :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
    ∀ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M')),
      (IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) ⊔ F₀ = ⊤) →
      (∀ (K' : IntermediateField ↥k₀ (AlgebraicClosure ℚ)), FiniteDimensional ↥k₀ ↥K' →
        ∀ (m : ℕ) (c : Fin m → (AlgebraicClosure ℚ)) (a : Fin m → ↥(fieldBar q M')), (∀ i, a i ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K' : Set (AlgebraicClosure ℚ))) ⊔ F₀) →
          LinearIndependent ↥K' c → ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c i) * a i = 0 → ∀ i, a i = 0) →
    ∀ (W₀ : ValuationSubring ↥F₀),
      ((∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥F₀ x ∈ W₀) ∧
      IsDiscreteValuationRing ↥W₀ ∧
      (∃ hπW : algebraMap ↥k₀ ↥F₀ π₀ ∈ W₀, maximalIdeal ↥W₀ = Ideal.span {(⟨_, hπW⟩ : ↥W₀)})) →
    ∀ (O : Subring ↥F₀) [IsLocalRing ↥O] [IsNoetherianRing ↥O],
      (∀ f : ↥F₀, f ∈ O → f ∈ W₀) →
      (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥F₀ x ∈ O) →
      (∀ (f : ↥F₀) (hf : f ∈ O), ∃ (x : ↥k₀) (hx : algebraMap ↥k₀ ↥F₀ x ∈ O), (x : (AlgebraicClosure ℚ)) ∈ A ∧
              ¬ IsUnit ((⟨f, hf⟩ : ↥O) - ⟨_, hx⟩)) →

      (∀ f : ↥F₀, ∃ g h : ↥F₀, g ∈ O ∧ h ∈ O ∧ h ≠ 0 ∧ f * h = g) →
    ∀ (E₀ : ℕ) (_ : 1 ≤ E₀) (hπO : algebraMap ↥k₀ ↥F₀ π₀ ∈ O) (cx cy : ↥O) (u : (↥O)ˣ)
      (ιO : (AdicCompletion (maximalIdeal ↥O) ↥O) ≃+* UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀))
      (γU γV : (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀))ˣ),
      cx * cy = (⟨_, hπO⟩ : ↥O) ^ E₀ * (u : ↥O) →
      (∀ (x : ↥k₀) (hx : (x : (AlgebraicClosure ℚ)) ∈ A) (hxO : algebraMap ↥k₀ ↥F₀ x ∈ O),
                ιO (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨_, hxO⟩) =
                  UVCrossingModel.const ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀) (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨x, hx⟩)) →
      ιO (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) cx) = (γU : UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀)) * UVCrossingModel.U ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀) →
      ιO (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) cy) = (γV : UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀)) * UVCrossingModel.V ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀) →
      ((cy : ↥F₀) ∈ W₀) → (∀ hcy : (cy : ↥F₀) ∈ W₀, (⟨(cy : ↥F₀), hcy⟩ : ↥W₀) ∈ maximalIdeal ↥W₀) →
      (∀ hcx : (cx : ↥F₀) ∈ W₀, (⟨(cx : ↥F₀), hcx⟩ : ↥W₀) ∉ maximalIdeal ↥W₀) →

    ∀ (FI : Type) [Field FI] [Algebra (ResidueField ↥A) FI] (Rx : RegularProlongation A ↥(fieldBar q M') FI) (bx : Place (ResidueField ↥A) FI),
      bx.IsRational → (∀ f : ↥F₀, f ∈ O → (f : ↥(fieldBar q M')) ∈ Rx.integers) →
      (∀ (f : ↥F₀) (_ : f ∈ O) (hR : (f : ↥(fieldBar q M')) ∈ Rx.integers), Rx.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ bx.toValuationSubring) →
      (∀ (f : ↥F₀) (hf : f ∈ O) (hR : (f : ↥(fieldBar q M')) ∈ Rx.integers), ¬ IsUnit (⟨f, hf⟩ : ↥O) →
        ∃ hm : Rx.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ bx.toValuationSubring,
          (⟨_, hm⟩ : ↥bx.toValuationSubring) ∈ maximalIdeal ↥bx.toValuationSubring) →
      (∀ h₁ : ((cx : ↥F₀) : ↥(fieldBar q M')) ∈ Rx.integers, Rx.residue ⟨((cx : ↥F₀) : ↥(fieldBar q M')), h₁⟩ = 0) →
      (∀ h₁ : ((cy : ↥F₀) : ↥(fieldBar q M')) ∈ Rx.integers, bx.ord (Rx.residue ⟨((cy : ↥F₀) : ↥(fieldBar q M')), h₁⟩) = 1) →

    ∀ (FSS : Type) [Field FSS] [Algebra (ResidueField ↥A) FSS] (R : RegularProlongation A ↥(fieldBar q M') FSS) (nd : Place (ResidueField ↥A) FSS),
      (∀ f : ↥F₀, ((f : ↥(fieldBar q M')) ∈ R.integers ↔ f ∈ W₀)) → nd.IsRational →
      (∀ (f : ↥F₀) (_ : f ∈ O) (hR : (f : ↥(fieldBar q M')) ∈ R.integers), R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ nd.toValuationSubring) →
      (∀ (f : ↥F₀) (hf : f ∈ O) (hR : (f : ↥(fieldBar q M')) ∈ R.integers), ¬ IsUnit (⟨f, hf⟩ : ↥O) →
        ∃ hm : R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ nd.toValuationSubring,
          (⟨_, hm⟩ : ↥nd.toValuationSubring) ∈ maximalIdeal ↥nd.toValuationSubring) →
      (∀ h₂ : ((cy : ↥F₀) : ↥(fieldBar q M')) ∈ R.integers, R.residue ⟨((cy : ↥F₀) : ↥(fieldBar q M')), h₂⟩ = 0) →
      (∀ h₂ : ((cx : ↥F₀) : ↥(fieldBar q M')) ∈ R.integers, nd.ord (R.residue ⟨((cx : ↥F₀) : ↥(fieldBar q M')), h₂⟩) = 1) →

    ∀ (S : Set (Place (AlgebraicClosure ℚ) ↥(fieldBar q M'))),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), P ∈ S ↔
        (∀ f : ↥F₀, f ∈ O → (f : ↥(fieldBar q M')) ∈ P.toValuationSubring) ∧
        (∀ (f : ↥F₀) (hfO : f ∈ O), ¬ IsUnit (⟨f, hfO⟩ : ↥O) →
          ∃ h : P.evalAt (f : ↥(fieldBar q M')) ∈ A, (⟨_, h⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A)) →
      (∀ P ∈ S, P.IsRational) →
    ∀ (𝒩 : Subring ↥(fieldBar q M')),
      (∀ f : ↥(fieldBar q M'), f ∈ 𝒩 ↔ f ∈ Rx.integers ∧ f ∈ R.integers ∧ ∀ P ∈ S, f ∈ P.toValuationSubring) →
      (∀ f ∈ 𝒩, ∀ P ∈ S, P.evalAt f ∈ A) →

    ∀ (C : Subring (AlgebraicClosure ℚ)),
      (∀ c : AlgebraicClosure ℚ, c ∈ C ↔ c ∈ A ∧ c ∈ (⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ))) →
    ∀ (𝒩₀ : Subring ↥(fieldBar q M')),
      (∀ f : ↥(fieldBar q M'), f ∈ 𝒩₀ ↔ ∃ hf : f ∈ F₀, (⟨f, hf⟩ : ↥F₀) ∈ O) →
      ∃ (_ : IsLocalRing ↥𝒩₀) (_ : IsNoetherianRing ↥𝒩₀),
        S.Nonempty ∧
        𝒩₀ ≤ 𝒩 ∧

        (∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), P ∈ S ↔
          (∀ f : ↥(fieldBar q M'), f ∈ 𝒩₀ → f ∈ P.toValuationSubring) ∧
          (∀ f : ↥𝒩₀, ¬ IsUnit f → ∃ h : P.evalAt (f : ↥(fieldBar q M')) ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A)) ∧

        (∀ c : AlgebraicClosure ℚ, c ∈ C → algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') c ∈ 𝒩₀) ∧
        (∀ g : ↥𝒩₀, ∃ (o : ↥C) (h : algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (o : AlgebraicClosure ℚ) ∈ 𝒩₀), ¬ IsUnit (g - ⟨_, h⟩)) ∧

        (∀ (n : ℕ) (c : Fin n → AlgebraicClosure ℚ) (a : Fin n → ↥𝒩₀), LinearIndependent ↥C c →
          ∑ i, c i • ((a i : ↥𝒩₀) : ↥(fieldBar q M')) = 0 → ∀ i, a i = 0) ∧

        (∀ (f : ↥𝒩₀) (h₁ : (f : ↥(fieldBar q M')) ∈ Rx.integers), 0 ≤ bx.ord (Rx.residue ⟨f, h₁⟩) ∧
          (¬ IsUnit f → Rx.residue ⟨f, h₁⟩ ≠ 0 → 0 < bx.ord (Rx.residue ⟨f, h₁⟩))) ∧
        (∀ (f : ↥𝒩₀) (h₂ : (f : ↥(fieldBar q M')) ∈ R.integers), 0 ≤ nd.ord (R.residue ⟨f, h₂⟩) ∧
          (¬ IsUnit f → R.residue ⟨f, h₂⟩ ≠ 0 → 0 < nd.ord (R.residue ⟨f, h₂⟩))) ∧

        ((cx : ↥F₀) : ↥(fieldBar q M')) ∈ 𝒩₀ ∧ ((cy : ↥F₀) : ↥(fieldBar q M')) ∈ 𝒩₀ ∧
        (∀ h₁ : ((cx : ↥F₀) : ↥(fieldBar q M')) ∈ Rx.integers, Rx.residue ⟨((cx : ↥F₀) : ↥(fieldBar q M')), h₁⟩ = 0) ∧
        (∀ h₂ : ((cx : ↥F₀) : ↥(fieldBar q M')) ∈ R.integers, R.residue ⟨((cx : ↥F₀) : ↥(fieldBar q M')), h₂⟩ ≠ 0) ∧
        (∀ h₂ : ((cy : ↥F₀) : ↥(fieldBar q M')) ∈ R.integers, R.residue ⟨((cy : ↥F₀) : ↥(fieldBar q M')), h₂⟩ = 0) ∧
        (∀ h₁ : ((cy : ↥F₀) : ↥(fieldBar q M')) ∈ Rx.integers, Rx.residue ⟨((cy : ↥F₀) : ↥(fieldBar q M')), h₁⟩ ≠ 0) := by
  intro F₀ hK1 hLD W₀ hW₀ O instLoc instNoeth hOW hOk hOc hOF E₀ hE₀ hπO cx cy u ιO γU γV hxy hιconst hιcx hιcy
    hcyW hcyWm hcxW FI instFI instAlgFI Rx bx hbx hORx hORxc hORxm hRxcx hRxcy FSS instFSS instAlgFSS R nd hRW hnd
    hORc hORm hRcy hRcx S hS hSrat 𝒩 h𝒩 h𝒩A C hC 𝒩₀ h𝒩₀

  have hmem𝒩₀ : ∀ g : ↥O, ((g : ↥F₀) : ↥(fieldBar q M')) ∈ 𝒩₀ := fun g =>
    (h𝒩₀ _).2 ⟨(g : ↥F₀).2, by simpa only [Subtype.coe_eta] using g.2⟩
  let φ : ↥O →+* ↥𝒩₀ :=
    (F₀.val.toRingHom.comp O.subtype).codRestrict 𝒩₀ (fun g => hmem𝒩₀ g)
  have hφinj : Function.Injective φ := fun g₁ g₂ h =>
    Subtype.ext (Subtype.ext (congrArg (fun x : ↥𝒩₀ => (x : ↥(fieldBar q M'))) h))
  have hφsurj : Function.Surjective φ := fun f => by
    obtain ⟨hf, hO⟩ := (h𝒩₀ (f : ↥(fieldBar q M'))).1 f.2
    exact ⟨⟨⟨(f : ↥(fieldBar q M')), hf⟩, hO⟩, Subtype.ext rfl⟩
  let e : ↥O ≃+* ↥𝒩₀ := RingEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  have he : ∀ g : ↥O, ((e g : ↥𝒩₀) : ↥(fieldBar q M')) = ((g : ↥F₀) : ↥(fieldBar q M')) := fun g => rfl
  have hunit : ∀ g : ↥O, IsUnit (e g) ↔ IsUnit g := fun g => MulEquiv.isUnit_map e

  have hback : ∀ (f : ↥(fieldBar q M')) (hfF : f ∈ F₀) (hfO : (⟨f, hfF⟩ : ↥F₀) ∈ O) (hf : f ∈ 𝒩₀),
      e ⟨⟨f, hfF⟩, hfO⟩ = ⟨f, hf⟩ := fun f hfF hfO hf => Subtype.ext rfl
  have hnu_iff : ∀ (f : ↥(fieldBar q M')) (hfF : f ∈ F₀) (hfO : (⟨f, hfF⟩ : ↥F₀) ∈ O) (hf : f ∈ 𝒩₀),
      IsUnit (⟨f, hf⟩ : ↥𝒩₀) ↔ IsUnit (⟨⟨f, hfF⟩, hfO⟩ : ↥O) := fun f hfF hfO hf => by
    rw [← hback f hfF hfO hf, hunit]

  haveI hloc𝒩₀ : IsLocalRing ↥𝒩₀ := IsLocalRing.of_surjective' φ hφsurj
  haveI hnoe𝒩₀ : IsNoetherianRing ↥𝒩₀ := isNoetherianRing_of_ringEquiv ↥O e

  have hkF : ∀ x : ↥k₀, ((algebraMap ↥k₀ ↥F₀ x : ↥F₀) : ↥(fieldBar q M')) =
      algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (x : AlgebraicClosure ℚ) := fun x => rfl

  have hSchar : ∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), P ∈ S ↔
      (∀ f : ↥(fieldBar q M'), f ∈ 𝒩₀ → f ∈ P.toValuationSubring) ∧
      (∀ f : ↥𝒩₀, ¬ IsUnit f →
        ∃ h : P.evalAt (f : ↥(fieldBar q M')) ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A) := by
    intro P
    rw [hS P]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun f hf => ?_, fun f hf => ?_⟩
      · obtain ⟨hfF, hfO⟩ := (h𝒩₀ f).1 hf
        exact h1 ⟨f, hfF⟩ hfO
      · obtain ⟨hfF, hfO⟩ := (h𝒩₀ (f : ↥(fieldBar q M'))).1 f.2
        have hnu : ¬ IsUnit (⟨⟨(f : ↥(fieldBar q M')), hfF⟩, hfO⟩ : ↥O) := by
          rw [← hnu_iff _ hfF hfO f.2]; simpa using hf
        exact h2 ⟨(f : ↥(fieldBar q M')), hfF⟩ hfO hnu
    · rintro ⟨h1, h2⟩
      refine ⟨fun f hfO => h1 _ (hmem𝒩₀ ⟨f, hfO⟩), fun f hfO hnu => ?_⟩
      have hnu' : ¬ IsUnit (e ⟨f, hfO⟩) := fun hu => hnu ((hunit _).1 hu)
      exact h2 (e ⟨f, hfO⟩) hnu'

  have hSne : S.Nonempty := by
    obtain ⟨P, hP1, hP2⟩ :=
      ModularCurve.FullLevel.exists_place_mem_toValuationSubring_and_evalAt_mem_maximalIdeal_of_ringEquiv_uvCrossingModel
        q M' A k₀ π₀ hπ hdvr hunif hhens hres hκ F₀ hK1 hLD O hOk hOc hOF E₀ hE₀ hπO ιO hιconst
    exact ⟨P, (hS P).2 ⟨hP1, hP2⟩⟩

  have hle : 𝒩₀ ≤ 𝒩 := by
    intro f hf
    obtain ⟨hfF, hfO⟩ := (h𝒩₀ f).1 hf
    exact (h𝒩 f).2 ⟨hORx ⟨f, hfF⟩ hfO, (hRW ⟨f, hfF⟩).2 (hOW _ hfO),
      fun P hP => ((hS P).1 hP).1 ⟨f, hfF⟩ hfO⟩

  have hCk : ∀ c : AlgebraicClosure ℚ, c ∈ C → ∃ x : ↥k₀, (x : AlgebraicClosure ℚ) = c ∧ (x : AlgebraicClosure ℚ) ∈ A := by
    intro c hc
    obtain ⟨hcA, hcb⟩ := (hC c).1 hc
    obtain ⟨x, rfl⟩ := IntermediateField.mem_bot.1 hcb
    exact ⟨x, rfl, hcA⟩
  have hCmem : ∀ c : AlgebraicClosure ℚ, c ∈ C → algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') c ∈ 𝒩₀ := by
    intro c hc
    obtain ⟨x, rfl, hxA⟩ := hCk c hc
    rw [← hkF x]
    exact hmem𝒩₀ ⟨_, (hOk x).1 hxA⟩
  have hconstmod : ∀ g : ↥𝒩₀, ∃ (o : ↥C) (h : algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (o : AlgebraicClosure ℚ) ∈ 𝒩₀),
      ¬ IsUnit (g - ⟨_, h⟩) := by
    intro g
    obtain ⟨x, hx, hxA, hnu⟩ := hOc ((e.symm g : ↥O) : ↥F₀) (e.symm g).2
    have hoC : (x : AlgebraicClosure ℚ) ∈ C := (hC _).2 ⟨hxA, IntermediateField.mem_bot.2 ⟨x, rfl⟩⟩
    refine ⟨⟨(x : AlgebraicClosure ℚ), hoC⟩, hCmem _ hoC, fun hu => hnu ?_⟩
    have hex : e ⟨algebraMap ↥k₀ ↥F₀ x, hx⟩ =
        ⟨algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (x : AlgebraicClosure ℚ), hCmem _ hoC⟩ :=
      Subtype.ext (hkF x)
    have heg : e (e.symm g) = g := e.apply_symm_apply g
    have hg'eta : (⟨((e.symm g : ↥O) : ↥F₀), (e.symm g).2⟩ : ↥O) = e.symm g := Subtype.coe_eta _ _
    rw [hg'eta, ← hunit, map_sub, heg, hex]
    exact hu

  have hLDC : ∀ (n : ℕ) (c : Fin n → AlgebraicClosure ℚ) (a : Fin n → ↥𝒩₀), LinearIndependent ↥C c →
      ∑ i, c i • ((a i : ↥𝒩₀) : ↥(fieldBar q M')) = 0 → ∀ i, a i = 0 := by
    intro n c a hli hsum

    have hli' : LinearIndependent ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) c := by
      rw [Fintype.linearIndependent_iff]
      intro g hg i

      have hgt : ∀ j, ∃ t : ↥k₀, (t : AlgebraicClosure ℚ) = (g j : AlgebraicClosure ℚ) := fun j => by
        obtain ⟨t, ht⟩ := IntermediateField.mem_bot.1 (g j).2
        exact ⟨t, ht⟩
      choose t ht using hgt

      let A₀ : ValuationSubring ↥k₀ := A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))
      classical
      let d : Fin n → ↥k₀ := fun j => if t j ∈ A₀ then 1 else (t j)⁻¹
      have hd : ∀ j, d j ∈ A₀ ∧ d j ≠ 0 ∧ d j * t j ∈ A₀ := by
        intro j
        by_cases htj : t j ∈ A₀
        · simp only [d, if_pos htj]; exact ⟨A₀.one_mem, one_ne_zero, by simpa using htj⟩
        · have htj0 : t j ≠ 0 := by rintro h0; exact htj (h0 ▸ A₀.zero_mem)
          have hinv : (t j)⁻¹ ∈ A₀ := (A₀.mem_or_inv_mem (t j)).resolve_left htj
          simp only [d, if_neg htj]
          exact ⟨hinv, inv_ne_zero htj0, by rw [inv_mul_cancel₀ htj0]; exact A₀.one_mem⟩
      let D : ↥k₀ := ∏ j, d j
      have hDA : D ∈ A₀ := prod_mem (fun j _ => (hd j).1)
      have hD0 : D ≠ 0 := Finset.prod_ne_zero_iff.2 (fun j _ => (hd j).2.1)
      have hDt : ∀ j, D * t j ∈ A₀ := by
        intro j
        have hsplit : D = (∏ k ∈ Finset.univ.erase j, d k) * d j :=
          (Finset.prod_erase_mul (Finset.univ) d (Finset.mem_univ j)).symm
        rw [hsplit, mul_assoc]
        exact mul_mem (prod_mem (fun k _ => (hd k).1)) (hd j).2.2

      have hγ : ∀ j, ((D * t j : ↥k₀) : AlgebraicClosure ℚ) ∈ C := fun j =>
        (hC _).2 ⟨hDt j, IntermediateField.mem_bot.2 ⟨D * t j, rfl⟩⟩
      let γ : Fin n → ↥C := fun j => ⟨((D * t j : ↥k₀) : AlgebraicClosure ℚ), hγ j⟩
      have hsumγ : ∑ j, γ j • c j = 0 := by
        have h1 : ∑ j, γ j • c j = (D : AlgebraicClosure ℚ) * ∑ j, (g j : AlgebraicClosure ℚ) * c j := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          show ((D * t j : ↥k₀) : AlgebraicClosure ℚ) * c j = _
          rw [← ht j]; push_cast; ring
        have h2 : ∑ j, (g j : AlgebraicClosure ℚ) * c j = 0 := by
          have h__ := hg
          try simp at h__
          try simp
          exact h__
        rw [h1, h2, mul_zero]
      have hγ0 := (Fintype.linearIndependent_iff.1 hli) γ hsumγ i
      have : (D : AlgebraicClosure ℚ) * (t i : AlgebraicClosure ℚ) = 0 := by
        have := congrArg (fun x : ↥C => (x : AlgebraicClosure ℚ)) hγ0
        simpa [γ] using this
      rcases mul_eq_zero.1 this with hD | hti
      · exact absurd hD (by exact_mod_cast hD0)
      · apply Subtype.ext
        rw [← ht i, hti]
        simp
    have hmem : ∀ i, ((a i : ↥𝒩₀) : ↥(fieldBar q M')) ∈
        IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) ''
          (↑(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ))) ⊔ F₀ := fun i =>
      (le_sup_right : F₀ ≤ _) ((h𝒩₀ _).1 (a i).2).1
    have hsum' : ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c i) * ((a i : ↥𝒩₀) : ↥(fieldBar q M')) = 0 := by
      rw [← hsum]
      exact Finset.sum_congr rfl (fun i _ => (Algebra.smul_def (c i) _).symm)
    intro i
    have h0 := hLD ⊥ inferInstance n c (fun i => ((a i : ↥𝒩₀) : ↥(fieldBar q M'))) hmem hli' hsum' i
    exact_mod_cast h0

  have hregx : ∀ (f : ↥𝒩₀) (h₁ : (f : ↥(fieldBar q M')) ∈ Rx.integers), 0 ≤ bx.ord (Rx.residue ⟨f, h₁⟩) ∧
      (¬ IsUnit f → Rx.residue ⟨f, h₁⟩ ≠ 0 → 0 < bx.ord (Rx.residue ⟨f, h₁⟩)) := by
    intro f h₁
    obtain ⟨hfF, hfO⟩ := (h𝒩₀ (f : ↥(fieldBar q M'))).1 f.2
    have hm : Rx.residue ⟨f, h₁⟩ ∈ bx.toValuationSubring := hORxc ⟨f, hfF⟩ hfO h₁
    refine ⟨ord_nonneg_of_mem bx hm, fun hnu hne => ?_⟩
    have hnuO : ¬ IsUnit (⟨⟨(f : ↥(fieldBar q M')), hfF⟩, hfO⟩ : ↥O) := by
      rw [← hnu_iff _ hfF hfO f.2]; simpa using hnu
    obtain ⟨hm', hmax⟩ := hORxm ⟨f, hfF⟩ hfO h₁ hnuO
    exact ord_pos_of_mem_maximalIdeal bx hm' hne hmax
  have hregR : ∀ (f : ↥𝒩₀) (h₂ : (f : ↥(fieldBar q M')) ∈ R.integers), 0 ≤ nd.ord (R.residue ⟨f, h₂⟩) ∧
      (¬ IsUnit f → R.residue ⟨f, h₂⟩ ≠ 0 → 0 < nd.ord (R.residue ⟨f, h₂⟩)) := by
    intro f h₂
    obtain ⟨hfF, hfO⟩ := (h𝒩₀ (f : ↥(fieldBar q M'))).1 f.2
    have hm : R.residue ⟨f, h₂⟩ ∈ nd.toValuationSubring := hORc ⟨f, hfF⟩ hfO h₂
    refine ⟨ord_nonneg_of_mem nd hm, fun hnu hne => ?_⟩
    have hnuO : ¬ IsUnit (⟨⟨(f : ↥(fieldBar q M')), hfF⟩, hfO⟩ : ↥O) := by
      rw [← hnu_iff _ hfF hfO f.2]; simpa using hnu
    obtain ⟨hm', hmax⟩ := hORm ⟨f, hfF⟩ hfO h₂ hnuO
    exact ord_pos_of_mem_maximalIdeal nd hm' hne hmax

  have hRcx' : ∀ h₂ : ((cx : ↥F₀) : ↥(fieldBar q M')) ∈ R.integers, R.residue ⟨((cx : ↥F₀) : ↥(fieldBar q M')), h₂⟩ ≠ 0 := by
    intro h₂ h0
    have h1 := hRcx h₂
    rw [h0, Place.ord_zero] at h1
    exact zero_ne_one h1
  have hRxcy' : ∀ h₁ : ((cy : ↥F₀) : ↥(fieldBar q M')) ∈ Rx.integers, Rx.residue ⟨((cy : ↥F₀) : ↥(fieldBar q M')), h₁⟩ ≠ 0 := by
    intro h₁ h0
    have h1 := hRxcy h₁
    rw [h0, Place.ord_zero] at h1
    exact zero_ne_one h1
  exact ⟨hloc𝒩₀, hnoe𝒩₀, hSne, hle, hSchar, hCmem, hconstmod, hLDC, hregx, hregR, hmem𝒩₀ cx, hmem𝒩₀ cy,
    hRxcx, hRcx', hRcy, hRxcy'⟩

end S_ModularCurve_FullLevel_exists_baseRationalNodeRing_input_of_node_ends_nodePlaces_of_prime
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_baseRationalNodeRing_input_of_node_ends_nodePlaces_of_prime (solution)
