-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_layerRationalNodeRing_of_baseRationalNodeRing_layer_chart_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/c3b41337-b92a-57cb-8d05-105db4c5b380

import Mathlib
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
import Theorems.Thm_ModularCurve_FullLevel_exists_baseRationalNodeRing_input_of_node_ends_nodePlaces_of_prime
import Theorems.Thm_AlgebraicCurve_NodeAnnulusEngine_exists_localizedBaseChange_of_layer_pos_localization
import Theorems.Thm_AlgebraicCurve_NodeAnnulusEngine_exists_ringEquiv_adicCompletion_uvCrossingModel_of_layer_compatibleUV
import Theorems.Thm_AlgebraicCurve_NodeAnnulusEngine_exists_isUnit_sub_mul_V_pow_mem_of_ord_residue_eq_of_ringEquiv_uvCrossingModel
import Theorems.Thm_AlgebraicCurve_NodeAnnulusEngine_exists_isUnit_sub_mul_U_pow_mem_of_ord_residue_eq_of_ringEquiv_uvCrossingModel
import Theorems.Thm_IsLocalRing_exists_ringEquiv_adicCompletion_maximalIdeal_comp_algebraMap_of_ringEquiv
import Theorems.Thm_IsLocalRing_exists_branchReadings_of_ringEquiv_adicCompletion_uvCrossingModel_pow
import Theorems.Thm_IsDiscreteValuationRing_exists_isAdicComplete_map_maximalIdeal_eq_forall_sub_mem_maximalIdeal
import Theorems.Thm_IsDiscreteValuationRing_exists_ringEquiv_adicCompletion_apply_eq_algebraMap_of_maximalIdeal_eq_span_map_of_forall_exists_sub_mem
import Theorems.Thm_AdicCompletion_isNoetherianRing_of_isNoetherianRing
import Definitions.Def_AdicCompletionLocalRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_layerRationalNodeRing_of_baseRationalNodeRing_layer_chart_of_prime
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord"

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup ModularCurve.UVCrossingModel
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 400000000 in

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
      Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A)
    {ι : Type} (K : ι → IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (hKfin : ∀ n, FiniteDimensional ↥k₀ ↥(K n))
    (An : ∀ n, ValuationSubring ↥(K n))
    (hAn : ∀ n (x : ↥(K n)), x ∈ An n ↔ (x : AlgebraicClosure ℚ) ∈ A)

    (n₀ : ι) (hn₀ : ∀ n, K n₀ ≤ K n) :
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

    ∀ (hJK : ModularCurve.jqNModC (AlgebraicClosure ℚ) q ∈ fieldBar q M') (a₀ : ↥k₀)
      (hjF : (⟨ModularCurve.jqNModC (AlgebraicClosure ℚ) q, hJK⟩ : ↥(fieldBar q M')) -
        algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a₀ : (AlgebraicClosure ℚ)) ∈ F₀)
      (hjO : (⟨_, hjF⟩ : ↥F₀) ∈ O) (eJ : ℕ) (wV : (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀))ˣ),
      1 ≤ eJ → ιO (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨_, hjO⟩) = (wV : UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀)) * (UVCrossingModel.V ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀)) ^ eJ →

    ∀ (Bx : Subring ↥F₀),
      (∀ f : ↥F₀, f ∈ Bx → f ∈ O) →
      (∀ f : ↥F₀, f ∈ O ↔ ∃ g h : ↥F₀, g ∈ Bx ∧ h ∈ Bx ∧ (∀ hh : h ∈ O, IsUnit (⟨h, hh⟩ : ↥O)) ∧ f * h = g) →
      (∃ T : Finset ↥F₀, Bx = Subring.closure
        ({f : ↥F₀ | ∃ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ∧ f = algebraMap ↥k₀ ↥F₀ x} ∪ (↑T : Set ↥F₀))) →

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

    ∀ (C' : ι → Subring (AlgebraicClosure ℚ)) (hC'A : ∀ (l : ι) (c : AlgebraicClosure ℚ), c ∈ C' l → c ∈ A)
      [∀ l, IsDomain ↥(C' l)] [∀ l, IsDiscreteValuationRing ↥(C' l)]
      (ϖ' : ∀ l, ↥(C' l))
      (Wc : ι → Type) [∀ l, CommRing (Wc l)] [∀ l, IsDomain (Wc l)] [∀ l, IsDiscreteValuationRing (Wc l)]
      [∀ l, IsAdicComplete (maximalIdeal (Wc l)) (Wc l)]
      (π : ∀ l, Wc l) (eL : ι → ℕ) (jc : ∀ l, ↥(C' l) →+* Wc l),
      (∀ (l : ι) (c : AlgebraicClosure ℚ), c ∈ C' l ↔ c ∈ A ∧ c ∈ Set.range (fun x : ↥(K l) => (x : AlgebraicClosure ℚ))) →
      (∀ (l : ι) (d : ↥(C' l)), IsLocalRing.residue A ⟨(d : AlgebraicClosure ℚ), hC'A l d d.2⟩ = 0 ↔ ∃ d' : ↥(C' l), d = ϖ' l * d') →
      (∀ l, C' n₀ ≤ C' l) →
      (∀ l, Irreducible (π l)) →
      (∀ l, ∃ v : AlgebraicClosure ℚ, v ∈ C' l ∧ v⁻¹ ∈ C' l ∧ (π₀ : AlgebraicClosure ℚ) = v * ((ϖ' l : ↥(C' l)) : AlgebraicClosure ℚ) ^ eL l) →
      (∀ l, jc l (ϖ' l) = π l) →
      (∀ (l : ι) (n : ℕ) (c : ↥(C' l)), jc l c ∈ Ideal.span {π l ^ n} → c ∈ Ideal.span {ϖ' l ^ n}) →
      (∀ (l : ι) (n : ℕ) (w : Wc l), ∃ c : ↥(C' l), w - jc l c ∈ Ideal.span {π l ^ n}) →

    ∀ (l : ι),
    ∀ (𝒩₀ : Subring ↥(fieldBar q M')), (∀ f : ↥(fieldBar q M'), f ∈ 𝒩₀ ↔ ∃ hf : f ∈ F₀, (⟨f, hf⟩ : ↥F₀) ∈ O) →
    ∀ [IsLocalRing ↥𝒩₀] [IsNoetherianRing ↥𝒩₀]
      (N1 : Subring ↥(fieldBar q M')) [IsLocalRing ↥N1] [IsNoetherianRing ↥N1] (h01 : 𝒩₀ ≤ N1),

      N1 ≤ 𝒩 →
      (∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), P ∈ S ↔
        (∀ f : ↥(fieldBar q M'), f ∈ N1 → f ∈ P.toValuationSubring) ∧
        (∀ f : ↥N1, ¬ IsUnit f → ∃ h : P.evalAt (f : ↥(fieldBar q M')) ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A)) →
      (∀ c : AlgebraicClosure ℚ, c ∈ C' n₀ → algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') c ∈ N1) →
      (∀ g : ↥N1, ∃ (o : ↥(C' n₀)) (h : algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (o : AlgebraicClosure ℚ) ∈ N1), ¬ IsUnit (g - ⟨_, h⟩)) →
      (∀ (n : ℕ) (c : Fin n → AlgebraicClosure ℚ) (a : Fin n → ↥N1), LinearIndependent ↥(C' n₀) c →
        ∑ i, c i • ((a i : ↥N1) : ↥(fieldBar q M')) = 0 → ∀ i, a i = 0) →
      (∀ f : ↥𝒩₀, ¬ IsUnit f → ¬ IsUnit (Subring.inclusion h01 f)) →
      (∀ hϖ : algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((ϖ' n₀ : ↥(C' n₀)) : AlgebraicClosure ℚ) ∈ N1,
        maximalIdeal ↥N1 ≤ (maximalIdeal ↥𝒩₀).map (Subring.inclusion h01) ⊔ Ideal.span {⟨_, hϖ⟩}) →
      (∀ (f : ↥N1) (h₁ : (f : ↥(fieldBar q M')) ∈ Rx.integers), 0 ≤ bx.ord (Rx.residue ⟨f, h₁⟩) ∧
        (¬ IsUnit f → Rx.residue ⟨f, h₁⟩ ≠ 0 → 0 < bx.ord (Rx.residue ⟨f, h₁⟩))) →
      (∀ (f : ↥N1) (h₂ : (f : ↥(fieldBar q M')) ∈ R.integers), 0 ≤ nd.ord (R.residue ⟨f, h₂⟩) ∧
        (¬ IsUnit f → R.residue ⟨f, h₂⟩ ≠ 0 → 0 < nd.ord (R.residue ⟨f, h₂⟩))) →
      2 ≤ ringKrullDim ↥N1 →

    (∃ Bx : Subring (fieldBar q M'),
    (∀ f : fieldBar q M', f ∈ Bx → f ∈ N1) ∧
    ((cx : ↥F₀) : ↥(fieldBar q M')) ∈ Bx ∧ ((cy : ↥F₀) : ↥(fieldBar q M')) ∈ Bx ∧ (((u : ↥O) : ↥F₀) : ↥(fieldBar q M')) ∈ Bx ∧
    (∀ f : fieldBar q M', f ∈ N1 ↔ ∃ g h : fieldBar q M', g ∈ Bx ∧ h ∈ Bx ∧
    (∀ hh : h ∈ N1, IsUnit (⟨h, hh⟩ : ↥(N1))) ∧ f * h = g) ∧
    (∃ T : Finset (fieldBar q M'), Bx = Subring.closure
    ({f : fieldBar q M' | ∃ c : AlgebraicClosure ℚ, c ∈ C' n₀ ∧ f = algebraMap (AlgebraicClosure ℚ) (fieldBar q M') c} ∪
    (↑T : Set (fieldBar q M'))))) →
      ∃ (Nl : Subring ↥(fieldBar q M')) (_ : IsLocalRing ↥Nl) (_ : IsNoetherianRing ↥Nl),
              N1 ≤ Nl ∧

              (l = n₀ → Nl = N1) ∧

              (∀ (f : ↥N1) (hf : (f : ↥(fieldBar q M')) ∈ Nl), ¬ IsUnit f → ¬ IsUnit (⟨(f : ↥(fieldBar q M')), hf⟩ : ↥Nl)) ∧ Nl ≤ 𝒩 ∧
              (∀ P : Place (AlgebraicClosure ℚ) (fieldBar q M'), P ∈ S ↔
                (∀ f : fieldBar q M', f ∈ Nl → f ∈ P.toValuationSubring) ∧
                (∀ f : ↥(Nl), ¬ IsUnit f → ∃ h : P.evalAt (f : fieldBar q M') ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A)) ∧
              (∀ c : AlgebraicClosure ℚ, c ∈ C' l → algebraMap (AlgebraicClosure ℚ) (fieldBar q M') c ∈ Nl) ∧
              (∀ g : ↥(Nl), ∃ (o : ↥(C' l)) (h : algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (o : AlgebraicClosure ℚ) ∈ Nl), ¬ IsUnit (g - ⟨_, h⟩)) ∧
              (∀ (n : ℕ) (c : Fin n → AlgebraicClosure ℚ) (a : Fin n → ↥(Nl)), LinearIndependent ↥(C' l) c →
                ∑ i, c i • ((a i : ↥(Nl)) : fieldBar q M') = 0 → ∀ i, a i = 0) ∧

              (∃ Bx : Subring (fieldBar q M'),
                (∀ f : fieldBar q M', f ∈ Bx → f ∈ Nl) ∧
                ((cx : ↥F₀) : ↥(fieldBar q M')) ∈ Bx ∧ ((cy : ↥F₀) : ↥(fieldBar q M')) ∈ Bx ∧ (((u : ↥O) : ↥F₀) : ↥(fieldBar q M')) ∈ Bx ∧
                (∀ f : fieldBar q M', f ∈ Nl ↔ ∃ g h : fieldBar q M', g ∈ Bx ∧ h ∈ Bx ∧
                  (∀ hh : h ∈ Nl, IsUnit (⟨h, hh⟩ : ↥(Nl))) ∧ f * h = g) ∧
                (∃ T : Finset (fieldBar q M'), Bx = Subring.closure
                  ({f : fieldBar q M' | ∃ c : AlgebraicClosure ℚ, c ∈ C' l ∧ f = algebraMap (AlgebraicClosure ℚ) (fieldBar q M') c} ∪
                    (↑T : Set (fieldBar q M'))))) ∧
              ((cx : ↥F₀) : ↥(fieldBar q M')) ∈ Nl ∧ ((cy : ↥F₀) : ↥(fieldBar q M')) ∈ Nl ∧ (∃ hu : (((u : ↥O) : ↥F₀) : ↥(fieldBar q M')) ∈ Nl, IsUnit (⟨(((u : ↥O) : ↥F₀) : ↥(fieldBar q M')), hu⟩ : ↥(Nl))) ∧
              ∃ (σ : Wc l →+* AdicCompletion (maximalIdeal ↥(Nl)) ↥(Nl))
                (ιc : AdicCompletion (maximalIdeal ↥(Nl)) ↥(Nl) ≃+* UVCrossingModel (Wc l) (π l ^ (eL l * E₀))),
                (∀ h : algebraMap (AlgebraicClosure ℚ) (fieldBar q M') ((ϖ' l : ↥(C' l)) : AlgebraicClosure ℚ) ∈ Nl,
                  σ (π l) = algebraMap ↥(Nl) (AdicCompletion (maximalIdeal ↥(Nl)) ↥(Nl)) ⟨_, h⟩) ∧
                (∀ o : Wc l, ιc (σ o) = const (π l ^ (eL l * E₀)) o) ∧

                (∃ (hJ : (⟨ModularCurve.jqNModC (AlgebraicClosure ℚ) q, hJK⟩ : ↥(fieldBar q M')) -
                      algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a₀ : AlgebraicClosure ℚ) ∈ Nl)
                   (e : ℕ) (w : (UVCrossingModel (Wc l) (π l ^ (eL l * E₀)))ˣ), 1 ≤ e ∧
                  ιc (algebraMap ↥(Nl) (AdicCompletion (maximalIdeal ↥(Nl)) ↥(Nl)) ⟨_, hJ⟩) =
                    (w : UVCrossingModel (Wc l) (π l ^ (eL l * E₀))) * V (π l ^ (eL l * E₀)) ^ e) ∧
                (∀ (c : ↥(C' l)) (h : algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (c : AlgebraicClosure ℚ) ∈ Nl),
                  ∃ o : Wc l, σ o = algebraMap ↥(Nl) (AdicCompletion (maximalIdeal ↥(Nl)) ↥(Nl)) ⟨_, h⟩) ∧
                (∀ (f : ↥(Nl)) (n : ℕ) (h₁ : f.1 ∈ Rx.integers), Rx.residue ⟨f.1, h₁⟩ ≠ 0 →
                  bx.ord (Rx.residue ⟨f.1, h₁⟩) = (n : ℤ) →
                    ∃ γ : UVCrossingModel (Wc l) (π l ^ (eL l * E₀)), IsUnit γ ∧
                      ιc (algebraMap ↥(Nl) (AdicCompletion (maximalIdeal ↥(Nl)) ↥(Nl)) f) - γ * V (π l ^ (eL l * E₀)) ^ n ∈
                        Ideal.span {const (π l ^ (eL l * E₀)) (π l), U (π l ^ (eL l * E₀))}) ∧
                (∀ (f : ↥(Nl)) (n : ℕ) (h₂ : f.1 ∈ R.integers), R.residue ⟨f.1, h₂⟩ ≠ 0 →
                  nd.ord (R.residue ⟨f.1, h₂⟩) = (n : ℤ) →
                    ∃ γ : UVCrossingModel (Wc l) (π l ^ (eL l * E₀)), IsUnit γ ∧
                      ιc (algebraMap ↥(Nl) (AdicCompletion (maximalIdeal ↥(Nl)) ↥(Nl)) f) - γ * U (π l ^ (eL l * E₀)) ^ n ∈
                        Ideal.span {const (π l ^ (eL l * E₀)) (π l), V (π l ^ (eL l * E₀))}) := by
  intro F₀ hK1 hLD W₀ hW₀ O instOL instON hOW hOk hOres hFrac E₀ hE₀ hπO cx cy u ιO γU γV hcxy hιconst hιcx hιcy hcyW hcym hcxm
    hJK a₀ hjF hjO eJ wV heJ hgerm Bx hBxO hBxloc hBxfg
    FI instFI instAFI Rx bx hbx hORx hcI1 hcI2 hcxI hcyI
    FSS instFS instAFS R nd hRW hnd hcS1 hcS2 hcyS hcxS
    S hS hrat 𝒩 h𝒩 hval
    C' hC'A instCD instCV ϖ' Wc instW1 instW2 instW3 instW4 π eL jc hC'K hC'ϖ hC'le hπirr hram hjcϖ hjcinj hjcsur
    l 𝒩₀ h𝒩₀ inst0L inst0N N1 inst1L inst1N h01 h1le hS1c hCmem1 hres1 hld1 hloc1 hgen1 hreg11 hreg21 hdim1 hchart1
  classical

  haveI hA0dvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) := hdvr
  let C : Subring (AlgebraicClosure ℚ) := ((A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))).toSubring.map (algebraMap ↥k₀ (AlgebraicClosure ℚ))
  have hC : ∀ c : AlgebraicClosure ℚ, c ∈ C ↔ c ∈ A ∧ c ∈ (⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) := by
    intro c
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(ValuationSubring.mem_comap).mp hx, IntermediateField.algebraMap_mem ⊥ x⟩
    · rintro ⟨hcA, hcbot⟩
      rw [IntermediateField.mem_bot] at hcbot
      obtain ⟨x, rfl⟩ := hcbot
      exact ⟨x, (ValuationSubring.mem_comap).mpr hcA, rfl⟩
  have hψ : ∀ f : ↥F₀, algebraMap ↥F₀ ↥(fieldBar q M') f = (f : ↥(fieldBar q M')) := fun f => rfl
  have hψk : ∀ x : ↥k₀, ((algebraMap ↥k₀ ↥F₀ x : ↥F₀) : ↥(fieldBar q M')) =
      algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (x : AlgebraicClosure ℚ) := fun x => rfl
  have hmem0 : ∀ (f : ↥F₀), f ∈ O → (f : ↥(fieldBar q M')) ∈ 𝒩₀ := fun f hf => (h𝒩₀ _).2 ⟨f.2, by simpa using hf⟩

  have hLH := ModularCurve.FullLevel.exists_baseRationalNodeRing_input_of_node_ends_nodePlaces_of_prime q M' hqM' A hA k₀ π₀ hπ hdvr hunif hhens hres hκ F₀ hK1 hLD W₀ hW₀ O hOW hOk hOres hFrac E₀ hE₀ hπO cx cy u ιO γU γV hcxy hιconst hιcx hιcy hcyW hcym hcxm
      FI Rx bx hbx hORx hcI1 hcI2 hcxI hcyI FSS R nd hRW hnd hcS1 hcS2 hcyS hcxS S hS hrat 𝒩 h𝒩 hval C hC 𝒩₀ h𝒩₀
  obtain ⟨-, -, hSne, h0le, -, -, -, -, -, -, hcx0, hcy0, xf, xs, ys, yf⟩ := hLH

  have hC'K' : ∀ (m : ι) (c : AlgebraicClosure ℚ), c ∈ C' m ↔ c ∈ A ∧ c ∈ K m := by
    intro m c
    rw [hC'K m c]
    constructor
    · rintro ⟨h1, ⟨x, hx⟩⟩
      exact ⟨h1, hx ▸ x.2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, ⟨⟨c, h2⟩, rfl⟩⟩
  haveI : FiniteDimensional ↥k₀ ↥(K n₀) := hKfin n₀
  haveI : FiniteDimensional ↥k₀ ↥(K l) := hKfin l
  have hpack : ∃ (Nl : Subring ↥(fieldBar q M')) (_ : IsLocalRing ↥Nl) (_ : IsNoetherianRing ↥Nl) (h1l : N1 ≤ Nl),
      (l = n₀ → Nl = N1) ∧ Nl ≤ 𝒩 ∧
      (∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), P ∈ S ↔
        (∀ f : ↥(fieldBar q M'), f ∈ Nl → f ∈ P.toValuationSubring) ∧
        (∀ f : ↥Nl, ¬ IsUnit f → ∃ h : P.evalAt (f : ↥(fieldBar q M')) ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A)) ∧
      (∀ c : AlgebraicClosure ℚ, c ∈ C' l → algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') c ∈ Nl) ∧
      (∀ g : ↥Nl, ∃ (o : ↥(C' l)) (h : algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (o : AlgebraicClosure ℚ) ∈ Nl), ¬ IsUnit (g - ⟨_, h⟩)) ∧
      (∀ (n : ℕ) (c : Fin n → AlgebraicClosure ℚ) (a : Fin n → ↥Nl), LinearIndependent ↥(C' l) c →
        ∑ i, c i • ((a i : ↥Nl) : ↥(fieldBar q M')) = 0 → ∀ i, a i = 0) ∧
      (∀ f : ↥N1, ¬ IsUnit f → ¬ IsUnit (Subring.inclusion h1l f)) ∧
      (∀ hϖ : algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((ϖ' l : ↥(C' l)) : AlgebraicClosure ℚ) ∈ Nl,
        maximalIdeal ↥Nl ≤ (maximalIdeal ↥N1).map (Subring.inclusion h1l) ⊔ Ideal.span {⟨_, hϖ⟩}) ∧
      (∀ (f : ↥Nl) (h₁ : (f : ↥(fieldBar q M')) ∈ Rx.integers), 0 ≤ bx.ord (Rx.residue ⟨f, h₁⟩) ∧
        (¬ IsUnit f → Rx.residue ⟨f, h₁⟩ ≠ 0 → 0 < bx.ord (Rx.residue ⟨f, h₁⟩))) ∧
      (∀ (f : ↥Nl) (h₂ : (f : ↥(fieldBar q M')) ∈ R.integers), 0 ≤ nd.ord (R.residue ⟨f, h₂⟩) ∧
        (¬ IsUnit f → R.residue ⟨f, h₂⟩ ≠ 0 → 0 < nd.ord (R.residue ⟨f, h₂⟩))) ∧
      2 ≤ ringKrullDim ↥Nl ∧
      (∃ Bx : Subring (fieldBar q M'),
        (∀ f : fieldBar q M', f ∈ Bx → f ∈ Nl) ∧
        ((cx : ↥F₀) : ↥(fieldBar q M')) ∈ Bx ∧ ((cy : ↥F₀) : ↥(fieldBar q M')) ∈ Bx ∧ (((u : ↥O) : ↥F₀) : ↥(fieldBar q M')) ∈ Bx ∧
        (∀ f : fieldBar q M', f ∈ Nl ↔ ∃ g h : fieldBar q M', g ∈ Bx ∧ h ∈ Bx ∧
          (∀ hh : h ∈ Nl, IsUnit (⟨h, hh⟩ : ↥(Nl))) ∧ f * h = g) ∧
        (∃ T : Finset (fieldBar q M'), Bx = Subring.closure
          ({f : fieldBar q M' | ∃ c : AlgebraicClosure ℚ, c ∈ C' l ∧ f = algebraMap (AlgebraicClosure ℚ) (fieldBar q M') c} ∪
            (↑T : Set (fieldBar q M'))))) := by
    by_cases hl : l = n₀
    · subst hl
      refine ⟨N1, inst1L, inst1N, le_rfl, fun _ => rfl, h1le, hS1c, hCmem1, hres1, hld1, ?_, ?_, hreg11, hreg21, hdim1, hchart1⟩
      · intro f hf
        have : Subring.inclusion (le_refl N1) f = f := Subtype.ext rfl
        rwa [this]
      · intro hϖ z hz
        refine Ideal.mem_sup_left ?_
        have : Subring.inclusion (le_refl N1) z = z := Subtype.ext rfl
        rw [← this]
        exact Ideal.mem_map_of_mem _ hz
    ·
      have hBC := AlgebraicCurve.NodeAnnulusEngine.exists_localizedBaseChange_of_layer_pos_localization
        (k := ↥k₀) (L := AlgebraicClosure ℚ) A (F := ↥(fieldBar q M'))
        Rx R bx nd S hrat hSne 𝒩 h𝒩 hval (K n₀) (K l) (hn₀ l)
        (C' n₀) (hC'K' n₀) (hC'A n₀) (C' l) (hC'K' l) (hC'A l) (ϖ' l) (hC'ϖ l) N1 h1le hS1c hCmem1 hres1 hld1 hreg11 hreg21
        ((cx : ↥F₀) : ↥(fieldBar q M')) ((cy : ↥F₀) : ↥(fieldBar q M')) (h01 hcx0) (h01 hcy0) xf xs ys yf
      obtain ⟨Nl, instL, instN, h1l, hl𝒩, hSl, hCl, hresl, hldl, hlocl, hgenl, hreg1l, hreg2l, hdiml, hpresl⟩ := hBC
      refine ⟨Nl, instL, instN, h1l, fun h => absurd h hl, hl𝒩, hSl, hCl, hresl, hldl, hlocl, hgenl, hreg1l, hreg2l, hdiml, ?_⟩

      obtain ⟨B1, hB1le, hcxB, hcyB, huB, hN1loc, ⟨T1, hB1T⟩⟩ := hchart1
      have hpres := hpresl B1 hB1le hN1loc
      have hC0l : ({f : ↥(fieldBar q M') | ∃ c : AlgebraicClosure ℚ, c ∈ C' n₀ ∧ f = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') c} : Set ↥(fieldBar q M')) ⊆ ({f : ↥(fieldBar q M') | ∃ c : AlgebraicClosure ℚ, c ∈ C' l ∧ f = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') c} : Set ↥(fieldBar q M')) := by
        rintro f ⟨c, hc, rfl⟩
        exact ⟨c, hC'le l hc, rfl⟩
      refine ⟨Subring.closure ((B1 : Set ↥(fieldBar q M')) ∪ {f : ↥(fieldBar q M') | ∃ c : AlgebraicClosure ℚ, c ∈ C' l ∧ f = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') c}), ?_, ?_, ?_, ?_, hpres, ⟨T1, ?_⟩⟩
      · intro f hf
        refine (Subring.closure_le.2 ?_) hf
        rintro g (hg | ⟨c, hc, rfl⟩)
        · exact h1l (hB1le g hg)
        · exact hCl c hc
      · exact Subring.subset_closure (Or.inl hcxB)
      · exact Subring.subset_closure (Or.inl hcyB)
      · exact Subring.subset_closure (Or.inl huB)
      · apply le_antisymm
        · refine Subring.closure_le.2 ?_
          rintro g (hg | hg)
          · have hg' : g ∈ Subring.closure (({f : ↥(fieldBar q M') | ∃ c : AlgebraicClosure ℚ, c ∈ C' n₀ ∧ f = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') c} : Set ↥(fieldBar q M')) ∪ (↑T1 : Set ↥(fieldBar q M'))) := by rw [← hB1T]; exact hg
            refine Subring.closure_mono ?_ hg'
            rintro t (ht | ht)
            · exact Or.inl (hC0l ht)
            · exact Or.inr ht
          · exact Subring.subset_closure (Or.inl hg)
        · refine Subring.closure_le.2 ?_
          rintro g (hg | hg)
          · exact Subring.subset_closure (Or.inr hg)
          · have : g ∈ B1 := by rw [hB1T]; exact Subring.subset_closure (Or.inr hg)
            exact Subring.subset_closure (Or.inl this)
  obtain ⟨Nl, instL, instN, h1l, hEq, hNl𝒩, hSl, hCl, hresl, hldl, hlocl, hgenl, hreg1l, hreg2l, hdiml, hchartl⟩ := hpack
  haveI : IsLocalRing ↥Nl := instL
  haveI : IsNoetherianRing ↥Nl := instN
  have h0l : 𝒩₀ ≤ Nl := h01.trans h1l
  have hloc0l : ∀ f : ↥𝒩₀, ¬ IsUnit f → ¬ IsUnit (Subring.inclusion h0l f) := by
    intro f hf
    have h1 := hloc1 f hf
    have h2 := hlocl (Subring.inclusion h01 f) h1
    exact h2
  have hNlRx : ∀ f : ↥(fieldBar q M'), f ∈ Nl → f ∈ Rx.integers := fun f hf => ((h𝒩 f).1 (hNl𝒩 hf)).1
  have hNlR : ∀ f : ↥(fieldBar q M'), f ∈ Nl → f ∈ R.integers := fun f hf => ((h𝒩 f).1 (hNl𝒩 hf)).2.1

  have hϖ'N : ∀ c : ↥(C' l), algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c : AlgebraicClosure ℚ) ∈ Nl := fun c => hCl c c.2

  have hϖ₀res : IsLocalRing.residue ↥A ⟨((ϖ' n₀ : ↥(C' n₀)) : AlgebraicClosure ℚ), hC'A n₀ _ (ϖ' n₀).2⟩ = 0 :=
    (hC'ϖ n₀ (ϖ' n₀)).2 ⟨1, (mul_one _).symm⟩
  have hϖ₀l : ((ϖ' n₀ : ↥(C' n₀)) : AlgebraicClosure ℚ) ∈ C' l := hC'le l (ϖ' n₀).2
  obtain ⟨dϖ, hdϖ⟩ := (hC'ϖ l ⟨_, hϖ₀l⟩).1 hϖ₀res
  have hgen0l : maximalIdeal ↥Nl ≤ (maximalIdeal ↥𝒩₀).map (Subring.inclusion h0l) ⊔
      Ideal.span {⟨algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((ϖ' l : ↥(C' l)) : AlgebraicClosure ℚ), hCl _ (ϖ' l).2⟩} := by
    intro z hz
    have hz1 := hgenl (hCl _ (ϖ' l).2) hz

    rcases Submodule.mem_sup.1 hz1 with ⟨z₁, hz₁, z₂, hz₂, rfl⟩
    refine add_mem ?_ (Ideal.mem_sup_right hz₂)
    refine (Ideal.map_le_iff_le_comap.2 (fun y hy => Ideal.mem_comap.2 ?_)) hz₁
    have hy1 := hgen1 (hCmem1 _ (ϖ' n₀).2) hy
    obtain ⟨y₁, hy₁, y₂, hy₂, hyeq⟩ := Submodule.mem_sup.1 hy1
    rw [← hyeq, map_add]
    refine add_mem (Ideal.mem_sup_left ?_) (Ideal.mem_sup_right ?_)
    · have hy₁' := Ideal.mem_map_of_mem (Subring.inclusion h1l) hy₁
      rw [Ideal.map_map] at hy₁'
      refine (Ideal.map_le_iff_le_comap.2 (fun a ha => Ideal.mem_comap.2 ?_)) hy₁'
      have : ((Subring.inclusion h1l).comp (Subring.inclusion h01)) a = Subring.inclusion h0l a := Subtype.ext rfl
      rw [this]
      exact Ideal.mem_map_of_mem _ ha
    · obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 hy₂
      rw [map_mul]
      refine Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton'.2
        ⟨⟨algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((dϖ : ↥(C' l)) : AlgebraicClosure ℚ), hCl _ dϖ.2⟩, ?_⟩)
      apply Subtype.ext
      have h1 := congrArg Subtype.val hdϖ
      rw [MulMemClass.coe_mul] at h1
      have h2 := congrArg (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) h1
      rw [map_mul, mul_comm] at h2
      rw [MulMemClass.coe_mul]
      exact h2.symm
  have heEl : 1 ≤ eL l * E₀ := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by

    obtain ⟨v, hv, hvi, hπv⟩ := hram l
    intro h0
    rw [h0, pow_zero, mul_one] at hπv

    have hπ0notunit : ¬ IsUnit (⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) := by
      have hm : (⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ∈ maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) := by
        rw [hunif]; exact Ideal.mem_span_singleton_self _
      exact (mem_nonunits_iff).1 ((mem_maximalIdeal _).1 hm)
    apply hπ0notunit
    refine isUnit_iff_exists_inv.2 ⟨⟨π₀⁻¹, ?_⟩, ?_⟩
    · show algebraMap ↥k₀ (AlgebraicClosure ℚ) π₀⁻¹ ∈ A
      rw [map_inv₀]
      show ((π₀ : AlgebraicClosure ℚ))⁻¹ ∈ A
      rw [hπv]; exact hC'A l _ hvi
    · apply Subtype.ext
      have : (π₀ : ↥k₀) ≠ 0 := by
        intro h
        apply IsDiscreteValuationRing.not_a_field ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))
        rw [hunif, Ideal.span_singleton_eq_bot]
        exact Subtype.ext h
      show (π₀ : ↥k₀) * π₀⁻¹ = 1
      exact mul_inv_cancel₀ this) (by omega))

  haveI hW0noe : IsNoetherianRing (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) :=
    AdicCompletion.isNoetherianRing_of_isNoetherianRing _
  obtain ⟨Wa, iWa1, iWa2, iWa3, iWa4, σa, -, hσamap, hσadense⟩ :=
    IsDiscreteValuationRing.exists_isAdicComplete_map_maximalIdeal_eq_forall_sub_mem_maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))
  have hWamax : maximalIdeal Wa = Ideal.span {σa ⟨π₀, hπ⟩} := by
    rw [← hσamap, hunif, Ideal.map_span, Set.image_singleton]
  obtain ⟨ρ, hρ⟩ :=
    IsDiscreteValuationRing.exists_ringEquiv_adicCompletion_apply_eq_algebraMap_of_maximalIdeal_eq_span_map_of_forall_exists_sub_mem
      ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ⟨π₀, hπ⟩ hunif Wa σa hWamax hσadense
  haveI hW0dom : IsDomain (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) := MulEquiv.isDomain Wa ρ.symm.toMulEquiv
  haveI hW0dvr : IsDiscreteValuationRing (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing ρ
  haveI hW0cpl : IsAdicComplete (maximalIdeal (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
      (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) := by
    rw [AdicCompletion.maximalIdeal_eq_map]
    exact (IsAdicComplete.map_algebraMap_iff (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))).mpr
      (AdicCompletion.isAdicComplete AdicCompletion.maximalIdeal_fg)
  have hpiWirr : Irreducible (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) := by
    have h1 : Irreducible (σa ⟨π₀, hπ⟩) := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hWamax
    have h2 := h1.map ρ
    rwa [hρ] at h2

  have hOmap : O.map (algebraMap ↥F₀ ↥(fieldBar q M')) = 𝒩₀ := by
    ext f
    rw [h𝒩₀]
    constructor
    · rintro ⟨x, hx, hxf⟩
      rw [hψ] at hxf
      subst hxf
      exact ⟨x.2, by simpa using hx⟩
    · rintro ⟨hf, hO⟩
      exact ⟨⟨f, hf⟩, hO, rfl⟩
  let eON : ↥O ≃+* ↥𝒩₀ :=
    (O.equivMapOfInjective (algebraMap ↥F₀ ↥(fieldBar q M')) (algebraMap ↥F₀ ↥(fieldBar q M')).injective).trans
      (RingEquiv.subringCongr hOmap)
  have heON : ∀ (f : ↥F₀) (hf : f ∈ O), eON ⟨f, hf⟩ = ⟨(f : ↥(fieldBar q M')), hmem0 f hf⟩ := by
    intro f hf
    apply Subtype.ext
    show ((O.equivMapOfInjective (algebraMap ↥F₀ ↥(fieldBar q M'))
      (algebraMap ↥F₀ ↥(fieldBar q M')).injective ⟨f, hf⟩ : ↥(O.map (algebraMap ↥F₀ ↥(fieldBar q M')))) :
        ↥(fieldBar q M')) = f
    rw [Subring.coe_equivMapOfInjective_apply]
    rfl
  obtain ⟨ê, hê⟩ := IsLocalRing.exists_ringEquiv_adicCompletion_maximalIdeal_comp_algebraMap_of_ringEquiv eON
  let ι₀ : AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀ ≃+*
      UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀) := ê.symm.trans ιO
  have hι₀O : ∀ (f : ↥F₀) (hf : f ∈ O),
      ι₀ (algebraMap ↥𝒩₀ _ ⟨(f : ↥(fieldBar q M')), hmem0 f hf⟩) = ιO (algebraMap ↥O _ ⟨f, hf⟩) := by
    intro f hf
    show ιO (ê.symm (algebraMap ↥𝒩₀ _ ⟨(f : ↥(fieldBar q M')), hmem0 f hf⟩)) = _
    rw [← heON f hf, ← hê, RingEquiv.symm_apply_apply]
  let σ₀ : AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) →+* AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀ :=
    ι₀.symm.toRingHom.comp (UVCrossingModel.constHom ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀))
  have hσ₀const : ∀ o, ι₀ (σ₀ o) = const ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀) o := by
    intro o
    show ι₀ (ι₀.symm (UVCrossingModel.constHom ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀) o)) = _
    rw [RingEquiv.apply_symm_apply, UVCrossingModel.constHom_apply]

  have hπ₀F : algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (π₀ : AlgebraicClosure ℚ) ∈ 𝒩₀ := by
    rw [← hψk]; exact hmem0 _ hπO
  have hπ₀N_eq : (⟨algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (π₀ : AlgebraicClosure ℚ), hπ₀F⟩ : ↥𝒩₀) =
      ⟨((algebraMap ↥k₀ ↥F₀ π₀ : ↥F₀) : ↥(fieldBar q M')), hmem0 _ hπO⟩ := Subtype.ext (by rw [hψk])
  have hσ₀π : σ₀ (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) = algebraMap ↥𝒩₀ (AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀)
      ⟨algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (π₀ : AlgebraicClosure ℚ), hπ₀F⟩ := by
    apply ι₀.injective
    rw [hσ₀const, hπ₀N_eq, hι₀O _ hπO, hιconst π₀ hπ hπO]

  have hι₀x : ι₀ (algebraMap ↥𝒩₀ _ ⟨((cx : ↥F₀) : ↥(fieldBar q M')), hcx0⟩) = (γU : UVCrossingModel _ ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀)) * U ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀) := by
    rw [hι₀O (cx : ↥F₀) (cx : ↥O).2, Subtype.coe_eta, hιcx]
  have hι₀y : ι₀ (algebraMap ↥𝒩₀ _ ⟨((cy : ↥F₀) : ↥(fieldBar q M')), hcy0⟩) = (γV : UVCrossingModel _ ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀)) * V ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀) := by
    rw [hι₀O (cy : ↥F₀) (cy : ↥O).2, Subtype.coe_eta, hιcy]
  have hJ0 : ((⟨_, hjF⟩ : ↥F₀) : ↥(fieldBar q M')) ∈ 𝒩₀ := hmem0 _ hjO
  have hι₀J : ι₀ (algebraMap ↥𝒩₀ _ ⟨((⟨_, hjF⟩ : ↥F₀) : ↥(fieldBar q M')), hJ0⟩) = (wV : UVCrossingModel _ ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀)) * V ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀) ^ eJ := by
    rw [hι₀O _ hjO, hgerm]

  obtain ⟨σ', ι', hσ'j, hconst', hmaxl, hadx, hady, θ, βU, βV, hβU, hβV, hθU, hθV, hθ⟩ :=
    AlgebraicCurve.NodeAnnulusEngine.exists_ringEquiv_adicCompletion_uvCrossingModel_of_layer_compatibleUV
      (L := AlgebraicClosure ℚ) (F := ↥(fieldBar q M')) 𝒩₀ (π₀ : AlgebraicClosure ℚ) hπ₀F
      (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) hpiWirr σ₀ hσ₀π E₀ hE₀ ι₀ hσ₀const
      ((cx : ↥F₀) : ↥(fieldBar q M')) ((cy : ↥F₀) : ↥(fieldBar q M')) hcx0 hcy0
      ⟨γU, Units.isUnit _, by rw [hι₀x, mul_comm, sub_self]; exact zero_mem _⟩
      ⟨γV, Units.isUnit _, by rw [hι₀y, mul_comm, sub_self]; exact zero_mem _⟩
      (C' l) (ϖ' l) (eL l) (hram l)
      Nl h0l hloc0l hCl hresl hgen0l hdiml
      (π l) (hπirr l) (jc l) (hjcϖ l) (hjcinj l) (hjcsur l)

  have hι'x : ι' (algebraMap ↥Nl _ (⟨((cx : ↥F₀) : ↥(fieldBar q M')), h0l hcx0⟩ : ↥Nl)) = (θ γU * βU) * U (π l ^ (eL l * E₀)) := by
    rw [hθ _ hcx0, hι₀x, map_mul, hθU, mul_assoc]
  have hι'y : ι' (algebraMap ↥Nl _ (⟨((cy : ↥F₀) : ↥(fieldBar q M')), h0l hcy0⟩ : ↥Nl)) = (θ γV * βV) * V (π l ^ (eL l * E₀)) := by
    rw [hθ _ hcy0, hι₀y, map_mul, hθV, mul_assoc]
  have hΓU : IsUnit (θ (γU : UVCrossingModel _ ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀)) * βU) := ((Units.isUnit γU).map θ).mul hβU
  have hΓV : IsUnit (θ (γV : UVCrossingModel _ ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀)) * βV) := ((Units.isUnit γV).map θ).mul hβV
  have hσ'π : σ' (π l) = algebraMap ↥Nl _ (⟨algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((ϖ' l : ↥(C' l)) : AlgebraicClosure ℚ), hCl _ (ϖ' l).2⟩ : ↥Nl) := by rw [← hjcϖ l, hσ'j]
  have hι'ϖ : ι' (algebraMap ↥Nl _ (⟨algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((ϖ' l : ↥(C' l)) : AlgebraicClosure ℚ), hCl _ (ϖ' l).2⟩ : ↥Nl)) = const (π l ^ (eL l * E₀)) (π l) := by
    rw [← hσ'π]; exact hconst' (π l)

  have hNlRxle : Nl ≤ Rx.integers.toSubring := fun f hf => hNlRx f hf
  have hNlRle : Nl ≤ R.integers.toSubring := fun f hf => hNlR f hf
  let rU : ↥Nl →+* FI := Rx.residue.comp (Subring.inclusion hNlRxle)
  let rV : ↥Nl →+* FSS := R.residue.comp (Subring.inclusion hNlRle)
  have hrU : ∀ f : ↥Nl, rU f = Rx.residue ⟨(f : ↥(fieldBar q M')), hNlRx f f.2⟩ := fun f => rfl
  have hrV : ∀ f : ↥Nl, rV f = R.residue ⟨(f : ↥(fieldBar q M')), hNlR f f.2⟩ := fun f => rfl
  haveI hPUprime : (RingHom.ker rU).IsPrime := RingHom.ker_isPrime rU
  haveI hPVprime : (RingHom.ker rV).IsPrime := RingHom.ker_isPrime rV

  have hϖlA : ((ϖ' l : ↥(C' l)) : AlgebraicClosure ℚ) ∈ A := hC'A l _ (ϖ' l).2
  have hϖlres : IsLocalRing.residue ↥A ⟨((ϖ' l : ↥(C' l)) : AlgebraicClosure ℚ), hϖlA⟩ = 0 :=
    (hC'ϖ l (ϖ' l)).2 ⟨1, (mul_one _).symm⟩
  have hϖU : (⟨algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((ϖ' l : ↥(C' l)) : AlgebraicClosure ℚ), hCl _ (ϖ' l).2⟩ : ↥Nl) ∈ RingHom.ker rU := by
    rw [RingHom.mem_ker, hrU]
    have := Rx.residue_algebraMap ⟨_, hϖlA⟩
    rw [hϖlres, map_zero] at this
    exact this
  have hϖV : (⟨algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((ϖ' l : ↥(C' l)) : AlgebraicClosure ℚ), hCl _ (ϖ' l).2⟩ : ↥Nl) ∈ RingHom.ker rV := by
    rw [RingHom.mem_ker, hrV]
    have := R.residue_algebraMap ⟨_, hϖlA⟩
    rw [hϖlres, map_zero] at this
    exact this
  have hxU : (⟨((cx : ↥F₀) : ↥(fieldBar q M')), h0l hcx0⟩ : ↥Nl) ∈ RingHom.ker rU := by rw [RingHom.mem_ker, hrU]; exact hcxI _
  have hyU : (⟨((cy : ↥F₀) : ↥(fieldBar q M')), h0l hcy0⟩ : ↥Nl) ∉ RingHom.ker rU := by rw [RingHom.mem_ker, hrU]; exact yf _
  have hyV : (⟨((cy : ↥F₀) : ↥(fieldBar q M')), h0l hcy0⟩ : ↥Nl) ∈ RingHom.ker rV := by rw [RingHom.mem_ker, hrV]; exact hcyS _
  have hxV : (⟨((cx : ↥F₀) : ↥(fieldBar q M')), h0l hcx0⟩ : ↥Nl) ∉ RingHom.ker rV := by rw [RingHom.mem_ker, hrV]; exact xs _
  have hπlmax : maximalIdeal (Wc l) = Ideal.span {π l} := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 (hπirr l)
  obtain ⟨hDV, hDU, -, -⟩ :=
    IsLocalRing.exists_branchReadings_of_ringEquiv_adicCompletion_uvCrossingModel_pow
      (π l) hπlmax (eL l * E₀) heEl ι' (⟨algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((ϖ' l : ↥(C' l)) : AlgebraicClosure ℚ), hCl _ (ϖ' l).2⟩ : ↥Nl) hι'ϖ (⟨((cx : ↥F₀) : ↥(fieldBar q M')), h0l hcx0⟩ : ↥Nl) (⟨((cy : ↥F₀) : ↥(fieldBar q M')), h0l hcy0⟩ : ↥Nl) hΓU.unit hΓV.unit
      (by rw [hι'x, IsUnit.unit_spec]) (by rw [hι'y, IsUnit.unit_spec])
      (RingHom.ker rV) (RingHom.ker rU) hϖV hyV hxV hϖU hxU hyU
  have hkerU : ∀ f : ↥Nl, Rx.residue ⟨f, hNlRx f f.2⟩ = 0 ↔
      ι' (algebraMap ↥Nl _ f) ∈ Ideal.span {const (π l ^ (eL l * E₀)) (π l), U (π l ^ (eL l * E₀))} := by
    intro f; rw [← hrU, ← RingHom.mem_ker]; exact hDU f
  have hkerV : ∀ f : ↥Nl, R.residue ⟨f, hNlR f f.2⟩ = 0 ↔
      ι' (algebraMap ↥Nl _ f) ∈ Ideal.span {const (π l ^ (eL l * E₀)) (π l), V (π l ^ (eL l * E₀))} := by
    intro f; rw [← hrV, ← RingHom.mem_ker]; exact hDV f
  have hres2 : ∀ g : ↥Nl, ∃ o : ↥(C' l), ¬ IsUnit (g - ⟨algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (o : AlgebraicClosure ℚ), hCl (o : AlgebraicClosure ℚ) o.2⟩) := by
    intro g
    obtain ⟨o, h, ho⟩ := hresl g
    exact ⟨o, ho⟩
  have hVlaw := AlgebraicCurve.NodeAnnulusEngine.exists_isUnit_sub_mul_V_pow_mem_of_ord_residue_eq_of_ringEquiv_uvCrossingModel
    A Rx bx Nl hNlRx (C' l) (hC'A l) hCl (ϖ' l) hres2 (π l) (hπirr l) σ' hσ'π (eL l * E₀) heEl ι' hconst' (⟨((cx : ↥F₀) : ↥(fieldBar q M')), h0l hcx0⟩ : ↥Nl) (⟨((cy : ↥F₀) : ↥(fieldBar q M')), h0l hcy0⟩ : ↥Nl)
    ⟨_, hΓU, by rw [hι'x, sub_self]; exact zero_mem _⟩ ⟨_, hΓV, by rw [hι'y, sub_self]; exact zero_mem _⟩
    hkerU (fun f hf hne => (hreg1l f (hNlRx f f.2)).2 hf hne) (hcxI _) (hcyI _)
  have hUlaw := AlgebraicCurve.NodeAnnulusEngine.exists_isUnit_sub_mul_U_pow_mem_of_ord_residue_eq_of_ringEquiv_uvCrossingModel
    A R nd Nl hNlR (C' l) (hC'A l) hCl (ϖ' l) hres2 (π l) (hπirr l) σ' hσ'π (eL l * E₀) heEl ι' hconst' (⟨((cx : ↥F₀) : ↥(fieldBar q M')), h0l hcx0⟩ : ↥Nl) (⟨((cy : ↥F₀) : ↥(fieldBar q M')), h0l hcy0⟩ : ↥Nl)
    ⟨_, hΓU, by rw [hι'x, sub_self]; exact zero_mem _⟩ ⟨_, hΓV, by rw [hι'y, sub_self]; exact zero_mem _⟩
    hkerV (fun f hf hne => (hreg2l f (hNlR f f.2)).2 hf hne) (hcyS _) (hcxS _)

  have huNl : ∃ hu : (((u : ↥O) : ↥F₀) : ↥(fieldBar q M')) ∈ Nl,
      IsUnit (⟨(((u : ↥O) : ↥F₀) : ↥(fieldBar q M')), hu⟩ : ↥Nl) := by
    refine ⟨h0l (hmem0 _ (u : ↥O).2), ?_⟩
    have h1 : IsUnit (eON ⟨((u : ↥O) : ↥F₀), (u : ↥O).2⟩) := by
      rw [Subtype.coe_eta]; exact (Units.isUnit u).map eON
    rw [heON] at h1
    exact h1.map (Subring.inclusion h0l)
  refine ⟨Nl, instL, instN, h1l, hEq, ?_, hNl𝒩, hSl, hCl, hresl, hldl, hchartl, h0l hcx0, h0l hcy0, huNl,
    σ', ι', ?_, hconst', ?_, ?_, ?_, ?_⟩
  ·
    intro f hf hnu
    exact hlocl f hnu
  · intro h
    rw [hσ'π]
  ·
    refine ⟨h0l hJ0, eJ, ((Units.isUnit wV).map θ).mul (hβV.pow eJ) |>.unit, heJ, ?_⟩
    rw [IsUnit.unit_spec, hθ _ hJ0, hι₀J, map_mul, map_pow, hθV, mul_pow, mul_assoc]
  · intro c h
    exact ⟨jc l c, by rw [hσ'j]⟩
  · intro f n h₁ hne hord
    exact ((hVlaw f n hne).2 hord)
  · intro f n h₂ hne hord
    exact ((hUlaw f n hne).2 hord)

end S_ModularCurve_FullLevel_exists_layerRationalNodeRing_of_baseRationalNodeRing_layer_chart_of_prime
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_layerRationalNodeRing_of_baseRationalNodeRing_layer_chart_of_prime (solution)
