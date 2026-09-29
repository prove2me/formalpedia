-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_layeredRationalNodeRings_of_node_ends_layers
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/35d81239-2ec4-5403-8fb8-86f796a5589c

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
import Theorems.Thm_ModularCurve_FullLevel_exists_baseRationalNodeRing_input_of_node_ends_nodePlaces
import Theorems.Thm_ModularCurve_FullLevel_exists_layerRationalNodeRing_of_baseRationalNodeRing_layer_chart
import Theorems.Thm_ModularCurve_FullLevel_exists_mul_mem_eq_sum_smul_of_adjoin_sup_eq_top_of_fractionRing
import Theorems.Thm_AlgebraicCurve_NodeAnnulusEngine_exists_localizedBaseChange_of_layer_pos_localization
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_layeredRationalNodeRings_of_node_ends_layers
p2m_attr_erase "instance" "AdicCompletion.instIsLocalRingMaximalIdeal instTopologicallyFGOfFiniteType AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord"

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup ModularCurve.UVCrossingModel
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 12800000 in

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
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

    ∃ (𝒩₀L : ι → Subring ↥(fieldBar q M')) (hlocL : ∀ l, IsLocalRing ↥(𝒩₀L l)) (_ : ∀ l, IsNoetherianRing ↥(𝒩₀L l)),

      (∀ f : ↥F₀, f ∈ O → (f : ↥(fieldBar q M')) ∈ 𝒩₀L n₀) ∧
      (∀ (f : ↥F₀) (hf : f ∈ O) (hN : (f : ↥(fieldBar q M')) ∈ 𝒩₀L n₀), letI : IsLocalRing ↥(𝒩₀L n₀) := hlocL n₀;
        ¬ IsUnit (⟨f, hf⟩ : ↥O) → ¬ IsUnit (⟨(f : ↥(fieldBar q M')), hN⟩ : ↥(𝒩₀L n₀))) ∧

      (∀ f : fieldBar q M', ∃ (n : ℕ) (c : Fin n → AlgebraicClosure ℚ) (a : Fin n → ↥(𝒩₀L n₀)) (b : ↥(𝒩₀L n₀)),
        (b : fieldBar q M') ≠ 0 ∧ f * (b : fieldBar q M') = ∑ i, c i • ((a i : ↥(𝒩₀L n₀)) : fieldBar q M')) ∧

            (∀ l, letI : IsLocalRing ↥(𝒩₀L l) := hlocL l;
              𝒩₀L n₀ ≤ 𝒩₀L l ∧ 𝒩₀L l ≤ 𝒩 ∧
              (∀ P : Place (AlgebraicClosure ℚ) (fieldBar q M'), P ∈ S ↔
                (∀ f : fieldBar q M', f ∈ 𝒩₀L l → f ∈ P.toValuationSubring) ∧
                (∀ f : ↥(𝒩₀L l), ¬ IsUnit f → ∃ h : P.evalAt (f : fieldBar q M') ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A)) ∧
              (∀ c : AlgebraicClosure ℚ, c ∈ C' l → algebraMap (AlgebraicClosure ℚ) (fieldBar q M') c ∈ 𝒩₀L l) ∧
              (∀ g : ↥(𝒩₀L l), ∃ (o : ↥(C' l)) (h : algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (o : AlgebraicClosure ℚ) ∈ 𝒩₀L l), ¬ IsUnit (g - ⟨_, h⟩)) ∧
              (∀ (n : ℕ) (c : Fin n → AlgebraicClosure ℚ) (a : Fin n → ↥(𝒩₀L l)), LinearIndependent ↥(C' l) c →
                ∑ i, c i • ((a i : ↥(𝒩₀L l)) : fieldBar q M') = 0 → ∀ i, a i = 0) ∧

              (∃ Bx : Subring (fieldBar q M'),
                (∀ f : fieldBar q M', f ∈ Bx → f ∈ 𝒩₀L l) ∧
                ((cx : ↥F₀) : ↥(fieldBar q M')) ∈ Bx ∧ ((cy : ↥F₀) : ↥(fieldBar q M')) ∈ Bx ∧ (((u : ↥O) : ↥F₀) : ↥(fieldBar q M')) ∈ Bx ∧
                (∀ f : fieldBar q M', f ∈ 𝒩₀L l ↔ ∃ g h : fieldBar q M', g ∈ Bx ∧ h ∈ Bx ∧
                  (∀ hh : h ∈ 𝒩₀L l, IsUnit (⟨h, hh⟩ : ↥(𝒩₀L l))) ∧ f * h = g) ∧
                (∃ T : Finset (fieldBar q M'), Bx = Subring.closure
                  ({f : fieldBar q M' | ∃ c : AlgebraicClosure ℚ, c ∈ C' l ∧ f = algebraMap (AlgebraicClosure ℚ) (fieldBar q M') c} ∪
                    (↑T : Set (fieldBar q M'))))) ∧
              ((cx : ↥F₀) : ↥(fieldBar q M')) ∈ 𝒩₀L l ∧ ((cy : ↥F₀) : ↥(fieldBar q M')) ∈ 𝒩₀L l ∧ (∃ hu : (((u : ↥O) : ↥F₀) : ↥(fieldBar q M')) ∈ 𝒩₀L l, IsUnit (⟨(((u : ↥O) : ↥F₀) : ↥(fieldBar q M')), hu⟩ : ↥(𝒩₀L l))) ∧
              ∃ (σ : Wc l →+* AdicCompletion (maximalIdeal ↥(𝒩₀L l)) ↥(𝒩₀L l))
                (ιc : AdicCompletion (maximalIdeal ↥(𝒩₀L l)) ↥(𝒩₀L l) ≃+* UVCrossingModel (Wc l) (π l ^ (eL l * E₀))),
                (∀ h : algebraMap (AlgebraicClosure ℚ) (fieldBar q M') ((ϖ' l : ↥(C' l)) : AlgebraicClosure ℚ) ∈ 𝒩₀L l,
                  σ (π l) = algebraMap ↥(𝒩₀L l) (AdicCompletion (maximalIdeal ↥(𝒩₀L l)) ↥(𝒩₀L l)) ⟨_, h⟩) ∧
                (∀ o : Wc l, ιc (σ o) = const (π l ^ (eL l * E₀)) o) ∧

                (∃ (hJ : (⟨ModularCurve.jqNModC (AlgebraicClosure ℚ) q, hJK⟩ : ↥(fieldBar q M')) -
                      algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a₀ : AlgebraicClosure ℚ) ∈ 𝒩₀L l)
                   (e : ℕ) (w : (UVCrossingModel (Wc l) (π l ^ (eL l * E₀)))ˣ), 1 ≤ e ∧
                  ιc (algebraMap ↥(𝒩₀L l) (AdicCompletion (maximalIdeal ↥(𝒩₀L l)) ↥(𝒩₀L l)) ⟨_, hJ⟩) =
                    (w : UVCrossingModel (Wc l) (π l ^ (eL l * E₀))) * V (π l ^ (eL l * E₀)) ^ e) ∧
                (∀ (c : ↥(C' l)) (h : algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (c : AlgebraicClosure ℚ) ∈ 𝒩₀L l),
                  ∃ o : Wc l, σ o = algebraMap ↥(𝒩₀L l) (AdicCompletion (maximalIdeal ↥(𝒩₀L l)) ↥(𝒩₀L l)) ⟨_, h⟩) ∧
                (∀ (f : ↥(𝒩₀L l)) (n : ℕ) (h₁ : f.1 ∈ Rx.integers), Rx.residue ⟨f.1, h₁⟩ ≠ 0 →
                  bx.ord (Rx.residue ⟨f.1, h₁⟩) = (n : ℤ) →
                    ∃ γ : UVCrossingModel (Wc l) (π l ^ (eL l * E₀)), IsUnit γ ∧
                      ιc (algebraMap ↥(𝒩₀L l) (AdicCompletion (maximalIdeal ↥(𝒩₀L l)) ↥(𝒩₀L l)) f) - γ * V (π l ^ (eL l * E₀)) ^ n ∈
                        Ideal.span {const (π l ^ (eL l * E₀)) (π l), U (π l ^ (eL l * E₀))}) ∧
                (∀ (f : ↥(𝒩₀L l)) (n : ℕ) (h₂ : f.1 ∈ R.integers), R.residue ⟨f.1, h₂⟩ ≠ 0 →
                  nd.ord (R.residue ⟨f.1, h₂⟩) = (n : ℤ) →
                    ∃ γ : UVCrossingModel (Wc l) (π l ^ (eL l * E₀)), IsUnit γ ∧
                      ιc (algebraMap ↥(𝒩₀L l) (AdicCompletion (maximalIdeal ↥(𝒩₀L l)) ↥(𝒩₀L l)) f) - γ * U (π l ^ (eL l * E₀)) ^ n ∈
                        Ideal.span {const (π l ^ (eL l * E₀)) (π l), V (π l ^ (eL l * E₀))})) := by
  intro F₀ hK1 hLD W₀ hW₀ O instOL instON hOW hOk hOres hFrac E₀ hE₀ hπO cx cy u ιO γU γV hcxy hιconst hιcx hιcy hcyW hcym hcxm
    hJK a₀ hjF hjO eJ wV heJ hgerm Bx hBxO hBxloc hBxfg
    FI instFI instAFI Rx bx hbx hORx hcI1 hcI2 hcxI hcyI
    FSS instFS instAFS R nd hRW hnd hcS1 hcS2 hcyS hcxS
    S hS hrat 𝒩 h𝒩 hval
    C' hC'A instCD instCV ϖ' Wc instW1 instW2 instW3 instW4 π eL jc hC'K hC'ϖ hC'le hπirr hram hjcϖ hjcinj hjcsur

  classical

  let A0 : ValuationSubring ↥k₀ := A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))
  let C : Subring (AlgebraicClosure ℚ) := A0.toSubring.map (algebraMap ↥k₀ (AlgebraicClosure ℚ))
  have hC : ∀ c : AlgebraicClosure ℚ, c ∈ C ↔ c ∈ A ∧ c ∈ (⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) := by
    intro c
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(ValuationSubring.mem_comap).mp hx, IntermediateField.algebraMap_mem ⊥ x⟩
    · rintro ⟨hcA, hcbot⟩
      rw [IntermediateField.mem_bot] at hcbot
      obtain ⟨x, rfl⟩ := hcbot
      exact ⟨x, (ValuationSubring.mem_comap).mpr hcA, rfl⟩

  let 𝒩₀ : Subring ↥(fieldBar q M') := O.map (algebraMap ↥F₀ ↥(fieldBar q M'))
  have h𝒩₀ : ∀ f : ↥(fieldBar q M'), f ∈ 𝒩₀ ↔ ∃ hf : f ∈ F₀, (⟨f, hf⟩ : ↥F₀) ∈ O := by
    intro f
    constructor
    · rintro ⟨x, hx, hxf⟩
      have hxf' : (x : ↥(fieldBar q M')) = f := by simpa [IntermediateField.algebraMap_apply] using hxf
      refine ⟨hxf' ▸ x.2, ?_⟩
      have : (⟨f, hxf' ▸ x.2⟩ : ↥F₀) = x := Subtype.ext (by simp [hxf'])
      rw [this]; exact hx
    · rintro ⟨hf, hO⟩
      exact ⟨⟨f, hf⟩, hO, by simp [IntermediateField.algebraMap_apply]⟩

  have hLH := ModularCurve.FullLevel.exists_baseRationalNodeRing_input_of_node_ends_nodePlaces q hq M' hqM' A hA k₀ π₀ hπ hdvr hunif hhens hres hκ F₀ hK1 hLD W₀ hW₀ O hOW hOk hOres hFrac E₀ hE₀ hπO cx cy u ιO γU γV hcxy hιconst hιcx hιcy hcyW hcym hcxm
      FI Rx bx hbx hORx hcI1 hcI2 hcxI hcyI FSS R nd hRW hnd hcS1 hcS2 hcyS hcxS S hS hrat 𝒩 h𝒩 hval C hC 𝒩₀ h𝒩₀
  obtain ⟨instL0, instN0, hSne, h0le, hS0, hCmem0, hres0, hld0, hreg1, hreg2, hcx0, hcy0, xf, xs, ys, yf⟩ := hLH

  haveI : IsLocalRing ↥𝒩₀ := instL0
  have hmem0 : ∀ (f : ↥F₀), f ∈ O → (f : ↥(fieldBar q M')) ∈ 𝒩₀ := fun f hf => (h𝒩₀ _).2 ⟨f.2, by simpa using hf⟩
  have hψ : ∀ f : ↥F₀, algebraMap ↥F₀ ↥(fieldBar q M') f = (f : ↥(fieldBar q M')) := fun f => rfl
  have hψk : ∀ x : ↥k₀, ((algebraMap ↥k₀ ↥F₀ x : ↥F₀) : ↥(fieldBar q M')) =
      algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (x : AlgebraicClosure ℚ) := fun x => rfl
  have heO : ∀ (f : ↥F₀) (hf : f ∈ O),
      (O.equivMapOfInjective (algebraMap ↥F₀ ↥(fieldBar q M')) (algebraMap ↥F₀ ↥(fieldBar q M')).injective) ⟨f, hf⟩ =
        ⟨(f : ↥(fieldBar q M')), hmem0 f hf⟩ :=
    fun f hf => Subtype.ext (by simp [IntermediateField.algebraMap_apply])
  have hunitO : ∀ (f : ↥F₀) (hf : f ∈ O),
      IsUnit (⟨f, hf⟩ : ↥O) ↔ IsUnit (⟨(f : ↥(fieldBar q M')), hmem0 f hf⟩ : ↥𝒩₀) := by
    intro f hf
    rw [← heO f hf]
    constructor
    · intro hu
      simpa using hu.map (O.equivMapOfInjective (algebraMap ↥F₀ ↥(fieldBar q M')) (algebraMap ↥F₀ ↥(fieldBar q M')).injective).toRingHom.toMonoidHom
    · intro hu
      simpa using hu.map (O.equivMapOfInjective (algebraMap ↥F₀ ↥(fieldBar q M')) (algebraMap ↥F₀ ↥(fieldBar q M')).injective).symm.toRingHom.toMonoidHom
  obtain ⟨B₀, hB₀⟩ : ∃ B₀ : Subring ↥(fieldBar q M'), B₀ = Bx.map (algebraMap ↥F₀ ↥(fieldBar q M')) := ⟨_, rfl⟩
  have hB₀mem : ∀ g : ↥F₀, g ∈ Bx → (g : ↥(fieldBar q M')) ∈ B₀ := by
    intro g hg
    rw [hB₀]
    exact ⟨g, hg, hψ g⟩
  have hB₀le : B₀ ≤ 𝒩₀ := by
    intro g hg
    rw [hB₀] at hg
    obtain ⟨g₀, hg₀, hgψ⟩ := hg
    rw [hψ] at hgψ
    subst hgψ
    exact hmem0 g₀ (hBxO g₀ hg₀)
  have hloc0 : ∀ f : ↥(fieldBar q M'), f ∈ 𝒩₀ ↔ ∃ g h : ↥(fieldBar q M'), g ∈ B₀ ∧ h ∈ B₀ ∧
      (∀ hh : h ∈ 𝒩₀, IsUnit (⟨h, hh⟩ : ↥𝒩₀)) ∧ f * h = g := by
    intro f
    constructor
    · intro hf
      obtain ⟨hfF, hfO⟩ := (h𝒩₀ f).1 hf
      obtain ⟨g₀, h₀, hg₀, hh₀, hu₀, he₀⟩ := (hBxloc ⟨f, hfF⟩).1 hfO
      refine ⟨(g₀ : ↥(fieldBar q M')), (h₀ : ↥(fieldBar q M')), hB₀mem g₀ hg₀, hB₀mem h₀ hh₀, ?_, ?_⟩
      · intro hh
        exact (hunitO h₀ (hBxO h₀ hh₀)).1 (hu₀ (hBxO h₀ hh₀))
      · have h1 := congrArg (fun z : ↥F₀ => (z : ↥(fieldBar q M'))) he₀
        simpa using h1
    · rintro ⟨g, h, hgB, hhB, hu, he⟩
      rw [hB₀] at hgB hhB
      obtain ⟨g₀, hg₀, hgψ⟩ := hgB
      obtain ⟨h₀, hh₀, hhψ⟩ := hhB
      rw [hψ] at hgψ hhψ
      subst hgψ hhψ
      have hh₀O : h₀ ∈ O := hBxO h₀ hh₀
      have huO : ∀ hh : h₀ ∈ O, IsUnit (⟨h₀, hh⟩ : ↥O) := fun hh => (hunitO h₀ hh).2 (hu (hmem0 h₀ hh))
      have hh0 : h₀ ≠ 0 := by
        intro h0
        exact (huO hh₀O).ne_zero (Subtype.ext h0)
      have hh0' : (h₀ : ↥(fieldBar q M')) ≠ 0 := by exact_mod_cast hh0
      have hfO : (g₀ * h₀⁻¹ : ↥F₀) ∈ O :=
        (hBxloc (g₀ * h₀⁻¹)).2 ⟨g₀, h₀, hg₀, hh₀, huO, by rw [mul_assoc, inv_mul_cancel₀ hh0, mul_one]⟩
      have hf : f = ((g₀ * h₀⁻¹ : ↥F₀) : ↥(fieldBar q M')) := by
        push_cast
        rw [eq_mul_inv_iff_mul_eq₀ hh0']
        exact he
      rw [hf]
      exact hmem0 _ hfO

  haveI : IsNoetherianRing ↥𝒩₀ := instN0
  haveI : FiniteDimensional ↥k₀ ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) := by infer_instance
  haveI : FiniteDimensional ↥k₀ ↥(K n₀) := hKfin n₀
  haveI : IsDiscreteValuationRing ↥A0 := hdvr
  haveI : IsDiscreteValuationRing ↥C := by
    have e : ↥A0.toSubring ≃+* ↥C :=
      A0.toSubring.equivMapOfInjective (algebraMap ↥k₀ (AlgebraicClosure ℚ)) (algebraMap ↥k₀ (AlgebraicClosure ℚ)).injective
    have hA0 : IsDiscreteValuationRing ↥A0.toSubring := hdvr
    exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e
  have hCA : ∀ c : AlgebraicClosure ℚ, c ∈ C → c ∈ A := fun c h => ((hC c).1 h).1
  have hC'K0 : ∀ c : AlgebraicClosure ℚ, c ∈ C' n₀ ↔ c ∈ A ∧ c ∈ K n₀ := by
    intro c
    rw [hC'K n₀ c]
    constructor
    · rintro ⟨h1, ⟨x, hx⟩⟩
      exact ⟨h1, hx ▸ x.2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, ⟨⟨c, h2⟩, rfl⟩⟩
  have hBC := AlgebraicCurve.NodeAnnulusEngine.exists_localizedBaseChange_of_layer_pos_localization (k := ↥k₀) (L := AlgebraicClosure ℚ) A (F := ↥(fieldBar q M'))
    Rx R bx nd S hrat hSne 𝒩 h𝒩 hval (⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (K n₀) bot_le
    C hC hCA (C' n₀) hC'K0 (hC'A n₀) (ϖ' n₀) (hC'ϖ n₀) 𝒩₀ h0le hS0 hCmem0 hres0 hld0 hreg1 hreg2
    ((cx : ↥F₀) : ↥(fieldBar q M')) ((cy : ↥F₀) : ↥(fieldBar q M')) hcx0 hcy0 xf xs ys yf
  obtain ⟨N1, instL1, instN1, h01, h1le, hS1c, hCmem1, hres1, hld1, hloc1, hgen1, hreg11, hreg21, hdim1, hpres1⟩ := hBC

  haveI : IsLocalRing ↥N1 := instL1
  haveI : IsNoetherianRing ↥N1 := instN1

  obtain ⟨T₀, hBxT⟩ := id hBxfg
  have hN1pres := hpres1 B₀ hB₀le hloc0
  obtain ⟨T, hT⟩ : ∃ T : Finset ↥(fieldBar q M'), T = T₀.image (fun g : ↥F₀ => (g : ↥(fieldBar q M'))) ∪
      {((cx : ↥F₀) : ↥(fieldBar q M')), ((cy : ↥F₀) : ↥(fieldBar q M')), (((u : ↥O) : ↥F₀) : ↥(fieldBar q M'))} := ⟨_, rfl⟩
  obtain ⟨Bx₁, hBx₁⟩ : ∃ Bx₁ : Subring ↥(fieldBar q M'), Bx₁ = Subring.closure
      ({f : ↥(fieldBar q M') | ∃ c : AlgebraicClosure ℚ, c ∈ C' n₀ ∧ f = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') c} ∪
        (↑T : Set ↥(fieldBar q M'))) := ⟨_, rfl⟩
  have hCS1 : ∀ c : AlgebraicClosure ℚ, c ∈ C' n₀ → algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') c ∈ Bx₁ := by
    intro c hc
    rw [hBx₁]
    exact Subring.subset_closure (Or.inl ⟨c, hc, rfl⟩)
  have hT1 : ∀ t ∈ T, t ∈ Bx₁ := by
    intro t ht
    rw [hBx₁]
    exact Subring.subset_closure (Or.inr ht)
  have hcxT : ((cx : ↥F₀) : ↥(fieldBar q M')) ∈ T := by rw [hT]; simp
  have hcyT : ((cy : ↥F₀) : ↥(fieldBar q M')) ∈ T := by rw [hT]; simp
  have huT : (((u : ↥O) : ↥F₀) : ↥(fieldBar q M')) ∈ T := by rw [hT]; simp
  have hT₀T : ∀ g ∈ T₀, (g : ↥(fieldBar q M')) ∈ T := by
    intro g hg
    rw [hT]
    exact Finset.mem_union.2 (Or.inl (Finset.mem_image.2 ⟨g, hg, rfl⟩))
  have hBx1le : ∀ f : ↥(fieldBar q M'), f ∈ Bx₁ → f ∈ N1 := by
    intro f hf
    rw [hBx₁] at hf
    refine Subring.closure_le.2 ?_ hf
    rintro t (⟨c, hc, rfl⟩ | ht)
    · exact hCmem1 c hc
    · have ht' : t ∈ T := ht
      rw [hT] at ht'
      rcases Finset.mem_union.1 ht' with ht' | ht'
      · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 ht'
        have hgBx : g ∈ Bx := by
          rw [hBxT]
          exact Subring.subset_closure (Or.inr hg)
        exact h01 (hmem0 g (hBxO g hgBx))
      · simp only [Finset.mem_insert, Finset.mem_singleton] at ht'
        rcases ht' with rfl | rfl | rfl
        · exact h01 (hmem0 _ cx.2)
        · exact h01 (hmem0 _ cy.2)
        · exact h01 (hmem0 _ (u : ↥O).2)
  have hB₀le1 : B₀ ≤ Bx₁ := by
    intro g hg
    rw [hB₀, hBxT, RingHom.map_closure] at hg
    refine Subring.closure_le.2 ?_ hg
    rintro _ ⟨t, ht, rfl⟩
    rcases ht with ⟨x, hxA, rfl⟩ | ht
    · rw [hψ, hψk]
      exact hCS1 _ ((hC'K n₀ _).2 ⟨hxA, ⟨⟨(x : AlgebraicClosure ℚ), IntermediateField.algebraMap_mem (K n₀) x⟩, rfl⟩⟩)
    · rw [hψ]
      exact hT1 _ (hT₀T t ht)
  have hcl : Subring.closure ((B₀ : Set ↥(fieldBar q M')) ∪
      {x : ↥(fieldBar q M') | ∃ c : AlgebraicClosure ℚ, c ∈ C' n₀ ∧ x = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') c}) ≤ Bx₁ := by
    refine Subring.closure_le.2 ?_
    rintro t (ht | ⟨c, hc, rfl⟩)
    · exact hB₀le1 ht
    · exact hCS1 c hc
  have hchart1 : ∃ Bx : Subring (fieldBar q M'),
      (∀ f : fieldBar q M', f ∈ Bx → f ∈ N1) ∧
      ((cx : ↥F₀) : ↥(fieldBar q M')) ∈ Bx ∧ ((cy : ↥F₀) : ↥(fieldBar q M')) ∈ Bx ∧ (((u : ↥O) : ↥F₀) : ↥(fieldBar q M')) ∈ Bx ∧
      (∀ f : fieldBar q M', f ∈ N1 ↔ ∃ g h : fieldBar q M', g ∈ Bx ∧ h ∈ Bx ∧
        (∀ hh : h ∈ N1, IsUnit (⟨h, hh⟩ : ↥(N1))) ∧ f * h = g) ∧
      (∃ T : Finset (fieldBar q M'), Bx = Subring.closure
        ({f : fieldBar q M' | ∃ c : AlgebraicClosure ℚ, c ∈ C' n₀ ∧ f = algebraMap (AlgebraicClosure ℚ) (fieldBar q M') c} ∪
          (↑T : Set (fieldBar q M')))) := by
    refine ⟨Bx₁, hBx1le, hT1 _ hcxT, hT1 _ hcyT, hT1 _ huT, ?_, ⟨T, hBx₁⟩⟩
    intro f
    constructor
    · intro hf
      obtain ⟨g, h, hg, hh, hu, he⟩ := (hN1pres f).1 hf
      exact ⟨g, h, hcl hg, hcl hh, hu, he⟩
    · rintro ⟨g, h, hg, hh, hu, he⟩
      have hhN : h ∈ N1 := hBx1le h hh
      obtain ⟨v, hv⟩ := hu hhN
      have hmul : h * (((v⁻¹ : (↥N1)ˣ) : ↥N1) : ↥(fieldBar q M')) = 1 := by
        have h1 := congrArg (fun z : ↥N1 => (z : ↥(fieldBar q M'))) v.mul_inv
        simpa [hv] using h1
      have hf' : f = g * (((v⁻¹ : (↥N1)ˣ) : ↥N1) : ↥(fieldBar q M')) := by
        calc f = f * (h * (((v⁻¹ : (↥N1)ˣ) : ↥N1) : ↥(fieldBar q M'))) := by rw [hmul, mul_one]
          _ = (f * h) * (((v⁻¹ : (↥N1)ˣ) : ↥N1) : ↥(fieldBar q M')) := by rw [mul_assoc]
          _ = g * (((v⁻¹ : (↥N1)ˣ) : ↥N1) : ↥(fieldBar q M')) := by rw [he]
      rw [hf']
      exact N1.mul_mem (hBx1le g hg) ((v⁻¹ : (↥N1)ˣ) : ↥N1).2
  have step := fun l => ModularCurve.FullLevel.exists_layerRationalNodeRing_of_baseRationalNodeRing_layer_chart q hq M' hqM' A hA k₀ π₀ hπ hdvr hunif hhens hres hκ K hKfin An hAn n₀ hn₀
    F₀ hK1 hLD W₀ hW₀ O hOW hOk hOres hFrac E₀ hE₀ hπO cx cy u ιO γU γV hcxy hιconst hιcx hιcy hcyW hcym hcxm
    hJK a₀ hjF hjO eJ wV heJ hgerm Bx hBxO hBxloc hBxfg FI Rx bx hbx hORx hcI1 hcI2 hcxI hcyI FSS R nd hRW hnd hcS1 hcS2 hcyS hcxS
    S hS hrat 𝒩 h𝒩 hval C' hC'A ϖ' Wc π eL jc hC'K hC'ϖ hC'le hπirr hram hjcϖ hjcinj hjcsur
    l 𝒩₀ h𝒩₀ N1 h01 h1le hS1c hCmem1 hres1 hld1 hloc1 hgen1 hreg11 hreg21 hdim1 hchart1
  choose Nl hNlL hNlN hN1le hEq hlocl hNl𝒩 hblk using step
  have hgen0 := ModularCurve.FullLevel.exists_mul_mem_eq_sum_smul_of_adjoin_sup_eq_top_of_fractionRing q M' k₀ F₀ hK1 hLD O hFrac 𝒩₀ h𝒩₀
  refine ⟨Nl, hNlL, hNlN, ?_, ?_, ?_, ?_⟩
  · intro f hf
    exact hN1le n₀ (h01 (hmem0 f hf))
  · intro f hf hN hnu
    have hf0 : (f : ↥(fieldBar q M')) ∈ 𝒩₀ := hmem0 f hf
    have h0 : ¬ IsUnit (⟨(f : ↥(fieldBar q M')), hf0⟩ : ↥𝒩₀) := by
      intro hu
      apply hnu
      have hx : (O.equivMapOfInjective (algebraMap ↥F₀ ↥(fieldBar q M')) (algebraMap ↥F₀ ↥(fieldBar q M')).injective) ⟨f, hf⟩ =
          ⟨(f : ↥(fieldBar q M')), hf0⟩ := Subtype.ext (by simp [IntermediateField.algebraMap_apply])
      have hu' : IsUnit ((O.equivMapOfInjective (algebraMap ↥F₀ ↥(fieldBar q M')) (algebraMap ↥F₀ ↥(fieldBar q M')).injective) ⟨f, hf⟩) := by
        rw [hx]; exact hu
      simpa using hu'.map ((O.equivMapOfInjective (algebraMap ↥F₀ ↥(fieldBar q M')) (algebraMap ↥F₀ ↥(fieldBar q M')).injective).symm.toRingHom.toMonoidHom)
    have h1 : ¬ IsUnit (Subring.inclusion h01 ⟨(f : ↥(fieldBar q M')), hf0⟩) := hloc1 _ h0
    exact hlocl n₀ (Subring.inclusion h01 ⟨(f : ↥(fieldBar q M')), hf0⟩) ((hN1le n₀) (h01 hf0)) h1
  · intro f
    obtain ⟨n, c, a, b, hb, hfb⟩ := hgen0 f
    exact ⟨n, c, fun i => ⟨((a i : ↥𝒩₀) : ↥(fieldBar q M')), hN1le n₀ (h01 (a i).2)⟩,
      ⟨((b : ↥𝒩₀) : ↥(fieldBar q M')), hN1le n₀ (h01 b.2)⟩, hb, hfb⟩
  · intro l
    refine ⟨?_, hNl𝒩 l, hblk l⟩
    rw [hEq n₀ rfl]
    exact hN1le l

end S_ModularCurve_FullLevel_exists_layeredRationalNodeRings_of_node_ends_layers
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_layeredRationalNodeRings_of_node_ends_layers (solution)
