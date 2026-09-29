-- Prove2me | solution 1 for NumberField.finsum_setIntegral_range_idelicNorm_comp_mul_eq_setIntegral_principalIdeles_sup_range_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/07cd4963-92c6-56f7-91a9-d7c1a1012d5a

import Mathlib
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_NumberField_exists_algebraNorm_eq_of_mem_range_idelicNorm_of_isCyclic
import Theorems.Thm_NumberField_isOpen_range_idelicNorm
import Theorems.Thm_M4aHerbrand_GenuineDescent_adelicNorm_genuineBaseChange_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_finsum_setIntegral_range_idelicNorm_comp_mul_eq_setIntegral_principalIdeles_sup_range_of_prime
p2m_attr_erase "instance" "M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk AutomorphicForm.rightTranslationEmbed_smul_apply AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq"
p2m_attr_erase "simp" "TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero"

set_option autoImplicit false

open MeasureTheory NumberField
open scoped ENNReal Pointwise

namespace CosetHasse

theorem finite_setOf_mem_and_exists_mem_of_isCompact {G A : Type*} [CommGroup G]
    [TopologicalSpace G] [ContinuousMul G] [CommGroup A] (U : Subgroup G)
    (hU : IsOpen (U : Set G)) (ι : A →* G) (T : Set A)
    (key : ∀ t ∈ T, ∀ t' ∈ T, ι (t⁻¹ * t') ∈ U → t = t') {C : Set G} (hC : IsCompact C) :
    {t | t ∈ T ∧ ∃ u ∈ C, (ι t)⁻¹ * u ∈ U}.Finite := by
  have hDopen : ∀ x : G, IsOpen {u : G | x⁻¹ * u ∈ (U : Set G)} := fun x =>
    hU.preimage (continuous_const_mul x⁻¹)
  obtain ⟨X, hXcov⟩ := hC.elim_finite_subcover (fun x : G => {u : G | x⁻¹ * u ∈ (U : Set G)})
    hDopen (fun u _ => Set.mem_iUnion.2 ⟨u, by
      show u⁻¹ * u ∈ (U : Set G)
      rw [inv_mul_cancel]
      exact U.one_mem⟩)
  have hsub : ∀ x : G, ({t | t ∈ T ∧ (ι t)⁻¹ * x ∈ U} : Set A).Subsingleton := by
    intro x t ht t' ht'
    refine key t ht.1 t' ht'.1 ?_
    have h : ι (t⁻¹ * t') = ((ι t)⁻¹ * x) * ((ι t')⁻¹ * x)⁻¹ := by
      rw [map_mul, map_inv, mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]
    rw [h]
    exact U.mul_mem ht.2 (U.inv_mem ht'.2)
  refine Set.Finite.subset (Set.Finite.biUnion X.finite_toSet fun x _ => (hsub x).finite) ?_
  rintro t ⟨htT, u, huC, hu⟩
  obtain ⟨x, hxX, hx⟩ := Set.mem_iUnion₂.1 (hXcov huC)
  refine Set.mem_iUnion₂.2 ⟨x, hxX, htT, ?_⟩
  have h : (ι t)⁻¹ * x = ((ι t)⁻¹ * u) * (x⁻¹ * u)⁻¹ := by
    rw [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]
  rw [h]
  exact U.mul_mem hu (U.inv_mem hx)

theorem engine {G A : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsMulLeftInvariant]
    [CommGroup A] (ι : A →* G) (T : Set A)
    (U : Subgroup G) (hUopen : IsOpen (U : Set G))
    (key : ∀ t ∈ T, ∀ t' ∈ T, ι (t⁻¹ * t') ∈ U → t = t')
    (hcover : ∀ a : A, ∃ t ∈ T, ι (t⁻¹ * a) ∈ U)
    (F : G → ℂ) (hFi : Integrable F ν) (hFs : HasCompactSupport F) :
    (T ∩ Function.support fun t => ∫ u in (U : Set G), F (ι t * u) ∂ν).Finite ∧
      ∑ᶠ t ∈ T, ∫ u in (U : Set G), F (ι t * u) ∂ν = ∫ u in ((ι.range ⊔ U : Subgroup G) : Set G), F u ∂ν := by
  classical
  set I : A → ℂ := fun t => ∫ u in (U : Set G), F (ι t * u) ∂ν with hI
  let C : A → Set G := fun t => {u | (ι t)⁻¹ * u ∈ U}
  have hCopen : ∀ t, IsOpen (C t) := fun t => hUopen.preimage (continuous_const_mul (ι t)⁻¹)
  have hCmeas : ∀ t, MeasurableSet (C t) := fun t => (hCopen t).measurableSet
  have hdisj : ∀ t ∈ T, ∀ t' ∈ T, ∀ u : G, u ∈ C t → u ∈ C t' → t = t' := by
    intro t ht t' ht' u hu hu'
    refine key t ht t' ht' ?_
    have h : ι (t⁻¹ * t') = ((ι t)⁻¹ * u) * ((ι t')⁻¹ * u)⁻¹ := by
      rw [map_mul, map_inv, mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]
    rw [h]
    exact U.mul_mem hu (U.inv_mem hu')
  have hS₀fin : {t | t ∈ T ∧ ∃ u ∈ tsupport F, (ι t)⁻¹ * u ∈ U}.Finite :=
    finite_setOf_mem_and_exists_mem_of_isCompact U hUopen ι T key hFs
  set s : Finset A := hS₀fin.toFinset with hs_def
  have hs : ∀ t, t ∈ s ↔ t ∈ T ∧ ∃ u ∈ tsupport F, u ∈ C t := by
    intro t
    rw [hs_def, Set.Finite.mem_toFinset]
    rfl

  have hcoset : ∀ t : A, I t = ∫ u, (C t).indicator F u ∂ν := by
    intro t
    have hind : ∀ u : G, (C t).indicator F u = (U : Set G).indicator (fun v => F (ι t * v)) ((ι t)⁻¹ * u) := by
      intro u
      by_cases hu : u ∈ C t
      · rw [Set.indicator_of_mem hu, Set.indicator_of_mem (show (ι t)⁻¹ * u ∈ (U : Set G) from hu),
          mul_inv_cancel_left]
      · rw [Set.indicator_of_notMem hu,
          Set.indicator_of_notMem (show (ι t)⁻¹ * u ∉ (U : Set G) from hu)]
    calc I t = ∫ v, (U : Set G).indicator (fun v => F (ι t * v)) v ∂ν :=
          (integral_indicator hUopen.measurableSet).symm
      _ = ∫ u, (U : Set G).indicator (fun v => F (ι t * v)) ((ι t)⁻¹ * u) ∂ν :=
          (integral_mul_left_eq_self (fun v => (U : Set G).indicator (fun v => F (ι t * v)) v) (ι t)⁻¹).symm
      _ = ∫ u, (C t).indicator F u ∂ν := by
          congr 1; funext u; exact (hind u).symm

  have hI0 : ∀ t, (¬ ∃ u ∈ tsupport F, u ∈ C t) → I t = 0 := by
    intro t ht
    rw [hcoset t]
    have h : (C t).indicator F = fun _ => 0 := by
      funext u
      by_cases hu : u ∈ C t
      · rw [Set.indicator_of_mem hu]
        by_contra hne
        exact ht ⟨u, subset_tsupport _ hne, hu⟩
      · rw [Set.indicator_of_notMem hu]
    rw [h, integral_zero]
  have h1 : (T ∩ Function.support I) ⊆ {t | t ∈ T ∧ ∃ u ∈ tsupport F, (ι t)⁻¹ * u ∈ U} := by
    rintro t ⟨htT, hsupp⟩
    refine ⟨htT, ?_⟩
    by_contra hne
    exact hsupp (hI0 t hne)
  have hfin : (T ∩ Function.support I).Finite := hS₀fin.subset h1
  have hfinsum : ∑ᶠ t ∈ T, I t = ∑ t ∈ s, I t := by
    apply finsum_mem_eq_sum_of_inter_support_eq
    ext t
    constructor
    · rintro ⟨htT, hsupp⟩
      exact ⟨Finset.mem_coe.2 ((hs t).2 (h1 ⟨htT, hsupp⟩)), hsupp⟩
    · rintro ⟨hts, hsupp⟩
      exact ⟨((hs t).1 (Finset.mem_coe.1 hts)).1, hsupp⟩

  set S : Set G := ((ι.range ⊔ U : Subgroup G) : Set G) with hSdef
  have hSopen : IsOpen S := Subgroup.isOpen_mono (le_sup_right : U ≤ ι.range ⊔ U) hUopen
  have hpt : ∀ u : G, S.indicator F u = ∑ t ∈ s, (C t).indicator F u := by
    intro u
    by_cases hFu : F u = 0
    · have : S.indicator F u = 0 := by
        by_cases hu : u ∈ S
        · rw [Set.indicator_of_mem hu, hFu]
        · rw [Set.indicator_of_notMem hu]
      rw [this]
      symm
      refine Finset.sum_eq_zero fun t _ => ?_
      by_cases hu : u ∈ C t
      · rw [Set.indicator_of_mem hu, hFu]
      · rw [Set.indicator_of_notMem hu]
    have hu_ts : u ∈ tsupport F := subset_tsupport _ hFu
    by_cases hH : u ∈ S
    · rw [Set.indicator_of_mem hH]
      obtain ⟨_, ⟨a, rfl⟩, w, hw, rfl⟩ := Subgroup.mem_sup.1 hH
      obtain ⟨t₀, ht₀T, ht₀⟩ := hcover a
      have hut₀ : ι a * w ∈ C t₀ := by
        show (ι t₀)⁻¹ * (ι a * w) ∈ U
        have h : (ι t₀)⁻¹ * (ι a * w) = ι (t₀⁻¹ * a) * w := by rw [map_mul, map_inv, mul_assoc]
        rw [h]
        exact U.mul_mem ht₀ hw
      have ht₀s : t₀ ∈ s := (hs t₀).2 ⟨ht₀T, _, hu_ts, hut₀⟩
      rw [Finset.sum_eq_single_of_mem t₀ ht₀s]
      · rw [Set.indicator_of_mem hut₀]
      · intro t hts hne
        rw [Set.indicator_of_notMem]
        intro hut
        exact hne (hdisj t ((hs t).1 hts).1 t₀ ht₀T _ hut hut₀)
    · rw [Set.indicator_of_notMem hH]
      symm
      refine Finset.sum_eq_zero fun t _ => ?_
      rw [Set.indicator_of_notMem]
      intro hut
      apply hH
      rw [hSdef, ← mul_inv_cancel_left (ι t) u]
      exact Subgroup.mul_mem_sup ⟨t, rfl⟩ hut
  have hmain : ∫ u in S, F u ∂ν = ∑ t ∈ s, I t := by
    calc ∫ u in S, F u ∂ν = ∫ u, S.indicator F u ∂ν := (integral_indicator hSopen.measurableSet).symm
      _ = ∫ u, ∑ t ∈ s, (C t).indicator F u ∂ν := by
          congr 1; funext u; exact hpt u
      _ = ∑ t ∈ s, ∫ u, (C t).indicator F u ∂ν :=
          integral_finsetSum s (fun t _ => hFi.indicator (hCmeas t))
      _ = ∑ t ∈ s, I t := Finset.sum_congr rfl fun t _ => (hcoset t).symm
  refine ⟨hfin, ?_⟩
  rw [hfinsum, hmain]

end CosetHasse

open CosetHasse in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (hprime : (Module.finrank K L).Prime)
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure]
    (T : Set Kˣ)
    (hT : ∀ a : Kˣ, ∃! t : Kˣ, t ∈ T ∧ ∃ b : Lˣ, a = t * Units.map (Algebra.norm K : L →* K) b)
    (G : (AdeleRing (𝓞 K) K)ˣ → ℂ) (hGi : Integrable G νZK) (hGs : HasCompactSupport G) :
    (T ∩ Function.support (fun t : Kˣ =>
        ∫ u in Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm,
          G (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) t * u) ∂νZK)).Finite ∧
    ∑ᶠ t ∈ T, ∫ u in Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm,
        G (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) t * u) ∂νZK =
      ∫ u in ((M4aHerbrand.principalIdeles (𝓞 K) K ⊔
          (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm.range : Subgroup (AdeleRing (𝓞 K) K)ˣ) :
            Set (AdeleRing (𝓞 K) K)ˣ), G u ∂νZK := by
  classical
  let B := M4aHerbrand.GenuineDescent.genuineBaseChange K L
  let N : (AdeleRing (𝓞 L) L)ˣ →* (AdeleRing (𝓞 K) K)ˣ := B.idelicNorm
  let ιK : Kˣ →* (AdeleRing (𝓞 K) K)ˣ :=
    Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)
  let ιL : Lˣ →* (AdeleRing (𝓞 L) L)ˣ :=
    Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)
  haveI : IsCyclic (L ≃ₐ[K] L) := ⟨⟨σ, hgen⟩⟩
  have hopen : IsOpen ((N.range : Subgroup (AdeleRing (𝓞 K) K)ˣ) : Set (AdeleRing (𝓞 K) K)ˣ) :=
    NumberField.isOpen_range_idelicNorm K L B
  have hcompat : ∀ b : Lˣ, ιK (Units.map (Algebra.norm K : L →* K) b) = N (ιL b) := by
    intro b
    ext
    simp only [ιK, ιL, N, M4aHerbrand.AdeleBaseChange.idelicNorm, Units.coe_map]
    exact (M4aHerbrand.GenuineDescent.adelicNorm_genuineBaseChange_algebraMap K L (b : L)).symm
  have hHasse : ∀ a : Kˣ, ιK a ∈ N.range → ∃ b : Lˣ, Units.map (Algebra.norm K : L →* K) b = a := by
    intro a ha
    obtain ⟨b, hb⟩ :=
      NumberField.exists_algebraNorm_eq_of_mem_range_idelicNorm_of_isCyclic K L a ha
    have hb0 : b ≠ 0 := by
      intro h
      apply a.ne_zero
      rw [← hb, h, Algebra.norm_zero]
    refine ⟨Units.mk0 b hb0, Units.ext ?_⟩
    simp only [Units.coe_map, Units.val_mk0]
    exact hb
  have key : ∀ t ∈ T, ∀ t' ∈ T, ιK (t⁻¹ * t') ∈ N.range → t = t' := by
    intro t ht t' ht' hmem
    obtain ⟨b, hb⟩ := hHasse _ hmem
    obtain ⟨t₀, -, huniq⟩ := hT t'
    have e1 : t' = t₀ := huniq t' ⟨ht', 1, by rw [map_one, mul_one]⟩
    have e2 : t = t₀ := huniq t ⟨ht, b, by rw [hb, mul_inv_cancel_left]⟩
    rw [e2, e1]
  have hcover : ∀ a : Kˣ, ∃ t ∈ T, ιK (t⁻¹ * a) ∈ N.range := by
    intro a
    obtain ⟨t, ⟨htT, b, hab⟩, -⟩ := hT a
    refine ⟨t, htT, ιL b, ?_⟩
    rw [← hcompat b, hab, inv_mul_cancel_left]
  obtain ⟨h1, h2⟩ := engine νZK ιK T N.range hopen key hcover G hGi hGs
  have hS : ((M4aHerbrand.principalIdeles (𝓞 K) K ⊔ N.range : Subgroup (AdeleRing (𝓞 K) K)ˣ) :
      Set (AdeleRing (𝓞 K) K)ˣ) = ((ιK.range ⊔ N.range : Subgroup (AdeleRing (𝓞 K) K)ˣ) : Set _) := rfl
  have hrange : Set.range N = ((N.range : Subgroup (AdeleRing (𝓞 K) K)ˣ) : Set (AdeleRing (𝓞 K) K)ˣ) := rfl
  refine ⟨?_, ?_⟩
  · first | simpa only [hrange] using h1 | simpa only [hrange, N] using h1 | exact h1
  · rw [hS]
    first | simpa only [hrange] using h2 | simpa only [hrange, N] using h2 | exact h2

end S_NumberField_finsum_setIntegral_range_idelicNorm_comp_mul_eq_setIntegral_principalIdeles_sup_range_of_prime
end P2MW
export P2MW.S_NumberField_finsum_setIntegral_range_idelicNorm_comp_mul_eq_setIntegral_principalIdeles_sup_range_of_prime (solution)
