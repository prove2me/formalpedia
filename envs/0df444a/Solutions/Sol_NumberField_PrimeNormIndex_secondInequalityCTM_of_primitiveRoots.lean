-- Prove2me | solution 1 for NumberField.PrimeNormIndex.secondInequalityCTM_of_primitiveRoots
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/d598dd3c-09c2-5b4d-8e4b-e507639ba538

import Mathlib
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_LanglandsTunnell_ArtinFrobenius
import Definitions.Def_M4aHerbrand_AdeleBaseChange
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NarrowRayClassGroup
import Definitions.Def_NumberField_Completion_HenselianLocalRing
import Definitions.Def_NumberField_IdeleBox
import Definitions.Def_PrimeNormIndex_AdmissibleExpAt
import Theorems.Thm_ClassGroup_exists_finset_forall_exists_mk0_eq_of_dvd
import Theorems.Thm_HeckeCharacter_fadContentHom_projFin_idelicNorm_eq_fracRelNormUnit
import Theorems.Thm_HeckeCharacter_isAdjuster_idelicNorm_of_isAdjuster
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_Extension_finrank_adicCompletion_eq_one_of_pow_eq
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_Extension_inertia_eq_bot_of_forall_pow_eq
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_Extension_inertia_eq_bot_of_pow_eq
import Theorems.Thm_KummerTheory_algEquiv_eq_one_of_forall_apply_eq_of_isSplittingField
import Theorems.Thm_KummerTheory_isGalois_and_commute_and_pow_eq_one_of_isSplittingField_prod_X_pow_sub_C
import Theorems.Thm_M4aHerbrand_AdeleBaseChange_ideleBox_le_range_idelicNorm
import Theorems.Thm_NumberField_AdeleRing_principalIdeles_inf_unitIdelesOutside_eq_map_unit
import Theorems.Thm_NumberField_AdeleRing_principalIdeles_sup_unitIdelesOutside_eq_top
import Theorems.Thm_NumberField_AdeleRing_relIndex_ideleBox_unitIdelesOutside
import Theorems.Thm_NumberField_exists_pow_eq_of_forall_mem_range_powMonoidHom
import Theorems.Thm_NumberField_natCard_sUnit_quotient_range_powMonoidHom
import Theorems.Thm_NumberField_prod_natCard_units_adicCompletion_quotient_range_powMonoidHom_mul_prod_infinitePlace_eq_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots
p2m_attr_erase "simp" "NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk IsLocalRing.principalUnits_zero"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

section Fold_M4aKummer_CompletionQuot

set_option autoImplicit false

noncomputable section

p2m_open "IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.NumberField WithZero"

namespace M4aKummer

variable {k : Type*} [Field k] [NumberField k] (v : HeightOneSpectrum (𝓞 k))

private theorem valued_coe_intRing (x : 𝓞 k) :
    Valued.v (algebraMap (𝓞 k) (v.adicCompletion k) x) = v.intValuation x := by
  have hcoe2 : algebraMap (𝓞 k) (v.adicCompletion k) x =
      ((algebraMap (𝓞 k) k x : k) : v.adicCompletion k) := by
    rw [IsScalarTower.algebraMap_apply (𝓞 k) k (v.adicCompletion k),
      algebraMap_adicCompletion]
    rfl
  have hval : Valued.v (((algebraMap (𝓞 k) k x : k) : v.adicCompletion k)) =
      v.valuation k (algebraMap (𝓞 k) k x) := v.valuedAdicCompletion_eq_valuation' _
  rw [hcoe2, hval, valuation_of_algebraMap]

private theorem exists_intRing_valued_sub_le (y : v.adicCompletion k) (hy : Valued.v y ≤ 1) (m : ℕ) :
    ∃ a : 𝓞 k,
      Valued.v (y - algebraMap (𝓞 k) (v.adicCompletion k) a) ≤ WithZero.exp (-(m : ℤ)) := by

  obtain ⟨π, hπ⟩ := v.intValuation_exists_uniformizer
  have hw0 : Valued.v (algebraMap (𝓞 k) (v.adicCompletion k) (π ^ m)) =
      WithZero.exp (-(m : ℤ)) := by
    rw [valued_coe_intRing, map_pow, hπ, ← WithZero.exp_nsmul, nsmul_eq_mul, mul_neg, mul_one]
  have hr0 : (Valued.v : Valuation (v.adicCompletion k) ℤᵐ⁰).restrict
      (algebraMap (𝓞 k) (v.adicCompletion k) (π ^ m)) ≠ 0 := by
    rw [Ne, Valuation.restrict_eq_zero_iff, hw0]
    exact exp_ne_zero

  have hball : {z : v.adicCompletion k | Valued.v (z - y) < WithZero.exp (-(m : ℤ))} ∈
      nhds y := by
    refine (Valued.mem_nhds).mpr ⟨Units.mk0 _ hr0, fun z hz => ?_⟩
    show Valued.v (z - y) < WithZero.exp (-(m : ℤ))
    rw [← hw0]
    exact (Valuation.restrict_lt_iff _).mp hz

  obtain ⟨x, hx1, γ', rfl⟩ :=
    mem_closure_iff_nhds.mp ((denseRange_algebraMap (K := k) (v := v)) y) _ hball
  have hcoeγ' : algebraMap k (v.adicCompletion k) γ' = (γ' : v.adicCompletion k) := by
    rw [algebraMap_adicCompletion]; rfl
  have hγ'ball : Valued.v (algebraMap k (v.adicCompletion k) γ' - y) <
      WithZero.exp (-(m : ℤ)) := hx1

  have hγ'int : v.valuation k γ' ≤ 1 := by
    have h1 : Valued.v (algebraMap k (v.adicCompletion k) γ') = v.valuation k γ' := by
      rw [hcoeγ']; exact v.valuedAdicCompletion_eq_valuation' _
    have h2 : Valued.v (algebraMap k (v.adicCompletion k) γ') ≤ 1 := by
      have hsplit : algebraMap k (v.adicCompletion k) γ' =
          y + (algebraMap k (v.adicCompletion k) γ' - y) := by ring
      rw [hsplit]
      refine le_trans (Valuation.map_add _ _ _) (max_le hy ?_)
      refine le_trans (le_of_lt hγ'ball) ?_
      rw [← WithZero.exp_zero, WithZero.exp_le_exp]
      omega
    rwa [h1] at h2

  obtain ⟨a, ha⟩ := exists_valuation_sub_lt_of_integer v hγ'int
    (Units.mk0 (WithZero.exp (-(m : ℤ))) (exp_ne_zero))
  refine ⟨a, ?_⟩
  have hsplit : y - algebraMap (𝓞 k) (v.adicCompletion k) a =
      (y - algebraMap k (v.adicCompletion k) γ') +
        (algebraMap k (v.adicCompletion k) γ' -
          algebraMap (𝓞 k) (v.adicCompletion k) a) := by ring
  rw [hsplit]
  refine le_trans (Valuation.map_add _ _ _) (max_le ?_ ?_)
  · rw [← Valuation.map_neg, neg_sub]
    exact le_of_lt hγ'ball
  · have hcoe : algebraMap k (v.adicCompletion k) γ' -
        algebraMap (𝓞 k) (v.adicCompletion k) a =
        algebraMap k (v.adicCompletion k) (γ' - algebraMap (𝓞 k) k a) := by
      rw [map_sub]
      congr 1
    have hcoe2 : algebraMap k (v.adicCompletion k) (γ' - algebraMap (𝓞 k) k a) =
        ((γ' - algebraMap (𝓞 k) k a : k) : v.adicCompletion k) := by
      rw [algebraMap_adicCompletion]; rfl
    have hval : Valued.v (algebraMap k (v.adicCompletion k)
        (γ' - algebraMap (𝓞 k) k a)) = v.valuation k (γ' - algebraMap (𝓞 k) k a) := by
      rw [hcoe2]; exact v.valuedAdicCompletion_eq_valuation' _
    rw [hcoe, hval, ← Valuation.map_neg, neg_sub]
    have ha' := ha
    rw [Units.val_mk0] at ha'
    exact le_of_lt ha'

variable (a : 𝓞 k)

private def quotMapHom : 𝓞 k →+*
    ((v.adicCompletionIntegers k) ⧸
      Ideal.span {algebraMap (𝓞 k) (v.adicCompletionIntegers k) a}) :=
  (Ideal.Quotient.mk _).comp (algebraMap (𝓞 k) (v.adicCompletionIntegers k))

private theorem integers_handle :
    (Valued.v : Valuation (v.adicCompletion k) ℤᵐ⁰).Integers (v.adicCompletionIntegers k) :=
  Valuation.valuationSubring.integers _

private theorem mem_span_iff_valued_le (x : v.adicCompletionIntegers k) :
    x ∈ Ideal.span {algebraMap (𝓞 k) (v.adicCompletionIntegers k) a} ↔
      Valued.v ((x : v.adicCompletion k)) ≤
        Valued.v ((algebraMap (𝓞 k) (v.adicCompletionIntegers k) a :
          v.adicCompletionIntegers k) : v.adicCompletion k) := by
  have h := (integers_handle v).coe_span_singleton_eq_setOf_le_v_algebraMap
    (x := algebraMap (𝓞 k) (v.adicCompletionIntegers k) a)
  constructor
  · intro hx
    have : x ∈ (Ideal.span {algebraMap (𝓞 k) (v.adicCompletionIntegers k) a} :
        Set (v.adicCompletionIntegers k)) := hx
    rw [h] at this
    exact this
  · intro hx
    have : x ∈ {y : v.adicCompletionIntegers k |
        Valued.v (algebraMap _ (v.adicCompletion k) y) ≤
          Valued.v (algebraMap _ (v.adicCompletion k)
            (algebraMap (𝓞 k) (v.adicCompletionIntegers k) a))} := hx
    rw [← h] at this
    exact this

private theorem valued_algebraMap_eq (x : 𝓞 k) :
    Valued.v ((algebraMap (𝓞 k) (v.adicCompletionIntegers k) x :
      v.adicCompletionIntegers k) : v.adicCompletion k) = v.intValuation x := by
  have h1 : ((algebraMap (𝓞 k) (v.adicCompletionIntegers k) x :
      v.adicCompletionIntegers k) : v.adicCompletion k) =
      algebraMap (𝓞 k) (v.adicCompletion k) x := rfl
  rw [h1, valued_coe_intRing]

variable {m : ℕ} (hm : v.intValuation a = WithZero.exp (-(m : ℤ)))

include hm in

private theorem quotMapHom_surjective : Function.Surjective (quotMapHom v a) := by
  intro c
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective c
  obtain ⟨b, hb⟩ := exists_intRing_valued_sub_le v (y : v.adicCompletion k) y.2 m
  refine ⟨b, ?_⟩
  rw [quotMapHom, RingHom.comp_apply]
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  rw [mem_span_iff_valued_le, valued_algebraMap_eq, hm]
  have hsub : ((algebraMap (𝓞 k) (v.adicCompletionIntegers k) b - y :
      v.adicCompletionIntegers k) : v.adicCompletion k) =
      -(((y : v.adicCompletion k)) - algebraMap (𝓞 k) (v.adicCompletion k) b) := by
    have hAB : ((algebraMap (𝓞 k) (v.adicCompletionIntegers k) b :
        v.adicCompletionIntegers k) : v.adicCompletion k) =
        algebraMap (𝓞 k) (v.adicCompletion k) b := rfl
    push_cast
    rw [hAB]
    ring
  rw [hsub, Valuation.map_neg]
  exact hb

include hm in

private theorem ker_quotMapHom : RingHom.ker (quotMapHom v a) = v.asIdeal ^ m := by
  ext x
  rw [RingHom.mem_ker, quotMapHom, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem,
    mem_span_iff_valued_le, valued_algebraMap_eq, valued_algebraMap_eq, hm,
    ← intValuation_le_pow_iff_mem]

include hm in

private def completionQuotEquiv :
    ((𝓞 k) ⧸ (v.asIdeal ^ m)) ≃+*
      ((v.adicCompletionIntegers k) ⧸
        Ideal.span {algebraMap (𝓞 k) (v.adicCompletionIntegers k) a}) :=
  (Ideal.quotEquivOfEq (ker_quotMapHom v a hm).symm).trans
    (RingHom.quotientKerEquivOfSurjective (quotMapHom_surjective v a hm))

include hm in

private theorem natCard_completion_quot_eq :
    Nat.card ((v.adicCompletionIntegers k) ⧸
        Ideal.span {algebraMap (𝓞 k) (v.adicCompletionIntegers k) a}) =
      Nat.card ((𝓞 k) ⧸ (v.asIdeal ^ m)) :=
  (Nat.card_congr (completionQuotEquiv v a hm).toEquiv).symm

end M4aKummer

end

end Fold_M4aKummer_CompletionQuot

section Fold_M4aTheta_FadContent

set_option autoImplicit false

p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.NumberField IsDedekindDomain Deep.NTSupply WithZero"
open scoped nonZeroDivisors

noncomputable section

namespace HeckeCharacter
p2m_export "HeckeCharacter" "idealMultiplicity placeUnder' placeUnder'_asIdeal modulusExt fracRelNormUnit placeUnder'_dvd_iff gcopNC2 coe_raySymbol_gcop_eq_fracRelNormUnit' fracRelNormUnit_mem_coprimeToModulus relNormCTM fad_one_apply fad_mul_apply placeOrd valued_ne_zero_of_unit placeOrd_eq_zero_iff finite_support_placeOrd fadContentHom projFin placeOf isReal_compOfRealHom isReal_placeOf archRealProjTau archSign archSign_of_fst_eq_one archSign_mul archSign_one archSign_inv unit_cong_mul unit_cong_div fad_units_inv_apply IsAdjuster fadContentHom_projFin_idelicNorm_eq_fracRelNormUnit isAdjuster_idelicNorm_of_isAdjuster"
p2m_open "HeckeCharacter"

variable (K : Type*) [Field K] [NumberField K]

section StageA

private theorem fadContentHom_apply (u : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    fadContentHom K u = ∏ᶠ v : HeightOneSpectrum (𝓞 K), (primeUnit K v) ^ (placeOrd K u v) :=
  rfl

private theorem fadContentHom_single_uniformizer (u : (FiniteAdeleRing (𝓞 K) K)ˣ)
    {v : HeightOneSpectrum (𝓞 K)}
    (huw : ∀ w : HeightOneSpectrum (𝓞 K), w ≠ v →
      Valued.v ((u : FiniteAdeleRing (𝓞 K) K) w) = 1)
    (huv : Valued.v ((u : FiniteAdeleRing (𝓞 K) K) v) = WithZero.exp (-1 : ℤ)) :
    fadContentHom K u = primeUnit K v := by
  rw [fadContentHom_apply]
  rw [finprod_eq_single _ v]
  · have : placeOrd K u v = 1 := by unfold placeOrd; rw [huv, WithZero.log_exp]; ring
    rw [this, zpow_one]
  · intro w hwv
    have : placeOrd K u w = 0 := (placeOrd_eq_zero_iff K u w).mpr (huw w hwv)
    rw [this, zpow_zero]

end StageA

section StageB

private theorem coe_fadContentHom (u : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    ((fadContentHom K u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
      = ∏ᶠ v : HeightOneSpectrum (𝓞 K),
          (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ (placeOrd K u v) := by
  rw [fadContentHom_apply, ← Units.coeHom_apply,
    (Units.coeHom _).map_finprod_of_preimage_one (fun _ h => Units.ext h)
      (fun v => primeUnit K v ^ placeOrd K u v)]
  refine finprod_congr fun v => ?_
  rw [Units.coeHom_apply, Units.val_zpow_eq_zpow_val, primeUnit_val]

private theorem count_fadContentHom (u : (FiniteAdeleRing (𝓞 K) K)ˣ) (w : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K w ((fadContentHom K u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K) = placeOrd K u w := by
  rw [coe_fadContentHom]
  exact FractionalIdeal.count_finprod K w (placeOrd K u) (by
    rw [Filter.eventually_cofinite]
    exact finite_support_placeOrd K u)

private theorem fadContentHom_mem_coprimeToModulus_iff (u : (FiniteAdeleRing (𝓞 K) K)ˣ)
    (𝔣 : Ideal (𝓞 K)) :
    fadContentHom K u ∈ coprimeToModulus K 𝔣 ↔
      ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
        Valued.v ((u : FiniteAdeleRing (𝓞 K) K) v) = 1 := by
  rw [mem_coprimeToModulus_iff]
  refine forall_congr' fun v => forall_congr' fun _ => ?_
  rw [count_fadContentHom, placeOrd_eq_zero_iff]

private theorem placeOrd_unitEmbedding (α : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    placeOrd K (FiniteAdeleRing.unitEmbedding (𝓞 K) K α) v
      = FractionalIdeal.count K v (FractionalIdeal.spanSingleton ((𝓞 K)⁰) (α : K)) := by
  classical

  have hLHS : placeOrd K (FiniteAdeleRing.unitEmbedding (𝓞 K) K α) v
      = -WithZero.log (v.valuation K (α : K)) := by
    unfold placeOrd
    rw [FiniteAdeleRing.unitEmbedding, Units.coe_map, MonoidHom.coe_coe,
      FiniteAdeleRing.algebraMap_apply,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (α : K)]
  rw [hLHS]

  obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.mk'_surjective (M := (𝓞 K)⁰) (S := K) (α : K)
  have hnd' : IsLocalization.mk' K n d = (α : K) := hnd
  have hn0 : n ≠ 0 := by
    rintro rfl; simp only [IsLocalization.mk'_zero] at hnd'; exact α.ne_zero hnd'.symm
  have hd0 : (d : 𝓞 K) ≠ 0 := nonZeroDivisors.coe_ne_zero d
  rw [← hnd', HeightOneSpectrum.valuation_of_mk',
    HeightOneSpectrum.intValuation_if_neg _ hn0, HeightOneSpectrum.intValuation_if_neg _ hd0,
    ← WithZero.exp_sub, WithZero.log_exp, neg_sub_neg,
    IsFractionRing.mk'_eq_div, div_eq_mul_inv,
    ← FractionalIdeal.spanSingleton_mul_spanSingleton,
    FractionalIdeal.count_mul K v
      (by rw [ne_eq, FractionalIdeal.spanSingleton_eq_zero_iff]
          exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hn0)
      (by rw [ne_eq, FractionalIdeal.spanSingleton_eq_zero_iff, inv_eq_zero]
          exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hd0),
    ← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K v
      (by simp only [ne_eq, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hn0),
    show FractionalIdeal.spanSingleton ((𝓞 K)⁰) (algebraMap (𝓞 K) K d)⁻¹
        = (FractionalIdeal.spanSingleton ((𝓞 K)⁰) (algebraMap (𝓞 K) K d))⁻¹ by
        rw [← one_div, ← FractionalIdeal.spanSingleton_div_spanSingleton,
          FractionalIdeal.spanSingleton_one, one_div],
    FractionalIdeal.count_inv, ← FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.count_coe K v
      (by simp only [ne_eq, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hd0)]
  ring

private theorem coe_fadContentHom_principal (α : Kˣ) :
    ((fadContentHom K (FiniteAdeleRing.unitEmbedding (𝓞 K) K α) :
      (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
      = FractionalIdeal.spanSingleton ((𝓞 K)⁰) (α : K) := by
  rw [coe_fadContentHom]
  conv_rhs => rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' (K := K)
    (I := FractionalIdeal.spanSingleton ((𝓞 K)⁰) (α : K))
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr α.ne_zero)]
  exact finprod_congr fun v => by rw [placeOrd_unitEmbedding]

private theorem fadContentHom_unitEmbedding (α : Kˣ) :
    fadContentHom K (FiniteAdeleRing.unitEmbedding (𝓞 K) K α) = toPrincipalIdeal (𝓞 K) K α :=
  Units.ext <| (coe_fadContentHom_principal K α).trans (coe_toPrincipalIdeal α).symm

end StageB

end HeckeCharacter

section Battery
p2m_open "HeckeCharacter P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.HeckeCharacter"
end Battery
end

end Fold_M4aTheta_FadContent

section Fold_M4aTheta_IdeleContentBuild

set_option autoImplicit false

p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.NumberField IsDedekindDomain Deep.NTSupply WithZero"
open scoped nonZeroDivisors

noncomputable section

namespace HeckeCharacter
p2m_export "HeckeCharacter" "idealMultiplicity placeUnder' placeUnder'_asIdeal modulusExt fracRelNormUnit placeUnder'_dvd_iff gcopNC2 coe_raySymbol_gcop_eq_fracRelNormUnit' fracRelNormUnit_mem_coprimeToModulus relNormCTM fad_one_apply fad_mul_apply placeOrd valued_ne_zero_of_unit placeOrd_eq_zero_iff finite_support_placeOrd fadContentHom projFin placeOf isReal_compOfRealHom isReal_placeOf archRealProjTau archSign archSign_of_fst_eq_one archSign_mul archSign_one archSign_inv unit_cong_mul unit_cong_div fad_units_inv_apply IsAdjuster fadContentHom_projFin_idelicNorm_eq_fracRelNormUnit isAdjuster_idelicNorm_of_isAdjuster"
p2m_open "HeckeCharacter"

variable (K : Type*) [Field K] [NumberField K]

section StageC

private theorem projFin_val (u : (AdeleRing (𝓞 K) K)ˣ) :
    ((projFin K u : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) =
      (u : AdeleRing (𝓞 K) K).2 := rfl

private theorem projFin_principal (α : Kˣ) :
    projFin K (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)
      = FiniteAdeleRing.unitEmbedding (𝓞 K) K α := by
  apply Units.ext; rfl

omit [NumberField K] in
omit [NumberField K] in
omit [NumberField K] in

private theorem embedding_of_isReal_placeOf (τ : K →+* ℝ) :
    InfinitePlace.embedding_of_isReal (isReal_placeOf K τ) = τ := by
  ext x
  apply Complex.ofReal_injective
  rw [InfinitePlace.embedding_of_isReal_apply, show (placeOf K τ).embedding
      = Complex.ofRealHom.comp τ from
    InfinitePlace.embedding_mk_eq_of_isReal (isReal_compOfRealHom K τ)]
  rfl

private theorem archSign_principal (τ : K →+* ℝ) (α : Kˣ) :
    archSign K τ (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α) ↔ 0 < τ (α : K) := by
  unfold archSign archRealProjTau
  rw [Units.coe_map, MonoidHom.coe_coe, AdeleRing.algebraMap_fst_apply,
    InfinitePlace.Completion.ringEquivRealOfIsReal_apply,
    InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe,
    embedding_of_isReal_placeOf K τ]
  rfl

namespace IsAdjuster p2m_export "HeckeCharacter.IsAdjuster" "mk cong sign" end IsAdjuster
namespace IsAdjuster
p2m_open_scoped "HeckeCharacter.IsAdjuster" in
private theorem _root_.HeckeCharacter.IsAdjuster.coprime {𝔣 : Ideal (𝓞 K)} {u : (AdeleRing (𝓞 K) K)ˣ} {α : Kˣ}
    (h : IsAdjuster K 𝔣 u α) :
    fadContentHom K (projFin K (u * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)⁻¹))
      ∈ coprimeToModulus K 𝔣 := by
  rw [fadContentHom_mem_coprimeToModulus_iff]
  intro v hv
  rw [projFin_val]
  exact (h.cong v hv).1

end IsAdjuster
p2m_export "HeckeCharacter" "IsAdjuster.coprime"
private theorem isAdjuster_one_one (𝔣 : Ideal (𝓞 K)) : IsAdjuster K 𝔣 1 1 := by
  refine ⟨fun v _ => ?_, fun τ => ?_⟩
  · simp only [map_one, inv_one, mul_one]
    refine ⟨?_, ?_⟩
    · show Valued.v ((1 : FiniteAdeleRing (𝓞 K) K) v) = 1
      rw [fad_one_apply]; exact map_one _
    · show Valued.v ((1 : FiniteAdeleRing (𝓞 K) K) v - 1) ≤ _
      rw [fad_one_apply, sub_self, map_zero]; exact zero_le'
  · simp only [map_one, inv_one, mul_one]
    exact archSign_of_fst_eq_one K τ rfl

private abbrev adjFinV (u : (AdeleRing (𝓞 K) K)ˣ) (α : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    v.adicCompletion K :=
  (((u * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)⁻¹ :
      (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v

private theorem four_comm {G : Type*} [CommMonoid G] (a b c d : G) :
    a * b * (d * c) = a * c * (b * d) := by
  simp only [mul_comm, mul_left_comm]

private abbrev pK : Kˣ →* (AdeleRing (𝓞 K) K)ˣ :=
  Units.map (algebraMap K (AdeleRing (𝓞 K) K))

private theorem adj_adele_mul (u u' : (AdeleRing (𝓞 K) K)ˣ) (α α' : Kˣ) :
    u * u' * (pK K (α * α'))⁻¹ = (u * (pK K α)⁻¹) * (u' * (pK K α')⁻¹) := by
  rw [map_mul, mul_inv_rev]; exact four_comm _ _ _ _

private theorem adj_adele_ratio (u : (AdeleRing (𝓞 K) K)ˣ) (α α' : Kˣ) :
    (u * (pK K α)⁻¹)⁻¹ * (u * (pK K α')⁻¹) = pK K (α * α'⁻¹) := by
  rw [mul_inv_rev, inv_inv, map_mul, map_inv, mul_assoc, ← mul_assoc u⁻¹, inv_mul_cancel,
    one_mul]

private theorem adjFinV_mul (u u' : (AdeleRing (𝓞 K) K)ˣ) (α α' : Kˣ)
    (v : HeightOneSpectrum (𝓞 K)) :
    adjFinV K (u * u') (α * α') v = adjFinV K u α v * adjFinV K u' α' v := by
  unfold adjFinV
  rw [show u * u' * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) (α * α'))⁻¹
      = (u * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)⁻¹)
        * (u' * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α')⁻¹) from by
    rw [map_mul, mul_inv_rev]; exact four_comm _ _ _ _]
  exact fad_mul_apply K _ _ v

namespace IsAdjuster
p2m_open_scoped "HeckeCharacter.IsAdjuster" in
private theorem _root_.HeckeCharacter.IsAdjuster.mul {𝔣 : Ideal (𝓞 K)} {u u' : (AdeleRing (𝓞 K) K)ˣ} {α α' : Kˣ}
    (hα : IsAdjuster K 𝔣 u α) (hα' : IsAdjuster K 𝔣 u' α') :
    IsAdjuster K 𝔣 (u * u') (α * α') := by
  have hfac : u * u' * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) (α * α'))⁻¹
      = (u * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)⁻¹)
        * (u' * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α')⁻¹) := by
    rw [map_mul, mul_inv_rev]; exact four_comm _ _ _ _
  refine ⟨fun v hv𝔣 => ?_, fun τ => ?_⟩
  · show Valued.v (adjFinV K (u * u') (α * α') v) = 1 ∧
      Valued.v (adjFinV K (u * u') (α * α') v - 1) ≤ _
    rw [adjFinV_mul]
    exact unit_cong_mul K (hα.cong v hv𝔣).1 (hα.cong v hv𝔣).2 (hα'.cong v hv𝔣).1
      (hα'.cong v hv𝔣).2
  · rw [hfac, archSign_mul K τ]
    exact iff_of_true (hα.sign τ) (hα'.sign τ)

end IsAdjuster
p2m_export "HeckeCharacter" "IsAdjuster.mul"
private theorem isAdjuster_principal_self (𝔣 : Ideal (𝓞 K)) (α : Kˣ) :
    IsAdjuster K 𝔣 (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α) α := by
  refine ⟨fun v _ => ?_, fun τ => ?_⟩
  · have h1 : adjFinV K (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α) α v = 1 := by
      unfold adjFinV; simp only [mul_inv_cancel, Units.val_one]
      exact fad_one_apply K v
    show Valued.v (adjFinV K _ α v) = 1 ∧ Valued.v (adjFinV K _ α v - 1) ≤ _
    rw [h1]
    exact ⟨map_one _, by rw [sub_self, map_zero]; exact zero_le'⟩
  · have h1 : (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α : (AdeleRing (𝓞 K) K)ˣ)
        * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)⁻¹ = 1 := mul_inv_cancel _
    rw [h1]; exact archSign_one K τ

private theorem adjFinV_ratio (u : (AdeleRing (𝓞 K) K)ˣ) (α α' : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    (((α * α'⁻¹ : Kˣ) : K) : v.adicCompletion K)
      = adjFinV K u α' v * (adjFinV K u α v)⁻¹ := by
  have hkey := congrArg (fun x : (FiniteAdeleRing (𝓞 K) K)ˣ =>
    ((x : FiniteAdeleRing (𝓞 K) K) : FiniteAdeleRing (𝓞 K) K) v)
    (congrArg (projFin K) (adj_adele_ratio K u α α'))
  rw [map_mul, map_inv, projFin_principal] at hkey
  simp only [Units.val_mul, fad_mul_apply, fad_units_inv_apply, projFin_val] at hkey
  rw [show ((FiniteAdeleRing.unitEmbedding (𝓞 K) K (α * α'⁻¹) : (FiniteAdeleRing (𝓞 K) K)ˣ) :
      FiniteAdeleRing (𝓞 K) K) v = (((α * α'⁻¹ : Kˣ) : K) : v.adicCompletion K) from by
    rw [FiniteAdeleRing.unitEmbedding_apply]; exact FiniteAdeleRing.algebraMap_apply ..] at hkey
  rw [← hkey, mul_comm]; rfl

private theorem valuation_ratio_sub_one_le {𝔣 : Ideal (𝓞 K)} {u : (AdeleRing (𝓞 K) K)ˣ} {α α' : Kˣ}
    (hα : IsAdjuster K 𝔣 u α) (hα' : IsAdjuster K 𝔣 u α')
    (v : HeightOneSpectrum (𝓞 K)) (hv : v.asIdeal ∣ 𝔣) :
    v.valuation K (((α * α'⁻¹ : Kˣ) : K) - 1)
      ≤ WithZero.exp (-(idealMultiplicity K v 𝔣 : ℤ)) := by
  rw [← v.valuedAdicCompletion_eq_valuation']
  have hcoe : ((((α * α'⁻¹ : Kˣ) : K) - 1 : K) : v.adicCompletion K)
      = (((α * α'⁻¹ : Kˣ) : K) : v.adicCompletion K) - 1 := by
    have h : ∀ y : K, (y : v.adicCompletion K) = algebraMap K (v.adicCompletion K) y := fun y => by
      rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]; rfl
    rw [h, h, map_sub, map_one]
  rw [hcoe, adjFinV_ratio K u α α']
  exact unit_cong_div K (hα'.cong v hv).2 (hα.cong v hv).1 (hα.cong v hv).2

private theorem ratio_totally_positive {𝔣 : Ideal (𝓞 K)} {u : (AdeleRing (𝓞 K) K)ˣ} {α α' : Kˣ}
    (hα : IsAdjuster K 𝔣 u α) (hα' : IsAdjuster K 𝔣 u α') (τ : K →+* ℝ) :
    0 < τ ((α * α'⁻¹ : Kˣ) : K) := by
  rw [← archSign_principal K τ, show Units.map (algebraMap K (AdeleRing (𝓞 K) K)) (α * α'⁻¹)
    = pK K (α * α'⁻¹) from rfl, map_mul, map_inv, archSign_mul K τ, archSign_inv K τ]
  have h1 : archSign K τ u ↔ archSign K τ (pK K α) := by
    have := hα.sign τ; rwa [archSign_mul K τ, archSign_inv K τ] at this
  have h2 : archSign K τ u ↔ archSign K τ (pK K α') := by
    have := hα'.sign τ; rwa [archSign_mul K τ, archSign_inv K τ] at this
  exact h1.symm.trans h2

private theorem valuation_eq_one_of_cong {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥) {β : K}
    (hcong : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
      v.valuation K (β - 1) ≤ WithZero.exp (-(idealMultiplicity K v 𝔣 : ℤ)))
    (v : HeightOneSpectrum (𝓞 K)) (hv : v.asIdeal ∣ 𝔣) :
    v.valuation K β = 1 := by
  have hm1 : 1 ≤ idealMultiplicity K v 𝔣 := by
    unfold idealMultiplicity
    rwa [Nat.one_le_iff_ne_zero, Associates.count_ne_zero_iff_dvd h𝔣 v.irreducible]
  have hlt : v.valuation K (β - 1) < 1 :=
    lt_of_le_of_lt (hcong v hv) (by
      rw [show (1 : ℤᵐ⁰) = WithZero.exp (0 : ℤ) from (WithZero.exp_zero).symm,
        WithZero.exp_lt_exp]
      omega)
  have hβ : β = (β - 1) + 1 := (sub_add_cancel β 1).symm
  rw [hβ, Valuation.map_add_eq_of_lt_right _ (by rwa [map_one]), map_one]

private theorem count_spanSingleton_eq_zero_of_valuation_eq_one {β : Kˣ}
    (v : HeightOneSpectrum (𝓞 K)) (h : v.valuation K (β : K) = 1) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton ((𝓞 K)⁰) (β : K)) = 0 := by
  rw [← placeOrd_unitEmbedding]
  unfold placeOrd
  rw [FiniteAdeleRing.unitEmbedding, Units.coe_map, MonoidHom.coe_coe,
    FiniteAdeleRing.algebraMap_apply,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (β : K), h,
    WithZero.log_one, neg_zero]

private theorem mem_modulus_of_forall_valuation_le {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥) {x : 𝓞 K}
    (hx : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
      v.valuation K (algebraMap (𝓞 K) K x) ≤ WithZero.exp (-(idealMultiplicity K v 𝔣 : ℤ))) :
    x ∈ 𝔣 := by
  have h𝔣0 : (𝔣 : Ideal (𝓞 K)) ≠ 0 := by rwa [Ne, Ideal.zero_eq_bot]
  rw [← Ideal.iInf_maxPowDividing_eq h𝔣0, Submodule.mem_iInf]
  intro v
  show x ∈ v.asIdeal ^ (idealMultiplicity K v 𝔣)
  by_cases hv : v.asIdeal ∣ 𝔣
  · rw [← v.intValuation_le_pow_iff_mem, ← v.valuation_of_algebraMap (K := K)]
    exact hx v hv
  · have hm0 : idealMultiplicity K v 𝔣 = 0 := by
      unfold idealMultiplicity
      by_contra hne
      exact hv ((Associates.count_ne_zero_iff_dvd h𝔣 v.irreducible).mp hne)
    simp [hm0]

private theorem toPrincipalIdeal_mem_narrowRaySubgroup {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥) (β : Kˣ)
    (hcong : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
      v.valuation K ((β : K) - 1) ≤ WithZero.exp (-(idealMultiplicity K v 𝔣 : ℤ)))
    (hsign : ∀ τ : K →+* ℝ, 0 < τ (β : K)) :
    toPrincipalIdeal (𝓞 K) K β ∈ narrowRaySubgroup K 𝔣 := by

  have hloc : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton ((𝓞 K)⁰) (β : K)) = 0 :=
    fun v hv => count_spanSingleton_eq_zero_of_valuation_eq_one K v
      (valuation_eq_one_of_cong K h𝔣 hcong v hv)

  obtain ⟨d, hd0, hd1, n, hn⟩ := movingLemma K h𝔣 (β : K) β.ne_zero hloc

  have hd0' : (algebraMap (𝓞 K) K) d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hd0
  have hn0 : n ≠ 0 := by
    rintro rfl; rw [map_zero] at hn
    exact β.ne_zero ((mul_eq_zero.mp hn.symm).resolve_left hd0')

  have hnd1 : n - d ∈ 𝔣 := by
    refine mem_modulus_of_forall_valuation_le K h𝔣 fun v hv => ?_
    have hval_d : v.valuation K (algebraMap (𝓞 K) K d) = 1 := by
      rw [v.valuation_of_algebraMap (K := K)]
      refine le_antisymm (v.intValuation_le_one d) ?_
      rw [← not_lt, v.intValuation_lt_one_iff_mem]
      intro hmem
      exact v.isMaximal.ne_top ((Ideal.eq_top_iff_one _).mpr
        (show (1 : 𝓞 K) ∈ v.asIdeal from by
          have : (d : 𝓞 K) - (d - 1) ∈ v.asIdeal := sub_mem hmem
            ((Ideal.dvd_iff_le.mp hv) hd1)
          simpa using this))
    have hsplit : (algebraMap (𝓞 K) K) (n - d)
        = algebraMap (𝓞 K) K d * ((β : K) - 1) := by
      rw [map_sub, hn]; ring
    rw [hsplit, map_mul, hval_d, one_mul]
    exact hcong v hv
  have hn1 : n - 1 ∈ 𝔣 := by
    have : n - 1 = (n - d) + (d - 1) := by ring
    rw [this]; exact add_mem hnd1 hd1

  have hn0' : (algebraMap (𝓞 K) K) n ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hn0
  have hsgn : ∀ τ : K →+* ℝ, (0 < τ (algebraMap (𝓞 K) K n))
      ↔ (0 < τ (algebraMap (𝓞 K) K d)) := by
    intro τ
    have hτβ : 0 < τ (β : K) := hsign τ
    rw [show (algebraMap (𝓞 K) K) n = (algebraMap (𝓞 K) K) d * (β : K) from hn,
      map_mul]
    refine ⟨fun h => ?_, fun h => mul_pos h hτβ⟩
    exact ((mul_pos_iff.mp h).resolve_right fun ⟨_, hb⟩ => hb.not_gt hτβ).1

  set yn : ↥(coprimeToModulus K 𝔣) :=
    ⟨principalUnit K n hn0, principalUnit_mem_coprimeToModulus K hn0 hn1⟩ with hyn_def
  set yd : ↥(coprimeToModulus K 𝔣) :=
    ⟨principalUnit K d hd0, principalUnit_mem_coprimeToModulus K hd0 hd1⟩ with hyd_def
  have hyn_val : ((yn : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K)
      = ((Ideal.span {n} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) :=
    principalUnit_val K n hn0
  have hyd_val : ((yd : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K)
      = ((Ideal.span {d} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) :=
    principalUnit_val K d hd0

  have hyd2 : ((yd * yd : ↥(coprimeToModulus K 𝔣)) : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) ∈
      narrowRaySubgroup K 𝔣 :=
    Subgroup.subset_closure (mul_mem_narrowRaySet_of_sameSign K hd0 hd1 hyd_val hd0 hd1 hyd_val
      fun _ => Iff.rfl)
  have hynyd : ((yn * yd : ↥(coprimeToModulus K 𝔣)) : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) ∈
      narrowRaySubgroup K 𝔣 :=
    Subgroup.subset_closure (mul_mem_narrowRaySet_of_sameSign K hn0 hn1 hyn_val hd0 hd1 hyd_val
      hsgn)

  have hβnd' : toPrincipalIdeal (𝓞 K) K β * (yd : (FractionalIdeal ((𝓞 K)⁰) K)ˣ)
      = (yn : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) := by
    refine Units.ext ?_
    rw [Units.val_mul, hyn_val, hyd_val, coe_toPrincipalIdeal,
      FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.spanSingleton_mul_spanSingleton, mul_comm, hn]
  have hβnd : toPrincipalIdeal (𝓞 K) K β
      = (yn : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) * (yd : (FractionalIdeal ((𝓞 K)⁰) K)ˣ)⁻¹ :=
    eq_mul_inv_of_mul_eq hβnd'

  rw [hβnd]
  have hrw : (yn : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) * (yd : (FractionalIdeal ((𝓞 K)⁰) K)ˣ)⁻¹
      = (((yd * yd : ↥(coprimeToModulus K 𝔣)) : (FractionalIdeal ((𝓞 K)⁰) K)ˣ))⁻¹
        * ((yn * yd : ↥(coprimeToModulus K 𝔣)) : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, mul_inv_rev, mul_assoc,
      show ((yd : (FractionalIdeal ((𝓞 K)⁰) K)ˣ))⁻¹
          * ((yn : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) * (yd : (FractionalIdeal ((𝓞 K)⁰) K)ˣ))
        = (yn : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) from by
          rw [mul_comm (yn : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) _, ← mul_assoc, inv_mul_cancel,
            one_mul],
      mul_comm]
  rw [hrw]
  exact mul_mem (inv_mem hyd2) hynyd

private theorem mk_eq_mk_of_isAdjuster {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥)
    {u : (AdeleRing (𝓞 K) K)ˣ} {α α' : Kˣ}
    (hα : IsAdjuster K 𝔣 u α) (hα' : IsAdjuster K 𝔣 u α') :
    NarrowRayClassGroup.mk K 𝔣 ⟨_, hα.coprime⟩
      = NarrowRayClassGroup.mk K 𝔣 ⟨_, hα'.coprime⟩ := by
  rw [NarrowRayClassGroup.mk_eq_mk_iff]
  show (fadContentHom K (projFin K _))⁻¹ * fadContentHom K (projFin K _) ∈ _
  rw [← map_inv, ← map_mul, ← map_inv, ← map_mul, adj_adele_ratio K u α α',
    projFin_principal, fadContentHom_unitEmbedding]
  exact toPrincipalIdeal_mem_narrowRaySubgroup K h𝔣 (α * α'⁻¹)
    (fun v hv => valuation_ratio_sub_one_le K hα hα' v hv)
    (fun τ => ratio_totally_positive K hα hα' τ)

end StageC

end HeckeCharacter

section Battery
p2m_open "HeckeCharacter P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.HeckeCharacter"
end Battery
end

end Fold_M4aTheta_IdeleContentBuild

section Fold_M4aTheta_MixedApprox

p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.NumberField IsDedekindDomain AbsoluteValue"
open Filter Topology

namespace NumberField
p2m_export "NumberField" "FinitePlace ComplexEmbedding.isReal_iff InfinitePlace.mk_embedding FinitePlace.norm_lt_one_iff_mem FinitePlace.mk InfinitePlace.embedding_of_isReal_apply RingOfIntegers.mapRingHom InfinitePlace.IsReal InfinitePlace.map_natCast Units.rank of_module_finite mk InfinitePlace.mk_eq_iff InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe FinitePlace.norm_eq_one_iff_notMem InfinitePlace.embedding_mk_eq_of_isReal RingOfIntegers.not_isField InfinitePlace.mk InfinitePlace.denseRange_algebraMap_pi AdeleRing.algebraMap_fst_apply InfinitePlace.Completion FinitePlace.norm_embedding InfinitePlace.embedding_of_isReal HeightOneSpectrum.adicAbv InfinitePlace.eq_iff_isEquiv RingOfIntegers of_intermediateField RingOfIntegers.basis RingOfIntegers.coe_injective HeightOneSpectrum.adicAbv_def HeightOneSpectrum.adicAbv_natCast_le_one InfinitePlace.isReal_iff InfinitePlace.apply ComplexEmbedding.IsReal InfinitePlace ComplexEmbedding.conjugate AdeleRing FinitePlace.embedding_apply InfinitePlace.mk_conjugate_eq HeightOneSpectrum.one_lt_absNorm_nnreal InfinitePlace.Completion.ringEquivRealOfIsReal_apply InfinitePlace.isNontrivial InfinitePlace.coe_apply RingOfIntegers.ext FinitePlace.mk_apply FinitePlace.embedding ComplexEmbedding.conjugate_coe_eq AdeleRing.unitIdelesOutside AdeleRing.finiteUnitsComponent AdeleRing.infiniteUnitsComponent AdeleRing.ideleBox AdeleRing.mem_ideleBox_iff AdeleRing.ideleBox_le_unitIdelesOutside PrimeNormIndex.admissibleExpAt PrimeNormIndex.IsAdmissibleModulusAt AdeleRing.principalIdeles_inf_unitIdelesOutside_eq_map_unit AdeleRing.principalIdeles_sup_unitIdelesOutside_eq_top AdeleRing.relIndex_ideleBox_unitIdelesOutside exists_pow_eq_of_forall_mem_range_powMonoidHom natCard_sUnit_quotient_range_powMonoidHom prod_natCard_units_adicCompletion_quotient_range_powMonoidHom_mul_prod_infinitePlace_eq_pow"
p2m_open "NumberField"

variable (K : Type*) [Field K] [NumberField K]

namespace FinitePlace p2m_export "NumberField.FinitePlace" "norm_lt_one_iff_mem mk coe_apply norm_eq_one_iff_notMem mk_eq_iff pos_iff norm_embedding embedding_apply maximalIdeal mk_apply embedding" end FinitePlace
namespace FinitePlace
p2m_open_scoped "NumberField.FinitePlace" in
private theorem _root_.NumberField.FinitePlace.isNontrivial (v : HeightOneSpectrum (𝓞 K)) :
    (FinitePlace.mk v).1.IsNontrivial := by
  obtain ⟨x, hx, hx0⟩ : ∃ x ∈ v.asIdeal, x ≠ 0 := by
    obtain ⟨x, hx, hx0⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr v.ne_bot)
    exact ⟨x, hx, fun h => hx0 (h ▸ Ideal.zero_mem _)⟩
  refine ⟨algebraMap (𝓞 K) K x, ?_, ?_⟩
  · exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hx0
  · show (FinitePlace.mk v).1 (algebraMap (𝓞 K) K x) ≠ 1
    rw [show (FinitePlace.mk v).1 (algebraMap (𝓞 K) K x)
        = ‖FinitePlace.embedding v (algebraMap (𝓞 K) K x)‖ from rfl]
    exact ((FinitePlace.norm_lt_one_iff_mem K v x).mpr hx).ne

end FinitePlace
p2m_export "NumberField" "FinitePlace.isNontrivial"
p2m_open_scoped "NumberField.FinitePlace" in
private theorem FinitePlace.not_isEquiv_of_ne {v₁ v₂ : HeightOneSpectrum (𝓞 K)} (h : v₁ ≠ v₂) :
    ¬ (FinitePlace.mk v₁).1.IsEquiv (FinitePlace.mk v₂).1 := by
  rw [isEquiv_iff_lt_one_iff]
  push Not
  have ⟨x, hx1, hx2⟩ : ∃ x : 𝓞 K, x ∈ v₁.asIdeal ∧ x ∉ v₂.asIdeal := by
    by_contra! H
    exact h (HeightOneSpectrum.ext_iff.mpr
      (Ideal.IsMaximal.eq_of_le (HeightOneSpectrum.isMaximal v₁) Ideal.IsPrime.ne_top' H))
  refine ⟨algebraMap (𝓞 K) K x, ?_⟩
  rw [show ((FinitePlace.mk v₁).1 : K → ℝ) = fun y => ‖FinitePlace.embedding v₁ y‖ from rfl,
    show ((FinitePlace.mk v₂).1 : K → ℝ) = fun y => ‖FinitePlace.embedding v₂ y‖ from rfl]
  simp only
  exact Or.inl ⟨(FinitePlace.norm_lt_one_iff_mem K v₁ x).mpr hx1,
    ((FinitePlace.norm_eq_one_iff_notMem K v₂ x).mpr hx2).ge⟩

namespace InfinitePlace p2m_export "NumberField.InfinitePlace" "mk_embedding embedding_of_isReal_apply IsReal smul_apply inertiaDeg_eq_one mk_eq_iff Completion.extensionEmbeddingOfIsReal_coe embedding_mk_eq_of_isReal mk denseRange_algebraMap_pi Completion embedding_of_isReal eq_iff_isEquiv ext comap pos_iff isReal_iff apply embedding mk_conjugate_eq Completion.ringEquivRealOfIsReal_apply isNontrivial coe_apply le_iff_le Extension" end InfinitePlace
p2m_open_scoped "NumberField.InfinitePlace" in
private theorem InfinitePlace.not_isEquiv_finitePlace (w : InfinitePlace K)
    (v : HeightOneSpectrum (𝓞 K)) :
    ¬ w.1.IsEquiv (FinitePlace.mk v).1 := by
  intro hequiv
  have hw2 : ¬ w.1 (2 : K) ≤ 1 := by
    have : (2 : K) = ((2 : ℕ) : K) := by norm_num
    rw [← InfinitePlace.coe_apply, this, InfinitePlace.map_natCast w 2]
    norm_num
  have hv2 : (FinitePlace.mk v).1 (2 : K) ≤ 1 := by
    show ‖FinitePlace.embedding v (2 : K)‖ ≤ 1
    have : (2 : K) = ((2 : ℕ) : K) := by norm_num
    rw [FinitePlace.norm_embedding, this]
    exact HeightOneSpectrum.adicAbv_natCast_le_one K v 2
  exact hw2 (hequiv.le_one_iff.mpr hv2)

private noncomputable def mixedAbs (S : Finset (HeightOneSpectrum (𝓞 K))) :
    InfinitePlace K ⊕ ↥S → AbsoluteValue K ℝ :=
  Sum.elim (·.1) (fun v => (FinitePlace.mk v.1).1)

private theorem mixedAbs_isNontrivial (S : Finset (HeightOneSpectrum (𝓞 K)))
    (i : InfinitePlace K ⊕ ↥S) : (mixedAbs K S i).IsNontrivial := by
  rcases i with w | v
  · exact InfinitePlace.isNontrivial w
  · exact FinitePlace.isNontrivial K v.1

private theorem mixedAbs_pairwise_not_isEquiv (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Pairwise fun i j => ¬ (mixedAbs K S i).IsEquiv (mixedAbs K S j) := by
  intro i j hij
  match i, j with
  | Sum.inl w, Sum.inl w' =>
    exact (InfinitePlace.eq_iff_isEquiv (K := K)).not.mp (by simpa using hij)
  | Sum.inl w, Sum.inr v => exact InfinitePlace.not_isEquiv_finitePlace K w v.1
  | Sum.inr v, Sum.inl w =>
    exact fun h => InfinitePlace.not_isEquiv_finitePlace K w v.1 h.symm
  | Sum.inr v, Sum.inr v' =>
    exact FinitePlace.not_isEquiv_of_ne K (by simpa using hij)

private theorem denseRange_algebraMap_pi_mixedAbs (S : Finset (HeightOneSpectrum (𝓞 K))) :
    DenseRange (algebraMap K ((i : InfinitePlace K ⊕ ↥S) → WithAbs (mixedAbs K S i))) := by
  classical
  refine Metric.denseRange_iff.mpr fun z r hr ↦ ?_
  choose a hx using AbsoluteValue.exists_one_lt_lt_one_pi_of_not_isEquiv
    (mixedAbs_isNontrivial K S) (mixedAbs_pairwise_not_isEquiv K S)
  let y := fun n ↦
    ∑ i, (1 / (1 + (a i)⁻¹ ^ n)) * WithAbs.equiv (mixedAbs K S i) (z i)
  have htend : Filter.atTop.Tendsto
      (fun n i ↦ (WithAbs.equiv (mixedAbs K S i)).symm (y n)) (𝓝 z) := by
    refine tendsto_pi_nhds.mpr fun u ↦ ?_
    simp_rw [← Fintype.sum_pi_single u z, y, map_sum, map_mul]
    refine tendsto_finsetSum _ fun w _ ↦ ?_
    by_cases hw : u = w
    · rw [← hw, Pi.single_eq_same]
      have : mixedAbs K S u (a u)⁻¹ < 1 := by
        simpa [← inv_pow, inv_lt_one_iff₀] using .inr (hx u).1
      simpa using (WithAbs.tendsto_one_div_one_add_pow_nhds_one this).mul_const (z u)
    · rw [Pi.single_eq_of_ne (M := fun i ↦ WithAbs (mixedAbs K S i)) hw (z w)]
      have haw0 : a w ≠ 0 := fun ha => by
        have := (hx w).1; rw [ha, map_zero] at this; linarith
      have hu : 1 < mixedAbs K S u (a w)⁻¹ := by
        rw [map_inv₀, one_lt_inv_iff₀]
        exact ⟨(mixedAbs K S u).pos_iff.2 haw0, (hx w).2 u hw⟩
      have := (mixedAbs K S u).tendsto_div_one_add_pow_nhds_zero hu
      simp_rw [← WithAbs.norm_toAbs_eq] at this
      simpa using (tendsto_zero_iff_norm_tendsto_zero.2 this).mul_const
        ((WithAbs.equiv (mixedAbs K S u)).symm (WithAbs.equiv (mixedAbs K S w) (z w)))
  let ⟨N, h⟩ := Metric.tendsto_atTop.1 htend r hr
  exact ⟨y N, dist_comm z (algebraMap K _ (y N)) ▸ h N le_rfl⟩

private theorem denseRange_algebraMap_pi_mixedAbs_empty :
    DenseRange (algebraMap K ((w : InfinitePlace K) → WithAbs w.1)) :=
  InfinitePlace.denseRange_algebraMap_pi K

end NumberField

section Battery
p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.NumberField"
end Battery

end Fold_M4aTheta_MixedApprox

section Fold_M4aTheta_ExistsAdjuster

p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.NumberField IsDedekindDomain"
open scoped nonZeroDivisors

namespace HeckeCharacter
p2m_export "HeckeCharacter" "idealMultiplicity placeUnder' placeUnder'_asIdeal modulusExt fracRelNormUnit placeUnder'_dvd_iff gcopNC2 coe_raySymbol_gcop_eq_fracRelNormUnit' fracRelNormUnit_mem_coprimeToModulus relNormCTM fad_one_apply fad_mul_apply placeOrd valued_ne_zero_of_unit placeOrd_eq_zero_iff finite_support_placeOrd fadContentHom projFin placeOf isReal_compOfRealHom isReal_placeOf archRealProjTau archSign archSign_of_fst_eq_one archSign_mul archSign_one archSign_inv unit_cong_mul unit_cong_div fad_units_inv_apply IsAdjuster fadContentHom_projFin_idelicNorm_eq_fracRelNormUnit isAdjuster_idelicNorm_of_isAdjuster"
p2m_open "HeckeCharacter"

variable (K : Type*) [Field K] [NumberField K]

private theorem isometry_finitePlaceEmbedding_withAbs (v : HeightOneSpectrum (𝓞 K)) :
    Isometry (fun x : WithAbs (FinitePlace.mk v).1 =>
      FinitePlace.embedding v (WithAbs.equiv (FinitePlace.mk v).1 x)) := by
  refine Isometry.of_dist_eq (fun x y => ?_)
  rw [dist_eq_norm, dist_eq_norm, ← map_sub (FinitePlace.embedding v),
    show WithAbs.equiv _ x - WithAbs.equiv _ y
      = WithAbs.ofAbs (v := (FinitePlace.mk v).1) (x - y) from (WithAbs.ofAbs_sub _ _ _).symm]
  exact (FinitePlace.mk_apply v (WithAbs.ofAbs (x - y))).symm

private theorem valuation_le_of_adicAbv_le (v : HeightOneSpectrum (𝓞 K)) {x y : K}
    (h : NumberField.HeightOneSpectrum.adicAbv K v x
      ≤ NumberField.HeightOneSpectrum.adicAbv K v y) :
    v.valuation K x ≤ v.valuation K y := by
  rw [NumberField.HeightOneSpectrum.adicAbv_def, NumberField.HeightOneSpectrum.adicAbv_def] at h
  exact (WithZeroMulInt.toNNReal_strictMono
    (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v)).le_iff_le.mp
    (by exact_mod_cast h)

private theorem sign_eq_of_withAbs_dist_lt (τ : K →+* ℝ) (α t : K) (ht : t ≠ 0)
    (h : (placeOf K τ).1 (α - t) < (placeOf K τ).1 t) :
    (0 < τ α ↔ 0 < τ t) := by

  have hval : ∀ x : K, (placeOf K τ).1 x = |τ x| := by
    intro x
    rw [← InfinitePlace.coe_apply]
    show (InfinitePlace.mk (Complex.ofRealHom.comp τ)) x = |τ x|
    rw [InfinitePlace.apply, RingHom.comp_apply, Complex.ofRealHom_eq_coe,
      Complex.norm_real, Real.norm_eq_abs]
  rw [hval, hval, map_sub] at h

  have ht0 : τ t ≠ 0 := fun h0 => ht ((map_eq_zero τ).mp h0)
  rcases lt_or_gt_of_ne ht0 with hneg | hpos
  · refine ⟨fun hα => absurd ?_ (not_lt.mpr hα.le), fun hα => absurd hα hneg.not_gt⟩
    calc τ α = τ t + (τ α - τ t) := by ring
      _ < 0 := by
        have := abs_lt.mp h
        linarith [abs_of_neg hneg ▸ this.2]
  · refine ⟨fun _ => hpos, fun _ => ?_⟩
    calc (0 : ℝ) < τ t - |τ α - τ t| := by linarith [abs_of_pos hpos ▸ h]
      _ ≤ τ t - (τ t - τ α) := by linarith [neg_abs_le (τ α - τ t)]
      _ = τ α := by ring

private noncomputable def primesOf (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥) :
    Finset (HeightOneSpectrum (𝓞 K)) :=
  (Ideal.finite_factors (by rwa [Ne, Ideal.zero_eq_bot])).toFinset

private theorem mem_primesOf {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥) (v : HeightOneSpectrum (𝓞 K)) :
    v ∈ primesOf K 𝔣 h𝔣 ↔ v.asIdeal ∣ 𝔣 :=
  Set.Finite.mem_toFinset _

private noncomputable def fadComp (u : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    v.adicCompletion K :=
  ((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v

private theorem fadComp_ne_zero (u : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    fadComp K u v ≠ 0 := by
  intro h
  exact valued_ne_zero_of_unit K (projFin K u) v (by rw [projFin_val, ← fadComp, h, map_zero])

private theorem archRealProjTau_principal (τ : K →+* ℝ) (α : Kˣ) :
    archRealProjTau K τ (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α) = τ (α : K) := by
  unfold archRealProjTau
  rw [Units.coe_map, MonoidHom.coe_coe, AdeleRing.algebraMap_fst_apply,
    InfinitePlace.Completion.ringEquivRealOfIsReal_apply,
    InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe, embedding_of_isReal_placeOf]
  rfl

private theorem exists_embedding_near_fadComp (u : (AdeleRing (𝓞 K) K)ˣ)
    (v : HeightOneSpectrum (𝓞 K)) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : K, ‖FinitePlace.embedding v t - fadComp K u v‖ < ε := by
  obtain ⟨t, ht⟩ := Metric.denseRange_iff.mp (v.denseRange_algebraMap K) (fadComp K u v) ε hε
  exact ⟨t, by rw [FinitePlace.embedding_apply]; rwa [dist_comm, dist_eq_norm] at ht⟩

private theorem cong_of_completion_close {v : HeightOneSpectrum (𝓞 K)} {α : K} {U : v.adicCompletion K}
    (hU : U ≠ 0) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (h : ‖FinitePlace.embedding v α - U‖ < ‖U‖ * δ) :
    ‖U * (FinitePlace.embedding v α)⁻¹‖ = 1 ∧
    ‖U * (FinitePlace.embedding v α)⁻¹ - 1‖ ≤ δ := by
  set αv := FinitePlace.embedding v α with hαv
  have hUpos : 0 < ‖U‖ := norm_pos_iff.mpr hU
  have hlt : ‖αv - U‖ < ‖U‖ :=
    h.trans_le (by nlinarith)
  have hαeq : ‖αv‖ = ‖U‖ := by
    have hne : ‖U‖ ≠ ‖αv - U‖ := (hlt.trans_le (le_refl _)).ne'
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := U) (y := αv - U) hne
    rw [add_sub_cancel, max_eq_left hlt.le] at this
    exact this
  have hα0 : αv ≠ 0 := fun h0 => by simp [h0] at hαeq; exact hU (norm_eq_zero.mp hαeq.symm)
  refine ⟨?_, ?_⟩
  · rw [norm_mul, norm_inv, hαeq, mul_inv_cancel₀ hUpos.ne']
  · have hfac : U * αv⁻¹ - 1 = (U - αv) * αv⁻¹ := by
      field_simp
    rw [hfac, norm_mul, norm_inv, hαeq, norm_sub_rev]
    calc ‖αv - U‖ * ‖U‖⁻¹ ≤ (‖U‖ * δ) * ‖U‖⁻¹ := by
          exact mul_le_mul_of_nonneg_right h.le (inv_nonneg.mpr hUpos.le)
      _ = δ := by field_simp

private theorem adjCompEq (u : (AdeleRing (𝓞 K) K)ˣ) (α : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    (((u * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)⁻¹ :
        (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v
      = fadComp K u v * (FinitePlace.embedding v (α : K))⁻¹ := by
  have hmul : ((u * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)⁻¹ :
      (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2
      = (u : AdeleRing (𝓞 K) K).2
        * (((Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)⁻¹ :
            (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 := by
    rw [Units.val_mul]; rfl
  rw [hmul, fad_mul_apply K, ← fadComp]
  congr 1
  rw [← map_inv, Units.coe_map, MonoidHom.coe_coe, Units.val_inv_eq_inv_val,
    FinitePlace.embedding_apply]
  show ((algebraMap K (AdeleRing (𝓞 K) K)) ((α : K)⁻¹)).2 v = _
  rw [show ∀ x : K, ((algebraMap K (AdeleRing (𝓞 K) K)) x).2 v
      = algebraMap K (v.adicCompletion K) x from fun x => rfl,
    map_inv₀]
  rfl

private theorem valued_cong_of_norm_cong {v : HeightOneSpectrum (𝓞 K)} {X Y : v.adicCompletion K}
    (h1 : ‖X‖ = 1) (h2 : ‖X - 1‖ ≤ ‖Y‖) :
    Valued.v X = 1 ∧ Valued.v (X - 1) ≤ Valued.v Y := by
  refine ⟨le_antisymm ?_ ?_, ?_⟩
  · exact (Valued.toNormedField.norm_le_one_iff).mp h1.le
  · exact (Valued.toNormedField.one_le_norm_iff).mp h1.ge
  · exact (Valued.toNormedField.norm_le_iff).mp h2

private theorem exists_isAdjuster {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥) (u : (AdeleRing (𝓞 K) K)ˣ) :
    ∃ α : Kˣ, IsAdjuster K 𝔣 u α := by
  classical
  set S := primesOf K 𝔣 h𝔣 with hS

  obtain ⟨γ, hγ𝔣, hγ0⟩ : ∃ γ : 𝓞 K, γ ∈ 𝔣 ∧ γ ≠ 0 := by
    obtain ⟨γ, hγ𝔣, hγ0⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr h𝔣)
    exact ⟨γ, hγ𝔣, fun h => hγ0 (h ▸ Ideal.zero_mem ⊥)⟩
  have hγK0 : (γ : K) ≠ 0 := by exact_mod_cast hγ0

  have hγemb_ne : ∀ v : HeightOneSpectrum (𝓞 K), FinitePlace.embedding v (γ : K) ≠ 0 :=
    fun v => (map_ne_zero _).mpr hγK0
  have hγnorm_pos : ∀ v : HeightOneSpectrum (𝓞 K), 0 < ‖FinitePlace.embedding v (γ : K)‖ :=
    fun v => norm_pos_iff.mpr (hγemb_ne v)
  have hγnorm_le_one : ∀ v : HeightOneSpectrum (𝓞 K),
      ‖FinitePlace.embedding v (γ : K)‖ ≤ 1 := by
    intro v
    rw [Valued.toNormedField.norm_le_one_iff,
      show FinitePlace.embedding v (γ : K) = ((γ : K) : v.adicCompletion K) from rfl,
      v.valuedAdicCompletion_eq_valuation']
    exact v.valuation_le_one γ
  have hγval_le : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
      Valued.v (FinitePlace.embedding v (γ : K))
        ≤ WithZero.exp (-(idealMultiplicity K v 𝔣 : ℤ)) := by
    intro v _
    rw [show FinitePlace.embedding v (γ : K) = ((γ : K) : v.adicCompletion K) from rfl,
      v.valuedAdicCompletion_eq_valuation', v.valuation_of_algebraMap]
    refine (v.intValuation_le_pow_iff_dvd γ _).mpr
      (dvd_trans ?_ ((Ideal.dvd_iff_le).mpr
        (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hγ𝔣))))
    have h𝔣0 : (Associates.mk 𝔣) ≠ 0 :=
      Associates.mk_ne_zero.mpr (by rwa [Ne, Ideal.zero_eq_bot])
    have hirr := Associates.irreducible_mk.mpr v.irreducible
    have := (Associates.prime_pow_dvd_iff_le h𝔣0 hirr
        (k := idealMultiplicity K v 𝔣)).mpr le_rfl
    rwa [← Associates.mk_pow, Associates.mk_le_mk_iff_dvd] at this

  have hUpos : ∀ v : HeightOneSpectrum (𝓞 K), 0 < ‖fadComp K u v‖ :=
    fun v => norm_pos_iff.mpr (fadComp_ne_zero K u v)

  set bnd : HeightOneSpectrum (𝓞 K) → ℝ :=
    fun v => ‖fadComp K u v‖ * ‖FinitePlace.embedding v (γ : K)‖ with hbnd
  have hbnd_pos : ∀ v, 0 < bnd v := fun v => mul_pos (hUpos v) (hγnorm_pos v)
  obtain ⟨r, hr0, hr1, hrS⟩ : ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ v ∈ S, r < bnd v := by
    by_cases hne : S.Nonempty
    · have hm_pos : 0 < S.inf' hne bnd :=
        (Finset.lt_inf'_iff hne).mpr (fun v _ => hbnd_pos v)
      refine ⟨min (1/2) (S.inf' hne bnd / 2), ?_, ?_, ?_⟩
      · exact lt_min (by norm_num) (by linarith)
      · exact (min_le_left _ _).trans_lt (by norm_num)
      · intro v hv
        refine (min_le_right _ _).trans_lt ?_
        have hle := Finset.inf'_le bnd hv
        linarith [hbnd_pos v]
    · exact ⟨1/2, by norm_num, by norm_num, fun v hv => absurd ⟨v, hv⟩ hne⟩

  have htv : ∀ v ∈ S, ∃ t : K, ‖FinitePlace.embedding v t - fadComp K u v‖ < r :=
    fun v _ => exists_embedding_near_fadComp K u v hr0
  choose tv htv using htv

  set archTgt : InfinitePlace K → K := fun w =>
    if hw : w.IsReal then
      (if archSign K (InfinitePlace.embedding_of_isReal hw) u then (1:K) else (-1:K))
    else (1:K) with harchTgt
  have harchTgt_ne : ∀ w, archTgt w ≠ 0 := by
    intro w; unfold archTgt; split_ifs
    · exact one_ne_zero
    · exact neg_ne_zero.mpr one_ne_zero
    · exact one_ne_zero
  have harchTgt_abs : ∀ w : InfinitePlace K, w (archTgt w) = 1 := by
    intro w; unfold archTgt; split_ifs
    · exact map_one _
    · exact (w.1.map_neg 1).trans (map_one _)
    · exact map_one _

  set z : InfinitePlace K ⊕ ↥S → K := Sum.elim archTgt (fun v => tv v.1 v.2) with hz

  obtain ⟨α, hα⟩ := Metric.denseRange_iff.mp
    (NumberField.denseRange_algebraMap_pi_mixedAbs K S)
    (fun i => (WithAbs.equiv (NumberField.mixedAbs K S i)).symm (z i)) r hr0
  have hα_at : ∀ i, (NumberField.mixedAbs K S i) (α - z i) < r := by
    intro i
    have hi := (dist_pi_lt_iff hr0).mp hα i
    rw [dist_comm, dist_eq_norm, WithAbs.norm_eq_apply_ofAbs, WithAbs.ofAbs_sub] at hi
    convert hi using 2
    all_goals first | rfl | simp

  have hα0 : α ≠ 0 := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace K) := inferInstance
    intro h
    have := hα_at (Sum.inl w)
    simp only [hz, Sum.elim_inl, h, zero_sub] at this
    have heq : (NumberField.mixedAbs K S (Sum.inl w)) (-archTgt w) = 1 := by
      change (w.1 : AbsoluteValue K ℝ) (-archTgt w) = 1
      rw [(w.1).map_neg, ← InfinitePlace.coe_apply, harchTgt_abs w]
    rw [heq] at this; linarith
  refine ⟨Units.mk0 α hα0, ?_, ?_⟩
  ·
    intro v hv
    have hvS : v ∈ S := (mem_primesOf K h𝔣 v).mpr hv
    rw [adjCompEq K u (Units.mk0 α hα0) v, Units.val_mk0]

    have hstep : ‖FinitePlace.embedding v α - fadComp K u v‖
        < ‖fadComp K u v‖ * ‖FinitePlace.embedding v (γ : K)‖ := by
      have hα_fin := hα_at (Sum.inr ⟨v, hvS⟩)
      simp only [hz, Sum.elim_inr, NumberField.mixedAbs] at hα_fin

      have h1 : ‖FinitePlace.embedding v α - FinitePlace.embedding v (tv v hvS)‖ < r := by
        rw [← map_sub]; exact hα_fin
      have h2 := htv v hvS
      calc ‖FinitePlace.embedding v α - fadComp K u v‖
          ≤ max ‖FinitePlace.embedding v α - FinitePlace.embedding v (tv v hvS)‖
              ‖FinitePlace.embedding v (tv v hvS) - fadComp K u v‖ := by
            rw [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm]
            exact IsUltrametricDist.dist_triangle_max _ _ _
        _ < r := max_lt h1 h2
        _ < bnd v := hrS v hvS
    have hcong := cong_of_completion_close K (fadComp_ne_zero K u v)
      (hγnorm_pos v) (hγnorm_le_one v) hstep
    have hbr := valued_cong_of_norm_cong K hcong.1 hcong.2
    exact ⟨hbr.1, hbr.2.trans (hγval_le v hv)⟩
  ·
    intro τ
    rw [archSign_mul K τ, archSign_inv K τ]
    show archSign K τ u ↔ archSign K τ (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) (Units.mk0 α hα0))
    unfold archSign
    rw [archRealProjTau_principal K τ (Units.mk0 α hα0), Units.val_mk0]

    have hwτ := isReal_placeOf K τ
    have htgt_τ : archTgt (placeOf K τ)
        = if (0:ℝ) < archRealProjTau K τ u then (1:K) else (-1:K) := by
      unfold archTgt; rw [dif_pos hwτ]
      congr 1
      · unfold archSign
        rw [show InfinitePlace.embedding_of_isReal hwτ = τ from embedding_of_isReal_placeOf K τ]
    have habs_tgt : (placeOf K τ) (archTgt (placeOf K τ)) = 1 := harchTgt_abs _
    have hclose : (placeOf K τ) (α - archTgt (placeOf K τ)) < (placeOf K τ) (archTgt (placeOf K τ)) := by
      rw [habs_tgt]
      have := hα_at (Sum.inl (placeOf K τ))
      simp only [hz, Sum.elim_inl, NumberField.mixedAbs] at this
      exact this.trans hr1
    have hsign_iff := sign_eq_of_withAbs_dist_lt K τ α (archTgt (placeOf K τ))
      (harchTgt_ne _) hclose
    constructor
    · intro hpos
      refine hsign_iff.mpr ?_
      rw [htgt_τ, if_pos hpos, map_one]; exact one_pos
    · intro hτα
      by_contra hneg
      have hlt : (0:ℝ) < -1 := by
        have := hsign_iff.mp hτα
        rwa [htgt_τ, if_neg hneg, map_neg, map_one] at this
      linarith

end HeckeCharacter

section Battery
p2m_open "HeckeCharacter P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.HeckeCharacter"
end Battery

end Fold_M4aTheta_ExistsAdjuster

section Fold_M4aTheta_IdeleContent

p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.NumberField IsDedekindDomain Deep.NTSupply WithZero"
open scoped nonZeroDivisors

noncomputable section

namespace HeckeCharacter
p2m_export "HeckeCharacter" "idealMultiplicity placeUnder' placeUnder'_asIdeal modulusExt fracRelNormUnit placeUnder'_dvd_iff gcopNC2 coe_raySymbol_gcop_eq_fracRelNormUnit' fracRelNormUnit_mem_coprimeToModulus relNormCTM fad_one_apply fad_mul_apply placeOrd valued_ne_zero_of_unit placeOrd_eq_zero_iff finite_support_placeOrd fadContentHom projFin placeOf isReal_compOfRealHom isReal_placeOf archRealProjTau archSign archSign_of_fst_eq_one archSign_mul archSign_one archSign_inv unit_cong_mul unit_cong_div fad_units_inv_apply IsAdjuster fadContentHom_projFin_idelicNorm_eq_fracRelNormUnit isAdjuster_idelicNorm_of_isAdjuster"
p2m_open "HeckeCharacter"

variable (K : Type*) [Field K] [NumberField K]

private def ideleContentHom (𝔣 : Ideal (𝓞 K)) :
    (AdeleRing (𝓞 K) K)ˣ →* NarrowRayClassGroup K 𝔣 := by
  classical
  by_cases h𝔣 : 𝔣 = ⊥
  · exact 1
  · exact
      { toFun := fun u => NarrowRayClassGroup.mk K 𝔣
          ⟨_, (Classical.choose_spec (exists_isAdjuster K h𝔣 u)).coprime⟩
        map_one' := by
          rw [mk_eq_mk_of_isAdjuster K h𝔣
            (Classical.choose_spec (exists_isAdjuster K h𝔣 1)) (isAdjuster_one_one K 𝔣)]
          simp only [map_one, inv_one, mul_one]; rfl
        map_mul' := fun u u' => by
          have hαu := Classical.choose_spec (exists_isAdjuster K h𝔣 u)
          have hαu' := Classical.choose_spec (exists_isAdjuster K h𝔣 u')
          have hαuu' : IsAdjuster K 𝔣 (u * u') (_ * _) := IsAdjuster.mul K hαu hαu'
          rw [mk_eq_mk_of_isAdjuster K h𝔣
              (Classical.choose_spec (exists_isAdjuster K h𝔣 (u * u'))) hαuu',
            ← (NarrowRayClassGroup.mk K 𝔣).map_mul ⟨_, hαu.coprime⟩ ⟨_, hαu'.coprime⟩]
          refine congrArg (NarrowRayClassGroup.mk K 𝔣) (Subtype.ext ?_)
          show fadContentHom K (projFin K _) = fadContentHom K (projFin K _)
            * fadContentHom K (projFin K _)
          rw [← map_mul, ← map_mul, adj_adele_mul K u u'] }

private theorem ideleContentHom_apply {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥)
    {u : (AdeleRing (𝓞 K) K)ˣ} {α : Kˣ} (hα : IsAdjuster K 𝔣 u α) :
    ideleContentHom K 𝔣 u = NarrowRayClassGroup.mk K 𝔣 ⟨_, hα.coprime⟩ := by
  unfold ideleContentHom
  rw [dif_neg h𝔣]
  exact mk_eq_mk_of_isAdjuster K h𝔣 (Classical.choose_spec (exists_isAdjuster K h𝔣 u)) hα

private theorem ideleContentHom_principal (𝔣 : Ideal (𝓞 K)) (α : Kˣ) :
    ideleContentHom K 𝔣 (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α) = 1 := by
  by_cases h𝔣 : 𝔣 = ⊥
  · unfold ideleContentHom; rw [dif_pos h𝔣]; rfl
  · rw [ideleContentHom_apply K h𝔣 (isAdjuster_principal_self K 𝔣 α)]
    have h1 : fadContentHom K (projFin K (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α
        * (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) α)⁻¹)) = 1 := by
      rw [mul_inv_cancel, map_one, map_one]
    rw [show (⟨_, (isAdjuster_principal_self K 𝔣 α).coprime⟩ : ↥(coprimeToModulus K 𝔣)) = 1
      from Subtype.ext h1, map_one]

private theorem ideleContentHom_uniformizerIdele_v2 (𝔣 : Ideal (𝓞 K))
    {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ 𝔣)
    (u : (AdeleRing (𝓞 K) K)ˣ)
    (huarch : (u : AdeleRing (𝓞 K) K).1 = 1)
    (huw : ∀ w : HeightOneSpectrum (𝓞 K), w ≠ v →
      Valued.v ((u : AdeleRing (𝓞 K) K).2 w) = 1)
    (huv : Valued.v ((u : AdeleRing (𝓞 K) K).2 v) = WithZero.exp (-1 : ℤ))
    (hu𝔣 : ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal ∣ 𝔣 →
      Valued.v ((u : AdeleRing (𝓞 K) K).2 w - 1)
        ≤ WithZero.exp (-(idealMultiplicity K w 𝔣 : ℤ))) :
    ideleContentHom K 𝔣 u = primeClass K 𝔣 v hv := by
  by_cases h𝔣 : 𝔣 = ⊥
  · subst h𝔣; simp only [show v.asIdeal ∣ (⊥ : Ideal (𝓞 K)) from ⟨0, (mul_zero _).symm⟩,
      not_true] at hv
  ·
    have hadj : IsAdjuster K 𝔣 u 1 := by
      refine ⟨fun w hw𝔣 => ?_, fun τ => ?_⟩
      · have hwv : w ≠ v := fun h => hv (h ▸ hw𝔣)
        show Valued.v (adjFinV K u 1 w) = 1 ∧ Valued.v (adjFinV K u 1 w - 1) ≤ _
        have hu1 : adjFinV K u 1 w = (((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K)
            w) := by unfold adjFinV; simp only [map_one, inv_one, mul_one]
        rw [hu1]
        exact ⟨huw w hwv, hu𝔣 w hw𝔣⟩
      · simp only [map_one, inv_one, mul_one]
        exact archSign_of_fst_eq_one K τ huarch
    rw [ideleContentHom_apply K h𝔣 hadj]

    refine congrArg (NarrowRayClassGroup.mk K 𝔣) (Subtype.ext ?_)
    show fadContentHom K (projFin K (u * (pK K 1)⁻¹)) = primeUnit K v
    rw [map_one, inv_one, mul_one, fadContentHom_apply]
    refine finprod_eq_single (fun w => primeUnit K w ^ placeOrd K (projFin K u) w) v
      ?_ |>.trans ?_
    · intro w hwv
      show primeUnit K w ^ placeOrd K (projFin K u) w = 1
      rw [show placeOrd K (projFin K u) w = 0 from
        (placeOrd_eq_zero_iff K (projFin K u) w).mpr (projFin_val K u ▸ huw w hwv), zpow_zero]
    · show primeUnit K v ^ placeOrd K (projFin K u) v = primeUnit K v
      rw [show placeOrd K (projFin K u) v = 1 from by
        unfold placeOrd; rw [projFin_val, huv, WithZero.log_exp, neg_neg], zpow_one]

end HeckeCharacter

end

section Battery
p2m_open "HeckeCharacter P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.HeckeCharacter"
end Battery

end Fold_M4aTheta_IdeleContent

section Fold_M4aKummer_ServedNorm

set_option autoImplicit false

p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.HeckeCharacter WithZero"
open scoped nonZeroDivisors

noncomputable section

namespace M4aKummer

section Gen

variable (K : Type*) [Field K] [NumberField K]

private def primeGens (𝔣 : Ideal (𝓞 K)) : Set (FractionalIdeal ((𝓞 K)⁰) K)ˣ :=
  {I | ∃ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔣 ∧ I = primeUnit K v}

private theorem closure_primeGens_le (𝔣 : Ideal (𝓞 K)) : Subgroup.closure (primeGens K 𝔣) ≤ coprimeToModulus K 𝔣 :=
  (Subgroup.closure_le _).mpr (by rintro _ ⟨v, hv, rfl⟩; exact primeUnit_mem_coprimeToModulus K hv)

omit [NumberField K] in

private theorem val_finprod {ι α : Type*} [CommMonoid α] (f : ι → αˣ) (hf : Function.HasFiniteMulSupport f) :
    (((∏ᶠ i, f i : αˣ)) : α) = ∏ᶠ i, (f i : α) :=
  MonoidHom.map_finprod (Units.coeHom α) hf

private theorem finprod_primeUnit_zpow_count (I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 K), primeUnit K v ^ FractionalIdeal.count K v (I : FractionalIdeal ((𝓞 K)⁰) K) = I := by
  apply Units.ext
  rw [val_finprod _ (hasFiniteMulSupport_raySymbol_factors K (primeUnit K) _)]
  simp only [Units.val_zpow_eq_zpow_val, primeUnit_val]
  exact FractionalIdeal.finprod_heightOneSpectrum_factorization' K I.ne_zero

private theorem coprimeToModulus_le_closure (𝔣 : Ideal (𝓞 K)) :
    coprimeToModulus K 𝔣 ≤ Subgroup.closure (primeGens K 𝔣) := by
  intro I hI
  rw [← finprod_primeUnit_zpow_count K I]
  refine finprod_induction (· ∈ Subgroup.closure _) (one_mem _) (fun _ _ => mul_mem) fun v => ?_
  by_cases hv : v.asIdeal ∣ 𝔣
  · rw [(mem_coprimeToModulus_iff (K := K)).mp hI v hv, zpow_zero]
    exact one_mem _
  · exact zpow_mem (Subgroup.subset_closure (show primeUnit K v ∈ primeGens K 𝔣 from ⟨v, hv, rfl⟩)) _

private theorem closure_primeCarriers_eq_top (𝔣 : Ideal (𝓞 K)) :
    Subgroup.closure {c : ↥(coprimeToModulus K 𝔣) | ∃ (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ 𝔣),
      c = ⟨primeUnit K v, primeUnit_mem_coprimeToModulus K hv⟩} = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨I, hI⟩ -
  have key : ∀ J ∈ Subgroup.closure (primeGens K 𝔣), ∀ hJ : J ∈ coprimeToModulus K 𝔣,
      (⟨J, hJ⟩ : ↥(coprimeToModulus K 𝔣)) ∈ Subgroup.closure {c : ↥(coprimeToModulus K 𝔣) |
        ∃ (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ 𝔣), c = ⟨primeUnit K v, primeUnit_mem_coprimeToModulus K hv⟩} := by
    intro J hJ
    refine Subgroup.closure_induction (p := fun J (_ : J ∈ Subgroup.closure (primeGens K 𝔣)) =>
      ∀ hJ : J ∈ coprimeToModulus K 𝔣, (⟨J, hJ⟩ : ↥(coprimeToModulus K 𝔣)) ∈ Subgroup.closure _) ?_ ?_ ?_ ?_ hJ
    · rintro _ ⟨v, hv, rfl⟩ hJ
      exact Subgroup.subset_closure ⟨v, hv, rfl⟩
    · intro _
      exact one_mem _
    · intro a b ha hb iha ihb hab
      have hmul : (⟨a * b, hab⟩ : ↥(coprimeToModulus K 𝔣))
          = ⟨a, closure_primeGens_le K 𝔣 ha⟩ * ⟨b, closure_primeGens_le K 𝔣 hb⟩ := rfl
      rw [hmul]
      exact mul_mem (iha _) (ihb _)
    · intro a ha iha hainv
      have hinv : (⟨a⁻¹, hainv⟩ : ↥(coprimeToModulus K 𝔣)) = ⟨a, closure_primeGens_le K 𝔣 ha⟩⁻¹ := rfl
      rw [hinv]
      exact inv_mem (iha _)
  exact key I (coprimeToModulus_le_closure K 𝔣 hI) hI

end Gen

section Uniformizer

variable (K : Type*) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private def unifAt : v.adicCompletion K := ((v.valuation_exists_uniformizer K).choose : K)

private theorem valued_unifAt : Valued.v (unifAt K v) = exp (-1 : ℤ) := by
  unfold unifAt
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact (v.valuation_exists_uniformizer K).choose_spec

private theorem unifAt_ne_zero : unifAt K v ≠ 0 := fun h => by
  have h1 := valued_unifAt K v
  rw [h, map_zero] at h1
  exact exp_ne_zero h1.symm

private theorem isUnit_mulSingle (x : v.adicCompletion K) (hx : x ≠ 0) [DecidableEq (HeightOneSpectrum (𝓞 K))] :
    IsUnit (show FiniteAdeleRing (𝓞 K) K from
      RestrictedProduct.mulSingle (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletionIntegers K) v x) := by
  rw [FiniteAdeleRing.isUnit_iff]
  refine ⟨fun w => ?_, ?_⟩
  · show Pi.mulSingle (M := fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K) v x w ≠ 0
    by_cases h : w = v
    · subst h; rw [Pi.mulSingle_eq_same]; exact hx
    · rw [Pi.mulSingle_eq_of_ne h]; exact one_ne_zero
  · filter_upwards [show ({v}ᶜ : Set (HeightOneSpectrum (𝓞 K))) ∈ Filter.cofinite by simp] with w hw
    show Valued.v (Pi.mulSingle (M := fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K) v x w) = 1
    rw [Pi.mulSingle_eq_of_ne (by simpa using hw), map_one]

open scoped Classical in

private def uniformizerFad : (FiniteAdeleRing (𝓞 K) K)ˣ :=
  (isUnit_mulSingle K v (unifAt K v) (unifAt_ne_zero K v)).unit

open scoped Classical in
private theorem uniformizerFad_apply (w : HeightOneSpectrum (𝓞 K)) :
    ((uniformizerFad K v : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) w =
      Pi.mulSingle (M := fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K) v (unifAt K v) w := by
  unfold uniformizerFad
  rw [IsUnit.unit_spec]
  rfl

open scoped Classical in
private theorem uniformizerFad_apply_self :
    ((uniformizerFad K v : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v = unifAt K v := by
  rw [uniformizerFad_apply, Pi.mulSingle_eq_same]

open scoped Classical in
private theorem uniformizerFad_apply_of_ne {w : HeightOneSpectrum (𝓞 K)} (hw : w ≠ v) :
    ((uniformizerFad K v : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) w = 1 := by
  rw [uniformizerFad_apply, Pi.mulSingle_eq_of_ne hw]

private def uniformizerIdele : (AdeleRing (𝓞 K) K)ˣ where
  val := (1, (uniformizerFad K v : FiniteAdeleRing (𝓞 K) K))
  inv := (1, ((uniformizerFad K v)⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ))
  val_inv := Prod.ext (one_mul 1) (uniformizerFad K v).mul_inv
  inv_val := Prod.ext (one_mul 1) (uniformizerFad K v).inv_mul

private theorem uniformizerIdele_fst : ((uniformizerIdele K v : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 = 1 := rfl

private theorem uniformizerIdele_snd :
    ((uniformizerIdele K v : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 = uniformizerFad K v := rfl

private theorem ideleContentHom_uniformizerIdele (𝔣 : Ideal (𝓞 K)) (hv : ¬ v.asIdeal ∣ 𝔣) :
    ideleContentHom K 𝔣 (uniformizerIdele K v) = primeClass K 𝔣 v hv := by
  refine ideleContentHom_uniformizerIdele_v2 K 𝔣 hv (uniformizerIdele K v) rfl
    (fun w hw => ?_) ?_ (fun w hw𝔣 => ?_)
  · rw [uniformizerIdele_snd, uniformizerFad_apply_of_ne K v hw, map_one]
  · rw [uniformizerIdele_snd, uniformizerFad_apply_self, valued_unifAt]
  · have hwv : w ≠ v := fun h => hv (h ▸ hw𝔣)
    rw [uniformizerIdele_snd, uniformizerFad_apply_of_ne K v hwv, sub_self, map_zero]
    exact zero_le'

end Uniformizer

section Surj

variable (K : Type*) [Field K] [NumberField K]

private theorem ideleContentHom_surjective (𝔣 : Ideal (𝓞 K)) :
    Function.Surjective (ideleContentHom K 𝔣) := by
  intro x
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective _ x
  have hc : c ∈ (⊤ : Subgroup ↥(coprimeToModulus K 𝔣)) := Subgroup.mem_top c
  rw [← closure_primeCarriers_eq_top K 𝔣] at hc
  refine Subgroup.closure_induction
    (p := fun c _ => ∃ u, ideleContentHom K 𝔣 u = QuotientGroup.mk' _ c) ?_ ?_ ?_ ?_ hc
  · rintro _ ⟨w, hw, rfl⟩
    exact ⟨uniformizerIdele K w, ideleContentHom_uniformizerIdele K w 𝔣 hw⟩
  · exact ⟨1, by rw [map_one, map_one]⟩
  · rintro a b _ _ ⟨u, hu⟩ ⟨u', hu'⟩
    exact ⟨u * u', by rw [map_mul, map_mul, hu, hu']⟩
  · rintro a _ ⟨u, hu⟩
    exact ⟨u⁻¹, by rw [map_inv, map_inv, hu]⟩

private theorem range_ideleContentHom (𝔣 : Ideal (𝓞 K)) : (ideleContentHom K 𝔣).range = ⊤ :=
  MonoidHom.range_eq_top.mpr (ideleContentHom_surjective K 𝔣)

end Surj

section Norm

variable (k E : Type*) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]

private abbrev modulusExt (𝔠 : Ideal (𝓞 k)) : Ideal (𝓞 E) := 𝔠.map (algebraMap (𝓞 k) (𝓞 E))

private def fracRelNormUnit : (FractionalIdeal ((𝓞 E)⁰) E)ˣ →* (FractionalIdeal ((𝓞 k)⁰) k)ˣ :=
  raySymbolUnitsHom E (fun w : HeightOneSpectrum (𝓞 E) =>
    primeUnit k (w.under (𝓞 k)) ^ ((w.under (𝓞 k)).asIdeal.inertiaDeg' w.asIdeal))

private theorem fracRelNormUnit_primeUnit (w : HeightOneSpectrum (𝓞 E)) :
    fracRelNormUnit k E (primeUnit E w) = primeUnit k (w.under (𝓞 k)) ^ ((w.under (𝓞 k)).asIdeal.inertiaDeg' w.asIdeal) := by
  show raySymbol E _ ((primeUnit E w : (FractionalIdeal ((𝓞 E)⁰) E)ˣ) : FractionalIdeal ((𝓞 E)⁰) E) = _
  rw [raySymbol_primeUnit]

private theorem relNorm_mem_nzd {I : Ideal (𝓞 E)} (hI : I ∈ (nonZeroDivisors (Ideal (𝓞 E)))) :
    Ideal.relNorm (𝓞 k) I ∈ nonZeroDivisors (Ideal (𝓞 k)) :=
  mem_nonZeroDivisors_of_ne_zero (fun h =>
    (mem_nonZeroDivisors_iff_ne_zero.mp hI) (by
      rw [Submodule.zero_eq_bot] at *; exact Ideal.relNorm_eq_bot_iff.mp h))

private theorem fracRelNormUnit_primeUnit_eq_relNorm (w : HeightOneSpectrum (𝓞 E)) :
    fracRelNormUnit k E (primeUnit E w)
      = FractionalIdeal.mk0 k ⟨Ideal.relNorm (𝓞 k) w.asIdeal, relNorm_mem_nzd k E
          (mem_nonZeroDivisors_of_ne_zero (by rw [Ne, Submodule.zero_eq_bot]; exact w.ne_bot))⟩ := by
  haveI : PerfectField (FractionRing (𝓞 k)) := PerfectField.ofCharZero
  haveI : w.asIdeal.IsMaximal := Ideal.IsPrime.isMaximal w.isPrime w.ne_bot
  haveI : (w.under (𝓞 k)).asIdeal.IsMaximal :=
    Ideal.IsPrime.isMaximal (w.under (𝓞 k)).isPrime (w.under (𝓞 k)).ne_bot
  haveI : w.asIdeal.LiesOver (w.under (𝓞 k)).asIdeal := ⟨rfl⟩
  rw [fracRelNormUnit_primeUnit k E w]
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, primeUnit_val, FractionalIdeal.coe_mk0, ← FractionalIdeal.coeIdeal_pow,
    Ideal.inertiaDeg'_eq_inertiaDeg (w.under (𝓞 k)).asIdeal w.asIdeal]
  exact congrArg _ (Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 k)).asIdeal).symm

private theorem fracRelNormUnit_mk0 (I : (Ideal (𝓞 E))⁰) :
    ((fracRelNormUnit k E (FractionalIdeal.mk0 E I) : (FractionalIdeal ((𝓞 k)⁰) k)ˣ) : FractionalIdeal ((𝓞 k)⁰) k)
      = ((Ideal.relNorm (𝓞 k) (I : Ideal (𝓞 E)) : Ideal (𝓞 k)) : FractionalIdeal ((𝓞 k)⁰) k) := by
  obtain ⟨J, hJ⟩ := I
  have hJ' : J ≠ ⊥ := fun h =>
    (mem_nonZeroDivisors_iff_ne_zero.mp hJ) (h.trans (Submodule.zero_eq_bot (R := 𝓞 E)).symm)
  simp only at *
  induction J using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hJ'
  | h₂ u hu =>
    obtain rfl : u = ⊤ := Ideal.isUnit_iff.mp hu
    rw [show FractionalIdeal.mk0 E (⟨(⊤ : Ideal (𝓞 E)), hJ⟩ : (Ideal (𝓞 E))⁰) = 1 from
        Units.ext (by rw [FractionalIdeal.coe_mk0, Units.val_one, FractionalIdeal.coeIdeal_top]),
      map_one, Units.val_one, ← Ideal.one_eq_top, map_one, Ideal.one_eq_top, FractionalIdeal.coeIdeal_top]
  | h₃ a p ha hp ih =>
    have ha' : a ≠ ⊥ := fun h => ha (h.trans (Submodule.zero_eq_bot (R := 𝓞 E)).symm)
    have hp_nz : p ∈ nonZeroDivisors (Ideal (𝓞 E)) :=
      mem_nonZeroDivisors_of_ne_zero (fun h => hp.ne_zero (h.trans (Submodule.zero_eq_bot (R := 𝓞 E)).symm))
    have ha_nz : a ∈ nonZeroDivisors (Ideal (𝓞 E)) := mem_nonZeroDivisors_of_ne_zero ha
    let w : HeightOneSpectrum (𝓞 E) := ⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩
    have hpw : (FractionalIdeal.mk0 E ⟨p, hp_nz⟩ : (FractionalIdeal ((𝓞 E)⁰) E)ˣ) = primeUnit E w := by
      unfold primeUnit; exact congrArg (FractionalIdeal.mk0 E) (Subtype.ext rfl)
    rw [show (⟨p * a, hJ⟩ : (Ideal (𝓞 E))⁰) = ⟨p, hp_nz⟩ * ⟨a, ha_nz⟩ from rfl,
      map_mul, map_mul (fracRelNormUnit k E), Units.val_mul, hpw,
      fracRelNormUnit_primeUnit_eq_relNorm k E w, FractionalIdeal.coe_mk0,
      ih ha_nz ha', map_mul (Ideal.relNorm (𝓞 k)), FractionalIdeal.coeIdeal_mul]

private theorem intNorm_ne_zero {α : 𝓞 E} (hα : α ≠ 0) : Algebra.intNorm (𝓞 k) (𝓞 E) α ≠ 0 := by
  intro h
  have : Ideal.relNorm (𝓞 k) (Ideal.span {α}) = (⊥ : Ideal (𝓞 k)) := by
    rw [Ideal.relNorm_singleton, h, Ideal.span_singleton_eq_bot]
  exact hα (Ideal.span_singleton_eq_bot.mp (Ideal.relNorm_eq_bot_iff.mp this))

private theorem fracRelNormUnit_principalUnit (α : 𝓞 E) (hα : α ≠ 0) :
    fracRelNormUnit k E (principalUnit E α hα) = principalUnit k (Algebra.intNorm (𝓞 k) (𝓞 E) α) (intNorm_ne_zero k E hα) := by
  apply Units.ext
  rw [show principalUnit E α hα = FractionalIdeal.mk0 E ⟨Ideal.span {α}, _⟩ from rfl, fracRelNormUnit_mk0 k E,
    Ideal.relNorm_singleton, principalUnit_val]

private theorem fracRelNormUnit_mem_coprimeToModulus {𝔠 : Ideal (𝓞 k)} {Y : (FractionalIdeal ((𝓞 E)⁰) E)ˣ}
    (hY : Y ∈ coprimeToModulus E (modulusExt k E 𝔠)) : fracRelNormUnit k E Y ∈ coprimeToModulus k 𝔠 := by

  have hY' := coprimeToModulus_le_closure E (modulusExt k E 𝔠) hY
  refine Subgroup.closure_induction (p := fun J (_ : J ∈ Subgroup.closure (primeGens E (modulusExt k E 𝔠))) =>
    fracRelNormUnit k E J ∈ coprimeToModulus k 𝔠) ?_ ?_ ?_ ?_ hY'
  rotate_left
  · simp only [map_one]
    exact one_mem _
  · intro _ _ _ _ ha hb
    simp only [map_mul]
    exact mul_mem ha hb
  · intro _ _ ha
    simp only [map_inv]
    exact inv_mem ha
  rintro _ ⟨w, hw, rfl⟩
  show fracRelNormUnit k E (primeUnit E w) ∈ coprimeToModulus k 𝔠
  rw [fracRelNormUnit_primeUnit]
  refine pow_mem (primeUnit_mem_coprimeToModulus k fun h => hw ?_) _

  rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap]
  exact Ideal.dvd_iff_le.mp h

private def relNormCTM (𝔠 : Ideal (𝓞 k)) : ↥(coprimeToModulus E (modulusExt k E 𝔠)) →* ↥(coprimeToModulus k 𝔠) :=
  ((fracRelNormUnit k E).comp (coprimeToModulus E (modulusExt k E 𝔠)).subtype).codRestrict
    (coprimeToModulus k 𝔠) (fun Y => fracRelNormUnit_mem_coprimeToModulus k E Y.2)

private theorem coe_relNormCTM {𝔠 : Ideal (𝓞 k)} (Y : ↥(coprimeToModulus E (modulusExt k E 𝔠))) :
    ((relNormCTM k E 𝔠 Y : ↥(coprimeToModulus k 𝔠)) : (FractionalIdeal ((𝓞 k)⁰) k)ˣ)
      = fracRelNormUnit k E (Y : (FractionalIdeal ((𝓞 E)⁰) E)ˣ) := rfl

private theorem relNormCTM_primeUnit {𝔠 : Ideal (𝓞 k)} {w : HeightOneSpectrum (𝓞 E)} (hw : ¬ w.asIdeal ∣ modulusExt k E 𝔠) :
    ((relNormCTM k E 𝔠 ⟨primeUnit E w, primeUnit_mem_coprimeToModulus E hw⟩ : ↥(coprimeToModulus k 𝔠)) :
        (FractionalIdeal ((𝓞 k)⁰) k)ˣ)
      = primeUnit k (w.under (𝓞 k)) ^ ((w.under (𝓞 k)).asIdeal.inertiaDeg' w.asIdeal) :=
  fracRelNormUnit_primeUnit k E w

private theorem relNormCTM_principalUnit {𝔠 : Ideal (𝓞 k)} {α : 𝓞 E} (hα : α ≠ 0)
    (hαcop : principalUnit E α hα ∈ coprimeToModulus E (modulusExt k E 𝔠)) :
    ((relNormCTM k E 𝔠 ⟨principalUnit E α hα, hαcop⟩ : ↥(coprimeToModulus k 𝔠)) : (FractionalIdeal ((𝓞 k)⁰) k)ˣ)
      = principalUnit k (Algebra.intNorm (𝓞 k) (𝓞 E) α) (intNorm_ne_zero k E hα) :=
  fracRelNormUnit_principalUnit k E α hα

private theorem range_relNormCTM (𝔠 : Ideal (𝓞 k)) :
    (relNormCTM k E 𝔠).range = ((coprimeToModulus E (modulusExt k E 𝔠)).map (fracRelNormUnit k E)).subgroupOf
      (coprimeToModulus k 𝔠) := by
  ext X
  constructor
  · rintro ⟨Y, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr ⟨Y, Y.2, rfl⟩
  · intro hX
    obtain ⟨Y, hY, hYX⟩ := Subgroup.mem_subgroupOf.mp hX
    exact ⟨⟨Y, hY⟩, Subtype.ext hYX⟩

private def _root_.M4aKummer.normRaySubgroup (𝔠 : Ideal (𝓞 k)) : Subgroup ↥(coprimeToModulus k 𝔠) :=
  (narrowRaySubgroup k 𝔠).subgroupOf (coprimeToModulus k 𝔠) ⊔ (relNormCTM k E 𝔠).range

p2m_export "M4aKummer" "normRaySubgroup"
private theorem normRaySubgroup_eq_frozen (𝔣 : Ideal (𝓞 k)) :
    normRaySubgroup k E 𝔣 =
      (narrowRaySubgroup k 𝔣).subgroupOf (coprimeToModulus k 𝔣) ⊔
        ((coprimeToModulus E (𝔣.map (algebraMap (𝓞 k) (𝓞 E)))).map
          (raySymbolUnitsHom E (fun w : HeightOneSpectrum (𝓞 E) =>
            primeUnit k (w.under (𝓞 k)) ^ ((w.under (𝓞 k)).asIdeal.inertiaDeg' w.asIdeal)))).subgroupOf
          (coprimeToModulus k 𝔣) := by
  rw [normRaySubgroup, range_relNormCTM]
  rfl

end Norm

end M4aKummer

end

end Fold_M4aKummer_ServedNorm

section Fold_M4aKummer_ContentGlue

set_option autoImplicit false

p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.HeckeCharacter"
open scoped nonZeroDivisors

namespace M4aKummer

variable (k E : Type*) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]

private theorem normRaySubgroup_index_eq_map_mk (𝔣 : Ideal (𝓞 k)) :
    (normRaySubgroup k E 𝔣).index
      = ((normRaySubgroup k E 𝔣).map (NarrowRayClassGroup.mk k 𝔣)).index := by
  refine (Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective _) ?_).symm
  show (QuotientGroup.mk' _).ker ≤ normRaySubgroup k E 𝔣
  rw [QuotientGroup.ker_mk']
  exact le_sup_left

private theorem normRaySubgroup_index_dvd_of_idele (𝔣 : Ideal (𝓞 k))
    (H : Subgroup (AdeleRing (𝓞 k) k)ˣ)
    (hContent : H.map (ideleContentHom k 𝔣)
      ≤ (normRaySubgroup k E 𝔣).map (NarrowRayClassGroup.mk k 𝔣)) :
    (normRaySubgroup k E 𝔣).index ∣ H.index := by
  calc (normRaySubgroup k E 𝔣).index
      = ((normRaySubgroup k E 𝔣).map (NarrowRayClassGroup.mk k 𝔣)).index :=
        normRaySubgroup_index_eq_map_mk k E 𝔣
    _ ∣ (H.map (ideleContentHom k 𝔣)).index := Subgroup.index_dvd_of_le hContent
    _ ∣ H.index := Subgroup.index_map_dvd _ (ideleContentHom_surjective k 𝔣)

private theorem map_principalIdeles_le_normRaySubgroup_map_mk (𝔣 : Ideal (𝓞 k)) :
    ((Units.map (algebraMap k (AdeleRing (𝓞 k) k)).toMonoidHom).range.map (ideleContentHom k 𝔣))
      ≤ (normRaySubgroup k E 𝔣).map (NarrowRayClassGroup.mk k 𝔣) := by
  rintro _ ⟨_, ⟨α, rfl⟩, rfl⟩
  exact (ideleContentHom_principal k 𝔣 α) ▸ one_mem _

end M4aKummer

end Fold_M4aKummer_ContentGlue

section Fold_M4aKummer_ResidueDegTwo

set_option autoImplicit false

noncomputable section

p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum"

attribute [local instance] Ideal.Quotient.field

namespace M4aKummer

variable (k E : Type*) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]
variable (v : HeightOneSpectrum (𝓞 k)) (w : HeightOneSpectrum (𝓞 E))

private def resMap (hwv : w.asIdeal.under (𝓞 k) = v.asIdeal) :
    𝓞 k ⧸ v.asIdeal →+* 𝓞 E ⧸ w.asIdeal :=
  Ideal.quotientMap w.asIdeal (algebraMap (𝓞 k) (𝓞 E)) hwv.ge

omit [NumberField k] [NumberField E] in
private theorem resMap_mk (hwv : w.asIdeal.under (𝓞 k) = v.asIdeal) (x : 𝓞 k) :
    resMap k E v w hwv (Ideal.Quotient.mk v.asIdeal x) =
      Ideal.Quotient.mk w.asIdeal (algebraMap (𝓞 k) (𝓞 E) x) :=
  Ideal.quotientMap_mk

private theorem card_residue_pow (hwv : w.asIdeal.under (𝓞 k) = v.asIdeal) :
    Nat.card (𝓞 E ⧸ w.asIdeal) =
      Nat.card (𝓞 k ⧸ v.asIdeal) ^ v.asIdeal.inertiaDeg' w.asIdeal := by
  haveI := v.isMaximal
  haveI := w.isMaximal
  haveI : w.asIdeal.LiesOver v.asIdeal := ⟨hwv.symm⟩
  haveI : Finite (𝓞 E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  rw [Ideal.inertiaDeg_algebraMap, Module.natCard_eq_pow_finrank (K := 𝓞 k ⧸ v.asIdeal)]

private theorem isSquare_resMap_of_inertiaDeg_two (hwv : w.asIdeal.under (𝓞 k) = v.asIdeal)
    (hf : v.asIdeal.inertiaDeg' w.asIdeal = 2)
    (h2 : ringChar (𝓞 k ⧸ v.asIdeal) ≠ 2) (x : 𝓞 k ⧸ v.asIdeal) :
    IsSquare (resMap k E v w hwv x) := by
  haveI := v.isMaximal
  haveI := w.isMaximal
  haveI : Finite (𝓞 k ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  haveI : Finite (𝓞 E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  haveI : Fintype (𝓞 k ⧸ v.asIdeal) := Fintype.ofFinite _
  haveI : Fintype (𝓞 E ⧸ w.asIdeal) := Fintype.ofFinite _
  rcases eq_or_ne x 0 with rfl | hx
  · exact ⟨0, by rw [map_zero, mul_zero]⟩
  have hinj : Function.Injective (resMap k E v w hwv) := (resMap k E v w hwv).injective

  haveI hcF : CharP (𝓞 k ⧸ v.asIdeal) (ringChar (𝓞 k ⧸ v.asIdeal)) := ringChar.charP _
  haveI hcG : CharP (𝓞 E ⧸ w.asIdeal) (ringChar (𝓞 k ⧸ v.asIdeal)) :=
    charP_of_injective_ringHom hinj _
  have h2G : ringChar (𝓞 E ⧸ w.asIdeal) ≠ 2 := by
    rw [CharP.eq (𝓞 E ⧸ w.asIdeal) (ringChar.charP _) hcG]
    exact h2

  have hcard : Fintype.card (𝓞 E ⧸ w.asIdeal) = Fintype.card (𝓞 k ⧸ v.asIdeal) ^ 2 := by
    have h := card_residue_pow k E v w hwv
    rwa [hf, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h
  have hq : Fintype.card (𝓞 k ⧸ v.asIdeal) % 2 = 1 := FiniteField.odd_card_of_char_ne_two h2

  rw [FiniteField.isSquare_iff h2G (fun h0 => hx (hinj (by rw [h0, map_zero])))]
  set q := Fintype.card (𝓞 k ⧸ v.asIdeal) with hqdef
  obtain ⟨m, hm⟩ : ∃ m, q = 2 * m + 1 := ⟨q / 2, by omega⟩
  have e1 : (q + 1) / 2 = m + 1 := by omega
  have e2 : q - 1 = 2 * m := by omega
  have e3 : q ^ 2 = 2 * (2 * m * (m + 1)) + 1 := by rw [hm]; ring
  have hexp : Fintype.card (𝓞 E ⧸ w.asIdeal) / 2 = (q - 1) * ((q + 1) / 2) := by
    rw [hcard, e3, e2, e1]
    generalize 2 * m * (m + 1) = X
    omega
  rw [hexp, pow_mul, ← map_pow, FiniteField.pow_card_sub_one_eq_one x hx, map_one, one_pow]

private theorem isSquare_resMap_iff_of_inertiaDeg_one (hwv : w.asIdeal.under (𝓞 k) = v.asIdeal)
    (hf : v.asIdeal.inertiaDeg' w.asIdeal = 1) (x : 𝓞 k ⧸ v.asIdeal) :
    IsSquare (resMap k E v w hwv x) ↔ IsSquare x := by
  haveI := v.isMaximal
  haveI := w.isMaximal
  haveI : Finite (𝓞 k ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  haveI : Finite (𝓞 E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  haveI : Fintype (𝓞 k ⧸ v.asIdeal) := Fintype.ofFinite _
  haveI : Fintype (𝓞 E ⧸ w.asIdeal) := Fintype.ofFinite _
  have hcard : Fintype.card (𝓞 E ⧸ w.asIdeal) = Fintype.card (𝓞 k ⧸ v.asIdeal) := by
    have h := card_residue_pow k E v w hwv
    rwa [hf, pow_one, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h
  have hbij : Function.Bijective (resMap k E v w hwv) :=
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨(resMap k E v w hwv).injective, hcard.symm⟩
  constructor
  · rintro ⟨r, hr⟩
    obtain ⟨s, rfl⟩ := hbij.surjective r
    exact ⟨s, hbij.injective (by rw [hr, map_mul])⟩
  · rintro ⟨r, rfl⟩
    exact ⟨resMap k E v w hwv r, by rw [map_mul]⟩

private theorem inertiaDeg_eq_one_or_two (hwv : w.asIdeal.under (𝓞 k) = v.asIdeal)
    (hdeg : Module.finrank k E = 2) :
    v.asIdeal.inertiaDeg' w.asIdeal = 1 ∨ v.asIdeal.inertiaDeg' w.asIdeal = 2 := by
  haveI := v.isMaximal
  haveI := w.isMaximal
  haveI : w.asIdeal.LiesOver v.asIdeal := ⟨hwv.symm⟩
  haveI : Module.Finite (𝓞 k) (𝓞 E) :=
    Module.Finite.of_restrictScalars_finite ℤ (𝓞 k) (𝓞 E)
  haveI : NoZeroSMulDivisors (𝓞 k) (𝓞 E) := by
    refine ⟨fun {c x} h => ?_⟩
    rw [Algebra.smul_def] at h
    rcases mul_eq_zero.mp h with h1 | h2
    · exact Or.inl (FaithfulSMul.algebraMap_injective (𝓞 k) (𝓞 E) (by rw [h1, map_zero]))
    · exact Or.inr h2
  have hpos : 0 < v.asIdeal.inertiaDeg' w.asIdeal := Ideal.inertiaDeg'_pos _ _
  have hle : v.asIdeal.inertiaDeg' w.asIdeal ≤ Module.finrank k E :=
    Ideal.inertiaDeg_le_finrank (S := 𝓞 E) (K := k) (L := E) (P := w.asIdeal) v.ne_bot
  rw [hdeg] at hle
  omega

end M4aKummer

end

end Fold_M4aKummer_ResidueDegTwo

section Fold_M4aLocalCFT_SquareClassLocal

set_option autoImplicit false

p2m_open "IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.NumberField IsLocalRing"

namespace M4aLocalCFT
namespace SquareClassLocal

section FiniteField

private theorem index_range_sq_eq_two {F : Type*} [Field F] [Finite F] (h2 : (2 : F) ≠ 0) :
    ((powMonoidHom 2 : Fˣ →* Fˣ).range).index = 2 := by
  have hker : Nat.card (powMonoidHom 2 : Fˣ →* Fˣ).ker = 2 := by
    rw [Nat.card_eq_two_iff]
    refine ⟨⟨1, (powMonoidHom 2 : Fˣ →* Fˣ).ker.one_mem⟩,
      ⟨-1, by rw [MonoidHom.mem_ker, powMonoidHom_apply, neg_one_sq]⟩, ?_, ?_⟩
    · intro h
      have h' : ((1 : Fˣ) : F) = ((-1 : Fˣ) : F) :=
        congrArg (fun u : (powMonoidHom 2 : Fˣ →* Fˣ).ker => ((u : Fˣ) : F)) h
      rw [Units.val_one, Units.val_neg, Units.val_one] at h'
      apply h2
      linear_combination h'
    · ext u
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      have hu : ((u : Fˣ) : F) ^ 2 = 1 := by
        have h := u.2
        rw [MonoidHom.mem_ker, powMonoidHom_apply] at h
        have h' := congrArg (fun w : Fˣ => (w : F)) h
        simpa using h'
      rcases sq_eq_one_iff.mp hu with h | h
      · exact Or.inl (Subtype.ext (Units.ext h))
      · exact Or.inr (Subtype.ext (Units.ext (by simpa using h)))
  have h1 := Subgroup.card_mul_index (powMonoidHom 2 : Fˣ →* Fˣ).range
  have h3 := Subgroup.card_mul_index (powMonoidHom 2 : Fˣ →* Fˣ).ker
  rw [Subgroup.index_ker, hker] at h3
  have hpos : 0 < Nat.card (powMonoidHom 2 : Fˣ →* Fˣ).range := Nat.card_pos
  have h4 : Nat.card (powMonoidHom 2 : Fˣ →* Fˣ).range * ((powMonoidHom 2 : Fˣ →* Fˣ).range).index =
      Nat.card (powMonoidHom 2 : Fˣ →* Fˣ).range * 2 := by
    rw [h1, ← h3]; ring
  exact Nat.eq_of_mul_eq_mul_left hpos h4

example : ((powMonoidHom 2 : (ZMod 3)ˣ →* (ZMod 3)ˣ).range).index = 2 :=
  index_range_sq_eq_two (by decide)

end FiniteField

section Local

variable {K : Type*} [Field K] [NumberField K]
variable (v : HeightOneSpectrum (𝓞 K))

local notation "Kᵥ" => HeightOneSpectrum.adicCompletion K v
local notation "𝒪ᵥ" => HeightOneSpectrum.adicCompletionIntegers K v

private noncomputable def unitsIncl : (𝒪ᵥ)ˣ →* (Kᵥ)ˣ :=
  Units.map ((HeightOneSpectrum.adicCompletionIntegers K v).subtype : 𝒪ᵥ →+* Kᵥ).toMonoidHom

private theorem coe_unitsIncl (u : (𝒪ᵥ)ˣ) : ((unitsIncl v u : (Kᵥ)ˣ) : Kᵥ) = ((u : 𝒪ᵥ) : Kᵥ) := rfl

private theorem unitsIncl_injective : Function.Injective (unitsIncl v) := by
  intro a b h
  apply Units.ext
  apply Subtype.ext
  exact congrArg (fun x : (Kᵥ)ˣ => (x : Kᵥ)) h

private theorem valued_unitsIncl (u : (𝒪ᵥ)ˣ) : Valued.v ((unitsIncl v u : (Kᵥ)ˣ) : Kᵥ) = 1 :=
  adicCompletionIntegers.isUnit_iff_valued_eq_one.mp u.isUnit

private theorem mem_range_unitsIncl_iff (x : (Kᵥ)ˣ) :
    x ∈ (unitsIncl v).range ↔ Valued.v (x : Kᵥ) = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    exact valued_unitsIncl v u
  · intro hx
    have hxO : (x : Kᵥ) ∈ HeightOneSpectrum.adicCompletionIntegers K v := by
      rw [mem_adicCompletionIntegers]; exact hx.le
    have hxO' : ((x⁻¹ : (Kᵥ)ˣ) : Kᵥ) ∈ HeightOneSpectrum.adicCompletionIntegers K v := by
      rw [mem_adicCompletionIntegers, Units.val_inv_eq_inv_val, map_inv₀, hx, inv_one]
    refine ⟨⟨⟨x, hxO⟩, ⟨(x⁻¹ : (Kᵥ)ˣ), hxO'⟩, Subtype.ext x.mul_inv, Subtype.ext x.inv_mul⟩, ?_⟩
    exact Units.ext rfl

private noncomputable abbrev sqRange : Subgroup (Kᵥ)ˣ := (powMonoidHom 2 : (Kᵥ)ˣ →* (Kᵥ)ˣ).range

private noncomputable abbrev unitsRange : Subgroup (Kᵥ)ˣ := (unitsIncl v).range

private noncomputable def ordHom : (Kᵥ)ˣ →* Multiplicative ℤ where
  toFun x := Multiplicative.ofAdd (WithZero.log (Valued.v (x : Kᵥ)))
  map_one' := by simp
  map_mul' x y := by
    rw [← ofAdd_add, Units.val_mul, map_mul,
      WithZero.log_mul ((Valuation.ne_zero_iff _).mpr x.ne_zero)
        ((Valuation.ne_zero_iff _).mpr y.ne_zero)]

private theorem ordHom_apply (x : (Kᵥ)ˣ) :
    ordHom v x = Multiplicative.ofAdd (WithZero.log (Valued.v (x : Kᵥ))) :=
  rfl

private noncomputable def parityHom : (Kᵥ)ˣ →* Multiplicative (ZMod 2) :=
  (AddMonoidHom.toMultiplicative (Int.castAddHom (ZMod 2))).comp (ordHom v)

private theorem parityHom_apply (x : (Kᵥ)ˣ) :
    parityHom v x = Multiplicative.ofAdd (((WithZero.log (Valued.v (x : Kᵥ)) : ℤ) : ZMod 2)) :=
  rfl

private theorem parityHom_eq_one_iff (x : (Kᵥ)ˣ) :
    parityHom v x = 1 ↔ (2 : ℤ) ∣ WithZero.log (Valued.v (x : Kᵥ)) := by
  simp only [parityHom_apply, ofAdd_eq_one, ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_ofNat]

private theorem parityHom_sq (x : (Kᵥ)ˣ) : parityHom v (x ^ 2) = 1 := by
  rw [map_pow, parityHom_apply, ← ofAdd_nsmul, two_nsmul, CharTwo.add_self_eq_zero, ofAdd_zero]

private theorem parityHom_unitsIncl (u : (𝒪ᵥ)ˣ) : parityHom v (unitsIncl v u) = 1 := by
  rw [parityHom_apply, valued_unitsIncl, WithZero.log_one, Int.cast_zero, ofAdd_zero]

private theorem exists_valued_eq_exp_one : ∃ g : (Kᵥ)ˣ, Valued.v (g : Kᵥ) = WithZero.exp (1 : ℤ) := by
  obtain ⟨t, ht⟩ := valuedAdicCompletion_surjective K v (WithZero.exp (1 : ℤ))
  have ht0 : t ≠ 0 := by
    intro h
    rw [h, map_zero] at ht
    exact WithZero.exp_ne_zero ht.symm
  exact ⟨Units.mk0 t ht0, by rw [Units.val_mk0, ht]⟩

private theorem parityHom_surjective : Function.Surjective (parityHom v) := by
  obtain ⟨g, hg⟩ := exists_valued_eq_exp_one v
  intro c
  refine ⟨g ^ (Multiplicative.toAdd c).val, ?_⟩
  rw [map_pow, parityHom_apply, hg, WithZero.log_exp, Int.cast_one, ← ofAdd_nsmul, nsmul_eq_mul,
    mul_one, ZMod.natCast_zmod_val, ofAdd_toAdd]

private theorem ker_parityHom : (parityHom v).ker = sqRange v ⊔ unitsRange v := by
  refine le_antisymm (fun x hx => ?_) (sup_le ?_ ?_)
  · rw [MonoidHom.mem_ker, parityHom_eq_one_iff] at hx
    obtain ⟨m, hm⟩ := hx
    obtain ⟨g, hg⟩ := exists_valued_eq_exp_one v
    rw [Subgroup.mem_sup]
    refine ⟨(g ^ m) ^ 2, ⟨g ^ m, rfl⟩, ((g ^ m) ^ 2)⁻¹ * x, ?_, mul_inv_cancel_left _ _⟩
    rw [mem_range_unitsIncl_iff]
    have hz0 : Valued.v ((((g ^ m) ^ 2)⁻¹ * x : (Kᵥ)ˣ) : Kᵥ) ≠ 0 :=
      (Valuation.ne_zero_iff _).mpr (Units.ne_zero _)
    rw [← WithZero.exp_log hz0, ← WithZero.exp_zero]
    congr 1
    rw [Units.val_mul, map_mul,
      WithZero.log_mul ((Valuation.ne_zero_iff _).mpr (Units.ne_zero _))
        ((Valuation.ne_zero_iff _).mpr (Units.ne_zero _)),
      Units.val_inv_eq_inv_val, map_inv₀, WithZero.log_inv, Units.val_pow_eq_pow_val, map_pow,
      WithZero.log_pow, Units.val_zpow_eq_zpow_val, map_zpow₀, WithZero.log_zpow, hg,
      WithZero.log_exp, hm]
    simp only [smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, mul_one]
    ring
  · rintro _ ⟨y, rfl⟩
    rw [MonoidHom.mem_ker]
    exact parityHom_sq v y
  · rintro _ ⟨u, rfl⟩
    rw [MonoidHom.mem_ker]
    exact parityHom_unitsIncl v u

private theorem index_sup_eq_two : (sqRange v ⊔ unitsRange v).index = 2 := by
  rw [← ker_parityHom, Subgroup.index_ker,
    MonoidHom.range_eq_top_of_surjective _ (parityHom_surjective v), Subgroup.card_top]
  exact (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod 2)

private theorem index_sqRange : (sqRange v).index = 2 * ((sqRange v).comap (unitsIncl v)).index := by
  have h1 := Subgroup.relIndex_mul_index (H := sqRange v) (K := sqRange v ⊔ unitsRange v) le_sup_left
  have h2 : (sqRange v).relIndex (sqRange v ⊔ unitsRange v) = (sqRange v).relIndex (unitsRange v) :=
    Subgroup.relIndex_sup_left (unitsRange v) (sqRange v)
  have h3 : ((sqRange v).comap (unitsIncl v)).index = (sqRange v).relIndex (unitsRange v) := by
    rw [← Subgroup.relIndex_top_right, Subgroup.relIndex_comap, ← MonoidHom.range_eq_map]
  rw [index_sup_eq_two, h2, ← h3] at h1
  omega

private theorem card_mod_sq_eq_two_mul :
    Nat.card ((Kᵥ)ˣ ⧸ sqRange v) = 2 * ((sqRange v).comap (unitsIncl v)).index := by
  rw [← Subgroup.index_eq_card, index_sqRange]

private theorem residueUnits_surjective :
    Function.Surjective (Units.map (IsLocalRing.residue 𝒪ᵥ).toMonoidHom) := by
  intro z
  obtain ⟨x, hx⟩ := IsLocalRing.residue_surjective (z : ResidueField 𝒪ᵥ)
  have hxU : IsUnit x :=
    (IsLocalRing.residue_ne_zero_iff_isUnit x).mp (by rw [hx]; exact z.ne_zero)
  exact ⟨hxU.unit, Units.ext (by simp [hx])⟩

private theorem comap_sqRange_eq_range_sq :
    (sqRange v).comap (unitsIncl v) = (powMonoidHom 2 : (𝒪ᵥ)ˣ →* (𝒪ᵥ)ˣ).range := by
  ext x
  simp only [Subgroup.mem_comap, MonoidHom.mem_range, powMonoidHom_apply]
  constructor
  · rintro ⟨y, hy⟩
    have hvy : Valued.v (y : Kᵥ) = 1 := by
      have h := valued_unitsIncl v x
      rw [← hy, Units.val_pow_eq_pow_val, map_pow] at h
      have hy0 : Valued.v (y : Kᵥ) ≠ 0 := (Valuation.ne_zero_iff _).mpr y.ne_zero
      have hl : WithZero.log (Valued.v (y : Kᵥ) ^ 2) = 0 := by rw [h, WithZero.log_one]
      rw [WithZero.log_pow, nsmul_eq_mul] at hl
      push_cast at hl
      have hl' : WithZero.log (Valued.v (y : Kᵥ)) = 0 := by omega
      rw [← WithZero.exp_log hy0, hl', WithZero.exp_zero]
    obtain ⟨y', rfl⟩ := (mem_range_unitsIncl_iff v y).mpr hvy
    exact ⟨y', unitsIncl_injective v (by rw [map_pow]; exact hy)⟩
  · rintro ⟨y', rfl⟩
    exact ⟨unitsIncl v y', by rw [map_pow]⟩

private theorem index_comap_sqRange_eq_index_range_sq :
    ((sqRange v).comap (unitsIncl v)).index = ((powMonoidHom 2 : (𝒪ᵥ)ˣ →* (𝒪ᵥ)ˣ).range).index := by
  rw [comap_sqRange_eq_range_sq]

private theorem comap_sqRange_eq (h2 : IsUnit (2 : 𝒪ᵥ)) :
    (sqRange v).comap (unitsIncl v) =
      ((powMonoidHom 2 : (ResidueField 𝒪ᵥ)ˣ →* (ResidueField 𝒪ᵥ)ˣ).range).comap
        (Units.map (IsLocalRing.residue 𝒪ᵥ).toMonoidHom) := by
  ext x
  simp only [Subgroup.mem_comap, MonoidHom.mem_range, powMonoidHom_apply]
  constructor
  · rintro ⟨y, hy⟩

    have hvy : Valued.v (y : Kᵥ) = 1 := by
      have h := valued_unitsIncl v x
      rw [← hy, Units.val_pow_eq_pow_val, map_pow] at h
      have hy0 : Valued.v (y : Kᵥ) ≠ 0 := (Valuation.ne_zero_iff _).mpr y.ne_zero
      have hl : WithZero.log (Valued.v (y : Kᵥ) ^ 2) = 0 := by rw [h, WithZero.log_one]
      rw [WithZero.log_pow, nsmul_eq_mul] at hl
      push_cast at hl
      have hl' : WithZero.log (Valued.v (y : Kᵥ)) = 0 := by omega
      rw [← WithZero.exp_log hy0, hl', WithZero.exp_zero]
    obtain ⟨y', rfl⟩ := (mem_range_unitsIncl_iff v y).mpr hvy
    have hx : y' ^ 2 = x := unitsIncl_injective v (by rw [map_pow]; exact hy)
    refine ⟨Units.map (IsLocalRing.residue 𝒪ᵥ).toMonoidHom y', ?_⟩
    rw [← map_pow, hx]
  · rintro ⟨z, hz⟩
    obtain ⟨w, rfl⟩ := residueUnits_surjective v z

    have hker : Units.map (IsLocalRing.residue 𝒪ᵥ).toMonoidHom (x * (w ^ 2)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_pow, hz, mul_inv_cancel]
    have hres : IsLocalRing.residue 𝒪ᵥ ((x * (w ^ 2)⁻¹ : (𝒪ᵥ)ˣ) : 𝒪ᵥ) = 1 := by
      simpa using congrArg (fun u : (ResidueField 𝒪ᵥ)ˣ => (u : ResidueField 𝒪ᵥ)) hker
    have hmem : ((x * (w ^ 2)⁻¹ : (𝒪ᵥ)ˣ) : 𝒪ᵥ) - 1 ∈ maximalIdeal 𝒪ᵥ := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_one, hres, sub_self]

    obtain ⟨a, ha, -⟩ :=
      exists_nthRoot_of_sub_one_mem_maximalIdeal hmem (n := 2) (by exact_mod_cast h2)
    have haU : IsUnit a := by
      rw [← isUnit_pow_iff two_ne_zero, ha]
      exact Units.isUnit _
    refine ⟨unitsIncl v (haU.unit * w), ?_⟩
    rw [← map_pow]
    congr 1
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mul, IsUnit.unit_spec, mul_pow, ha,
      ← Units.val_pow_eq_pow_val, ← Units.val_mul, inv_mul_cancel_right]

private theorem two_ne_zero_residueField (h2 : IsUnit (2 : 𝒪ᵥ)) : (2 : ResidueField 𝒪ᵥ) ≠ 0 := by
  rw [← map_ofNat (IsLocalRing.residue 𝒪ᵥ) 2]
  exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr h2

private theorem index_comap_sqRange_of_isUnit_two (h2 : IsUnit (2 : 𝒪ᵥ)) :
    ((sqRange v).comap (unitsIncl v)).index = 2 := by
  rw [comap_sqRange_eq v h2, Subgroup.index_comap_of_surjective _ (residueUnits_surjective v)]
  exact index_range_sq_eq_two (two_ne_zero_residueField v h2)

private theorem card_quot_two_eq_one (h2 : IsUnit (2 : 𝒪ᵥ)) :
    Nat.card (𝒪ᵥ ⧸ Ideal.span ({(2 : 𝒪ᵥ)} : Set 𝒪ᵥ)) = 1 := by
  haveI : Subsingleton (𝒪ᵥ ⧸ Ideal.span ({(2 : 𝒪ᵥ)} : Set 𝒪ᵥ)) :=
    Ideal.Quotient.subsingleton_iff.mpr (Ideal.span_singleton_eq_top.mpr h2)
  exact Nat.card_unique

private theorem card_units_mod_sq_of_isUnit_two (h2 : IsUnit (2 : v.adicCompletionIntegers K)) :
    Nat.card ((v.adicCompletion K)ˣ ⧸
      (MonoidHom.range (powMonoidHom 2 : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ))) =
    4 * Nat.card ((v.adicCompletionIntegers K) ⧸
      Ideal.span ({(2 : v.adicCompletionIntegers K)} : Set (v.adicCompletionIntegers K))) ∧
    Nat.card ((v.adicCompletion K)ˣ ⧸
      (MonoidHom.range (powMonoidHom 2 : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ)))
      ≠ 0 := by
  have h : Nat.card ((Kᵥ)ˣ ⧸ sqRange v) = 4 := by
    rw [card_mod_sq_eq_two_mul, index_comap_sqRange_of_isUnit_two v h2]
  have h' : Nat.card ((v.adicCompletion K)ˣ ⧸
      (MonoidHom.range (powMonoidHom 2 : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ))) = 4 := h
  refine ⟨?_, ?_⟩
  · rw [card_quot_two_eq_one v h2, mul_one]
    exact h'
  · rw [h']
    norm_num

private theorem isUnit_two_of_notMem (hv : (2 : 𝓞 K) ∉ v.asIdeal) : IsUnit (2 : 𝒪ᵥ) := by
  rw [adicCompletionIntegers.isUnit_iff_valued_eq_one]
  have e1 : ((2 : 𝒪ᵥ) : Kᵥ) = algebraMap K Kᵥ (algebraMap (𝓞 K) K 2) := by
    rw [map_ofNat, map_ofNat]
    exact map_ofNat (HeightOneSpectrum.adicCompletionIntegers K v).subtype 2
  have e2 : Valued.v (algebraMap K Kᵥ (algebraMap (𝓞 K) K 2)) =
      v.valuation K (algebraMap (𝓞 K) K 2) :=
    valuedAdicCompletion_eq_valuation' v _
  rw [show (2 : 𝒪ᵥ).1 = ((2 : 𝒪ᵥ) : Kᵥ) from rfl, e1, e2]
  exact (valuation_eq_one_iff_notMem (K := K) (v := v)).mpr hv

private theorem card_units_mod_sq_of_notMem (hv : (2 : 𝓞 K) ∉ v.asIdeal) :
    Nat.card ((v.adicCompletion K)ˣ ⧸
      (MonoidHom.range (powMonoidHom 2 : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ))) =
    4 * Nat.card ((v.adicCompletionIntegers K) ⧸
      Ideal.span ({(2 : v.adicCompletionIntegers K)} : Set (v.adicCompletionIntegers K))) ∧
    Nat.card ((v.adicCompletion K)ˣ ⧸
      (MonoidHom.range (powMonoidHom 2 : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ)))
      ≠ 0 :=
  card_units_mod_sq_of_isUnit_two v (isUnit_two_of_notMem v hv)

private theorem card_units_mod_sq_of_unitIndex
    (hU : ((sqRange v).comap (unitsIncl v)).index =
      2 * Nat.card (𝒪ᵥ ⧸ Ideal.span ({(2 : 𝒪ᵥ)} : Set 𝒪ᵥ)))
    (hN : Nat.card (𝒪ᵥ ⧸ Ideal.span ({(2 : 𝒪ᵥ)} : Set 𝒪ᵥ)) ≠ 0) :
    Nat.card ((v.adicCompletion K)ˣ ⧸
      (MonoidHom.range (powMonoidHom 2 : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ))) =
    4 * Nat.card ((v.adicCompletionIntegers K) ⧸
      Ideal.span ({(2 : v.adicCompletionIntegers K)} : Set (v.adicCompletionIntegers K))) ∧
    Nat.card ((v.adicCompletion K)ˣ ⧸
      (MonoidHom.range (powMonoidHom 2 : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ)))
      ≠ 0 := by
  have h : Nat.card ((Kᵥ)ˣ ⧸ sqRange v) =
      4 * Nat.card (𝒪ᵥ ⧸ Ideal.span ({(2 : 𝒪ᵥ)} : Set 𝒪ᵥ)) := by
    rw [card_mod_sq_eq_two_mul, hU]
    ring
  have h' : Nat.card ((v.adicCompletion K)ˣ ⧸
      (MonoidHom.range (powMonoidHom 2 : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ))) =
      4 * Nat.card (𝒪ᵥ ⧸ Ideal.span ({(2 : 𝒪ᵥ)} : Set 𝒪ᵥ)) := h
  refine ⟨h', ?_⟩
  rw [h']
  exact mul_ne_zero four_ne_zero hN

end Local

end SquareClassLocal
end M4aLocalCFT

end Fold_M4aLocalCFT_SquareClassLocal

section Fold_M4aTheta_ArtinCount

set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "P2.Artin.normRaySubgroup P2.Artin.SecondInequalityCTM P2.Artin.IdeleFirstIneqDataAt P2.Artin.artinFrob"
namespace P2
p2m_export "LanglandsTunnell.P2" "Artin.normRaySubgroup Artin.SecondInequalityCTM Artin.IdeleFirstIneqDataAt Artin.artinFrob"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
namespace Count
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

variable {A T : Type*} [Group A] [Group T]

private theorem ker_eq_and_surjective_of_le_of_index_eq_card [Finite T] (φ : A →* T) {N : Subgroup A}
    (hker : φ.ker ≤ N) (hidx : N.index = Nat.card T) :
    φ.ker = N ∧ Function.Surjective φ := by
  have hTpos : 0 < Nat.card T := Nat.card_pos
  have hkidx : φ.ker.index = Nat.card φ.range := Subgroup.index_ker φ
  have hle : Nat.card φ.range ≤ Nat.card T :=
    Nat.card_le_card_of_injective _ φ.range.subtype_injective
  have hmul := Subgroup.relIndex_mul_index hker
  rw [hkidx, hidx] at hmul

  have hrpos : 0 < Nat.card φ.range := Nat.card_pos
  have hrel1 : φ.ker.relIndex N = 1 := by
    have h1 : φ.ker.relIndex N * Nat.card T ≤ 1 * Nat.card T := by rw [one_mul, hmul]; exact hle
    have h2 : 1 ≤ φ.ker.relIndex N := by
      rcases Nat.eq_zero_or_pos (φ.ker.relIndex N) with h | h
      · rw [h, zero_mul] at hmul; omega
      · exact h
    exact le_antisymm (Nat.le_of_mul_le_mul_right h1 hTpos) h2
  have hkerN : φ.ker = N := le_antisymm hker (Subgroup.relIndex_eq_one.mp hrel1)
  refine ⟨hkerN, ?_⟩

  have hcard : Nat.card φ.range = Nat.card T := by
    rw [← hkidx, hkerN, hidx]
  have : φ.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by simpa using hcard)
  exact MonoidHom.range_eq_top.mp this

private theorem ker_eq_of_le_of_index_eq_card [Finite T] (φ : A →* T) {N : Subgroup A}
    (hker : φ.ker ≤ N) (hidx : N.index = Nat.card T) : φ.ker = N :=
  (ker_eq_and_surjective_of_le_of_index_eq_card φ hker hidx).1

private theorem surjective_of_le_of_index_eq_card [Finite T] (φ : A →* T) {N : Subgroup A}
    (hker : φ.ker ≤ N) (hidx : N.index = Nat.card T) : Function.Surjective φ :=
  (ker_eq_and_surjective_of_le_of_index_eq_card φ hker hidx).2

private theorem apply_eq_one_of_mem [Finite T] (φ : A →* T) {N : Subgroup A}
    (hker : φ.ker ≤ N) (hidx : N.index = Nat.card T) {x : A} (hx : x ∈ N) : φ x = 1 := by
  have h := ker_eq_of_le_of_index_eq_card φ hker hidx
  rw [← MonoidHom.mem_ker, h]
  exact hx

private theorem le_ker_of_le_of_index_eq_card [Finite T] (φ : A →* T) {N P : Subgroup A}
    (hker : φ.ker ≤ N) (hidx : N.index = Nat.card T) (hP : P ≤ N) : P ≤ φ.ker := by
  rw [ker_eq_of_le_of_index_eq_card φ hker hidx]
  exact hP

end LanglandsTunnell.P2.Artin.Count

end Fold_M4aTheta_ArtinCount

section Fold_M4aTheta_ArtinCrossing

set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "P2.Artin.normRaySubgroup P2.Artin.SecondInequalityCTM P2.Artin.IdeleFirstIneqDataAt P2.Artin.artinFrob"
namespace P2
p2m_export "LanglandsTunnell.P2" "Artin.normRaySubgroup Artin.SecondInequalityCTM Artin.IdeleFirstIneqDataAt Artin.artinFrob"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

variable {I : Type*} [CommGroup I] (𝔑 : Subgroup I) {G : Type*} [Group G] (ω : I →* G) (σ : G)

section Transfer

variable {Ip : Type*} [CommGroup Ip] (N : Ip →* I) (ωp : Ip →* G)

private def transferClass (b : Ip) : I ⧸ 𝔑 := ((N b : I) : I ⧸ 𝔑)

variable {𝔑 N ωp σ}

private theorem transferClass_indep (hker : ∀ x, ωp x = 1 → N x ∈ 𝔑) {b b' : Ip} (hb : ωp b = σ) (hb' : ωp b' = σ) :
    transferClass 𝔑 N b = transferClass 𝔑 N b' := by
  unfold transferClass
  rw [QuotientGroup.eq, ← map_inv, ← map_mul]
  exact hker _ (by rw [map_mul, map_inv, hb, hb', inv_mul_cancel])

private theorem transferClass_pow_orderOf (hker : ∀ x, ωp x = 1 → N x ∈ 𝔑) {b : Ip} (hb : ωp b = σ) :
    transferClass 𝔑 N b ^ orderOf σ = 1 := by
  unfold transferClass
  rw [← QuotientGroup.mk_pow, ← map_pow, QuotientGroup.eq_one_iff]
  exact hker _ (by rw [map_pow, hb, pow_orderOf_eq_one])

private theorem coe_eq_transferClass_zpow (hker : ∀ x, ωp x = 1 → N x ∈ 𝔑) {b : Ip} (hb : ωp b = σ) {P : Ip} {p : I} (hNP : N P = p)
    {d : ℤ} (hd : ωp P = σ ^ d) : ((p : I) : I ⧸ 𝔑) = transferClass 𝔑 N b ^ d := by
  unfold transferClass
  rw [← hNP, ← QuotientGroup.mk_zpow, ← map_zpow, QuotientGroup.eq, ← map_inv, ← map_mul]
  exact hker _ (by rw [map_mul, map_inv, map_zpow, hb, hd, inv_mul_cancel])

private theorem apply_eq_zpow_of_transfer (hcompat : ∀ x, ω (N x) = ωp x) {P : Ip} {p : I} (hNP : N P = p) {d : ℤ} (hd : ωp P = σ ^ d) :
    ω p = σ ^ d := by
  rw [← hNP, hcompat, hd]

end Transfer

section Crossing

variable {Ip Iq Ipq : Type*} [CommGroup Ip] [CommGroup Iq] [CommGroup Ipq]
variable {N : Ip →* I} {ωp : Ip →* G} {N' : Iq →* I} {ωq : Iq →* G}
variable {𝔑 σ}

private theorem transferClass_eq_of_common_norm (hkerp : ∀ x, ωp x = 1 → N x ∈ 𝔑) (hkerq : ∀ x, ωq x = 1 → N' x ∈ 𝔑)
    {bp : Ip} {bq : Iq} (hN : N bp = N' bq) (hbp : ωp bp = σ) (hbq : ωq bq = σ)
    {b : Ip} (hb : ωp b = σ) {b' : Iq} (hb' : ωq b' = σ) : transferClass 𝔑 N b = transferClass 𝔑 N' b' := by
  rw [transferClass_indep hkerp hb hbp, transferClass_indep hkerq hb' hbq]
  unfold transferClass
  rw [hN]

variable {Np : Ipq →* Ip} {Nq : Ipq →* Iq} {ωpq : Ipq →* G}

private theorem transferClass_eq_of_crossing (hkerp : ∀ x, ωp x = 1 → N x ∈ 𝔑) (hkerq : ∀ x, ωq x = 1 → N' x ∈ 𝔑)
    (hNN : ∀ x, N (Np x) = N' (Nq x)) (hωp : ∀ x, ωp (Np x) = ωpq x) (hωq : ∀ x, ωq (Nq x) = ωpq x)
    {B : Ipq} (hB : ωpq B = σ) {b : Ip} (hb : ωp b = σ) {b' : Iq} (hb' : ωq b' = σ) :
    transferClass 𝔑 N b = transferClass 𝔑 N' b' :=
  transferClass_eq_of_common_norm hkerp hkerq (hNN B) (by rw [hωp, hB]) (by rw [hωq, hB]) hb hb'

end Crossing

private theorem exists_zpow_of_mem_closure (c : I ⧸ 𝔑) (S : Set I)
    (hS : ∀ p ∈ S, ∃ d : ℤ, ω p = σ ^ d ∧ ((p : I) : I ⧸ 𝔑) = c ^ d) {x : I} (hx : x ∈ Subgroup.closure S) :
    ∃ e : ℤ, ω x = σ ^ e ∧ ((x : I) : I ⧸ 𝔑) = c ^ e := by
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact hS y hy
  | one => exact ⟨0, by rw [map_one, zpow_zero], by rw [QuotientGroup.mk_one, zpow_zero]⟩
  | mul y z _ _ ihy ihz =>
    obtain ⟨e, he, he'⟩ := ihy
    obtain ⟨f, hf, hf'⟩ := ihz
    exact ⟨e + f, by rw [map_mul, he, hf, zpow_add], by rw [QuotientGroup.mk_mul, he', hf', zpow_add]⟩
  | inv y _ ihy =>
    obtain ⟨e, he, he'⟩ := ihy
    exact ⟨-e, by rw [map_inv, he, zpow_neg], by rw [QuotientGroup.mk_inv, he', zpow_neg]⟩

private theorem mem_of_ker_of_classes (c : I ⧸ 𝔑) (hc : c ^ orderOf σ = 1) (S : Set I)
    (hS : ∀ p ∈ S, ∃ d : ℤ, ω p = σ ^ d ∧ ((p : I) : I ⧸ 𝔑) = c ^ d) {x : I} (hx : x ∈ Subgroup.closure S) (hω : ω x = 1) :
    x ∈ 𝔑 := by
  obtain ⟨e, he, he'⟩ := exists_zpow_of_mem_closure 𝔑 ω σ c S hS hx

  have hdvd : (orderOf σ : ℤ) ∣ e := orderOf_dvd_iff_zpow_eq_one.mpr (by rw [← he, hω])
  have hce : c ^ e = 1 := by
    obtain ⟨t, rfl⟩ := hdvd
    rw [zpow_mul, zpow_natCast, hc, one_zpow]
  rw [← QuotientGroup.eq_one_iff, he', hce]

private theorem ker_inf_closure_le (c : I ⧸ 𝔑) (hc : c ^ orderOf σ = 1) (S : Set I)
    (hS : ∀ p ∈ S, ∃ d : ℤ, ω p = σ ^ d ∧ ((p : I) : I ⧸ 𝔑) = c ^ d) : ω.ker ⊓ Subgroup.closure S ≤ 𝔑 :=
  fun _ hx => mem_of_ker_of_classes 𝔑 ω σ c hc S hS hx.2 (MonoidHom.mem_ker.mp hx.1)

private theorem ker_inf_closure_le_of_transfer {Ip : Type*} [CommGroup Ip] (S : Set I)
    (N : I → (Ip →* I)) (ωp : I → (Ip →* G)) (P : I → Ip) (d : I → ℤ)
    (hcompat : ∀ p ∈ S, ∀ x, ω (N p x) = ωp p x) (hker : ∀ p ∈ S, ∀ x, ωp p x = 1 → N p x ∈ 𝔑)
    (hNP : ∀ p ∈ S, N p (P p) = p) (hd : ∀ p ∈ S, ωp p (P p) = σ ^ d p)
    (hcross : ∀ p ∈ S, ∀ q ∈ S, ∃ bp bq : Ip, N p bp = N q bq ∧ ωp p bp = σ) :
    ω.ker ⊓ Subgroup.closure S ≤ 𝔑 := by
  by_cases hS : S.Nonempty
  · obtain ⟨p₀, hp₀⟩ := hS
    obtain ⟨b₀, -, -, hb₀⟩ := hcross p₀ hp₀ p₀ hp₀
    refine ker_inf_closure_le 𝔑 ω σ (transferClass 𝔑 (N p₀) b₀) (transferClass_pow_orderOf (hker p₀ hp₀) hb₀) S ?_
    intro p hp
    obtain ⟨bp, bq, hN, hbp⟩ := hcross p₀ hp₀ p hp

    have hbq : ωp p bq = σ := by rw [← hcompat p hp, ← hN, hcompat p₀ hp₀, hbp]
    refine ⟨d p, apply_eq_zpow_of_transfer ω (hcompat p hp) (hNP p hp) (hd p hp), ?_⟩
    rw [transferClass_eq_of_common_norm (hker p₀ hp₀) (hker p hp) hN hbp hbq hb₀ hbq]
    exact coe_eq_transferClass_zpow (hker p hp) hbq (hNP p hp) (hd p hp)
  · rw [Set.not_nonempty_iff_eq_empty.mp hS, Subgroup.closure_empty, inf_bot_eq]
    exact bot_le

end LanglandsTunnell.P2.Artin

end Fold_M4aTheta_ArtinCrossing

section Fold_M4aTheta_ArtinFrob

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "P2.Artin.normRaySubgroup P2.Artin.SecondInequalityCTM P2.Artin.IdeleFirstIneqDataAt P2.Artin.artinFrob"
namespace P2
p2m_export "LanglandsTunnell.P2" "Artin.normRaySubgroup Artin.SecondInequalityCTM Artin.IdeleFirstIneqDataAt Artin.artinFrob"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.NumberField IsDedekindDomain"
open scoped Pointwise

section Transport

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {G : Type*} [Group G] [MulSemiringAction G S] [SMulCommClass G R S]

private theorem inertia_smul_eq_bot (τ : G) (Q : Ideal S) (hI : Q.inertia G = ⊥) : (τ • Q).inertia G = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  have hg' : ∀ x : S, g • x - x ∈ τ • Q := fun x => hg x
  have hmem : τ⁻¹ * g * τ ∈ Q.inertia G := by
    intro x
    have hx := Ideal.mem_pointwise_smul_iff_inv_smul_mem.1 (hg' (τ • x))
    rw [smul_sub, inv_smul_smul, ← mul_smul, ← mul_smul] at hx
    exact hx
  rw [hI, Subgroup.mem_bot] at hmem
  have hgg : g = τ * (τ⁻¹ * g * τ) * τ⁻¹ := by group
  rw [hmem] at hgg
  simpa using hgg

private theorem eq_of_isArithFrobAt_of_inertia_eq_bot {σ σ' : G} {Q : Ideal S} (H : IsArithFrobAt R σ Q) (H' : IsArithFrobAt R σ' Q)
    (hI : Q.inertia G = ⊥) : σ = σ' := by
  have h := H.mul_inv_mem_inertia H'
  rw [hI, Subgroup.mem_bot] at h
  exact mul_inv_eq_one.1 h

private theorem pow_smul_sub_pow_mem {σ : G} {Q : Ideal S} [Q.IsPrime] (H : IsArithFrobAt R σ Q) (k : ℕ) (x : S) :
    σ ^ k • x - x ^ (Nat.card (R ⧸ Q.under R) ^ k) ∈ Q := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    have hσQ : ∀ y ∈ Q, σ • y ∈ Q := fun y hy => by
      have hstab := H.mem_stabilizer
      rw [MulAction.mem_stabilizer_iff] at hstab
      have h := Ideal.smul_mem_pointwise_smul σ y Q hy
      rwa [hstab] at h
    have h1 : σ ^ (k + 1) • x - σ • x ^ (Nat.card (R ⧸ Q.under R) ^ k) ∈ Q := by
      rw [pow_succ', mul_smul, ← smul_sub]
      exact hσQ _ (ih x)
    have h2 : σ • x ^ (Nat.card (R ⧸ Q.under R) ^ k) - x ^ (Nat.card (R ⧸ Q.under R) ^ (k + 1)) ∈ Q := by
      rw [smul_pow', pow_succ', pow_mul]
      exact Ideal.mem_of_dvd _ (sub_dvd_pow_sub_pow _ _ _) (H x)
    have h := Q.add_mem h1 h2
    rwa [sub_add_sub_cancel] at h

private theorem smul_pow_zero_sub_mem {σ : G} {Q : Ideal S} [Q.IsPrime] (H : IsArithFrobAt R σ Q) (x : S) :
    σ ^ 0 • x - x ^ (Nat.card (R ⧸ Q.under R) ^ 0) ∈ Q :=
  pow_smul_sub_pow_mem H 0 x

variable [Finite G] [Algebra.IsInvariant R S G]

private theorem arithFrobAt_smul (τ : G) (Q : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)] [Finite (S ⧸ τ • Q)] (hI : Q.inertia G = ⊥) :
    arithFrobAt R G (τ • Q) = τ * arithFrobAt R G Q * τ⁻¹ := by
  have h1 : IsArithFrobAt R (arithFrobAt R G (τ • Q)) (τ • Q) := IsArithFrobAt.arithFrobAt R G (τ • Q)
  have h2 : IsArithFrobAt R (τ * arithFrobAt R G Q * τ⁻¹) (τ • Q) := (IsArithFrobAt.arithFrobAt R G Q).conj τ
  have h3 := h1.mul_inv_mem_inertia h2
  rw [inertia_smul_eq_bot τ Q hI, Subgroup.mem_bot] at h3
  exact mul_inv_eq_one.1 h3

end Transport

section Artin

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
  (v : HeightOneSpectrum (𝓞 K))

private theorem arithFrobAt_eq_artinFrob [IsMulCommutative (M ≃ₐ[K] M)] (Q : Ideal (𝓞 M)) [Q.IsPrime] [Finite (𝓞 M ⧸ Q)]
    (hQ : Q.under (𝓞 K) = v.asIdeal) (hI : Q.inertia (M ≃ₐ[K] M) = ⊥) :
    arithFrobAt (𝓞 K) (M ≃ₐ[K] M) Q = artinFrob K M v := by
  haveI : Q.LiesOver v.asIdeal := ⟨hQ.symm⟩
  haveI := v.isMaximal
  obtain ⟨τ, hτ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup v.asIdeal (primeAbove K M v) Q (M ≃ₐ[K] M)
  subst hτ
  have hI₀ : (primeAbove K M v).inertia (M ≃ₐ[K] M) = ⊥ := by
    have h := inertia_smul_eq_bot τ⁻¹ (τ • primeAbove K M v) hI
    rwa [inv_smul_smul] at h
  rw [arithFrobAt_smul τ (primeAbove K M v) hI₀, IsMulCommutative.is_comm.comm τ, mul_inv_cancel_right]
  rfl

private theorem eq_artinFrob_of_isArithFrobAt [IsMulCommutative (M ≃ₐ[K] M)] {σ : M ≃ₐ[K] M} {Q : Ideal (𝓞 M)} [Q.IsPrime]
    (H : IsArithFrobAt (𝓞 K) σ Q) (hQ : Q.under (𝓞 K) = v.asIdeal) (hI : Q.inertia (M ≃ₐ[K] M) = ⊥) : σ = artinFrob K M v := by
  haveI := finite_quotient_of_under_eq K M v hQ
  rw [← arithFrobAt_eq_artinFrob K M v Q hQ hI]
  exact eq_of_isArithFrobAt_of_inertia_eq_bot H (IsArithFrobAt.arithFrobAt (𝓞 K) (M ≃ₐ[K] M) Q) hI

end Artin

section Restrict

variable (K M M' : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Field M'] [NumberField M']
  [Algebra K M] [Algebra K M'] [Algebra M M'] [IsScalarTower K M M'] [IsGalois K M] [IsGalois K M']

private scoped instance : IsScalarTower (𝓞 K) (𝓞 M) (𝓞 M') :=
  IsScalarTower.of_algebraMap_eq fun x => by
    refine RingOfIntegers.ext ?_
    show algebraMap K M' (x : K) = algebraMap M M' (algebraMap (𝓞 K) (𝓞 M) x : M)
    rw [show (algebraMap (𝓞 K) (𝓞 M) x : M) = algebraMap K M (x : K) from rfl, ← IsScalarTower.algebraMap_apply K M M']

private theorem isArithFrobAt_restrictNormal (τ : M' ≃ₐ[K] M') (Q' : Ideal (𝓞 M')) (H : IsArithFrobAt (𝓞 K) τ Q') :
    IsArithFrobAt (𝓞 K) (AlgEquiv.restrictNormalHom M τ) (Q'.under (𝓞 M)) := by
  intro x
  have hcard : Nat.card (𝓞 K ⧸ (Q'.under (𝓞 M)).under (𝓞 K)) = Nat.card (𝓞 K ⧸ Q'.under (𝓞 K)) := by
    rw [Ideal.under_under]
  have hkey : algebraMap (𝓞 M) (𝓞 M') ((AlgEquiv.restrictNormalHom M τ) • x) = τ • algebraMap (𝓞 M) (𝓞 M') x := by
    refine RingOfIntegers.ext ?_
    show algebraMap M M' ((τ.restrictNormal M) (x : M)) = τ (algebraMap M M' (x : M))
    exact AlgEquiv.restrictNormal_commutes τ M (x : M)
  rw [hcard, Ideal.under_def, Ideal.mem_comap, map_sub, map_pow]
  erw [hkey]
  exact H (algebraMap (𝓞 M) (𝓞 M') x)

private theorem restrictNormal_artinFrob [IsMulCommutative (M ≃ₐ[K] M)] (v : HeightOneSpectrum (𝓞 K))
    (hI : ((primeAbove K M' v).under (𝓞 M)).inertia (M ≃ₐ[K] M) = ⊥) :
    AlgEquiv.restrictNormalHom M (artinFrob K M' v) = artinFrob K M v := by
  have H := isArithFrobAt_restrictNormal K M M' (artinFrob K M' v) (primeAbove K M' v) (isArithFrobAt_artinFrob K M' v)
  haveI : ((primeAbove K M' v).under (𝓞 M)).IsPrime := Ideal.IsPrime.under (𝓞 M) (primeAbove K M' v)
  refine eq_artinFrob_of_isArithFrobAt K M v H ?_ hI
  rw [Ideal.under_under, under_primeAbove]

end Restrict

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell"

end
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin"

end Fold_M4aTheta_ArtinFrob
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin"

section Fold_M4aTheta_ArtinSymbol

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "P2.Artin.normRaySubgroup P2.Artin.SecondInequalityCTM P2.Artin.IdeleFirstIneqDataAt P2.Artin.artinFrob"
namespace P2
p2m_export "LanglandsTunnell.P2" "Artin.normRaySubgroup Artin.SecondInequalityCTM Artin.IdeleFirstIneqDataAt Artin.artinFrob"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.NumberField IsDedekindDomain"

section Symbol

open Deep.NTSupply
open scoped nonZeroDivisors

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
  [IsMulCommutative (M ≃ₐ[K] M)]

open scoped IsMulCommutative

omit [NumberField M] [Algebra K M] [IsGalois K M] [IsMulCommutative (M ≃ₐ[K] M)] in

private theorem map_raySymbol {N N' : Type*} [CommGroup N] [CommGroup N'] (φ : N →* N') (f : HeightOneSpectrum (𝓞 K) → N)
    (I : FractionalIdeal ((𝓞 K)⁰) K) : φ (raySymbol K f I) = raySymbol K (φ ∘ f) I := by
  unfold raySymbol
  rw [φ.map_finprod (hasFiniteMulSupport_raySymbol_factors K f I)]
  simp only [map_zpow, Function.comp_apply]

variable (M' : Type*) [Field M'] [NumberField M'] [Algebra K M'] [Algebra M M'] [IsScalarTower K M M'] [IsGalois K M']
  [IsMulCommutative (M' ≃ₐ[K] M')]

private theorem restrictNormalHom_artinSymbol (𝔣 : Ideal (𝓞 K))
    (hI : ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔣 → ((primeAbove K M' v).under (𝓞 M)).inertia (M ≃ₐ[K] M) = ⊥)
    (I : ↥(coprimeToModulus K 𝔣)) :
    AlgEquiv.restrictNormalHom M (artinSymbol K M' 𝔣 I) = artinSymbol K M 𝔣 I := by
  rw [artinSymbol, artinSymbol, raySymbolHom_apply, raySymbolHom_apply, map_raySymbol]
  unfold raySymbol
  refine finprod_congr fun v => ?_
  by_cases hv : v.asIdeal ∣ 𝔣
  · rw [I.2 v hv, zpow_zero, zpow_zero]
  · rw [Function.comp_apply, restrictNormal_artinFrob K M M' v (hI v hv)]

end Symbol
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin"

end Fold_M4aTheta_ArtinSymbol
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin"

section Fold_M4aTheta_ArtinReciprocity

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "P2.Artin.normRaySubgroup P2.Artin.SecondInequalityCTM P2.Artin.IdeleFirstIneqDataAt P2.Artin.artinFrob"
namespace P2
p2m_export "LanglandsTunnell.P2" "Artin.normRaySubgroup Artin.SecondInequalityCTM Artin.IdeleFirstIneqDataAt Artin.artinFrob"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.NumberField IsDedekindDomain Deep.NTSupply"
open scoped nonZeroDivisors IsMulCommutative

section Carriers

variable (K : Type*) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K))

private theorem primeCarrier_mem (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ 𝔣) :
    primeCarrier K 𝔣 v hv ∈ primeCarriers K 𝔣 :=
  ⟨v, hv, rfl⟩

open Classical in

private def carrierOrOne (v : HeightOneSpectrum (𝓞 K)) : ↥(coprimeToModulus K 𝔣) :=
  if hv : v.asIdeal ∣ 𝔣 then 1 else primeCarrier K 𝔣 v hv

private theorem carrierOrOne_mem_closure (v : HeightOneSpectrum (𝓞 K)) :
    carrierOrOne K 𝔣 v ∈ Subgroup.closure (primeCarriers K 𝔣) := by
  unfold carrierOrOne
  split_ifs with hv
  · exact one_mem _
  · exact Subgroup.subset_closure (primeCarrier_mem K 𝔣 v hv)

open Classical in

private theorem val_carrierOrOne_zpow (v : HeightOneSpectrum (𝓞 K)) (n : ℤ) :
    (((carrierOrOne K 𝔣 v ^ n : ↥(coprimeToModulus K 𝔣)) : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K)
      = if v.asIdeal ∣ 𝔣 then 1 else (v.asIdeal : FractionalIdeal ((𝓞 K)⁰) K) ^ n := by
  rw [SubgroupClass.coe_zpow, Units.val_zpow_eq_zpow_val]
  unfold carrierOrOne
  split_ifs with hv
  · rw [OneMemClass.coe_one, Units.val_one, one_zpow]
  · rw [primeCarrier, primeUnit_val]

private theorem raySymbolHom_carrierOrOne (I : ↥(coprimeToModulus K 𝔣)) : raySymbolHom K 𝔣 (carrierOrOne K 𝔣) I = I := by
  apply Subtype.ext
  apply Units.ext
  rw [raySymbolHom_apply]
  unfold raySymbol
  have hfin := hasFiniteMulSupport_raySymbol_factors K (carrierOrOne K 𝔣)
    ((I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K)

  let φ : ↥(coprimeToModulus K 𝔣) →* FractionalIdeal ((𝓞 K)⁰) K :=
    (Units.coeHom (FractionalIdeal ((𝓞 K)⁰) K)).comp (coprimeToModulus K 𝔣).subtype
  show φ (∏ᶠ v, carrierOrOne K 𝔣 v ^ FractionalIdeal.count K v
      ((I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K)) = φ I
  rw [MonoidHom.map_finprod φ hfin]
  conv_rhs => rw [show φ I = ((I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K) from rfl,
    ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K (Units.ne_zero (I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ))]
  refine finprod_congr fun v => ?_
  rw [show φ (carrierOrOne K 𝔣 v ^ FractionalIdeal.count K v ((I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K))
      = (((carrierOrOne K 𝔣 v ^ FractionalIdeal.count K v ((I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K)
          : ↥(coprimeToModulus K 𝔣)) : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K) from rfl,
    val_carrierOrOne_zpow]
  split_ifs with hv
  · rw [I.2 v hv, zpow_zero]
  · rfl

private theorem _root_.LanglandsTunnell.P2.Artin.closure_primeCarriers_eq_top : Subgroup.closure (primeCarriers K 𝔣) = ⊤ := by
  rw [eq_top_iff]
  intro I _
  rw [← raySymbolHom_carrierOrOne K 𝔣 I, raySymbolHom_apply]
  unfold raySymbol
  exact finprod_induction (· ∈ Subgroup.closure (primeCarriers K 𝔣)) (one_mem _) (fun _ _ => mul_mem)
    fun v => zpow_mem (carrierOrOne_mem_closure K 𝔣 v) _

p2m_export "LanglandsTunnell.P2.Artin" "closure_primeCarriers_eq_top"
end Carriers
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin"

section Assembly

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
  [IsMulCommutative (L ≃ₐ[K] L)]
variable (𝔣 : Ideal (𝓞 K)) (𝔑 : Subgroup ↥(coprimeToModulus K 𝔣)) (σ : L ≃ₐ[K] L)
variable {Ip : Type*} [CommGroup Ip]
  (N : ↥(coprimeToModulus K 𝔣) → (Ip →* ↥(coprimeToModulus K 𝔣))) (ωp : ↥(coprimeToModulus K 𝔣) → (Ip →* (L ≃ₐ[K] L)))
  (P : ↥(coprimeToModulus K 𝔣) → Ip) (d : ↥(coprimeToModulus K 𝔣) → ℤ)

private theorem artinSymbol_ker_eq_and_surjective_of_transfer
    (hcompat : ∀ p ∈ primeCarriers K 𝔣, ∀ x, artinSymbol K L 𝔣 (N p x) = ωp p x)
    (hker : ∀ p ∈ primeCarriers K 𝔣, ∀ x, ωp p x = 1 → N p x ∈ 𝔑)
    (hNP : ∀ p ∈ primeCarriers K 𝔣, N p (P p) = p) (hd : ∀ p ∈ primeCarriers K 𝔣, ωp p (P p) = σ ^ d p)
    (hcross : ∀ p ∈ primeCarriers K 𝔣, ∀ q ∈ primeCarriers K 𝔣, ∃ bp bq : Ip, N p bp = N q bq ∧ ωp p bp = σ)
    (hidx : 𝔑.index = Nat.card (L ≃ₐ[K] L)) :
    (artinSymbol K L 𝔣).ker = 𝔑 ∧ Function.Surjective (artinSymbol K L 𝔣) := by
  refine Count.ker_eq_and_surjective_of_le_of_index_eq_card (artinSymbol K L 𝔣) ?_ hidx
  have h := ker_inf_closure_le_of_transfer 𝔑 (artinSymbol K L 𝔣) σ (primeCarriers K 𝔣) N ωp P d hcompat hker hNP hd hcross
  rwa [closure_primeCarriers_eq_top, inf_top_eq] at h

private theorem raySymbol_artinFrob_eq_one_of_transfer
    (hcompat : ∀ p ∈ primeCarriers K 𝔣, ∀ x, artinSymbol K L 𝔣 (N p x) = ωp p x)
    (hker : ∀ p ∈ primeCarriers K 𝔣, ∀ x, ωp p x = 1 → N p x ∈ 𝔑)
    (hNP : ∀ p ∈ primeCarriers K 𝔣, N p (P p) = p) (hd : ∀ p ∈ primeCarriers K 𝔣, ωp p (P p) = σ ^ d p)
    (hcross : ∀ p ∈ primeCarriers K 𝔣, ∀ q ∈ primeCarriers K 𝔣, ∃ bp bq : Ip, N p bp = N q bq ∧ ωp p bp = σ)
    (hidx : 𝔑.index = Nat.card (L ≃ₐ[K] L))
    (hP : ∀ (α : 𝓞 K) (hα0 : α ≠ 0) (hα1 : α - 1 ∈ 𝔣), (∀ τ : K →+* ℝ, 0 < τ (algebraMap (𝓞 K) K α)) →
      (⟨principalUnit K α hα0, principalUnit_mem_coprimeToModulus K hα0 hα1⟩ : ↥(coprimeToModulus K 𝔣)) ∈ 𝔑)
    {α : 𝓞 K} (hα0 : α ≠ 0) (hα1 : α - 1 ∈ 𝔣) (hpos : ∀ τ : K →+* ℝ, 0 < τ (algebraMap (𝓞 K) K α)) :
    raySymbol K (artinFrob K L) (((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K)) = 1 := by
  obtain ⟨hkerEq, -⟩ :=
    artinSymbol_ker_eq_and_surjective_of_transfer K L 𝔣 𝔑 σ N ωp P d hcompat hker hNP hd hcross hidx
  have hmem : (⟨principalUnit K α hα0, principalUnit_mem_coprimeToModulus K hα0 hα1⟩ : ↥(coprimeToModulus K 𝔣))
      ∈ (artinSymbol K L 𝔣).ker := hkerEq ▸ hP α hα0 hα1 hpos
  rw [MonoidHom.mem_ker, artinSymbol, raySymbolHom_apply] at hmem
  rw [← principalUnit_val K α hα0]
  exact hmem

end Assembly
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin"

end Fold_M4aTheta_ArtinReciprocity
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin"

section Fold_M4aTheta_ArtinNorm

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "P2.Artin.normRaySubgroup P2.Artin.SecondInequalityCTM P2.Artin.IdeleFirstIneqDataAt P2.Artin.artinFrob"
namespace P2
p2m_export "LanglandsTunnell.P2" "Artin.normRaySubgroup Artin.SecondInequalityCTM Artin.IdeleFirstIneqDataAt Artin.artinFrob"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.NumberField IsDedekindDomain"
open scoped Pointwise

section FrobLike

variable {S : Type*} [CommRing S] {G : Type*} [Group G] [MulSemiringAction G S]

private theorem mul_inv_mem_inertia_of_frobLike {σ τ : G} {Q : Ideal S} {q : ℕ}
    (hσ : ∀ x : S, σ • x - x ^ q ∈ Q) (hτ : ∀ x : S, τ • x - x ^ q ∈ Q) : σ * τ⁻¹ ∈ Q.inertia G := by
  intro x
  have h1 := hσ (τ⁻¹ • x)
  have h2 := hτ (τ⁻¹ • x)
  rw [smul_inv_smul] at h2
  have h := Q.sub_mem h1 h2
  rwa [sub_sub_sub_cancel_right, ← mul_smul] at h

private theorem eq_of_frobLike {σ τ : G} {Q : Ideal S} {q : ℕ}
    (hσ : ∀ x : S, σ • x - x ^ q ∈ Q) (hτ : ∀ x : S, τ • x - x ^ q ∈ Q) (hI : Q.inertia G = ⊥) : σ = τ := by
  have h := mul_inv_mem_inertia_of_frobLike hσ hτ
  rw [hI, Subgroup.mem_bot] at h
  exact mul_inv_eq_one.1 h

end FrobLike
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin"

section ResidueTower

attribute [local instance] Ideal.Quotient.field

variable {K E : Type*} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]

private theorem natCard_residue_eq_pow (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 E)) (hwv : w.asIdeal.under (𝓞 K) = v.asIdeal) :
    Nat.card (𝓞 E ⧸ w.asIdeal) = Nat.card (𝓞 K ⧸ v.asIdeal) ^ v.asIdeal.inertiaDeg' w.asIdeal := by
  haveI := v.isMaximal
  haveI := w.isMaximal
  haveI : w.asIdeal.LiesOver v.asIdeal := ⟨hwv.symm⟩
  haveI : Finite (𝓞 E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  rw [Ideal.inertiaDeg_algebraMap]
  exact Module.natCard_eq_pow_finrank

end ResidueTower
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin"

section Norm

variable (K M E N : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Field E] [NumberField E] [Field N] [NumberField N]
  [Algebra K M] [Algebra K E] [Algebra K N] [Algebra M N] [Algebra E N] [IsScalarTower K M N] [IsScalarTower K E N]
  [IsGalois K M] [IsGalois E N]

private theorem restrictNormal_artinFrob_eq_pow [IsMulCommutative (M ≃ₐ[K] M)] (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 E))
    (hwv : w.asIdeal.under (𝓞 K) = v.asIdeal)
    (hI : ((primeAbove E N w).under (𝓞 M)).inertia (M ≃ₐ[K] M) = ⊥) :
    ((artinFrob E N w).restrictScalars K).restrictNormal M = artinFrob K M v ^ v.asIdeal.inertiaDeg' w.asIdeal := by
  haveI : ((primeAbove E N w).under (𝓞 M)).IsPrime := Ideal.IsPrime.under (𝓞 M) (primeAbove E N w)
  have hQMv : ((primeAbove E N w).under (𝓞 M)).under (𝓞 K) = v.asIdeal := by
    rw [Ideal.under_under, ← Ideal.under_under (B := 𝓞 E), under_primeAbove, hwv]
  haveI : Finite (𝓞 M ⧸ (primeAbove E N w).under (𝓞 M)) := finite_quotient_of_under_eq K M v hQMv

  have hw : Nat.card (𝓞 E ⧸ (primeAbove E N w).under (𝓞 E)) = Nat.card (𝓞 E ⧸ w.asIdeal) := by rw [under_primeAbove]
  have hφ : ∀ y : 𝓞 M, (((artinFrob E N w).restrictScalars K).restrictNormal M) • y - y ^ Nat.card (𝓞 E ⧸ w.asIdeal)
      ∈ (primeAbove E N w).under (𝓞 M) := by
    intro y
    have hkey : algebraMap (𝓞 M) (𝓞 N) ((((artinFrob E N w).restrictScalars K).restrictNormal M) • y)
        = (artinFrob E N w) • algebraMap (𝓞 M) (𝓞 N) y := by
      refine RingOfIntegers.ext ?_
      show algebraMap M N ((((artinFrob E N w).restrictScalars K).restrictNormal M) (y : M)) = (artinFrob E N w) (algebraMap M N (y : M))
      exact AlgEquiv.restrictNormal_commutes _ M (y : M)
    rw [Ideal.under_def, Ideal.mem_comap, map_sub, map_pow]
    erw [hkey]
    rw [← hw]
    exact isArithFrobAt_artinFrob E N w (algebraMap (𝓞 M) (𝓞 N) y)

  have hF : IsArithFrobAt (𝓞 K) (arithFrobAt (𝓞 K) (M ≃ₐ[K] M) ((primeAbove E N w).under (𝓞 M))) ((primeAbove E N w).under (𝓞 M)) :=
    IsArithFrobAt.arithFrobAt (𝓞 K) (M ≃ₐ[K] M) _
  have hcard : Nat.card (𝓞 E ⧸ w.asIdeal)
      = Nat.card (𝓞 K ⧸ ((primeAbove E N w).under (𝓞 M)).under (𝓞 K)) ^ v.asIdeal.inertiaDeg' w.asIdeal := by
    rw [hQMv]
    exact natCard_residue_eq_pow v w hwv
  have hFf : ∀ y : 𝓞 M, arithFrobAt (𝓞 K) (M ≃ₐ[K] M) ((primeAbove E N w).under (𝓞 M)) ^ v.asIdeal.inertiaDeg' w.asIdeal • y
      - y ^ Nat.card (𝓞 E ⧸ w.asIdeal) ∈ (primeAbove E N w).under (𝓞 M) := fun y => by
    rw [hcard]
    exact pow_smul_sub_pow_mem hF _ y

  rw [eq_of_frobLike hφ hFf hI, arithFrobAt_eq_artinFrob K M v ((primeAbove E N w).under (𝓞 M)) hQMv hI]

end Norm
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin"

end Fold_M4aTheta_ArtinNorm
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin"

section Fold_M4aTheta_ArtinRelNorm

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "P2.Artin.normRaySubgroup P2.Artin.SecondInequalityCTM P2.Artin.IdeleFirstIneqDataAt P2.Artin.artinFrob"
namespace P2
p2m_export "LanglandsTunnell.P2" "Artin.normRaySubgroup Artin.SecondInequalityCTM Artin.IdeleFirstIneqDataAt Artin.artinFrob"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.NumberField IsDedekindDomain Deep.NTSupply"
open scoped IsMulCommutative nonZeroDivisors

section Finite
variable (K E : Type*) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]

private scoped instance moduleFinite_ringOfIntegers : Module.Finite (𝓞 K) (𝓞 E) :=
  Module.Finite.of_restrictScalars_finite ℤ (𝓞 K) (𝓞 E)

end Finite
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin"

section RaySymbolAux
variable (K : Type*) [Field K] [NumberField K] {G : Type*} [CommGroup G] (f : HeightOneSpectrum (𝓞 K) → G)

private theorem raySymbol_one' : raySymbol K f (1 : FractionalIdeal ((𝓞 K)⁰) K) = 1 := by
  simp [raySymbol, FractionalIdeal.count_one]

private theorem raySymbol_coeIdeal_prime (v : HeightOneSpectrum (𝓞 K)) :
    raySymbol K f (v.asIdeal : FractionalIdeal ((𝓞 K)⁰) K) = f v := by
  rw [← primeUnit_val, raySymbol_primeUnit]

private theorem raySymbol_coeIdeal_pow (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (n : ℕ) :
    raySymbol K f ((I ^ n : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) = raySymbol K f (I : FractionalIdeal ((𝓞 K)⁰) K) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, Ideal.one_eq_top, FractionalIdeal.coeIdeal_top, raySymbol_one']
  | succ n ih =>
    rw [pow_succ, pow_succ, FractionalIdeal.coeIdeal_mul, raySymbol_mul K f ?_ ?_, ih]
    · exact FractionalIdeal.coeIdeal_ne_zero.mpr (pow_ne_zero n hI)
    · exact FractionalIdeal.coeIdeal_ne_zero.mpr hI

end RaySymbolAux
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin"

section Tower

variable (K M E N : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Field E] [NumberField E] [Field N] [NumberField N]
  [Algebra K M] [Algebra K E] [Algebra K N] [Algebra M N] [Algebra E N] [IsScalarTower K M N] [IsScalarTower K E N]
  [IsGalois K M] [IsGalois E N]

omit [NumberField K] [NumberField M] [NumberField E] [NumberField N] [IsGalois E N] in
private theorem resHom_apply (σ : N ≃ₐ[E] N) : resHom K M E N σ = (σ.restrictScalars K).restrictNormal M := rfl

variable [IsMulCommutative (M ≃ₐ[K] M)]

private theorem resHom_artinFrob (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 E)) (hwv : w.asIdeal.under (𝓞 K) = v.asIdeal)
    (hI : ((primeAbove E N w).under (𝓞 M)).inertia (M ≃ₐ[K] M) = ⊥) :
    resHom K M E N (artinFrob E N w) = artinFrob K M v ^ v.asIdeal.inertiaDeg' w.asIdeal :=
  restrictNormal_artinFrob_eq_pow K M E N v w hwv hI

private def placeUnder (w : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 K) :=
  ⟨w.asIdeal.under (𝓞 K), inferInstance, fun h => w.ne_bot (Ideal.eq_bot_of_comap_eq_bot h)⟩

omit [NumberField K] [NumberField E] [IsGalois K M] [IsMulCommutative (M ≃ₐ[K] M)] in
private theorem placeUnder_asIdeal (w : HeightOneSpectrum (𝓞 E)) : (placeUnder K E w).asIdeal = w.asIdeal.under (𝓞 K) := rfl

variable [IsMulCommutative (N ≃ₐ[E] N)]

private theorem resHom_raySymbol_eq_raySymbol_relNorm (𝔞 : Ideal (𝓞 E)) (h𝔞 : 𝔞 ≠ ⊥)
    (hI : ∀ w : HeightOneSpectrum (𝓞 E), w.asIdeal ∣ 𝔞 → ((primeAbove E N w).under (𝓞 M)).inertia (M ≃ₐ[K] M) = ⊥) :
    resHom K M E N (raySymbol E (artinFrob E N) (𝔞 : FractionalIdeal ((𝓞 E)⁰) E)) =
      raySymbol K (artinFrob K M) ((Ideal.relNorm (𝓞 K) 𝔞 : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) := by
  induction 𝔞 using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact (h𝔞 Submodule.zero_eq_bot).elim
  | h₂ u hu =>
    have h1 : Ideal.relNorm (𝓞 K) (⊤ : Ideal (𝓞 E)) = ⊤ := by rw [← Ideal.one_eq_top, map_one, Ideal.one_eq_top]
    rw [Ideal.isUnit_iff.mp hu, h1, FractionalIdeal.coeIdeal_top, FractionalIdeal.coeIdeal_top, raySymbol_one', raySymbol_one', map_one]
  | h₃ a p ha hp ih =>

    haveI hpP : p.IsPrime := Ideal.isPrime_of_prime hp
    let w : HeightOneSpectrum (𝓞 E) := ⟨p, hpP, hp.ne_zero⟩
    let v : HeightOneSpectrum (𝓞 K) := placeUnder K E w
    haveI := v.isMaximal
    haveI := w.isMaximal
    haveI : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
    have hab : a ≠ ⊥ := ha
    have hIa : ∀ w' : HeightOneSpectrum (𝓞 E), w'.asIdeal ∣ a → ((primeAbove E N w').under (𝓞 M)).inertia (M ≃ₐ[K] M) = ⊥ :=
      fun w' hw' => hI w' (dvd_mul_of_dvd_right hw' p)
    have hIw : ((primeAbove E N w).under (𝓞 M)).inertia (M ≃ₐ[K] M) = ⊥ := hI w (dvd_mul_right p a)

    rw [FractionalIdeal.coeIdeal_mul, raySymbol_mul E (artinFrob E N) (FractionalIdeal.coeIdeal_ne_zero.mpr hp.ne_zero)
      (FractionalIdeal.coeIdeal_ne_zero.mpr hab), map_mul, ih hab hIa,
      show (p : FractionalIdeal ((𝓞 E)⁰) E) = (w.asIdeal : FractionalIdeal ((𝓞 E)⁰) E) from rfl, raySymbol_coeIdeal_prime,
      resHom_artinFrob K M E N v w rfl hIw]

    have hrel : Ideal.relNorm (𝓞 K) p = v.asIdeal ^ v.asIdeal.inertiaDeg' w.asIdeal := by
      show Ideal.relNorm (𝓞 K) w.asIdeal = _
      rw [Ideal.inertiaDeg'_eq_inertiaDeg v.asIdeal w.asIdeal]
      exact Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal v.asIdeal
    have hrel0 : Ideal.relNorm (𝓞 K) a ≠ ⊥ := by
      rw [Ne, Ideal.relNorm_eq_bot_iff]; exact hab
    rw [map_mul, hrel, FractionalIdeal.coeIdeal_mul, raySymbol_mul K (artinFrob K M) ?_ (FractionalIdeal.coeIdeal_ne_zero.mpr hrel0),
      raySymbol_coeIdeal_pow K (artinFrob K M) v.asIdeal v.ne_bot, raySymbol_coeIdeal_prime]
    exact FractionalIdeal.coeIdeal_ne_zero.mpr (pow_ne_zero _ v.ne_bot)

end Tower
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin"

end Fold_M4aTheta_ArtinRelNorm
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin"

section Fold_M4aTheta_ICNNormUnit

noncomputable section

p2m_open "Deep.NTSupply NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.NumberField IsDedekindDomain"
open scoped nonZeroDivisors

namespace HeckeCharacter
p2m_export "HeckeCharacter" "idealMultiplicity placeUnder' placeUnder'_asIdeal modulusExt fracRelNormUnit placeUnder'_dvd_iff gcopNC2 coe_raySymbol_gcop_eq_fracRelNormUnit' fracRelNormUnit_mem_coprimeToModulus relNormCTM fad_one_apply fad_mul_apply placeOrd valued_ne_zero_of_unit placeOrd_eq_zero_iff finite_support_placeOrd fadContentHom projFin placeOf isReal_compOfRealHom isReal_placeOf archRealProjTau archSign archSign_of_fst_eq_one archSign_mul archSign_one archSign_inv unit_cong_mul unit_cong_div fad_units_inv_apply IsAdjuster fadContentHom_projFin_idelicNorm_eq_fracRelNormUnit isAdjuster_idelicNorm_of_isAdjuster"
p2m_open "HeckeCharacter"

variable (k E : Type*) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]

private theorem fracRelNormUnit_primeUnit (w : HeightOneSpectrum (𝓞 E))
    (𝔭 : HeightOneSpectrum (𝓞 k)) (h𝔭w : w.asIdeal.under (𝓞 k) = 𝔭.asIdeal) :
    fracRelNormUnit k E (primeUnit E w)
      = primeUnit k 𝔭 ^ (𝔭.asIdeal.inertiaDeg' w.asIdeal) := by
  have heq : placeUnder' k E w = 𝔭 :=
    IsDedekindDomain.HeightOneSpectrum.ext (by rw [placeUnder'_asIdeal, h𝔭w])
  show raySymbolUnitsHom E _ (primeUnit E w) = _
  rw [show raySymbolUnitsHom E _ (primeUnit E w)
        = raySymbol E _ ((primeUnit E w : (FractionalIdeal ((𝓞 E)⁰) E)ˣ) :
            FractionalIdeal ((𝓞 E)⁰) E) from rfl,
    raySymbol_primeUnit, heq]

private theorem relNorm_mem_nzd {I : Ideal (𝓞 E)} (hI : I ∈ (nonZeroDivisors (Ideal (𝓞 E)))) :
    Ideal.relNorm (𝓞 k) I ∈ nonZeroDivisors (Ideal (𝓞 k)) :=
  mem_nonZeroDivisors_of_ne_zero (fun h =>
    (mem_nonZeroDivisors_iff_ne_zero.mp hI) (by
      rw [Submodule.zero_eq_bot] at *; exact Ideal.relNorm_eq_bot_iff.mp h))

private theorem fracRelNormUnit_primeUnit_eq_relNorm (w : HeightOneSpectrum (𝓞 E)) :
    fracRelNormUnit k E (primeUnit E w)
      = FractionalIdeal.mk0 k ⟨Ideal.relNorm (𝓞 k) w.asIdeal, relNorm_mem_nzd k E
          (mem_nonZeroDivisors_of_ne_zero (by
            rw [Ne, Submodule.zero_eq_bot]; exact w.ne_bot))⟩ := by
  haveI : PerfectField (FractionRing (𝓞 k)) := PerfectField.ofCharZero
  haveI : w.asIdeal.IsMaximal := Ideal.IsPrime.isMaximal w.isPrime w.ne_bot
  haveI : (placeUnder' k E w).asIdeal.IsMaximal :=
    Ideal.IsPrime.isMaximal (placeUnder' k E w).isPrime (placeUnder' k E w).ne_bot
  haveI : w.asIdeal.LiesOver (placeUnder' k E w).asIdeal :=
    ⟨(placeUnder'_asIdeal k E w).symm⟩
  rw [fracRelNormUnit_primeUnit k E w (placeUnder' k E w) (placeUnder'_asIdeal k E w).symm]
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, primeUnit_val, FractionalIdeal.coe_mk0,
    ← FractionalIdeal.coeIdeal_pow, Ideal.inertiaDeg'_eq_inertiaDeg (placeUnder' k E w).asIdeal w.asIdeal]
  exact congrArg _
    (Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (placeUnder' k E w).asIdeal).symm

private theorem fracRelNormUnit_mk0 (I : (Ideal (𝓞 E))⁰) :
    ((fracRelNormUnit k E (FractionalIdeal.mk0 E I) :
        (FractionalIdeal ((𝓞 k)⁰) k)ˣ) : FractionalIdeal ((𝓞 k)⁰) k)
      = ((Ideal.relNorm (𝓞 k) (I : Ideal (𝓞 E)) : Ideal (𝓞 k)) :
          FractionalIdeal ((𝓞 k)⁰) k) := by
  obtain ⟨J, hJ⟩ := I
  have hJ' : J ≠ ⊥ := fun h =>
    (mem_nonZeroDivisors_iff_ne_zero.mp hJ) (h.trans (Submodule.zero_eq_bot (R := 𝓞 E)).symm)
  simp only at *
  induction J using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hJ'
  | h₂ u hu =>
    obtain rfl : u = ⊤ := Ideal.isUnit_iff.mp hu
    rw [show FractionalIdeal.mk0 E (⟨(⊤ : Ideal (𝓞 E)), hJ⟩ : (Ideal (𝓞 E))⁰) = 1 from
        Units.ext (by rw [FractionalIdeal.coe_mk0, Units.val_one, FractionalIdeal.coeIdeal_top]),
      map_one, Units.val_one, ← Ideal.one_eq_top, map_one, Ideal.one_eq_top,
      FractionalIdeal.coeIdeal_top]
  | h₃ a p ha hp ih =>
    have ha' : a ≠ ⊥ := fun h => ha (h.trans (Submodule.zero_eq_bot (R := 𝓞 E)).symm)
    have hp_nz : p ∈ nonZeroDivisors (Ideal (𝓞 E)) :=
      mem_nonZeroDivisors_of_ne_zero
        (fun h => hp.ne_zero (h.trans (Submodule.zero_eq_bot (R := 𝓞 E)).symm))
    have ha_nz : a ∈ nonZeroDivisors (Ideal (𝓞 E)) := mem_nonZeroDivisors_of_ne_zero ha
    let w : HeightOneSpectrum (𝓞 E) := ⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩
    have hpw : (FractionalIdeal.mk0 E ⟨p, hp_nz⟩ : (FractionalIdeal ((𝓞 E)⁰) E)ˣ)
        = primeUnit E w := by
      unfold primeUnit; exact congrArg (FractionalIdeal.mk0 E) (Subtype.ext rfl)
    rw [show (⟨p * a, hJ⟩ : (Ideal (𝓞 E))⁰) = ⟨p, hp_nz⟩ * ⟨a, ha_nz⟩ from rfl,
      map_mul, map_mul (fracRelNormUnit k E), Units.val_mul, hpw,
      fracRelNormUnit_primeUnit_eq_relNorm k E w, FractionalIdeal.coe_mk0,
      ih ha_nz ha', map_mul (Ideal.relNorm (𝓞 k)), FractionalIdeal.coeIdeal_mul]

private theorem fracRelNormUnit_principalUnit (α : 𝓞 E) (hα : α ≠ 0) :
    ((fracRelNormUnit k E (principalUnit E α hα) :
        (FractionalIdeal ((𝓞 k)⁰) k)ˣ) : FractionalIdeal ((𝓞 k)⁰) k)
      = ((Ideal.span {Algebra.intNorm (𝓞 k) (𝓞 E) α} : Ideal (𝓞 k)) :
          FractionalIdeal ((𝓞 k)⁰) k) := by
  rw [show principalUnit E α hα = FractionalIdeal.mk0 E ⟨Ideal.span {α}, _⟩ from rfl,
    fracRelNormUnit_mk0 k E, Ideal.relNorm_singleton]

end HeckeCharacter
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin"

section Battery
p2m_open "HeckeCharacter P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.HeckeCharacter"
end Battery
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin"

end Fold_M4aTheta_ICNNormUnit
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin"

section Fold_M4aTheta_NormClassKill

set_option autoImplicit false

noncomputable section

namespace M4aP2

p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.NumberField nonZeroDivisors IsDedekindDomain Deep.NTSupply"

variable (K : Type*) [Field K] [NumberField K] (q : ℕ)

private theorem norm_int_cast_eq_one_of_sub_one_mem {α : 𝓞 K}
    (hα : α - 1 ∈ Ideal.span {(q : 𝓞 K)}) :
    ((Algebra.norm ℤ α : ℤ) : ZMod q) = 1 := by
  classical
  obtain ⟨γ, hγ⟩ := Ideal.mem_span_singleton'.mp hα
  have hsm : q • γ = γ * (q : 𝓞 K) := by rw [nsmul_eq_mul, mul_comm]
  have hαeq : α = 1 + q • γ := by rw [hsm, hγ]; ring
  let b := RingOfIntegers.basis K
  have h1 : ((Algebra.norm ℤ α : ℤ) : ZMod q)
      = ((Int.castRingHom (ZMod q)).mapMatrix (Algebra.leftMulMatrix b α)).det := by
    rw [Algebra.norm_eq_matrix_det b, ← RingHom.map_det]; rfl
  have h0 : (q • (Int.castRingHom (ZMod q)).mapMatrix (Algebra.leftMulMatrix b γ)
      : Matrix (Module.Free.ChooseBasisIndex ℤ (𝓞 K))
        (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) (ZMod q)) = 0 := by
    ext i j
    simp [Matrix.smul_apply, nsmul_eq_mul]
  rw [h1, hαeq, map_add, map_one, map_nsmul, map_add, map_one, map_nsmul, h0, add_zero,
    Matrix.det_one]

private theorem norm_int_pos_of_totPos {α : 𝓞 K} (h0 : α ≠ 0)
    (hpos : ∀ τ : K →+* ℝ, 0 < τ (algebraMap (𝓞 K) K α)) :
    0 < Algebra.norm ℤ α := by
  classical
  set x : K := algebraMap (𝓞 K) K α with hxdef
  have hx0 : x ≠ 0 := by
    rw [hxdef, map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)]
    exact h0

  have hper : ∀ w : InfinitePlace K, ∃ r : ℝ, 0 < r ∧
      (∏ φ ∈ ({φ | InfinitePlace.mk φ = w} : Finset (K →+* ℂ)), φ x) = (r : ℂ) := by
    intro w
    have hfibset : ({φ | InfinitePlace.mk φ = w} : Finset (K →+* ℂ))
        = {w.embedding, NumberField.ComplexEmbedding.conjugate w.embedding} := by
      ext φ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · intro h
        have h' : InfinitePlace.mk φ = InfinitePlace.mk w.embedding :=
          h.trans (InfinitePlace.mk_embedding w).symm
        rcases InfinitePlace.mk_eq_iff.mp h' with h1 | h2
        · exact Or.inl h1
        · exact Or.inr ((star_star φ).symm.trans (congrArg star h2))
      · rintro (h | h)
        · rw [h, InfinitePlace.mk_embedding]
        · rw [h, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
    by_cases hw : InfinitePlace.IsReal w
    · have hre : NumberField.ComplexEmbedding.conjugate w.embedding = w.embedding :=
        NumberField.ComplexEmbedding.isReal_iff.mp (InfinitePlace.isReal_iff.mp hw)
      refine ⟨(InfinitePlace.embedding_of_isReal hw) x, hpos _, ?_⟩
      rw [hfibset, hre, Finset.insert_eq_self.mpr (Finset.mem_singleton_self _),
        Finset.prod_singleton, InfinitePlace.embedding_of_isReal_apply hw]
    · have hne : w.embedding ≠ NumberField.ComplexEmbedding.conjugate w.embedding := by
        intro h
        exact hw (InfinitePlace.isReal_iff.mpr
          (NumberField.ComplexEmbedding.isReal_iff.mpr h.symm))
      have hval0 : w.embedding x ≠ 0 := by
        rw [← map_zero w.embedding]
        exact fun h => hx0 (w.embedding.injective h)
      refine ⟨Complex.normSq (w.embedding x), Complex.normSq_pos.mpr hval0, ?_⟩
      rw [hfibset, Finset.prod_pair hne,
        NumberField.ComplexEmbedding.conjugate_coe_eq, Complex.mul_conj]
  choose r hrpos hreq using hper

  have htot : algebraMap ℚ ℂ (Algebra.norm ℚ x) = ((∏ w : InfinitePlace K, r w : ℝ) : ℂ) := by
    rw [Algebra.norm_eq_prod_embeddings ℚ ℂ x,
      ← Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun φ : K →+* ℂ => φ x)
        (fun σ : K →ₐ[ℚ] ℂ => σ x)
        (fun φ => by simp [RingHom.equivRatAlgHom_apply]),
      ← Finset.prod_fiberwise Finset.univ InfinitePlace.mk (fun φ : K →+* ℂ => φ x),
      Finset.prod_congr rfl fun w _ => hreq w, ← Complex.ofReal_prod]

  have hofreal : (((Algebra.norm ℚ x : ℚ) : ℝ) : ℂ) = ((∏ w : InfinitePlace K, r w : ℝ) : ℂ) := by
    rw [← htot, eq_ratCast (algebraMap ℚ ℂ) (Algebra.norm ℚ x), Complex.ofReal_ratCast]
  have hQpos : 0 < Algebra.norm ℚ x := by
    have hreal : ((Algebra.norm ℚ x : ℚ) : ℝ) = ∏ w : InfinitePlace K, r w :=
      Complex.ofReal_inj.mp hofreal
    have hP : 0 < ∏ w : InfinitePlace K, r w :=
      Finset.prod_pos fun w _ => hrpos w
    rw [← Rat.cast_pos (K := ℝ), hreal]
    exact hP

  have hcoe : ((Algebra.norm ℤ α : ℤ) : ℚ) = Algebra.norm ℚ x := Algebra.coe_norm_int α
  have : (0 : ℚ) < ((Algebra.norm ℤ α : ℤ) : ℚ) := by rw [hcoe]; exact hQpos
  exact_mod_cast this

private theorem absNorm_coprime_of_not_dvd (v : HeightOneSpectrum (𝓞 K))
    (hv : ¬ v.asIdeal ∣ Ideal.span {(q : 𝓞 K)}) :
    Nat.Coprime (Ideal.absNorm v.asIdeal) q := by
  classical
  haveI hmax : v.asIdeal.IsMaximal := Ideal.IsPrime.isMaximal v.isPrime v.ne_bot
  letI : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  haveI : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  haveI : Fintype (𝓞 K ⧸ v.asIdeal) := Fintype.ofFinite _
  obtain ⟨n, hp, hcard⟩ :=
    FiniteField.card (𝓞 K ⧸ v.asIdeal) (ringChar (𝓞 K ⧸ v.asIdeal))
  have habs : Ideal.absNorm v.asIdeal = ringChar (𝓞 K ⧸ v.asIdeal) ^ (n : ℕ) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card, ← hcard]
  rw [habs]
  refine Nat.Coprime.pow_left _ ?_
  by_contra hnc
  have hpq : ringChar (𝓞 K ⧸ v.asIdeal) ∣ q := by
    by_contra hdvd
    exact hnc ((Nat.Prime.coprime_iff_not_dvd hp).mpr hdvd)
  apply hv
  rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]
  have hpmem : ((ringChar (𝓞 K ⧸ v.asIdeal) : ℕ) : 𝓞 K) ∈ v.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    rw [map_natCast (Ideal.Quotient.mk v.asIdeal), CharP.cast_eq_zero]
  obtain ⟨t, ht⟩ := hpq
  have hqt : ((q : ℕ) : 𝓞 K)
      = ((ringChar (𝓞 K ⧸ v.asIdeal) : ℕ) : 𝓞 K) * ((t : ℕ) : 𝓞 K) := by
    rw [← Nat.cast_mul, ← ht]
  rw [SetLike.mem_coe, hqt]
  exact Ideal.mul_mem_right _ _ hpmem

private def normClass (v : HeightOneSpectrum (𝓞 K)) : (ZMod q)ˣ :=
  if h : Nat.Coprime (Ideal.absNorm v.asIdeal) q then ZMod.unitOfCoprime _ h else 1

private theorem normClass_coe (v : HeightOneSpectrum (𝓞 K))
    (h : Nat.Coprime (Ideal.absNorm v.asIdeal) q) :
    ((normClass K q v : (ZMod q)ˣ) : ZMod q) = (Ideal.absNorm v.asIdeal : ZMod q) := by
  rw [normClass, dif_pos h, ZMod.coe_unitOfCoprime]

private theorem raySymbol_normClass_coe {I : Ideal (𝓞 K)} (hI : I ≠ ⊥)
    (hcop : I ⊔ Ideal.span {(q : 𝓞 K)} = ⊤) :
    ((raySymbol K (normClass K q) (I : FractionalIdeal ((𝓞 K)⁰) K) : (ZMod q)ˣ) : ZMod q)
      = (Ideal.absNorm I : ZMod q) := by
  classical
  have hI0 : I ≠ 0 := by simpa using hI
  have hvcop : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ I →
      Nat.Coprime (Ideal.absNorm v.asIdeal) q := by
    intro v hvI
    refine absNorm_coprime_of_not_dvd K q v fun hdvd => ?_
    have h1 : I ≤ v.asIdeal := Ideal.le_of_dvd hvI
    have h2 : Ideal.span {(q : 𝓞 K)} ≤ v.asIdeal := Ideal.le_of_dvd hdvd
    have htop : (⊤ : Ideal (𝓞 K)) ≤ v.asIdeal := hcop ▸ sup_le h1 h2
    exact v.isPrime.ne_top (top_le_iff.mp htop)
  have hdvd_of_n : ∀ v : HeightOneSpectrum (𝓞 K),
      (Associates.mk v.asIdeal).count (Associates.mk I).factors ≠ 0 → v.asIdeal ∣ I := by
    intro v hv
    rwa [← Associates.count_ne_zero_iff_dvd hI0 v.irreducible]
  have hfuneq : (fun v : HeightOneSpectrum (𝓞 K) =>
        normClass K q v ^ FractionalIdeal.count K v (I : FractionalIdeal ((𝓞 K)⁰) K))
      = fun v => normClass K q v
          ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors := by
    funext v
    rw [FractionalIdeal.count_coe K v hI0, zpow_natCast]
  have hfin := hasFiniteMulSupport_raySymbol_factors K (normClass K q)
    (I : FractionalIdeal ((𝓞 K)⁰) K)
  rw [hfuneq] at hfin
  have hsym : raySymbol K (normClass K q) (I : FractionalIdeal ((𝓞 K)⁰) K)
      = ∏ᶠ v : HeightOneSpectrum (𝓞 K),
          normClass K q v ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors := by
    rw [raySymbol, hfuneq]
  have hcoe : ((∏ᶠ v : HeightOneSpectrum (𝓞 K),
        normClass K q v ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors
          : (ZMod q)ˣ) : ZMod q)
      = ∏ᶠ v : HeightOneSpectrum (𝓞 K),
          ((normClass K q v : ZMod q))
            ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors := by
    rw [show ((∏ᶠ v : HeightOneSpectrum (𝓞 K),
          normClass K q v ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors
            : (ZMod q)ˣ) : ZMod q)
        = Units.coeHom (ZMod q) (∏ᶠ v : HeightOneSpectrum (𝓞 K),
            normClass K q v ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors)
        from rfl,
      MonoidHom.map_finprod (Units.coeHom (ZMod q)) hfin]
    exact finprod_congr fun v => by
      rw [Units.coeHom_apply, Units.val_pow_eq_pow_val]
  have hval : (fun v : HeightOneSpectrum (𝓞 K) =>
        ((normClass K q v : ZMod q))
          ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors)
      = fun v => ((Ideal.absNorm v.asIdeal : ZMod q))
          ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors := by
    funext v
    by_cases hv : (Associates.mk v.asIdeal).count (Associates.mk I).factors = 0
    · rw [hv, pow_zero, pow_zero]
    · rw [normClass_coe K q v (hvcop v (hdvd_of_n v hv))]
  have hnfin : Function.HasFiniteMulSupport
      (fun v : HeightOneSpectrum (𝓞 K) => Ideal.absNorm v.asIdeal
        ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors) := by
    show (Function.mulSupport _).Finite
    refine ((Filter.eventually_cofinite.mp
      (FractionalIdeal.finite_factors (I : FractionalIdeal ((𝓞 K)⁰) K))).subset ?_)
    intro v hv
    rw [Function.mem_mulSupport] at hv
    simp only [Set.mem_setOf_eq]
    intro hcount
    apply hv
    rw [FractionalIdeal.count_coe K v hI0, Nat.cast_eq_zero] at hcount
    show Ideal.absNorm v.asIdeal
      ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors = 1
    rw [hcount, pow_zero]
  have hmfin : Function.HasFiniteMulSupport
      (fun v : HeightOneSpectrum (𝓞 K) => v.maxPowDividing I) := by
    show (Function.mulSupport _).Finite
    refine ((Filter.eventually_cofinite.mp
      (FractionalIdeal.finite_factors (I : FractionalIdeal ((𝓞 K)⁰) K))).subset ?_)
    intro v hv
    rw [Function.mem_mulSupport] at hv
    simp only [Set.mem_setOf_eq]
    intro hcount
    apply hv
    rw [FractionalIdeal.count_coe K v hI0, Nat.cast_eq_zero] at hcount
    show v.asIdeal ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors = 1
    rw [hcount, pow_zero]
  have hcast : ((∏ᶠ v : HeightOneSpectrum (𝓞 K), Ideal.absNorm v.asIdeal
        ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors : ℕ) : ZMod q)
      = ∏ᶠ v : HeightOneSpectrum (𝓞 K), ((Ideal.absNorm v.asIdeal : ZMod q))
          ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors := by
    rw [show ((∏ᶠ v : HeightOneSpectrum (𝓞 K), Ideal.absNorm v.asIdeal
          ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors : ℕ) : ZMod q)
        = (Nat.castRingHom (ZMod q)) (∏ᶠ v : HeightOneSpectrum (𝓞 K),
            Ideal.absNorm v.asIdeal
              ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors)
        from rfl,
      map_finprod (Nat.castRingHom (ZMod q)) hnfin]
    exact finprod_congr fun v => by rw [map_pow]; rfl
  have hnat : (∏ᶠ v : HeightOneSpectrum (𝓞 K), Ideal.absNorm v.asIdeal
        ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors)
      = Ideal.absNorm I := by
    conv_rhs => rw [← Ideal.finprod_heightOneSpectrum_factorization hI0]
    rw [map_finprod Ideal.absNorm hmfin]
    refine finprod_congr fun v => ?_
    show Ideal.absNorm v.asIdeal
        ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors
      = Ideal.absNorm (v.asIdeal
          ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors)
    exact (map_pow Ideal.absNorm _ _).symm
  rw [hsym, hcoe, hval, ← hcast, hnat]

private theorem normClassKillsRay {𝔣 : Ideal (𝓞 K)} (hq𝔣 : Ideal.span {(q : 𝓞 K)} ∣ 𝔣) :
    ∀ α : 𝓞 K, α ≠ 0 → α - 1 ∈ 𝔣 →
      (∀ τ : K →+* ℝ, 0 < τ (algebraMap (𝓞 K) K α)) →
      raySymbol K (normClass K q)
        ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) = 1 := by
  intro α hα0 hα1 hpos
  have hspan : (Ideal.span {α} : Ideal (𝓞 K)) ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hα0
  have hα1q : α - 1 ∈ Ideal.span {(q : 𝓞 K)} := Ideal.le_of_dvd hq𝔣 hα1
  have hcop : (Ideal.span {α} : Ideal (𝓞 K)) ⊔ Ideal.span {(q : 𝓞 K)} = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have h1 : α - (α - 1) = 1 := by ring
    exact h1 ▸ Submodule.sub_mem _
      (Ideal.mem_sup_left (Ideal.subset_span rfl))
      (Ideal.mem_sup_right hα1q)
  have h1 := raySymbol_normClass_coe K q hspan hcop
  rw [Ideal.absNorm_span_singleton] at h1
  have hpos' : 0 < Algebra.norm ℤ α := norm_int_pos_of_totPos K hα0 hpos
  have hnat : (((Algebra.norm ℤ α).natAbs : ℕ) : ZMod q) = 1 := by
    rw [← Int.cast_natCast (R := ZMod q), Int.natAbs_of_nonneg hpos'.le,
      norm_int_cast_eq_one_of_sub_one_mem K q hα1q]
  rw [hnat] at h1
  exact Units.val_eq_one.mp h1

private def normClassChar {𝔣 : Ideal (𝓞 K)} (hq𝔣 : Ideal.span {(q : 𝓞 K)} ∣ 𝔣) :
    NarrowRayClassGroup K 𝔣 →* (ZMod q)ˣ :=
  raySymbolDescend K (normClass K q) (normClassKillsRay K q hq𝔣)

private theorem normClassChar_primeClass {𝔣 : Ideal (𝓞 K)} (hq𝔣 : Ideal.span {(q : 𝓞 K)} ∣ 𝔣)
    (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ 𝔣) :
    normClassChar K q hq𝔣 (primeClass K 𝔣 v hv) = normClass K q v :=
  raySymbolDescend_primeClass K (normClass K q) (normClassKillsRay K q hq𝔣) hv

end M4aP2
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin"

end
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin"

end Fold_M4aTheta_NormClassKill
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin"

section Fold_M4aTheta_NormRayCompat

p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.NumberField"

namespace M4aP2

variable (k E : Type*) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]

private theorem prod_sub_one_mem {R : Type*} [CommRing R] (J : Ideal R)
    {ι : Type*} (s : Finset ι) (f : ι → R) (h : ∀ i ∈ s, f i - 1 ∈ J) :
    (∏ i ∈ s, f i) - 1 ∈ J := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.prod_cons]
    have h1 := h a (Finset.mem_cons_self a s)
    have h2 := ih fun i hi => h i (Finset.mem_cons_of_mem hi)
    have hsplit : f a * ∏ i ∈ s, f i - 1 = f a * ((∏ i ∈ s, f i) - 1) + (f a - 1) := by ring
    rw [hsplit]
    exact J.add_mem (Ideal.mul_mem_left _ _ h2) h1

private abbrev NCl := ↥(IntermediateField.normalClosure k E (AlgebraicClosure k))

@[reducible] private noncomputable def algONcl : Algebra (𝓞 k) (𝓞 (NCl k E)) :=
  (RingOfIntegers.mapRingHom (algebraMap k (NCl k E))).toAlgebra

attribute [local instance] algONcl

omit [NumberField k] [NumberField E] in
private theorem algONcl_coe (x : 𝓞 k) :
    (algebraMap (𝓞 k) (𝓞 (NCl k E)) x : NCl k E) = algebraMap k (NCl k E) (x : k) := rfl

omit [NumberField k] [NumberField E] in
private theorem algONcl_injective :
    Function.Injective (algebraMap (𝓞 k) (𝓞 (NCl k E))) := by
  intro a b h
  have h1 : algebraMap k (NCl k E) (a : k) = algebraMap k (NCl k E) (b : k) := by
    rw [← algONcl_coe, ← algONcl_coe, h]
  exact FaithfulSMul.algebraMap_injective (𝓞 k) k ((algebraMap k (NCl k E)).injective h1)

private scoped instance : IsScalarTower ℤ (𝓞 k) (𝓞 (NCl k E)) :=
  IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

private scoped instance : Algebra.IsIntegral (𝓞 k) (𝓞 (NCl k E)) :=
  ⟨fun x => IsIntegral.tower_top (R := ℤ) (Algebra.IsIntegral.isIntegral x)⟩

private scoped instance : FaithfulSMul (𝓞 k) (𝓞 (NCl k E)) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr (algONcl_injective k E)

variable {k E}

private noncomputable def embO (σ : E →ₐ[k] AlgebraicClosure k) :
    𝓞 E →+* 𝓞 (NCl k E) :=
  RingOfIntegers.mapRingHom
    ((σ.codRestrict _ fun x => σ.fieldRange_le_normalClosure ⟨x, rfl⟩ :
      E →ₐ[k] NCl k E) : E →+* NCl k E)

omit [NumberField k] [NumberField E] in
private theorem embO_coe (σ : E →ₐ[k] AlgebraicClosure k) (x : 𝓞 E) :
    algebraMap (NCl k E) (AlgebraicClosure k) ((embO σ x : 𝓞 (NCl k E)) : NCl k E)
    = σ (algebraMap (𝓞 E) E x) := rfl

omit [NumberField k] [NumberField E] in
private theorem embO_comp (σ : E →ₐ[k] AlgebraicClosure k) :
    (embO σ).comp (algebraMap (𝓞 k) (𝓞 E)) = algebraMap (𝓞 k) (𝓞 (NCl k E)) := by
  apply RingHom.ext
  intro x
  apply FaithfulSMul.algebraMap_injective (𝓞 (NCl k E)) (NCl k E)
  show (σ.codRestrict _ fun z => σ.fieldRange_le_normalClosure ⟨z, rfl⟩ :
      E →ₐ[k] NCl k E) (algebraMap k E (x : k))
    = algebraMap k (NCl k E) (x : k)
  exact (σ.codRestrict _ fun z => σ.fieldRange_le_normalClosure ⟨z, rfl⟩ :
    E →ₐ[k] NCl k E).commutes (x : k)

variable (k E)

private theorem intNorm_sub_one_mem_of_sub_one_mem (𝔠 : Ideal (𝓞 k)) (y : 𝓞 E)
    (hy : y - 1 ∈ 𝔠.map (algebraMap (𝓞 k) (𝓞 E))) :
    Algebra.intNorm (𝓞 k) (𝓞 E) y - 1 ∈ 𝔠 := by
  classical
  haveI : FiniteDimensional k E := FiniteDimensional.right ℚ k E

  have hmem : ∀ σ : E →ₐ[k] AlgebraicClosure k,
      embO σ y - 1 ∈ 𝔠.map (algebraMap (𝓞 k) (𝓞 (NCl k E))) := by
    intro σ
    have h1 : embO σ (y - 1) ∈ (𝔠.map (algebraMap (𝓞 k) (𝓞 E))).map (embO σ) :=
      Ideal.mem_map_of_mem (embO σ) hy
    rw [Ideal.map_map, embO_comp σ] at h1
    simpa [map_sub] using h1
  have hPsub : (∏ σ : E →ₐ[k] AlgebraicClosure k, embO σ y) - 1
      ∈ 𝔠.map (algebraMap (𝓞 k) (𝓞 (NCl k E))) :=
    prod_sub_one_mem _ _ _ fun σ _ => hmem σ

  have hPeq : (∏ σ : E →ₐ[k] AlgebraicClosure k, embO σ y)
      = algebraMap (𝓞 k) (𝓞 (NCl k E)) (Algebra.intNorm (𝓞 k) (𝓞 E) y) := by
    apply FaithfulSMul.algebraMap_injective (𝓞 (NCl k E)) (NCl k E)
    apply RingHom.injective (algebraMap (NCl k E) (AlgebraicClosure k))
    rw [show ((algebraMap (𝓞 (NCl k E)) (NCl k E))
        (∏ σ : E →ₐ[k] AlgebraicClosure k, embO σ y))
        = ∏ σ : E →ₐ[k] AlgebraicClosure k,
          ((embO σ y : 𝓞 (NCl k E)) : NCl k E) from map_prod _ _ _,
      map_prod]
    have hL : ∀ σ : E →ₐ[k] AlgebraicClosure k,
        algebraMap (NCl k E) (AlgebraicClosure k) ((embO σ y : 𝓞 (NCl k E)) : NCl k E)
        = σ (algebraMap (𝓞 E) E y) := fun σ => embO_coe σ y
    rw [Finset.prod_congr rfl fun σ _ => hL σ]
    have hR : algebraMap (NCl k E) (AlgebraicClosure k)
        ((algebraMap (𝓞 k) (𝓞 (NCl k E)) (Algebra.intNorm (𝓞 k) (𝓞 E) y) : NCl k E))
        = algebraMap k (AlgebraicClosure k)
          (algebraMap (𝓞 k) k (Algebra.intNorm (𝓞 k) (𝓞 E) y)) := by
      rw [algONcl_coe]
      exact (IsScalarTower.algebraMap_apply k (NCl k E) (AlgebraicClosure k) _).symm
    rw [hR, Algebra.algebraMap_intNorm (A := 𝓞 k) (B := 𝓞 E) (K := k) (L := E)]
    exact (Algebra.norm_eq_prod_embeddings (K := k) (L := E)
      (E := AlgebraicClosure k) _).symm

  have hfin : algebraMap (𝓞 k) (𝓞 (NCl k E)) (Algebra.intNorm (𝓞 k) (𝓞 E) y - 1)
      ∈ 𝔠.map (algebraMap (𝓞 k) (𝓞 (NCl k E))) := by
    rw [map_sub, map_one, ← hPeq]
    exact hPsub
  haveI hTF : Module.IsTorsionFree (𝓞 k) (𝓞 (NCl k E)) := inferInstance
  haveI hFlat : Module.Flat (𝓞 k) (𝓞 (NCl k E)) := inferInstance
  haveI hFF : Module.FaithfullyFlat (𝓞 k) (𝓞 (NCl k E)) := inferInstance
  rw [← Ideal.comap_map_eq_self_of_faithfullyFlat
    (A := 𝓞 k) (B := 𝓞 (NCl k E)) 𝔠]
  exact Ideal.mem_comap.mpr hfin

private theorem intNorm_totPos_of_totPos (y : 𝓞 E) (hy0 : y ≠ 0)
    (hpos : ∀ τ : E →+* ℝ, 0 < τ (algebraMap (𝓞 E) E y)) :
    ∀ τ' : k →+* ℝ, 0 < τ' (algebraMap (𝓞 k) k (Algebra.intNorm (𝓞 k) (𝓞 E) y)) := by
  intro τ'
  classical
  letI : Algebra k ℂ := (Complex.ofRealHom.comp τ').toAlgebra
  haveI : FiniteDimensional k E := FiniteDimensional.right ℚ k E
  set yE : E := algebraMap (𝓞 E) E y with hyEdef
  have hyE0 : yE ≠ 0 := fun h =>
    hy0 ((map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 E) E)).mp h)
  have hσ0 : ∀ σ : E →ₐ[k] ℂ, σ yE ≠ 0 := fun σ h =>
    hyE0 ((map_eq_zero_iff _ (RingHom.injective (σ : E →+* ℂ))).mp h)
  have hstar_alg : ∀ c : k, (starRingEnd ℂ) (algebraMap k ℂ c) = algebraMap k ℂ c := fun c =>
    Complex.conj_ofReal _
  let conjA : (E →ₐ[k] ℂ) → (E →ₐ[k] ℂ) := fun σ =>
    { toRingHom := (starRingEnd ℂ).comp (σ : E →+* ℂ)
      commutes' := fun c => by
        show (starRingEnd ℂ) (σ (algebraMap k E c)) = algebraMap k ℂ c
        rw [σ.commutes]
        exact hstar_alg c }
  have hconjA_apply : ∀ (σ : E →ₐ[k] ℂ) (x : E), conjA σ x = (starRingEnd ℂ) (σ x) :=
    fun _ _ => rfl
  have hconjA_invol : ∀ σ, conjA (conjA σ) = σ := fun σ => AlgHom.ext fun x =>
    Complex.conj_conj (σ x)
  have hf_pair : ∀ σ : E →ₐ[k] ℂ,
      σ yE / (‖σ yE‖ : ℂ) * ((conjA σ) yE / (‖(conjA σ) yE‖ : ℂ)) = 1 := by
    intro σ
    have hz : σ yE ≠ 0 := hσ0 σ
    have hr0 : (‖σ yE‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
    have hc : (conjA σ) yE = (starRingEnd ℂ) (σ yE) := rfl
    rw [hc, Complex.norm_conj, div_mul_div_comm, Complex.mul_conj', ← sq]
    exact div_self (pow_ne_zero 2 hr0)
  have hf_fixed : ∀ σ : E →ₐ[k] ℂ, σ yE / (‖σ yE‖ : ℂ) ≠ 1 → conjA σ ≠ σ := by
    intro σ hf1 heq
    apply hf1
    have hreal : NumberField.ComplexEmbedding.IsReal (σ : E →+* ℂ) := by
      rw [NumberField.ComplexEmbedding.isReal_iff]
      ext x
      have h1 := congrArg (fun ψ : E →ₐ[k] ℂ => ψ x) heq
      simpa [NumberField.ComplexEmbedding.conjugate_coe_eq, hconjA_apply] using h1
    have hτpos := hpos hreal.embedding
    have hval : σ yE = ((hreal.embedding yE : ℝ) : ℂ) := (hreal.coe_embedding_apply yE).symm
    rw [hval, Complex.norm_real, Real.norm_of_nonneg hτpos.le]
    exact div_self (Complex.ofReal_ne_zero.mpr hτpos.ne')
  have hprod1 : ∏ σ : E →ₐ[k] ℂ, (σ yE / (‖σ yE‖ : ℂ)) = 1 :=
    Finset.prod_involution (fun σ _ => conjA σ) (fun σ _ => hf_pair σ)
      (fun σ _ h => hf_fixed σ h) (fun σ _ => Finset.mem_univ _) (fun σ _ => hconjA_invol σ)
  have hsplit : ∀ σ : E →ₐ[k] ℂ, σ yE = σ yE / (‖σ yE‖ : ℂ) * (‖σ yE‖ : ℂ) := fun σ =>
    (div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr
      (norm_ne_zero_iff.mpr (hσ0 σ)))).symm
  have hprodR : ∏ σ : E →ₐ[k] ℂ, σ yE = ((∏ σ : E →ₐ[k] ℂ, ‖σ yE‖ : ℝ) : ℂ) := by
    rw [Complex.ofReal_prod]
    calc ∏ σ : E →ₐ[k] ℂ, σ yE
        = ∏ σ : E →ₐ[k] ℂ, (σ yE / (‖σ yE‖ : ℂ) * (‖σ yE‖ : ℂ)) :=
          Finset.prod_congr rfl fun σ _ => hsplit σ
      _ = (∏ σ : E →ₐ[k] ℂ, (σ yE / (‖σ yE‖ : ℂ))) * ∏ σ : E →ₐ[k] ℂ, (‖σ yE‖ : ℂ) :=
          Finset.prod_mul_distrib
      _ = ∏ σ : E →ₐ[k] ℂ, (‖σ yE‖ : ℂ) := by rw [hprod1, one_mul]
  have hbridge : algebraMap k ℂ (algebraMap (𝓞 k) k (Algebra.intNorm (𝓞 k) (𝓞 E) y))
      = ∏ σ : E →ₐ[k] ℂ, σ yE := by
    rw [Algebra.algebraMap_intNorm (A := 𝓞 k) (B := 𝓞 E) (K := k) (L := E)]
    exact Algebra.norm_eq_prod_embeddings (K := k) (L := E) (E := ℂ) yE
  have hfinal : ((τ' (algebraMap (𝓞 k) k (Algebra.intNorm (𝓞 k) (𝓞 E) y)) : ℝ) : ℂ)
      = ((∏ σ : E →ₐ[k] ℂ, ‖σ yE‖ : ℝ) : ℂ) := by
    rw [show ((τ' (algebraMap (𝓞 k) k (Algebra.intNorm (𝓞 k) (𝓞 E) y)) : ℝ) : ℂ)
        = algebraMap k ℂ (algebraMap (𝓞 k) k (Algebra.intNorm (𝓞 k) (𝓞 E) y)) from rfl,
      hbridge, hprodR]
  have hval := Complex.ofReal_injective hfinal
  rw [hval]
  exact Finset.prod_pos fun σ _ => norm_pos_iff.mpr (hσ0 σ)

end M4aP2
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

end Fold_M4aTheta_NormRayCompat
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

section Fold_M4aTheta_ICNRelNormRCG

noncomputable section

p2m_open "Deep.NTSupply NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.NumberField IsDedekindDomain"
open scoped nonZeroDivisors

namespace HeckeCharacter
p2m_export "HeckeCharacter" "idealMultiplicity placeUnder' placeUnder'_asIdeal modulusExt fracRelNormUnit placeUnder'_dvd_iff gcopNC2 coe_raySymbol_gcop_eq_fracRelNormUnit' fracRelNormUnit_mem_coprimeToModulus relNormCTM fad_one_apply fad_mul_apply placeOrd valued_ne_zero_of_unit placeOrd_eq_zero_iff finite_support_placeOrd fadContentHom projFin placeOf isReal_compOfRealHom isReal_placeOf archRealProjTau archSign archSign_of_fst_eq_one archSign_mul archSign_one archSign_inv unit_cong_mul unit_cong_div fad_units_inv_apply IsAdjuster fadContentHom_projFin_idelicNorm_eq_fracRelNormUnit isAdjuster_idelicNorm_of_isAdjuster"
p2m_open "HeckeCharacter"

variable (k E : Type*) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]

private theorem intNorm_ne_zero {α : 𝓞 E} (hα : α ≠ 0) : Algebra.intNorm (𝓞 k) (𝓞 E) α ≠ 0 := by
  intro h
  have : Ideal.relNorm (𝓞 k) (Ideal.span {α}) = (⊥ : Ideal (𝓞 k)) := by
    rw [Ideal.relNorm_singleton, h, Ideal.span_singleton_eq_bot]
  exact hα (Ideal.span_singleton_eq_bot.mp (Ideal.relNorm_eq_bot_iff.mp this))

open scoped Classical in

private def fNC2 (𝔠 : Ideal (𝓞 k)) (w : HeightOneSpectrum (𝓞 E)) : NarrowRayClassGroup k 𝔠 :=
  if h : ¬ (placeUnder' k E w).asIdeal ∣ 𝔠
  then primeClass k 𝔠 (placeUnder' k E w) h ^ ((placeUnder' k E w).asIdeal.inertiaDeg' w.asIdeal)
  else 1

omit [NumberField E] in
private theorem fNC2_of_dvd (𝔠 : Ideal (𝓞 k)) (w : HeightOneSpectrum (𝓞 E))
    (h : (placeUnder' k E w).asIdeal ∣ 𝔠) : fNC2 k E 𝔠 w = 1 := by
  simp [fNC2, h]

omit [NumberField E] in

private theorem fNC2_eq_mk_gcop (𝔠 : Ideal (𝓞 k)) (w : HeightOneSpectrum (𝓞 E)) :
    fNC2 k E 𝔠 w = NarrowRayClassGroup.mk k 𝔠 (gcopNC2 k E 𝔠 w) := by
  classical
  unfold fNC2 gcopNC2
  split
  · simp only [primeClass, ← map_pow]; rfl
  · rw [map_one]

private theorem coe_raySymbol_gcop_eq_fracRelNormUnit {𝔠 : Ideal (𝓞 k)} (α : 𝓞 E) (hα0 : α ≠ 0)
    (hα1 : α - 1 ∈ modulusExt k E 𝔠) :
    ((raySymbol E (gcopNC2 k E 𝔠)
        ((Ideal.span {α} : Ideal (𝓞 E)) : FractionalIdeal ((𝓞 E)⁰) E)
      : ↥(coprimeToModulus k 𝔠)) : (FractionalIdeal ((𝓞 k)⁰) k)ˣ)
      = fracRelNormUnit k E (principalUnit E α hα0) := by
  set J := ((Ideal.span {α} : Ideal (𝓞 E)) : FractionalIdeal ((𝓞 E)⁰) E)
  have hfRN : fracRelNormUnit k E (principalUnit E α hα0)
      = raySymbol E
          (fun w => primeUnit k (placeUnder' k E w)
            ^ ((placeUnder' k E w).asIdeal.inertiaDeg' w.asIdeal)) J := by
    show raySymbol E _ ((principalUnit E α hα0 : (FractionalIdeal ((𝓞 E)⁰) E)ˣ) :
        FractionalIdeal ((𝓞 E)⁰) E) = _
    exact congrArg _ (principalUnit_val E α hα0)
  rw [hfRN]
  unfold raySymbol
  refine ((MonoidHom.map_finprod ((coprimeToModulus k 𝔠).subtype)
    (hasFiniteMulSupport_raySymbol_factors E (gcopNC2 k E 𝔠) J))).trans ?_
  refine finprod_congr (fun w => ?_)
  rw [map_zpow, Subgroup.coe_subtype]
  classical
  by_cases hw : (placeUnder' k E w).asIdeal ∣ 𝔠
  ·
    have hct : FractionalIdeal.count E w J = 0 :=
      count_span_singleton_eq_zero_of_sub_one_mem E hα0 hα1
        ((placeUnder'_dvd_iff k E 𝔠 w).mp hw)
    rw [hct]; simp
  ·
    simp only [gcopNC2]
    rw [dif_pos hw]

set_option maxSynthPendingDepth 3 in

private theorem relNormRCG_hkill (𝔠 : Ideal (𝓞 k)) (α : 𝓞 E) (hα0 : α ≠ 0)
    (hα1 : α - 1 ∈ modulusExt k E 𝔠) (hpos : ∀ τ : E →+* ℝ, 0 < τ (algebraMap (𝓞 E) E α)) :
    raySymbol E (fNC2 k E 𝔠)
      ((Ideal.span {α} : Ideal (𝓞 E)) : FractionalIdeal ((𝓞 E)⁰) E) = 1 := by
  set J := ((Ideal.span {α} : Ideal (𝓞 E)) : FractionalIdeal ((𝓞 E)⁰) E)

  have hstep1 : raySymbol E (fNC2 k E 𝔠) J
      = NarrowRayClassGroup.mk k 𝔠 (raySymbol E (gcopNC2 k E 𝔠) J) := by
    unfold raySymbol
    rw [show (fun v => fNC2 k E 𝔠 v ^ FractionalIdeal.count E v J)
        = (fun v => NarrowRayClassGroup.mk k 𝔠 (gcopNC2 k E 𝔠 v ^ FractionalIdeal.count E v J))
      from funext (fun w => by rw [fNC2_eq_mk_gcop, map_zpow])]
    exact (_root_.map_finprod (NarrowRayClassGroup.mk k 𝔠)
      (hasFiniteMulSupport_raySymbol_factors E (gcopNC2 k E 𝔠) J)).symm
  rw [hstep1]

  apply NarrowRayClassGroup.mk_eq_one_of_mem

  rw [coe_raySymbol_gcop_eq_fracRelNormUnit k E α hα0 hα1]

  apply Subgroup.subset_closure
  rw [mem_narrowRaySet_iff]
  exact ⟨Algebra.intNorm (𝓞 k) (𝓞 E) α, intNorm_ne_zero k E hα0,
    M4aP2.intNorm_sub_one_mem_of_sub_one_mem k E 𝔠 α hα1,
    M4aP2.intNorm_totPos_of_totPos k E α hα0 hpos,
    fracRelNormUnit_principalUnit k E α hα0⟩

private def relNormRCG (𝔠 : Ideal (𝓞 k)) :
    NarrowRayClassGroup E (modulusExt k E 𝔠) →* NarrowRayClassGroup k 𝔠 :=
  raySymbolDescend E (fNC2 k E 𝔠)
    (fun α hα0 hα1 hpos => relNormRCG_hkill k E 𝔠 α hα0 hα1 hpos)

private theorem relNormRCG_primeClass (𝔠 : Ideal (𝓞 k)) (h𝔠 : 𝔠 ≠ ⊥)
    (w : HeightOneSpectrum (𝓞 E)) (hw : ¬ w.asIdeal ∣ modulusExt k E 𝔠)
    (𝔭 : HeightOneSpectrum (𝓞 k)) (h𝔭w : w.asIdeal.under (𝓞 k) = 𝔭.asIdeal)
    (h𝔭 : ¬ 𝔭.asIdeal ∣ 𝔠) :
    relNormRCG k E 𝔠 (primeClass E (modulusExt k E 𝔠) w hw)
      = primeClass k 𝔠 𝔭 h𝔭 ^ (𝔭.asIdeal.inertiaDeg' w.asIdeal) := by
  have _ := h𝔠
  have heq : placeUnder' k E w = 𝔭 :=
    IsDedekindDomain.HeightOneSpectrum.ext (by rw [placeUnder'_asIdeal, h𝔭w])
  subst heq
  classical
  rw [relNormRCG, raySymbolDescend_primeClass E (fNC2 k E 𝔠) _ hw, fNC2,
    dif_pos h𝔭]

end HeckeCharacter
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

end
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

section Battery
p2m_open "HeckeCharacter P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.HeckeCharacter"
end Battery
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

end Fold_M4aTheta_ICNRelNormRCG
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

section Fold_M4aTheta_ICNIdeleNorm

noncomputable section

p2m_open "Deep.NTSupply NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.NumberField IsDedekindDomain"
open scoped nonZeroDivisors

namespace HeckeCharacter
p2m_export "HeckeCharacter" "idealMultiplicity placeUnder' placeUnder'_asIdeal modulusExt fracRelNormUnit placeUnder'_dvd_iff gcopNC2 coe_raySymbol_gcop_eq_fracRelNormUnit' fracRelNormUnit_mem_coprimeToModulus relNormCTM fad_one_apply fad_mul_apply placeOrd valued_ne_zero_of_unit placeOrd_eq_zero_iff finite_support_placeOrd fadContentHom projFin placeOf isReal_compOfRealHom isReal_placeOf archRealProjTau archSign archSign_of_fst_eq_one archSign_mul archSign_one archSign_inv unit_cong_mul unit_cong_div fad_units_inv_apply IsAdjuster fadContentHom_projFin_idelicNorm_eq_fracRelNormUnit isAdjuster_idelicNorm_of_isAdjuster"
p2m_open "HeckeCharacter"

variable (k E : Type*) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]

omit [NumberField k] [NumberField E] in

private theorem modulusExt_ne_bot {𝔠 : Ideal (𝓞 k)} (h𝔠 : 𝔠 ≠ ⊥) : modulusExt k E 𝔠 ≠ ⊥ := by
  intro h
  exact h𝔠 ((Ideal.map_eq_bot_iff_of_injective
    (f := algebraMap (𝓞 k) (𝓞 E)) (FaithfulSMul.algebraMap_injective (𝓞 k) (𝓞 E))).mp h)

set_option maxSynthPendingDepth 3 in

private theorem relNormRCG_mk (𝔠 : Ideal (𝓞 k)) (Y : ↥(coprimeToModulus E (modulusExt k E 𝔠))) :
    relNormRCG k E 𝔠 (NarrowRayClassGroup.mk E (modulusExt k E 𝔠) Y)
      = NarrowRayClassGroup.mk k 𝔠
          ⟨fracRelNormUnit k E (Y : (FractionalIdeal ((𝓞 E)⁰) E)ˣ),
            fracRelNormUnit_mem_coprimeToModulus k E Y.2⟩ := by
  rw [relNormRCG, raySymbolDescend_mk]

  rw [raySymbolHom_apply]
  set J := ((Y : (FractionalIdeal ((𝓞 E)⁰) E)ˣ) : FractionalIdeal ((𝓞 E)⁰) E)

  have hstep1 : raySymbol E (fNC2 k E 𝔠) J
      = NarrowRayClassGroup.mk k 𝔠 (raySymbol E (gcopNC2 k E 𝔠) J) := by
    unfold raySymbol
    rw [show (fun v => fNC2 k E 𝔠 v ^ FractionalIdeal.count E v J)
        = (fun v => NarrowRayClassGroup.mk k 𝔠 (gcopNC2 k E 𝔠 v ^ FractionalIdeal.count E v J))
      from funext (fun w => by rw [fNC2_eq_mk_gcop, map_zpow])]
    exact (_root_.map_finprod (NarrowRayClassGroup.mk k 𝔠)
      (hasFiniteMulSupport_raySymbol_factors E (gcopNC2 k E 𝔠) J)).symm
  rw [hstep1]
  exact congrArg _ (Subtype.ext (coe_raySymbol_gcop_eq_fracRelNormUnit' k E _ Y.2))

private theorem fracRelNormUnit_principalUnit' (a : 𝓞 E) (ha : a ≠ 0) :
    fracRelNormUnit k E (principalUnit E a ha)
      = principalUnit k (Algebra.intNorm (𝓞 k) (𝓞 E) a) (intNorm_ne_zero k E ha) :=
  Units.ext ((fracRelNormUnit_principalUnit k E a ha).trans
    (principalUnit_val k _ (intNorm_ne_zero k E ha)).symm)

private theorem toPrincipalIdeal_algebraMap (K : Type*) [Field K] [NumberField K] (a : 𝓞 K) (ha : a ≠ 0) :
    toPrincipalIdeal (𝓞 K) K
        (Units.mk0 (algebraMap (𝓞 K) K a)
          (fun h => ha (by exact_mod_cast (FaithfulSMul.algebraMap_injective (𝓞 K) K) h)))
      = principalUnit K a ha :=
  Units.ext <| by
    rw [coe_toPrincipalIdeal, Units.val_mk0, principalUnit_val,
      FractionalIdeal.coeIdeal_span_singleton]

private theorem fracRelNormUnit_toPrincipalIdeal (α : Eˣ) :
    fracRelNormUnit k E (toPrincipalIdeal (𝓞 E) E α)
      = toPrincipalIdeal (𝓞 k) k (Units.map (Algebra.norm k) α) := by

  obtain ⟨x, y, hy, hαxy⟩ := IsFractionRing.div_surjective (A := 𝓞 E) (α : E)
  have hy0 : (y : 𝓞 E) ≠ 0 := nonZeroDivisors.coe_ne_zero ⟨y, hy⟩
  have hey : (algebraMap (𝓞 E) E) y ≠ 0 := fun h => hy0
    (by exact_mod_cast (FaithfulSMul.algebraMap_injective (𝓞 E) E) h)
  have hx0 : x ≠ 0 := by
    intro h; subst h
    exact α.ne_zero (hαxy.symm.trans (by simp))
  have hex : (algebraMap (𝓞 E) E) x ≠ 0 := fun h => hx0
    (by exact_mod_cast (FaithfulSMul.algebraMap_injective (𝓞 E) E) h)

  have hα_dec : α = Units.mk0 _ hex / Units.mk0 _ hey :=
    Units.ext (by rw [Units.val_div_eq_div_val, Units.val_mk0, Units.val_mk0, ← hαxy])
  rw [hα_dec]
  simp only [map_div]

  rw [toPrincipalIdeal_algebraMap E x hx0, toPrincipalIdeal_algebraMap E y hy0,
    fracRelNormUnit_principalUnit' k E x hx0, fracRelNormUnit_principalUnit' k E y hy0]
  congr 1 <;>
    · rw [← toPrincipalIdeal_algebraMap k]
      exact congrArg _ (Units.ext (by
        simp only [Units.coe_map, Units.val_mk0]
        exact Algebra.algebraMap_intNorm (K := k) (L := E) _))

private theorem ideleContentHom_comp_ideleNorm (𝔠 : Ideal (𝓞 k)) (h𝔠 : 𝔠 ≠ ⊥)
    (Nrm : (AdeleRing (𝓞 E) E)ˣ →* (AdeleRing (𝓞 k) k)ˣ)
    (hNrm_adjuster : ∀ {u : (AdeleRing (𝓞 E) E)ˣ} {α : Eˣ},
      IsAdjuster E (modulusExt k E 𝔠) u α →
      IsAdjuster k 𝔠 (Nrm u) (Units.map (Algebra.norm k) α))
    (hNrm_fadContent : ∀ u : (AdeleRing (𝓞 E) E)ˣ,
      fadContentHom k (projFin k (Nrm u)) = fracRelNormUnit k E (fadContentHom E (projFin E u))) :
    (ideleContentHom k 𝔠).comp Nrm
      = (relNormRCG k E 𝔠).comp (ideleContentHom E (modulusExt k E 𝔠)) := by
  ext u
  have h𝔠E := modulusExt_ne_bot k E h𝔠
  obtain ⟨α, hα⟩ := exists_isAdjuster E h𝔠E u
  have hNα := hNrm_adjuster hα
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply,
    ideleContentHom_apply k h𝔠 hNα, ideleContentHom_apply E h𝔠E hα,
    relNormRCG_mk k E 𝔠]

  congr 1
  apply Subtype.ext
  show fadContentHom k (projFin k _) = fracRelNormUnit k E (fadContentHom E (projFin E _))
  simp only [map_mul, map_inv]
  rw [hNrm_fadContent u]
  congr 1
  rw [projFin_principal, projFin_principal, fadContentHom_unitEmbedding,
    fadContentHom_unitEmbedding, fracRelNormUnit_toPrincipalIdeal]

end HeckeCharacter
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

end
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

section Battery
p2m_open "HeckeCharacter P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.HeckeCharacter"
end Battery
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

end Fold_M4aTheta_ICNIdeleNorm
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

section Fold_M4aTheta_RelNormCTM

noncomputable section

p2m_open "Deep.NTSupply NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.NumberField IsDedekindDomain"
open scoped nonZeroDivisors

namespace HeckeCharacter
p2m_export "HeckeCharacter" "idealMultiplicity placeUnder' placeUnder'_asIdeal modulusExt fracRelNormUnit placeUnder'_dvd_iff gcopNC2 coe_raySymbol_gcop_eq_fracRelNormUnit' fracRelNormUnit_mem_coprimeToModulus relNormCTM fad_one_apply fad_mul_apply placeOrd valued_ne_zero_of_unit placeOrd_eq_zero_iff finite_support_placeOrd fadContentHom projFin placeOf isReal_compOfRealHom isReal_placeOf archRealProjTau archSign archSign_of_fst_eq_one archSign_mul archSign_one archSign_inv unit_cong_mul unit_cong_div fad_units_inv_apply IsAdjuster fadContentHom_projFin_idelicNorm_eq_fracRelNormUnit isAdjuster_idelicNorm_of_isAdjuster"
p2m_open "HeckeCharacter"

variable (k E : Type*) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]

private theorem coe_relNormCTM {𝔠 : Ideal (𝓞 k)} (Y : ↥(coprimeToModulus E (modulusExt k E 𝔠))) :
    ((relNormCTM k E 𝔠 Y : ↥(coprimeToModulus k 𝔠)) : (FractionalIdeal ((𝓞 k)⁰) k)ˣ)
      = fracRelNormUnit k E (Y : (FractionalIdeal ((𝓞 E)⁰) E)ˣ) := rfl

private theorem relNormCTM_primeUnit {𝔠 : Ideal (𝓞 k)} {w : HeightOneSpectrum (𝓞 E)}
    (hw : ¬ w.asIdeal ∣ modulusExt k E 𝔠) :
    ((relNormCTM k E 𝔠 ⟨primeUnit E w, primeUnit_mem_coprimeToModulus E hw⟩
        : ↥(coprimeToModulus k 𝔠)) : (FractionalIdeal ((𝓞 k)⁰) k)ˣ)
      = primeUnit k (placeUnder' k E w)
          ^ ((placeUnder' k E w).asIdeal.inertiaDeg' w.asIdeal) := by
  exact fracRelNormUnit_primeUnit k E w (placeUnder' k E w) (placeUnder'_asIdeal k E w).symm

private theorem relNormCTM_principalUnit {𝔠 : Ideal (𝓞 k)} {α : 𝓞 E} (hα : α ≠ 0)
    (hαcop : principalUnit E α hα ∈ coprimeToModulus E (modulusExt k E 𝔠)) :
    ((relNormCTM k E 𝔠 ⟨principalUnit E α hα, hαcop⟩
        : ↥(coprimeToModulus k 𝔠)) : (FractionalIdeal ((𝓞 k)⁰) k)ˣ)
      = principalUnit k (Algebra.intNorm (𝓞 k) (𝓞 E) α) (intNorm_ne_zero k E hα) := by
  exact fracRelNormUnit_principalUnit' k E α hα

private theorem mk_relNormCTM {𝔠 : Ideal (𝓞 k)} (Y : ↥(coprimeToModulus E (modulusExt k E 𝔠))) :
    NarrowRayClassGroup.mk k 𝔠 (relNormCTM k E 𝔠 Y)
      = relNormRCG k E 𝔠 (NarrowRayClassGroup.mk E (modulusExt k E 𝔠) Y) :=
  (relNormRCG_mk k E 𝔠 Y).symm

end HeckeCharacter
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

section Battery
p2m_open "HeckeCharacter P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.HeckeCharacter"
end Battery
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"
end
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

end Fold_M4aTheta_RelNormCTM
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

section Fold_M4aTheta_ArtinDischargeGlue

noncomputable section

p2m_open "Deep.NTSupply NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.NumberField IsDedekindDomain"
open scoped nonZeroDivisors

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "P2.Artin.normRaySubgroup P2.Artin.SecondInequalityCTM P2.Artin.IdeleFirstIneqDataAt P2.Artin.artinFrob"
namespace P2
p2m_export "LanglandsTunnell.P2" "Artin.normRaySubgroup Artin.SecondInequalityCTM Artin.IdeleFirstIneqDataAt Artin.artinFrob"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

section DefN

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private theorem principalCarrier_mem_normRaySubgroup {𝔣 : Ideal (𝓞 K)} {α : 𝓞 K} (hα0 : α ≠ 0) (hα1 : α - 1 ∈ 𝔣)
    (hpos : ∀ τ : K →+* ℝ, 0 < τ (algebraMap (𝓞 K) K α)) :
    (⟨principalUnit K α hα0, principalUnit_mem_coprimeToModulus K hα0 hα1⟩ : ↥(coprimeToModulus K 𝔣))
      ∈ normRaySubgroup K L 𝔣 :=
  le_sup_left (a := (narrowRaySubgroup K 𝔣).subgroupOf (coprimeToModulus K 𝔣))
    (Subgroup.mem_subgroupOf.mpr
      (Subgroup.subset_closure ⟨α, hα0, hα1, hpos, (principalUnit_val K α hα0).symm ▸ rfl⟩))

end DefN
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

section hNP

variable (k E : Type*) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]

p2m_open "HeckeCharacter P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.HeckeCharacter"

private theorem relNormCTM_primeCarrier_of_inertiaDeg_eq_one {𝔠 : Ideal (𝓞 k)} {w : HeightOneSpectrum (𝓞 E)}
    (hw : ¬ w.asIdeal ∣ modulusExt k E 𝔠) {v : HeightOneSpectrum (𝓞 k)} (hv : ¬ v.asIdeal ∣ 𝔠)
    (hwv : w.asIdeal.under (𝓞 k) = v.asIdeal) (hf : v.asIdeal.inertiaDeg' w.asIdeal = 1) :
    relNormCTM k E 𝔠 ⟨primeUnit E w, primeUnit_mem_coprimeToModulus E hw⟩
      = ⟨primeUnit k v, primeUnit_mem_coprimeToModulus k hv⟩ := by
  have heq : placeUnder' k E w = v :=
    IsDedekindDomain.HeightOneSpectrum.ext (by rw [placeUnder'_asIdeal, hwv])
  exact Subtype.ext (by rw [relNormCTM_primeUnit k E hw, heq, hf, pow_one])

end hNP
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

section hcompat

variable (K M E N : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Field E] [NumberField E]
  [Field N] [NumberField N] [Algebra K M] [Algebra K E] [Algebra K N] [Algebra M N] [Algebra E N]
  [IsScalarTower K M N] [IsScalarTower K E N] [IsGalois K M] [IsGalois E N]
  [IsMulCommutative (M ≃ₐ[K] M)] [IsMulCommutative (N ≃ₐ[E] N)]

p2m_open "HeckeCharacter P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.HeckeCharacter"

set_option maxSynthPendingDepth 3 in

private theorem artinSymbol_relNormCTM_primeCarrier (𝔣 : Ideal (𝓞 K)) {w : HeightOneSpectrum (𝓞 E)}
    (hw : ¬ w.asIdeal ∣ modulusExt K E 𝔣) {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ 𝔣)
    (hwv : w.asIdeal.under (𝓞 K) = v.asIdeal)
    (hI : ((primeAbove E N w).under (𝓞 M)).inertia (M ≃ₐ[K] M) = ⊥) :
    artinSymbol K M 𝔣 (relNormCTM K E 𝔣 ⟨primeUnit E w, primeUnit_mem_coprimeToModulus E hw⟩)
      = resHom K M E N (artinSymbol E N (modulusExt K E 𝔣) ⟨primeUnit E w, primeUnit_mem_coprimeToModulus E hw⟩) := by
  have heq : placeUnder' K E w = v :=
    IsDedekindDomain.HeightOneSpectrum.ext (by rw [placeUnder'_asIdeal, hwv])
  have hvcop : ¬ (placeUnder' K E w).asIdeal ∣ 𝔣 := heq ▸ hv

  rw [show relNormCTM K E 𝔣 ⟨primeUnit E w, primeUnit_mem_coprimeToModulus E hw⟩
      = (⟨primeUnit K (placeUnder' K E w), primeUnit_mem_coprimeToModulus K hvcop⟩
          : ↥(coprimeToModulus K 𝔣)) ^ ((placeUnder' K E w).asIdeal.inertiaDeg' w.asIdeal) from
    Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact relNormCTM_primeUnit K E hw),
    map_pow, artinSymbol_prime K M hvcop]

  rw [artinSymbol_prime E N hw, resHom_artinFrob K M E N v w hwv hI, heq]

set_option maxSynthPendingDepth 3 in

private theorem artinSymbol_comp_relNormCTM_eq (𝔣 : Ideal (𝓞 K))
    (hI_all : ∀ w : HeightOneSpectrum (𝓞 E), ¬ w.asIdeal ∣ modulusExt K E 𝔣 →
      ((primeAbove E N w).under (𝓞 M)).inertia (M ≃ₐ[K] M) = ⊥) :
    (artinSymbol K M 𝔣).comp (relNormCTM K E 𝔣)
      = (resHom K M E N).comp (artinSymbol E N (modulusExt K E 𝔣)) := by
  refine MonoidHom.eq_of_eqOn_dense (closure_primeCarriers_eq_top E (modulusExt K E 𝔣)) ?_
  rintro _ ⟨w, hw, rfl⟩
  have hv : ¬ (placeUnder' K E w).asIdeal ∣ 𝔣 := fun h => hw ((placeUnder'_dvd_iff K E 𝔣 w).mp h)
  exact artinSymbol_relNormCTM_primeCarrier K M E N 𝔣 hw hv (placeUnder'_asIdeal K E w).symm
    (hI_all w hw)

end hcompat
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

section Battery
p2m_open "LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin"
end Battery
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"
end
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

end Fold_M4aTheta_ArtinDischargeGlue
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

section Fold_M4aTheta_ArtinField

set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "P2.Artin.normRaySubgroup P2.Artin.SecondInequalityCTM P2.Artin.IdeleFirstIneqDataAt P2.Artin.artinFrob"
namespace P2
p2m_export "LanglandsTunnell.P2" "Artin.normRaySubgroup Artin.SecondInequalityCTM Artin.IdeleFirstIneqDataAt Artin.artinFrob"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

open IntermediateField

variable {K M : Type*} [Field K] [Field M] [Algebra K M]
variable (L : IntermediateField K M) [IsGalois K L]
variable {m : ℕ} [NeZero m] {ζ : M} (hζ : IsPrimitiveRoot ζ m)
variable {C : Type*} [Group C] (ψ : (ZMod m)ˣ ≃* C)

private theorem autToPow_eq_one_iff (τ : M ≃ₐ[K] M) : hζ.autToPow K τ = 1 ↔ τ ζ = ζ := by
  have key : ∀ v : ℕ, ζ ^ v = ζ ↔ (v : ZMod m) = 1 := fun v => by
    rw [show (ζ ^ v = ζ ↔ ζ ^ v = ζ ^ 1) by rw [pow_one], (hζ.isOfFinOrder (NeZero.ne m)).pow_eq_pow_iff_modEq,
      ← hζ.eq_orderOf, ← ZMod.natCast_eq_natCast_iff, Nat.cast_one]
  rw [← hζ.autToPow_spec K τ, key, ZMod.natCast_zmod_val, Units.val_eq_one]

private theorem mem_fixingSubgroup_intermediateField_iff (E : IntermediateField K M) (τ : M ≃ₐ[K] M) :
    τ ∈ E.fixingSubgroup ↔ ∀ x ∈ E, τ x = x :=
  _root_.mem_fixingSubgroup_iff _

private theorem apply_eq_self_iff_mem_fixingSubgroup_adjoin (τ : M ≃ₐ[K] M) : τ ζ = ζ ↔ τ ∈ K⟮ζ⟯.fixingSubgroup := by
  rw [← Subgroup.zpowers_le, ← IntermediateField.le_iff_le, adjoin_simple_le_iff, mem_fixedField_iff]
  constructor
  · intro h g hg
    exact (Subgroup.zpowers_le.mpr (show τ ∈ MulAction.stabilizer (M ≃ₐ[K] M) ζ from h) : _ ≤ _) hg
  · intro h
    exact h τ (Subgroup.mem_zpowers τ)

private noncomputable def galProd : (M ≃ₐ[K] M) →* (L ≃ₐ[K] L) × C :=
  (AlgEquiv.restrictNormalHom L).prod (ψ.toMonoidHom.comp (hζ.autToPow K))

private theorem galProd_apply_fst (τ : M ≃ₐ[K] M) : (galProd L hζ ψ τ).1 = AlgEquiv.restrictNormalHom L τ := rfl

private theorem galProd_apply_snd (τ : M ≃ₐ[K] M) : (galProd L hζ ψ τ).2 = ψ (hζ.autToPow K τ) := rfl

private theorem galProd_fst_eq_one_iff (τ : M ≃ₐ[K] M) : (galProd L hζ ψ τ).1 = 1 ↔ τ ∈ L.fixingSubgroup := by
  rw [galProd_apply_fst, mem_fixingSubgroup_intermediateField_iff]
  exact AlgEquiv.restrictNormal_eq_one_iff L τ

private theorem galProd_snd_eq_one_iff (τ : M ≃ₐ[K] M) : (galProd L hζ ψ τ).2 = 1 ↔ τ ∈ K⟮ζ⟯.fixingSubgroup := by
  rw [galProd_apply_snd, EmbeddingLike.map_eq_one_iff, autToPow_eq_one_iff, apply_eq_self_iff_mem_fixingSubgroup_adjoin]

private theorem comap_galProd_prod_bot :
    ((⊤ : Subgroup (L ≃ₐ[K] L)).prod (⊥ : Subgroup C)).comap (galProd L hζ ψ) = K⟮ζ⟯.fixingSubgroup := by
  ext τ
  rw [Subgroup.mem_comap, Subgroup.mem_prod, ← galProd_snd_eq_one_iff L hζ ψ, Subgroup.mem_bot]
  exact ⟨fun h => h.2, fun h => ⟨Subgroup.mem_top _, h⟩⟩

private theorem comap_galProd_bot_prod :
    ((⊥ : Subgroup (L ≃ₐ[K] L)).prod (⊤ : Subgroup C)).comap (galProd L hζ ψ) = L.fixingSubgroup := by
  ext τ
  rw [Subgroup.mem_comap, Subgroup.mem_prod, ← galProd_fst_eq_one_iff L hζ ψ, Subgroup.mem_bot]
  exact ⟨fun h => h.1, fun h => ⟨h, Subgroup.mem_top _⟩⟩

private theorem galProd_injective (htop : L ⊔ K⟮ζ⟯ = ⊤) : Function.Injective (galProd L hζ ψ) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro τ hτ
  rw [MonoidHom.mem_ker, Prod.ext_iff] at hτ
  have h1 : τ ∈ L.fixingSubgroup := (galProd_fst_eq_one_iff L hζ ψ τ).mp hτ.1
  have h2 : τ ∈ K⟮ζ⟯.fixingSubgroup := (galProd_snd_eq_one_iff L hζ ψ τ).mp hτ.2
  have h : τ ∈ (L ⊔ K⟮ζ⟯).fixingSubgroup := by
    rw [IntermediateField.fixingSubgroup_sup]
    exact ⟨h1, h2⟩
  rw [htop, mem_fixingSubgroup_intermediateField_iff] at h
  exact Subgroup.mem_bot.mpr (AlgEquiv.ext fun x => h x IntermediateField.mem_top)

private theorem galProd_bijective [Finite C] [FiniteDimensional K M] [IsGalois K M] (htop : L ⊔ K⟮ζ⟯ = ⊤)
    (hdeg : Module.finrank K M = Module.finrank K L * m.totient) : Function.Bijective (galProd L hζ ψ) := by
  classical
  refine (Nat.bijective_iff_injective_and_card _).mpr ⟨galProd_injective L hζ ψ htop, ?_⟩
  rw [Nat.card_prod, IsGalois.card_aut_eq_finrank, IsGalois.card_aut_eq_finrank, hdeg, ← Nat.card_congr ψ.toEquiv,
    Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]

private noncomputable def galEquivProd [Finite C] [FiniteDimensional K M] [IsGalois K M] (htop : L ⊔ K⟮ζ⟯ = ⊤)
    (hdeg : Module.finrank K M = Module.finrank K L * m.totient) : (M ≃ₐ[K] M) ≃* (L ≃ₐ[K] L) × C :=
  MulEquiv.ofBijective (galProd L hζ ψ) (galProd_bijective L hζ ψ htop hdeg)

private theorem galEquivProd_apply [Finite C] [FiniteDimensional K M] [IsGalois K M] (htop : L ⊔ K⟮ζ⟯ = ⊤)
    (hdeg : Module.finrank K M = Module.finrank K L * m.totient) (τ : M ≃ₐ[K] M) :
    galEquivProd L hζ ψ htop hdeg τ = galProd L hζ ψ τ := rfl

private noncomputable def auxField (H : Subgroup ((L ≃ₐ[K] L) × C)) : IntermediateField K M :=
  fixedField (H.comap (galProd L hζ ψ))

variable [FiniteDimensional K M]

private theorem fixingSubgroup_auxField (H : Subgroup ((L ≃ₐ[K] L) × C)) :
    (auxField L hζ ψ H).fixingSubgroup = H.comap (galProd L hζ ψ) :=
  fixingSubgroup_fixedField _

private theorem mem_fixingSubgroup_auxField {H : Subgroup ((L ≃ₐ[K] L) × C)} {τ : M ≃ₐ[K] M} (h : galProd L hζ ψ τ ∈ H) :
    τ ∈ (auxField L hζ ψ H).fixingSubgroup := by
  rw [fixingSubgroup_auxField]
  exact h

variable [IsGalois K M]

private theorem auxField_sup_adjoin_eq_top (htop : L ⊔ K⟮ζ⟯ = ⊤) {H : Subgroup ((L ≃ₐ[K] L) × C)}
    (hH : H ⊓ (⊤ : Subgroup (L ≃ₐ[K] L)).prod (⊥ : Subgroup C) = ⊥) : auxField L hζ ψ H ⊔ K⟮ζ⟯ = ⊤ := by
  have hfix : (auxField L hζ ψ H ⊔ K⟮ζ⟯).fixingSubgroup = ⊥ := by
    rw [IntermediateField.fixingSubgroup_sup, fixingSubgroup_auxField, ← comap_galProd_prod_bot L hζ ψ,
      ← Subgroup.comap_inf, hH, MonoidHom.comap_bot, (MonoidHom.ker_eq_bot_iff _).mpr (galProd_injective L hζ ψ htop)]
  rw [← IsGalois.fixedField_fixingSubgroup (auxField L hζ ψ H ⊔ K⟮ζ⟯), hfix, IntermediateField.fixedField_bot]

private theorem adjoin_auxField_eq_top (htop : L ⊔ K⟮ζ⟯ = ⊤) {H : Subgroup ((L ≃ₐ[K] L) × C)}
    (hH : H ⊓ (⊤ : Subgroup (L ≃ₐ[K] L)).prod (⊥ : Subgroup C) = ⊥) :
    IntermediateField.adjoin (auxField L hζ ψ H) ({ζ} : Set M) = ⊤ := by
  apply IntermediateField.restrictScalars_injective K
  rw [restrictScalars_adjoin, restrictScalars_top, adjoin_union, adjoin_self]
  exact auxField_sup_adjoin_eq_top L hζ ψ htop hH

private theorem auxField_inf_eq_bot [Finite C] (htop : L ⊔ K⟮ζ⟯ = ⊤) (hdeg : Module.finrank K M = Module.finrank K L * m.totient)
    {H : Subgroup ((L ≃ₐ[K] L) × C)} (hH : H ⊔ (⊥ : Subgroup (L ≃ₐ[K] L)).prod (⊤ : Subgroup C) = ⊤) :
    auxField L hζ ψ H ⊓ L = ⊥ := by
  have hsup : H.comap (galProd L hζ ψ) ⊔ L.fixingSubgroup = ⊤ := by
    rw [← comap_galProd_bot_prod L hζ ψ, Subgroup.comap_sup_eq (galProd L hζ ψ) _ _ (galProd_bijective L hζ ψ htop hdeg).2,
      hH, Subgroup.comap_top]
  rw [eq_bot_iff, ← IsGalois.fixedField_top (F := K) (E := M)]
  rintro x ⟨hxE, hxL⟩ ⟨g, -⟩
  have hstab : H.comap (galProd L hζ ψ) ⊔ L.fixingSubgroup ≤ MulAction.stabilizer (M ≃ₐ[K] M) x :=
    sup_le (fun τ hτ => hxE ⟨τ, hτ⟩) (fun τ hτ => (_root_.mem_fixingSubgroup_iff _).mp hτ x hxL)
  exact hstab (by rw [hsup]; exact Subgroup.mem_top g)

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

end Fold_M4aTheta_ArtinField
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

section Fold_M4aTheta_CycCharCross

p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.NumberField nonZeroDivisors IsDedekindDomain Deep.NTSupply LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin"
open scoped IsMulCommutative

namespace M4aP2

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M]
  [Algebra K M] [IsGalois K M]

open _root_.NumberField.HeightOneSpectrum _root_.IsDedekindDomain.HeightOneSpectrum in
omit [NumberField M] [IsGalois K M] in

private theorem natCast_notMem_primeAbove (q : ℕ) (v : HeightOneSpectrum (𝓞 K))
    (hq : ¬ v.asIdeal ∣ Ideal.span {(q : 𝓞 K)}) :
    (q : 𝓞 M) ∉ primeAbove K M v := by
  intro hmem
  apply hq
  have h1 : (q : 𝓞 K) ∈ (primeAbove K M v).under (𝓞 K) := by
    rw [Ideal.under, Ideal.mem_comap, map_natCast]
    exact hmem
  rw [under_primeAbove] at h1
  rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]
  exact h1

open _root_.NumberField.HeightOneSpectrum _root_.IsDedekindDomain.HeightOneSpectrum in

private theorem artinFrob_primitiveRoot {q : ℕ} [NeZero q] {ζ : M} (hζ : IsPrimitiveRoot ζ q)
    (v : HeightOneSpectrum (𝓞 K)) (hq : ¬ v.asIdeal ∣ Ideal.span {(q : 𝓞 K)}) :
    artinFrob K M v ζ = ζ ^ Ideal.absNorm v.asIdeal := by
  classical
  have hq0 : q ≠ 0 := NeZero.ne q
  have hint : IsIntegral ℤ ζ :=
    ⟨Polynomial.X ^ q - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hq0, by
      simp [hζ.pow_eq_one]⟩
  let ζO : 𝓞 M := ⟨ζ, hint⟩
  have hpow : ζO ^ q = 1 := Subtype.coe_injective (by push_cast; exact hζ.pow_eq_one)
  have H : (MulSemiringAction.toAlgHom (𝓞 K) (𝓞 M) (artinFrob K M v)).IsArithFrobAt
      (primeAbove K M v) := isArithFrobAt_artinFrob K M v
  have h2 := H.apply_of_pow_eq_one hpow (natCast_notMem_primeAbove K M q v hq)
  have hcard : Nat.card (𝓞 K ⧸ (primeAbove K M v).under (𝓞 K)) = Ideal.absNorm v.asIdeal := by
    rw [under_primeAbove, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [hcard] at h2
  have h3 := congrArg (algebraMap (𝓞 M) M) h2
  rw [map_pow] at h3
  exact h3

open _root_.NumberField.HeightOneSpectrum _root_.IsDedekindDomain.HeightOneSpectrum in

private theorem autToPow_artinFrob {q : ℕ} [NeZero q] {ζ : M} (hζ : IsPrimitiveRoot ζ q)
    (v : HeightOneSpectrum (𝓞 K)) (hq : ¬ v.asIdeal ∣ Ideal.span {(q : 𝓞 K)}) :
    hζ.autToPow K (artinFrob K M v) = normClass K q v := by
  have hact := artinFrob_primitiveRoot K M hζ v hq
  have hcop := absNorm_coprime_of_not_dvd K q v hq
  refine Units.ext ?_
  rw [normClass_coe K q v hcop]
  have hspec := hζ.autToPow_spec K (artinFrob K M v)
  have hordζ : orderOf ζ = q := hζ.eq_orderOf.symm
  have hval : ζ ^ ((Ideal.absNorm v.asIdeal : ZMod q)).val = ζ ^ Ideal.absNorm v.asIdeal := by
    rw [ZMod.val_natCast, ← hordζ]
    exact pow_mod_orderOf ζ _
  have hvals : ((hζ.autToPow K (artinFrob K M v) : ZMod q)).val
      = ((Ideal.absNorm v.asIdeal : ZMod q)).val :=
    hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (by rw [hspec, hact]; exact hval.symm)
  exact ZMod.val_injective q hvals

open _root_.NumberField.HeightOneSpectrum _root_.IsDedekindDomain.HeightOneSpectrum in

private theorem autToPow_artinSymbol {q : ℕ} [NeZero q] {ζ : M} (hζ : IsPrimitiveRoot ζ q)
    [IsMulCommutative (M ≃ₐ[K] M)] {𝔣 : Ideal (𝓞 K)}
    (hq𝔣 : Ideal.span {(q : 𝓞 K)} ∣ 𝔣) (I : coprimeToModulus K 𝔣) :
    hζ.autToPow K (artinSymbol K M 𝔣 I) = raySymbol K (normClass K q) I.1 := by
  have hunf : artinSymbol K M 𝔣 I = raySymbolHom K 𝔣 (artinFrob K M) I := rfl
  rw [hunf, raySymbolHom_apply, map_raySymbol]
  unfold raySymbol
  refine finprod_congr fun v => ?_
  by_cases hcv : FractionalIdeal.count K v
      ((I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K) = 0
  · rw [hcv, zpow_zero, zpow_zero]
  · have hv𝔣 : ¬ v.asIdeal ∣ 𝔣 := fun hdvd => hcv ((mem_coprimeToModulus_iff K).mp I.2 v hdvd)
    have hvq : ¬ v.asIdeal ∣ Ideal.span {(q : 𝓞 K)} := fun h => hv𝔣 (h.trans hq𝔣)
    simp only [Function.comp_apply]
    rw [autToPow_artinFrob K M hζ v hvq]

open _root_.NumberField.HeightOneSpectrum _root_.IsDedekindDomain.HeightOneSpectrum in

private theorem autToPow_artinSymbol_eq_normClassChar {q : ℕ} [NeZero q] {ζ : M}
    (hζ : IsPrimitiveRoot ζ q) [IsMulCommutative (M ≃ₐ[K] M)] {𝔣 : Ideal (𝓞 K)}
    (hq𝔣 : Ideal.span {(q : 𝓞 K)} ∣ 𝔣) (I : coprimeToModulus K 𝔣) :
    hζ.autToPow K (artinSymbol K M 𝔣 I)
      = normClassChar K q hq𝔣 (NarrowRayClassGroup.mk K 𝔣 I) := by
  rw [autToPow_artinSymbol K M hζ hq𝔣 I]
  unfold normClassChar
  rw [raySymbolDescend_mk, raySymbolHom_apply]

end M4aP2
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

end Fold_M4aTheta_CycCharCross
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

section Fold_M4aTheta_ArtinFrobProd

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "P2.Artin.normRaySubgroup P2.Artin.SecondInequalityCTM P2.Artin.IdeleFirstIneqDataAt P2.Artin.artinFrob"
namespace P2
p2m_export "LanglandsTunnell.P2" "Artin.normRaySubgroup Artin.SecondInequalityCTM Artin.IdeleFirstIneqDataAt Artin.artinFrob"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.NumberField IsDedekindDomain IntermediateField Polynomial"

section FrobProd

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
variable (L : IntermediateField K M) [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]
variable {m : ℕ} [NeZero m] {ζ : M} (hζ : IsPrimitiveRoot ζ m) {C : Type*} [Group C] (ψ : (ZMod m)ˣ ≃* C)

private theorem galProd_artinFrob_fst (v : HeightOneSpectrum (𝓞 K)) (hI : ((primeAbove K M v).under (𝓞 L)).inertia (L ≃ₐ[K] L) = ⊥) :
    (galProd L hζ ψ (artinFrob K M v)).1 = artinFrob K L v := by
  rw [galProd_apply_fst]
  exact restrictNormal_artinFrob K L M v hI

omit [IsMulCommutative (L ≃ₐ[K] L)] in

private theorem galProd_artinFrob_snd (v : HeightOneSpectrum (𝓞 K)) (hm : ¬ v.asIdeal ∣ Ideal.span {(m : 𝓞 K)}) :
    (galProd L hζ ψ (artinFrob K M v)).2 = ψ (M4aP2.normClass K m v) := by
  rw [galProd_apply_snd, M4aP2.autToPow_artinFrob K M hζ v hm]

private theorem galProd_artinFrob (v : HeightOneSpectrum (𝓞 K)) (hI : ((primeAbove K M v).under (𝓞 L)).inertia (L ≃ₐ[K] L) = ⊥)
    (hm : ¬ v.asIdeal ∣ Ideal.span {(m : 𝓞 K)}) :
    galProd L hζ ψ (artinFrob K M v) = (artinFrob K L v, ψ (M4aP2.normClass K m v)) :=
  Prod.ext (galProd_artinFrob_fst K M L hζ ψ v hI) (galProd_artinFrob_snd K M L hζ ψ v hm)

end FrobProd
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

section DegreeOne

attribute [local instance] Ideal.Quotient.field

variable {K M : Type*} [Field K] [Field M] [Algebra K M]
variable (E : IntermediateField K M)

private theorem smul_fixingSubgroupEquiv (τ : E.fixingSubgroup) (x : 𝓞 M) :
    (E.fixingSubgroupEquiv τ : M ≃ₐ[E] M) • x = (τ : M ≃ₐ[K] M) • x :=
  RingOfIntegers.ext rfl

private theorem isMulCommutative_gal_intermediateField [IsMulCommutative (M ≃ₐ[K] M)] : IsMulCommutative (M ≃ₐ[E] M) :=
  ⟨⟨fun a b => by
    have h := IsMulCommutative.is_comm.comm (a.restrictScalars K) (b.restrictScalars K)
    ext x
    exact AlgEquiv.congr_fun h x⟩⟩

variable {E}
variable [NumberField K] [NumberField M] [IsGalois K M]

private theorem card_quot_under_eq_of_fix {τ : M ≃ₐ[K] M} (hτ : τ ∈ E.fixingSubgroup) (Q : Ideal (𝓞 M)) [Q.IsMaximal]
    (H : IsArithFrobAt (𝓞 K) τ Q) :
    Nat.card (𝓞 E ⧸ Q.under (𝓞 E)) = Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) := by
  classical
  haveI hP : (Q.under (𝓞 E)).IsMaximal := Ideal.IsMaximal.under (𝓞 E) Q
  haveI hp : (Q.under (𝓞 K)).IsMaximal := Ideal.IsMaximal.under (𝓞 K) Q
  have hpP : (Q.under (𝓞 E)).under (𝓞 K) = Q.under (𝓞 K) := Ideal.under_under Q
  haveI : (Q.under (𝓞 E)).LiesOver (Q.under (𝓞 K)) := ⟨hpP.symm⟩
  have hPne : Q.under (𝓞 E) ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField E)
  have hpne : Q.under (𝓞 K) ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hp (RingOfIntegers.not_isField K)
  haveI : Finite (𝓞 E ⧸ Q.under (𝓞 E)) := Ideal.finiteQuotientOfFreeOfNeBot _ hPne
  haveI : Finite (𝓞 K ⧸ Q.under (𝓞 K)) := Ideal.finiteQuotientOfFreeOfNeBot _ hpne
  set q := Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) with hqdef
  have hq1 : 1 < q := Finite.one_lt_card

  have hge : q ≤ Nat.card (𝓞 E ⧸ Q.under (𝓞 E)) :=
    Nat.card_le_card_of_injective _ (algebraMap (𝓞 K ⧸ Q.under (𝓞 K)) (𝓞 E ⧸ Q.under (𝓞 E))).injective

  have hfix : ∀ a : 𝓞 E, τ • algebraMap (𝓞 E) (𝓞 M) a = algebraMap (𝓞 E) (𝓞 M) a := fun a =>
    RingOfIntegers.ext ((mem_fixingSubgroup_intermediateField_iff E τ).mp hτ _ (a : E).2)
  have hroot : ∀ y : 𝓞 E ⧸ Q.under (𝓞 E), y ^ q = y := by
    intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← map_pow, eq_comm, Ideal.Quotient.mk_eq_mk_iff_sub_mem, Ideal.under_def, Ideal.mem_comap, map_sub, map_pow]
    have h := H (algebraMap (𝓞 E) (𝓞 M) a)
    rw [MulSemiringAction.toAlgHom_apply, hfix] at h
    exact h
  have hle : Nat.card (𝓞 E ⧸ Q.under (𝓞 E)) ≤ q := by
    letI := Fintype.ofFinite (𝓞 E ⧸ Q.under (𝓞 E))
    have hne : (X ^ q - X : (𝓞 E ⧸ Q.under (𝓞 E))[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero _ hq1
    have hsub : (Finset.univ : Finset (𝓞 E ⧸ Q.under (𝓞 E))).val ⊆ (X ^ q - X : (𝓞 E ⧸ Q.under (𝓞 E))[X]).roots := by
      intro y _
      rw [Polynomial.mem_roots hne, Polynomial.IsRoot.def, eval_sub, eval_pow, eval_X, hroot y, sub_self]
    have h := Polynomial.card_le_degree_of_subset_roots hsub
    rwa [Finset.card_univ, FiniteField.X_pow_card_sub_X_natDegree_eq _ hq1, ← Nat.card_eq_fintype_card] at h
  exact le_antisymm hle hge

private theorem inertiaDeg_under_eq_one_of_fix {τ : M ≃ₐ[K] M} (hτ : τ ∈ E.fixingSubgroup) (Q : Ideal (𝓞 M)) [Q.IsMaximal]
    (H : IsArithFrobAt (𝓞 K) τ Q) :
    (Q.under (𝓞 K)).inertiaDeg' (Q.under (𝓞 E)) = 1 := by
  classical
  haveI hP : (Q.under (𝓞 E)).IsMaximal := Ideal.IsMaximal.under (𝓞 E) Q
  haveI hp : (Q.under (𝓞 K)).IsMaximal := Ideal.IsMaximal.under (𝓞 K) Q
  haveI : (Q.under (𝓞 E)).LiesOver (Q.under (𝓞 K)) := ⟨(Ideal.under_under Q).symm⟩
  have hPne : Q.under (𝓞 E) ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField E)
  have hpne : Q.under (𝓞 K) ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hp (RingOfIntegers.not_isField K)
  haveI : Finite (𝓞 E ⧸ Q.under (𝓞 E)) := Ideal.finiteQuotientOfFreeOfNeBot _ hPne
  haveI : Finite (𝓞 K ⧸ Q.under (𝓞 K)) := Ideal.finiteQuotientOfFreeOfNeBot _ hpne
  have hq1 : 1 < Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) := Finite.one_lt_card
  have hcard := card_quot_under_eq_of_fix hτ Q H
  have hpow := Module.natCard_eq_pow_finrank (K := 𝓞 K ⧸ Q.under (𝓞 K)) (V := 𝓞 E ⧸ Q.under (𝓞 E))
  rw [hcard] at hpow
  rw [Ideal.inertiaDeg_algebraMap]
  have h1 : Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) ^ Module.finrank (𝓞 K ⧸ Q.under (𝓞 K)) (𝓞 E ⧸ Q.under (𝓞 E))
      = Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) ^ 1 := by
    rw [pow_one]; exact hpow.symm
  exact Nat.pow_right_injective hq1 h1

private theorem relNorm_under_eq_of_fix {τ : M ≃ₐ[K] M} (hτ : τ ∈ E.fixingSubgroup) (Q : Ideal (𝓞 M)) [Q.IsMaximal]
    (H : IsArithFrobAt (𝓞 K) τ Q) :
    Ideal.relNorm (𝓞 K) (Q.under (𝓞 E)) = Q.under (𝓞 K) := by
  haveI : (Q.under (𝓞 E)).IsMaximal := Ideal.IsMaximal.under (𝓞 E) Q
  haveI : (Q.under (𝓞 K)).IsMaximal := Ideal.IsMaximal.under (𝓞 K) Q
  haveI : (Q.under (𝓞 E)).LiesOver (Q.under (𝓞 K)) := ⟨(Ideal.under_under Q).symm⟩
  rw [Ideal.relNorm_eq_pow_of_isMaximal (Q.under (𝓞 E)) (Q.under (𝓞 K)),
    ← Ideal.inertiaDeg'_eq_inertiaDeg (Q.under (𝓞 K)) (Q.under (𝓞 E)), inertiaDeg_under_eq_one_of_fix hτ Q H, pow_one]

private theorem isArithFrobAt_fixingSubgroupEquiv {τ : M ≃ₐ[K] M} (hτ : τ ∈ E.fixingSubgroup) (Q : Ideal (𝓞 M)) [Q.IsMaximal]
    (H : IsArithFrobAt (𝓞 K) τ Q) :
    IsArithFrobAt (𝓞 E) (E.fixingSubgroupEquiv ⟨τ, hτ⟩ : M ≃ₐ[E] M) Q := by
  intro x
  show (MulSemiringAction.toAlgHom (𝓞 E) (𝓞 M) (E.fixingSubgroupEquiv ⟨τ, hτ⟩ : M ≃ₐ[E] M)) x
      - x ^ Nat.card (𝓞 E ⧸ Q.under (𝓞 E)) ∈ Q
  rw [MulSemiringAction.toAlgHom_apply, smul_fixingSubgroupEquiv, card_quot_under_eq_of_fix hτ Q H]
  exact H x

private theorem fixingSubgroupEquiv_eq_artinFrob [IsMulCommutative (M ≃ₐ[K] M)] {τ : M ≃ₐ[K] M} (hτ : τ ∈ E.fixingSubgroup)
    (Q : Ideal (𝓞 M)) [Q.IsMaximal] (H : IsArithFrobAt (𝓞 K) τ Q)
    (w : HeightOneSpectrum (𝓞 E)) (hw : Q.under (𝓞 E) = w.asIdeal) (hI : Q.inertia (M ≃ₐ[E] M) = ⊥) :
    (E.fixingSubgroupEquiv ⟨τ, hτ⟩ : M ≃ₐ[E] M) = artinFrob E M w := by
  haveI := isMulCommutative_gal_intermediateField E (K := K) (M := M)
  exact eq_artinFrob_of_isArithFrobAt E M w (isArithFrobAt_fixingSubgroupEquiv hτ Q H) hw hI

end DegreeOne
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

end
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

end Fold_M4aTheta_ArtinFrobProd
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

section Fold_M4aTheta_CSc2Onto

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "P2.Artin.normRaySubgroup P2.Artin.SecondInequalityCTM P2.Artin.IdeleFirstIneqDataAt P2.Artin.artinFrob"
namespace P2
p2m_export "LanglandsTunnell.P2" "Artin.normRaySubgroup Artin.SecondInequalityCTM Artin.IdeleFirstIneqDataAt Artin.artinFrob"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.NumberField IsDedekindDomain Deep.NTSupply IntermediateField"
open scoped nonZeroDivisors IsMulCommutative

section Onto

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
  [IsMulCommutative (M ≃ₐ[K] M)]

private def NoTotallySplitSub (𝔣 : Ideal (𝓞 K)) : Prop :=
  ∀ F' : IntermediateField K M, F' ≠ ⊥ →
    ∃ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔣 ∧ ∃ x : M, x ∈ F' ∧ artinFrob K M v x ≠ x

private theorem artinFrob_mem_range_artinSymbol (𝔣 : Ideal (𝓞 K)) {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ 𝔣) :
    artinFrob K M v ∈ (artinSymbol K M 𝔣).range :=
  ⟨primeCarrier K 𝔣 v hv, by rw [primeCarrier, artinSymbol_prime K M hv]⟩

private theorem artinFrob_apply_eq_self_of_mem_fixedField (𝔣 : Ideal (𝓞 K)) {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ 𝔣)
    {x : M} (hx : x ∈ fixedField (artinSymbol K M 𝔣).range) : artinFrob K M v x = x :=
  (mem_fixedField_iff _ x).mp hx _ (artinFrob_mem_range_artinSymbol K M 𝔣 hv)

private theorem _root_.LanglandsTunnell.P2.Artin.artinSymbol_surjective (𝔣 : Ideal (𝓞 K)) (h : NoTotallySplitSub K M 𝔣) : Function.Surjective (artinSymbol K M 𝔣) := by
  rw [← MonoidHom.range_eq_top]
  set H := (artinSymbol K M 𝔣).range with hH
  have hbot : fixedField H = ⊥ := by
    by_contra hne
    obtain ⟨v, hv, x, hx, hne'⟩ := h (fixedField H) hne
    exact hne' (artinFrob_apply_eq_self_of_mem_fixedField K M 𝔣 hv hx)
  rw [← fixingSubgroup_fixedField H, hbot, fixingSubgroup_bot]

p2m_export "LanglandsTunnell.P2.Artin" "artinSymbol_surjective"
private theorem exists_artinSymbol_eq (𝔣 : Ideal (𝓞 K)) (h : NoTotallySplitSub K M 𝔣) (σ : M ≃ₐ[K] M) :
    ∃ I : ↥(coprimeToModulus K 𝔣), artinSymbol K M 𝔣 I = σ :=
  artinSymbol_surjective K M 𝔣 h σ

omit [IsMulCommutative (M ≃ₐ[K] M)] in

private theorem NoTotallySplitSub.of_dvd {𝔣 𝔣' : Ideal (𝓞 K)} (hd : 𝔣 ∣ 𝔣') (h : NoTotallySplitSub K M 𝔣') : NoTotallySplitSub K M 𝔣 := by
  intro F' hF'
  obtain ⟨v, hv, x, hx, hne⟩ := h F' hF'
  exact ⟨v, fun hv𝔣 => hv (dvd_trans hv𝔣 hd), x, hx, hne⟩

end Onto
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

end
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

end Fold_M4aTheta_CSc2Onto
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

section Fold_M4aTheta_ArtinPincer

noncomputable section

p2m_open "Deep.NTSupply NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.NumberField IsDedekindDomain"
open scoped nonZeroDivisors

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "P2.Artin.normRaySubgroup P2.Artin.SecondInequalityCTM P2.Artin.IdeleFirstIneqDataAt P2.Artin.artinFrob"
namespace P2
p2m_export "LanglandsTunnell.P2" "Artin.normRaySubgroup Artin.SecondInequalityCTM Artin.IdeleFirstIneqDataAt Artin.artinFrob"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

section Pincer

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]

p2m_open "HeckeCharacter P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.HeckeCharacter"

omit [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] in

private theorem index_normRaySubgroup_eq_card (𝔣 : Ideal (𝓞 K))
    (hCSb : SecondInequalityCTM K L 𝔣) (hCSc1 : FirstInequalityCTM K L 𝔣) :
    (normRaySubgroup K L 𝔣).index = Nat.card (L ≃ₐ[K] L) :=
  Nat.dvd_antisymm hCSb hCSc1

private theorem ker_artinSymbol_eq_normRaySubgroup (𝔣 : Ideal (𝓞 K))
    (hle : normRaySubgroup K L 𝔣 ≤ (artinSymbol K L 𝔣).ker)
    (h : NoTotallySplitSub K L 𝔣)
    (hCSb : SecondInequalityCTM K L 𝔣) :
    (artinSymbol K L 𝔣).ker = normRaySubgroup K L 𝔣 := by
  have hGpos : 0 < Nat.card (L ≃ₐ[K] L) := Nat.card_pos
  haveI : (normRaySubgroup K L 𝔣).FiniteIndex :=
    ⟨fun h0 => absurd (h0 ▸ hCSb) (fun h' => hGpos.ne' (Nat.eq_zero_of_zero_dvd h'))⟩
  have hker_idx : (artinSymbol K L 𝔣).ker.index = Nat.card (L ≃ₐ[K] L) := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr (artinSymbol_surjective K L 𝔣 h),
      Nat.card_congr Subgroup.topEquiv.toEquiv]
  have heq : (normRaySubgroup K L 𝔣).index = (artinSymbol K L 𝔣).ker.index :=
    le_antisymm (hker_idx ▸ Nat.le_of_dvd hGpos hCSb) (Subgroup.index_antitone hle)
  refine le_antisymm (Subgroup.relIndex_eq_one.mp ?_) hle
  have hmul := Subgroup.relIndex_mul_index hle
  rw [heq] at hmul
  exact (mul_eq_right₀ (hker_idx ▸ hGpos.ne')).mp hmul

private theorem relNormCTM_range_le_ker_artinSymbol (𝔣 : Ideal (𝓞 K))
    (hfrob : ∀ w : HeightOneSpectrum (𝓞 L), ¬ (placeUnder' K L w).asIdeal ∣ 𝔣 →
      artinFrob K L (placeUnder' K L w) ^ (placeUnder' K L w).asIdeal.inertiaDeg' w.asIdeal = 1) :
    (relNormCTM K L 𝔣).range ≤ (artinSymbol K L 𝔣).ker := by
  rw [MonoidHom.range_le_ker_iff]
  apply MonoidHom.eq_of_eqOn_dense (closure_primeCarriers_eq_top L (modulusExt K L 𝔣))
  rintro _ ⟨w, hw, rfl⟩
  have hv : ¬ (placeUnder' K L w).asIdeal ∣ 𝔣 := fun h => hw ((placeUnder'_dvd_iff K L 𝔣 w).mp h)
  show artinSymbol K L 𝔣 (relNormCTM K L 𝔣 ⟨primeUnit L w, primeUnit_mem_coprimeToModulus L hw⟩) = 1
  rw [show relNormCTM K L 𝔣 ⟨primeUnit L w, primeUnit_mem_coprimeToModulus L hw⟩
        = (⟨primeUnit K (placeUnder' K L w), primeUnit_mem_coprimeToModulus K hv⟩
            : ↥(coprimeToModulus K 𝔣)) ^ (placeUnder' K L w).asIdeal.inertiaDeg' w.asIdeal from
      Subtype.ext (relNormCTM_primeUnit K L hw),
    map_pow, artinSymbol_prime K L hv]
  exact hfrob w hv

private theorem normRaySubgroup_le_ker_artinSymbol (𝔣 : Ideal (𝓞 K))
    (hP_ker : (narrowRaySubgroup K 𝔣).subgroupOf (coprimeToModulus K 𝔣) ≤ (artinSymbol K L 𝔣).ker)
    (hfrob : ∀ w : HeightOneSpectrum (𝓞 L), ¬ (placeUnder' K L w).asIdeal ∣ 𝔣 →
      artinFrob K L (placeUnder' K L w) ^ (placeUnder' K L w).asIdeal.inertiaDeg' w.asIdeal = 1) :
    normRaySubgroup K L 𝔣 ≤ (artinSymbol K L 𝔣).ker :=
  sup_le hP_ker (relNormCTM_range_le_ker_artinSymbol K L 𝔣 hfrob)

end Pincer
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

section Battery
p2m_open "LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin"
end Battery
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"
end
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

end Fold_M4aTheta_ArtinPincer
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

section Fold_M4aTheta_CSc2L1

set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "P2.Artin.normRaySubgroup P2.Artin.SecondInequalityCTM P2.Artin.IdeleFirstIneqDataAt P2.Artin.artinFrob"
namespace P2
p2m_export "LanglandsTunnell.P2" "Artin.normRaySubgroup Artin.SecondInequalityCTM Artin.IdeleFirstIneqDataAt Artin.artinFrob"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.NumberField IsDedekindDomain Deep.NTSupply IntermediateField"
open scoped nonZeroDivisors IsMulCommutative

section Group

variable {G : Type*} [CommGroup G] [Finite G]

private theorem isSimpleGroup_quotient_of_isCoatom {H : Subgroup G} (hH : IsCoatom H) : IsSimpleGroup (G ⧸ H) := by
  haveI : Nontrivial (G ⧸ H) := by
    rw [← Finite.one_lt_card_iff_nontrivial, ← Subgroup.index]
    exact Subgroup.one_lt_index_of_ne_top hH.1
  refine ⟨fun N _ => ?_⟩
  have hle : H ≤ N.comap (QuotientGroup.mk' H) := by
    intro x hx
    rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact one_mem N
  have hinj := Subgroup.comap_injective (QuotientGroup.mk'_surjective H)
  rcases hH.le_iff.mp hle with htop | heq
  · right
    exact hinj (htop.trans (Subgroup.comap_top _).symm)
  · left
    refine hinj (heq.trans ?_)
    rw [MonoidHom.comap_bot, QuotientGroup.ker_mk']

private theorem index_prime_of_isCoatom {H : Subgroup G} (hH : IsCoatom H) : H.index.Prime := by
  haveI := isSimpleGroup_quotient_of_isCoatom hH
  exact IsSimpleGroup.prime_card

end Group
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

section Field

variable (K M : Type*) [Field K] [Field M] [Algebra K M] [FiniteDimensional K M] [IsGalois K M]
  [IsMulCommutative (M ≃ₐ[K] M)]

omit [IsMulCommutative (M ≃ₐ[K] M)] in

private theorem finrank_fixedField_eq_index (H : Subgroup (M ≃ₐ[K] M)) : Module.finrank K (fixedField H) = H.index := by
  have h1 : Module.finrank K (fixedField H) * Module.finrank (fixedField H) M = Module.finrank K M := Module.finrank_mul_finrank K _ M
  rw [finrank_fixedField_eq_card, ← IsGalois.card_aut_eq_finrank K M] at h1
  have h2 := H.index_mul_card
  have hpos : 0 < Nat.card H := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)

private theorem exists_le_finrank_prime (F' : IntermediateField K M) (hF' : F' ≠ ⊥) :
    ∃ F : IntermediateField K M, F ≤ F' ∧ (Module.finrank K F).Prime := by
  have hne : F'.fixingSubgroup ≠ ⊤ := fun h => hF' (by
    rw [← IsGalois.fixedField_fixingSubgroup F', h, ← IntermediateField.fixingSubgroup_bot, IsGalois.fixedField_fixingSubgroup])
  obtain ⟨Hm, hcoatom, hle⟩ := (eq_top_or_exists_le_coatom F'.fixingSubgroup).resolve_left hne
  refine ⟨fixedField Hm, ?_, ?_⟩
  · calc fixedField Hm ≤ fixedField F'.fixingSubgroup := fixedField_le hle
      _ = F' := IsGalois.fixedField_fixingSubgroup F'
  · rw [finrank_fixedField_eq_index]
    exact index_prime_of_isCoatom hcoatom

omit [IsMulCommutative (M ≃ₐ[K] M)] in

private theorem isGalois_intermediateField [IsMulCommutative (M ≃ₐ[K] M)] (F : IntermediateField K M) : IsGalois K F := by
  rw [← IsGalois.fixedField_fixingSubgroup F]
  infer_instance

end Field
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

section Contract

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]

private def NoTotallySplitPrimeSub (𝔣 : Ideal (𝓞 K)) : Prop :=
  ∀ F : IntermediateField K M, (Module.finrank K F).Prime →
    ∃ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔣 ∧ ∃ x : M, x ∈ F ∧ artinFrob K M v x ≠ x

variable {K M}

private theorem NoTotallySplitSub.prime {𝔣 : Ideal (𝓞 K)} (h : NoTotallySplitSub K M 𝔣) : NoTotallySplitPrimeSub K M 𝔣 :=
  fun F hF => h F fun hbot => hF.ne_one (by rw [hbot, IntermediateField.finrank_bot])

private theorem NoTotallySplitPrimeSub.noTotallySplitSub [IsMulCommutative (M ≃ₐ[K] M)] {𝔣 : Ideal (𝓞 K)} (h : NoTotallySplitPrimeSub K M 𝔣) :
    NoTotallySplitSub K M 𝔣 := by
  intro F' hF'
  obtain ⟨F, hle, hp⟩ := exists_le_finrank_prime K M F' hF'
  obtain ⟨v, hv, x, hx, hne⟩ := h F hp
  exact ⟨v, hv, x, hle hx, hne⟩

private theorem noTotallySplitSub_iff_prime [IsMulCommutative (M ≃ₐ[K] M)] (𝔣 : Ideal (𝓞 K)) :
    NoTotallySplitSub K M 𝔣 ↔ NoTotallySplitPrimeSub K M 𝔣 :=
  ⟨NoTotallySplitSub.prime, NoTotallySplitPrimeSub.noTotallySplitSub⟩

private theorem artinSymbol_surjective_of_prime [IsMulCommutative (M ≃ₐ[K] M)] {𝔣 : Ideal (𝓞 K)} (h : NoTotallySplitPrimeSub K M 𝔣) :
    Function.Surjective (artinSymbol K M 𝔣) :=
  artinSymbol_surjective K M 𝔣 h.noTotallySplitSub

end Contract
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

end Fold_M4aTheta_CSc2L1
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

section Fold_M4aTheta_CSc2L2

set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "P2.Artin.normRaySubgroup P2.Artin.SecondInequalityCTM P2.Artin.IdeleFirstIneqDataAt P2.Artin.artinFrob"
namespace P2
p2m_export "LanglandsTunnell.P2" "Artin.normRaySubgroup Artin.SecondInequalityCTM Artin.IdeleFirstIneqDataAt Artin.artinFrob"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.NumberField IsDedekindDomain Deep.NTSupply IntermediateField HeckeCharacter P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.HeckeCharacter"
open scoped nonZeroDivisors IsMulCommutative

section Under

variable (K : Type*) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K))

private theorem not_dvd_modulusExt_of_under {E : Type*} [Field E] [NumberField E] [Algebra K E]
    {w : HeightOneSpectrum (𝓞 E)} {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ 𝔣)
    (hwv : w.asIdeal.under (𝓞 K) = v.asIdeal) : ¬ w.asIdeal ∣ modulusExt K E 𝔣 := fun h => hv (by
  rw [Ideal.dvd_iff_le] at h ⊢
  rw [← hwv]
  exact Ideal.map_le_iff_le_comap.mp h)

variable (M : Type*) [Field M] [NumberField M] [Algebra K M] (F : IntermediateField K M)

private noncomputable def primeUnderIn (v : HeightOneSpectrum (𝓞 K)) : HeightOneSpectrum (𝓞 F) :=
  ⟨(primeAbove K M v).under (𝓞 F), ((primeAbove_isMaximal K M v).under (𝓞 F)).isPrime,
    Ring.ne_bot_of_isMaximal_of_not_isField ((primeAbove_isMaximal K M v).under (𝓞 F)) (RingOfIntegers.not_isField F)⟩

private theorem primeUnderIn_asIdeal (v : HeightOneSpectrum (𝓞 K)) : (primeUnderIn K M F v).asIdeal = (primeAbove K M v).under (𝓞 F) := rfl

private theorem primeUnderIn_under (v : HeightOneSpectrum (𝓞 K)) : (primeUnderIn K M F v).asIdeal.under (𝓞 K) = v.asIdeal := by
  rw [primeUnderIn_asIdeal, Ideal.under_under, under_primeAbove]

end Under
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

section Split

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
  (F : IntermediateField K M) (𝔣 : Ideal (𝓞 K))

private theorem inertiaDeg_primeUnderIn_eq_one (v : HeightOneSpectrum (𝓞 K)) (hfix : ∀ x : M, x ∈ F → artinFrob K M v x = x) :
    v.asIdeal.inertiaDeg' (primeUnderIn K M F v).asIdeal = 1 := by
  have h := inertiaDeg_under_eq_one_of_fix (E := F) ((mem_fixingSubgroup_iff F _).mpr hfix) (primeAbove K M v)
    (isArithFrobAt_artinFrob K M v)
  rwa [under_primeAbove] at h

private theorem primeCarrier_mem_range_relNormCTM (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ 𝔣)
    (hfix : ∀ x : M, x ∈ F → artinFrob K M v x = x) : primeCarrier K 𝔣 v hv ∈ (relNormCTM K F 𝔣).range :=
  ⟨⟨primeUnit F (primeUnderIn K M F v),
      primeUnit_mem_coprimeToModulus F (not_dvd_modulusExt_of_under K 𝔣 hv (primeUnderIn_under K M F v))⟩,
    relNormCTM_primeCarrier_of_inertiaDeg_eq_one K F (not_dvd_modulusExt_of_under K 𝔣 hv (primeUnderIn_under K M F v)) hv
      (primeUnderIn_under K M F v) (inertiaDeg_primeUnderIn_eq_one K M F v hfix)⟩

private theorem normRaySubgroup_eq_top_of_fix
    (hfix : ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔣 → ∀ x : M, x ∈ F → artinFrob K M v x = x) :
    normRaySubgroup K F 𝔣 = ⊤ := by
  rw [eq_top_iff, ← closure_primeCarriers_eq_top K 𝔣, Subgroup.closure_le]
  rintro _ ⟨v, hv, rfl⟩
  exact Subgroup.mem_sup_right (primeCarrier_mem_range_relNormCTM K M F 𝔣 v hv (hfix v hv))

private theorem index_normRaySubgroup_eq_one_of_fix
    (hfix : ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔣 → ∀ x : M, x ∈ F → artinFrob K M v x = x) :
    (normRaySubgroup K F 𝔣).index = 1 := by
  rw [normRaySubgroup_eq_top_of_fix K M F 𝔣 hfix, Subgroup.index_top]

end Split
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

section Reduce

variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
  [IsMulCommutative (M ≃ₐ[K] M)]

private theorem noTotallySplitPrimeSub_of_firstInequalityCTM (𝔣 : Ideal (𝓞 K))
    (hFI : ∀ F : IntermediateField K M, (Module.finrank K F).Prime → FirstInequalityCTM K F 𝔣) :
    NoTotallySplitPrimeSub K M 𝔣 := by
  intro F hF
  by_contra hcon
  push Not at hcon
  have h1 := hFI F hF
  unfold FirstInequalityCTM at h1
  rw [index_normRaySubgroup_eq_one_of_fix K M F 𝔣 hcon, Nat.dvd_one] at h1
  haveI := isGalois_intermediateField K M F
  rw [IsGalois.card_aut_eq_finrank] at h1
  exact hF.ne_one h1

private theorem noTotallySplitSub_of_firstInequalityCTM (𝔣 : Ideal (𝓞 K))
    (hFI : ∀ F : IntermediateField K M, (Module.finrank K F).Prime → FirstInequalityCTM K F 𝔣) :
    NoTotallySplitSub K M 𝔣 :=
  (noTotallySplitPrimeSub_of_firstInequalityCTM 𝔣 hFI).noTotallySplitSub

private theorem artinSymbol_surjective_of_firstInequalityCTM (𝔣 : Ideal (𝓞 K))
    (hFI : ∀ F : IntermediateField K M, (Module.finrank K F).Prime → FirstInequalityCTM K F 𝔣) :
    Function.Surjective (artinSymbol K M 𝔣) :=
  artinSymbol_surjective_of_prime (noTotallySplitPrimeSub_of_firstInequalityCTM 𝔣 hFI)

end Reduce
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

end Fold_M4aTheta_CSc2L2
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

section Fold_M4aTheta_CSdictTransfer

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "P2.Artin.normRaySubgroup P2.Artin.SecondInequalityCTM P2.Artin.IdeleFirstIneqDataAt P2.Artin.artinFrob"
namespace P2
p2m_export "LanglandsTunnell.P2" "Artin.normRaySubgroup Artin.SecondInequalityCTM Artin.IdeleFirstIneqDataAt Artin.artinFrob"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.HeckeCharacter"
open scoped nonZeroDivisors IsMulCommutative

section Square

variable {I I' R R' : Type*} [Group I] [Group I'] [Group R] [Group R']

private theorem sup_range_eq_comap_range (C : I →* R) (C' : I' →* R') (Nrm : I' →* I) (n : R' →* R) (P : Subgroup I)
    (hsq : C.comp Nrm = n.comp C') (hC' : Function.Surjective C') (hker : C.ker ≤ P ⊔ Nrm.range) (hP : P ≤ C.ker) :
    P ⊔ Nrm.range = n.range.comap C := by
  apply le_antisymm
  · refine sup_le (fun p hp => ?_) ?_
    · rw [Subgroup.mem_comap, show C p = 1 from hP hp]
      exact one_mem _
    · rintro _ ⟨x, rfl⟩
      rw [Subgroup.mem_comap, ← MonoidHom.comp_apply, hsq, MonoidHom.comp_apply]
      exact ⟨C' x, rfl⟩
  · intro u hu
    rw [Subgroup.mem_comap] at hu
    obtain ⟨r', hr'⟩ := hu
    obtain ⟨x, rfl⟩ := hC' r'
    have hx : C (Nrm x) = C u := by rw [← MonoidHom.comp_apply, hsq, MonoidHom.comp_apply, hr']
    have hk : u * (Nrm x)⁻¹ ∈ C.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hx, mul_inv_cancel]
    have hmem : u * (Nrm x)⁻¹ * Nrm x ∈ P ⊔ Nrm.range := mul_mem (hker hk) (Subgroup.mem_sup_right ⟨x, rfl⟩)
    rwa [inv_mul_cancel_right] at hmem

private theorem index_sup_range_eq (C : I →* R) (C' : I' →* R') (Nrm : I' →* I) (n : R' →* R) (P : Subgroup I)
    (hsq : C.comp Nrm = n.comp C') (hC : Function.Surjective C) (hC' : Function.Surjective C')
    (hker : C.ker ≤ P ⊔ Nrm.range) (hP : P ≤ C.ker) :
    (P ⊔ Nrm.range).index = n.range.index := by
  rw [sup_range_eq_comap_range C C' Nrm n P hsq hC' hker hP]
  exact (n.range).index_comap_of_surjective hC

end Square
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

section IdealSide

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private theorem normRaySubgroup_eq_comap (𝔣 : Ideal (𝓞 K)) :
    normRaySubgroup K L 𝔣 = (relNormRCG K L 𝔣).range.comap (NarrowRayClassGroup.mk K 𝔣) := by
  refine sup_range_eq_comap_range (NarrowRayClassGroup.mk K 𝔣) (NarrowRayClassGroup.mk L (modulusExt K L 𝔣))
    (relNormCTM K L 𝔣) (relNormRCG K L 𝔣) _ (MonoidHom.ext fun Y => mk_relNormCTM K L Y) (QuotientGroup.mk'_surjective _)
    (fun x hx => Subgroup.mem_sup_left ?_) (fun x hx => ?_)
  · rwa [MonoidHom.mem_ker, NarrowRayClassGroup.mk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
  · rw [MonoidHom.mem_ker, NarrowRayClassGroup.mk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact hx

private theorem normRaySubgroup_index_eq_index_range_relNormRCG (𝔣 : Ideal (𝓞 K)) :
    (normRaySubgroup K L 𝔣).index = (relNormRCG K L 𝔣).range.index := by
  rw [normRaySubgroup_eq_comap]
  exact ((relNormRCG K L 𝔣).range).index_comap_of_surjective (QuotientGroup.mk'_surjective _)

end IdealSide
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

section IdeleSide

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private abbrev _root_.LanglandsTunnell.P2.Artin.principalIdeles : Subgroup (AdeleRing (𝓞 K) K)ˣ := (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range

p2m_export "LanglandsTunnell.P2.Artin" "principalIdeles"
private theorem normRaySubgroup_index_eq_idele_index (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥)
    (Nrm : (AdeleRing (𝓞 L) L)ˣ →* (AdeleRing (𝓞 K) K)ˣ)
    (hNrm_adjuster : ∀ {u : (AdeleRing (𝓞 L) L)ˣ} {α : Lˣ},
      IsAdjuster L (modulusExt K L 𝔣) u α → IsAdjuster K 𝔣 (Nrm u) (Units.map (Algebra.norm K) α))
    (hNrm_fadContent : ∀ u : (AdeleRing (𝓞 L) L)ˣ,
      fadContentHom K (projFin K (Nrm u)) = fracRelNormUnit K L (fadContentHom L (projFin L u)))
    (hsurjK : Function.Surjective (ideleContentHom K 𝔣))
    (hsurjL : Function.Surjective (ideleContentHom L (modulusExt K L 𝔣)))
    (hkerK : (ideleContentHom K 𝔣).ker ≤ principalIdeles K ⊔ Nrm.range) :
    (normRaySubgroup K L 𝔣).index = (principalIdeles K ⊔ Nrm.range).index := by
  rw [normRaySubgroup_index_eq_index_range_relNormRCG,
    index_sup_range_eq (ideleContentHom K 𝔣) (ideleContentHom L (modulusExt K L 𝔣)) Nrm (relNormRCG K L 𝔣) (principalIdeles K)
      (ideleContentHom_comp_ideleNorm K L 𝔣 h𝔣 Nrm hNrm_adjuster hNrm_fadContent) hsurjK hsurjL hkerK ?_]
  intro u hu
  obtain ⟨α, rfl⟩ := MonoidHom.mem_range.mp hu
  rw [MonoidHom.mem_ker]
  exact ideleContentHom_principal K 𝔣 α

end IdeleSide
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

section Admissible

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

omit [NumberField K] [IsGalois K L] in

private theorem admissibleExp_pos (v : HeightOneSpectrum (𝓞 K)) : 0 < admissibleExp K v := Nat.succ_pos _

omit [NumberField L] [IsGalois K L] in

private theorem dvd_of_isAdmissibleModulus {𝔣 : Ideal (𝓞 K)} (h : IsAdmissibleModulus K L 𝔣) {v : HeightOneSpectrum (𝓞 K)}
    (hv : (primeAbove K L v).inertia (L ≃ₐ[K] L) ≠ ⊥) : v.asIdeal ∣ 𝔣 :=
  dvd_trans (dvd_pow_self _ (admissibleExp_pos K v).ne') (h.2 v hv)

omit [NumberField L] [IsGalois K L] in

private theorem inertia_eq_bot_of_isAdmissibleModulus {𝔣 : Ideal (𝓞 K)} (h : IsAdmissibleModulus K L 𝔣) (v : HeightOneSpectrum (𝓞 K))
    (hv : ¬ v.asIdeal ∣ 𝔣) : (primeAbove K L v).inertia (L ≃ₐ[K] L) = ⊥ :=
  not_ne_iff.mp fun hne => hv (dvd_of_isAdmissibleModulus K L h hne)

end Admissible
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

end
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

end Fold_M4aTheta_CSdictTransfer
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

section Fold_M4aTheta_CSdictAdmMono

set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "P2.Artin.normRaySubgroup P2.Artin.SecondInequalityCTM P2.Artin.IdeleFirstIneqDataAt P2.Artin.artinFrob"
namespace P2
p2m_export "LanglandsTunnell.P2" "Artin.normRaySubgroup Artin.SecondInequalityCTM Artin.IdeleFirstIneqDataAt Artin.artinFrob"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.NumberField IsDedekindDomain Deep.NTSupply IntermediateField"
open scoped IsMulCommutative Pointwise

section Mono

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
  [IsMulCommutative (M ≃ₐ[K] M)] (F : IntermediateField K M)

attribute [local instance] Ideal.Quotient.field

private theorem inertia_ne_bot_iff_ramificationIdxIn_ne_one (L : Type*) [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    (primeAbove K L v).inertia (L ≃ₐ[K] L) ≠ ⊥ ↔ v.asIdeal.ramificationIdxIn (𝓞 L) ≠ 1 := by
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  haveI : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  rw [← Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[K] L) v.asIdeal (primeAbove K L v), ne_eq, ne_eq,
    Subgroup.card_eq_one]

private theorem ramificationIdxIn_ne_one_of_intermediateField (v : HeightOneSpectrum (𝓞 K))
    (h : v.asIdeal.ramificationIdxIn (𝓞 F) ≠ 1) : v.asIdeal.ramificationIdxIn (𝓞 M) ≠ 1 := by
  haveI := isGalois_intermediateField K M F
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  have htower := Ideal.ramificationIdxIn_mul_ramificationIdxIn' (p := v.asIdeal) (primeAbove K F v) (F ≃ₐ[K] F) (𝓞 M)
    (M ≃ₐ[K] M) (M ≃ₐ[F] M)
  intro h1
  rw [h1] at htower
  exact h (Nat.eq_one_of_mul_eq_one_right htower)

namespace IsAdmissibleModulus
private theorem _root_.LanglandsTunnell.P2.Artin.IsAdmissibleModulus.of_intermediateField {𝔣 : Ideal (𝓞 K)} (h : IsAdmissibleModulus K M 𝔣) :
    IsAdmissibleModulus K F 𝔣 := by
  haveI := isGalois_intermediateField K M F
  refine ⟨h.1, fun v hv => h.2 v ?_⟩
  rw [inertia_ne_bot_iff_ramificationIdxIn_ne_one] at hv ⊢
  exact ramificationIdxIn_ne_one_of_intermediateField K M F v hv

end IsAdmissibleModulus
p2m_export "LanglandsTunnell.P2.Artin" "IsAdmissibleModulus.of_intermediateField"
end Mono
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

end Fold_M4aTheta_CSdictAdmMono
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

section Fold_M4aTheta_CSdictBker

set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "P2.Artin.normRaySubgroup P2.Artin.SecondInequalityCTM P2.Artin.IdeleFirstIneqDataAt P2.Artin.artinFrob"
namespace P2
p2m_export "LanglandsTunnell.P2" "Artin.normRaySubgroup Artin.SecondInequalityCTM Artin.IdeleFirstIneqDataAt Artin.artinFrob"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.HeckeCharacter WithZero"
open scoped nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]

local notation "pK" => Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)

section RayUnit

variable (𝔣 : Ideal (𝓞 K))

private def IsRayUnit (β : Kˣ) : Prop :=
  (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
      v.valuation K ((β : K) - 1) ≤ exp (-(idealMultiplicity K v 𝔣 : ℤ))) ∧
    ∀ τ : K →+* ℝ, 0 < τ (β : K)

variable {K 𝔣}

private theorem IsRayUnit.valuation_eq_one (h𝔣 : 𝔣 ≠ ⊥) {β : Kˣ} (h : IsRayUnit K 𝔣 β)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v.asIdeal ∣ 𝔣) : v.valuation K (β : K) = 1 :=
  valuation_eq_one_of_cong K h𝔣 h.1 v hv

private theorem isRayUnit_one : IsRayUnit K 𝔣 1 :=
  ⟨fun v _ => by rw [Units.val_one, sub_self, map_zero]; exact zero_le', fun τ => by rw [Units.val_one, map_one]; exact one_pos⟩

private theorem IsRayUnit.mul (h𝔣 : 𝔣 ≠ ⊥) {β β' : Kˣ} (h : IsRayUnit K 𝔣 β) (h' : IsRayUnit K 𝔣 β') : IsRayUnit K 𝔣 (β * β') := by
  refine ⟨fun v hv => ?_, fun τ => by rw [Units.val_mul, map_mul]; exact mul_pos (h.2 τ) (h'.2 τ)⟩
  have heq : ((β * β' : Kˣ) : K) - 1 = (β : K) * ((β' : K) - 1) + ((β : K) - 1) := by push_cast; ring
  rw [heq]
  refine le_trans (Valuation.map_add _ _ _) (max_le ?_ (h.1 v hv))
  rw [map_mul, h.valuation_eq_one h𝔣 v hv, one_mul]
  exact h'.1 v hv

private theorem IsRayUnit.inv (h𝔣 : 𝔣 ≠ ⊥) {β : Kˣ} (h : IsRayUnit K 𝔣 β) : IsRayUnit K 𝔣 β⁻¹ := by
  refine ⟨fun v hv => ?_, fun τ => by rw [Units.val_inv_eq_inv_val, map_inv₀]; exact inv_pos.mpr (h.2 τ)⟩
  have hβ0 : (β : K) ≠ 0 := β.ne_zero
  have heq : ((β⁻¹ : Kˣ) : K) - 1 = -(β : K)⁻¹ * ((β : K) - 1) := by
    rw [Units.val_inv_eq_inv_val]; field_simp; ring
  rw [heq, map_mul, Valuation.map_neg, map_inv₀, h.valuation_eq_one h𝔣 v hv, inv_one, one_mul]
  exact h.1 v hv

variable (K 𝔣)

private theorem exists_isRayUnit_of_mem_narrowRaySubgroup (h𝔣 : 𝔣 ≠ ⊥) {I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ}
    (hI : I ∈ narrowRaySubgroup K 𝔣) : ∃ β : Kˣ, IsRayUnit K 𝔣 β ∧ I = toPrincipalIdeal (𝓞 K) K β := by
  refine Subgroup.closure_induction (p := fun I _ => ∃ β : Kˣ, IsRayUnit K 𝔣 β ∧ I = toPrincipalIdeal (𝓞 K) K β)
    ?_ ?_ ?_ ?_ hI
  · rintro I ⟨α, hα0, hα𝔣, hpos, hIα⟩
    have hα0' : (algebraMap (𝓞 K) K α) ≠ 0 := fun h => hα0 ((map_eq_zero_iff _ (RingOfIntegers.coe_injective)).mp h)
    refine ⟨Units.mk0 _ hα0', ⟨fun v hv => ?_, fun τ => hpos τ⟩, Units.ext ?_⟩
    · rw [Units.val_mk0, show algebraMap (𝓞 K) K α - 1 = algebraMap (𝓞 K) K (α - 1) by rw [map_sub, map_one],
        HeightOneSpectrum.valuation_of_algebraMap]
      refine (v.intValuation_le_pow_iff_dvd (α - 1) _).mpr
        (dvd_trans ?_ ((Ideal.dvd_iff_le).mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hα𝔣))))
      have h𝔣0 : (Associates.mk 𝔣) ≠ 0 := Associates.mk_ne_zero.mpr (by rwa [Ne, Ideal.zero_eq_bot])
      have hirr := Associates.irreducible_mk.mpr v.irreducible
      have := (Associates.prime_pow_dvd_iff_le h𝔣0 hirr (k := idealMultiplicity K v 𝔣)).mpr le_rfl
      rwa [← Associates.mk_pow, Associates.mk_le_mk_iff_dvd] at this
    · rw [hIα, coe_toPrincipalIdeal, Units.val_mk0, FractionalIdeal.coeIdeal_span_singleton]
  · exact ⟨1, isRayUnit_one, by rw [map_one]⟩
  · rintro I J _ _ ⟨β, hβ, rfl⟩ ⟨β', hβ', rfl⟩
    exact ⟨β * β', hβ.mul h𝔣 hβ', by rw [map_mul]⟩
  · rintro I _ ⟨β, hβ, rfl⟩
    exact ⟨β⁻¹, hβ.inv h𝔣, by rw [map_inv]⟩

end RayUnit
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

section UnitIdeles

variable (𝔣 : Ideal (𝓞 K))

private theorem adele_snd_apply (u : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    ((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v = ((projFin K u : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v := by
  rw [projFin_val]

variable {K 𝔣}

private theorem mem_unitIdeles_iff (u : (AdeleRing (𝓞 K) K)ˣ) : u ∈ unitIdeles K 𝔣 ↔
    (∀ v : HeightOneSpectrum (𝓞 K), Valued.v (((projFin K u : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v) = 1) ∧
    (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
      Valued.v (((projFin K u : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v - 1) ≤ exp (-(idealMultiplicity K v 𝔣 : ℤ))) ∧
    ∀ τ : K →+* ℝ, archSign K τ u := Iff.rfl

variable (K 𝔣)

private theorem isAdjuster_one_of_mem_unitIdeles {u : (AdeleRing (𝓞 K) K)ˣ} (hu : u ∈ unitIdeles K 𝔣) : IsAdjuster K 𝔣 u 1 := by
  refine ⟨fun v hv => ?_, fun τ => ?_⟩
  · rw [map_one, inv_one, mul_one, adele_snd_apply]
    exact ⟨hu.1 v, hu.2.1 v hv⟩
  · rw [map_one, inv_one, mul_one]; exact hu.2.2 τ

private theorem fadContentHom_projFin_eq_one_of_mem_unitIdeles {u : (AdeleRing (𝓞 K) K)ˣ} (hu : u ∈ unitIdeles K 𝔣) :
    fadContentHom K (projFin K u) = 1 := by
  rw [fadContentHom_apply]
  exact finprod_eq_one_of_forall_eq_one fun v => by rw [(placeOrd_eq_zero_iff K _ v).mpr (hu.1 v), zpow_zero]

private theorem unitIdeles_le_ker (h𝔣 : 𝔣 ≠ ⊥) : unitIdeles K 𝔣 ≤ (ideleContentHom K 𝔣).ker := by
  intro u hu
  rw [MonoidHom.mem_ker, ideleContentHom_apply K h𝔣 (isAdjuster_one_of_mem_unitIdeles K 𝔣 hu)]
  refine NarrowRayClassGroup.mk_eq_one_of_mem K ?_
  have h1 : fadContentHom K (projFin K (u * (pK 1)⁻¹)) = 1 := by
    rw [map_one, inv_one, mul_one]; exact fadContentHom_projFin_eq_one_of_mem_unitIdeles K 𝔣 hu
  show fadContentHom K (projFin K (u * (pK 1)⁻¹)) ∈ narrowRaySubgroup K 𝔣
  rw [h1]; exact one_mem _

private theorem principalIdeles_le_ker : principalIdeles K ≤ (ideleContentHom K 𝔣).ker := by
  rintro _ ⟨α, rfl⟩
  rw [MonoidHom.mem_ker]
  exact ideleContentHom_principal K 𝔣 α

end UnitIdeles
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

section Ker

variable (𝔣 : Ideal (𝓞 K))

private theorem coe_sub_one_adicCompletion (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    (((x - 1 : K)) : v.adicCompletion K) = (x : v.adicCompletion K) - 1 := by
  have h : ∀ y : K, (y : v.adicCompletion K) = algebraMap K (v.adicCompletion K) y := fun y => by
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]; rfl
  rw [h, h, map_sub, map_one]

private theorem valued_eq_of_fadContentHom_eq {X Y : (FiniteAdeleRing (𝓞 K) K)ˣ} (h : fadContentHom K X = fadContentHom K Y)
    (v : HeightOneSpectrum (𝓞 K)) :
    Valued.v ((X : FiniteAdeleRing (𝓞 K) K) v) = Valued.v ((Y : FiniteAdeleRing (𝓞 K) K) v) := by
  have hc := congrArg (fun I : (FractionalIdeal (𝓞 K)⁰ K)ˣ => FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K)) h
  simp only [count_fadContentHom] at hc
  unfold placeOrd at hc
  rw [neg_inj] at hc
  rw [← exp_log (valued_ne_zero_of_unit K X v), ← exp_log (valued_ne_zero_of_unit K Y v), hc]

private theorem ker_ideleContentHom_eq (h𝔣 : 𝔣 ≠ ⊥) :
    (ideleContentHom K 𝔣).ker = principalIdeles K ⊔ unitIdeles K 𝔣 := by
  refine le_antisymm (fun u hu => ?_) (sup_le (principalIdeles_le_ker K 𝔣) (unitIdeles_le_ker K 𝔣 h𝔣))
  obtain ⟨α, hα⟩ := exists_isAdjuster K h𝔣 u
  rw [MonoidHom.mem_ker, ideleContentHom_apply K h𝔣 hα, NarrowRayClassGroup.mk, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hu
  obtain ⟨β, hβ, hcβ⟩ := exists_isRayUnit_of_mem_narrowRaySubgroup K 𝔣 h𝔣 hu

  have hcont : fadContentHom K (projFin K (u * (pK α)⁻¹)) = fadContentHom K (projFin K (pK β)) := by
    rw [projFin_principal, fadContentHom_unitEmbedding]; exact hcβ
  set w : (AdeleRing (𝓞 K) K)ˣ := u * (pK α)⁻¹ * (pK β)⁻¹ with hw
  have hw_mem : w ∈ unitIdeles K 𝔣 := by
    have hval : ∀ v : HeightOneSpectrum (𝓞 K),
        Valued.v (((projFin K (u * (pK α)⁻¹) : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v) =
          Valued.v (((projFin K (pK β) : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v) :=
      valued_eq_of_fadContentHom_eq K hcont
    have hβv : ∀ v : HeightOneSpectrum (𝓞 K),
        ((projFin K (pK β) : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v = ((β : K) : v.adicCompletion K) := by
      intro v; rw [projFin_principal]; rfl
    have hβ1 : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 → Valued.v (((β : K) : v.adicCompletion K)) = 1 := by
      intro v hv; rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; exact hβ.valuation_eq_one h𝔣 v hv
    have hβc : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
        Valued.v (((β : K) : v.adicCompletion K) - 1) ≤ exp (-(idealMultiplicity K v 𝔣 : ℤ)) := by
      intro v hv
      rw [← coe_sub_one_adicCompletion, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact hβ.1 v hv
    have hβ0 : ∀ v : HeightOneSpectrum (𝓞 K), Valued.v (((β : K) : v.adicCompletion K)) ≠ 0 := by
      intro v; rw [← hβv]; exact valued_ne_zero_of_unit K _ v
    refine ⟨fun v => ?_, fun v hv => ?_, fun τ => ?_⟩
    · rw [hw, map_mul, Units.val_mul, fad_mul_apply, map_mul, map_inv, fad_units_inv_apply, map_inv₀, hval v, hβv,
        mul_inv_cancel₀ (hβ0 v)]
    · rw [hw, map_mul, Units.val_mul, fad_mul_apply, map_inv, fad_units_inv_apply, hβv]
      have hca := (hα.cong v hv).2
      rw [adele_snd_apply] at hca
      exact unit_cong_div K hca (hβ1 v hv) (hβc v hv)
    · rw [hw, archSign_mul, archSign_inv, archSign_principal]
      exact iff_of_true (hα.sign τ) (hβ.2 τ)
  have hu_eq : u = pK (α * β) * w := by
    have hw' : w = (pK β)⁻¹ * ((pK α)⁻¹ * u) := by rw [hw, mul_comm (u * (pK α)⁻¹), mul_comm u]
    rw [hw', map_mul, mul_assoc, mul_inv_cancel_left, mul_inv_cancel_left]
  rw [hu_eq]
  exact Subgroup.mul_mem_sup ⟨α * β, rfl⟩ hw_mem

private theorem ker_ideleContentHom_le_of_unitIdeles_le (h𝔣 : 𝔣 ≠ ⊥) {N : Subgroup (AdeleRing (𝓞 K) K)ˣ}
    (hN : unitIdeles K 𝔣 ≤ N) : (ideleContentHom K 𝔣).ker ≤ principalIdeles K ⊔ N := by
  rw [ker_ideleContentHom_eq K 𝔣 h𝔣]; exact sup_le_sup_left hN _

end Ker
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

end Fold_M4aTheta_CSdictBker
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

section Fold_M4aTheta_CSdictBsurj

set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "P2.Artin.normRaySubgroup P2.Artin.SecondInequalityCTM P2.Artin.IdeleFirstIneqDataAt P2.Artin.artinFrob"
namespace P2
p2m_export "LanglandsTunnell.P2" "Artin.normRaySubgroup Artin.SecondInequalityCTM Artin.IdeleFirstIneqDataAt Artin.artinFrob"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.HeckeCharacter WithZero"
open scoped nonZeroDivisors

section Uniformizer

variable (K : Type*) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private noncomputable def unifAt : v.adicCompletion K := ((v.valuation_exists_uniformizer K).choose : K)

private theorem valued_unifAt : Valued.v (unifAt K v) = exp (-1 : ℤ) := by
  unfold unifAt
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact (v.valuation_exists_uniformizer K).choose_spec

private theorem unifAt_ne_zero : unifAt K v ≠ 0 := fun h => by
  have h1 := valued_unifAt K v
  rw [h, map_zero] at h1
  exact exp_ne_zero h1.symm

private theorem isUnit_mulSingle (x : v.adicCompletion K) (hx : x ≠ 0) [DecidableEq (HeightOneSpectrum (𝓞 K))] :
    IsUnit (show FiniteAdeleRing (𝓞 K) K from
      RestrictedProduct.mulSingle (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletionIntegers K) v x) := by
  rw [FiniteAdeleRing.isUnit_iff]
  refine ⟨fun w => ?_, ?_⟩
  · show Pi.mulSingle (M := fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K) v x w ≠ 0
    by_cases h : w = v
    · subst h; rw [Pi.mulSingle_eq_same]; exact hx
    · rw [Pi.mulSingle_eq_of_ne h]; exact one_ne_zero
  · filter_upwards [show ({v}ᶜ : Set (HeightOneSpectrum (𝓞 K))) ∈ Filter.cofinite by simp] with w hw
    show Valued.v (Pi.mulSingle (M := fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K) v x w) = 1
    rw [Pi.mulSingle_eq_of_ne (by simpa using hw), map_one]

open scoped Classical in

private noncomputable def uniformizerFad : (FiniteAdeleRing (𝓞 K) K)ˣ :=
  (isUnit_mulSingle K v (unifAt K v) (unifAt_ne_zero K v)).unit

open scoped Classical in
private theorem uniformizerFad_apply (w : HeightOneSpectrum (𝓞 K)) :
    ((uniformizerFad K v : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) w =
      Pi.mulSingle (M := fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K) v (unifAt K v) w := by
  unfold uniformizerFad
  rw [IsUnit.unit_spec]
  rfl

open scoped Classical in
private theorem uniformizerFad_apply_self :
    ((uniformizerFad K v : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v = unifAt K v := by
  rw [uniformizerFad_apply, Pi.mulSingle_eq_same]

open scoped Classical in
private theorem uniformizerFad_apply_of_ne {w : HeightOneSpectrum (𝓞 K)} (hw : w ≠ v) :
    ((uniformizerFad K v : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) w = 1 := by
  rw [uniformizerFad_apply, Pi.mulSingle_eq_of_ne hw]

private noncomputable def uniformizerIdele : (AdeleRing (𝓞 K) K)ˣ where
  val := (1, (uniformizerFad K v : FiniteAdeleRing (𝓞 K) K))
  inv := (1, ((uniformizerFad K v)⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ))
  val_inv := Prod.ext (one_mul 1) (uniformizerFad K v).mul_inv
  inv_val := Prod.ext (one_mul 1) (uniformizerFad K v).inv_mul

private theorem uniformizerIdele_fst : ((uniformizerIdele K v : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 = 1 := rfl

private theorem uniformizerIdele_snd :
    ((uniformizerIdele K v : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 = uniformizerFad K v := rfl

private theorem ideleContentHom_uniformizerIdele (𝔣 : Ideal (𝓞 K)) (hv : ¬ v.asIdeal ∣ 𝔣) :
    ideleContentHom K 𝔣 (uniformizerIdele K v) = primeClass K 𝔣 v hv := by
  refine ideleContentHom_uniformizerIdele_v2 K 𝔣 hv (uniformizerIdele K v) rfl (fun w hw => ?_) ?_ (fun w hw𝔣 => ?_)
  · rw [uniformizerIdele_snd, uniformizerFad_apply_of_ne K v hw, map_one]
  · rw [uniformizerIdele_snd, uniformizerFad_apply_self, valued_unifAt]
  · have hwv : w ≠ v := fun h => hv (h ▸ hw𝔣)
    rw [uniformizerIdele_snd, uniformizerFad_apply_of_ne K v hwv, sub_self, map_zero]
    exact zero_le'

end Uniformizer
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

section Surj

variable (K : Type*) [Field K] [NumberField K]

private theorem ideleContentHom_surjective (𝔣 : Ideal (𝓞 K)) : Function.Surjective (ideleContentHom K 𝔣) := by
  intro x
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective _ x
  have hc : c ∈ (⊤ : Subgroup ↥(coprimeToModulus K 𝔣)) := Subgroup.mem_top c
  rw [← closure_primeCarriers_eq_top K 𝔣] at hc
  refine Subgroup.closure_induction (p := fun c _ => ∃ u, ideleContentHom K 𝔣 u = QuotientGroup.mk' _ c)
    ?_ ?_ ?_ ?_ hc
  · rintro _ ⟨w, hw, rfl⟩
    exact ⟨uniformizerIdele K w, ideleContentHom_uniformizerIdele K w 𝔣 hw⟩
  · exact ⟨1, by rw [map_one, map_one]⟩
  · rintro a b _ _ ⟨u, hu⟩ ⟨u', hu'⟩
    exact ⟨u * u', by rw [map_mul, map_mul, hu, hu']⟩
  · rintro a _ ⟨u, hu⟩
    exact ⟨u⁻¹, by rw [map_inv, map_inv, hu]⟩

private theorem range_ideleContentHom (𝔣 : Ideal (𝓞 K)) : (ideleContentHom K 𝔣).range = ⊤ :=
  MonoidHom.range_eq_top.mpr (ideleContentHom_surjective K 𝔣)

end Surj
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

end Fold_M4aTheta_CSdictBsurj
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

section Fold_M4aTheta_CSdictDockVocab

set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "P2.Artin.normRaySubgroup P2.Artin.SecondInequalityCTM P2.Artin.IdeleFirstIneqDataAt P2.Artin.artinFrob"
namespace P2
p2m_export "LanglandsTunnell.P2" "Artin.normRaySubgroup Artin.SecondInequalityCTM Artin.IdeleFirstIneqDataAt Artin.artinFrob"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.NumberField IsDedekindDomain HeckeCharacter P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.HeckeCharacter"

variable (K : Type*) [Field K] [NumberField K]

private theorem principalIdeles_eq_served : principalIdeles K = M4aHerbrand.principalIdeles (𝓞 K) K := rfl

private theorem ker_ideleContentHom_eq_served (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥) :
    (ideleContentHom K 𝔣).ker = M4aHerbrand.principalIdeles (𝓞 K) K ⊔ unitIdeles K 𝔣 :=
  ker_ideleContentHom_eq K 𝔣 h𝔣

private theorem ker_ideleContentHom_le_served (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥) {N : Subgroup (AdeleRing (𝓞 K) K)ˣ}
    (hN : unitIdeles K 𝔣 ≤ N) : (ideleContentHom K 𝔣).ker ≤ M4aHerbrand.principalIdeles (𝓞 K) K ⊔ N :=
  ker_ideleContentHom_le_of_unitIdeles_le K 𝔣 h𝔣 hN

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

end Fold_M4aTheta_CSdictDockVocab
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

section Fold_M4aTheta_CSdictFirstIneq

set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "P2.Artin.normRaySubgroup P2.Artin.SecondInequalityCTM P2.Artin.IdeleFirstIneqDataAt P2.Artin.artinFrob"
namespace P2
p2m_export "LanglandsTunnell.P2" "Artin.normRaySubgroup Artin.SecondInequalityCTM Artin.IdeleFirstIneqDataAt Artin.artinFrob"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.HeckeCharacter"
open scoped nonZeroDivisors

section Assembly

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private theorem normRaySubgroup_index_eq_of_anchors (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥)
    (Nrm : (AdeleRing (𝓞 L) L)ˣ →* (AdeleRing (𝓞 K) K)ˣ)
    (hA1 : ∀ {u : (AdeleRing (𝓞 L) L)ˣ} {α : Lˣ},
      IsAdjuster L (modulusExt K L 𝔣) u α → IsAdjuster K 𝔣 (Nrm u) (Units.map (Algebra.norm K) α))
    (hA2 : ∀ u : (AdeleRing (𝓞 L) L)ˣ,
      fadContentHom K (projFin K (Nrm u)) = fracRelNormUnit K L (fadContentHom L (projFin L u)))
    (hA3 : unitIdeles K 𝔣 ≤ Nrm.range) :
    (normRaySubgroup K L 𝔣).index = (principalIdeles K ⊔ Nrm.range).index :=
  normRaySubgroup_index_eq_idele_index K L 𝔣 h𝔣 Nrm hA1 hA2 (ideleContentHom_surjective K 𝔣)
    (ideleContentHom_surjective L (modulusExt K L 𝔣)) (ker_ideleContentHom_le_of_unitIdeles_le K 𝔣 h𝔣 hA3)

variable [IsGalois K L]

private theorem firstInequalityCTM_of_idele (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥)
    (Nrm : (AdeleRing (𝓞 L) L)ˣ →* (AdeleRing (𝓞 K) K)ˣ)
    (hA1 : ∀ {u : (AdeleRing (𝓞 L) L)ˣ} {α : Lˣ},
      IsAdjuster L (modulusExt K L 𝔣) u α → IsAdjuster K 𝔣 (Nrm u) (Units.map (Algebra.norm K) α))
    (hA2 : ∀ u : (AdeleRing (𝓞 L) L)ˣ,
      fadContentHom K (projFin K (Nrm u)) = fracRelNormUnit K L (fadContentHom L (projFin L u)))
    (hA3 : unitIdeles K 𝔣 ≤ Nrm.range)
    (hH1d : Module.finrank K L ∣ (principalIdeles K ⊔ Nrm.range).index) :
    FirstInequalityCTM K L 𝔣 := by
  unfold FirstInequalityCTM
  rw [IsGalois.card_aut_eq_finrank, normRaySubgroup_index_eq_of_anchors K L 𝔣 h𝔣 Nrm hA1 hA2 hA3]
  exact hH1d

private theorem firstInequalityCTM_of_idele_served (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥)
    (Nrm : (AdeleRing (𝓞 L) L)ˣ →* (AdeleRing (𝓞 K) K)ˣ)
    (hA1 : ∀ {u : (AdeleRing (𝓞 L) L)ˣ} {α : Lˣ},
      IsAdjuster L (modulusExt K L 𝔣) u α → IsAdjuster K 𝔣 (Nrm u) (Units.map (Algebra.norm K) α))
    (hA2 : ∀ u : (AdeleRing (𝓞 L) L)ˣ,
      fadContentHom K (projFin K (Nrm u)) = fracRelNormUnit K L (fadContentHom L (projFin L u)))
    (hA3 : unitIdeles K 𝔣 ≤ Nrm.range)
    (hH1d : Module.finrank K L ∣ (M4aHerbrand.principalIdeles (𝓞 K) K ⊔ Nrm.range).index) :
    FirstInequalityCTM K L 𝔣 :=
  firstInequalityCTM_of_idele K L 𝔣 h𝔣 Nrm hA1 hA2 hA3 (principalIdeles_eq_served K ▸ hH1d)

private theorem firstInequalityCTM_of_idele_admissible (𝔣 : Ideal (𝓞 K)) (hadm : IsAdmissibleModulus K L 𝔣)
    (Nrm : (AdeleRing (𝓞 L) L)ˣ →* (AdeleRing (𝓞 K) K)ˣ)
    (hA1 : ∀ {u : (AdeleRing (𝓞 L) L)ˣ} {α : Lˣ},
      IsAdjuster L (modulusExt K L 𝔣) u α → IsAdjuster K 𝔣 (Nrm u) (Units.map (Algebra.norm K) α))
    (hA2 : ∀ u : (AdeleRing (𝓞 L) L)ˣ,
      fadContentHom K (projFin K (Nrm u)) = fracRelNormUnit K L (fadContentHom L (projFin L u)))
    (hA3 : IsAdmissibleModulus K L 𝔣 → unitIdeles K 𝔣 ≤ Nrm.range)
    (hH1d : Module.finrank K L ∣ (M4aHerbrand.principalIdeles (𝓞 K) K ⊔ Nrm.range).index) :
    FirstInequalityCTM K L 𝔣 :=
  firstInequalityCTM_of_idele_served K L 𝔣 hadm.1 Nrm hA1 hA2 (hA3 hadm) hH1d

private theorem index_normRaySubgroup_eq_finrank_of_idele (𝔣 : Ideal (𝓞 K)) (hadm : IsAdmissibleModulus K L 𝔣)
    (Nrm : (AdeleRing (𝓞 L) L)ˣ →* (AdeleRing (𝓞 K) K)ˣ)
    (hA1 : ∀ {u : (AdeleRing (𝓞 L) L)ˣ} {α : Lˣ},
      IsAdjuster L (modulusExt K L 𝔣) u α → IsAdjuster K 𝔣 (Nrm u) (Units.map (Algebra.norm K) α))
    (hA2 : ∀ u : (AdeleRing (𝓞 L) L)ˣ,
      fadContentHom K (projFin K (Nrm u)) = fracRelNormUnit K L (fadContentHom L (projFin L u)))
    (hA3 : IsAdmissibleModulus K L 𝔣 → unitIdeles K 𝔣 ≤ Nrm.range)
    (hH1d : Module.finrank K L ∣ (M4aHerbrand.principalIdeles (𝓞 K) K ⊔ Nrm.range).index)
    (hCSb : SecondInequalityCTM K L 𝔣) :
    (normRaySubgroup K L 𝔣).index = Module.finrank K L := by
  rw [index_normRaySubgroup_eq_card K L 𝔣 hCSb (firstInequalityCTM_of_idele_admissible K L 𝔣 hadm Nrm hA1 hA2 hA3 hH1d),
    IsGalois.card_aut_eq_finrank]

end Assembly
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

end Fold_M4aTheta_CSdictFirstIneq
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

section Fold_M4aTheta_CSdictOntoAssembly

set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "P2.Artin.normRaySubgroup P2.Artin.SecondInequalityCTM P2.Artin.IdeleFirstIneqDataAt P2.Artin.artinFrob"
namespace P2
p2m_export "LanglandsTunnell.P2" "Artin.normRaySubgroup Artin.SecondInequalityCTM Artin.IdeleFirstIneqDataAt Artin.artinFrob"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.HeckeCharacter IntermediateField"
open scoped nonZeroDivisors IsMulCommutative

section Onto

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
  [IsMulCommutative (M ≃ₐ[K] M)]

private theorem firstInequalityCTM_intermediateField_of_idele (F : IntermediateField K M) (𝔣 : Ideal (𝓞 K))
    (hadm : IsAdmissibleModulus K M 𝔣)
    (Nrm : (AdeleRing (𝓞 F) F)ˣ →* (AdeleRing (𝓞 K) K)ˣ)
    (hA1 : ∀ {u : (AdeleRing (𝓞 F) F)ˣ} {α : (F)ˣ},
      IsAdjuster F (modulusExt K F 𝔣) u α → IsAdjuster K 𝔣 (Nrm u) (Units.map (Algebra.norm K) α))
    (hA2 : ∀ u : (AdeleRing (𝓞 F) F)ˣ,
      fadContentHom K (projFin K (Nrm u)) = fracRelNormUnit K F (fadContentHom F (projFin F u)))
    (hA3 : IsAdmissibleModulus K F 𝔣 → unitIdeles K 𝔣 ≤ Nrm.range)
    (hH1d : Module.finrank K F ∣ (M4aHerbrand.principalIdeles (𝓞 K) K ⊔ Nrm.range).index) :
    FirstInequalityCTM K F 𝔣 :=
  haveI := isGalois_intermediateField K M F
  firstInequalityCTM_of_idele_admissible K F 𝔣 (hadm.of_intermediateField K M F) Nrm hA1 hA2 hA3 hH1d

private theorem noTotallySplitSub_of_ideleData (𝔣 : Ideal (𝓞 K)) (hadm : IsAdmissibleModulus K M 𝔣)
    (hdata : ∀ F : IntermediateField K M, (Module.finrank K F).Prime → IdeleFirstIneqData K M F 𝔣) :
    NoTotallySplitSub K M 𝔣 :=
  noTotallySplitSub_of_firstInequalityCTM 𝔣 fun F hF => by
    obtain ⟨Nrm, h1, h2, h3, h4⟩ := hdata F hF
    exact firstInequalityCTM_intermediateField_of_idele K M F 𝔣 hadm Nrm h1 h2 h3 h4

private theorem artinSymbol_surjective_of_ideleData (𝔣 : Ideal (𝓞 K)) (hadm : IsAdmissibleModulus K M 𝔣)
    (hdata : ∀ F : IntermediateField K M, (Module.finrank K F).Prime → IdeleFirstIneqData K M F 𝔣) :
    Function.Surjective (artinSymbol K M 𝔣) :=
  artinSymbol_surjective_of_firstInequalityCTM 𝔣 fun F hF => by
    obtain ⟨Nrm, h1, h2, h3, h4⟩ := hdata F hF
    exact firstInequalityCTM_intermediateField_of_idele K M F 𝔣 hadm Nrm h1 h2 h3 h4

end Onto
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

end Fold_M4aTheta_CSdictOntoAssembly
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

section Fold_M4aTheta_CSdictSecondIneq

set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "P2.Artin.normRaySubgroup P2.Artin.SecondInequalityCTM P2.Artin.IdeleFirstIneqDataAt P2.Artin.artinFrob"
namespace P2
p2m_export "LanglandsTunnell.P2" "Artin.normRaySubgroup Artin.SecondInequalityCTM Artin.IdeleFirstIneqDataAt Artin.artinFrob"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.HeckeCharacter"
open scoped nonZeroDivisors

section Dock

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private theorem fracRelNormUnit_eq_kummerNorm :
    fracRelNormUnit K L = raySymbolUnitsHom L (fun w : HeightOneSpectrum (𝓞 L) =>
      primeUnit K (w.under (𝓞 K)) ^ ((w.under (𝓞 K)).asIdeal.inertiaDeg' w.asIdeal)) := rfl

private theorem range_relNormCTM_eq (𝔣 : Ideal (𝓞 K)) :
    (relNormCTM K L 𝔣).range =
      ((coprimeToModulus L (𝔣.map (algebraMap (𝓞 K) (𝓞 L)))).map (raySymbolUnitsHom L (fun w : HeightOneSpectrum (𝓞 L) =>
        primeUnit K (w.under (𝓞 K)) ^ ((w.under (𝓞 K)).asIdeal.inertiaDeg' w.asIdeal)))).subgroupOf (coprimeToModulus K 𝔣) := by
  rw [← fracRelNormUnit_eq_kummerNorm]
  ext x
  simp only [MonoidHom.mem_range, Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨(y : (FractionalIdeal ((𝓞 L)⁰) L)ˣ), y.2, (coe_relNormCTM K L y).symm⟩
  · rintro ⟨z, hz, hzx⟩
    exact ⟨⟨z, hz⟩, Subtype.ext (by rw [coe_relNormCTM]; exact hzx)⟩

private theorem normRaySubgroup_eq_kummer (𝔣 : Ideal (𝓞 K)) :
    normRaySubgroup K L 𝔣 =
      (narrowRaySubgroup K 𝔣).subgroupOf (coprimeToModulus K 𝔣) ⊔
        ((coprimeToModulus L (𝔣.map (algebraMap (𝓞 K) (𝓞 L)))).map (raySymbolUnitsHom L (fun w : HeightOneSpectrum (𝓞 L) =>
          primeUnit K (w.under (𝓞 K)) ^ ((w.under (𝓞 K)).asIdeal.inertiaDeg' w.asIdeal)))).subgroupOf (coprimeToModulus K 𝔣) := by
  rw [normRaySubgroup, range_relNormCTM_eq]

private theorem secondInequalityCTM_of_kummer (𝔣 : Ideal (𝓞 K))
    (hH1 : ((narrowRaySubgroup K 𝔣).subgroupOf (coprimeToModulus K 𝔣) ⊔
      ((coprimeToModulus L (𝔣.map (algebraMap (𝓞 K) (𝓞 L)))).map (raySymbolUnitsHom L (fun w : HeightOneSpectrum (𝓞 L) =>
        primeUnit K (w.under (𝓞 K)) ^ ((w.under (𝓞 K)).asIdeal.inertiaDeg' w.asIdeal)))).subgroupOf (coprimeToModulus K 𝔣)).index ∣
      Nat.card (L ≃ₐ[K] L)) :
    SecondInequalityCTM K L 𝔣 := by
  unfold SecondInequalityCTM
  rwa [normRaySubgroup_eq_kummer]

variable [IsGalois K L]

private theorem index_normRaySubgroup_eq_finrank_of_kummer_idele (𝔣 : Ideal (𝓞 K)) (hadm : IsAdmissibleModulus K L 𝔣)
    (hH1 : ((narrowRaySubgroup K 𝔣).subgroupOf (coprimeToModulus K 𝔣) ⊔
      ((coprimeToModulus L (𝔣.map (algebraMap (𝓞 K) (𝓞 L)))).map (raySymbolUnitsHom L (fun w : HeightOneSpectrum (𝓞 L) =>
        primeUnit K (w.under (𝓞 K)) ^ ((w.under (𝓞 K)).asIdeal.inertiaDeg' w.asIdeal)))).subgroupOf (coprimeToModulus K 𝔣)).index ∣
      Nat.card (L ≃ₐ[K] L))
    (Nrm : (AdeleRing (𝓞 L) L)ˣ →* (AdeleRing (𝓞 K) K)ˣ)
    (hA1 : ∀ {u : (AdeleRing (𝓞 L) L)ˣ} {α : Lˣ},
      IsAdjuster L (modulusExt K L 𝔣) u α → IsAdjuster K 𝔣 (Nrm u) (Units.map (Algebra.norm K) α))
    (hA2 : ∀ u : (AdeleRing (𝓞 L) L)ˣ,
      fadContentHom K (projFin K (Nrm u)) = fracRelNormUnit K L (fadContentHom L (projFin L u)))
    (hA3 : IsAdmissibleModulus K L 𝔣 → unitIdeles K 𝔣 ≤ Nrm.range)
    (hH1d : Module.finrank K L ∣ (M4aHerbrand.principalIdeles (𝓞 K) K ⊔ Nrm.range).index) :
    (normRaySubgroup K L 𝔣).index = Module.finrank K L :=
  index_normRaySubgroup_eq_finrank_of_idele K L 𝔣 hadm Nrm hA1 hA2 hA3 hH1d (secondInequalityCTM_of_kummer K L 𝔣 hH1)

end Dock
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

end Fold_M4aTheta_CSdictSecondIneq
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

section Fold_M4aTheta_CSdictStageBAdapters

set_option autoImplicit false

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "P2.Artin.normRaySubgroup P2.Artin.SecondInequalityCTM P2.Artin.IdeleFirstIneqDataAt P2.Artin.artinFrob"
namespace P2
p2m_export "LanglandsTunnell.P2" "Artin.normRaySubgroup Artin.SecondInequalityCTM Artin.IdeleFirstIneqDataAt Artin.artinFrob"
namespace Artin
p2m_export "LanglandsTunnell.P2.Artin" "primeCarrier primeCarriers resHom admissibleExp IsAdmissibleModulus normRaySubgroup SecondInequalityCTM FirstInequalityCTM unitIdeles IdeleFirstIneqData IdeleFirstIneqDataAt primeAbove primeAbove_isMaximal under_primeAbove primeAbove_ne_bot finite_quotient_of_under_eq artinFrob isArithFrobAt_artinFrob artinSymbol artinSymbol_prime"
p2m_open "LanglandsTunnell.P2.Artin LanglandsTunnell.P2 LanglandsTunnell"

p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.HeckeCharacter IntermediateField"
open scoped nonZeroDivisors IsMulCommutative

section Top

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]

private theorem ideleFirstIneqData_iff_at (F : IntermediateField K M) (𝔣 : Ideal (𝓞 K)) :
    IdeleFirstIneqData K M F 𝔣 ↔ IdeleFirstIneqDataAt K F 𝔣 := Iff.rfl

variable [IsGalois K M]

private theorem firstInequalityCTM_of_ideleDataAt (𝔣 : Ideal (𝓞 K)) (hadm : IsAdmissibleModulus K M 𝔣)
    (h : IdeleFirstIneqDataAt K M 𝔣) : FirstInequalityCTM K M 𝔣 := by
  obtain ⟨Nrm, h1, h2, h3, h4⟩ := h
  exact firstInequalityCTM_of_idele_admissible K M 𝔣 hadm Nrm h1 h2 h3 h4

private theorem index_normRaySubgroup_eq_finrank_of_kummer_ideleDataAt (𝔣 : Ideal (𝓞 K)) (hadm : IsAdmissibleModulus K M 𝔣)
    (hH1 : ((narrowRaySubgroup K 𝔣).subgroupOf (coprimeToModulus K 𝔣) ⊔
      ((coprimeToModulus M (𝔣.map (algebraMap (𝓞 K) (𝓞 M)))).map (raySymbolUnitsHom M (fun w : HeightOneSpectrum (𝓞 M) =>
        primeUnit K (w.under (𝓞 K)) ^ ((w.under (𝓞 K)).asIdeal.inertiaDeg' w.asIdeal)))).subgroupOf (coprimeToModulus K 𝔣)).index ∣
      Nat.card (M ≃ₐ[K] M))
    (h : IdeleFirstIneqDataAt K M 𝔣) : (normRaySubgroup K M 𝔣).index = Module.finrank K M := by
  obtain ⟨Nrm, h1, h2, h3, h4⟩ := h
  exact index_normRaySubgroup_eq_finrank_of_kummer_idele K M 𝔣 hadm hH1 Nrm h1 h2 h3 h4

variable [IsMulCommutative (M ≃ₐ[K] M)]

private theorem firstInequalityCTM_prime_of_ideleData (𝔣 : Ideal (𝓞 K)) (hadm : IsAdmissibleModulus K M 𝔣)
    (hdata : ∀ F : IntermediateField K M, (Module.finrank K F).Prime → IdeleFirstIneqData K M F 𝔣) :
    ∀ F : IntermediateField K M, (Module.finrank K F).Prime → FirstInequalityCTM K F 𝔣 := by
  intro F hF
  obtain ⟨Nrm, h1, h2, h3, h4⟩ := hdata F hF
  exact firstInequalityCTM_intermediateField_of_idele K M F 𝔣 hadm Nrm h1 h2 h3 h4

private theorem exists_artinSymbol_eq_of_ideleData (𝔣 : Ideal (𝓞 K)) (hadm : IsAdmissibleModulus K M 𝔣)
    (hdata : ∀ F : IntermediateField K M, (Module.finrank K F).Prime → IdeleFirstIneqData K M F 𝔣)
    (τ : M ≃ₐ[K] M) : ∃ B : ↥(coprimeToModulus K 𝔣), artinSymbol K M 𝔣 B = τ :=
  artinSymbol_surjective_of_ideleData K M 𝔣 hadm hdata τ

end Top
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

end LanglandsTunnell.P2.Artin
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

end Fold_M4aTheta_CSdictStageBAdapters
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

section Fold_P2F_CubicAdapter

set_option autoImplicit false

p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.HeckeCharacter"
open scoped nonZeroDivisors

noncomputable section

namespace P2F
namespace CubicAdapter

variable (k E : Type*) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]

private theorem house_normRaySubgroup_eq_served (𝔣 : Ideal (𝓞 k)) :
    M4aKummer.normRaySubgroup k E 𝔣 = LanglandsTunnell.P2.Artin.normRaySubgroup k E 𝔣 :=
  (M4aKummer.normRaySubgroup_eq_frozen k E 𝔣).trans
    (LanglandsTunnell.P2.Artin.normRaySubgroup_eq_kummer k E 𝔣).symm

private theorem mem_principalIdeles_iff (x : (AdeleRing (𝓞 k) k)ˣ) :
    x ∈ M4aHerbrand.principalIdeles (𝓞 k) k ↔
      ∃ α : kˣ, Units.map (algebraMap k (AdeleRing (𝓞 k) k) : k →* AdeleRing (𝓞 k) k) α = x :=
  Iff.rfl

private theorem coprimeToModulus_bot_subsingleton :
    Subsingleton ↥(coprimeToModulus k (⊥ : Ideal (𝓞 k))) := by
  refine ⟨fun a b => ?_⟩
  have h1 : ∀ c : ↥(coprimeToModulus k (⊥ : Ideal (𝓞 k))), c = 1 := by
    rintro ⟨I, hI⟩
    apply Subtype.ext
    apply Units.ext
    show (I : FractionalIdeal ((𝓞 k)⁰) k) = ((1 : (FractionalIdeal ((𝓞 k)⁰) k)ˣ) : FractionalIdeal ((𝓞 k)⁰) k)
    rw [Units.val_one, ← FractionalIdeal.finprod_heightOneSpectrum_factorization' (K := k) I.ne_zero]
    have h0 : ∀ v : HeightOneSpectrum (𝓞 k), FractionalIdeal.count k v (I : FractionalIdeal ((𝓞 k)⁰) k) = 0 :=
      fun v => hI v (dvd_zero _)
    have hfun : (fun v : HeightOneSpectrum (𝓞 k) =>
        (v.asIdeal : FractionalIdeal ((𝓞 k)⁰) k) ^ FractionalIdeal.count k v (I : FractionalIdeal ((𝓞 k)⁰) k))
          = fun _ => 1 := by
      funext v; rw [h0 v, zpow_zero]
    rw [hfun]
    exact finprod_one
  rw [h1 a, h1 b]

private theorem index_eq_one_of_subsingleton {G : Type*} [Group G] [Subsingleton G] (H : Subgroup G) :
    H.index = 1 :=
  Subgroup.index_eq_one.mpr (eq_top_iff.mpr fun x _ => by rw [Subsingleton.elim x 1]; exact one_mem H)

private theorem map_sup_le_normRaySubgroup_map_mk (𝔣 : Ideal (𝓞 k)) (h𝔣 : 𝔣 ≠ ⊥) :
    (M4aHerbrand.principalIdeles (𝓞 k) k ⊔
        (M4aHerbrand.GenuineDescent.genuineBaseChange k E).idelicNorm.range).map (ideleContentHom k 𝔣)
      ≤ (LanglandsTunnell.P2.Artin.normRaySubgroup k E 𝔣).map (NarrowRayClassGroup.mk k 𝔣) := by
  rw [Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨α, rfl⟩ := (mem_principalIdeles_iff k x).mp hx
    exact (ideleContentHom_principal k 𝔣 α) ▸ one_mem _
  · rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
    have hsq := congrArg (fun φ : (AdeleRing (𝓞 E) E)ˣ →* NarrowRayClassGroup k 𝔣 => φ u)
      (ideleContentHom_comp_ideleNorm k E 𝔣 h𝔣
        (M4aHerbrand.GenuineDescent.genuineBaseChange k E).idelicNorm
        (fun {v α} h => isAdjuster_idelicNorm_of_isAdjuster k E 𝔣 (v := v) (α := α) h)
        (fadContentHom_projFin_idelicNorm_eq_fracRelNormUnit k E))
    simp only [MonoidHom.comp_apply] at hsq
    rw [hsq]
    obtain ⟨Y, hY⟩ := QuotientGroup.mk'_surjective
      ((narrowRaySubgroup E (modulusExt k E 𝔣)).subgroupOf (coprimeToModulus E (modulusExt k E 𝔣)))
      (ideleContentHom E (modulusExt k E 𝔣) u)
    have hY' : NarrowRayClassGroup.mk E (modulusExt k E 𝔣) Y = ideleContentHom E (modulusExt k E 𝔣) u := hY
    rw [← hY', ← mk_relNormCTM k E Y]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_sup_right (MonoidHom.mem_range.mpr ⟨Y, rfl⟩))

private theorem normRaySubgroup_index_dvd_idelicNorm_index (𝔣 : Ideal (𝓞 k)) :
    (LanglandsTunnell.P2.Artin.normRaySubgroup k E 𝔣).index ∣
      (M4aHerbrand.principalIdeles (𝓞 k) k ⊔
        (M4aHerbrand.GenuineDescent.genuineBaseChange k E).idelicNorm.range).index := by
  by_cases h𝔣 : 𝔣 = ⊥
  · subst h𝔣
    haveI := coprimeToModulus_bot_subsingleton k
    rw [index_eq_one_of_subsingleton]
    exact one_dvd _
  · rw [← house_normRaySubgroup_eq_served]
    refine M4aKummer.normRaySubgroup_index_dvd_of_idele k E 𝔣 _ ?_
    rw [house_normRaySubgroup_eq_served]
    exact map_sup_le_normRaySubgroup_map_mk k E 𝔣 h𝔣

private theorem exists_adeleBaseChange_forall_normRaySubgroup_index_dvd :
    ∃ B : M4aHerbrand.AdeleBaseChange (𝓞 k) k (𝓞 E) E, ∀ 𝔣 : Ideal (𝓞 k),
      (LanglandsTunnell.P2.Artin.normRaySubgroup k E 𝔣).index ∣
        (M4aHerbrand.principalIdeles (𝓞 k) k ⊔ B.idelicNorm.range).index :=
  ⟨M4aHerbrand.GenuineDescent.genuineBaseChange k E, normRaySubgroup_index_dvd_idelicNorm_index k E⟩

private theorem normRaySubgroup_index_dvd_of_idelicNorm_index_dvd (𝔣 : Ideal (𝓞 k)) (p : ℕ)
    (hcap : (M4aHerbrand.principalIdeles (𝓞 k) k ⊔
      (M4aHerbrand.GenuineDescent.genuineBaseChange k E).idelicNorm.range).index ∣ p) :
    (LanglandsTunnell.P2.Artin.normRaySubgroup k E 𝔣).index ∣ p :=
  dvd_trans (normRaySubgroup_index_dvd_idelicNorm_index k E 𝔣) hcap

private theorem normClassIndex_dvd_of_idelicNorm_index_dvd (𝔣 : Ideal (𝓞 k)) (p : ℕ)
    (hcap : (M4aHerbrand.principalIdeles (𝓞 k) k ⊔
      (M4aHerbrand.GenuineDescent.genuineBaseChange k E).idelicNorm.range).index ∣ p) :
    ((narrowRaySubgroup k 𝔣).subgroupOf (coprimeToModulus k 𝔣) ⊔
      ((coprimeToModulus E (𝔣.map (algebraMap (𝓞 k) (𝓞 E)))).map
        (raySymbolUnitsHom E (fun w : HeightOneSpectrum (𝓞 E) =>
          primeUnit k (w.under (𝓞 k)) ^ ((w.under (𝓞 k)).asIdeal.inertiaDeg' w.asIdeal)))).subgroupOf
        (coprimeToModulus k 𝔣)).index ∣ p := by
  rw [← LanglandsTunnell.P2.Artin.normRaySubgroup_eq_kummer]
  exact normRaySubgroup_index_dvd_of_idelicNorm_index_dvd k E 𝔣 p hcap

private theorem secondInequalityCTM_of_idelicNorm_index_dvd [IsGalois k E] (p : ℕ) (hdeg : Module.finrank k E = p)
    (𝔣 : Ideal (𝓞 k))
    (hcap : (M4aHerbrand.principalIdeles (𝓞 k) k ⊔
      (M4aHerbrand.GenuineDescent.genuineBaseChange k E).idelicNorm.range).index ∣ p) :
    LanglandsTunnell.P2.Artin.SecondInequalityCTM k E 𝔣 := by
  unfold LanglandsTunnell.P2.Artin.SecondInequalityCTM
  rw [IsGalois.card_aut_eq_finrank, hdeg]
  exact normRaySubgroup_index_dvd_of_idelicNorm_index_dvd k E 𝔣 p hcap

end P2F.CubicAdapter
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

end
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

end Fold_P2F_CubicAdapter
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

section Fold_P2F_CubicCapstone

set_option autoImplicit false

noncomputable section

p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.NumberField IsDedekindDomain"

namespace P2F
namespace CubicCapstone

section Presentation

variable (k E : Type*) [Field k] [Field E] [Algebra k E]

private theorem exists_kummer_generator [IsGalois k E] {p : ℕ} (hp : p.Prime)
    (hμ : (primitiveRoots p k).Nonempty) (hdeg : Module.finrank k E = p) :
    ∃ (α : E) (a : kˣ), α ^ p = algebraMap k E (a : k) ∧ ∀ σ : E ≃ₐ[k] E, σ α = α → σ = 1 := by
  haveI : FiniteDimensional k E := Module.finite_of_finrank_pos (by rw [hdeg]; exact hp.pos)
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsCyclic (E ≃ₐ[k] E) :=
    isCyclic_of_prime_card (p := p) (by rw [IsGalois.card_aut_eq_finrank, hdeg])
  have hK : (primitiveRoots (Module.finrank k E) k).Nonempty := by rw [hdeg]; exact hμ
  obtain ⟨α, ⟨a₀, ha₀⟩, htop⟩ :=
    exists_root_adjoin_eq_top_of_isCyclic (K := k) (L := E) (hK := hK)
  rw [hdeg] at ha₀
  have hα0 : α ≠ 0 := by
    rintro rfl
    have h1 : Module.finrank k E = 1 :=
      IntermediateField.bot_eq_top_iff_finrank_eq_one.mp
        ((IntermediateField.adjoin_simple_eq_bot_iff.mpr (zero_mem _)).symm.trans htop)
    exact hp.one_lt.ne' (hdeg.symm.trans h1)
  have ha₀0 : a₀ ≠ 0 := by
    intro h
    rw [h, map_zero] at ha₀
    exact pow_ne_zero p hα0 ha₀.symm
  refine ⟨α, Units.mk0 a₀ ha₀0, by simpa using ha₀.symm, ?_⟩
  intro σ hσ
  have hle : Algebra.adjoin k ({α} : Set E) ≤ AlgHom.equalizer (σ : E →ₐ[k] E) (AlgHom.id k E) := by
    rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe, AlgHom.mem_equalizer]
    simpa using hσ
  ext x
  have hx : x ∈ (⊤ : IntermediateField k E) := trivial
  rw [← htop] at hx
  have hx' : x ∈ Algebra.adjoin k ({α} : Set E) := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (IsAlgebraic.of_finite k α)]
    exact hx
  simpa using (AlgHom.mem_equalizer _ _ x).mp (hle hx')

private theorem radicand_not_pow [IsGalois k E] {p : ℕ} (hp : p.Prime) (hμ : (primitiveRoots p k).Nonempty)
    (hdeg : Module.finrank k E = p) (α : E) (a : kˣ) (hα : α ^ p = algebraMap k E (a : k))
    (hgen : ∀ σ : E ≃ₐ[k] E, σ α = α → σ = 1) (b : kˣ) : b ^ p ≠ a := by
  intro hb
  haveI : FiniteDimensional k E := Module.finite_of_finrank_pos (by rw [hdeg]; exact hp.pos)
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := hμ
  have hζ' : IsPrimitiveRoot ζ p := (mem_primitiveRoots hp.pos).mp hζ
  have hζE : IsPrimitiveRoot (algebraMap k E ζ) p := hζ'.map_of_injective (algebraMap k E).injective
  have hb0 : algebraMap k E (b : k) ≠ 0 := by simp
  have hba : algebraMap k E (b : k) ^ p = algebraMap k E (a : k) := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, hb]
  have hξ : (α / algebraMap k E (b : k)) ^ p = 1 := by
    rw [div_pow, hα, ← hba, div_self (pow_ne_zero _ hb0)]
  obtain ⟨i, -, hi⟩ := hζE.eq_pow_of_pow_eq_one hξ
  have hαk : α = algebraMap k E (ζ ^ i * (b : k)) := by
    rw [map_mul, map_pow, hi]
    exact (div_mul_cancel₀ α hb0).symm
  have hall : ∀ σ : E ≃ₐ[k] E, σ = 1 := fun σ => hgen σ (by rw [hαk, AlgEquiv.commutes])
  haveI : Subsingleton (E ≃ₐ[k] E) := subsingleton_of_forall_eq 1 hall
  have h1 : Nat.card (E ≃ₐ[k] E) = 1 := Nat.card_of_subsingleton 1
  rw [IsGalois.card_aut_eq_finrank, hdeg] at h1
  exact hp.one_lt.ne' h1

end Presentation
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

section BadPlaces

variable (k : Type*) [Field k] [NumberField k]

private theorem finite_valuation_ne_one (a : kˣ) :
    {v : HeightOneSpectrum (𝓞 k) | v.valuation k (a : k) ≠ 1}.Finite := by
  refine ((HeightOneSpectrum.Support.finite (𝓞 k) (a : k)).union
    (HeightOneSpectrum.Support.finite (𝓞 k) ((a⁻¹ : kˣ) : k))).subset ?_
  intro v hv
  have hv' : v.valuation k (a : k) ≠ 1 := hv
  rcases lt_or_gt_of_ne hv' with h | h
  · refine Set.mem_union_right _ ?_
    have h0 : v.valuation k (a : k) ≠ 0 := by simp
    show 1 < v.valuation k ((a⁻¹ : kˣ) : k)
    rw [Units.val_inv_eq_inv_val, map_inv₀]
    exact (one_lt_inv₀ (zero_lt_iff.mpr h0)).mpr h
  · exact Set.mem_union_left _ h

private theorem finite_natCast_mem (p : ℕ) (hp : p ≠ 0) :
    {v : HeightOneSpectrum (𝓞 k) | (p : 𝓞 k) ∈ v.asIdeal}.Finite := by
  have hpk : algebraMap (𝓞 k) k (p : 𝓞 k) ≠ 0 := by
    rw [map_natCast]; exact_mod_cast hp
  refine (finite_valuation_ne_one k (Units.mk0 _ hpk)).subset ?_
  intro v hv
  simp only [Set.mem_setOf_eq] at hv
  show v.valuation k ((Units.mk0 _ hpk : kˣ) : k) ≠ 1
  rw [Units.val_mk0, Ne, HeightOneSpectrum.valuation_eq_one_iff_notMem]
  exact not_not.mpr hv

private theorem exists_finset_bad_places (S₀ : Finset (HeightOneSpectrum (𝓞 k))) (p : ℕ) (hp : p ≠ 0) (a : kˣ) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 k)), S₀ ⊆ S ∧
      (∀ v : HeightOneSpectrum (𝓞 k), (p : 𝓞 k) ∈ v.asIdeal → v ∈ S) ∧
      (∀ v : HeightOneSpectrum (𝓞 k), v.valuation k (a : k) ≠ 1 → v ∈ S) := by
  classical
  refine ⟨S₀ ∪ (finite_natCast_mem k p hp).toFinset ∪ (finite_valuation_ne_one k a).toFinset,
    ?_, ?_, ?_⟩
  · intro v hv
    simp [hv]
  · intro v hv
    simp [hv]
  · intro v hv
    simp [hv]

end BadPlaces
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

end P2F.CubicCapstone
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.NumberField IsDedekindDomain"
open scoped Classical

namespace P2F
namespace CubicCapstone

variable (k E : Type*) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]

private def auxSetSpec (p : ℕ) (S T : Finset (HeightOneSpectrum (𝓞 k))) : Prop :=
  (∀ v ∈ T, v ∉ S) ∧
  S.card + Fintype.card (InfinitePlace k) ≤ T.card + 1 ∧
  (∀ v ∈ T, ∃ w : v.Extension (𝓞 E), Module.finrank (v.adicCompletion k) (w.1.adicCompletion E) = 1) ∧
  (∀ x : (v : HeightOneSpectrum (𝓞 k)) → (v.adicCompletion k)ˣ,
    (∀ v ∈ T, v ∉ S → Valued.v ((x v : (v.adicCompletion k)ˣ) : v.adicCompletion k) = 1) →
    ∃ s : kˣ, (∀ v : HeightOneSpectrum (𝓞 k), v ∉ S → v.valuation k (s : k) = 1) ∧
      ∀ v ∈ T, v ∉ S → ∃ c : (v.adicCompletion k)ˣ,
        x v * (Units.map (algebraMap k (v.adicCompletion k) : k →* v.adicCompletion k) s)⁻¹ = c ^ p)

section IndexAlgebra

variable {G : Type*} [CommGroup G]

private theorem inf_sup_eq_sup_inf_of_le (P Bx I : Subgroup G) (hBI : Bx ≤ I) :
    (P ⊓ I) ⊔ Bx = (P ⊔ Bx) ⊓ I := by
  refine le_antisymm ?_ ?_
  · exact sup_le (le_inf (inf_le_left.trans le_sup_left) inf_le_right) (le_inf le_sup_right hBI)
  · intro x hx
    obtain ⟨hxPB, hxI⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.mp hxPB
    have hyI : y ∈ I := by
      have h : y * z * z⁻¹ ∈ I := I.mul_mem hxI (I.inv_mem (hBI hz))
      simpa using h
    exact Subgroup.mem_sup.mpr ⟨y, Subgroup.mem_inf.mpr ⟨hy, hyI⟩, z, hz, rfl⟩

private theorem index_sup_mul_relIndex_inf (P Bx I : Subgroup G) (hBI : Bx ≤ I) (htop : P ⊔ I = ⊤) :
    (P ⊔ Bx).index * Bx.relIndex (P ⊓ I) = Bx.relIndex I := by
  have h1 : Bx.relIndex ((P ⊓ I) ⊔ Bx) * ((P ⊓ I) ⊔ Bx).relIndex I = Bx.relIndex I :=
    Subgroup.relIndex_mul_relIndex _ _ _ le_sup_right (sup_le inf_le_right hBI)
  have h2 : Bx.relIndex ((P ⊓ I) ⊔ Bx) = Bx.relIndex (P ⊓ I) := Subgroup.relIndex_sup_right (P ⊓ I) Bx
  have h3 : ((P ⊓ I) ⊔ Bx).relIndex I = (P ⊔ Bx).index := by
    rw [inf_sup_eq_sup_inf_of_le P Bx I hBI, Subgroup.inf_relIndex_right]
    have hsup : I ⊔ (P ⊔ Bx) = ⊤ := by
      rw [eq_top_iff, ← htop]
      exact sup_le (le_sup_left.trans le_sup_right) le_sup_left
    calc (P ⊔ Bx).relIndex I = (P ⊔ Bx).relIndex (I ⊔ (P ⊔ Bx)) :=
          (Subgroup.relIndex_sup_right I (P ⊔ Bx)).symm
      _ = (P ⊔ Bx).index := by rw [hsup, Subgroup.relIndex_top_right]
  rw [← h1, h2, h3]
  ring

private theorem dvd_of_mul_pow_eq_pow {p e s idx : ℕ} (hp : 0 < p) (h : idx * p ^ e = p ^ (2 * s))
    (he : 2 * s ≤ e + 1) : idx ∣ p := by
  have hdvd : idx * p ^ e ∣ p ^ e * p := by
    rw [h, ← pow_succ]
    exact pow_dvd_pow p he
  rw [mul_comm] at hdvd
  exact Nat.dvd_of_mul_dvd_mul_left (pow_pos hp e) hdvd

end IndexAlgebra
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

section Box

variable {k E}

private noncomputable def boxH (p : ℕ) (S : Finset (HeightOneSpectrum (𝓞 k))) (v : HeightOneSpectrum (𝓞 k)) :
    Subgroup (v.adicCompletion k)ˣ :=
  if v ∈ S then (powMonoidHom p : (v.adicCompletion k)ˣ →* (v.adicCompletion k)ˣ).range else ⊤

private theorem boxH_of_mem {p : ℕ} {S : Finset (HeightOneSpectrum (𝓞 k))} {v : HeightOneSpectrum (𝓞 k)} (hv : v ∈ S) :
    boxH p S v = (powMonoidHom p : (v.adicCompletion k)ˣ →* (v.adicCompletion k)ˣ).range := by
  unfold boxH; rw [if_pos hv]

private theorem boxH_of_notMem {p : ℕ} {S : Finset (HeightOneSpectrum (𝓞 k))} {v : HeightOneSpectrum (𝓞 k)}
    (hv : v ∉ S) : boxH p S v = ⊤ := by
  unfold boxH; rw [if_neg hv]

private noncomputable def boxHinf (p : ℕ) (w : InfinitePlace k) : Subgroup (w.Completion)ˣ :=
  (powMonoidHom p : (w.Completion)ˣ →* (w.Completion)ˣ).range

private noncomputable def box (p : ℕ) (S T : Finset (HeightOneSpectrum (𝓞 k))) : Subgroup (AdeleRing (𝓞 k) k)ˣ :=
  NumberField.AdeleRing.ideleBox (𝓞 k) k (↑(S ∪ T)) (boxH p S) (boxHinf p)

private theorem box_le_unitIdelesOutside (p : ℕ) (S T : Finset (HeightOneSpectrum (𝓞 k))) :
    box p S T ≤ NumberField.AdeleRing.unitIdelesOutside (𝓞 k) k (↑(S ∪ T)) :=
  NumberField.AdeleRing.ideleBox_le_unitIdelesOutside (𝓞 k) k _ _ _

private theorem box_le_range_idelicNorm [IsGalois k E] {p : ℕ} (hdeg : Module.finrank k E = p)
    (α : E) (a : kˣ) (hα : α ^ p = algebraMap k E (a : k)) (hgen : ∀ σ : E ≃ₐ[k] E, σ α = α → σ = 1)
    {S T : Finset (HeightOneSpectrum (𝓞 k))}
    (hSp : ∀ v : HeightOneSpectrum (𝓞 k), (p : 𝓞 k) ∈ v.asIdeal → v ∈ S)
    (hSa : ∀ v : HeightOneSpectrum (𝓞 k), v.valuation k (a : k) ≠ 1 → v ∈ S)
    (hT : auxSetSpec k E p S T) (B : M4aHerbrand.AdeleBaseChange (𝓞 k) k (𝓞 E) E) :
    box p S T ≤ B.idelicNorm.range := by
  obtain ⟨hTS, -, hsplit, -⟩ := hT
  unfold box
  refine M4aHerbrand.AdeleBaseChange.ideleBox_le_range_idelicNorm k E B (n := p) (by simp [hdeg]) (S ∪ T)
    (boxH p S) (boxHinf p) ?_ ?_ ?_
  · intro v hv
    rcases Finset.mem_union.mp hv with hvS | hvT
    · exact Or.inl (boxH_of_mem hvS).le
    · exact Or.inr (hsplit v hvT)
  · intro v hv w
    have hvS : v ∉ S := fun h => hv (Finset.mem_union_left T h)
    refine IsDedekindDomain.HeightOneSpectrum.Extension.inertia_eq_bot_of_pow_eq k E (a : k) α hα hgen v ?_ ?_ w
    · by_contra h
      exact hvS (hSa v h)
    · intro h
      exact hvS (hSp v h)
  · intro w _
    unfold boxHinf
    exact le_rfl

private theorem relIndex_box {p : ℕ} (hp : p.Prime) (hμ : (primitiveRoots p k).Nonempty)
    {S T : Finset (HeightOneSpectrum (𝓞 k))}
    (hSp : ∀ v : HeightOneSpectrum (𝓞 k), (p : 𝓞 k) ∈ v.asIdeal → v ∈ S) (hTS : ∀ v ∈ T, v ∉ S) :
    (box p S T).relIndex (NumberField.AdeleRing.unitIdelesOutside (𝓞 k) k (↑(S ∪ T)))
      = p ^ (2 * (S.card + Fintype.card (InfinitePlace k))) := by
  unfold box
  rw [NumberField.AdeleRing.relIndex_ideleBox_unitIdelesOutside]
  have hdisj : Disjoint S T := Finset.disjoint_left.mpr fun v hvS hvT => hTS v hvT hvS
  have hprodT : ∏ v ∈ T, (boxH p S v).index = 1 :=
    Finset.prod_eq_one fun v hv => by rw [boxH_of_notMem (hTS v hv), Subgroup.index_top]
  have hprodS : ∏ v ∈ S, (boxH p S v).index
      = ∏ v ∈ S, Nat.card ((v.adicCompletion k)ˣ ⧸
          (powMonoidHom p : (v.adicCompletion k)ˣ →* (v.adicCompletion k)ˣ).range) :=
    Finset.prod_congr rfl fun v hv => by rw [boxH_of_mem hv, Subgroup.index_eq_card]
  have hprodInf : ∏ w : InfinitePlace k, (boxHinf p w).index
      = ∏ w : InfinitePlace k, Nat.card ((w.Completion)ˣ ⧸
          (powMonoidHom p : (w.Completion)ˣ →* (w.Completion)ˣ).range) :=
    Finset.prod_congr rfl fun w _ => by unfold boxHinf; rw [Subgroup.index_eq_card]
  rw [Finset.prod_union hdisj, hprodT, mul_one, hprodS, hprodInf]
  exact NumberField.prod_natCard_units_adicCompletion_quotient_range_powMonoidHom_mul_prod_infinitePlace_eq_pow
    hp hμ S hSp

end Box
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

section Principal

variable {k}

private noncomputable abbrev diag : kˣ →* (AdeleRing (𝓞 k) k)ˣ :=
  Units.map (algebraMap k (AdeleRing (𝓞 k) k) : k →* AdeleRing (𝓞 k) k)

private theorem val_finiteUnitsComponent_diag (u : kˣ) (v : HeightOneSpectrum (𝓞 k)) :
    ((NumberField.AdeleRing.finiteUnitsComponent (𝓞 k) k v (diag u) : (v.adicCompletion k)ˣ) :
        v.adicCompletion k) = algebraMap k (v.adicCompletion k) (u : k) := by
  rfl

private theorem val_infiniteUnitsComponent_diag (u : kˣ) (w : InfinitePlace k) :
    ((NumberField.AdeleRing.infiniteUnitsComponent (𝓞 k) k w (diag u) : (w.Completion)ˣ) : w.Completion)
      = algebraMap k w.Completion (u : k) := by
  rfl

private theorem valuation_eq_one_of_pow_eq_one {p : ℕ} (hp : p ≠ 0) (v : HeightOneSpectrum (𝓞 k)) (c : k) (hc : c ≠ 0)
    (h : v.valuation k c ^ p = 1) : v.valuation k c = 1 := by
  have hne : v.valuation k c ≠ 0 := by simpa using hc
  exact (pow_eq_one_iff_left hp).mp h

private theorem diag_pow_mem_box (p : ℕ) (S T : Finset (HeightOneSpectrum (𝓞 k)))
    (c : kˣ) (hc : c ∈ (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 k))).unit k) :
    diag (c ^ p) ∈ box p S T := by
  have hcI : diag c ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 k) k (↑(S ∪ T)) := by
    have hmem : diag c ∈ M4aHerbrand.principalIdeles (𝓞 k) k ⊓
        NumberField.AdeleRing.unitIdelesOutside (𝓞 k) k (↑(S ∪ T)) := by
      rw [NumberField.AdeleRing.principalIdeles_inf_unitIdelesOutside_eq_map_unit]
      exact Subgroup.mem_map_of_mem _ hc
    exact (Subgroup.mem_inf.mp hmem).2
  have hI : diag (c ^ p) ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 k) k (↑(S ∪ T)) := by
    rw [map_pow]; exact pow_mem hcI p
  unfold box
  rw [NumberField.AdeleRing.mem_ideleBox_iff]
  refine ⟨⟨fun v hv => ?_, ?_⟩, fun w => ?_⟩
  · by_cases hvS : v ∈ S
    · rw [boxH_of_mem hvS, map_pow, map_pow]
      exact ⟨_, rfl⟩
    · rw [boxH_of_notMem hvS]; exact Subgroup.mem_top _
  · exact hI
  · unfold boxHinf
    rw [map_pow, map_pow]
    exact ⟨_, rfl⟩

private theorem exists_pow_eq_of_diag_mem_box {p : ℕ} (hp : p.Prime) (hμ : (primitiveRoots p k).Nonempty)
    {S T : Finset (HeightOneSpectrum (𝓞 k))}
    (hSp : ∀ v : HeightOneSpectrum (𝓞 k), (p : 𝓞 k) ∈ v.asIdeal → v ∈ S)
    (hScl : M4aHerbrand.principalIdeles (𝓞 k) k ⊔ NumberField.AdeleRing.unitIdelesOutside (𝓞 k) k ↑S = ⊤)
    (hsurj : ∀ x : (v : HeightOneSpectrum (𝓞 k)) → (v.adicCompletion k)ˣ,
      (∀ v ∈ T, v ∉ S → Valued.v ((x v : (v.adicCompletion k)ˣ) : v.adicCompletion k) = 1) →
      ∃ s : kˣ, (∀ v : HeightOneSpectrum (𝓞 k), v ∉ S → v.valuation k (s : k) = 1) ∧
        ∀ v ∈ T, v ∉ S → ∃ c : (v.adicCompletion k)ˣ,
          x v * (Units.map (algebraMap k (v.adicCompletion k) : k →* v.adicCompletion k) s)⁻¹ = c ^ p)
    (u : kˣ) (hu : u ∈ (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 k))).unit k) (hbox : diag u ∈ box p S T) :
    ∃ c ∈ (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 k))).unit k, c ^ p = u := by
  unfold box at hbox
  rw [NumberField.AdeleRing.mem_ideleBox_iff] at hbox
  have hunit : ∀ v : HeightOneSpectrum (𝓞 k), v ∉ S → v ∉ T → v.valuation k (u : k) = 1 := by
    intro v hvS hvT
    refine Set.unit_valuation_eq_one (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 k))) k
      (⟨u, hu⟩ : (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 k))).unit k) ?_
    simp [hvS, hvT]
  have hpowS : ∀ v ∈ S, ∃ b : v.adicCompletion k, algebraMap k (v.adicCompletion k) (u : k) = b ^ p := by
    intro v hvS
    have hv : v ∈ (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 k))) := by simp [hvS]
    have hcomp := hbox.1.1 v hv
    rw [boxH_of_mem hvS] at hcomp
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hcomp
    refine ⟨(c : v.adicCompletion k), ?_⟩
    rw [← val_finiteUnitsComponent_diag, ← hc]
    rfl
  have hpowInf : ∀ w : InfinitePlace k, w.IsReal →
      ∃ b : w.Completion, algebraMap k w.Completion (u : k) = b ^ p := by
    intro w _
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp (hbox.2 w)
    refine ⟨(c : w.Completion), ?_⟩
    rw [← val_infiniteUnitsComponent_diag, ← hc]
    rfl
  obtain ⟨c₀, hc₀⟩ := NumberField.exists_pow_eq_of_forall_mem_range_powMonoidHom k hp hμ S T hSp hScl hsurj
    (u : k) hunit hpowS hpowInf
  have hc₀0 : c₀ ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hc₀
    exact u.ne_zero hc₀
  have hcunit : ∀ v : HeightOneSpectrum (𝓞 k), v ∉ (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 k))) →
      v.valuation k c₀ = 1 := by
    intro v hv
    have hv' : v ∉ S ∧ v ∉ T := by simpa using hv
    refine valuation_eq_one_of_pow_eq_one hp.ne_zero v c₀ hc₀0 ?_
    rw [← map_pow, ← hc₀]
    exact hunit v hv'.1 hv'.2
  refine ⟨Units.mk0 c₀ hc₀0, ?_, ?_⟩
  · exact hcunit
  · ext
    simp [hc₀]

private theorem relIndex_box_principal_inf {p : ℕ} (hp : p.Prime) (hμ : (primitiveRoots p k).Nonempty)
    {S T : Finset (HeightOneSpectrum (𝓞 k))}
    (hSp : ∀ v : HeightOneSpectrum (𝓞 k), (p : 𝓞 k) ∈ v.asIdeal → v ∈ S)
    (hScl : M4aHerbrand.principalIdeles (𝓞 k) k ⊔ NumberField.AdeleRing.unitIdelesOutside (𝓞 k) k ↑S = ⊤)
    (hsurj : ∀ x : (v : HeightOneSpectrum (𝓞 k)) → (v.adicCompletion k)ˣ,
      (∀ v ∈ T, v ∉ S → Valued.v ((x v : (v.adicCompletion k)ˣ) : v.adicCompletion k) = 1) →
      ∃ s : kˣ, (∀ v : HeightOneSpectrum (𝓞 k), v ∉ S → v.valuation k (s : k) = 1) ∧
        ∀ v ∈ T, v ∉ S → ∃ c : (v.adicCompletion k)ˣ,
          x v * (Units.map (algebraMap k (v.adicCompletion k) : k →* v.adicCompletion k) s)⁻¹ = c ^ p) :
    (box p S T).relIndex (M4aHerbrand.principalIdeles (𝓞 k) k ⊓
        NumberField.AdeleRing.unitIdelesOutside (𝓞 k) k (↑(S ∪ T)))
      = p ^ (Nat.card (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 k))) + NumberField.Units.rank k + 1) := by
  rw [NumberField.AdeleRing.principalIdeles_inf_unitIdelesOutside_eq_map_unit, ← Subgroup.relIndex_comap]
  have hkey : ((box p S T).comap (diag (k := k))).subgroupOf ((↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 k))).unit k)
      = (powMonoidHom p : ((↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 k))).unit k) →*
          ((↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 k))).unit k)).range := by
    ext ⟨x, hx⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, MonoidHom.mem_range]
    constructor
    · intro hbox
      have hbox' : diag x ∈ box p S T := hbox
      obtain ⟨c, hc, hcx⟩ := exists_pow_eq_of_diag_mem_box hp hμ hSp hScl hsurj x hx hbox'
      exact ⟨⟨c, hc⟩, Subtype.ext (by simpa using hcx)⟩
    · rintro ⟨⟨c, hc⟩, hcx⟩
      have hcx' : c ^ p = x := by simpa using congrArg Subtype.val hcx
      show diag x ∈ box p S T
      rw [← hcx']
      exact diag_pow_mem_box p S T c hc
  show (((box p S T).comap (diag (k := k))).subgroupOf ((↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 k))).unit k)).index = _
  rw [hkey, Subgroup.index_eq_card]
  haveI : Finite (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 k))) := (Finset.finite_toSet _).to_subtype
  exact NumberField.natCard_sUnit_quotient_range_powMonoidHom k _ hμ

end Principal
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

section Radicand

variable {k}

private abbrev SUnitModPow (p : ℕ) (S : Finset (HeightOneSpectrum (𝓞 k))) : Type _ :=
  ((↑S : Set (HeightOneSpectrum (𝓞 k))).unit k) ⧸
    (powMonoidHom p : ((↑S : Set (HeightOneSpectrum (𝓞 k))).unit k) →*
      ((↑S : Set (HeightOneSpectrum (𝓞 k))).unit k)).range

private abbrev SUnitSpace (p : ℕ) (S : Finset (HeightOneSpectrum (𝓞 k))) : Type _ := Additive (SUnitModPow (k := k) p S)

private theorem sUnitModPow_pow_eq_one (p : ℕ) (S : Finset (HeightOneSpectrum (𝓞 k))) (q : SUnitModPow (k := k) p S) :
    q ^ p = 1 := by
  refine QuotientGroup.induction_on q fun y => ?_
  rw [← QuotientGroup.mk_pow]
  exact (QuotientGroup.eq_one_iff _).mpr (MonoidHom.mem_range.mpr ⟨y, rfl⟩)

private scoped instance sUnitSpace_module (p : ℕ) (S : Finset (HeightOneSpectrum (𝓞 k))) :
    Module (ZMod p) (SUnitSpace (k := k) p S) :=
  AddCommGroup.zmodModule (G := SUnitSpace (k := k) p S) (n := p) fun x => by
    rw [← ofMul_toMul x, ← ofMul_pow, sUnitModPow_pow_eq_one]
    rfl

private theorem mem_sUnit_iff (S : Set (HeightOneSpectrum (𝓞 k))) (x : kˣ) :
    x ∈ S.unit k ↔ ∀ v : HeightOneSpectrum (𝓞 k), v ∉ S → v.valuation k (x : k) = 1 :=
  Iff.rfl

private theorem mem_sUnit_of_pow_mem {p : ℕ} (hp : p ≠ 0) {S : Set (HeightOneSpectrum (𝓞 k))} {w : kˣ}
    (h : w ^ p ∈ S.unit k) : w ∈ S.unit k := by
  rw [mem_sUnit_iff] at h ⊢
  intro v hv
  have h1 := h v hv
  rw [Units.val_pow_eq_pow_val, map_pow] at h1
  exact valuation_eq_one_of_pow_eq_one hp v (w : k) w.ne_zero h1

private theorem exists_radicand_basis {p : ℕ} (hp : p.Prime) (hμ : (primitiveRoots p k).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 k))) (a : kˣ) (haS : a ∈ (↑S : Set (HeightOneSpectrum (𝓞 k))).unit k)
    (ha : ∀ b : kˣ, b ^ p ≠ a) :
    ∃ (t : ℕ) (u : Fin t → kˣ), (∀ j, u j ∈ (↑S : Set (HeightOneSpectrum (𝓞 k))).unit k) ∧
      t + 1 = S.card + Fintype.card (InfinitePlace k) ∧
      ∀ (e₀ : ℕ) (e : Fin t → ℕ) (w : kˣ), a ^ e₀ * ∏ j, u j ^ e j = w ^ p → (∀ j, p ∣ e j) ∧ p ∣ e₀ := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (↑S : Set (HeightOneSpectrum (𝓞 k))) := (Finset.finite_toSet S).to_subtype

  have hcardQ : Nat.card (SUnitModPow (k := k) p S)
      = p ^ (Nat.card (↑S : Set (HeightOneSpectrum (𝓞 k))) + NumberField.Units.rank k + 1) :=
    NumberField.natCard_sUnit_quotient_range_powMonoidHom k _ hμ
  have hcardV : Nat.card (SUnitSpace (k := k) p S)
      = p ^ (Nat.card (↑S : Set (HeightOneSpectrum (𝓞 k))) + NumberField.Units.rank k + 1) := by
    exact hcardQ
  haveI : Finite (SUnitSpace (k := k) p S) :=
    Nat.finite_of_card_ne_zero (by rw [hcardV]; exact pow_ne_zero _ hp.ne_zero)
  have hfinV : Module.finrank (ZMod p) (SUnitSpace (k := k) p S)
      = Nat.card (↑S : Set (HeightOneSpectrum (𝓞 k))) + NumberField.Units.rank k + 1 := by
    apply Nat.pow_right_injective hp.two_le
    have h := (Module.natCard_eq_pow_finrank (K := ZMod p) (V := SUnitSpace (k := k) p S)).symm.trans hcardV
    simpa [Nat.card_zmod] using h

  set φ : ((↑S : Set (HeightOneSpectrum (𝓞 k))).unit k) →* SUnitModPow (k := k) p S := QuotientGroup.mk' _
  set A : SUnitSpace (k := k) p S := Additive.ofMul (φ ⟨a, haS⟩) with hAdef
  have hA : A ≠ 0 := by
    intro h0
    have h1 : φ ⟨a, haS⟩ = 1 := by
      exact Additive.ofMul.injective (h0.trans ofMul_one.symm)
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp ((QuotientGroup.eq_one_iff _).mp h1)
    apply ha (b : kˣ)
    have hb' := congrArg Subtype.val hb
    simpa using hb'

  obtain ⟨W, hW⟩ := Submodule.exists_isCompl (Submodule.span (ZMod p) {A})
  have hrank : Module.finrank (ZMod p) W + 1
      = Nat.card (↑S : Set (HeightOneSpectrum (𝓞 k))) + NumberField.Units.rank k + 1 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span (ZMod p) {A}) W
    have h1 : Module.finrank (ZMod p) (Submodule.span (ZMod p) {A}) = 1 := by
      exact finrank_span_singleton hA
    rw [hW.sup_eq_top, hW.inf_eq_bot] at h
    simp only [finrank_top, finrank_bot, add_zero] at h
    omega
  let bW := Module.finBasis (ZMod p) W

  have hrep : ∀ j, ∃ y : ((↑S : Set (HeightOneSpectrum (𝓞 k))).unit k),
      φ y = Additive.toMul ((bW j : W) : SUnitSpace (k := k) p S) :=
    fun j => QuotientGroup.mk'_surjective _ (Additive.toMul ((bW j : W) : SUnitSpace (k := k) p S))
  choose y hy using hrep
  refine ⟨Module.finrank (ZMod p) W, fun j => ((y j : ((↑S : Set (HeightOneSpectrum (𝓞 k))).unit k)) : kˣ),
    fun j => (y j).2, ?_, ?_⟩
  ·
    have hSc : Nat.card (↑S : Set (HeightOneSpectrum (𝓞 k))) = S.card := by
      (rw [Finset.coe_sort_coe, Nat.card_eq_finsetCard])
    have hinf : 0 < Fintype.card (InfinitePlace k) := Fintype.card_pos
    rw [hSc, NumberField.Units.rank] at hrank
    rw [hrank]
    omega
  · intro e₀ e w hrel

    have hwU : w ∈ (↑S : Set (HeightOneSpectrum (𝓞 k))).unit k := by
      refine mem_sUnit_of_pow_mem hp.ne_zero ?_
      rw [← hrel]
      exact Subgroup.mul_mem _ (Subgroup.pow_mem _ haS _)
        (Subgroup.prod_mem _ fun j _ => Subgroup.pow_mem _ (y j).2 _)
    have hUrel : (⟨a, haS⟩ : ((↑S : Set (HeightOneSpectrum (𝓞 k))).unit k)) ^ e₀ * ∏ j, y j ^ e j
        = (⟨w, hwU⟩ : ((↑S : Set (HeightOneSpectrum (𝓞 k))).unit k)) ^ p := by
      apply Subtype.ext
      (push_cast; exact hrel)

    have hQ : φ ⟨a, haS⟩ ^ e₀ * ∏ j, φ (y j) ^ e j = 1 := by
      have h := congrArg φ hUrel
      rw [map_mul, map_pow, map_prod, map_pow] at h
      simp only [map_pow] at h
      rw [h, sUnitModPow_pow_eq_one]
    have hV : (e₀ : ZMod p) • A + ∑ j, (e j : ZMod p) • ((bW j : W) : SUnitSpace (k := k) p S) = 0 := by
      have h := congrArg Additive.ofMul hQ
      rw [ofMul_mul, ofMul_pow, ofMul_prod] at h
      simp only [ofMul_pow, hy, ofMul_toMul, ofMul_one] at h
      simpa only [Nat.cast_smul_eq_nsmul, hAdef] using h

    have hzW : ∑ j, (e j : ZMod p) • ((bW j : W) : SUnitSpace (k := k) p S) ∈ W :=
      W.sum_mem fun j _ => W.smul_mem _ (bW j).2

    have hAW : (e₀ : ZMod p) • A ∈ W := by
      have h2 : (e₀ : ZMod p) • A + ∑ j, (e j : ZMod p) • ((bW j : W) : SUnitSpace (k := k) p S) ∈ W := by
        rw [hV]
        exact W.zero_mem
      exact (add_mem_cancel_right hzW).mp h2
    have hAspan : (e₀ : ZMod p) • A ∈ Submodule.span (ZMod p) {A} :=
      Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self A)
    have hA0 : (e₀ : ZMod p) • A = 0 := Submodule.disjoint_def.mp hW.disjoint _ hAspan hAW
    have he₀ : (e₀ : ZMod p) = 0 := (smul_eq_zero.mp hA0).resolve_right hA

    have hsum0 : ∑ j, (e j : ZMod p) • ((bW j : W) : SUnitSpace (k := k) p S) = 0 := by
      have h := hV
      rw [hA0] at h
      exact (zero_add _).symm.trans h
    have hsumW : ∑ j, (e j : ZMod p) • bW j = (0 : W) := by
      apply Subtype.val_injective
      (push_cast; exact hsum0)
    have hcoef := Fintype.linearIndependent_iff.mp bW.linearIndependent (fun j => (e j : ZMod p)) hsumW
    refine ⟨fun j => ?_, ?_⟩
    · exact (ZMod.natCast_eq_zero_iff _ _).mp (hcoef j)
    · exact (ZMod.natCast_eq_zero_iff _ _).mp he₀

end Radicand
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

section RadicandAtKummer

variable {k E}

omit [NumberField E] in

private theorem exists_radicand_basis_of_kummer [IsGalois k E] {p : ℕ} (hp : p.Prime) (hμ : (primitiveRoots p k).Nonempty)
    (hdeg : Module.finrank k E = p) (α : E) (a : kˣ) (hα : α ^ p = algebraMap k E (a : k))
    (hgen : ∀ σ : E ≃ₐ[k] E, σ α = α → σ = 1) (S : Finset (HeightOneSpectrum (𝓞 k)))
    (hSa : ∀ v : HeightOneSpectrum (𝓞 k), v.valuation k (a : k) ≠ 1 → v ∈ S) :
    ∃ (t : ℕ) (u : Fin t → kˣ), (∀ j, u j ∈ (↑S : Set (HeightOneSpectrum (𝓞 k))).unit k) ∧
      t + 1 = S.card + Fintype.card (InfinitePlace k) ∧
      ∀ (e₀ : ℕ) (e : Fin t → ℕ) (w : kˣ), a ^ e₀ * ∏ j, u j ^ e j = w ^ p → (∀ j, p ∣ e j) ∧ p ∣ e₀ := by
  have haS : a ∈ (↑S : Set (HeightOneSpectrum (𝓞 k))).unit k := by
    rw [mem_sUnit_iff]
    intro v hv
    by_contra h
    exact hv (Finset.mem_coe.mpr (hSa v h))
  exact exists_radicand_basis hp hμ S a haS (radicand_not_pow k E hp hμ hdeg α a hα hgen)

end RadicandAtKummer
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

section Assembly

variable {k E}

private theorem principal_sup_unitIdelesOutside_union_eq_top
    {S T : Finset (HeightOneSpectrum (𝓞 k))}
    (hScl : M4aHerbrand.principalIdeles (𝓞 k) k ⊔ NumberField.AdeleRing.unitIdelesOutside (𝓞 k) k ↑S = ⊤) :
    M4aHerbrand.principalIdeles (𝓞 k) k ⊔ NumberField.AdeleRing.unitIdelesOutside (𝓞 k) k (↑(S ∪ T)) = ⊤ := by
  have hsub : (↑S : Set (HeightOneSpectrum (𝓞 k))) ⊆ ↑(S ∪ T) :=
    Finset.coe_subset.mpr Finset.subset_union_left
  have hmono : NumberField.AdeleRing.unitIdelesOutside (𝓞 k) k ↑S ≤
      NumberField.AdeleRing.unitIdelesOutside (𝓞 k) k (↑(S ∪ T)) := by
    exact Subgroup.comap_mono (IsDedekindDomain.FiniteAdeleRing.unitIdelesOutside_mono (𝓞 k) k hsub)
  have h := sup_le_sup_left hmono (M4aHerbrand.principalIdeles (𝓞 k) k)
  rw [hScl] at h
  exact top_le_iff.mp h

private theorem exponent_bound {S T : Finset (HeightOneSpectrum (𝓞 k))} (hTS : ∀ v ∈ T, v ∉ S)
    (hcard : S.card + Fintype.card (InfinitePlace k) ≤ T.card + 1) :
    2 * (S.card + Fintype.card (InfinitePlace k)) ≤
      Nat.card (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 k))) + NumberField.Units.rank k + 1 + 1 := by
  have hdisj : Disjoint S T := Finset.disjoint_left.mpr fun v hvS hvT => hTS v hvT hvS
  have hcardU : Nat.card (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 k))) = S.card + T.card := by
    rw [Finset.coe_sort_coe, Nat.card_eq_finsetCard, Finset.card_union_of_disjoint hdisj]
  have hinf : 0 < Fintype.card (InfinitePlace k) := by
    exact Fintype.card_pos
  rw [hcardU, NumberField.Units.rank]
  omega

private theorem capstone_of_auxSet [IsGalois k E] {p : ℕ} (hp : p.Prime) (hμ : (primitiveRoots p k).Nonempty)
    (hdeg : Module.finrank k E = p)
    (α : E) (a : kˣ) (hα : α ^ p = algebraMap k E (a : k)) (hgen : ∀ σ : E ≃ₐ[k] E, σ α = α → σ = 1)
    {S : Finset (HeightOneSpectrum (𝓞 k))}
    (hSp : ∀ v : HeightOneSpectrum (𝓞 k), (p : 𝓞 k) ∈ v.asIdeal → v ∈ S)
    (hSa : ∀ v : HeightOneSpectrum (𝓞 k), v.valuation k (a : k) ≠ 1 → v ∈ S)
    (hScl : M4aHerbrand.principalIdeles (𝓞 k) k ⊔ NumberField.AdeleRing.unitIdelesOutside (𝓞 k) k ↑S = ⊤)
    {T : Finset (HeightOneSpectrum (𝓞 k))} (hT : auxSetSpec k E p S T)
    (B : M4aHerbrand.AdeleBaseChange (𝓞 k) k (𝓞 E) E) :
    (M4aHerbrand.principalIdeles (𝓞 k) k ⊔ B.idelicNorm.range).index ∣ p := by
  have hBx : box p S T ≤ B.idelicNorm.range := box_le_range_idelicNorm hdeg α a hα hgen hSp hSa hT B
  obtain ⟨hTS, hcard, -, hsurj⟩ := hT
  refine (Subgroup.index_dvd_of_le (sup_le_sup_left hBx _)).trans ?_
  have hid := index_sup_mul_relIndex_inf (M4aHerbrand.principalIdeles (𝓞 k) k) (box p S T)
    (NumberField.AdeleRing.unitIdelesOutside (𝓞 k) k (↑(S ∪ T))) (box_le_unitIdelesOutside p S T)
    (principal_sup_unitIdelesOutside_union_eq_top hScl)
  rw [relIndex_box hp hμ hSp hTS, relIndex_box_principal_inf hp hμ hSp hScl hsurj] at hid
  exact dvd_of_mul_pow_eq_pow hp.pos hid (exponent_bound hTS hcard)

end Assembly
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

section Glue

variable {k E}

private theorem exists_contract_S (p : ℕ) (hp : p ≠ 0) (a : kˣ) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 k)),
      (∀ v : HeightOneSpectrum (𝓞 k), (p : 𝓞 k) ∈ v.asIdeal → v ∈ S) ∧
      (∀ v : HeightOneSpectrum (𝓞 k), v.valuation k (a : k) ≠ 1 → v ∈ S) ∧
      M4aHerbrand.principalIdeles (𝓞 k) k ⊔ NumberField.AdeleRing.unitIdelesOutside (𝓞 k) k ↑S = ⊤ := by
  obtain ⟨S₀, hS₀⟩ := ClassGroup.exists_finset_forall_exists_mk0_eq_of_dvd (𝓞 k)
  obtain ⟨S, hS₀S, hSp, hSa⟩ := exists_finset_bad_places k S₀ p hp a
  refine ⟨S, hSp, hSa, ?_⟩
  refine NumberField.AdeleRing.principalIdeles_sup_unitIdelesOutside_eq_top (𝓞 k) k (↑S) ?_
  intro c
  obtain ⟨I, hI, hIS⟩ := hS₀ c
  exact ⟨I, hI, fun v hv => Finset.mem_coe.mpr (hS₀S (hIS v hv))⟩

private theorem capstone_index_dvd_of_choice [IsGalois k E] {p : ℕ} (hp : p.Prime) (hμ : (primitiveRoots p k).Nonempty)
    (hdeg : Module.finrank k E = p)
    (hchoice : ∀ (α : E) (a : kˣ), α ^ p = algebraMap k E (a : k) → (∀ σ : E ≃ₐ[k] E, σ α = α → σ = 1) →
      ∀ S : Finset (HeightOneSpectrum (𝓞 k)),
        (∀ v : HeightOneSpectrum (𝓞 k), (p : 𝓞 k) ∈ v.asIdeal → v ∈ S) →
        (∀ v : HeightOneSpectrum (𝓞 k), v.valuation k (a : k) ≠ 1 → v ∈ S) →
        M4aHerbrand.principalIdeles (𝓞 k) k ⊔ NumberField.AdeleRing.unitIdelesOutside (𝓞 k) k ↑S = ⊤ →
        ∃ T : Finset (HeightOneSpectrum (𝓞 k)), auxSetSpec k E p S T)
    (B : M4aHerbrand.AdeleBaseChange (𝓞 k) k (𝓞 E) E) :
    (M4aHerbrand.principalIdeles (𝓞 k) k ⊔ B.idelicNorm.range).index ∣ p := by
  obtain ⟨α, a, hα, hgen⟩ := exists_kummer_generator k E hp hμ hdeg
  obtain ⟨S, hSp, hSa, hScl⟩ := exists_contract_S p hp.ne_zero a
  obtain ⟨T, hT⟩ := hchoice α a hα hgen S hSp hSa hScl
  exact capstone_of_auxSet hp hμ hdeg α a hα hgen hSp hSa hScl hT B

private theorem capstone_genuine_of_choice [IsGalois k E] {p : ℕ} (hp : p.Prime) (hμ : (primitiveRoots p k).Nonempty)
    (hdeg : Module.finrank k E = p)
    (hchoice : ∀ (α : E) (a : kˣ), α ^ p = algebraMap k E (a : k) → (∀ σ : E ≃ₐ[k] E, σ α = α → σ = 1) →
      ∀ S : Finset (HeightOneSpectrum (𝓞 k)),
        (∀ v : HeightOneSpectrum (𝓞 k), (p : 𝓞 k) ∈ v.asIdeal → v ∈ S) →
        (∀ v : HeightOneSpectrum (𝓞 k), v.valuation k (a : k) ≠ 1 → v ∈ S) →
        M4aHerbrand.principalIdeles (𝓞 k) k ⊔ NumberField.AdeleRing.unitIdelesOutside (𝓞 k) k ↑S = ⊤ →
        ∃ T : Finset (HeightOneSpectrum (𝓞 k)), auxSetSpec k E p S T) :
    (M4aHerbrand.principalIdeles (𝓞 k) k ⊔
        (M4aHerbrand.GenuineDescent.genuineBaseChange k E).idelicNorm.range).index ∣ p :=
  capstone_index_dvd_of_choice hp hμ hdeg hchoice _

end Glue
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2"

end P2F.CubicCapstone
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F"

end
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone"

end Fold_P2F_CubicCapstone
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone"

section Fold_P2F_PrimeAuxSet

set_option autoImplicit false

noncomputable section

namespace P2F
namespace PrimeAuxSet
namespace SignSpace

private scoped instance neZero_of_fact_prime {p : ℕ} [hp : Fact p.Prime] : NeZero p := ⟨hp.out.ne_zero⟩

section Lam

variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
variable {p : ℕ} [hp : Fact p.Prime]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ p)
variable {m : ℕ} (r : Fin m → Ω) {y : Fin m → F} (hr : ∀ i, r i ^ p = algebraMap F Ω (y i)) (hy : ∀ i, y i ≠ 0)

private abbrev zetaΩ (ζ : F) : Ω := algebraMap F Ω ζ

omit hp in
include hζ in
private theorem zetaΩ_isPrimitiveRoot : IsPrimitiveRoot (zetaΩ (Ω := Ω) ζ) p :=
  hζ.map_of_injective (algebraMap F Ω).injective

include hr hy in
private theorem root_ne_zero (i : Fin m) : r i ≠ 0 := by
  intro h0
  apply hy i
  have h := hr i
  rw [h0, zero_pow hp.out.ne_zero, eq_comm, map_eq_zero_iff _ (algebraMap F Ω).injective] at h
  exact h

include hζ hr hy in

private theorem exists_pow_mul (σ : Ω ≃ₐ[F] Ω) (i : Fin m) : ∃ j, j < p ∧ σ (r i) = zetaΩ ζ ^ j * r i := by
  have hr0 := root_ne_zero r hr hy i
  set ξ : Ω := σ (r i) / r i with hξ
  have hξp : ξ ^ p = 1 := by
    rw [hξ, div_pow, ← map_pow, hr i, AlgEquiv.commutes, div_self]
    exact (map_ne_zero_iff _ (algebraMap F Ω).injective).mpr (hy i)
  obtain ⟨j, hj, hjξ⟩ := (zetaΩ_isPrimitiveRoot (Ω := Ω) hζ).eq_pow_of_pow_eq_one hξp
  refine ⟨j, hj, ?_⟩
  rw [hjξ, hξ, div_mul_cancel₀ _ hr0]

private def lam (σ : Ω ≃ₐ[F] Ω) : Fin m → ZMod p :=
  fun i => ((exists_pow_mul hζ r hr hy σ i).choose : ZMod p)

include hζ hr hy in
private theorem lam_spec (σ : Ω ≃ₐ[F] Ω) (i : Fin m) :
    σ (r i) = zetaΩ ζ ^ (lam hζ r hr hy σ i).val * r i := by
  obtain ⟨hj, hσ⟩ := (exists_pow_mul hζ r hr hy σ i).choose_spec
  have hval : (lam hζ r hr hy σ i).val = (exists_pow_mul hζ r hr hy σ i).choose := by
    unfold lam
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hj]
  rw [hval]
  exact hσ

include hζ hr hy in

private theorem lam_eq_natCast_iff (σ : Ω ≃ₐ[F] Ω) (i : Fin m) (j : ℕ) :
    lam hζ r hr hy σ i = (j : ZMod p) ↔ σ (r i) = zetaΩ ζ ^ j * r i := by
  have hprim := zetaΩ_isPrimitiveRoot (Ω := Ω) hζ
  have hfin : IsOfFinOrder (zetaΩ (Ω := Ω) ζ) := isOfFinOrder_iff_pow_eq_one.mpr ⟨p, hp.out.pos, hprim.pow_eq_one⟩
  have hmodp : ∀ a b : ℕ, zetaΩ (Ω := Ω) ζ ^ a = zetaΩ ζ ^ b ↔ a ≡ b [MOD p] := fun a b => by
    rw [hfin.pow_eq_pow_iff_modEq, ← hprim.eq_orderOf]
  have hspec := lam_spec hζ r hr hy σ i
  have hr0 := root_ne_zero r hr hy i
  constructor
  · intro h
    have hmod : (lam hζ r hr hy σ i).val ≡ j [MOD p] := by
      rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val, h]
    rw [hspec, (hmodp _ _).mpr hmod]
  · intro h
    have hpow : zetaΩ (Ω := Ω) ζ ^ j = zetaΩ ζ ^ (lam hζ r hr hy σ i).val :=
      mul_right_cancel₀ hr0 (h.symm.trans hspec)
    have hmod : j ≡ (lam hζ r hr hy σ i).val [MOD p] := (hmodp _ _).mp hpow
    rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val] at hmod
    exact hmod.symm

include hζ hr hy in
private theorem lam_one : lam hζ r hr hy (1 : Ω ≃ₐ[F] Ω) = 0 := by
  funext i
  have h := (lam_eq_natCast_iff hζ r hr hy 1 i 0).mpr (by simp)
  simpa using h

include hζ hr hy in

private theorem lam_mul (σ τ : Ω ≃ₐ[F] Ω) : lam hζ r hr hy (σ * τ) = lam hζ r hr hy σ + lam hζ r hr hy τ := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  funext i
  set a := (lam hζ r hr hy σ i).val with ha
  set b := (lam hζ r hr hy τ i).val with hb
  have hσ : σ (r i) = zetaΩ ζ ^ a * r i := lam_spec hζ r hr hy σ i
  have hτ : τ (r i) = zetaΩ ζ ^ b * r i := lam_spec hζ r hr hy τ i
  have hστ : (σ * τ) (r i) = zetaΩ ζ ^ (a + b) * r i := by
    rw [AlgEquiv.mul_apply, hτ, map_mul, map_pow, hσ, pow_add]
    have hfix : σ (zetaΩ ζ) = zetaΩ ζ := AlgEquiv.commutes σ ζ
    rw [hfix]
    ring
  have h := (lam_eq_natCast_iff hζ r hr hy (σ * τ) i (a + b)).mpr hστ
  rw [h, Nat.cast_add, ha, hb, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  simp only [Pi.add_apply]

private def lamHom : (Ω ≃ₐ[F] Ω) →* Multiplicative (Fin m → ZMod p) where
  toFun σ := Multiplicative.ofAdd (lam hζ r hr hy σ)
  map_one' := by rw [lam_one, ofAdd_zero]
  map_mul' σ τ := by rw [lam_mul, ofAdd_add]

private theorem lamHom_apply (σ : Ω ≃ₐ[F] Ω) : lamHom hζ r hr hy σ = Multiplicative.ofAdd (lam hζ r hr hy σ) := rfl

include hζ hr hy in

private theorem lam_eq_zero_iff (σ : Ω ≃ₐ[F] Ω) : lam hζ r hr hy σ = 0 ↔ ∀ i, σ (r i) = r i := by
  constructor
  · intro h i
    have hi : lam hζ r hr hy σ i = ((0 : ℕ) : ZMod p) := by rw [h]; simp
    simpa using (lam_eq_natCast_iff hζ r hr hy σ i 0).mp hi
  · intro h
    funext i
    have hi : σ (r i) = zetaΩ ζ ^ (0 : ℕ) * r i := by rw [pow_zero, one_mul]; exact h i
    simpa using (lam_eq_natCast_iff hζ r hr hy σ i 0).mpr hi

include hζ hr hy in

private theorem lam_injective (hgen : ∀ σ : Ω ≃ₐ[F] Ω, (∀ i, σ (r i) = r i) → σ = 1) :
    Function.Injective (lam hζ r hr hy) := by
  have hker : ∀ σ : Ω ≃ₐ[F] Ω, lamHom hζ r hr hy σ = 1 → σ = 1 := by
    intro σ hσ
    apply hgen
    rw [← lam_eq_zero_iff hζ r hr hy]
    rw [lamHom_apply] at hσ
    exact ofAdd_eq_one.mp hσ
  have hinj : Function.Injective (lamHom hζ r hr hy) := (injective_iff_map_eq_one _).mpr hker
  intro σ τ h
  apply hinj
  rw [lamHom_apply, lamHom_apply, h]

include hζ hr hy in

private theorem lam_bijective (hgen : ∀ σ : Ω ≃ₐ[F] Ω, (∀ i, σ (r i) = r i) → σ = 1)
    (hcard : Nat.card (Ω ≃ₐ[F] Ω) = p ^ m) : Function.Bijective (lam hζ r hr hy) := by
  have htarget : Nat.card (Fin m → ZMod p) = p ^ m := by
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
  haveI : Finite (Fin m → ZMod p) := by
    haveI : NeZero p := ⟨hp.out.ne_zero⟩
    infer_instance
  exact (lam_injective hζ r hr hy hgen).bijective_of_nat_card_le (by rw [htarget, hcard])

end Lam
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone"

section Span

variable {p : ℕ} [hp : Fact p.Prime]

private theorem exists_fin_linearIndependent {W : Type*} {m : ℕ} (f : W → (Fin m → ZMod p))
    (hspan : Submodule.span (ZMod p) (Set.range f) = ⊤) :
    ∃ w : Fin m → W, LinearIndependent (ZMod p) (f ∘ w) := by
  classical
  obtain ⟨b, hb, hspanb, hli⟩ := exists_linearIndependent (ZMod p) (Set.range f)
  haveI : Fintype b := Fintype.ofFinite b
  have hcard : Fintype.card b = m := by
    rw [linearIndependent_iff_card_eq_finrank_span, Subtype.range_coe_subtype, Set.setOf_mem_eq] at hli
    rw [hli, Set.finrank, hspanb, hspan, finrank_top, Module.finrank_fin_fun]
  let e : b ≃ Fin m := Fintype.equivFinOfCardEq hcard
  have hpre : ∀ j : Fin m, ∃ w : W, f w = (e.symm j : Fin m → ZMod p) := fun j => hb (e.symm j).2
  choose w hw using hpre
  refine ⟨w, ?_⟩
  have hfw : f ∘ w = ((↑) : b → (Fin m → ZMod p)) ∘ e.symm := funext fun j => hw j
  rw [hfw]
  rw [linearIndependent_iff_card_eq_finrank_span, Subtype.range_coe_subtype, Set.setOf_mem_eq] at hli
  have hli' : LinearIndependent (ZMod p) ((↑) : b → (Fin m → ZMod p)) := by
    rw [linearIndependent_iff_card_eq_finrank_span, Subtype.range_coe_subtype, Set.setOf_mem_eq]; exact hli
  exact hli'.comp e.symm e.symm.injective

end Span
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone"

section Gen

variable {p : ℕ} [hp : Fact p.Prime]

private theorem span_eq_top_of_generators {G : Type*} [Group G] {m : ℕ} (φ : G →* Multiplicative (Fin m → ZMod p))
    (hφ : Function.Surjective φ) (S : Set G) (hS : Subgroup.closure S = ⊤) :
    Submodule.span (ZMod p) ((fun g => Multiplicative.toAdd (φ g)) '' S) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨g, hg⟩ := hφ (Multiplicative.ofAdd x)
  have hx : x = Multiplicative.toAdd (φ g) := by rw [hg]; rfl
  rw [hx]
  have hmem : g ∈ Subgroup.closure S := by rw [hS]; exact Subgroup.mem_top g
  clear hx hg
  induction hmem using Subgroup.closure_induction with
  | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
  | one => rw [map_one]; exact Submodule.zero_mem _
  | mul y z _ _ hy hz => rw [map_mul, toAdd_mul]; exact Submodule.add_mem _ hy hz
  | inv y _ hy => rw [map_inv, toAdd_inv]; exact Submodule.neg_mem _ hy

end Gen
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone"

section Solve

variable {p : ℕ} [hp : Fact p.Prime]

private theorem exists_mulVec_eq {m : ℕ} (L : Matrix (Fin m) (Fin m) (ZMod p))
    (hL : LinearIndependent (ZMod p) (fun i => L i)) (ε : Fin m → ZMod p) :
    ∃ c : Fin m → ZMod p, L.mulVec c = ε := by
  have hu : IsUnit L := Matrix.linearIndependent_rows_iff_isUnit.mp hL
  exact Matrix.mulVec_surjective_iff_isUnit.mpr hu ε

private theorem exists_nat_exponents {m : ℕ} (L : Matrix (Fin m) (Fin m) (ZMod p))
    (hL : LinearIndependent (ZMod p) (fun i => L i)) (ε : Fin m → ZMod p) :
    ∃ c : Fin m → ℕ, ∀ i, ∑ j, ((c j : ℕ) : ZMod p) * L i j = ε i := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  obtain ⟨c, hc⟩ := exists_mulVec_eq L hL ε
  refine ⟨fun j => (c j).val, fun i => ?_⟩
  have hi := congrFun hc i
  simp only [Matrix.mulVec, dotProduct] at hi
  rw [← hi]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ZMod.natCast_zmod_val, mul_comm]

end Solve
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone"

end P2F.PrimeAuxSet.SignSpace
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone"

end
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace"

set_option autoImplicit false

p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.NumberField IsDedekindDomain LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin Polynomial P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aKummer"

noncomputable section

namespace P2F
namespace PrimeAuxSet
namespace Residue

private scoped instance neZero_of_fact_prime {p : ℕ} [hp : Fact p.Prime] : NeZero p := ⟨hp.out.ne_zero⟩

attribute [local instance] Ideal.Quotient.field

section ResidueRoot

variable {k : Type*} [Field k] [NumberField k] {p : ℕ} [hp : Fact p.Prime]
variable (v : HeightOneSpectrum (𝓞 k)) (hpv : (p : 𝓞 k) ∉ v.asIdeal) {ζ : 𝓞 k} (hζ : IsPrimitiveRoot ζ p)

include hpv hζ in

private theorem residue_isPrimitiveRoot : IsPrimitiveRoot (Ideal.Quotient.mk v.asIdeal ζ) p := by
  haveI := v.isMaximal
  set z := Ideal.Quotient.mk v.asIdeal ζ with hz
  have hzp : z ^ p = 1 := by rw [hz, ← map_pow, hζ.pow_eq_one, map_one]
  have hz1 : z ≠ 1 := by
    intro h1
    apply hpv
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]

    have hcyc : ((p : ℕ) : 𝓞 k) = ∏ μ ∈ primitiveRoots p (𝓞 k), (1 - μ) := by
      have h := Polynomial.eval_one_cyclotomic_prime (R := 𝓞 k) (p := p)
      rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ, Polynomial.eval_prod] at h
      rw [← h]
      refine Finset.prod_congr rfl fun μ _ => ?_
      simp
    have hmem : ζ ∈ primitiveRoots p (𝓞 k) := (mem_primitiveRoots hp.out.pos).mpr hζ
    have hcast : ((p : ℕ) : 𝓞 k ⧸ v.asIdeal) = Ideal.Quotient.mk v.asIdeal ((p : ℕ) : 𝓞 k) := by
      rw [map_natCast]
    rw [hcast, hcyc, map_prod]
    refine Finset.prod_eq_zero hmem ?_
    rw [map_sub, map_one, ← hz, h1, sub_self]
  have hord : orderOf z = p := orderOf_eq_prime hzp hz1
  have h := IsPrimitiveRoot.orderOf z
  rwa [hord] at h

include hpv hζ in

private theorem prime_dvd_card_sub_one : p ∣ Nat.card (𝓞 k ⧸ v.asIdeal) - 1 := by
  haveI := v.isMaximal
  haveI : Finite (𝓞 k ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  have hz := residue_isPrimitiveRoot v hpv hζ
  have hzu := hz.isUnit_unit hp.out.ne_zero
  have hord : orderOf (hz.isUnit hp.out.ne_zero).unit = p := hzu.eq_orderOf.symm
  have hdvd := orderOf_dvd_natCard (hz.isUnit hp.out.ne_zero).unit
  rwa [hord, Nat.card_units] at hdvd

include hpv hζ in
private theorem card_eq_mul_add_one :
    Nat.card (𝓞 k ⧸ v.asIdeal) = p * ((Nat.card (𝓞 k ⧸ v.asIdeal) - 1) / p) + 1 := by
  haveI := v.isMaximal
  haveI : Finite (𝓞 k ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  have hpos : 0 < Nat.card (𝓞 k ⧸ v.asIdeal) := Nat.card_pos
  have h := Nat.mul_div_cancel' (prime_dvd_card_sub_one v hpv hζ)
  omega

end ResidueRoot
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace"

section FrobValue

variable (k M : Type*) [Field k] [NumberField k] [Field M] [NumberField M] [Algebra k M] [IsGalois k M]
variable {p : ℕ} [hp : Fact p.Prime]

omit [NumberField k] [NumberField M] [IsGalois k M] in

private theorem isIntegral_root {x : 𝓞 k} {r : M} (hr : r ^ p = algebraMap k M x) : IsIntegral ℤ r := by
  refine IsIntegral.of_pow hp.out.pos ?_
  rw [hr, show algebraMap k M (x : k) = algebraMap (𝓞 M) M (algebraMap (𝓞 k) (𝓞 M) x) from
    (IsScalarTower.algebraMap_apply (𝓞 k) (𝓞 M) M x).symm.trans (IsScalarTower.algebraMap_apply (𝓞 k) k M x)]
  exact (algebraMap (𝓞 k) (𝓞 M) x).isIntegral_coe

variable {ζ : 𝓞 k} (hζ : IsPrimitiveRoot ζ p)

omit [NumberField k] [NumberField M] [IsGalois k M] hp in
include hζ in
private theorem zetaM_isPrimitiveRoot : IsPrimitiveRoot (algebraMap k M (ζ : k)) p :=
  (hζ.map_of_injective (f := algebraMap (𝓞 k) k) (FaithfulSMul.algebraMap_injective (𝓞 k) k)).map_of_injective
    (algebraMap k M).injective

omit [NumberField k] [NumberField M] [IsGalois k M] in
include hζ in

private theorem exists_aut_eq_pow_mul (σ : M ≃ₐ[k] M) {x : 𝓞 k} (hx0 : x ≠ 0) {r : M} (hr : r ^ p = algebraMap k M x) :
    ∃ j, j < p ∧ σ r = algebraMap k M (ζ : k) ^ j * r := by
  have hr0 : r ≠ 0 := by
    rintro rfl
    apply hx0
    have h : (algebraMap k M x : M) = 0 := by rw [← hr, zero_pow hp.out.ne_zero]
    rw [map_eq_zero_iff _ (algebraMap k M).injective] at h
    exact (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 k) k)).mp h
  have hξ : (σ r / r) ^ p = 1 := by
    rw [div_pow, ← map_pow, hr, AlgEquiv.commutes, div_self]
    rw [← hr]
    exact pow_ne_zero _ hr0
  obtain ⟨j, hj, hjξ⟩ := (zetaM_isPrimitiveRoot k M hζ).eq_pow_of_pow_eq_one hξ
  exact ⟨j, hj, by rw [hjξ, div_mul_cancel₀ _ hr0]⟩

variable (v : HeightOneSpectrum (𝓞 k))

private def resAbove : 𝓞 k ⧸ v.asIdeal →+* 𝓞 M ⧸ primeAbove k M v :=
  Ideal.quotientMap (primeAbove k M v) (algebraMap (𝓞 k) (𝓞 M)) (under_primeAbove k M v).ge

omit [NumberField M] [IsGalois k M] in
private theorem resAbove_mk (y : 𝓞 k) :
    resAbove k M v (Ideal.Quotient.mk v.asIdeal y) = Ideal.Quotient.mk (primeAbove k M v) (algebraMap (𝓞 k) (𝓞 M) y) :=
  Ideal.quotientMap_mk

omit [NumberField M] [IsGalois k M] in
private theorem resAbove_injective : Function.Injective (resAbove k M v) := by
  haveI := v.isMaximal
  haveI : (primeAbove k M v).IsMaximal := primeAbove_isMaximal k M v
  exact (resAbove k M v).injective

variable (hpv : (p : 𝓞 k) ∉ v.asIdeal)

include hζ hpv in

private theorem pow_residue_eq_of_artinFrob_eq {x : 𝓞 k} (hx : x ∉ v.asIdeal) {r : M} (hr : r ^ p = algebraMap k M x)
    (j : ℕ) (hσ : artinFrob k M v r = algebraMap k M (ζ : k) ^ j * r) :
    (Ideal.Quotient.mk v.asIdeal x) ^ ((Nat.card (𝓞 k ⧸ v.asIdeal) - 1) / p) = (Ideal.Quotient.mk v.asIdeal ζ) ^ j := by
  classical
  haveI := v.isMaximal
  haveI : (primeAbove k M v).IsMaximal := primeAbove_isMaximal k M v
  set Q := primeAbove k M v with hQ
  set nn := (Nat.card (𝓞 k ⧸ v.asIdeal) - 1) / p with hnn

  let R : 𝓞 M := ⟨r, isIntegral_root k M hr⟩
  have hcoe : ∀ y : 𝓞 k, (algebraMap (𝓞 k) (𝓞 M) y : M) = algebraMap k M (y : k) := fun y =>
    ((IsScalarTower.algebraMap_apply (𝓞 k) (𝓞 M) M y).symm.trans (IsScalarTower.algebraMap_apply (𝓞 k) k M y))
  have hRp : R ^ p = algebraMap (𝓞 k) (𝓞 M) x := by
    apply RingOfIntegers.ext
    show r ^ p = _
    rw [hr, hcoe]

  have hq : Nat.card (𝓞 k ⧸ Q.under (𝓞 k)) = p * nn + 1 := by
    rw [hQ, under_primeAbove, hnn]
    exact card_eq_mul_add_one v hpv hζ
  have hfrob : Ideal.Quotient.mk Q (artinFrob k M v • R)
      = (Ideal.Quotient.mk Q (algebraMap (𝓞 k) (𝓞 M) x)) ^ nn * Ideal.Quotient.mk Q R := by
    have h : Ideal.Quotient.mk Q (artinFrob k M v • R)
        = Ideal.Quotient.mk Q (R ^ Nat.card (𝓞 k ⧸ Q.under (𝓞 k))) :=
      Ideal.Quotient.eq.mpr (isArithFrobAt_artinFrob k M v R)
    rw [h, hq, pow_succ, pow_mul, hRp, map_mul, map_pow]

  have hsmul : ((artinFrob k M v • R : 𝓞 M) : M) = artinFrob k M v r := rfl
  have hσR : artinFrob k M v • R = algebraMap (𝓞 k) (𝓞 M) ζ ^ j * R := by
    apply RingOfIntegers.ext
    rw [hsmul, hσ]
    push_cast
    exact congrArg₂ (fun a b => a ^ j * b) (hcoe ζ).symm rfl

  have hR0 : Ideal.Quotient.mk Q R ≠ 0 := by
    intro h0
    apply hx
    have hRQ : R ∈ Q := Ideal.Quotient.eq_zero_iff_mem.mp h0
    have hxQ : algebraMap (𝓞 k) (𝓞 M) x ∈ Q := by
      rw [← hRp]
      exact Ideal.pow_mem_of_mem Q hRQ p hp.out.pos
    rw [← under_primeAbove k M v]
    exact hxQ

  have hQeq : (Ideal.Quotient.mk Q (algebraMap (𝓞 k) (𝓞 M) x)) ^ nn
      = (Ideal.Quotient.mk Q (algebraMap (𝓞 k) (𝓞 M) ζ)) ^ j := by
    have h1 : (Ideal.Quotient.mk Q (algebraMap (𝓞 k) (𝓞 M) ζ)) ^ j * Ideal.Quotient.mk Q R
        = (Ideal.Quotient.mk Q (algebraMap (𝓞 k) (𝓞 M) x)) ^ nn * Ideal.Quotient.mk Q R := by
      rw [← hfrob, hσR, map_mul, map_pow]
    exact (mul_right_cancel₀ hR0 h1).symm
  apply resAbove_injective k M v
  rw [map_pow, map_pow, resAbove_mk, resAbove_mk]
  exact hQeq

include hζ hpv in

private theorem artinFrob_eq_self_iff {x : 𝓞 k} (hx : x ∉ v.asIdeal) {r : M} (hr : r ^ p = algebraMap k M x) :
    artinFrob k M v r = r ↔
      (Ideal.Quotient.mk v.asIdeal x) ^ ((Nat.card (𝓞 k ⧸ v.asIdeal) - 1) / p) = 1 := by
  constructor
  · intro hfix
    have h := pow_residue_eq_of_artinFrob_eq k M hζ v hpv hx hr 0 (by rw [pow_zero, one_mul]; exact hfix)
    rwa [pow_zero] at h
  · intro h1
    have hx0 : x ≠ 0 := fun h0 => hx (h0 ▸ Submodule.zero_mem _)
    obtain ⟨j, hj, hσ⟩ := exists_aut_eq_pow_mul k M hζ (artinFrob k M v) hx0 hr
    have hval := pow_residue_eq_of_artinFrob_eq k M hζ v hpv hx hr j hσ
    rw [h1] at hval
    have hz := residue_isPrimitiveRoot v hpv hζ
    have hpj : p ∣ j := hz.pow_eq_one_iff_dvd j |>.mp hval.symm
    have hj0 : j = 0 := Nat.eq_zero_of_dvd_of_lt hpj hj
    rw [hσ, hj0, pow_zero, one_mul]

end FrobValue
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace"

section ResidueDeg

variable (k E : Type*) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]
variable {p : ℕ} [hp : Fact p.Prime]
variable (v : HeightOneSpectrum (𝓞 k)) (w : HeightOneSpectrum (𝓞 E)) (hwv : w.asIdeal.under (𝓞 k) = v.asIdeal)

include hwv in
private theorem natCard_residue_pow :
    Nat.card (𝓞 E ⧸ w.asIdeal) = Nat.card (𝓞 k ⧸ v.asIdeal) ^ v.asIdeal.inertiaDeg' w.asIdeal := by
  haveI := v.isMaximal
  haveI := w.isMaximal
  haveI : w.asIdeal.LiesOver v.asIdeal := ⟨hwv.symm⟩
  haveI : Finite (𝓞 E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  rw [Ideal.inertiaDeg_algebraMap, Module.natCard_eq_pow_finrank (K := 𝓞 k ⧸ v.asIdeal)]

include hwv in

private theorem inertiaDeg_dvd_finrank [IsGalois k E] : v.asIdeal.inertiaDeg' w.asIdeal ∣ Module.finrank k E := by
  haveI := v.isMaximal
  haveI := w.isMaximal
  haveI : w.asIdeal.LiesOver v.asIdeal := ⟨hwv.symm⟩
  haveI : Module.Finite (𝓞 k) (𝓞 E) := Module.Finite.of_restrictScalars_finite ℤ (𝓞 k) (𝓞 E)
  have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn v.asIdeal (B := 𝓞 E) (G := E ≃ₐ[k] E)
  rw [Ideal.inertiaDegIn_eq_inertiaDeg (G := E ≃ₐ[k] E) v.asIdeal w.asIdeal,
    ← Ideal.inertiaDeg'_eq_inertiaDeg v.asIdeal w.asIdeal, IsGalois.card_aut_eq_finrank] at h
  rw [← h]
  exact dvd_mul_of_dvd_right (dvd_mul_left _ _) _

include hwv in
private theorem inertiaDeg_eq_one_or_eq [IsGalois k E] (hdeg : Module.finrank k E = p) :
    v.asIdeal.inertiaDeg' w.asIdeal = 1 ∨ v.asIdeal.inertiaDeg' w.asIdeal = p := by
  have h := inertiaDeg_dvd_finrank k E v w hwv
  rw [hdeg] at h
  exact (Nat.dvd_prime hp.out).mp h

private theorem prime_mul_sub_one_dvd_pow_sub_one {q : ℕ} (hq1 : 1 ≤ q) (hq : p ∣ q - 1) : p * (q - 1) ∣ q ^ p - 1 := by
  have hgeom : (∑ i ∈ Finset.range p, q ^ i) * (q - 1) = q ^ p - 1 := geom_sum_mul_of_one_le hq1 p
  rw [← hgeom]
  refine mul_dvd_mul_right ?_ _
  rw [← ZMod.natCast_eq_zero_iff]
  have hq' : ((q : ℕ) : ZMod p) = 1 := by
    have h := (ZMod.natCast_eq_zero_iff (q - 1) p).mpr hq
    have hsplit : q = (q - 1) + 1 := (Nat.sub_add_cancel hq1).symm
    rw [hsplit, Nat.cast_add, Nat.cast_one, h, zero_add]
  push_cast
  simp [hq']

variable (hpv : (p : 𝓞 k) ∉ v.asIdeal) {ζ : 𝓞 k} (hζ : IsPrimitiveRoot ζ p)

include hwv hpv hζ in

private theorem pow_resMap_eq_one_of_dvd_inertiaDeg (hf : p ∣ v.asIdeal.inertiaDeg' w.asIdeal)
    (x : 𝓞 k ⧸ v.asIdeal) (hx : x ≠ 0) :
    (resMap k E v w hwv x) ^ ((Nat.card (𝓞 E ⧸ w.asIdeal) - 1) / p) = 1 := by
  haveI := v.isMaximal
  haveI : Finite (𝓞 k ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  letI : Fintype (𝓞 k ⧸ v.asIdeal) := Fintype.ofFinite _
  set qv := Nat.card (𝓞 k ⧸ v.asIdeal) with hqv
  have hqv1 : 1 ≤ qv := Nat.card_pos
  have hpq : p ∣ qv - 1 := prime_dvd_card_sub_one v hpv hζ
  obtain ⟨t, ht⟩ := hf
  have hcardw : Nat.card (𝓞 E ⧸ w.asIdeal) = (qv ^ p) ^ t := by
    rw [natCard_residue_pow k E v w hwv, ht, pow_mul]

  have hdvd : p * (qv - 1) ∣ (qv ^ p) ^ t - 1 := by
    refine (prime_mul_sub_one_dvd_pow_sub_one hqv1 hpq).trans ?_
    have h := Nat.sub_dvd_pow_sub_pow (qv ^ p) 1 t
    rwa [one_pow] at h
  have hquot : qv - 1 ∣ (Nat.card (𝓞 E ⧸ w.asIdeal) - 1) / p := by
    rw [hcardw]
    exact Nat.dvd_div_of_mul_dvd hdvd
  obtain ⟨m, hm⟩ := hquot
  rw [hm, pow_mul, ← map_pow]
  have hx1 : x ^ (qv - 1) = 1 := by
    rw [hqv, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one x hx
  rw [hx1, map_one, one_pow]

include hwv in
private theorem natCard_residue_eq_of_inertiaDeg_one (hf : v.asIdeal.inertiaDeg' w.asIdeal = 1) :
    Nat.card (𝓞 E ⧸ w.asIdeal) = Nat.card (𝓞 k ⧸ v.asIdeal) := by
  rw [natCard_residue_pow k E v w hwv, hf, pow_one]

private theorem resMap_injective : Function.Injective (resMap k E v w hwv) := by
  haveI := v.isMaximal
  haveI := w.isMaximal
  exact (resMap k E v w hwv).injective

end ResidueDeg
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace"

section Criterion

variable {κ : Type*} [Field κ] [Fintype κ] {p : ℕ} [hp : Fact p.Prime]

private theorem exists_pow_eq_of_pow_div_eq_one (hpκ : p ∣ Fintype.card κ - 1) {y : κ} (hy : y ≠ 0)
    (h : y ^ ((Fintype.card κ - 1) / p) = 1) : ∃ z : κ, z ^ p = y := by
  classical
  set nn := (Fintype.card κ - 1) / p with hnn
  have hcard1 : 0 < Fintype.card κ - 1 := by
    have := Fintype.one_lt_card (α := κ)
    omega
  have hnnpos : 0 < nn := Nat.div_pos (Nat.le_of_dvd hcard1 hpκ) hp.out.pos
  have hcard : Fintype.card κ - 1 = p * nn := (Nat.mul_div_cancel' hpκ).symm
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := κˣ)
  set yu : κˣ := Units.mk0 y hy with hyu
  obtain ⟨a, ha⟩ : ∃ a : ℕ, g ^ a = yu := by
    have hmem := hg yu
    rwa [← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff] at hmem
  have hord : orderOf g = p * nn := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, Nat.card_eq_fintype_card, hcard]
  have hpow : g ^ (a * nn) = 1 := by
    rw [pow_mul, ha]
    ext
    simp only [Units.val_pow_eq_pow_val, hyu, Units.val_mk0, Units.val_one]
    exact h
  have hdvd : p * nn ∣ a * nn := by rw [← hord]; exact orderOf_dvd_of_pow_eq_one hpow
  have hpa : p ∣ a := Nat.dvd_of_mul_dvd_mul_right hnnpos hdvd
  obtain ⟨b, rfl⟩ := hpa
  refine ⟨((g ^ b : κˣ) : κ), ?_⟩
  rw [← Units.val_pow_eq_pow_val, ← pow_mul, mul_comm b p, ha, hyu, Units.val_mk0]

end Criterion
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace"

end P2F.PrimeAuxSet.Residue
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Residue"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace"

end
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Residue"

set_option autoImplicit false

open Polynomial

noncomputable section

namespace P2F
namespace PrimeAuxSet
namespace AuxField

open scoped Classical

private scoped instance neZero_of_fact_prime {p : ℕ} [hp : Fact p.Prime] : NeZero p := ⟨hp.out.ne_zero⟩

variable {k E : Type*} [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]
variable {p : ℕ} [hp : Fact p.Prime]
variable {t : ℕ} (u : Fin t → kˣ)

section Field

variable (E) (p)

private def radE (j : Fin t) : Eˣ := Units.map (algebraMap k E : k →* E) (u j)

private def radSet : Finset Eˣ := Finset.univ.image (radE E u)

private abbrev kpoly : E[X] := ∏ w ∈ radSet E u, (X ^ p - C ((w : Eˣ) : E))

private abbrev KummerField : Type _ := (kpoly E p u).SplittingField

private scoped instance : NumberField (KummerField E p u) := NumberField.of_module_finite E _

omit [NumberField k] [NumberField E] in
private theorem radE_mem_radSet (j : Fin t) : radE E u j ∈ radSet E u := Finset.mem_image_of_mem _ (Finset.mem_univ j)

omit [NumberField k] [NumberField E] in
private theorem radE_coe (j : Fin t) : ((radE E u j : Eˣ) : E) = algebraMap k E (u j : k) := rfl

omit [NumberField k] [NumberField E] in
private theorem monic_kpoly : (kpoly E p u).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_pow_sub_C _ hp.out.ne_zero

omit [NumberField k] [NumberField E] in
private theorem exists_root (j : Fin t) :
    ∃ r : KummerField E p u, r ^ p = algebraMap E (KummerField E p u) (algebraMap k E (u j : k)) := by
  have hsplit : ((kpoly E p u).map (algebraMap E (KummerField E p u))).Splits := SplittingField.splits _
  have hne : (kpoly E p u).map (algebraMap E (KummerField E p u)) ≠ 0 :=
    ((monic_kpoly E p u).map _).ne_zero
  have hdvd : (X ^ p - C ((radE E u j : Eˣ) : E)).map (algebraMap E (KummerField E p u)) ∣
      (kpoly E p u).map (algebraMap E (KummerField E p u)) :=
    Polynomial.map_dvd _ (Finset.dvd_prod_of_mem _ (radE_mem_radSet E u j))
  have hf := hsplit.of_dvd hne hdvd
  rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C] at hf
  obtain ⟨r, hr⟩ := hf.exists_eval_eq_zero (by rw [degree_X_pow_sub_C hp.out.pos]; exact_mod_cast hp.out.ne_zero)
  refine ⟨r, ?_⟩
  rw [eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hr
  rw [hr, radE_coe]

private def rad (j : Fin t) : KummerField E p u := (exists_root E p u j).choose

omit [NumberField k] [NumberField E] in
private theorem rad_pow (j : Fin t) :
    rad E p u j ^ p = algebraMap E (KummerField E p u) (algebraMap k E (u j : k)) := (exists_root E p u j).choose_spec

omit [NumberField k] [NumberField E] in
private theorem rad_pow' (j : Fin t) : rad E p u j ^ p = algebraMap E (KummerField E p u) ((radE E u j : Eˣ) : E) := rad_pow E p u j

omit [NumberField k] [NumberField E] in
private theorem radE_coe_ne_zero (j : Fin t) : ((radE E u j : Eˣ) : E) ≠ 0 := (radE E u j).ne_zero

end Field
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Residue"

section Galois

variable (E) (p)

omit [NumberField k] [NumberField E] in
private theorem primitiveRoots_nonempty_E {ζ : k} (hζ : IsPrimitiveRoot ζ p) : (primitiveRoots p E).Nonempty :=
  ⟨algebraMap k E ζ, (mem_primitiveRoots hp.out.pos).mpr (hζ.map_of_injective (algebraMap k E).injective)⟩

variable {ζ : k} (hζ : IsPrimitiveRoot ζ p)
include hζ

omit [NumberField k] [NumberField E] in
private theorem isGalois_aux : IsGalois E (KummerField E p u) :=
  (KummerTheory.isGalois_and_commute_and_pow_eq_one_of_isSplittingField_prod_X_pow_sub_C E (KummerField E p u)
    (primitiveRoots_nonempty_E E p hζ) (radSet E u)).1

omit [NumberField k] [NumberField E] in
private theorem aut_comm (σ τ : KummerField E p u ≃ₐ[E] KummerField E p u) : σ * τ = τ * σ :=
  (KummerTheory.isGalois_and_commute_and_pow_eq_one_of_isSplittingField_prod_X_pow_sub_C E (KummerField E p u)
    (primitiveRoots_nonempty_E E p hζ) (radSet E u)).2.1 σ τ

omit [NumberField k] [NumberField E] in
private theorem aut_pow_eq_one (σ : KummerField E p u ≃ₐ[E] KummerField E p u) : σ ^ p = 1 :=
  (KummerTheory.isGalois_and_commute_and_pow_eq_one_of_isSplittingField_prod_X_pow_sub_C E (KummerField E p u)
    (primitiveRoots_nonempty_E E p hζ) (radSet E u)).2.2 σ

omit [NumberField k] [NumberField E] in

private theorem eq_zeta_pow_mul_rad (j : Fin t) (α : KummerField E p u)
    (hα : α ^ p = algebraMap E (KummerField E p u) ((radE E u j : Eˣ) : E)) :
    ∃ i : ℕ, α = algebraMap E (KummerField E p u) (algebraMap k E ζ) ^ i * rad E p u j := by
  have hζE : IsPrimitiveRoot (algebraMap E (KummerField E p u) (algebraMap k E ζ)) p :=
    (hζ.map_of_injective (algebraMap k E).injective).map_of_injective (algebraMap E (KummerField E p u)).injective
  have hr0 : rad E p u j ≠ 0 := by
    intro h0
    have h := rad_pow' E p u j
    rw [h0, zero_pow hp.out.ne_zero, eq_comm, map_eq_zero_iff _ (algebraMap E (KummerField E p u)).injective] at h
    exact radE_coe_ne_zero E u j h
  have hquot : (α / rad E p u j) ^ p = 1 := by
    rw [div_pow, hα, rad_pow' E p u j, div_self]
    exact (map_ne_zero_iff _ (algebraMap E (KummerField E p u)).injective).mpr (radE_coe_ne_zero E u j)
  obtain ⟨i, -, hi⟩ := hζE.eq_pow_of_pow_eq_one hquot
  exact ⟨i, by rw [hi, div_mul_cancel₀ _ hr0]⟩

omit [NumberField k] [NumberField E] in

private theorem aut_eq_one_of_forall_rad_eq (σ : KummerField E p u ≃ₐ[E] KummerField E p u)
    (h : ∀ j, σ (rad E p u j) = rad E p u j) : σ = 1 := by
  refine KummerTheory.algEquiv_eq_one_of_forall_apply_eq_of_isSplittingField E (KummerField E p u) (n := p) (radSet E u) σ ?_
  intro α w hw hα
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hw
  obtain ⟨i, rfl⟩ := eq_zeta_pow_mul_rad E p u hζ j α hα
  rw [map_mul, map_pow, AlgEquiv.commutes, h j]

end Galois
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Residue"

section Character

variable (E) (p)

private abbrev radVal (j : Fin t) : E := ((radE E u j : Eˣ) : E)

omit [NumberField k] [NumberField E] in
private theorem radVal_ne_zero (j : Fin t) : radVal E u j ≠ 0 := radE_coe_ne_zero E u j

variable {ζ : k} (hζ : IsPrimitiveRoot ζ p)
include hζ

omit [NumberField k] [NumberField E] hp in
private theorem zetaE_isPrimitiveRoot : IsPrimitiveRoot (algebraMap k E ζ) p := hζ.map_of_injective (algebraMap k E).injective

private def lamAux (σ : KummerField E p u ≃ₐ[E] KummerField E p u) : Fin t → ZMod p :=
  SignSpace.lam (zetaE_isPrimitiveRoot E p hζ) (rad E p u) (rad_pow' E p u) (radVal_ne_zero E u) σ

omit [NumberField k] [NumberField E] in
private theorem lamAux_spec (σ : KummerField E p u ≃ₐ[E] KummerField E p u) (j : Fin t) :
    σ (rad E p u j) = algebraMap E (KummerField E p u) (algebraMap k E ζ) ^ (lamAux E p u hζ σ j).val * rad E p u j :=
  SignSpace.lam_spec (zetaE_isPrimitiveRoot E p hζ) (rad E p u) (rad_pow' E p u) (radVal_ne_zero E u) σ j

omit [NumberField k] [NumberField E] in
private theorem lamAux_mul (σ τ : KummerField E p u ≃ₐ[E] KummerField E p u) :
    lamAux E p u hζ (σ * τ) = lamAux E p u hζ σ + lamAux E p u hζ τ :=
  SignSpace.lam_mul (zetaE_isPrimitiveRoot E p hζ) (rad E p u) (rad_pow' E p u) (radVal_ne_zero E u) σ τ

omit [NumberField k] [NumberField E] in
private theorem lamAux_injective : Function.Injective (lamAux E p u hζ) :=
  SignSpace.lam_injective (zetaE_isPrimitiveRoot E p hζ) (rad E p u) (rad_pow' E p u) (radVal_ne_zero E u)
    (aut_eq_one_of_forall_rad_eq E p u hζ)

omit [NumberField k] [NumberField E] in

private theorem lamAux_bijective (hcard : Nat.card (KummerField E p u ≃ₐ[E] KummerField E p u) = p ^ t) :
    Function.Bijective (lamAux E p u hζ) :=
  SignSpace.lam_bijective (zetaE_isPrimitiveRoot E p hζ) (rad E p u) (rad_pow' E p u) (radVal_ne_zero E u)
    (aut_eq_one_of_forall_rad_eq E p u hζ) hcard

end Character
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Residue"

end P2F.PrimeAuxSet.AuxField
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Residue P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.AuxField"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Residue"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Residue"

end
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Residue P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.AuxField"

set_option autoImplicit false

p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.NumberField IsDedekindDomain LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin"

noncomputable section

namespace P2F
namespace PrimeAuxSet
namespace OntoDock

open P2F.PrimeAuxSet.AuxField

universe v

variable {k : Type*} [Field k] [NumberField k] {E : Type v} [Field E] [NumberField E] [Algebra k E]
variable {p : ℕ} [hp : Fact p.Prime] {t : ℕ} (u : Fin t → kˣ) {ζ : k} (hζ : IsPrimitiveRoot ζ p)

section PGroup

variable (E p)
include hζ

omit [NumberField k] [NumberField E] in
private theorem isMulCommutative_aut : IsMulCommutative (KummerField E p u ≃ₐ[E] KummerField E p u) :=
  ⟨⟨fun σ τ => aut_comm E p u hζ σ τ⟩⟩

omit [NumberField k] [NumberField E] in
private theorem isPGroup_aut : IsPGroup p (KummerField E p u ≃ₐ[E] KummerField E p u) :=
  fun σ => ⟨1, by rw [pow_one]; exact aut_pow_eq_one E p u hζ σ⟩

omit [NumberField k] [NumberField E] in
private theorem exists_finrank_eq_pow : ∃ n : ℕ, Module.finrank E (KummerField E p u) = p ^ n := by
  haveI := isGalois_aux E p u hζ
  obtain ⟨n, hn⟩ := (isPGroup_aut E p u hζ).exists_card_eq
  exact ⟨n, by rw [← IsGalois.card_aut_eq_finrank]; exact hn⟩

omit [NumberField k] in

private theorem finrank_eq_of_prime (F : IntermediateField E (KummerField E p u)) (hF : (Module.finrank E F).Prime) :
    Module.finrank E F = p := by
  obtain ⟨n, hn⟩ := exists_finrank_eq_pow E p u hζ
  have hdvd : Module.finrank E F ∣ p ^ n := by
    rw [← hn, ← Module.finrank_mul_finrank E F (KummerField E p u)]
    exact dvd_mul_right _ _
  exact (Nat.prime_dvd_prime_iff_eq hF hp.out).mp (hF.dvd_of_dvd_pow hdvd)

end PGroup
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Residue P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.AuxField"

section Modulus

variable (p)
variable (𝔞 : Ideal (𝓞 E))

private def expOf (P : Ideal (𝓞 E)) : ℕ :=
  (2 * Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) P + 1) +
    (4 * Ideal.ramificationIdx' (Ideal.span {(2 : ℤ)}) P + 2 * Ideal.ramificationIdx' (Ideal.span {(3 : ℤ)}) P + 1)

private def N : ℕ := (UniqueFactorizationMonoid.normalizedFactors 𝔞).toFinset.sup (expOf p)

private def fM : Ideal (𝓞 E) := 𝔞 ^ N p 𝔞

variable {𝔞}

omit hp in
private theorem fM_ne_bot (h𝔞 : 𝔞 ≠ ⊥) : fM p 𝔞 ≠ ⊥ := pow_ne_zero _ h𝔞

omit hp in
private theorem dvd_of_dvd_fM {w : HeightOneSpectrum (𝓞 E)} (h : w.asIdeal ∣ fM p 𝔞) : w.asIdeal ∣ 𝔞 :=
  (Ideal.prime_of_isPrime w.ne_bot w.isPrime).dvd_of_dvd_pow h

omit hp in
private theorem expOf_le_N (h𝔞 : 𝔞 ≠ ⊥) {w : HeightOneSpectrum (𝓞 E)} (hw : w.asIdeal ∣ 𝔞) : expOf p w.asIdeal ≤ N p 𝔞 := by
  classical
  have hmem : w.asIdeal ∈ (UniqueFactorizationMonoid.normalizedFactors 𝔞).toFinset := by
    rw [Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff h𝔞]
    exact ⟨w.isPrime, Ideal.le_of_dvd hw⟩
  exact Finset.le_sup (f := expOf p) hmem

omit hp in

private theorem pow_admissibleExpAt_dvd_fM (h𝔞 : 𝔞 ≠ ⊥) {w : HeightOneSpectrum (𝓞 E)} (hw : w.asIdeal ∣ 𝔞) :
    w.asIdeal ^ PrimeNormIndex.admissibleExpAt E p w ∣ fM p 𝔞 := by
  refine dvd_trans (pow_dvd_pow _ ?_) (pow_dvd_pow_of_dvd hw _)
  refine le_trans ?_ (expOf_le_N p h𝔞 hw)
  unfold PrimeNormIndex.admissibleExpAt expOf
  omega

omit hp in

private theorem pow_admissibleExp_dvd_fM (h𝔞 : 𝔞 ≠ ⊥) {w : HeightOneSpectrum (𝓞 E)} (hw : w.asIdeal ∣ 𝔞) :
    w.asIdeal ^ (4 * Ideal.ramificationIdx' (Ideal.span {(2 : ℤ)}) w.asIdeal +
      2 * Ideal.ramificationIdx' (Ideal.span {(3 : ℤ)}) w.asIdeal + 1) ∣ fM p 𝔞 := by
  refine dvd_trans (pow_dvd_pow _ ?_) (pow_dvd_pow_of_dvd hw _)
  refine le_trans ?_ (expOf_le_N p h𝔞 hw)
  unfold expOf
  omega

variable (h𝔞p : ∀ w : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ w.asIdeal → w.asIdeal ∣ 𝔞)
variable (h𝔞u : ∀ w : HeightOneSpectrum (𝓞 E), ¬ w.asIdeal ∣ 𝔞 → ∀ j, w.valuation E (algebraMap k E (u j : k)) = 1)

include hζ h𝔞p h𝔞u in
omit [NumberField k] in

private theorem inertia_primeAbove_eq_bot {w : HeightOneSpectrum (𝓞 E)} (hw : ¬ w.asIdeal ∣ 𝔞) :
    (primeAbove E (KummerField E p u) w).inertia (KummerField E p u ≃ₐ[E] KummerField E p u) = ⊥ := by
  haveI := primeAbove_isMaximal E (KummerField E p u) w
  let W : HeightOneSpectrum (𝓞 (KummerField E p u)) :=
    ⟨primeAbove E (KummerField E p u) w, inferInstance, primeAbove_ne_bot E (KummerField E p u) w⟩
  have hWw : W.under (𝓞 E) = w := HeightOneSpectrum.ext (under_primeAbove E (KummerField E p u) w)
  exact HeightOneSpectrum.Extension.inertia_eq_bot_of_forall_pow_eq E (KummerField E p u)
    (fun j => algebraMap k E (u j : k)) (rad E p u) (rad_pow E p u) (aut_eq_one_of_forall_rad_eq E p u hζ) w
    (h𝔞u w hw) (fun hpw => hw (h𝔞p w hpw)) ⟨W, hWw⟩

include hζ h𝔞p h𝔞u in
omit [NumberField k] in

private theorem isAdmissibleModulus_fM (h𝔞 : 𝔞 ≠ ⊥) : IsAdmissibleModulus E (KummerField E p u) (fM p 𝔞) := by
  refine ⟨fM_ne_bot p h𝔞, fun w hI => ?_⟩
  by_cases hw : w.asIdeal ∣ 𝔞
  · exact pow_admissibleExp_dvd_fM p h𝔞 hw
  · exact absurd (inertia_primeAbove_eq_bot p u hζ h𝔞p h𝔞u hw) hI

omit hp in

private theorem isAdmissibleModulusAt_of_isAdmissibleModulus (h𝔞 : 𝔞 ≠ ⊥) (F : Type v) [Field F] [NumberField F] [Algebra E F]
    (hF : IsAdmissibleModulus E F (fM p 𝔞)) : PrimeNormIndex.IsAdmissibleModulusAt E F p (fM p 𝔞) := by
  refine ⟨fM_ne_bot p h𝔞, fun w hw => ?_⟩
  have h1 : w.asIdeal ∣ fM p 𝔞 := dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero _)) (hF.2 w hw)
  exact pow_admissibleExpAt_dvd_fM p h𝔞 (dvd_of_dvd_fM p h1)

end Modulus
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Residue P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.AuxField"

section Onto

variable (p)
variable {𝔞 : Ideal (𝓞 E)}
variable (h𝔞p : ∀ w : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ w.asIdeal → w.asIdeal ∣ 𝔞)
variable (h𝔞u : ∀ w : HeightOneSpectrum (𝓞 E), ¬ w.asIdeal ∣ 𝔞 → ∀ j, w.valuation E (algebraMap k E (u j : k)) = 1)
variable [IsGalois E (KummerField E p u)]
variable [IsMulCommutative (KummerField E p u ≃ₐ[E] KummerField E p u)]

include hζ h𝔞p h𝔞u in
omit [NumberField k] in

private theorem artinSymbol_surjective (h𝔞 : 𝔞 ≠ ⊥)
    (hFI : ∀ (M : Type v) [Field M] [NumberField M] [Algebra E M] [IsGalois E M], Module.finrank E M = p →
      ∀ 𝔣₀ : Ideal (NumberField.RingOfIntegers E), NumberField.PrimeNormIndex.IsAdmissibleModulusAt E M p 𝔣₀ →
        LanglandsTunnell.P2.Artin.IdeleFirstIneqDataAt E M 𝔣₀) :
    Function.Surjective (artinSymbol E (KummerField E p u) (fM p 𝔞)) := by
  have hadmM := isAdmissibleModulus_fM p u hζ h𝔞p h𝔞u h𝔞
  refine artinSymbol_surjective_of_firstInequalityCTM (fM p 𝔞) fun F hF => ?_
  haveI : IsGalois E F := isGalois_intermediateField E (KummerField E p u) F
  have hdegF : Module.finrank E F = p := finrank_eq_of_prime E p u hζ F hF
  have hadmF : IsAdmissibleModulus E F (fM p 𝔞) := IsAdmissibleModulus.of_intermediateField E (KummerField E p u) F hadmM
  have hadmFp : PrimeNormIndex.IsAdmissibleModulusAt E F p (fM p 𝔞) :=
    isAdmissibleModulusAt_of_isAdmissibleModulus p h𝔞 F hadmF
  exact firstInequalityCTM_of_ideleDataAt E F (fM p 𝔞) hadmF (hFI F hdegF (fM p 𝔞) hadmFp)

end Onto
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Residue P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.AuxField"

section Basis

variable (p)
variable {𝔞 : Ideal (𝓞 E)}

omit [NumberField k] [NumberField E] in
private theorem lamAux_eq (σ : KummerField E p u ≃ₐ[E] KummerField E p u) :
    lamAux E p u hζ σ =
      SignSpace.lam (zetaE_isPrimitiveRoot E p hζ) (rad E p u) (rad_pow' E p u) (radVal_ne_zero E u) σ := rfl

variable [IsGalois E (KummerField E p u)]
variable [IsMulCommutative (KummerField E p u ≃ₐ[E] KummerField E p u)]

include hζ in
omit [NumberField k] in

private theorem exists_frobenius_basis (honto : Function.Surjective (artinSymbol E (KummerField E p u) (fM p 𝔞)))
    (hlam : Function.Surjective (lamAux E p u hζ)) :
    ∃ wv : Fin t → {w : HeightOneSpectrum (𝓞 E) // ¬ w.asIdeal ∣ fM p 𝔞},
      LinearIndependent (ZMod p) (fun i => lamAux E p u hζ (artinFrob E (KummerField E p u) (wv i).1)) := by
  set FS : Set (KummerField E p u ≃ₐ[E] KummerField E p u) :=
    Set.range (fun w : {w : HeightOneSpectrum (𝓞 E) // ¬ w.asIdeal ∣ fM p 𝔞} => artinFrob E (KummerField E p u) w.1)
    with hFS
  have hgen : Subgroup.closure FS = ⊤ := by
    rw [eq_top_iff]
    intro σ _
    obtain ⟨X, rfl⟩ := honto σ
    have hX : X ∈ (⊤ : Subgroup _) := Subgroup.mem_top X
    rw [← M4aKummer.closure_primeCarriers_eq_top E (fM p 𝔞)] at hX
    have hmap := Subgroup.mem_map_of_mem (artinSymbol E (KummerField E p u) (fM p 𝔞)) hX
    rw [MonoidHom.map_closure] at hmap
    refine Subgroup.closure_mono ?_ hmap
    rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨⟨w, hw⟩, (artinSymbol_prime E (KummerField E p u) hw).symm⟩
  set φ := SignSpace.lamHom (zetaE_isPrimitiveRoot E p hζ) (rad E p u) (rad_pow' E p u) (radVal_ne_zero E u) with hφdef
  have hφ : Function.Surjective φ := fun c => by
    obtain ⟨σ, hσ⟩ := hlam (Multiplicative.toAdd c)
    exact ⟨σ, by rw [hφdef, SignSpace.lamHom_apply, ← lamAux_eq p u hζ σ, hσ]; rfl⟩
  have hspan := SignSpace.span_eq_top_of_generators φ hφ FS hgen
  have hrange : (fun g => Multiplicative.toAdd (φ g)) '' FS
      = Set.range (fun w : {w : HeightOneSpectrum (𝓞 E) // ¬ w.asIdeal ∣ fM p 𝔞} =>
          lamAux E p u hζ (artinFrob E (KummerField E p u) w.1)) := by
    rw [hFS, ← Set.range_comp]
    rfl
  rw [hrange] at hspan
  obtain ⟨wv, hwv⟩ := SignSpace.exists_fin_linearIndependent _ hspan
  exact ⟨wv, hwv⟩

end Basis
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Residue P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.AuxField"

end P2F.PrimeAuxSet.OntoDock
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Residue P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.AuxField"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Residue P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.AuxField"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Residue P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.AuxField"

end
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Residue P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.AuxField"

set_option autoImplicit false

namespace P2F
namespace PrimeAuxSet
namespace Local

private scoped instance neZero_of_fact_prime {p : ℕ} [hp : Fact p.Prime] : NeZero p := ⟨hp.out.ne_zero⟩

section ZetaPow

variable {K : Type*} [Field K] {p : ℕ} [hp : Fact p.Prime] {ζ : K} (hζ : IsPrimitiveRoot ζ p)

include hζ

private theorem zeta_pow_eq_iff (m n : ℕ) : ζ ^ m = ζ ^ n ↔ (m : ZMod p) = n := by
  have hfin : IsOfFinOrder ζ := hζ.isOfFinOrder hp.out.ne_zero
  rw [hfin.pow_eq_pow_iff_modEq, ← hζ.eq_orderOf, ZMod.natCast_eq_natCast_iff]

private theorem zeta_pow_val_add (a b : ZMod p) : ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val := by
  rw [← pow_add, zeta_pow_eq_iff hζ]
  push_cast
  simp

private theorem zeta_pow_val_mul (a b : ZMod p) : ζ ^ (a * b).val = (ζ ^ a.val) ^ b.val := by
  rw [← pow_mul, zeta_pow_eq_iff hζ]
  push_cast
  simp

private theorem zeta_pow_val_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod p) :
    ζ ^ (∑ i ∈ s, f i).val = ∏ i ∈ s, ζ ^ (f i).val := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zeta_pow_val_add hζ, ih]

end ZetaPow
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Residue P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.AuxField"

section Symbol

variable {κ : Type*} [Field κ] [Fintype κ] {p : ℕ} [hp : Fact p.Prime] {ζ : κ} (hζ : IsPrimitiveRoot ζ p)

variable (κ p)

private abbrev nn : ℕ := (Fintype.card κ - 1) / p

variable {κ p}

include hζ

private theorem prime_dvd_card_sub_one' : p ∣ Fintype.card κ - 1 := by
  classical
  have hzu := hζ.isUnit_unit hp.out.ne_zero
  have hord : orderOf (hζ.isUnit hp.out.ne_zero).unit = p := hzu.eq_orderOf.symm
  have hdvd := orderOf_dvd_natCard (hζ.isUnit hp.out.ne_zero).unit
  rwa [hord, Nat.card_units, Nat.card_eq_fintype_card] at hdvd

private theorem pow_nn_pow_p (y : κ) (hy : y ≠ 0) : (y ^ nn κ p) ^ p = 1 := by
  rw [← pow_mul, Nat.div_mul_cancel (prime_dvd_card_sub_one' hζ), FiniteField.pow_card_sub_one_eq_one y hy]

private theorem exists_symbol (y : κ) (hy : y ≠ 0) : ∃ e : ZMod p, y ^ nn κ p = ζ ^ e.val := by
  obtain ⟨i, hi, hiy⟩ := hζ.eq_pow_of_pow_eq_one (pow_nn_pow_p hζ y hy)
  exact ⟨(i : ZMod p), by rw [ZMod.val_natCast, Nat.mod_eq_of_lt hi, hiy]⟩

private theorem prod_pow_nn_eq {t : ℕ} (u : Fin t → κ) (L c : Fin t → ZMod p)
    (hu : ∀ j, u j ^ nn κ p = ζ ^ (L j).val) :
    (∏ j, u j ^ (c j).val) ^ nn κ p = ζ ^ (∑ j, L j * c j).val := by
  rw [zeta_pow_val_sum hζ, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← pow_mul, mul_comm ((c j).val), pow_mul, hu j, zeta_pow_val_mul hζ]

private theorem exists_pow_mul_of_symbol_eq {x s : κ} (hx : x ≠ 0) (hs : s ≠ 0) (e : ZMod p)
    (hxe : x ^ nn κ p = ζ ^ e.val) (hse : s ^ nn κ p = ζ ^ e.val) : ∃ z : κ, x = s * z ^ p := by
  have hq : (x / s) ^ nn κ p = 1 := by
    rw [div_pow, hxe, hse, div_self]
    exact pow_ne_zero _ (hζ.ne_zero hp.out.ne_zero)
  obtain ⟨z, hz⟩ := Residue.exists_pow_eq_of_pow_div_eq_one (prime_dvd_card_sub_one' hζ) (div_ne_zero hx hs) hq
  exact ⟨z, by rw [hz]; field_simp⟩

end Symbol
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Residue P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.AuxField"

end P2F.PrimeAuxSet.Local
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Residue P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.AuxField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Local"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Residue P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.AuxField"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Residue P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.AuxField"

set_option autoImplicit false

open Polynomial

noncomputable section

namespace P2F
namespace PrimeAuxSet
namespace Seam

open P2F.PrimeAuxSet.AuxField P2F.PrimeAuxSet.Local

variable {k E : Type*} [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]
variable {p : ℕ} [hp : Fact p.Prime] {t : ℕ} (u : Fin t → kˣ) {ζ : k} (hζ : IsPrimitiveRoot ζ p)

variable (E p)

omit [NumberField k] [NumberField E] in
private theorem lamAux_one : lamAux E p u hζ 1 = 0 := by
  have h := lamAux_mul E p u hζ 1 1
  rw [one_mul] at h
  simpa using h

omit [NumberField k] [NumberField E] in
private theorem lamAux_inv (σ : KummerField E p u ≃ₐ[E] KummerField E p u) : lamAux E p u hζ σ⁻¹ = - lamAux E p u hζ σ := by
  have h := lamAux_mul E p u hζ σ σ⁻¹
  rw [mul_inv_cancel, lamAux_one] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

private def imageAddSubgroup : AddSubgroup (Fin t → ZMod p) where
  carrier := Set.range (lamAux E p u hζ)
  zero_mem' := ⟨1, lamAux_one E p u hζ⟩
  add_mem' := by
    rintro _ _ ⟨σ, rfl⟩ ⟨τ, rfl⟩
    exact ⟨σ * τ, lamAux_mul E p u hζ σ τ⟩
  neg_mem' := by
    rintro _ ⟨σ, rfl⟩
    exact ⟨σ⁻¹, lamAux_inv E p u hζ σ⟩

private def imageSubmodule : Submodule (ZMod p) (Fin t → ZMod p) :=
  AddSubgroup.toZModSubmodule p (imageAddSubgroup E p u hζ)

omit [NumberField k] [NumberField E] in
private theorem mem_imageSubmodule_iff (w : Fin t → ZMod p) :
    w ∈ imageSubmodule E p u hζ ↔ ∃ σ, lamAux E p u hζ σ = w := by
  simp only [imageSubmodule, AddSubgroup.mem_toZModSubmodule]
  rfl

omit [NumberField k] [NumberField E] in
private theorem lamAux_mem_imageSubmodule (σ : KummerField E p u ≃ₐ[E] KummerField E p u) :
    lamAux E p u hζ σ ∈ imageSubmodule E p u hζ :=
  (mem_imageSubmodule_iff E p u hζ _).mpr ⟨σ, rfl⟩

private abbrev zetaM : KummerField E p u := algebraMap E (KummerField E p u) (algebraMap k E ζ)

omit [NumberField k] [NumberField E] hp in
include hζ in
private theorem zetaM_isPrimitiveRoot : IsPrimitiveRoot (zetaM E p u (ζ := ζ)) p :=
  (zetaE_isPrimitiveRoot E p hζ).map_of_injective (algebraMap E (KummerField E p u)).injective

private def radProd (e : Fin t → ZMod p) : KummerField E p u := ∏ j, rad E p u j ^ (e j).val

omit [NumberField k] [NumberField E] in
private theorem map_radProd (σ : KummerField E p u ≃ₐ[E] KummerField E p u) (e : Fin t → ZMod p) :
    σ (radProd E p u e) = zetaM E p u (ζ := ζ) ^ (∑ j, lamAux E p u hζ σ j * e j).val * radProd E p u e := by
  unfold radProd
  rw [map_prod, zeta_pow_val_sum (zetaM_isPrimitiveRoot E p u hζ), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [map_pow, lamAux_spec E p u hζ σ j, mul_pow, zeta_pow_val_mul (zetaM_isPrimitiveRoot E p u hζ)]

omit [NumberField k] [NumberField E] in
private theorem radProd_pow (e : Fin t → ZMod p) :
    radProd E p u e ^ p = algebraMap E (KummerField E p u) (∏ j, radVal E u j ^ (e j).val) := by
  unfold radProd
  rw [map_prod, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← pow_mul, mul_comm, pow_mul, rad_pow' E p u j, map_pow]

omit [NumberField k] [NumberField E] in
include hζ in

private theorem exists_eq_algebraMap_of_forall_fixed (e : Fin t → ZMod p)
    (hfix : ∀ σ : KummerField E p u ≃ₐ[E] KummerField E p u, σ (radProd E p u e) = radProd E p u e) :
    ∃ g : E, algebraMap E (KummerField E p u) g = radProd E p u e := by
  haveI := isGalois_aux E p u hζ
  have hmem : radProd E p u e ∈ IntermediateField.fixedField
      (IntermediateField.fixingSubgroup (⊥ : IntermediateField E (KummerField E p u))) :=
    fun σ => hfix σ.1
  rw [IsGalois.fixedField_fixingSubgroup, IntermediateField.mem_bot] at hmem
  exact hmem

include hζ in
omit [NumberField k] [NumberField E] in

private theorem lamAux_surjective
    (hind : ∀ (e : Fin t → ℕ) (g : E), g ^ p = ∏ j, radVal E u j ^ e j → ∀ j, p ∣ e j) :
    Function.Surjective (lamAux E p u hζ) := by
  by_contra hns

  have hlt : imageSubmodule E p u hζ < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hns
    intro w
    exact (mem_imageSubmodule_iff E p u hζ w).mp (htop ▸ Submodule.mem_top)
  obtain ⟨f, hf0, hfW⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hlt inferInstance
  have hkill : ∀ σ : KummerField E p u ≃ₐ[E] KummerField E p u, f (lamAux E p u hζ σ) = 0 := fun σ => by
    have h : f (lamAux E p u hζ σ) ∈ (imageSubmodule E p u hζ).map f :=
      Submodule.mem_map_of_mem (lamAux_mem_imageSubmodule E p u hζ σ)
    rw [hfW] at h
    exact (Submodule.mem_bot _).mp h

  set e : Fin t → ZMod p := fun j => f (fun i => if j = i then 1 else 0) with he
  have hfe : ∀ w : Fin t → ZMod p, f w = ∑ j, w j * e j := fun w => by
    rw [LinearMap.pi_apply_eq_sum_univ f w]
    rfl

  have hfix : ∀ σ : KummerField E p u ≃ₐ[E] KummerField E p u, σ (radProd E p u e) = radProd E p u e := fun σ => by
    rw [map_radProd E p u hζ σ e, ← hfe, hkill σ, ZMod.val_zero, pow_zero, one_mul]
  obtain ⟨g, hg⟩ := exists_eq_algebraMap_of_forall_fixed E p u hζ e hfix

  have hrel : g ^ p = ∏ j, radVal E u j ^ (e j).val := by
    apply (algebraMap E (KummerField E p u)).injective
    rw [map_pow, hg, radProd_pow]
  have hdvd := hind (fun j => (e j).val) g hrel

  have he0 : ∀ j, e j = 0 := fun j =>
    (ZMod.val_eq_zero (e j)).mp (Nat.eq_zero_of_dvd_of_lt (hdvd j) (ZMod.val_lt (e j)))
  apply hf0
  refine LinearMap.ext fun w => ?_
  rw [hfe w, LinearMap.zero_apply]
  exact Finset.sum_eq_zero fun j _ => by rw [he0 j, mul_zero]

end P2F.PrimeAuxSet.Seam
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Residue P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.AuxField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Local"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Residue P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.AuxField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Local"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Residue P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.AuxField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Local"

end
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Residue P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.AuxField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Local"

set_option autoImplicit false

noncomputable section

namespace P2F
namespace PrimeAuxSet
namespace Descent

open P2F.PrimeAuxSet.Local

variable {k E : Type*} [Field k] [Field E] [Algebra k E] [IsGalois k E]
variable {p : ℕ} [hp : Fact p.Prime] (hdeg : Module.finrank k E = p) {ζ : k} (hζ : IsPrimitiveRoot ζ p)
variable {α : E} {a : k} (ha0 : a ≠ 0) (hα : α ^ p = algebraMap k E a) (hgen : ∀ σ : E ≃ₐ[k] E, σ α = α → σ = 1)

include hdeg hζ ha0 hα hgen in

private theorem exists_aut_apply_eq_zeta_mul :
    ∃ τ : E ≃ₐ[k] E, τ α = algebraMap k E ζ * α ∧
      ∀ ρ : E ≃ₐ[k] E, ∃ n : ℕ, ρ = τ ^ n := by
  haveI : Module.Finite k E := Module.finite_of_finrank_pos (by rw [hdeg]; exact hp.out.pos)

  have hr : ∀ i : Fin 1, (fun _ : Fin 1 => α) i ^ p = algebraMap k E ((fun _ : Fin 1 => a) i) := fun _ => hα
  have hy : ∀ i : Fin 1, (fun _ : Fin 1 => a) i ≠ 0 := fun _ => ha0
  have hgen' : ∀ σ : E ≃ₐ[k] E, (∀ i : Fin 1, σ ((fun _ : Fin 1 => α) i) = (fun _ : Fin 1 => α) i) → σ = 1 :=
    fun σ h => hgen σ (h 0)
  have hcard : Nat.card (E ≃ₐ[k] E) = p ^ (1 : ℕ) := by rw [IsGalois.card_aut_eq_finrank, hdeg, pow_one]
  have hbij := SignSpace.lam_bijective hζ (fun _ : Fin 1 => α) hr hy hgen' hcard
  obtain ⟨τ, hτ⟩ := hbij.2 (fun _ => (1 : ZMod p))
  refine ⟨τ, ?_, fun ρ => ?_⟩
  · have h := SignSpace.lam_spec hζ (fun _ : Fin 1 => α) hr hy τ 0
    rw [hτ] at h
    simpa [ZMod.val_one] using h
  · refine ⟨(SignSpace.lam hζ (fun _ : Fin 1 => α) hr hy ρ 0).val, ?_⟩
    apply hbij.1
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi

    have hpow : ∀ n : ℕ, SignSpace.lam hζ (fun _ : Fin 1 => α) hr hy (τ ^ n) 0 = (n : ZMod p) := by
      intro n
      induction n with
      | zero => simp [SignSpace.lam_one]
      | succ n ih => rw [pow_succ, SignSpace.lam_mul, Pi.add_apply, ih, hτ]; push_cast; ring
    rw [hpow, ZMod.natCast_zmod_val]

include hdeg hζ ha0 hα hgen in

private theorem exists_pow_mul_eq_pow {c : k} (hc : c ≠ 0) {g : E} (hg : g ^ p = algebraMap k E c) :
    ∃ (m : ℕ) (d : k), a ^ m * c = d ^ p := by
  haveI : Module.Finite k E := Module.finite_of_finrank_pos (by rw [hdeg]; exact hp.out.pos)
  obtain ⟨τ, hτα, hτgen⟩ := exists_aut_apply_eq_zeta_mul hdeg hζ ha0 hα hgen
  have hζE : IsPrimitiveRoot (algebraMap k E ζ) p := hζ.map_of_injective (algebraMap k E).injective

  obtain ⟨j, -, hτg⟩ := SignSpace.exists_pow_mul hζ (fun _ : Fin 1 => g) (fun _ => hg) (fun _ => hc) τ 0

  set m : ℕ := (-(j : ZMod p)).val with hm
  set δ : E := g * α ^ m with hδ
  have hτδ : τ δ = δ := by
    rw [hδ, map_mul, map_pow, hτg, hτα, mul_pow]
    have h1 : algebraMap k E ζ ^ j * algebraMap k E ζ ^ m = 1 := by
      rw [← pow_add, ← pow_zero (algebraMap k E ζ), zeta_pow_eq_iff hζE]
      rw [hm]
      push_cast
      rw [ZMod.natCast_zmod_val]
      ring
    calc algebraMap k E ζ ^ j * g * (algebraMap k E ζ ^ m * α ^ m)
        = (algebraMap k E ζ ^ j * algebraMap k E ζ ^ m) * (g * α ^ m) := by ring
      _ = g * α ^ m := by rw [h1, one_mul]
  have hfix : ∀ ρ : E ≃ₐ[k] E, ρ δ = δ := by
    intro ρ
    obtain ⟨n, rfl⟩ := hτgen ρ
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', AlgEquiv.mul_apply, ih, hτδ]

  have hmem : δ ∈ IntermediateField.fixedField (IntermediateField.fixingSubgroup (⊥ : IntermediateField k E)) :=
    fun ρ => hfix ρ.1
  rw [IsGalois.fixedField_fixingSubgroup, IntermediateField.mem_bot] at hmem
  obtain ⟨d, hd⟩ := hmem
  refine ⟨m, d, (algebraMap k E).injective ?_⟩
  rw [map_pow, hd, hδ, mul_pow, hg, ← pow_mul, mul_comm m p, pow_mul, hα, ← map_pow, ← map_mul, mul_comm]

end P2F.PrimeAuxSet.Descent
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Residue P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.AuxField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Local"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Residue P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.AuxField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Local"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Residue P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.AuxField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Local"

end
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Residue P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.AuxField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Local"

set_option autoImplicit false

p2m_open "IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.NumberField IsLocalRing"
open M4aLocalCFT.SquareClassLocal (unitsIncl coe_unitsIncl mem_range_unitsIncl_iff unitsIncl_injective
  residueUnits_surjective)

noncomputable section

namespace P2F
namespace PrimeAuxSet
namespace LocalClass

variable {k : Type*} [Field k] [NumberField k] (v : HeightOneSpectrum (𝓞 k))

local notation "Kᵥ" => HeightOneSpectrum.adicCompletion k v
local notation "𝒪ᵥ" => HeightOneSpectrum.adicCompletionIntegers k v

private theorem isUnit_natCast_of_notMem (p : ℕ) (hv : (p : 𝓞 k) ∉ v.asIdeal) : IsUnit (p : 𝒪ᵥ) := by
  rw [adicCompletionIntegers.isUnit_iff_valued_eq_one]
  have e1 : ((p : 𝒪ᵥ) : Kᵥ) = algebraMap k Kᵥ (algebraMap (𝓞 k) k p) := by
    rw [map_natCast, map_natCast]
    exact map_natCast (HeightOneSpectrum.adicCompletionIntegers k v).subtype p
  have e2 : Valued.v (algebraMap k Kᵥ (algebraMap (𝓞 k) k p)) = v.valuation k (algebraMap (𝓞 k) k p) :=
    valuedAdicCompletion_eq_valuation' v _
  rw [show (p : 𝒪ᵥ).1 = ((p : 𝒪ᵥ) : Kᵥ) from rfl, e1, e2]
  exact (valuation_eq_one_iff_notMem (K := k) (v := v)).mpr hv

private theorem exists_pow_eq_of_residue_pow {p : ℕ} [hp : Fact p.Prime] (hpu : IsUnit (p : 𝒪ᵥ)) (x : (𝒪ᵥ)ˣ)
    {z : (ResidueField 𝒪ᵥ)ˣ} (hz : Units.map (IsLocalRing.residue 𝒪ᵥ).toMonoidHom x = z ^ p) :
    ∃ c : (𝒪ᵥ)ˣ, c ^ p = x := by
  obtain ⟨w, rfl⟩ := residueUnits_surjective v z
  have hker : Units.map (IsLocalRing.residue 𝒪ᵥ).toMonoidHom (x * (w ^ p)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_pow, hz, mul_inv_cancel]
  have hres : IsLocalRing.residue 𝒪ᵥ ((x * (w ^ p)⁻¹ : (𝒪ᵥ)ˣ) : 𝒪ᵥ) = 1 := by
    simpa using congrArg (fun u : (ResidueField 𝒪ᵥ)ˣ => (u : ResidueField 𝒪ᵥ)) hker
  have hmem : ((x * (w ^ p)⁻¹ : (𝒪ᵥ)ˣ) : 𝒪ᵥ) - 1 ∈ maximalIdeal 𝒪ᵥ := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_one, hres, sub_self]
  obtain ⟨a, ha, -⟩ := exists_nthRoot_of_sub_one_mem_maximalIdeal hmem (n := p) hpu
  have haU : IsUnit a := by
    rw [← isUnit_pow_iff hp.out.ne_zero, ha]
    exact Units.isUnit _
  refine ⟨haU.unit * w, Units.ext ?_⟩
  rw [Units.val_pow_eq_pow_val, Units.val_mul, IsUnit.unit_spec, mul_pow, ha,
    ← Units.val_pow_eq_pow_val, ← Units.val_mul, inv_mul_cancel_right]

private theorem exists_pow_eq_of_residue_eq_pow {p : ℕ} [hp : Fact p.Prime] (hpu : IsUnit (p : 𝒪ᵥ)) (x : (𝒪ᵥ)ˣ)
    {z : ResidueField 𝒪ᵥ} (hz : IsLocalRing.residue 𝒪ᵥ (x : 𝒪ᵥ) = z ^ p) : ∃ c : (𝒪ᵥ)ˣ, c ^ p = x := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.out.ne_zero] at hz
    exact (IsLocalRing.residue_ne_zero_iff_isUnit (x : 𝒪ᵥ)).mpr x.isUnit hz
  refine exists_pow_eq_of_residue_pow v hpu x (z := Units.mk0 z hz0) (Units.ext ?_)
  rw [Units.val_pow_eq_pow_val, Units.val_mk0]
  exact hz

private def toUnit (y : (Kᵥ)ˣ) (hy : Valued.v (y : Kᵥ) = 1) : (𝒪ᵥ)ˣ :=
  ((mem_range_unitsIncl_iff v y).mpr hy).choose

private theorem unitsIncl_toUnit (y : (Kᵥ)ˣ) (hy : Valued.v (y : Kᵥ) = 1) : unitsIncl v (toUnit v y hy) = y :=
  ((mem_range_unitsIncl_iff v y).mpr hy).choose_spec

private theorem toUnit_eq_of_unitsIncl_eq {y : (Kᵥ)ˣ} (hy : Valued.v (y : Kᵥ) = 1) {u : (𝒪ᵥ)ˣ}
    (hu : unitsIncl v u = y) : toUnit v y hy = u :=
  unitsIncl_injective v (by rw [unitsIncl_toUnit, hu])

private theorem valued_mul_inv_eq_one {x y : (Kᵥ)ˣ} (hx : Valued.v (x : Kᵥ) = 1) (hy : Valued.v (y : Kᵥ) = 1) :
    Valued.v ((x * y⁻¹ : (Kᵥ)ˣ) : Kᵥ) = 1 := by
  rw [Units.val_mul, map_mul, hx, Units.val_inv_eq_inv_val, map_inv₀, hy, inv_one, mul_one]

private theorem toUnit_mul_inv {x y : (Kᵥ)ˣ} (hx : Valued.v (x : Kᵥ) = 1) (hy : Valued.v (y : Kᵥ) = 1) :
    toUnit v (x * y⁻¹) (valued_mul_inv_eq_one v hx hy) = toUnit v x hx * (toUnit v y hy)⁻¹ :=
  toUnit_eq_of_unitsIncl_eq v _ (by rw [map_mul, map_inv, unitsIncl_toUnit, unitsIncl_toUnit])

private theorem exists_eq_pow_of_residue {p : ℕ} [Fact p.Prime] (hv : (p : 𝓞 k) ∉ v.asIdeal) (y : (Kᵥ)ˣ)
    (hy : Valued.v (y : Kᵥ) = 1) {z : ResidueField 𝒪ᵥ}
    (hz : IsLocalRing.residue 𝒪ᵥ ((toUnit v y hy : (𝒪ᵥ)ˣ) : 𝒪ᵥ) = z ^ p) : ∃ c : (Kᵥ)ˣ, y = c ^ p := by
  obtain ⟨c, hc⟩ := exists_pow_eq_of_residue_eq_pow v (isUnit_natCast_of_notMem v p hv) (toUnit v y hy) hz
  exact ⟨unitsIncl v c, by rw [← map_pow, hc, unitsIncl_toUnit]⟩

private def resHom : 𝓞 k →+* ResidueField 𝒪ᵥ :=
  (IsLocalRing.residue 𝒪ᵥ).comp (algebraMap (𝓞 k) 𝒪ᵥ)

private theorem resHom_apply (x : 𝓞 k) : resHom v x = IsLocalRing.residue 𝒪ᵥ (algebraMap (𝓞 k) 𝒪ᵥ x) := rfl

section Uniformizer

variable {π : 𝓞 k} (hπ : v.intValuation π = WithZero.exp (-((1 : ℕ) : ℤ)))
include hπ

private theorem uniformizer_mem : π ∈ v.asIdeal := by
  have h : π ∈ RingHom.ker (M4aKummer.quotMapHom v π) :=
    RingHom.mem_ker.mpr (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _))
  rwa [M4aKummer.ker_quotMapHom v π hπ, pow_one] at h

private theorem not_isUnit_algebraMap_uniformizer : ¬ IsUnit (algebraMap (𝓞 k) 𝒪ᵥ π) := by
  rw [adicCompletionIntegers.isUnit_iff_valued_eq_one]
  have e : (algebraMap (𝓞 k) 𝒪ᵥ π).1 = algebraMap k Kᵥ (algebraMap (𝓞 k) k π) := rfl
  have e2 : Valued.v (algebraMap k Kᵥ (algebraMap (𝓞 k) k π)) = v.valuation k (algebraMap (𝓞 k) k π) :=
    valuedAdicCompletion_eq_valuation' v _
  rw [e, e2]
  exact fun h => (valuation_eq_one_iff_notMem (K := k) (v := v)).mp h (uniformizer_mem v hπ)

private theorem span_uniformizer_le_maximalIdeal :
    Ideal.span {algebraMap (𝓞 k) 𝒪ᵥ π} ≤ maximalIdeal 𝒪ᵥ := by
  rw [Ideal.span_singleton_le_iff_mem, IsLocalRing.mem_maximalIdeal]
  exact not_isUnit_algebraMap_uniformizer v hπ

private theorem factor_comp_quotMapHom :
    (Ideal.Quotient.factor (span_uniformizer_le_maximalIdeal v hπ)).comp (M4aKummer.quotMapHom v π) = resHom v := by
  ext x
  rfl

private theorem resHom_surjective : Function.Surjective (resHom v) := fun z => by
  obtain ⟨q, hq⟩ := Ideal.Quotient.factor_surjective (span_uniformizer_le_maximalIdeal v hπ) z
  obtain ⟨y, hy⟩ := M4aKummer.quotMapHom_surjective v π hπ q
  exact ⟨y, (congrArg (Ideal.Quotient.factor (span_uniformizer_le_maximalIdeal v hπ)) hy).trans hq⟩

private theorem resHom_eq_zero_of_mem {x : 𝓞 k} (hx : x ∈ v.asIdeal) : resHom v x = 0 := by
  have hker : x ∈ RingHom.ker (M4aKummer.quotMapHom v π) := by
    rw [M4aKummer.ker_quotMapHom v π hπ, pow_one]; exact hx
  have h0 : M4aKummer.quotMapHom v π x = 0 := RingHom.mem_ker.mp hker
  exact (congrArg (Ideal.Quotient.factor (span_uniformizer_le_maximalIdeal v hπ)) h0).trans (map_zero _)

end Uniformizer
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Residue P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.AuxField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Local"

private theorem exists_uniformizer_exp_one : ∃ π : 𝓞 k, v.intValuation π = WithZero.exp (-((1 : ℕ) : ℤ)) := by
  obtain ⟨π, hπ⟩ := v.intValuation_exists_uniformizer
  exact ⟨π, by rw [hπ]; simp⟩

private theorem resHom_surjective' : Function.Surjective (resHom v) :=
  resHom_surjective v (exists_uniformizer_exp_one v).choose_spec

private theorem resHom_eq_zero_of_mem' {x : 𝓞 k} (hx : x ∈ v.asIdeal) : resHom v x = 0 :=
  resHom_eq_zero_of_mem v (exists_uniformizer_exp_one v).choose_spec hx

private def resQuotHom : (𝓞 k ⧸ v.asIdeal) →+* ResidueField 𝒪ᵥ :=
  Ideal.Quotient.lift v.asIdeal (resHom v) fun _ hx => resHom_eq_zero_of_mem' v hx

private theorem resQuotHom_mk (x : 𝓞 k) : resQuotHom v (Ideal.Quotient.mk v.asIdeal x) = resHom v x :=
  Ideal.Quotient.lift_mk _ _ _

private theorem resQuotHom_surjective : Function.Surjective (resQuotHom v) := fun z => by
  obtain ⟨x, hx⟩ := resHom_surjective' v z
  exact ⟨Ideal.Quotient.mk _ x, by rw [resQuotHom_mk, hx]⟩

private theorem residue_toUnit_algebraMap (s : 𝓞 k) (hs : Valued.v ((algebraMap (𝓞 k) Kᵥ s : Kᵥ)) = 1)
    (y : (Kᵥ)ˣ) (hys : (y : Kᵥ) = algebraMap (𝓞 k) Kᵥ s) (hy : Valued.v (y : Kᵥ) = 1) :
    IsLocalRing.residue 𝒪ᵥ ((toUnit v y hy : (𝒪ᵥ)ˣ) : 𝒪ᵥ) = resHom v s := by
  have hsU : IsUnit (algebraMap (𝓞 k) 𝒪ᵥ s) := by
    rw [adicCompletionIntegers.isUnit_iff_valued_eq_one]; exact hs
  have h := toUnit_eq_of_unitsIncl_eq v hy (u := hsU.unit)
    (Units.ext (by rw [coe_unitsIncl, IsUnit.unit_spec]; exact hys.symm))
  rw [h, IsUnit.unit_spec, resHom_apply]

end P2F.PrimeAuxSet.LocalClass
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Residue P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.AuxField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Local"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Residue P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.AuxField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Local"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Residue P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.AuxField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Local"

end
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Residue P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.AuxField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Local"

set_option autoImplicit false

p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing"
open P2F.PrimeAuxSet.LocalClass

noncomputable section

namespace P2F
namespace PrimeAuxSet
namespace LocalSurj

private scoped instance neZero_of_fact_prime {p : ℕ} [hp : Fact p.Prime] : NeZero p := ⟨hp.out.ne_zero⟩

attribute [local instance] Ideal.Quotient.field

variable {k : Type*} [Field k] [NumberField k] {p : ℕ} [hp : Fact p.Prime]

section Furniture

variable (v : HeightOneSpectrum (𝓞 k))

private theorem exists_num_den_notMem {x : k} (hx : v.valuation k x = 1) :
    ∃ n d : 𝓞 k, n ∉ v.asIdeal ∧ d ∉ v.asIdeal ∧ x * algebraMap (𝓞 k) k d = algebraMap (𝓞 k) k n := by
  obtain ⟨n, d, h⟩ := v.exists_primeCompl_mul_eq_of_integer (K := k) x (le_of_eq hx)
  have hd1 : v.intValuation d.1 = 1 := by
    refine le_antisymm (v.intValuation_le_one d.1)
      (not_lt.mp fun hlt => d.2 ((v.intValuation_lt_one_iff_mem d.1).mp hlt))
  have hn1 : v.intValuation n = 1 := by
    have hv : v.valuation k (algebraMap (𝓞 k) k n) = 1 := by
      rw [← h, Valuation.map_mul, hx, one_mul, valuation_of_algebraMap (K := k) v, hd1]
    rwa [valuation_of_algebraMap (K := k) v] at hv
  exact ⟨n, d.1, fun hmem => absurd hn1 (ne_of_lt ((v.intValuation_lt_one_iff_mem n).mpr hmem)), d.2, h⟩

omit [NumberField k] in
private theorem prod_pow_notMem {t : ℕ} {f : Fin t → 𝓞 k} (hf : ∀ j, f j ∉ v.asIdeal) (c : Fin t → ℕ) :
    ∏ j, f j ^ c j ∉ v.asIdeal := by
  classical
  induction (Finset.univ : Finset (Fin t)) using Finset.induction_on with
  | empty => rw [Finset.prod_empty]; exact v.isPrime.one_notMem
  | insert j s hj ih =>
    rw [Finset.prod_insert hj]
    intro hmem
    rcases v.isPrime.mem_or_mem hmem with h | h
    · exact hf j (v.isPrime.mem_of_pow_mem _ h)
    · exact ih h

omit [NumberField k] in
private theorem mul_pow_notMem {n d : 𝓞 k} (hn : n ∉ v.asIdeal) (hd : d ∉ v.asIdeal) (m : ℕ) :
    n * d ^ m ∉ v.asIdeal := by
  intro hmem
  rcases v.isPrime.mem_or_mem hmem with h | h
  · exact hn h
  · exact hd (v.isPrime.mem_of_pow_mem _ h)

omit [NumberField k] in
private theorem mk_ne_zero_of_notMem {y : 𝓞 k} (hy : y ∉ v.asIdeal) : Ideal.Quotient.mk v.asIdeal y ≠ 0 :=
  fun h0 => hy (Ideal.Quotient.eq_zero_iff_mem.mp h0)

omit [NumberField k] in
private theorem ne_zero_of_notMem {y : 𝓞 k} (hy : y ∉ v.asIdeal) : y ≠ 0 := fun h0 => hy (h0 ▸ v.asIdeal.zero_mem)

omit [NumberField k] in
private theorem algebraMap_ne_zero_of_notMem {y : 𝓞 k} (hy : y ∉ v.asIdeal) : algebraMap (𝓞 k) k y ≠ 0 :=
  (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 k) k)).mpr (ne_zero_of_notMem v hy)

private theorem valuation_algebraMap_eq_one_of_notMem {y : 𝓞 k} (hy : y ∉ v.asIdeal) :
    v.valuation k (algebraMap (𝓞 k) k y) = 1 :=
  (valuation_eq_one_iff_notMem (K := k) (v := v)).mpr hy

end Furniture
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Residue P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.AuxField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Local"

omit [NumberField k] in

private theorem mul_pow_eq (x : k) {n d : 𝓞 k} (hnd : x * algebraMap (𝓞 k) k d = algebraMap (𝓞 k) k n) :
    x * algebraMap (𝓞 k) k d ^ p = algebraMap (𝓞 k) k n * algebraMap (𝓞 k) k d ^ (p - 1) := by
  rw [← hnd]
  conv_lhs => rw [show p = p - 1 + 1 from (Nat.sub_add_cancel hp.out.one_le).symm]
  ring

omit [NumberField k] in

private theorem mul_pow_eq' (x : k) {n d : 𝓞 k} (hnd : x * algebraMap (𝓞 k) k d = algebraMap (𝓞 k) k n) :
    x * algebraMap (𝓞 k) k d ^ p = algebraMap (𝓞 k) k (n * d ^ (p - 1)) := by
  rw [map_mul, map_pow]
  exact mul_pow_eq x hnd

omit [NumberField k] in

private theorem coe_prod_mul_pow_eq {t : ℕ} (u : Fin t → kˣ) (n d : Fin t → 𝓞 k)
    (hnd : ∀ j, (u j : k) * algebraMap (𝓞 k) k (d j) = algebraMap (𝓞 k) k (n j)) (c : Fin t → ℕ) :
    ((∏ j, u j ^ c j : kˣ) : k) * algebraMap (𝓞 k) k (∏ j, d j ^ c j) ^ p
      = algebraMap (𝓞 k) k (∏ j, (n j * d j ^ (p - 1)) ^ c j) := by
  rw [Units.coe_prod, map_prod, map_prod, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp only [Units.val_pow_eq_pow_val, map_pow, map_mul]
  rw [← mul_pow_eq (u j : k) (hnd j)]
  ring

private theorem valuation_coe_prod_eq_one {t : ℕ} (u : Fin t → kˣ) (S : Finset (HeightOneSpectrum (𝓞 k)))
    (hu : ∀ j, ∀ v : HeightOneSpectrum (𝓞 k), v ∉ S → v.valuation k (u j : k) = 1) (c : Fin t → ℕ)
    (v : HeightOneSpectrum (𝓞 k)) (hv : v ∉ S) : v.valuation k ((∏ j, u j ^ c j : kˣ) : k) = 1 := by
  rw [Units.coe_prod, map_prod]
  refine Finset.prod_eq_one fun j _ => ?_
  rw [Units.val_pow_eq_pow_val, map_pow, hu j v hv, one_pow]

section OnePlace

variable (v : HeightOneSpectrum (𝓞 k))

local notation "Kᵥ" => HeightOneSpectrum.adicCompletion k v
local notation "𝒪ᵥ" => HeightOneSpectrum.adicCompletionIntegers k v

private theorem algebraMap_int_eq (y : 𝓞 k) : algebraMap (𝓞 k) Kᵥ y = algebraMap k Kᵥ (algebraMap (𝓞 k) k y) := rfl

private theorem valued_algebraMap_eq_of_valuation (y : k) : Valued.v (algebraMap k Kᵥ y) = v.valuation k y :=
  valuedAdicCompletion_eq_valuation' v y

private theorem valued_algebraMap_int_eq_one {y : 𝓞 k} (hy : y ∉ v.asIdeal) : Valued.v (algebraMap (𝓞 k) Kᵥ y) = 1 := by
  rw [algebraMap_int_eq, valued_algebraMap_eq_of_valuation]
  exact valuation_algebraMap_eq_one_of_notMem v hy

private theorem ne_zero_of_valued_eq_one {y : Kᵥ} (hy : Valued.v y = 1) : y ≠ 0 := by
  intro h0
  rw [h0, map_zero] at hy
  exact zero_ne_one hy

private def intUnit {y : 𝓞 k} (hy : y ∉ v.asIdeal) : (Kᵥ)ˣ :=
  Units.mk0 (algebraMap (𝓞 k) Kᵥ y) (ne_zero_of_valued_eq_one v (valued_algebraMap_int_eq_one v hy))

private theorem intUnit_coe {y : 𝓞 k} (hy : y ∉ v.asIdeal) : ((intUnit v hy : (Kᵥ)ˣ) : Kᵥ) = algebraMap (𝓞 k) Kᵥ y := rfl

private theorem valued_intUnit {y : 𝓞 k} (hy : y ∉ v.asIdeal) : Valued.v ((intUnit v hy : (Kᵥ)ˣ) : Kᵥ) = 1 :=
  valued_algebraMap_int_eq_one v hy

private theorem residue_toUnit_intUnit {y : 𝓞 k} (hy : y ∉ v.asIdeal) :
    IsLocalRing.residue 𝒪ᵥ ((toUnit v (intUnit v hy) (valued_intUnit v hy) : (𝒪ᵥ)ˣ) : 𝒪ᵥ) = resHom v y :=
  residue_toUnit_algebraMap v y (valued_algebraMap_int_eq_one v hy) (intUnit v hy) rfl (valued_intUnit v hy)

private theorem residue_coe_ne_zero (w : (𝒪ᵥ)ˣ) : IsLocalRing.residue 𝒪ᵥ (w : 𝒪ᵥ) ≠ 0 :=
  (IsLocalRing.residue_ne_zero_iff_isUnit (w : 𝒪ᵥ)).mpr w.isUnit

private theorem resHom_ne_zero_of_notMem {y : 𝓞 k} (hy : y ∉ v.asIdeal) : resHom v y ≠ 0 := by
  rw [← residue_toUnit_intUnit v hy]
  exact residue_coe_ne_zero v _

private theorem residue_coe_inv (w : (𝒪ᵥ)ˣ) :
    IsLocalRing.residue 𝒪ᵥ ((w⁻¹ : (𝒪ᵥ)ˣ) : 𝒪ᵥ) = (IsLocalRing.residue 𝒪ᵥ (w : 𝒪ᵥ))⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]

private theorem valued_units_map_eq_one (s : kˣ) (hs : v.valuation k (s : k) = 1) :
    Valued.v ((Units.map (algebraMap k Kᵥ : k →* Kᵥ) s : (Kᵥ)ˣ) : Kᵥ) = 1 := by
  rw [Units.coe_map, MonoidHom.coe_coe, valued_algebraMap_eq_of_valuation, hs]

omit hp in

private theorem units_map_mul_pow_eq {X D : 𝓞 k} (hX : X ∉ v.asIdeal) (hD : D ∉ v.asIdeal) (s : kˣ)
    (hsXD : (s : k) * algebraMap (𝓞 k) k D ^ p = algebraMap (𝓞 k) k X) :
    Units.map (algebraMap k Kᵥ : k →* Kᵥ) s * intUnit v hD ^ p = intUnit v hX := by
  ext
  rw [Units.val_mul, Units.val_pow_eq_pow_val, intUnit_coe, intUnit_coe, Units.coe_map, MonoidHom.coe_coe,
    algebraMap_int_eq, algebraMap_int_eq, ← map_pow, ← map_mul, hsXD]

private theorem exists_mul_inv_eq_pow (hpv : (p : 𝓞 k) ∉ v.asIdeal) {X D : 𝓞 k} (hX : X ∉ v.asIdeal) (hD : D ∉ v.asIdeal)
    (s : kˣ) (hs : v.valuation k (s : k) = 1) (hsXD : (s : k) * algebraMap (𝓞 k) k D ^ p = algebraMap (𝓞 k) k X)
    (x : (Kᵥ)ˣ) (hx : Valued.v (x : Kᵥ) = 1) {z : ResidueField 𝒪ᵥ}
    (hres : IsLocalRing.residue 𝒪ᵥ ((toUnit v x hx : (𝒪ᵥ)ˣ) : 𝒪ᵥ) = resHom v X * z ^ p) :
    ∃ c : (Kᵥ)ˣ, x * (Units.map (algebraMap k Kᵥ : k →* Kᵥ) s)⁻¹ = c ^ p := by
  set su : (Kᵥ)ˣ := Units.map (algebraMap k Kᵥ : k →* Kᵥ) s with hsu_def
  have hsv : Valued.v (su : Kᵥ) = 1 := valued_units_map_eq_one v s hs

  have htU : toUnit v (intUnit v hX) (valued_intUnit v hX)
      = toUnit v su hsv * (toUnit v (intUnit v hD) (valued_intUnit v hD)) ^ p :=
    toUnit_eq_of_unitsIncl_eq v (valued_intUnit v hX) (by
      rw [map_mul, map_pow, unitsIncl_toUnit, unitsIncl_toUnit]
      exact units_map_mul_pow_eq v hX hD s hsXD)

  have hb : IsLocalRing.residue 𝒪ᵥ ((toUnit v su hsv : (𝒪ᵥ)ˣ) : 𝒪ᵥ) * resHom v D ^ p = resHom v X := by
    rw [← residue_toUnit_intUnit v hD, ← residue_toUnit_intUnit v hX, htU, Units.val_mul, Units.val_pow_eq_pow_val,
      map_mul, map_pow]
  have hb0 : IsLocalRing.residue 𝒪ᵥ ((toUnit v su hsv : (𝒪ᵥ)ˣ) : 𝒪ᵥ) ≠ 0 := residue_coe_ne_zero v _
  have hD0 : resHom v D ≠ 0 := resHom_ne_zero_of_notMem v hD
  refine exists_eq_pow_of_residue v hpv (x * su⁻¹) (valued_mul_inv_eq_one v hx hsv) (z := z * resHom v D) ?_
  rw [toUnit_mul_inv v hx hsv, Units.val_mul, map_mul, residue_coe_inv, hres, ← hb]
  field_simp
  ring

end OnePlace
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Residue P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.AuxField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Local"

section Surjection

variable {ζ : 𝓞 k} (hζ : IsPrimitiveRoot ζ p) {t : ℕ} (u : Fin t → kˣ) (S : Finset (HeightOneSpectrum (𝓞 k)))
variable (hu : ∀ j, ∀ v : HeightOneSpectrum (𝓞 k), v ∉ S → v.valuation k (u j : k) = 1)
variable (vv : Fin t → HeightOneSpectrum (𝓞 k)) (hvS : ∀ i, vv i ∉ S) (hvp : ∀ i, (p : 𝓞 k) ∉ (vv i).asIdeal)
variable (L : Fin t → Fin t → ZMod p)
variable (hsym : ∀ (i j : Fin t) (n d : 𝓞 k), n ∉ (vv i).asIdeal → d ∉ (vv i).asIdeal →
  (u j : k) * algebraMap (𝓞 k) k d = algebraMap (𝓞 k) k n →
  (Ideal.Quotient.mk (vv i).asIdeal (n * d ^ (p - 1))) ^ ((Nat.card (𝓞 k ⧸ (vv i).asIdeal) - 1) / p)
    = (Ideal.Quotient.mk (vv i).asIdeal ζ) ^ (L i j).val)

include hζ hu hvS hvp hsym in

private theorem row_eq_of_eq {i i' : Fin t} (h : vv i = vv i') : L i = L i' := by
  haveI := (vv i).isMaximal
  have hζi := Residue.residue_isPrimitiveRoot (vv i) (hvp i) hζ
  funext j
  obtain ⟨n, d, hn, hd, hnd⟩ := exists_num_den_notMem (vv i) (hu j (vv i) (hvS i))
  have h1 := hsym i j n d hn hd hnd
  have h2 := hsym i' j n d (by rw [← h]; exact hn) (by rw [← h]; exact hd) hnd
  rw [← h] at h2
  have h12 := (Local.zeta_pow_eq_iff hζi _ _).mp (h1.symm.trans h2)
  rwa [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at h12

include hζ hu hvS hvp hsym in
private theorem vv_injective (hL : LinearIndependent (ZMod p) L) : Function.Injective vv := fun _ _ h =>
  hL.injective (row_eq_of_eq hζ u S hu vv hvS hvp L hsym h)

include hζ hu hvS hvp hsym in

private theorem exists_sUnit_forall_mul_inv_eq_pow (hL : LinearIndependent (ZMod p) L)
    (x : (v : HeightOneSpectrum (𝓞 k)) → (v.adicCompletion k)ˣ)
    (hx : ∀ i, Valued.v ((x (vv i) : ((vv i).adicCompletion k)ˣ) : (vv i).adicCompletion k) = 1) :
    ∃ s : kˣ, (∀ v : HeightOneSpectrum (𝓞 k), v ∉ S → v.valuation k (s : k) = 1) ∧
      ∀ i, ∃ c : ((vv i).adicCompletion k)ˣ,
        x (vv i) * (Units.map (algebraMap k ((vv i).adicCompletion k) : k →* (vv i).adicCompletion k) s)⁻¹ = c ^ p := by
  classical

  have hdata : ∀ i, ∃ (y : 𝓞 k ⧸ (vv i).asIdeal) (e : ZMod p),
      resQuotHom (vv i) y
          = IsLocalRing.residue ((vv i).adicCompletionIntegers k)
              ((toUnit (vv i) (x (vv i)) (hx i) : ((vv i).adicCompletionIntegers k)ˣ) : (vv i).adicCompletionIntegers k) ∧
        y ≠ 0 ∧
        y ^ ((Nat.card (𝓞 k ⧸ (vv i).asIdeal) - 1) / p) = (Ideal.Quotient.mk (vv i).asIdeal ζ) ^ e.val := by
    intro i
    haveI := (vv i).isMaximal
    haveI : Finite (𝓞 k ⧸ (vv i).asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ (vv i).ne_bot
    letI : Fintype (𝓞 k ⧸ (vv i).asIdeal) := Fintype.ofFinite _
    have hζi := Residue.residue_isPrimitiveRoot (vv i) (hvp i) hζ
    obtain ⟨y, hy⟩ := resQuotHom_surjective (vv i)
      (IsLocalRing.residue ((vv i).adicCompletionIntegers k)
        ((toUnit (vv i) (x (vv i)) (hx i) : ((vv i).adicCompletionIntegers k)ˣ) : (vv i).adicCompletionIntegers k))
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [map_zero] at hy
      exact residue_coe_ne_zero (vv i) _ hy.symm
    obtain ⟨e, he⟩ := Local.exists_symbol hζi y hy0
    refine ⟨y, e, hy, hy0, ?_⟩
    have hnn' : (Nat.card (𝓞 k ⧸ (vv i).asIdeal) - 1) / p = Local.nn (𝓞 k ⧸ (vv i).asIdeal) p := by
      simp only [Local.nn, Nat.card_eq_fintype_card]
    rw [hnn']
    exact he
  choose y e hy hy0 hye using hdata

  obtain ⟨c, hc⟩ := SignSpace.exists_nat_exponents L hL e
  set cz : Fin t → ZMod p := fun j => (c j : ZMod p) with hcz_def
  refine ⟨∏ j, u j ^ (cz j).val, valuation_coe_prod_eq_one u S hu _, fun i => ?_⟩
  haveI := (vv i).isMaximal
  haveI : Finite (𝓞 k ⧸ (vv i).asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ (vv i).ne_bot
  letI : Fintype (𝓞 k ⧸ (vv i).asIdeal) := Fintype.ofFinite _
  have hζi := Residue.residue_isPrimitiveRoot (vv i) (hvp i) hζ
  have hnn : (Nat.card (𝓞 k ⧸ (vv i).asIdeal) - 1) / p = Local.nn (𝓞 k ⧸ (vv i).asIdeal) p := by
    simp only [Local.nn, Nat.card_eq_fintype_card]

  choose n d hn hd hnd using fun j => exists_num_den_notMem (vv i) (hu j (vv i) (hvS i))
  have hX : ∏ j, (n j * d j ^ (p - 1)) ^ (cz j).val ∉ (vv i).asIdeal :=
    prod_pow_notMem (vv i) (fun j => mul_pow_notMem (vv i) (hn j) (hd j) _) _
  have hD : ∏ j, d j ^ (cz j).val ∉ (vv i).asIdeal := prod_pow_notMem (vv i) hd _

  have hXsym : (Ideal.Quotient.mk (vv i).asIdeal (∏ j, (n j * d j ^ (p - 1)) ^ (cz j).val))
      ^ Local.nn (𝓞 k ⧸ (vv i).asIdeal) p = (Ideal.Quotient.mk (vv i).asIdeal ζ) ^ (e i).val := by
    have h := Local.prod_pow_nn_eq hζi (fun j => Ideal.Quotient.mk (vv i).asIdeal (n j * d j ^ (p - 1))) (L i) cz
      (fun j => by rw [← hnn]; exact hsym i j (n j) (d j) (hn j) (hd j) (hnd j))
    have hsum : ∑ j, L i j * cz j = e i := by
      rw [← hc i]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [hsum] at h
    rw [map_prod]
    simp only [map_pow]
    exact h
  have hye' := hye i
  rw [hnn] at hye'
  obtain ⟨zq, hzq⟩ := Local.exists_pow_mul_of_symbol_eq hζi (hy0 i) (mk_ne_zero_of_notMem (vv i) hX) (e i) hye' hXsym
  have hfin : resQuotHom (vv i) (y i)
      = resHom (vv i) (∏ j, (n j * d j ^ (p - 1)) ^ (cz j).val) * (resQuotHom (vv i) zq) ^ p := by
    rw [hzq, map_mul, map_pow, resQuotHom_mk]
  exact exists_mul_inv_eq_pow (vv i) (hvp i) hX hD _ (valuation_coe_prod_eq_one u S hu _ (vv i) (hvS i))
    (coe_prod_mul_pow_eq u n d hnd _) (x (vv i)) (hx i) (z := resQuotHom (vv i) zq) ((hy i).symm.trans hfin)

end Surjection
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Residue P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.AuxField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Local"

end P2F.PrimeAuxSet.LocalSurj
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Residue P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.AuxField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Local P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.LocalSurj"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Residue P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.AuxField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Local"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Residue P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.AuxField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Local"

end
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Residue P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.AuxField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Local P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.LocalSurj"

set_option autoImplicit false

p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin"
open P2F.PrimeAuxSet.AuxField P2F.PrimeAuxSet.LocalSurj P2F.PrimeAuxSet.LocalClass

noncomputable section

namespace P2F
namespace PrimeAuxSet
namespace Degree

private scoped instance neZero_of_fact_prime {p : ℕ} [hp : Fact p.Prime] : NeZero p := ⟨hp.out.ne_zero⟩

variable {k : Type*} [Field k] [NumberField k] {E : Type*} [Field E] [NumberField E] [Algebra k E]
variable {p : ℕ} [hp : Fact p.Prime] {t : ℕ} (u : Fin t → kˣ) {ζ : k} (hζ : IsPrimitiveRoot ζ p)

private def zetaInt : 𝓞 k := ⟨ζ, hζ.isIntegral hp.out.pos⟩

omit [NumberField k] in
private theorem algebraMap_zetaInt : algebraMap (𝓞 k) k (zetaInt hζ) = ζ := rfl

omit [NumberField k] in
private theorem zetaInt_isPrimitiveRoot : IsPrimitiveRoot (zetaInt hζ) p :=
  IsPrimitiveRoot.of_map_of_injective
    (show IsPrimitiveRoot (algebraMap (𝓞 k) k (zetaInt hζ)) p by rw [algebraMap_zetaInt]; exact hζ)
    (FaithfulSMul.algebraMap_injective (𝓞 k) k)

variable (E) in
omit [NumberField k] [NumberField E] in

private theorem algebraMap_algebraMap (y : 𝓞 k) :
    algebraMap (𝓞 E) E (algebraMap (𝓞 k) (𝓞 E) y) = algebraMap k E (algebraMap (𝓞 k) k y) :=
  (IsScalarTower.algebraMap_apply (𝓞 k) (𝓞 E) E y).symm.trans (IsScalarTower.algebraMap_apply (𝓞 k) k E y)

variable (E) in

private def zetaIntE : 𝓞 E := algebraMap (𝓞 k) (𝓞 E) (zetaInt hζ)

variable (E) in
omit [NumberField k] [NumberField E] in
private theorem algebraMap_zetaIntE : algebraMap (𝓞 E) E (zetaIntE E hζ) = algebraMap k E ζ := by
  unfold zetaIntE
  rw [algebraMap_algebraMap, algebraMap_zetaInt]

variable (E) in
omit [NumberField k] [NumberField E] in
private theorem zetaIntE_isPrimitiveRoot : IsPrimitiveRoot (zetaIntE E hζ) p :=
  IsPrimitiveRoot.of_map_of_injective
    (show IsPrimitiveRoot (algebraMap (𝓞 E) E (zetaIntE E hζ)) p by
      rw [algebraMap_zetaIntE]; exact zetaE_isPrimitiveRoot E p hζ)
    (FaithfulSMul.algebraMap_injective (𝓞 E) E)

section Transport

variable {v : HeightOneSpectrum (𝓞 k)} {w : HeightOneSpectrum (𝓞 E)} (hwv : w.asIdeal.under (𝓞 k) = v.asIdeal)
include hwv

omit [NumberField k] [NumberField E] in
private theorem notMem_of_notMem_under {n : 𝓞 k} (hn : n ∉ v.asIdeal) : algebraMap (𝓞 k) (𝓞 E) n ∉ w.asIdeal := by
  rwa [← Ideal.mem_comap, ← Ideal.under_def, hwv]

omit [NumberField k] [NumberField E] in
private theorem natCast_notMem_of_notMem (m : ℕ) (hm : (m : 𝓞 k) ∉ v.asIdeal) : (m : 𝓞 E) ∉ w.asIdeal := by
  have h := notMem_of_notMem_under hwv hm
  rwa [map_natCast] at h

omit [NumberField k] in

private theorem valuation_algebraMap_eq_one {x : k} {n d : 𝓞 k} (hn : n ∉ v.asIdeal) (hd : d ∉ v.asIdeal)
    (hnd : x * algebraMap (𝓞 k) k d = algebraMap (𝓞 k) k n) :
    w.valuation E (algebraMap k E x) = 1 ∧
      algebraMap k E x * algebraMap (𝓞 E) E (algebraMap (𝓞 k) (𝓞 E) d)
        = algebraMap (𝓞 E) E (algebraMap (𝓞 k) (𝓞 E) n) := by
  have hndE : algebraMap k E x * algebraMap (𝓞 E) E (algebraMap (𝓞 k) (𝓞 E) d)
      = algebraMap (𝓞 E) E (algebraMap (𝓞 k) (𝓞 E) n) := by
    rw [algebraMap_algebraMap, algebraMap_algebraMap, ← map_mul, hnd]
  refine ⟨?_, hndE⟩
  have hvn : w.valuation E (algebraMap (𝓞 E) E (algebraMap (𝓞 k) (𝓞 E) n)) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact (w.intValuation_eq_one_iff).mpr (notMem_of_notMem_under hwv hn)
  have hvd : w.valuation E (algebraMap (𝓞 E) E (algebraMap (𝓞 k) (𝓞 E) d)) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact (w.intValuation_eq_one_iff).mpr (notMem_of_notMem_under hwv hd)
  have h := congrArg (w.valuation E) hndE
  rwa [Valuation.map_mul, hvd, mul_one, hvn] at h

end Transport
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Residue P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.AuxField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Local P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.LocalSurj"

section FrobeniusValue

variable [IsGalois E (KummerField E p u)]
variable (v : HeightOneSpectrum (𝓞 k)) (w : HeightOneSpectrum (𝓞 E)) (hwv : w.asIdeal.under (𝓞 k) = v.asIdeal)
variable (hvp : (p : 𝓞 k) ∉ v.asIdeal)

include hwv hvp in
omit [NumberField k] in

private theorem residue_pow_eq (j : Fin t) {n d : 𝓞 k} (hn : n ∉ v.asIdeal) (hd : d ∉ v.asIdeal)
    (hnd : (u j : k) * algebraMap (𝓞 k) k d = algebraMap (𝓞 k) k n) :
    (Ideal.Quotient.mk w.asIdeal (algebraMap (𝓞 k) (𝓞 E) (n * d ^ (p - 1))))
        ^ ((Nat.card (𝓞 E ⧸ w.asIdeal) - 1) / p)
      = (Ideal.Quotient.mk w.asIdeal (zetaIntE E hζ))
        ^ (lamAux E p u hζ (artinFrob E (KummerField E p u) w) j).val := by
  have hx : algebraMap (𝓞 k) (𝓞 E) (n * d ^ (p - 1)) ∉ w.asIdeal :=
    notMem_of_notMem_under hwv (mul_pow_notMem v hn hd _)
  have hpw : (p : 𝓞 E) ∉ w.asIdeal := natCast_notMem_of_notMem hwv p hvp
  set r : KummerField E p u :=
    rad E p u j * algebraMap E (KummerField E p u) (algebraMap k E (algebraMap (𝓞 k) k d)) with hr_def
  have hr : r ^ p = algebraMap E (KummerField E p u)
      ((algebraMap (𝓞 k) (𝓞 E) (n * d ^ (p - 1)) : 𝓞 E) : E) := by
    rw [hr_def, mul_pow, rad_pow, ← map_pow, ← map_mul, ← map_pow, ← map_mul, mul_pow_eq' (u j : k) hnd]
    rw [← algebraMap_algebraMap E (n * d ^ (p - 1))]
  have hσ : artinFrob E (KummerField E p u) w r
      = algebraMap E (KummerField E p u) ((zetaIntE E hζ : 𝓞 E) : E)
          ^ (lamAux E p u hζ (artinFrob E (KummerField E p u) w) j).val * r := by
    have hz : ((zetaIntE E hζ : 𝓞 E) : E) = algebraMap k E ζ := algebraMap_zetaIntE E hζ
    rw [hz, hr_def, map_mul, lamAux_spec, AlgEquiv.commutes, mul_assoc]
  exact Residue.pow_residue_eq_of_artinFrob_eq E (KummerField E p u) (zetaIntE_isPrimitiveRoot E hζ) w hpw hx hr _ hσ

end FrobeniusValue
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Residue P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.AuxField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Local P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.LocalSurj"

section SymbolRow

variable [IsGalois k E] [IsGalois E (KummerField E p u)] (hdeg : Module.finrank k E = p)
variable (v : HeightOneSpectrum (𝓞 k)) (w : HeightOneSpectrum (𝓞 E)) (hwv : w.asIdeal.under (𝓞 k) = v.asIdeal)
variable (hvp : (p : 𝓞 k) ∉ v.asIdeal) (hunit : ∀ j, v.valuation k (u j : k) = 1)
variable (hne : lamAux E p u hζ (artinFrob E (KummerField E p u) w) ≠ 0)

include hdeg hwv hvp hunit hne in

private theorem inertiaDeg_eq_one : v.asIdeal.inertiaDeg' w.asIdeal = 1 := by
  rcases Residue.inertiaDeg_eq_one_or_eq k E v w hwv hdeg with h1 | hf
  · exact h1
  exfalso
  apply hne
  funext j
  obtain ⟨n, d, hn, hd, hnd⟩ := exists_num_den_notMem v (hunit j)
  have key := residue_pow_eq u hζ v w hwv hvp j hn hd hnd
  have hone := Residue.pow_resMap_eq_one_of_dvd_inertiaDeg k E v w hwv hvp (zetaInt_isPrimitiveRoot hζ)
    (dvd_of_eq hf.symm) (Ideal.Quotient.mk v.asIdeal (n * d ^ (p - 1)))
    (mk_ne_zero_of_notMem v (mul_pow_notMem v hn hd _))
  rw [M4aKummer.resMap_mk] at hone
  rw [hone] at key
  have hζw := Residue.residue_isPrimitiveRoot w (natCast_notMem_of_notMem hwv p hvp) (zetaIntE_isPrimitiveRoot E hζ)
  have hdvd : p ∣ (lamAux E p u hζ (artinFrob E (KummerField E p u) w) j).val := (hζw.pow_eq_one_iff_dvd _).mp key.symm
  exact (ZMod.val_eq_zero _).mp (Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt _))

include hdeg hwv hvp hunit hne in

private theorem symbol_row (j : Fin t) {n d : 𝓞 k} (hn : n ∉ v.asIdeal) (hd : d ∉ v.asIdeal)
    (hnd : (u j : k) * algebraMap (𝓞 k) k d = algebraMap (𝓞 k) k n) :
    (Ideal.Quotient.mk v.asIdeal (n * d ^ (p - 1))) ^ ((Nat.card (𝓞 k ⧸ v.asIdeal) - 1) / p)
      = (Ideal.Quotient.mk v.asIdeal (zetaInt hζ))
        ^ (lamAux E p u hζ (artinFrob E (KummerField E p u) w) j).val := by
  have hf1 := inertiaDeg_eq_one u hζ hdeg v w hwv hvp hunit hne
  have key := residue_pow_eq u hζ v w hwv hvp j hn hd hnd
  rw [Residue.natCard_residue_eq_of_inertiaDeg_one k E v w hwv hf1] at key
  apply Residue.resMap_injective k E v w hwv
  rw [map_pow, map_pow, M4aKummer.resMap_mk, M4aKummer.resMap_mk]
  exact key

end SymbolRow
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Residue P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.AuxField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Local P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.LocalSurj"

section LocalDegree

variable [IsGalois k E] [IsGalois E (KummerField E p u)] (hdeg : Module.finrank k E = p)
variable (w : HeightOneSpectrum (𝓞 E))
variable (hvp : (p : 𝓞 k) ∉ (w.under (𝓞 k)).asIdeal) (hunit : ∀ j, (w.under (𝓞 k)).valuation k (u j : k) = 1)
variable (hne : lamAux E p u hζ (artinFrob E (KummerField E p u) w) ≠ 0)

include hdeg hvp hunit hne in

private theorem exists_extension_finrank_eq_one (α : E) (a : kˣ) (hα : α ^ p = algebraMap k E (a : k))
    (hgen : ∀ σ : E ≃ₐ[k] E, σ α = α → σ = 1) (ha : (w.under (𝓞 k)).valuation k (a : k) = 1) :
    ∃ w' : (w.under (𝓞 k)).Extension (𝓞 E),
      Module.finrank ((w.under (𝓞 k)).adicCompletion k) (w'.1.adicCompletion E) = 1 := by
  have hwv : w.asIdeal.under (𝓞 k) = (w.under (𝓞 k)).asIdeal := rfl
  have hf1 := inertiaDeg_eq_one u hζ hdeg (w.under (𝓞 k)) w hwv hvp hunit hne
  obtain ⟨n, d, hn, hd, hnd⟩ := exists_num_den_notMem (w.under (𝓞 k)) ha
  have hx0 : n * d ^ (p - 1) ∉ (w.under (𝓞 k)).asIdeal := mul_pow_notMem (w.under (𝓞 k)) hn hd _

  set β : E := α * algebraMap k E (algebraMap (𝓞 k) k d) with hβ_def
  have hβ : β ^ p = algebraMap k E (algebraMap (𝓞 k) k (n * d ^ (p - 1))) := by
    rw [hβ_def, mul_pow, hα, ← map_pow, ← map_mul, mul_pow_eq' (a : k) hnd]
  let B : 𝓞 E := ⟨β, Residue.isIntegral_root k E (x := n * d ^ (p - 1)) hβ⟩
  have hBp : B ^ p = algebraMap (𝓞 k) (𝓞 E) (n * d ^ (p - 1)) := by
    apply RingOfIntegers.ext
    show β ^ p = _
    rw [hβ]
    rw [← algebraMap_algebraMap E (n * d ^ (p - 1))]

  have hBw : (Ideal.Quotient.mk w.asIdeal B) ^ p
      = M4aKummer.resMap k E (w.under (𝓞 k)) w hwv (Ideal.Quotient.mk (w.under (𝓞 k)).asIdeal (n * d ^ (p - 1))) := by
    rw [M4aKummer.resMap_mk, ← map_pow, hBp]
  haveI : Finite (𝓞 E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  have hbij : Function.Bijective (M4aKummer.resMap k E (w.under (𝓞 k)) w hwv) :=
    (Residue.resMap_injective k E (w.under (𝓞 k)) w hwv).bijective_of_nat_card_le
      (Residue.natCard_residue_eq_of_inertiaDeg_one k E (w.under (𝓞 k)) w hwv hf1).le
  obtain ⟨zq, hzq⟩ := hbij.2 (Ideal.Quotient.mk w.asIdeal B)
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective zq
  have hzp : (Ideal.Quotient.mk (w.under (𝓞 k)).asIdeal z) ^ p
      = Ideal.Quotient.mk (w.under (𝓞 k)).asIdeal (n * d ^ (p - 1)) := by
    apply hbij.1
    rw [map_pow, hzq, hBw]

  have hres : IsLocalRing.residue ((w.under (𝓞 k)).adicCompletionIntegers k)
      ((toUnit (w.under (𝓞 k)) (intUnit (w.under (𝓞 k)) hx0) (valued_intUnit (w.under (𝓞 k)) hx0)
          : ((w.under (𝓞 k)).adicCompletionIntegers k)ˣ) : (w.under (𝓞 k)).adicCompletionIntegers k)
        = (resHom (w.under (𝓞 k)) z) ^ p := by
    rw [residue_toUnit_intUnit, ← resQuotHom_mk, ← resQuotHom_mk, ← map_pow, hzp]
  obtain ⟨c, hc⟩ := exists_eq_pow_of_residue (w.under (𝓞 k)) hvp (intUnit (w.under (𝓞 k)) hx0)
    (valued_intUnit (w.under (𝓞 k)) hx0) hres
  have hd0 : algebraMap k ((w.under (𝓞 k)).adicCompletion k) (algebraMap (𝓞 k) k d) ≠ 0 :=
    (_root_.map_ne_zero _).mpr (algebraMap_ne_zero_of_notMem (w.under (𝓞 k)) hd)
  have hb : ∃ b : (w.under (𝓞 k)).adicCompletion k,
      algebraMap k ((w.under (𝓞 k)).adicCompletion k) (a : k) = b ^ p := by
    refine ⟨(c : (w.under (𝓞 k)).adicCompletion k) / algebraMap k ((w.under (𝓞 k)).adicCompletion k) (algebraMap (𝓞 k) k d), ?_⟩
    rw [div_pow, eq_div_iff (pow_ne_zero _ hd0), ← map_pow, ← map_mul, mul_pow_eq' (a : k) hnd,
      ← algebraMap_int_eq (w.under (𝓞 k)), ← intUnit_coe (w.under (𝓞 k)) hx0, hc, Units.val_pow_eq_pow_val]
  have hμ : (primitiveRoots p k).Nonempty := ⟨ζ, (mem_primitiveRoots hp.out.pos).mpr hζ⟩
  exact ⟨⟨w, rfl⟩, IsDedekindDomain.HeightOneSpectrum.Extension.finrank_adicCompletion_eq_one_of_pow_eq k E hμ (a : k) α hα
    hgen (w.under (𝓞 k)) hb ⟨w, rfl⟩⟩

end LocalDegree
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Residue P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.AuxField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Local P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.LocalSurj"

end P2F.PrimeAuxSet.Degree
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Residue P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.AuxField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Local P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.LocalSurj P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Degree"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Residue P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.AuxField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Local P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.LocalSurj"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Residue P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.AuxField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Local P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.LocalSurj"

end
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Residue P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.AuxField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Local P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.LocalSurj P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Degree"

set_option autoImplicit false

p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum"
open P2F.PrimeAuxSet

noncomputable section

namespace P2F
namespace PrimeAuxSet
namespace Assembly

universe u v

private theorem exists_auxSet
    (k : Type u) (E : Type v) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]
    (p : ℕ) (hp : p.Prime) (hμ : (primitiveRoots p k).Nonempty) (hdeg : Module.finrank k E = p)
    [IsGalois k E]
    (hFI : ∀ (M : Type v) [Field M] [NumberField M] [Algebra E M] [IsGalois E M], Module.finrank E M = p →
      ∀ 𝔣₀ : Ideal (NumberField.RingOfIntegers E), NumberField.PrimeNormIndex.IsAdmissibleModulusAt E M p 𝔣₀ →
        LanglandsTunnell.P2.Artin.IdeleFirstIneqDataAt E M 𝔣₀) :
    ∀ (α : E) (a : kˣ), α ^ p = algebraMap k E (a : k) → (∀ σ : E ≃ₐ[k] E, σ α = α → σ = 1) →
      ∀ S : Finset (HeightOneSpectrum (𝓞 k)),
        (∀ v : HeightOneSpectrum (𝓞 k), (p : 𝓞 k) ∈ v.asIdeal → v ∈ S) →
        (∀ v : HeightOneSpectrum (𝓞 k), v.valuation k (a : k) ≠ 1 → v ∈ S) →
        M4aHerbrand.principalIdeles (𝓞 k) k ⊔ NumberField.AdeleRing.unitIdelesOutside (𝓞 k) k ↑S = ⊤ →
        ∃ T : Finset (HeightOneSpectrum (𝓞 k)), P2F.CubicCapstone.auxSetSpec k E p S T := by
  intro α a hα hgen S hSp hSa _hScl
  classical
  haveI hpf : Fact p.Prime := ⟨hp⟩
  obtain ⟨ζ, hζmem⟩ := id hμ
  have hζ : IsPrimitiveRoot ζ p := (mem_primitiveRoots hp.pos).mp hζmem

  obtain ⟨t, u, huS, hcard, hindep⟩ := P2F.CubicCapstone.exists_radicand_basis_of_kummer hp hμ hdeg α a hα hgen S hSa
  have hu : ∀ j, ∀ v : HeightOneSpectrum (𝓞 k), v ∉ S → v.valuation k (u j : k) = 1 := fun j v hv =>
    (P2F.CubicCapstone.mem_sUnit_iff _ _).mp (huS j) v (fun h => hv (Finset.mem_coe.mp h))

  obtain ⟨M₁, hM₁⟩ := Ideal.exists_maximal (𝓞 E)
  let w₁ : HeightOneSpectrum (𝓞 E) :=
    ⟨M₁, hM₁.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM₁ (RingOfIntegers.not_isField E)⟩
  set 𝔞 : Ideal (𝓞 E) := (∏ v ∈ S, (v.asIdeal).map (algebraMap (𝓞 k) (𝓞 E))) * w₁.asIdeal with h𝔞_def
  have hdvd_of_mem : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 k) ∈ S → w.asIdeal ∣ 𝔞 := fun w hw => by
    rw [h𝔞_def]
    refine dvd_mul_of_dvd_left (dvd_trans ?_ (Finset.dvd_prod_of_mem _ hw)) _
    show w.asIdeal ∣ ((w.under (𝓞 k)).asIdeal).map (algebraMap (𝓞 k) (𝓞 E))
    rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap]
    exact le_rfl
  have hunder_p : ∀ w : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ w.asIdeal → (p : 𝓞 k) ∈ (w.under (𝓞 k)).asIdeal :=
    fun w hw => by
      show (p : 𝓞 k) ∈ w.asIdeal.under (𝓞 k)
      rw [Ideal.under_def, Ideal.mem_comap, map_natCast]
      exact hw
  have h𝔞p : ∀ w : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ w.asIdeal → w.asIdeal ∣ 𝔞 := fun w hw =>
    hdvd_of_mem w (hSp _ (hunder_p w hw))
  have hnotMem_of_notDvd : ∀ w : HeightOneSpectrum (𝓞 E), ¬ w.asIdeal ∣ 𝔞 → w.under (𝓞 k) ∉ S :=
    fun w hw hmem => hw (hdvd_of_mem w hmem)
  have h𝔞u : ∀ w : HeightOneSpectrum (𝓞 E), ¬ w.asIdeal ∣ 𝔞 → ∀ j, w.valuation E (algebraMap k E (u j : k)) = 1 :=
    fun w hw j => by
      obtain ⟨n, d, hn, hd, hnd⟩ := LocalSurj.exists_num_den_notMem (w.under (𝓞 k)) (hu j _ (hnotMem_of_notDvd w hw))
      exact (Degree.valuation_algebraMap_eq_one (v := w.under (𝓞 k)) (w := w) rfl hn hd hnd).1
  have hinj_int : Function.Injective (algebraMap (𝓞 k) (𝓞 E)) := by
    intro x y hxy
    apply FaithfulSMul.algebraMap_injective (𝓞 k) k
    apply (algebraMap k E).injective
    have h := congrArg (algebraMap (𝓞 E) E) hxy
    rwa [Degree.algebraMap_algebraMap, Degree.algebraMap_algebraMap] at h
  have h𝔞 : 𝔞 ≠ ⊥ := by
    rw [h𝔞_def]
    intro hbot
    rcases Ideal.mul_eq_bot.mp hbot with hprod | hw₁
    · obtain ⟨v₀, -, hv₀⟩ := Finset.prod_eq_zero_iff.mp (hprod.trans (show (⊥ : Ideal (𝓞 E)) = 0 from rfl))
      exact v₀.ne_bot ((Ideal.map_eq_bot_iff_of_injective hinj_int).mp hv₀)
    · exact w₁.ne_bot hw₁

  haveI hGal : IsGalois E (AuxField.KummerField E p u) := AuxField.isGalois_aux E p u hζ
  haveI hComm : IsMulCommutative (AuxField.KummerField E p u ≃ₐ[E] AuxField.KummerField E p u) :=
    OntoDock.isMulCommutative_aut E p u hζ
  have honto := OntoDock.artinSymbol_surjective p u hζ h𝔞p h𝔞u h𝔞 hFI
  have hind : ∀ (e : Fin t → ℕ) (g : E), g ^ p = ∏ j, AuxField.radVal E u j ^ e j → ∀ j, p ∣ e j := by
    intro e g hg
    have hc : (∏ j, (u j : k) ^ e j) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => pow_ne_zero _ (u j).ne_zero
    have hg' : g ^ p = algebraMap k E (∏ j, (u j : k) ^ e j) := by
      rw [hg, map_prod]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [map_pow]
      rfl
    obtain ⟨m, dd, hmd⟩ := Descent.exists_pow_mul_eq_pow hdeg hζ a.ne_zero hα hgen hc hg'
    have hdd : dd ≠ 0 := by
      intro h0
      rw [h0, zero_pow hp.ne_zero] at hmd
      exact mul_ne_zero (pow_ne_zero _ a.ne_zero) hc hmd
    exact fun j => (hindep m e (Units.mk0 dd hdd) (by
      ext
      simpa [Units.coe_prod, Units.val_pow_eq_pow_val] using hmd)).1 j
  have hlam : Function.Surjective (AuxField.lamAux E p u hζ) := Seam.lamAux_surjective E p u hζ hind

  obtain ⟨wv, hli⟩ := OntoDock.exists_frobenius_basis p u hζ honto hlam
  have hN : OntoDock.N p 𝔞 ≠ 0 := by
    have h1 : OntoDock.expOf p w₁.asIdeal ≤ OntoDock.N p 𝔞 :=
      OntoDock.expOf_le_N p h𝔞 (by rw [h𝔞_def]; exact dvd_mul_left _ _)
    have h2 : 1 ≤ OntoDock.expOf p w₁.asIdeal := by
      unfold OntoDock.expOf
      omega
    omega
  have hnotDvd : ∀ i, ¬ (wv i).1.asIdeal ∣ 𝔞 := fun i h => (wv i).2 (by
    show (wv i).1.asIdeal ∣ 𝔞 ^ OntoDock.N p 𝔞
    exact h.trans (dvd_pow_self 𝔞 hN))
  have hvS : ∀ i, (wv i).1.under (𝓞 k) ∉ S := fun i => hnotMem_of_notDvd _ (hnotDvd i)
  have hvp : ∀ i, (p : 𝓞 k) ∉ ((wv i).1.under (𝓞 k)).asIdeal := fun i hmem => hvS i (hSp _ hmem)
  have hunit : ∀ i j, ((wv i).1.under (𝓞 k)).valuation k (u j : k) = 1 := fun i j => hu j _ (hvS i)
  have ha_unit : ∀ i, ((wv i).1.under (𝓞 k)).valuation k (a : k) = 1 := fun i => by
    by_contra h
    exact hvS i (hSa _ h)

  have hsym : ∀ (i j : Fin t) (n d : 𝓞 k), n ∉ ((wv i).1.under (𝓞 k)).asIdeal → d ∉ ((wv i).1.under (𝓞 k)).asIdeal →
      (u j : k) * algebraMap (𝓞 k) k d = algebraMap (𝓞 k) k n →
      (Ideal.Quotient.mk ((wv i).1.under (𝓞 k)).asIdeal (n * d ^ (p - 1)))
          ^ ((Nat.card (𝓞 k ⧸ ((wv i).1.under (𝓞 k)).asIdeal) - 1) / p)
        = (Ideal.Quotient.mk ((wv i).1.under (𝓞 k)).asIdeal (Degree.zetaInt hζ))
          ^ ((fun i => AuxField.lamAux E p u hζ
              (LanglandsTunnell.P2.Artin.artinFrob E (AuxField.KummerField E p u) (wv i).1)) i j).val :=
    fun i j n d hn hd hnd =>
      Degree.symbol_row u hζ hdeg ((wv i).1.under (𝓞 k)) (wv i).1 rfl (hvp i) (hunit i) (hli.ne_zero i) j hn hd hnd
  have hinj : Function.Injective (fun i => (wv i).1.under (𝓞 k)) :=
    LocalSurj.vv_injective (Degree.zetaInt_isPrimitiveRoot hζ) u S hu (fun i => (wv i).1.under (𝓞 k)) hvS hvp
      (fun i => AuxField.lamAux E p u hζ (LanglandsTunnell.P2.Artin.artinFrob E (AuxField.KummerField E p u) (wv i).1))
      hsym hli
  refine ⟨Finset.univ.image (fun i => (wv i).1.under (𝓞 k)), ?_⟩
  unfold P2F.CubicCapstone.auxSetSpec
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hv
    exact hvS i
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    omega
  · intro v hv
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hv
    exact Degree.exists_extension_finrank_eq_one u hζ hdeg (wv i).1 (hvp i) (hunit i) (hli.ne_zero i) α a hα hgen
      (ha_unit i)
  · intro x hx
    obtain ⟨s, hsS, hs⟩ := LocalSurj.exists_sUnit_forall_mul_inv_eq_pow (Degree.zetaInt_isPrimitiveRoot hζ) u S hu
      (fun i => (wv i).1.under (𝓞 k)) hvS hvp
      (fun i => AuxField.lamAux E p u hζ (LanglandsTunnell.P2.Artin.artinFrob E (AuxField.KummerField E p u) (wv i).1))
      hsym hli x
      (fun i => hx _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)) (hvS i))
    refine ⟨s, hsS, ?_⟩
    intro v hv _
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hv
    exact hs i

end P2F.PrimeAuxSet.Assembly
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Residue P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.AuxField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Local P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.LocalSurj P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Degree"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Residue P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.AuxField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Local P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.LocalSurj P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Degree"
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Residue P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.AuxField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Local P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.LocalSurj P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Degree"

end
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Residue P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.AuxField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Local P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.LocalSurj P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Degree"

end Fold_P2F_PrimeAuxSet
p2m_reactivate "P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.LanglandsTunnell.P2.Artin P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.M4aP2 P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.SignSpace P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Residue P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.AuxField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Local P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.LocalSurj P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.PrimeAuxSet.Degree"

set_option autoImplicit false

universe u v

p2m_open "NumberField P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.NumberField IsDedekindDomain P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots.P2F.CubicCapstone"

private theorem r1_hchoice
    (k : Type u) (E : Type v) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]
    (p : ℕ) (hp : p.Prime) (hμ : (primitiveRoots p k).Nonempty) (hdeg : Module.finrank k E = p)
    [IsGalois k E]
    (hFI : ∀ (M : Type v) [Field M] [NumberField M] [Algebra E M] [IsGalois E M], Module.finrank E M = p →
      ∀ 𝔣₀ : Ideal (NumberField.RingOfIntegers E), NumberField.PrimeNormIndex.IsAdmissibleModulusAt E M p 𝔣₀ →
        LanglandsTunnell.P2.Artin.IdeleFirstIneqDataAt E M 𝔣₀) :
    ∀ (α : E) (a : kˣ), α ^ p = algebraMap k E (a : k) → (∀ σ : E ≃ₐ[k] E, σ α = α → σ = 1) →
      ∀ S : Finset (HeightOneSpectrum (𝓞 k)),
        (∀ v : HeightOneSpectrum (𝓞 k), (p : 𝓞 k) ∈ v.asIdeal → v ∈ S) →
        (∀ v : HeightOneSpectrum (𝓞 k), v.valuation k (a : k) ≠ 1 → v ∈ S) →
        M4aHerbrand.principalIdeles (𝓞 k) k ⊔ NumberField.AdeleRing.unitIdelesOutside (𝓞 k) k ↑S = ⊤ →
        ∃ T : Finset (HeightOneSpectrum (𝓞 k)), auxSetSpec k E p S T := by
  exact P2F.PrimeAuxSet.Assembly.exists_auxSet k E p hp hμ hdeg hFI

theorem solution
    (k : Type u) (E : Type v) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]
    (p : ℕ) (hp : p.Prime) (hμ : (primitiveRoots p k).Nonempty) (hdeg : Module.finrank k E = p)
    [IsGalois k E]
    (hFI : ∀ (M : Type v) [Field M] [NumberField M] [Algebra E M] [IsGalois E M], Module.finrank E M = p →
      ∀ 𝔣₀ : Ideal (NumberField.RingOfIntegers E), NumberField.PrimeNormIndex.IsAdmissibleModulusAt E M p 𝔣₀ →
        LanglandsTunnell.P2.Artin.IdeleFirstIneqDataAt E M 𝔣₀)
    (𝔣 : Ideal (NumberField.RingOfIntegers k)) :
    LanglandsTunnell.P2.Artin.SecondInequalityCTM k E 𝔣 :=
  P2F.CubicAdapter.secondInequalityCTM_of_idelicNorm_index_dvd k E p hdeg 𝔣
    (P2F.CubicCapstone.capstone_genuine_of_choice hp hμ hdeg (r1_hchoice k E p hp hμ hdeg hFI))

end S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots
end P2MW
export P2MW.S_NumberField_PrimeNormIndex_secondInequalityCTM_of_primitiveRoots (solution)
