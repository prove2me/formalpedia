-- Prove2me | solution 1 for NumberField.AdeleRing.exists_isAddHaarMeasure_map_pi_fst_snd_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/c2b1c928-6f48-5695-9631-dcf369b0928e

import Mathlib
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdeleRing_exists_isAddHaarMeasure_map_pi_fst_snd_eq_prod
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

namespace E8A
namespace HS

theorem sct_infinite (K : Type) [Field K] [NumberField K] :
    SecondCountableTopology (InfiniteAdeleRing K) := by
  haveI : SecondCountableTopology (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology K
  have h : Topology.IsEmbedding
      (fun x : InfiniteAdeleRing K => ((x, (0 : FiniteAdeleRing (𝓞 K) K)) : AdeleRing (𝓞 K) K)) :=
    isEmbedding_prodMkLeft (0 : FiniteAdeleRing (𝓞 K) K)
  exact h.secondCountableTopology

theorem sct_finite (K : Type) [Field K] [NumberField K] :
    SecondCountableTopology (FiniteAdeleRing (𝓞 K) K) := by
  haveI : SecondCountableTopology (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology K
  have h : Topology.IsEmbedding
      (fun y : FiniteAdeleRing (𝓞 K) K => (((0 : InfiniteAdeleRing K), y) : AdeleRing (𝓞 K) K)) :=
    isEmbedding_prodMkRight (0 : InfiniteAdeleRing K)
  exact h.secondCountableTopology

def theta (K : Type) [Field K] [NumberField K] (ι : Type) :
    (ι → AdeleRing (𝓞 K) K) ≃+ ((ι → InfiniteAdeleRing K) × (ι → FiniteAdeleRing (𝓞 K) K)) where
  toFun a := ((fun k => (a k).1), (fun k => (a k).2))
  invFun p := fun k => ((p.1 k, p.2 k) : AdeleRing (𝓞 K) K)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

theorem continuous_theta (K : Type) [Field K] [NumberField K] (ι : Type) :
    Continuous (theta K ι) := by
  show Continuous (fun a : ι → AdeleRing (𝓞 K) K => ((fun k => (a k).1), (fun k => (a k).2)))
  refine Continuous.prodMk ?_ ?_
  · exact continuous_pi fun k =>
      (continuous_fst (X := InfiniteAdeleRing K) (Y := FiniteAdeleRing (𝓞 K) K)).comp
        (continuous_apply k)
  · exact continuous_pi fun k =>
      (continuous_snd (X := InfiniteAdeleRing K) (Y := FiniteAdeleRing (𝓞 K) K)).comp
        (continuous_apply k)

theorem continuous_theta_symm (K : Type) [Field K] [NumberField K] (ι : Type) :
    Continuous (theta K ι).symm := by
  show Continuous (fun p : (ι → InfiniteAdeleRing K) × (ι → FiniteAdeleRing (𝓞 K) K) =>
      fun k => ((p.1 k, p.2 k) : AdeleRing (𝓞 K) K))
  have h1 : ∀ k : ι,
      Continuous (fun p : (ι → InfiniteAdeleRing K) × (ι → FiniteAdeleRing (𝓞 K) K) => p.1 k) :=
    fun k => (continuous_apply k).comp continuous_fst
  have h2 : ∀ k : ι,
      Continuous (fun p : (ι → InfiniteAdeleRing K) × (ι → FiniteAdeleRing (𝓞 K) K) => p.2 k) :=
    fun k => (continuous_apply k).comp continuous_snd
  exact continuous_pi fun k => (h1 k).prodMk (h2 k)

end E8A.HS

theorem solution
    (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι]
    [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
    [MeasurableSpace (InfiniteAdeleRing K)] [BorelSpace (InfiniteAdeleRing K)]
    [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
    (ρ : Measure (ι → AdeleRing (𝓞 K) K)) [ρ.IsAddHaarMeasure]
    (ν : Measure (ι → InfiniteAdeleRing K)) [ν.IsAddHaarMeasure] :
    SecondCountableTopology (InfiniteAdeleRing K) ∧ SecondCountableTopology (FiniteAdeleRing (𝓞 K) K) ∧
    Measurable (fun a : ι → AdeleRing (𝓞 K) K => ((fun k => (a k).1), (fun k => (a k).2))) ∧
    Measurable (β := ι → AdeleRing (𝓞 K) K)
      (fun p : (ι → InfiniteAdeleRing K) × (ι → FiniteAdeleRing (𝓞 K) K) => fun k => (p.1 k, p.2 k)) ∧
    ∃ ν' : Measure (ι → FiniteAdeleRing (𝓞 K) K), ν'.IsAddHaarMeasure ∧
      Measure.map (fun a : ι → AdeleRing (𝓞 K) K => ((fun k => (a k).1), (fun k => (a k).2))) ρ =
        ν.prod ν' := by
  classical
  haveI hA : SecondCountableTopology (AdeleRing (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology K
  haveI hI : SecondCountableTopology (InfiniteAdeleRing K) := E8A.HS.sct_infinite K
  haveI hF : SecondCountableTopology (FiniteAdeleRing (𝓞 K) K) := E8A.HS.sct_finite K
  haveI : BorelSpace (ι → AdeleRing (𝓞 K) K) := Pi.borelSpace
  haveI : BorelSpace (ι → InfiniteAdeleRing K) := Pi.borelSpace
  haveI : BorelSpace (ι → FiniteAdeleRing (𝓞 K) K) := Pi.borelSpace
  haveI : BorelSpace ((ι → InfiniteAdeleRing K) × (ι → FiniteAdeleRing (𝓞 K) K)) := Prod.borelSpace
  have hc : Continuous (E8A.HS.theta K ι) := E8A.HS.continuous_theta K ι
  have hcs : Continuous (E8A.HS.theta K ι).symm := E8A.HS.continuous_theta_symm K ι
  have hmeas : Measurable (fun a : ι → AdeleRing (𝓞 K) K => ((fun k => (a k).1), (fun k => (a k).2))) :=
    hc.measurable
  have hmeas' : Measurable (β := ι → AdeleRing (𝓞 K) K)
      (fun p : (ι → InfiniteAdeleRing K) × (ι → FiniteAdeleRing (𝓞 K) K) => fun k => (p.1 k, p.2 k)) :=
    hcs.measurable
  refine ⟨hI, hF, hmeas, hmeas', ?_⟩

  haveI hHaar : (Measure.map (E8A.HS.theta K ι) ρ).IsAddHaarMeasure :=
    AddEquiv.isAddHaarMeasure_map ρ (E8A.HS.theta K ι) hc hcs

  set μf : Measure (ι → FiniteAdeleRing (𝓞 K) K) := Measure.addHaar with hμf
  haveI : μf.IsAddHaarMeasure := by rw [hμf]; infer_instance
  haveI : (ν.prod μf).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure ν μf

  have huniq := Measure.isAddLeftInvariant_eq_smul (Measure.map (E8A.HS.theta K ι) ρ) (ν.prod μf)
  set c := Measure.addHaarScalarFactor (Measure.map (E8A.HS.theta K ι) ρ) (ν.prod μf) with hcdef
  have hcpos : 0 < c :=
    Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (Measure.map (E8A.HS.theta K ι) ρ) (ν.prod μf)
  refine ⟨c • μf, Measure.IsAddHaarMeasure.nnreal_smul μf hcpos.ne', ?_⟩
  have hmap : Measure.map (fun a : ι → AdeleRing (𝓞 K) K => ((fun k => (a k).1), (fun k => (a k).2))) ρ =
      Measure.map (E8A.HS.theta K ι) ρ := rfl
  rw [hmap, huniq, ← Measure.coe_nnreal_smul, ← Measure.coe_nnreal_smul c μf,
    Measure.prod_smul_right]

end S_NumberField_AdeleRing_exists_isAddHaarMeasure_map_pi_fst_snd_eq_prod
end P2MW
export P2MW.S_NumberField_AdeleRing_exists_isAddHaarMeasure_map_pi_fst_snd_eq_prod (solution)
