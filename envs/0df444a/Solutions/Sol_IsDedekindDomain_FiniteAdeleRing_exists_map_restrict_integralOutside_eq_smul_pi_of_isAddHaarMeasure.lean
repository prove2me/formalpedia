-- Prove2me | solution 1 for IsDedekindDomain.FiniteAdeleRing.exists_map_restrict_integralOutside_eq_smul_pi_of_isAddHaarMeasure
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/469cf32d-1405-54d1-bd86-7ee0d16f9308

import Mathlib
import Definitions.Def_NumberField_AdelicBox
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDedekindDomain_FiniteAdeleRing_exists_map_restrict_integralOutside_eq_smul_pi_of_isAddHaarMeasure
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal Classical

namespace E8A
namespace HSP

theorem sct_finite (K : Type) [Field K] [NumberField K] :
    SecondCountableTopology (FiniteAdeleRing (𝓞 K) K) := by
  haveI : SecondCountableTopology (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology K
  have h : Topology.IsEmbedding
      (fun y : FiniteAdeleRing (𝓞 K) K => (((0 : InfiniteAdeleRing K), y) : AdeleRing (𝓞 K) K)) :=
    isEmbedding_prodMkRight (0 : InfiniteAdeleRing K)
  exact h.secondCountableTopology

section Main

variable (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (S : Finset (HeightOneSpectrum (𝓞 K)))

noncomputable def lift (t : ∀ v : ↥S, ι → v.1.adicCompletion K) : ι → FiniteAdeleRing (𝓞 K) K := fun k =>
  ⟨fun v => if h : v ∈ S then t ⟨v, h⟩ k else 0, by
    refine Filter.eventually_cofinite.mpr ((S.finite_toSet).subset fun v hv => ?_)
    by_contra hvS
    apply hv
    dsimp only
    rw [dif_neg (by simpa only [Finset.mem_coe] using hvS)]
    exact zero_mem _⟩

theorem lift_apply_mem (t : ∀ v : ↥S, ι → v.1.adicCompletion K) (k : ι) (v : ↥S) :
    (lift K ι S t k) v.1 = t v k := by
  show (fun w : HeightOneSpectrum (𝓞 K) =>
      (if h : w ∈ S then t ⟨w, h⟩ k else (0 : w.adicCompletion K))) v.1 = t v k
  exact dif_pos v.2

theorem lift_apply_not_mem (t : ∀ v : ↥S, ι → v.1.adicCompletion K) (k : ι)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) : (lift K ι S t k) v = 0 := by
  show (fun w : HeightOneSpectrum (𝓞 K) =>
      (if h : w ∈ S then t ⟨w, h⟩ k else (0 : w.adicCompletion K))) v = 0
  exact dif_neg hv

omit [Fintype ι] in
theorem add_apply' (a b : FiniteAdeleRing (𝓞 K) K) (v : HeightOneSpectrum (𝓞 K)) : (a + b) v = a v + b v := rfl

theorem piS_lift_add (t : ∀ v : ↥S, ι → v.1.adicCompletion K) (y : ι → FiniteAdeleRing (𝓞 K) K) :
    (fun (v : ↥S) (k : ι) => ((lift K ι S t + y) k) v.1) = t + fun (v : ↥S) (k : ι) => (y k) v.1 := by
  funext v k
  simp only [Pi.add_apply, add_apply', lift_apply_mem]

theorem preimage_lift_add (t : ∀ v : ↥S, ι → v.1.adicCompletion K) :
    (fun y => lift K ι S t + y) ⁻¹'
        {y : ι → FiniteAdeleRing (𝓞 K) K | ∀ k, ∀ v ∉ S, (y k) v ∈ v.adicCompletionIntegers K} =
      {y : ι → FiniteAdeleRing (𝓞 K) K | ∀ k, ∀ v ∉ S, (y k) v ∈ v.adicCompletionIntegers K} := by
  ext y
  simp only [Set.mem_preimage, Set.mem_setOf_eq, Pi.add_apply, add_apply']
  refine forall_congr' fun k => forall_congr' fun v => forall_congr' fun hv => ?_
  rw [lift_apply_not_mem K ι S t k v hv, zero_add]

omit [Fintype ι] in
theorem isOpen_integralOutside :
    IsOpen {a : FiniteAdeleRing (𝓞 K) K | ∀ v ∉ S, a v ∈ v.adicCompletionIntegers K} :=
  RestrictedProduct.isOpen_forall_imp_mem
    (R := fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (A := fun v : HeightOneSpectrum (𝓞 K) => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
    Fact.out (p := fun v => v ∉ S)

theorem isOpen_HS :
    IsOpen {y : ι → FiniteAdeleRing (𝓞 K) K | ∀ k, ∀ v ∉ S, (y k) v ∈ v.adicCompletionIntegers K} := by
  have : {y : ι → FiniteAdeleRing (𝓞 K) K | ∀ k, ∀ v ∉ S, (y k) v ∈ v.adicCompletionIntegers K} =
      Set.pi Set.univ (fun _ : ι => {a : FiniteAdeleRing (𝓞 K) K | ∀ v ∉ S, a v ∈ v.adicCompletionIntegers K}) := by
    ext y; simp only [Set.mem_setOf_eq, Set.mem_univ_pi]
  rw [this]
  exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_integralOutside K S

theorem continuous_piS :
    Continuous fun (y : ι → FiniteAdeleRing (𝓞 K) K) (v : ↥S) (k : ι) => (y k) v.1 :=
  continuous_pi fun v => continuous_pi fun k =>
    (RestrictedProduct.continuous_eval v.1).comp (continuous_apply k)

end Main

end E8A.HSP

open E8A.HSP in
theorem solution
    (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι]
    [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
    [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
    [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
    (μ : ∀ v : HeightOneSpectrum (𝓞 K), Measure (ι → v.adicCompletion K))
    [∀ v : HeightOneSpectrum (𝓞 K), (μ v).IsAddHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (ν : Measure (ι → FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      Measure.map (fun (y : ι → FiniteAdeleRing (𝓞 K) K) (v : ↥S) (k : ι) => (y k) v.1)
          (ν.restrict {y : ι → FiniteAdeleRing (𝓞 K) K |
            ∀ k, ∀ v ∉ S, (y k) v ∈ v.adicCompletionIntegers K}) =
        c • Measure.pi fun v : ↥S => μ v.1 := by
  classical

  haveI : SecondCountableTopology (FiniteAdeleRing (𝓞 K) K) := sct_finite K
  haveI : ∀ v : ↥S, SecondCountableTopology (ι → v.1.adicCompletion K) := fun _ => inferInstance
  haveI : ∀ v : ↥S, BorelSpace (ι → v.1.adicCompletion K) := fun _ => inferInstance
  haveI : SecondCountableTopology (∀ v : ↥S, ι → v.1.adicCompletion K) := inferInstance
  haveI : BorelSpace (∀ v : ↥S, ι → v.1.adicCompletion K) := inferInstance
  haveI : ∀ v : ↥S, IsTopologicalAddGroup (ι → v.1.adicCompletion K) := fun _ => inferInstance
  haveI : IsTopologicalAddGroup (∀ v : ↥S, ι → v.1.adicCompletion K) := inferInstance
  haveI : ∀ v : ↥S, LocallyCompactSpace (ι → v.1.adicCompletion K) := fun _ => inferInstance
  haveI : LocallyCompactSpace (∀ v : ↥S, ι → v.1.adicCompletion K) := inferInstance
  haveI : ∀ v : ↥S, SigmaFinite (μ v.1) := fun _ => inferInstance

  set HS : Set (ι → FiniteAdeleRing (𝓞 K) K) :=
    {y | ∀ k, ∀ v ∉ S, (y k) v ∈ v.adicCompletionIntegers K} with hHS
  set piS : (ι → FiniteAdeleRing (𝓞 K) K) → (∀ v : ↥S, ι → v.1.adicCompletion K) :=
    fun y v k => (y k) v.1 with hpiS
  set m : Measure (∀ v : ↥S, ι → v.1.adicCompletion K) := Measure.map piS (ν.restrict HS) with hm
  have hHSo : IsOpen HS := isOpen_HS K ι S
  have hHSm : MeasurableSet HS := hHSo.measurableSet
  have hpiSm : Measurable piS := (continuous_piS K ι S).measurable

  haveI : m.IsAddLeftInvariant := by
    refine ⟨fun t => ?_⟩
    rw [hm, Measure.map_map (measurable_const_add t) hpiSm]
    have hcomp : (fun z => t + z) ∘ piS = piS ∘ fun y => lift K ι S t + y := by
      funext y
      simp only [Function.comp_apply, hpiS]
      exact (piS_lift_add K ι S t y).symm
    rw [hcomp, ← Measure.map_map hpiSm (measurable_const_add _)]
    congr 1
    have h1 : (ν.map fun y => lift K ι S t + y) = ν := MeasureTheory.map_add_left_eq_self ν _
    have h2 := Measure.restrict_map (μ := ν) (measurable_const_add (lift K ι S t)) hHSm
    rw [h1, hHS, preimage_lift_add] at h2
    exact h2.symm

  set K₀ : Set (∀ v : ↥S, ι → v.1.adicCompletion K) :=
    Set.pi Set.univ fun v => Set.pi Set.univ fun _ => (v.1.adicCompletionIntegers K : Set (v.1.adicCompletion K))
    with hK₀
  have hOint : ∀ v : HeightOneSpectrum (𝓞 K), IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    Fact.out
  have hK₀c : IsCompact K₀ := by
    refine isCompact_univ_pi fun v => isCompact_univ_pi fun _ => ?_
    haveI : CompactSpace (v.1.adicCompletionIntegers K) := inferInstance
    exact isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace (v.1.adicCompletionIntegers K)))
  have hK₀o : IsOpen K₀ :=
    isOpen_set_pi Set.finite_univ fun v _ => isOpen_set_pi Set.finite_univ fun _ _ => hOint v.1
  have hK₀int : (interior K₀).Nonempty := by
    rw [hK₀o.interior_eq]
    exact ⟨0, fun v _ => fun _ _ => zero_mem _⟩

  set O : Set (ι → FiniteAdeleRing (𝓞 K) K) :=
    Set.pi Set.univ fun _ => NumberField.AdelicBox.integralFiniteAdeles (𝓞 K) K with hO
  have hO' : piS ⁻¹' K₀ ∩ HS = O := by
    ext y
    simp only [hK₀, hHS, hO, hpiS, Set.mem_inter_iff, Set.mem_preimage, Set.mem_univ_pi, Set.mem_setOf_eq,
      NumberField.AdelicBox.integralFiniteAdeles, SetLike.mem_coe]
    constructor
    · rintro ⟨h1, h2⟩ k v
      by_cases hv : v ∈ S
      · exact h1 ⟨v, hv⟩ k
      · exact h2 k v hv
    · intro h
      exact ⟨fun v k => h k v.1, fun k v _ => h k v⟩
  have hmK₀ : m K₀ = ν O := by
    rw [hm, Measure.map_apply hpiSm hK₀o.measurableSet, Measure.restrict_apply (hpiSm hK₀o.measurableSet), hO']
  have hOo : IsOpen O := isOpen_set_pi Set.finite_univ fun _ _ => NumberField.AdelicBox.isOpen_integralFiniteAdeles K
  have hOc : IsCompact O := isCompact_univ_pi fun _ => NumberField.AdelicBox.isCompact_integralFiniteAdeles K
  have hm0 : m K₀ ≠ 0 := by
    rw [hmK₀]; exact hOo.measure_ne_zero ν ⟨0, fun _ _ => fun v => zero_mem _⟩
  have hmtop : m K₀ ≠ ⊤ := by
    rw [hmK₀]; exact hOc.measure_lt_top.ne
  haveI : m.IsAddHaarMeasure := Measure.isAddHaarMeasure_of_isCompact_nonempty_interior m K₀ hK₀c hK₀int hm0 hmtop

  set π : Measure (∀ v : ↥S, ι → v.1.adicCompletion K) := Measure.pi fun v : ↥S => μ v.1 with hπ
  haveI : π.IsAddHaarMeasure := inferInstance
  have heq := Measure.isAddLeftInvariant_eq_smul m π
  refine ⟨(m.addHaarScalarFactor π : ℝ≥0∞), ?_, ENNReal.coe_ne_top, ?_⟩
  · exact ENNReal.coe_ne_zero.mpr (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure m π).ne'
  · conv_lhs => rw [heq]
    ext s _
    rw [Measure.coe_nnreal_smul_apply, Measure.smul_apply, smul_eq_mul]

end S_IsDedekindDomain_FiniteAdeleRing_exists_map_restrict_integralOutside_eq_smul_pi_of_isAddHaarMeasure
end P2MW
export P2MW.S_IsDedekindDomain_FiniteAdeleRing_exists_map_restrict_integralOutside_eq_smul_pi_of_isAddHaarMeasure (solution)
