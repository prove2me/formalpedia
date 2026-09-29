-- Prove2me | solution 1 for NumberField.Idele.sPartMeasure_pos_of_isOpen_of_partAt_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/39db4d89-d69a-562c-a22f-0dc899063006

import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_Idele_sPartMeasure_pos_of_isOpen_of_partAt_eq

set_option autoImplicit false

open MeasureTheory NumberField NumberField.Idele IsDedekindDomain
open scoped ENNReal

noncomputable section

namespace RS40LMb

open Topology

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar

variable (K : Type) [Field K] [NumberField K]

theorem partAt_eq_self_of_forall_snd_eq_one (S : Finset (HeightOneSpectrum (𝓞 K)))
    (t₀ : (AdeleRing (𝓞 K) K)ˣ) (ht₀ : ∀ v, v ∉ S → ((t₀ : AdeleRing (𝓞 K) K)).2 v = 1) :
    partAt K S t₀ = t₀ := by
  classical
  apply Units.ext
  refine Prod.ext (partAt_fst K S t₀) (RestrictedProduct.ext _ _ fun v => ?_)
  by_cases hv : v ∈ S
  · exact partAt_snd_of_mem K S t₀ hv
  · exact (partAt_snd_of_not_mem K S t₀ hv).trans (ht₀ v hv).symm

theorem mem_unitIdelesOutside_of_forall_snd_eq_one (S : Finset (HeightOneSpectrum (𝓞 K)))
    (t₀ : (AdeleRing (𝓞 K) K)ˣ) (ht₀ : ∀ v, v ∉ S → ((t₀ : AdeleRing (𝓞 K) K)).2 v = 1) :
    t₀ ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑S : Set (HeightOneSpectrum (𝓞 K))) := by
  rw [NumberField.AdeleRing.mem_unitIdelesOutside_iff, IsDedekindDomain.FiniteAdeleRing.mem_unitIdelesOutside_iff]
  intro v hv
  have hv' : v ∉ S := fun h => hv (Finset.mem_coe.mpr h)
  have h1 : ((t₀ : AdeleRing (𝓞 K) K)).2 v = 1 := ht₀ v hv'
  have h2 : (((t₀⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v = 1 := by
    have hmul : ((t₀ : AdeleRing (𝓞 K) K)).2 v * (((t₀⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v = 1 := by
      have h : (((t₀ * t₀⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v = 1 := by rw [mul_inv_cancel]; rfl
      exact h
    rwa [h1, one_mul] at hmul
  refine ⟨?_, ?_⟩
  · change ((t₀ : AdeleRing (𝓞 K) K)).2 v ∈ v.adicCompletionIntegers K
    rw [h1]; exact one_mem _
  · change (((t₀⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v ∈ v.adicCompletionIntegers K
    rw [h2]; exact one_mem _

end RS40LMb

end

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar

theorem solution
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (t₀ : (AdeleRing (𝓞 F) F)ˣ)
    (ht₀ : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → ((t₀ : AdeleRing (𝓞 F) F)).2 v = 1)
    (U : Set (AdeleRing (𝓞 F) F)ˣ) (hU : IsOpen U) (hU₀ : t₀ ∈ U) :
    0 < sPartMeasure F S U := by
  have hmeas : MeasurableSet U := hU.measurableSet
  rw [NumberField.Idele.sPartMeasure, Measure.map_apply (measurable_partAt F S) hmeas,
    Measure.restrict_apply (hmeas.preimage (measurable_partAt F S))]
  have hopen : IsOpen ((partAt F S) ⁻¹' U ∩
      (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S : Set (HeightOneSpectrum (𝓞 F))) :
        Set (AdeleRing (𝓞 F) F)ˣ)) :=
    (hU.preimage (continuous_partAt F S)).inter (isOpen_unitIdelesOutside F _)
  refine hopen.measure_pos (idelicHaar F) ⟨t₀, ?_, RS40LMb.mem_unitIdelesOutside_of_forall_snd_eq_one F S t₀ ht₀⟩
  show partAt F S t₀ ∈ U
  rw [RS40LMb.partAt_eq_self_of_forall_snd_eq_one F S t₀ ht₀]
  exact hU₀

end S_NumberField_Idele_sPartMeasure_pos_of_isOpen_of_partAt_eq
end P2MW
export P2MW.S_NumberField_Idele_sPartMeasure_pos_of_isOpen_of_partAt_eq (solution)
