-- Prove2me | solution 1 for NumberField.Idele.measurePreserving_mul_right_sPartMeasure
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/d11c83d4-b8aa-56ed-bacf-6af252120ddb

import Definitions.Def_NumberField_IdeleProductMeasure
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_Idele_measurePreserving_mul_right_sPartMeasure

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal NNReal Classical

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

attribute [local instance] NumberField.Idele.isHaarMeasure_idelicHaar

noncomputable section

namespace RS40P1

variable (K : Type) [Field K] [NumberField K]

theorem partAt_eq_self (S : Finset (HeightOneSpectrum (𝓞 K))) (u : (AdeleRing (𝓞 K) K)ˣ)
    (hu : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ((u : AdeleRing (𝓞 K) K)).2 v = 1) :
    NumberField.Idele.partAt K S u = u := by
  apply Units.ext
  refine Prod.ext (NumberField.Idele.partAt_fst K S u) ?_
  refine RestrictedProduct.ext _ _ fun v => ?_
  by_cases hv : v ∈ S
  · exact NumberField.Idele.partAt_snd_of_mem K S u hv
  · exact (NumberField.Idele.partAt_snd_of_not_mem K S u hv).trans (hu v hv).symm

theorem inv_snd_eq_one {u : (AdeleRing (𝓞 K) K)ˣ} {v : HeightOneSpectrum (𝓞 K)} (hu : ((u : AdeleRing (𝓞 K) K)).2 v = 1) :
    (((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ)) : AdeleRing (𝓞 K) K).2 v = 1 := by
  have h : (((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ)) : AdeleRing (𝓞 K) K).2 v * ((u : AdeleRing (𝓞 K) K)).2 v = 1 := by
    have : (((u⁻¹ * u : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v = 1 := by rw [inv_mul_cancel]; rfl
    exact this
  rw [hu, mul_one] at h
  exact h

theorem mem_unitIdelesOutside (S : Finset (HeightOneSpectrum (𝓞 K))) (u : (AdeleRing (𝓞 K) K)ˣ)
    (hu : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ((u : AdeleRing (𝓞 K) K)).2 v = 1) :
    u ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K ((↑S : Set (HeightOneSpectrum (𝓞 K)))) := by
  rw [NumberField.AdeleRing.mem_unitIdelesOutside_iff, IsDedekindDomain.FiniteAdeleRing.mem_unitIdelesOutside_iff]
  intro v hv
  have hv' : v ∉ S := by simpa using hv
  constructor
  · show ((u : AdeleRing (𝓞 K) K)).2 v ∈ _
    rw [hu v hv']; exact one_mem _
  · show (((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ)) : AdeleRing (𝓞 K) K).2 v ∈ _
    rw [inv_snd_eq_one K (hu v hv')]; exact one_mem _

theorem map_mul_right_sPartMeasure (S : Finset (HeightOneSpectrum (𝓞 K))) (u : (AdeleRing (𝓞 K) K)ˣ)
    (hu : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ((u : AdeleRing (𝓞 K) K)).2 v = 1) :
    (NumberField.Idele.sPartMeasure K S).map (fun t => t * u) = NumberField.Idele.sPartMeasure K S := by

  have hfun : (fun t : (AdeleRing (𝓞 K) K)ˣ => t * u) = fun t => u * t := funext fun t => mul_comm t u
  rw [hfun]
  set U : Set (AdeleRing (𝓞 K) K)ˣ := (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K
    ((↑S : Set (HeightOneSpectrum (𝓞 K)))) : Set (AdeleRing (𝓞 K) K)ˣ) with hU
  have hUm : MeasurableSet U := (NumberField.Idele.isOpen_unitIdelesOutside K _).measurableSet
  have huU : u ∈ U := mem_unitIdelesOutside K S u hu
  have hpre : (fun t : (AdeleRing (𝓞 K) K)ˣ => u * t) ⁻¹' U = U := by
    ext t
    simp only [Set.mem_preimage, hU, SetLike.mem_coe]
    constructor
    · intro h
      have := Subgroup.mul_mem _ (Subgroup.inv_mem _ huU) h
      rwa [inv_mul_cancel_left] at this
    · intro h; exact Subgroup.mul_mem _ huU h
  have hcomp : (fun t : (AdeleRing (𝓞 K) K)ˣ => u * t) ∘ (NumberField.Idele.partAt K S) =
      (NumberField.Idele.partAt K S) ∘ (fun t => u * t) := by
    funext t
    simp only [Function.comp_apply, map_mul, partAt_eq_self K S u hu]
  unfold NumberField.Idele.sPartMeasure
  rw [Measure.map_map (measurable_const_mul u) (NumberField.Idele.measurable_partAt K S), hcomp,
    ← Measure.map_map (NumberField.Idele.measurable_partAt K S) (measurable_const_mul u)]
  congr 1
  rw [← hU]
  conv_lhs => rw [← hpre]
  rw [← Measure.restrict_map (measurable_const_mul u) hUm, map_mul_left_eq_self]

end RS40P1

theorem solution
    (K : Type) [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (u : (AdeleRing (𝓞 K) K)ˣ) (_huS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ((u : AdeleRing (𝓞 K) K)).2 v = 1) :
    MeasurePreserving (fun t : (AdeleRing (𝓞 K) K)ˣ => t * u) (NumberField.Idele.sPartMeasure K S) (NumberField.Idele.sPartMeasure K S) :=
  ⟨measurable_mul_const u, RS40P1.map_mul_right_sPartMeasure K S u _huS⟩

end
end S_NumberField_Idele_measurePreserving_mul_right_sPartMeasure
end P2MW
export P2MW.S_NumberField_Idele_measurePreserving_mul_right_sPartMeasure (solution)
