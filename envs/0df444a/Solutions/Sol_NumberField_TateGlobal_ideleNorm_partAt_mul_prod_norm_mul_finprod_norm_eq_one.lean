-- Prove2me | solution 1 for NumberField.TateGlobal.ideleNorm_partAt_mul_prod_norm_mul_finprod_norm_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/bab832a5-826d-591c-bdba-d30f1527911a

import Definitions.Def_NumberField_IdeleProductMeasure
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_ideleNorm_partAt_mul_prod_norm_mul_finprod_norm_eq_one
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one"

set_option autoImplicit false

p2m_open "MeasureTheory NumberField P2MW.S_NumberField_TateGlobal_ideleNorm_partAt_mul_prod_norm_mul_finprod_norm_eq_one.NumberField NumberField.AdelicLevel IsDedekindDomain"

namespace NumberField
p2m_export "NumberField" "InfinitePlace AdeleRing Idele.partAt Idele.partAt_snd_of_mem Idele.partAt_snd_of_not_mem AdelicHaar.adeleBorel AdelicHaar.borelSpace_adeleBorel TateGlobal.ideleNorm AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm AdeleRing.distribHaarChar_algebraMap"
namespace TateGlobal
p2m_export "NumberField.TateGlobal" "ideleNorm"
namespace IdeleNormPartAtAux
p2m_open "NumberField.TateGlobal NumberField"

variable (K : Type) [Field K] [NumberField K]

theorem finite_mulSupport_norm_snd (a : (AdeleRing (𝓞 K) K)ˣ) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) => ‖(a : AdeleRing (𝓞 K) K).2 v‖).Finite := by
  have h1 : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      ((a : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K :=
    ((a : AdeleRing (𝓞 K) K).2).2
  have h2 : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      (((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v ∈
        v.adicCompletionIntegers K :=
    (((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2).2
  have h := Filter.eventually_cofinite.mp (h1.and h2)
  refine h.subset fun v hv => ?_
  simp only [Set.mem_setOf_eq]
  intro hcon
  obtain ⟨hi, hi'⟩ := hcon
  apply hv
  have hle : ‖((a : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v‖ ≤ 1 :=
    Valued.toNormedField.norm_le_one_iff.mpr hi
  have hle' : ‖(((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v‖ ≤ 1 :=
    Valued.toNormedField.norm_le_one_iff.mpr hi'
  have hmul : ((a : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v *
      (((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v = 1 := by
    have h2 := congrArg (fun x : AdeleRing (𝓞 K) K => (x.2 : FiniteAdeleRing (𝓞 K) K) v) a.mul_inv
    exact h2
  have hnm : ‖((a : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v‖ *
      ‖(((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v‖ = 1 := by
    rw [← norm_mul, hmul, norm_one]
  show ‖((a : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v‖ = 1
  nlinarith [norm_nonneg (((a : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v),
    norm_nonneg ((((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v)]

end NumberField.TateGlobal.IdeleNormPartAtAux

open NumberField.TateGlobal.IdeleNormPartAtAux in
open scoped Classical in
theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (hTS : Disjoint T S) (a : Kˣ) :
    NumberField.TateGlobal.ideleNorm K
        (NumberField.Idele.partAt K S (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a)) *
      (∏ v ∈ T, ‖algebraMap K (v.adicCompletion K) (a : K)‖) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 K),
        (if v ∈ S ∪ T then (1 : ℝ) else ‖algebraMap K (v.adicCompletion K) (a : K)‖) = 1 := by
  set a' : (AdeleRing (𝓞 K) K)ˣ := Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a
    with ha'

  set f : HeightOneSpectrum (𝓞 K) → ℝ := fun v => ‖(a' : AdeleRing (𝓞 K) K).2 v‖ with hf
  have hfv : ∀ v, ‖algebraMap K (v.adicCompletion K) (a : K)‖ = f v := fun v => rfl
  simp_rw [hfv]
  have hfin : (Function.mulSupport f).Finite := finite_mulSupport_norm_snd K a'

  set s : Finset (HeightOneSpectrum (𝓞 K)) := hfin.toFinset ∪ (S ∪ T) with hs
  have hfs : Function.mulSupport f ⊆ ↑s := by
    intro v hv
    simp only [hs, Finset.coe_union, Set.Finite.coe_toFinset, Set.mem_union]
    exact Or.inl hv
  set g₁ : HeightOneSpectrum (𝓞 K) → ℝ := fun v => if v ∈ S then f v else 1 with hg₁
  set g₂ : HeightOneSpectrum (𝓞 K) → ℝ := fun v => if v ∈ S ∪ T then 1 else f v with hg₂
  have hg₁s : Function.mulSupport g₁ ⊆ ↑s := by
    intro v hv
    simp only [Function.mem_mulSupport, hg₁] at hv
    simp only [hs, Finset.coe_union, Set.mem_union, Finset.mem_coe]
    by_cases h : v ∈ S
    · exact Or.inr (Or.inl h)
    · exact absurd (if_neg h) hv
  have hg₂s : Function.mulSupport g₂ ⊆ ↑s := by
    intro v hv
    simp only [Function.mem_mulSupport, hg₂] at hv
    apply hfs
    simp only [Function.mem_mulSupport]
    by_cases h : v ∈ S ∪ T
    · exact absurd (if_pos h) hv
    · rwa [if_neg h] at hv

  have hpart : NumberField.TateGlobal.ideleNorm K (NumberField.Idele.partAt K S a') =
      (∏ w : InfinitePlace K, ‖(a' : AdeleRing (𝓞 K) K).1 w‖ ^ w.mult) * ∏ᶠ v, g₁ v := by
    unfold NumberField.TateGlobal.ideleNorm
    rw [NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm]
    congr 1
    refine finprod_congr fun v => ?_
    simp only [hg₁]
    split_ifs with h
    · rw [NumberField.Idele.partAt_snd_of_mem K S a' h]
    · rw [NumberField.Idele.partAt_snd_of_not_mem K S a' h, norm_one]

  have hpf : (∏ w : InfinitePlace K, ‖(a' : AdeleRing (𝓞 K) K).1 w‖ ^ w.mult) * ∏ᶠ v, f v = 1 := by
    rw [← NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm]
    have := @NumberField.AdeleRing.distribHaarChar_algebraMap K _ _
      (NumberField.AdelicHaar.adeleBorel (𝓞 K) K) (NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 K) K) a
    have h1 : (distribHaarChar (AdeleRing (𝓞 K) K)) a' = 1 := this
    rw [h1]; rfl
  rw [hpart, finprod_eq_prod_of_mulSupport_subset g₁ hg₁s, finprod_eq_prod_of_mulSupport_subset g₂ hg₂s]
  rw [finprod_eq_prod_of_mulSupport_subset f hfs] at hpf

  have hTs : T ⊆ s := by
    intro v hv; simp only [hs, Finset.mem_union]; exact Or.inr (Or.inr hv)
  have hT : ∏ v ∈ T, f v = ∏ v ∈ s, (if v ∈ T then f v else 1) := by
    rw [Finset.prod_ite_mem s T f, Finset.inter_eq_right.mpr hTs]
  have hsplit : ∏ v ∈ s, f v = (∏ v ∈ s, g₁ v) * (∏ v ∈ T, f v) * ∏ v ∈ s, g₂ v := by
    rw [hT, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    simp only [hg₁, hg₂, Finset.mem_union]
    by_cases h1 : v ∈ S
    · have h2 : v ∉ T := fun h => Finset.disjoint_left.mp hTS h h1
      simp [h1, h2]
    · by_cases h2 : v ∈ T
      · simp [h1, h2]
      · simp [h1, h2]
  calc _ = (∏ w : InfinitePlace K, ‖(a' : AdeleRing (𝓞 K) K).1 w‖ ^ w.mult) *
        ((∏ v ∈ s, g₁ v) * (∏ v ∈ T, f v) * ∏ v ∈ s, g₂ v) := by ring
    _ = 1 := by rw [← hsplit]; exact hpf

end S_NumberField_TateGlobal_ideleNorm_partAt_mul_prod_norm_mul_finprod_norm_eq_one
end P2MW
export P2MW.S_NumberField_TateGlobal_ideleNorm_partAt_mul_prod_norm_mul_finprod_norm_eq_one (solution)
