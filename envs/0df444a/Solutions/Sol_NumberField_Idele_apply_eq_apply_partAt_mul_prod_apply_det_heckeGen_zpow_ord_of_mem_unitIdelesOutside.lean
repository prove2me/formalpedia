-- Prove2me | solution 1 for NumberField.Idele.apply_eq_apply_partAt_mul_prod_apply_det_heckeGen_zpow_ord_of_mem_unitIdelesOutside
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/188d5ad2-f3f7-5055-8708-50bc74c5117e

import Definitions.Def_NumberField_IdeleProductMeasure
import Theorems.Thm_NumberField_TateGlobal_apply_eq_one_of_forall_isUnramifiedCharAt_of_continuous
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_Idele_apply_eq_apply_partAt_mul_prod_apply_det_heckeGen_zpow_ord_of_mem_unitIdelesOutside

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain

open scoped Classical in
theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (hTS : Disjoint T S)
    (hur : ∀ v ∉ S, ∀ t : (v.adicCompletion K)ˣ, Valued.v (t : v.adicCompletion K) = 1 →
      ξ ⟨Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t), Subgroup.mem_top _⟩ = 1)
    (z : (AdeleRing (𝓞 K) K)ˣ)
    (hz : z ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K)))) :
    ξ ⟨z, Subgroup.mem_top z⟩ =
      ξ ⟨NumberField.Idele.partAt K S z, Subgroup.mem_top _⟩ *
        ∏ v ∈ T, ξ ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ ^
          NumberField.Idele.ord K v z := by

  let χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ :=
    { toFun := fun z => ξ ⟨z, Subgroup.mem_top z⟩
      map_one' := ξ.map_one
      map_mul' := fun a b => ξ.map_mul ⟨a, Subgroup.mem_top a⟩ ⟨b, Subgroup.mem_top b⟩ }
  have hχ : ∀ z : (AdeleRing (𝓞 K) K)ˣ, χ z = ξ ⟨z, Subgroup.mem_top z⟩ := fun z => rfl

  have hχc : Continuous χ := by
    rw [Units.continuous_iff]
    refine ⟨hξc, ?_⟩
    have hfun : (fun z : (AdeleRing (𝓞 K) K)ˣ => (((χ z)⁻¹ : ℂˣ) : ℂ)) =
        fun z => (((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))⁻¹ :=
      funext fun z => Units.val_inv_eq_inv_val _
    rw [hfun]
    exact hξc.inv₀ fun z => (ξ ⟨z, Subgroup.mem_top z⟩).ne_zero

  have hS : ∀ v ∉ S, NumberField.TateGlobal.IsUnramifiedCharAt χ v := by
    intro v hv t ht1 ht2
    rw [NumberField.TateGlobal.localChar_apply, hχ]
    apply hur v hv t
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at ht1 ht2
    refine le_antisymm ht1 ?_
    have hprod : Valued.v (t : v.adicCompletion K) *
        Valued.v ((t⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    calc (1 : WithZero (Multiplicative ℤ))
        = Valued.v (t : v.adicCompletion K) * Valued.v ((t⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) :=
          hprod.symm
      _ ≤ Valued.v (t : v.adicCompletion K) * 1 := mul_le_mul_right ht2 _
      _ = Valued.v (t : v.adicCompletion K) := mul_one _

  have hunit : χ (NumberField.Idele.unitPart K S z) = 1 :=
    NumberField.TateGlobal.apply_eq_one_of_forall_isUnramifiedCharAt_of_continuous K χ hχc S hS _
      (NumberField.Idele.unitPart_fst K S z) (NumberField.Idele.unitPart_snd_of_mem K S z)
      (NumberField.Idele.finitePartUnits_unitPart_mem_unitIdeles K S z)

  have hLS : ∀ v ∈ T.toList, v ∉ S := fun v hv => Finset.disjoint_left.1 hTS (Finset.mem_toList.1 hv)
  have hL : T.toList.Nodup := Finset.nodup_toList T
  have hz' : z ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K
      (↑S ∪ {v | v ∈ T.toList} : Set (HeightOneSpectrum (𝓞 K))) := by
    have hset : (↑S ∪ {v | v ∈ T.toList} : Set (HeightOneSpectrum (𝓞 K))) =
        (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K))) := by
      ext w
      simp [Finset.mem_toList]
    rw [hset]
    exact hz
  have hdec := NumberField.Idele.eq_partAt_mul_prod_mul_unitPart K S T.toList hLS hL z hz'

  have hgen : ∀ v : HeightOneSpectrum (𝓞 K),
      AutomorphicForm.uniformizerIdele K v = Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v) := by
    intro v
    refine Units.ext ?_
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    simp [heckeGen, heckeGenAt, AutomorphicForm.uniformizerIdele, diagOne_coe_apply, Matrix.det_fin_two]

  have key : χ z = χ (NumberField.Idele.partAt K S z) *
      ∏ v ∈ T, χ (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)) ^ NumberField.Idele.ord K v z := by
    conv_lhs => rw [hdec]
    rw [map_mul, map_mul, hunit, mul_one, map_list_prod, List.map_map, Finset.prod_map_toList]
    congr 1
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [Function.comp_apply, map_zpow, hgen]
  simpa only [hχ] using key

end S_NumberField_Idele_apply_eq_apply_partAt_mul_prod_apply_det_heckeGen_zpow_ord_of_mem_unitIdelesOutside
end P2MW
export P2MW.S_NumberField_Idele_apply_eq_apply_partAt_mul_prod_apply_det_heckeGen_zpow_ord_of_mem_unitIdelesOutside (solution)
