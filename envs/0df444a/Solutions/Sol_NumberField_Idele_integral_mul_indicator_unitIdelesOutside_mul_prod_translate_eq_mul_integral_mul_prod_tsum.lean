-- Prove2me | solution 1 for NumberField.Idele.integral_mul_indicator_unitIdelesOutside_mul_prod_translate_eq_mul_integral_mul_prod_tsum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/be6595b2-1c06-5952-8ca6-28f8b06f63a9

import Definitions.Def_NumberField_IdeleProductMeasure
import Theorems.Thm_NumberField_Idele_apply_eq_apply_partAt_mul_prod_apply_det_heckeGen_zpow_ord_of_mem_unitIdelesOutside
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_Idele_integral_mul_indicator_unitIdelesOutside_mul_prod_translate_eq_mul_integral_mul_prod_tsum

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain

open scoped Classical in
theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure]
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξ ⟨z, Subgroup.mem_top z⟩ = 1)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (hTS : Disjoint T S)
    (hur : ∀ v ∉ S, ∀ t : (v.adicCompletion K)ˣ, Valued.v (t : v.adicCompletion K) = 1 →
      ξ ⟨Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t), Subgroup.mem_top _⟩ = 1)
    (PZ : UnramifiedWhittaker.ProductMeasureData S νZK)
    (hPo : PZ.ord = NumberField.Idele.ord K) (hPp : PZ.projS = NumberField.Idele.partAt K S)
    (d : Kˣ)
    (Φ : (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hΦ : Integrable (fun zS : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) * Φ zS) PZ.νS)
    (φ : HeightOneSpectrum (𝓞 K) → ℤ → ℂ)
    (hφ : ∀ v ∈ T, Summable fun e : ℤ =>
      ‖((ξ ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ e * φ v e‖) :
    ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K))) :
            Set (AdeleRing (𝓞 K) K)ˣ).indicator
          (fun w => Φ (NumberField.Idele.partAt K S w) * ∏ v ∈ T, φ v (NumberField.Idele.ord K v w))
          (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) d) ∂νZK =
      (PZ.c : ℂ) * (∫ zS : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) * Φ zS ∂PZ.νS) *
        ∏ v ∈ T, ∑' e : ℤ,
          ((ξ ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ e * φ v e := by
  classical

  set dA : (AdeleRing (𝓞 K) K)ˣ := Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) d
    with hdA
  set ξ' : (AdeleRing (𝓞 K) K)ˣ → ℂ := fun z => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) with hξ'
  have hξ'mul : ∀ a b, ξ' (a * b) = ξ' a * ξ' b := by
    intro a b
    simp only [hξ']
    rw [← Units.val_mul, ← map_mul]
    rfl
  have hξ'd : ξ' dA⁻¹ = 1 := by
    simp only [hξ']
    rw [hξt dA⁻¹ ⟨d⁻¹, by rw [map_inv, hdA]⟩, Units.val_one]
  set U : Set (AdeleRing (𝓞 K) K)ˣ :=
    (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K))) :
      Set (AdeleRing (𝓞 K) K)ˣ) with hU
  set G : (AdeleRing (𝓞 K) K)ˣ → ℂ :=
    U.indicator (fun w => Φ (NumberField.Idele.partAt K S w) * ∏ v ∈ T, φ v (NumberField.Idele.ord K v w))
    with hG

  have h1 : ∫ z, ξ' z * G (z * dA) ∂νZK = ∫ z, ξ' z * G z ∂νZK := by
    have h := integral_mul_right_eq_self (μ := νZK) (fun z => ξ' (z * dA⁻¹) * G z) dA
    simp only [mul_assoc, mul_inv_cancel, mul_one] at h
    rw [h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [hξ'mul, hξ'd, mul_one]
  show ∫ z, ξ' z * G (z * dA) ∂νZK = _
  rw [h1]

  set L : List (HeightOneSpectrum (𝓞 K)) := T.toList with hL
  have hLS : ∀ v ∈ L, v ∉ S := fun v hv hvS =>
    Finset.disjoint_left.mp hTS (Finset.mem_toList.mp hv) hvS
  have hLn : L.Nodup := Finset.nodup_toList T
  have hUL : (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑S ∪ {v | v ∈ L}) : Set (AdeleRing (𝓞 K) K)ˣ) = U := by
    simp only [hU]
    congr 2
    ext v
    simp [hL, Finset.mem_toList]
  have hUm : MeasurableSet U := hUL ▸ PZ.measurableSet L hLS hLn
  set f : (AdeleRing (𝓞 K) K)ˣ → ℂ := fun z => ξ' z * Φ z with hf
  set ψ : HeightOneSpectrum (𝓞 K) → ℤ → ℂ := fun v e =>
    ((ξ ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ e * φ v e with hψ
  have h2 : ∫ z, ξ' z * G z ∂νZK =
      ∫ z in U, f (PZ.projS z) * (L.map fun v => ψ v (PZ.ord v z)).prod ∂νZK := by
    have hind : ∀ z, ξ' z * G z = U.indicator (fun z => ξ' z *
        (Φ (NumberField.Idele.partAt K S z) * ∏ v ∈ T, φ v (NumberField.Idele.ord K v z))) z := by
      intro z
      by_cases hz : z ∈ U
      · simp only [hG, Set.indicator_of_mem hz]
      · simp [hG, hz]
    simp_rw [hind]
    rw [integral_indicator hUm]
    refine setIntegral_congr_fun hUm fun z hz => ?_
    rw [hPp, hPo, Finset.prod_map_toList]
    have hsplit := NumberField.Idele.apply_eq_apply_partAt_mul_prod_apply_det_heckeGen_zpow_ord_of_mem_unitIdelesOutside
      K ξ hξc S T hTS hur z hz
    have hsplitC : ξ' z = ξ' (NumberField.Idele.partAt K S z) *
        ∏ v ∈ T, ((ξ ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^
          NumberField.Idele.ord K v z := by
      simp only [hξ']
      rw [hsplit, Units.val_mul, Units.coe_prod]
      simp only [Units.val_zpow_eq_zpow_val]
    rw [hsplitC]
    simp only [hf, hψ, Finset.prod_mul_distrib]
    ring
  rw [h2]

  obtain ⟨-, h3⟩ := PZ.tonelli L hLS hLn f ψ hΦ (fun v hv => hφ v (Finset.mem_toList.mp hv))
  rw [hUL] at h3
  rw [h3, Finset.prod_map_toList]

end S_NumberField_Idele_integral_mul_indicator_unitIdelesOutside_mul_prod_translate_eq_mul_integral_mul_prod_tsum
end P2MW
export P2MW.S_NumberField_Idele_integral_mul_indicator_unitIdelesOutside_mul_prod_translate_eq_mul_integral_mul_prod_tsum (solution)
