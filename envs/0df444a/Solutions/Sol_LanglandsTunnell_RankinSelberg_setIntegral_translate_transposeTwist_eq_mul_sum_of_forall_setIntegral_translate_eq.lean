-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.setIntegral_translate_transposeTwist_eq_mul_sum_of_forall_setIntegral_translate_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/b9c935fa-f789-548d-a642-883798590cc6

import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AdelicDock_LocalEmbedding
import Theorems.Thm_AutomorphicForm_map_transposeInvN_eq_self_of_isHaarMeasure_fin_two
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_setIntegral_translate_transposeTwist_eq_mul_sum_of_forall_setIntegral_translate_eq
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction NumberField.StandardAddChar

open NumberField.AdelicLevel (diagOne)

set_option maxHeartbeats 1600000

namespace SepTransportF4

noncomputable section

attribute [local instance] AutomorphicForm.localGLBorel
attribute [local instance] AutomorphicForm.borelSpace_localGLBorel

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

theorem continuous_T : Continuous (transposeInvN (Fin 2) : G → G) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (Units.continuous_coe_inv.matrix_transpose :
      Continuous fun g : G => Matrix.transpose ((g⁻¹ : G) : Mat))
  · exact (Units.continuous_val.matrix_transpose :
      Continuous fun g : G => Matrix.transpose ((g : G) : Mat))

def Tmeq : G ≃ᵐ G where
  toEquiv := ⟨transposeInvN (Fin 2), transposeInvN (Fin 2), transposeInvN_transposeInvN (Fin 2), transposeInvN_transposeInvN (Fin 2)⟩
  measurable_toFun := (continuous_T p).measurable
  measurable_invFun := (continuous_T p).measurable

theorem Tmeq_apply (g : G) : Tmeq p g = transposeInvN (Fin 2) g := rfl

theorem setIntegral_comp_T (μ₂ : Measure G) [μ₂.IsHaarMeasure] (S : Set G)
    (hS : (transposeInvN (Fin 2)) ⁻¹' S = S) (f : G → ℂ) :
    ∫ ω in S, f (transposeInvN (Fin 2) ω) ∂μ₂ = ∫ ω in S, f ω ∂μ₂ := by
  have hmap : Measure.map (Tmeq p) μ₂ = μ₂ := map_transposeInvN_eq_self_of_isHaarMeasure_fin_two p μ₂
  have hS' : (Tmeq p) ⁻¹' S = S := hS
  calc ∫ ω in S, f (transposeInvN (Fin 2) ω) ∂μ₂
      = ∫ ω, f (Tmeq p ω) ∂(μ₂.restrict ((Tmeq p) ⁻¹' S)) := by rw [hS']; rfl
    _ = ∫ y, f y ∂(Measure.map (Tmeq p) (μ₂.restrict ((Tmeq p) ⁻¹' S))) := (integral_map_equiv (Tmeq p) f).symm
    _ = ∫ y, f y ∂((Measure.map (Tmeq p) μ₂).restrict S) := by rw [MeasurableEquiv.restrict_map]
    _ = ∫ y in S, f y ∂μ₂ := by rw [hmap]

theorem modulus_det_eq_one_of_mem (Ω : Subgroup G) (hΩc : IsCompact (Ω : Set G)) :
    ∀ ω ∈ Ω, (modulus ((Matrix.GeneralLinearGroup.det ω : Fˣ) : F) : ℝ) = 1 := by
  have hf : ∀ g : G, (modulus ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) : ℝ) =
      ‖((Matrix.GeneralLinearGroup.det g : Fˣ) : F)‖ := fun g => by
    rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm]
    rfl
  have hcont : Continuous fun g : G => ‖((Matrix.GeneralLinearGroup.det g : Fˣ) : F)‖ := by
    refine continuous_norm.comp ?_
    have : (fun g : G => ((Matrix.GeneralLinearGroup.det g : Fˣ) : F)) = fun g : G => (g : Mat).det := by
      funext g; rfl
    rw [this]
    exact Units.continuous_val.matrix_det
  obtain ⟨C, hC⟩ := hΩc.exists_bound_of_continuousOn hcont.continuousOn
  have hle : ∀ ω ∈ Ω, ∀ n : ℕ, ‖((Matrix.GeneralLinearGroup.det ω : Fˣ) : F)‖ ^ n ≤ C := by
    intro ω hω n
    have h1 := hC (ω ^ n) (Ω.pow_mem hω n)
    rw [Real.norm_of_nonneg (norm_nonneg _), map_pow, Units.val_pow_eq_pow_val, norm_pow] at h1
    exact h1
  intro ω hω
  rw [hf]
  have hpos : 0 < ‖((Matrix.GeneralLinearGroup.det ω : Fˣ) : F)‖ := norm_pos_iff.mpr (Matrix.GeneralLinearGroup.det ω).ne_zero
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hinv : ‖((Matrix.GeneralLinearGroup.det ω⁻¹ : Fˣ) : F)‖ = ‖((Matrix.GeneralLinearGroup.det ω : Fˣ) : F)‖⁻¹ := by
      rw [map_inv, Units.val_inv_eq_inv_val, norm_inv]
    have hgt' : 1 < ‖((Matrix.GeneralLinearGroup.det ω⁻¹ : Fˣ) : F)‖ := by
      rw [hinv]; exact one_lt_inv₀ hpos |>.mpr hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C hgt'
    exact absurd (hle ω⁻¹ (Ω.inv_mem hω) n) (not_le.mpr hn)
  · obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C hgt
    exact absurd (hle ω hω n) (not_le.mpr hn)

end

end SepTransportF4

open SepTransportF4 in
theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (Ω : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) (hΩc : IsCompact (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))))
    (hΩt : ∀ ω ∈ Ω, transposeInvN (Fin 2) ω ∈ Ω)
    (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (ι : Type) [Fintype ι] (wj : ι → GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (c : ι → GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (a d : GL (Fin 2) (p.adicCompletion ℚ)) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure],
      (∀ g h : GL (Fin 2) (p.adicCompletion ℚ),
        ∫ ω in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))), w (g * ω * h) ∂μ₂ =
          ((μ₂ (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ)))).toReal : ℂ) * ∑ j, c j h * wj j g) →
      ∀ g h : GL (Fin 2) (p.adicCompletion ℚ),
        ∫ ω in (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))),
            (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det (d * g) : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) * w (a * transposeInvN (Fin 2) (d * g))) (g * ω * h) ∂μ₂ =
          ((μ₂ (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ)))).toReal : ℂ) *
            ∑ j, (((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) * c j (transposeInvN (Fin 2) h)) *
              (((modulus ((Matrix.GeneralLinearGroup.det (d * g) : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) * wj j (a * transposeInvN (Fin 2) (d * g))) := by
  intro μ₂ _ hsep g h
  letI := localGLBorel ℚ p
  haveI := borelSpace_localGLBorel ℚ p
  have hΩm : MeasurableSet (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))) := hΩc.measurableSet
  have h1 := modulus_det_eq_one_of_mem p Ω hΩc

  have hpt : ∀ ω ∈ (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))),
      (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det (d * g) : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) *
          w (a * transposeInvN (Fin 2) (d * g))) (g * ω * h) =
        ((modulus ((Matrix.GeneralLinearGroup.det (d * g) : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) *
          ((modulus ((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ)) : ℝ) : ℂ) *
          w (a * transposeInvN (Fin 2) (d * g) * transposeInvN (Fin 2) ω * transposeInvN (Fin 2) h) := by
    intro ω hω
    have hω1 := h1 ω hω
    simp only []
    have hass : d * (g * ω * h) = d * g * ω * h := by simp only [mul_assoc]
    rw [hass, transposeInvN_mul, transposeInvN_mul, map_mul, map_mul, Units.val_mul, Units.val_mul, modulus_mul, modulus_mul,
      NNReal.coe_mul, NNReal.coe_mul, hω1, mul_one]
    push_cast
    simp only [mul_assoc]
  rw [setIntegral_congr_fun hΩm hpt, integral_const_mul]

  have hS : (transposeInvN (Fin 2)) ⁻¹' (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))) = (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))) := by
    ext x
    simp only [Set.mem_preimage, SetLike.mem_coe]
    constructor
    · intro hx; have := hΩt _ hx; rwa [transposeInvN_transposeInvN] at this
    · intro hx; exact hΩt _ hx
  have hcov := setIntegral_comp_T p μ₂ (Ω : Set (GL (Fin 2) (p.adicCompletion ℚ))) hS
    (fun ω => w (a * transposeInvN (Fin 2) (d * g) * ω * transposeInvN (Fin 2) h))
  rw [hcov, hsep (a * transposeInvN (Fin 2) (d * g)) (transposeInvN (Fin 2) h)]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

#print axioms solution

end S_LanglandsTunnell_RankinSelberg_setIntegral_translate_transposeTwist_eq_mul_sum_of_forall_setIntegral_translate_eq
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_setIntegral_translate_transposeTwist_eq_mul_sum_of_forall_setIntegral_translate_eq (solution)
