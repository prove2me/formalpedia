-- Prove2me | solution 1 for HaarQuotient.integrable_integral_comp_mul_out_and_integral_eq_integral_integral_comp_mul_out
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/51bbbd32-d21f-5d34-ae32-d45263887202

import Mathlib
import Definitions.Def_HaarQuotient
import Theorems.Thm_HaarQuotient_lintegral_eq_lintegral_lintegral_mul_out
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HaarQuotient_integrable_integral_comp_mul_out_and_integral_eq_integral_integral_comp_mul_out

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace BochnerQuot

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem sigmaCompactSpace_subgroup (H : Subgroup G) (hH : IsClosed (H : Set G)) : SigmaCompactSpace H :=
  hH.isClosedEmbedding_subtypeVal.sigmaCompactSpace

theorem exists_out_mk (H : Subgroup G) (g : G) :
    ∃ h : H, (Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out = (h : G) * g := by
  have hmem : (Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out ∈
      MulAction.orbitRel.Quotient.orbit (Quotient.mk'' g : MulAction.orbitRel.Quotient H G) := by
    rw [MulAction.orbitRel.Quotient.mem_orbit]
    exact Quotient.out_eq _
  rw [MulAction.orbitRel.Quotient.orbit_mk] at hmem
  obtain ⟨h, hh⟩ := hmem
  exact ⟨h, by rw [← hh]; rfl⟩

theorem measurable_fibre_lintegral (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant] (F : G → ℝ≥0∞) (hF : Measurable F) :
    Measurable fun q : MulAction.orbitRel.Quotient H G => ∫⁻ x : H, F ((x : G) * q.out) ∂μH := by
  haveI := sigmaCompactSpace_subgroup H hH
  rw [measurable_from_quotient]
  have h1 : ((fun q : MulAction.orbitRel.Quotient H G => ∫⁻ x : H, F ((x : G) * q.out) ∂μH) ∘ Quotient.mk'') =
      fun g : G => ∫⁻ x : H, F ((x : G) * g) ∂μH := by
    funext g
    obtain ⟨h, hh⟩ := exists_out_mk H g
    simp only [Function.comp_apply, hh]
    have := lintegral_mul_right_eq_self (μ := μH) (fun y : H => F ((y : G) * g)) h
    simp only [Subgroup.coe_mul, mul_assoc] at this
    exact this
  rw [h1]
  exact Measurable.lintegral_prod_right
    (f := fun (g : G) (x : H) => F ((x : G) * g))
    (hF.comp ((measurable_subtype_coe.comp measurable_snd).mul measurable_fst))

theorem measurable_fibre_integral (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (u : G → E) (hu : Measurable u) :
    Measurable fun q : MulAction.orbitRel.Quotient H G => ∫ x : H, u ((x : G) * q.out) ∂μH := by
  haveI := sigmaCompactSpace_subgroup H hH
  rw [measurable_from_quotient]
  have h1 : ((fun q : MulAction.orbitRel.Quotient H G => ∫ x : H, u ((x : G) * q.out) ∂μH) ∘ Quotient.mk'') =
      fun g : G => ∫ x : H, u ((x : G) * g) ∂μH := by
    funext g
    obtain ⟨h, hh⟩ := exists_out_mk H g
    simp only [Function.comp_apply, hh]
    have := integral_mul_right_eq_self (μ := μH) (fun y : H => u ((y : G) * g)) h
    simp only [Subgroup.coe_mul, mul_assoc] at this
    exact this
  rw [h1]
  have hsm : StronglyMeasurable (Function.uncurry fun (g : G) (x : H) => u ((x : G) * g)) :=
    (hu.comp ((measurable_subtype_coe.comp measurable_snd).mul measurable_fst)).stronglyMeasurable
  exact (hsm.integral_prod_right' (ν := μH)).measurable

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [BorelSpace G] in

theorem measurable_fibre [MeasurableMul₂ G] (H : Subgroup G) {E : Type*} [MeasurableSpace E] (u : G → E) (hu : Measurable u)
    (q : MulAction.orbitRel.Quotient H G) : Measurable fun x : H => u ((x : G) * q.out) :=
  hu.comp (measurable_subtype_coe.mul_const _)

variable (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
  (H : Subgroup G) (hH : IsClosed (H : Set G))
  (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]

include hH in

theorem ae_integrable_fibre {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (u : G → E) (hu : Measurable u) (hui : ∫⁻ g, ‖u g‖ₑ ∂μ < ∞) :
    ∀ᵐ q ∂(HaarQuotient.measure μ H μH), Integrable (fun x : H => u ((x : G) * q.out)) μH := by
  have key := HaarQuotient.lintegral_eq_lintegral_lintegral_mul_out μ H hH μH (fun g => ‖u g‖ₑ) hu.enorm
  have hA := measurable_fibre_lintegral H hH μH (fun g => ‖u g‖ₑ) hu.enorm
  have hfin : ∫⁻ q, (∫⁻ x : H, ‖u ((x : G) * q.out)‖ₑ ∂μH) ∂(HaarQuotient.measure μ H μH) < ∞ := by
    rw [← key]; exact hui
  filter_upwards [ae_lt_top hA hfin.ne] with q hq
  exact ⟨(measurable_fibre H u hu q).aestronglyMeasurable, hq⟩

include hH in

theorem integrable_fibre_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (u : G → E) (hu : Measurable u) (hui : ∫⁻ g, ‖u g‖ₑ ∂μ < ∞) :
    Integrable (fun q : MulAction.orbitRel.Quotient H G => ∫ x : H, u ((x : G) * q.out) ∂μH)
      (HaarQuotient.measure μ H μH) := by
  have key := HaarQuotient.lintegral_eq_lintegral_lintegral_mul_out μ H hH μH (fun g => ‖u g‖ₑ) hu.enorm
  refine ⟨(measurable_fibre_integral H hH μH u hu).aestronglyMeasurable, ?_⟩
  show ∫⁻ q, ‖∫ x : H, u ((x : G) * q.out) ∂μH‖ₑ ∂(HaarQuotient.measure μ H μH) < ∞
  calc ∫⁻ q, ‖∫ x : H, u ((x : G) * q.out) ∂μH‖ₑ ∂(HaarQuotient.measure μ H μH)
      ≤ ∫⁻ q, (∫⁻ x : H, ‖u ((x : G) * q.out)‖ₑ ∂μH) ∂(HaarQuotient.measure μ H μH) :=
        lintegral_mono fun q => enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ g, ‖u g‖ₑ ∂μ := key.symm
    _ < ∞ := hui

include hH in

theorem integral_eq_real (u : G → ℝ) (hu : Measurable u) (hui : ∫⁻ g, ‖u g‖ₑ ∂μ < ∞) :
    ∫ g, u g ∂μ = ∫ q, (∫ x : H, u ((x : G) * q.out) ∂μH) ∂(HaarQuotient.measure μ H μH) := by
  have hmp : Measurable fun g => ENNReal.ofReal (u g) := ENNReal.measurable_ofReal.comp hu
  have hmn : Measurable fun g => ENNReal.ofReal (-u g) := ENNReal.measurable_ofReal.comp hu.neg
  have keyp := HaarQuotient.lintegral_eq_lintegral_lintegral_mul_out μ H hH μH _ hmp
  have keyn := HaarQuotient.lintegral_eq_lintegral_lintegral_mul_out μ H hH μH _ hmn
  have hAp := measurable_fibre_lintegral H hH μH _ hmp
  have hAn := measurable_fibre_lintegral H hH μH _ hmn
  have hle_p : ∫⁻ g, ENNReal.ofReal (u g) ∂μ < ∞ :=
    lt_of_le_of_lt (lintegral_mono fun g => by
      rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (le_abs_self _)) hui
  have hle_n : ∫⁻ g, ENNReal.ofReal (-u g) ∂μ < ∞ :=
    lt_of_le_of_lt (lintegral_mono fun g => by
      rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (neg_le_abs _)) hui
  have hfinp : ∫⁻ q, (∫⁻ x : H, ENNReal.ofReal (u ((x : G) * q.out)) ∂μH) ∂(HaarQuotient.measure μ H μH) < ∞ := by
    rw [← keyp]; exact hle_p
  have hfinn : ∫⁻ q, (∫⁻ x : H, ENNReal.ofReal (-u ((x : G) * q.out)) ∂μH) ∂(HaarQuotient.measure μ H μH) < ∞ := by
    rw [← keyn]; exact hle_n
  have hui' : Integrable u μ := ⟨hu.aestronglyMeasurable, hui⟩
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hui']
  have hfib := ae_integrable_fibre μ H hH μH u hu hui
  have hrw : ∀ᵐ q ∂(HaarQuotient.measure μ H μH), (∫ x : H, u ((x : G) * q.out) ∂μH) =
      (∫⁻ x : H, ENNReal.ofReal (u ((x : G) * q.out)) ∂μH).toReal -
        (∫⁻ x : H, ENNReal.ofReal (-u ((x : G) * q.out)) ∂μH).toReal := by
    filter_upwards [hfib] with q hq
    exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part hq
  rw [integral_congr_ae hrw, integral_sub (integrable_toReal_of_lintegral_ne_top hAp.aemeasurable hfinp.ne)
    (integrable_toReal_of_lintegral_ne_top hAn.aemeasurable hfinn.ne),
    integral_toReal hAp.aemeasurable (ae_lt_top hAp hfinp.ne),
    integral_toReal hAn.aemeasurable (ae_lt_top hAn hfinn.ne), ← keyp, ← keyn]

end BochnerQuot

open BochnerQuot in
theorem solution
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (f : G → ℂ) (hf : Measurable f) (hfi : ∫⁻ g, ‖f g‖ₑ ∂μ < ∞) :
    (∀ᵐ q ∂(HaarQuotient.measure μ H μH), Integrable (fun x : H => f ((x : G) * q.out)) μH) ∧
    Integrable (fun q : MulAction.orbitRel.Quotient H G => (∫ x : H, f ((x : G) * q.out) ∂μH))
      (HaarQuotient.measure μ H μH) ∧
    ∫ g, f g ∂μ = ∫ q, (∫ x : H, f ((x : G) * q.out) ∂μH) ∂(HaarQuotient.measure μ H μH) := by
  refine ⟨ae_integrable_fibre μ H hH μH f hf hfi, integrable_fibre_integral μ H hH μH f hf hfi, ?_⟩

  have hre : Measurable fun g => (f g).re := Complex.measurable_re.comp hf
  have him : Measurable fun g => (f g).im := Complex.measurable_im.comp hf
  have hrei : ∫⁻ g, ‖(f g).re‖ₑ ∂μ < ∞ :=
    lt_of_le_of_lt (lintegral_mono fun g => by
      rw [← ofReal_norm, ← ofReal_norm, Real.norm_eq_abs]
      exact ENNReal.ofReal_le_ofReal (Complex.abs_re_le_norm _)) hfi
  have himi : ∫⁻ g, ‖(f g).im‖ₑ ∂μ < ∞ :=
    lt_of_le_of_lt (lintegral_mono fun g => by
      rw [← ofReal_norm, ← ofReal_norm, Real.norm_eq_abs]
      exact ENNReal.ofReal_le_ofReal (Complex.abs_im_le_norm _)) hfi
  have hfI : Integrable f μ := ⟨hf.aestronglyMeasurable, hfi⟩
  have hR := integral_eq_real μ H hH μH _ hre hrei
  have hJ := integral_eq_real μ H hH μH _ him himi
  have hRi := integrable_fibre_integral μ H hH μH _ hre hrei
  have hJi := integrable_fibre_integral μ H hH μH _ him himi
  have hfib := ae_integrable_fibre μ H hH μH f hf hfi
  rw [← integral_re_add_im hfI]
  simp only [RCLike.re_to_complex, RCLike.im_to_complex, RCLike.I_to_complex]
  rw [hR, hJ]
  have hrw : ∀ᵐ q ∂(HaarQuotient.measure μ H μH), (∫ x : H, f ((x : G) * q.out) ∂μH) =
      ((∫ x : H, (f ((x : G) * q.out)).re ∂μH : ℝ) : ℂ) +
        ((∫ x : H, (f ((x : G) * q.out)).im ∂μH : ℝ) : ℂ) * Complex.I := by
    filter_upwards [hfib] with q hq
    have h := integral_re_add_im hq
    simp only [RCLike.re_to_complex, RCLike.im_to_complex, RCLike.I_to_complex] at h
    exact h.symm
  rw [integral_congr_ae hrw, integral_add hRi.ofReal (hJi.ofReal.mul_const _), integral_mul_const,
    integral_complex_ofReal, integral_complex_ofReal]
  rfl

end S_HaarQuotient_integrable_integral_comp_mul_out_and_integral_eq_integral_integral_comp_mul_out
end P2MW
export P2MW.S_HaarQuotient_integrable_integral_comp_mul_out_and_integral_eq_integral_integral_comp_mul_out (solution)
