-- Prove2me | solution 1 for GlobalTheory.isogeny_sum_mem_and_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:53:45.739426+00:00
-- url     : https://prove2.me/submissions/3c7f03e3-9b93-4c22-81c5-9691b5ab678b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FockTranslationLaws
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ContinuousThetaSectionPointwiseNormSq
import Theorems.Thm_GlobalTheory_IsogenySum_exists_common_sublattice
import Theorems.Thm_GlobalTheory_IsogenySum_translate_differentiable
import Theorems.Thm_GlobalTheory_IsogenySum_pairing_density_continuous
import Theorems.Thm_GlobalTheory_IsogenySum_integral_pairing_density_eq_zero
import Theorems.Thm_GlobalTheory_IsogenySum_translate_translate
import Theorems.Thm_GlobalTheory_IsogenySum_thetaSectionPointwiseNormSq_periodic
import Theorems.Thm_GlobalTheory_IsogenySum_continuous_thetaSectionPointwiseNormSq
import Theorems.Thm_GlobalTheory_IsogenySum_thetaSectionPointwiseNormSq_eq
import Theorems.Thm_GlobalTheory_average_fundamentalDomain_eq_real
import Theorems.Thm_GlobalTheory_fock_translation_laws
import Theorems.Thm_GlobalTheory_integrableOn_fundamentalDomain_of_continuous


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Complex ReciprocityTheory.ChartRestriction.G.I2 MeasureTheory
open IsogenySum FockTranslation
namespace GlobalTheory
theorem _root_.solution {ι : Type} [Fintype ι] (U : ℕ → EuclideanSpace ℂ ι → (EuclideanSpace ℂ ι → ℂ) → EuclideanSpace ℂ ι → ℂ)
    (hU : ∀ (q : ℕ) a F v, U q a F v = cexp (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2) * F (v - a))
    (Y Y' : GT ι) (hY : (∀ x ∈ lat Y.b, ∀ y ∈ lat Y.b, Y.ka (x + y) = Y.ka x * Y.ka y * cexp (Real.pi * I * (Hf x y).im))) (hY' : (∀ x ∈ lat Y'.b, ∀ y ∈ lat Y'.b, Y'.ka (x + y) = Y'.ka x * Y'.ka y * cexp (Real.pi * I * (Hf x y).im)))
    (hag : ∀ x ∈ lat Y.b, x ∈ lat Y'.b → Y.ka x = Y'.ka x)
    (R : Finset (EuclideanSpace ℂ ι)) (hR : ∀ y ∈ R, y ∈ lat Y'.b) (hR' : ∀ y ∈ lat Y'.b, ∃! r ∈ R, y - r ∈ lat Y.b)
    (F : EuclideanSpace ℂ ι → ℂ) (hF : F ∈ Y.Sec 1) :
    (∑ y ∈ R, Y'.ka y • U 1 y F) ∈ Y'.Sec 1 ∧ Y'.l2 1 (∑ y ∈ R, Y'.ka y • U 1 y F) = R.card * Y.l2 1 F := by
  classical
  obtain ⟨-, -, -, -, h5, h6, -⟩ := fock_translation_laws U hU 1
  have hinj : ∀ y ∈ R, ∀ y' ∈ R, y - y' ∈ lat Y.b → y = y' := fun y hy y' hy' h =>
    (hR' y (hR y hy)).unique ⟨hy, by simp⟩ ⟨hy', h⟩
  have hdiff : Differentiable ℂ (∑ y ∈ R, Y'.ka y • U 1 y F) :=
    Differentiable.sum fun y _ => (translate_differentiable U hU hF.1 y).const_smul _
  have hmem : (∑ y ∈ R, Y'.ka y • U 1 y F) ∈ Y'.Sec 1 := by
    refine (h6 Y' _).2 ⟨hdiff, fun γ hγ => ?_⟩
    have e : Y'.ka γ • U 1 γ (∑ y ∈ R, Y'.ka y • U 1 y F) =
        ∑ y ∈ R, Y'.ka γ • U 1 γ (Y'.ka y • U 1 y F) := by
      funext v
      simp only [Pi.smul_apply, smul_eq_mul, hU 1 γ, Finset.sum_apply, Finset.mul_sum]
    rw [e]
    choose σ hσ hσ' using fun (y) (hy : y ∈ R) =>
      (hR' (γ + y) ((lat Y'.b).add_mem hγ (hR y hy))).exists
    have hσinj : ∀ y (hy : y ∈ R) y' (hy' : y' ∈ R), σ y hy = σ y' hy' → y = y' := by
      intro y hy y' hy' h
      refine hinj y hy y' hy' ?_
      have := (lat Y.b).sub_mem (hσ' y hy) (hσ' y' hy')
      rwa [h, sub_sub_sub_cancel_right, add_sub_add_left_eq_sub] at this
    refine Finset.sum_bij σ hσ hσinj ?_ ?_
    · intro z hz
      obtain ⟨a, ha, h⟩ := Finset.surj_on_of_inj_on_of_card_le σ hσ
        (fun a₁ a₂ h₁ h₂ h => hσinj a₁ h₁ a₂ h₂ h) le_rfl z hz
      exact ⟨a, ha, h.symm⟩
    · intro y hy
      have hd' : γ + y - σ y hy ∈ lat Y'.b :=
        (lat Y'.b).sub_mem ((lat Y'.b).add_mem hγ (hR y hy)) (hR _ (hσ y hy))
      have hfix : Y'.ka (γ + y - σ y hy) • U 1 (γ + y - σ y hy) F = F := by
        rw [← hag _ (hσ' y hy) hd']
        exact ((h6 Y F).1 hF).2 _ (hσ' y hy)
      rw [translate_translate U hU Y' hY' hγ (hR y hy)]
      conv_rhs => rw [← hfix]
      rw [translate_translate U hU Y' hY' (hR _ (hσ y hy)) hd', add_sub_cancel]
  refine ⟨hmem, ?_⟩
  obtain ⟨b, hb, hb'⟩ := exists_common_sublattice Y Y' R fun y hy => (hR' y hy).exists
  have e1 := average_fundamentalDomain_eq_real volume Y'.b b _
    (continuous_thetaSectionPointwiseNormSq Y' hdiff.continuous) (fun γ hγ v => thetaSectionPointwiseNormSq_periodic U hU Y' hmem hγ v) hb' 0
  have e2 := fun a => average_fundamentalDomain_eq_real volume Y.b b _
    (continuous_thetaSectionPointwiseNormSq Y hF.1.continuous) (fun γ hγ v => thetaSectionPointwiseNormSq_periodic U hU Y hF hγ v) hb a
  simp only [add_zero] at e1
  have e3 : ∫ v in ZSpan.fundamentalDomain b, Y'.ptN2 1 (∑ y ∈ R, Y'.ka y • U 1 y F) v =
      ∑ y ∈ R, ∫ v in ZSpan.fundamentalDomain b, Y.ptN2 1 F (v + -y) := by
    apply Complex.ofReal_injective
    rw [← integral_complex_ofReal]
    have hpt : ∀ v, ((Y'.ptN2 1 (∑ y ∈ R, Y'.ka y • U 1 y F) v : ℝ) : ℂ) =
        ∑ y ∈ R, ∑ y' ∈ R, (Y'.ka y * (starRingEnd ℂ) (Y'.ka y')) *
          (U 1 y F v * (starRingEnd ℂ) (U 1 y' F v) * cexp (-(Real.pi * Hf v v))) := by
      intro v
      rw [thetaSectionPointwiseNormSq_eq]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul]
      rw [Finset.sum_mul_sum]
      simp only [Finset.sum_mul]
      exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun y' _ => by ring
    have hint : ∀ y y', IntegrableOn (fun v => (Y'.ka y * (starRingEnd ℂ) (Y'.ka y')) *
          (U 1 y F v * (starRingEnd ℂ) (U 1 y' F v) * cexp (-(Real.pi * Hf v v))))
          (ZSpan.fundamentalDomain b) volume := fun y y' =>
      integrableOn_fundamentalDomain_of_continuous volume b _
        (continuous_const.mul (pairing_density_continuous U hU hF.1 y y'))
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    rw [integral_finset_sum _ fun y _ => integrable_finset_sum _ fun y' _ => hint y y',
      Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [integral_finset_sum _ fun y' _ => hint y y', Finset.sum_eq_single_of_mem y hy]
    · have hk : Y'.ka y * (starRingEnd ℂ) (Y'.ka y) = 1 := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Y'.ka_abs y (hR y hy)]; simp
      rw [hk, ← integral_complex_ofReal]
      refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
      simp only [one_mul]
      rw [← thetaSectionPointwiseNormSq_eq Y, ← sub_eq_add_neg]
      exact congrArg _ (h5 y F v)
    · intro y' hy' hne
      rw [integral_const_mul, integral_pairing_density_eq_zero U hU Y hF b hb y y'
        (fun x hx => Y'.integral _ _ (hb' hx) ((lat Y'.b).sub_mem (hR y hy) (hR y' hy')))
        (fun h => hne (hinj y hy y' hy' h).symm), mul_zero]
  unfold GT.l2
  rw [← e1, setAverage_eq, e3, Finset.smul_sum]
  simp only [← setAverage_eq, e2]
  simp
end GlobalTheory
