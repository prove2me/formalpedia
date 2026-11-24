-- Prove2me | solution 1 for GlobalTheory.AbsFubini.memLp_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:21:37.220921+00:00
-- url     : https://prove2.me/submissions/158b1f21-44dd-4663-854f-a03effcd7178

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IntegralKernelLiftsFubiniSigmaFinite
import Theorems.Thm_GlobalTheory_AbsFubini_core

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate ENNReal
open GlobalTheory GlobalTheory.AbsFubini
variable {X₁ X₂ Y : Type*} [MeasurableSpace X₁] [MeasurableSpace X₂] [MeasurableSpace Y]
  {μ₁ : Measure X₁} {μ₂ : Measure X₂} {ν : Measure Y} [SigmaFinite μ₁] [SigmaFinite μ₂] [SigmaFinite ν]
namespace GlobalTheory.AbsFubini
theorem _root_.solution {k : X₁ → Y → ℂ} {u : X₁ → ℂ} (hk : Measurable (Function.uncurry k))
    (hu : Measurable u) {N : X₁ → ℝ≥0∞} (hN : ∀ x, ∫⁻ y, ‖k x y‖ₑ ^ 2 ∂ν ≤ N x ^ 2)
    (hfin : ∫⁻ x, N x * ‖u x‖ₑ ∂μ₁ ≠ ⊤) :
    MemLp (fun y => ∫ x, k x y * u x ∂μ₁) 2 ν := by
  have hF : Measurable fun q : Y × X₁ => k q.2 q.1 * u q.2 :=
    (hk.comp (measurable_snd.prodMk measurable_fst)).mul (hu.comp measurable_snd)
  have hsm : StronglyMeasurable fun y => ∫ x, k x y * u x ∂μ₁ :=
    hF.stronglyMeasurable.integral_prod_right'
  refine ⟨hsm.aestronglyMeasurable, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) ?_
  have hA : Measurable (Function.uncurry fun x y => ‖k x y‖ₑ) := hk.enorm
  have hb : Measurable fun x => ‖u x‖ₑ := hu.enorm
  have hc := core (μ₁ := μ₁) (μ₂ := μ₁) (ν := ν) hA hA hb hb hN hN
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hfin hfin) (le_trans ?_ hc)
  refine lintegral_mono fun y => ?_
  have h1 : ‖∫ x, k x y * u x ∂μ₁‖ₑ ≤ ∫⁻ x, ‖k x y‖ₑ * ‖u x‖ₑ ∂μ₁ := by
    simpa only [enorm_mul] using enorm_integral_le_lintegral_enorm (μ := μ₁) (fun x => k x y * u x)
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two, pow_two]
  exact mul_le_mul' h1 h1
end GlobalTheory.AbsFubini
