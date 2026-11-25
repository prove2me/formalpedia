-- Prove2me | solution 1 for GlobalTheory.HypOrbitUnique.fubini_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:02:26.196751+00:00
-- url     : https://prove2.me/submissions/56a969c0-0f27-4b10-b5d2-bdee780744ba

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushI
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HyperboloidInvariantMeasureOrbitRepresentation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open GlobalTheory GlobalTheory.HypOrbitUnique
open PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.HU PI.RhsWLim.W.MB
namespace GlobalTheory.HypOrbitUnique
theorem _root_.solution {G X : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G]
    [MeasurableSpace X] (act : G → X → X) (hm : Measurable (Function.uncurry act))
    (hmul : ∀ g g' x, act (g * g') x = act g (act g' x)) (hone : ∀ x, act 1 x = x)
    (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    (Q : Measure X) [SFinite Q] (hQ : ∀ g, Q.map (act g) = Q) (x₀ : X)
    (htr : ∀ᵐ x ∂Q, ∃ g, act g x₀ = x) {f h : X → ℝ≥0∞} (hf : Measurable f) (hh : Measurable h) :
    (∫⁻ g, f (act g x₀) ∂μ) * ∫⁻ x, h x ∂Q = (∫⁻ x, f x ∂Q) * ∫⁻ g, h (act g⁻¹ x₀) ∂μ := by
  have hmg : ∀ g, Measurable (act g) := fun g => hm.comp measurable_prodMk_left
  have hm1 : Measurable fun p : X × G => act p.2 p.1 := hm.comp measurable_swap
  have hm2 : Measurable fun p : G × X => act p.1⁻¹ p.2 :=
    hm.comp (measurable_fst.inv.prodMk measurable_snd)
  calc (∫⁻ g, f (act g x₀) ∂μ) * ∫⁻ x, h x ∂Q
      = ∫⁻ x, (∫⁻ g, f (act g x₀) ∂μ) * h x ∂Q := (lintegral_const_mul _ hh).symm
    _ = ∫⁻ x, ∫⁻ g, f (act g x) * h x ∂μ ∂Q := by
        refine lintegral_congr_ae (htr.mono ?_)
        rintro x ⟨p, rfl⟩
        have hmx : Measurable fun g => f (act g (act p x₀)) := hf.comp (hm.comp measurable_prodMk_right)
        simp only
        rw [lintegral_mul_const _ hmx]
        congr 1
        simp_rw [← hmul]
        exact (lintegral_mul_right_eq_self (fun g => f (act g x₀)) p).symm
    _ = ∫⁻ g, ∫⁻ x, f (act g x) * h x ∂Q ∂μ :=
        lintegral_lintegral_swap ((hf.comp hm1).mul (hh.comp measurable_fst)).aemeasurable
    _ = ∫⁻ g, ∫⁻ x, f x * h (act g⁻¹ x) ∂Q ∂μ := by
        refine lintegral_congr fun g => ?_
        conv_rhs => rw [← hQ g]
        rw [lintegral_map (f := fun x => f x * h (act g⁻¹ x)) (hf.mul (hh.comp (hmg g⁻¹))) (hmg g)]
        refine lintegral_congr fun x => ?_
        rw [← hmul, inv_mul_cancel, hone]
    _ = ∫⁻ x, ∫⁻ g, f x * h (act g⁻¹ x) ∂μ ∂Q :=
        lintegral_lintegral_swap ((hf.comp measurable_snd).mul (hh.comp hm2)).aemeasurable
    _ = ∫⁻ x, f x * ∫⁻ g, h (act g⁻¹ x₀) ∂μ ∂Q := by
        refine lintegral_congr_ae (htr.mono ?_)
        rintro x ⟨p, rfl⟩
        have hmx : Measurable fun g : G => h (act g⁻¹ (act p x₀)) :=
          hh.comp (hm2.comp measurable_prodMk_right)
        simp only
        rw [lintegral_const_mul _ hmx]
        congr 1
        rw [← lintegral_mul_left_eq_self (fun g : G => h (act g⁻¹ x₀)) p⁻¹]
        refine lintegral_congr fun g => ?_
        rw [← hmul, _root_.mul_inv_rev, inv_inv]
    _ = _ := lintegral_mul_const _ hf
end GlobalTheory.HypOrbitUnique
