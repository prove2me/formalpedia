-- Prove2me | solution 1 for GlobalTheory.Tw.IsCosetCutoff.isQuotMeasure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:42:19.717874+00:00
-- url     : https://prove2.me/submissions/ce67bb7e-a5ba-4529-9324-985404a63573

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_BruhatFunctionExistsClosedSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_QuotIntegrableIffCutoff
import Theorems.Thm_GlobalTheory_Tw_apply_out_mk
import Theorems.Thm_GlobalTheory_Tw_measurable_comp_out

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal
noncomputable section
open GlobalTheory GlobalTheory.Tw
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {T : Subgroup G} {μ : Measure G} {μT : Measure T}
namespace GlobalTheory.Tw
namespace IsCosetCutoff
theorem _root_.solution [SFinite μ] [μ.IsMulLeftInvariant] [SFinite μT] [μT.IsMulLeftInvariant]
    [μT.IsInvInvariant] {β : G → NNReal} (hβ : IsCosetCutoff T μT β) :
    IsQuotMeasure T μ μT ((μ.withDensity fun x => β x).map (Quotient.mk (QuotientGroup.rightRel T))) := by
  intro f hf
  have hb : Measurable fun x => (β x : ℝ≥0∞) := hβ.1.coe_nnreal_ennreal
  have hmul : Measurable fun p : G × T => (p.2 : G) * p.1 :=
    (measurable_subtype_coe.comp measurable_snd).mul measurable_fst
  have hmul' : Measurable fun p : G × T => ((p.2⁻¹ : T) : G) * p.1 :=
    (measurable_subtype_coe.comp measurable_snd.inv).mul measurable_fst
  have : μT.IsMulRightInvariant := by
    rw [← Measure.inv_eq_self μT]; infer_instance
  have hF : Measurable fun x => ∫⁻ t : T, f (t * x) ∂μT := (hf.comp hmul).lintegral_prod_right'
  have hinv : ∀ s ∈ T, ∀ x, ∫⁻ t : T, f (t * (s * x)) ∂μT = ∫⁻ t : T, f (t * x) ∂μT := fun s hs x => by
    rw [← lintegral_mul_right_eq_self (μ := μT) (fun t : T => f (t * x)) ⟨s, hs⟩]
    simp [mul_assoc]
  have hmk : Measurable (Quotient.mk (QuotientGroup.rightRel T)) := measurable_quotient_mk''
  rw [lintegral_map (measurable_comp_out hF hinv) hmk,
    lintegral_withDensity_eq_lintegral_mul _ hb (g := fun a => ∫⁻ t : T,
      f (t * Quotient.out (Quotient.mk (QuotientGroup.rightRel T) a)) ∂μT) ((measurable_comp_out hF hinv).comp hmk)]
  have e1 : ∀ x, ((fun x => (β x : ℝ≥0∞)) * fun a => ∫⁻ t : T,
      f (t * Quotient.out (Quotient.mk (QuotientGroup.rightRel T) a)) ∂μT) x = ∫⁻ t : T, β x * f (t * x) ∂μT := fun x => by
    rw [Pi.mul_apply, apply_out_mk (F := fun x => ∫⁻ t : T, f (t * x) ∂μT) hinv, lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  rw [lintegral_congr e1, lintegral_lintegral_swap ((hb.comp measurable_fst).mul (hf.comp hmul)).aemeasurable]
  have e2 : ∀ t : T, ∫⁻ x, β x * f (t * x) ∂μ = ∫⁻ x, β ((t⁻¹ : T) * x) * f x ∂μ := fun t => by
    rw [← lintegral_mul_left_eq_self (μ := μ) (fun x => β ((t⁻¹ : T) * x) * f x) t]
    simp
  rw [lintegral_congr e2,
    ← lintegral_lintegral_swap (f := fun x (t : T) => β ((t⁻¹ : T) * x) * f x)
      ((hb.comp hmul').mul (hf.comp measurable_fst)).aemeasurable]
  refine lintegral_congr fun x => ?_
  rw [lintegral_mul_const _ (f := fun t : T => (β ((t⁻¹ : T) * x) : ℝ≥0∞)) (hb.comp (hmul'.comp (measurable_prodMk_left))),
    lintegral_inv_eq_self (μ := μT) (fun t : T => (β (t * x) : ℝ≥0∞)), hβ.2, one_mul]
end IsCosetCutoff
end GlobalTheory.Tw
