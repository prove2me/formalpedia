-- Prove2me | solution 1 for GlobalTheory.FunObj.integral_prod_mul_of_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:17:04.189456+00:00
-- url     : https://prove2.me/submissions/8e13b92f-24d7-4364-8cb9-bc30c75875e7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingPiProdSplit
import Theorems.Thm_GlobalTheory_FunObj_measurePreserving_piProdSplit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
variable {ι : Type*} [Fintype ι] {α β γ : ι → Type*} [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSpace (β i)]
  [∀ i, MeasurableSpace (γ i)]
namespace GlobalTheory.FunObj
theorem _root_.solution {μ : ∀ i, Measure (α i)} {ν : ∀ i, Measure (β i)} {ρ : ∀ i, Measure (γ i)}
    [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)] [∀ i, SigmaFinite (ρ i)]
    {g : ∀ i, α i × β i → γ i} (hg : ∀ i, MeasurePreserving (g i) ((μ i).prod (ν i)) (ρ i))
    {p : ∀ i, γ i → α i} (hp : ∀ i, Measurable (p i)) (hpg : ∀ i a b, p i (g i (a, b)) = a)
    {F : ∀ i, γ i → ℂ} (hF : ∀ i, Integrable (F i) (ρ i))
    {H : (∀ i, α i) → ℂ} (hH : Measurable H) (hb : ∀ a, ‖H a‖ ≤ 1) :
    Integrable (fun e : ∀ i, γ i => (∏ i, F i (e i)) * H fun i => p i (e i)) (Measure.pi ρ) ∧
    Integrable (fun a : ∀ i, α i => (∏ i, ∫ b, F i (g i (a i, b)) ∂(ν i)) * H a) (Measure.pi μ) ∧
    ∫ e, (∏ i, F i (e i)) * H (fun i => p i (e i)) ∂(Measure.pi ρ) =
      ∫ a, (∏ i, ∫ b, F i (g i (a i, b)) ∂(ν i)) * H a ∂(Measure.pi μ) := by
  have hI : Integrable (fun e : ∀ i, γ i => (∏ i, F i (e i)) * H fun i => p i (e i)) (Measure.pi ρ) :=
    (Integrable.fintype_prod_dep hF).mul_bdd
      (hH.comp (measurable_pi_lambda _ fun i => (hp i).comp (measurable_pi_apply i))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun _ => hb _)
  have hΘ := (measurePreserving_pi _ _ hg).comp (measurePreserving_piProdSplit μ ν).symm
  have hJ := (hΘ.integrable_comp hI.aestronglyMeasurable).2 hI
  have key : ∀ a : ∀ i, α i, ∫ b, ((fun e : ∀ i, γ i => (∏ i, F i (e i)) * H fun i => p i (e i)) ∘
      ((fun a i => g i (a i)) ∘ (piProdSplit α β).symm)) (a, b) ∂(Measure.pi ν) =
      (∏ i, ∫ b, F i (g i (a i, b)) ∂(ν i)) * H a := fun a => by
    rw [← integral_fintype_prod_eq_prod (fun i b => F i (g i (a i, b))), ← integral_mul_const]
    congr 1
    funext b
    show (∏ i, F i (g i (a i, b i))) * H (fun i => p i (g i (a i, b i))) = _
    simp only [hpg]
  refine ⟨hI, ?_, ?_⟩
  · simpa only [key] using hJ.integral_prod_left
  · rw [← hΘ.map_eq, integral_map hΘ.measurable.aemeasurable (hΘ.map_eq.symm ▸ hI.aestronglyMeasurable)]
    simp only [← key]
    exact integral_prod _ hJ
end GlobalTheory.FunObj
