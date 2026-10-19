-- Prove2me | solution 2 for OAI.EntropyRateDimension.MeasureEntropy.mass_fairShift
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T06:08:09.681989+00:00
-- url     : https://prove2.me/submissions/f8c031db-7452-40ff-8972-0ea37d467f6f

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/MeasureEntropy.lean:L800-L821
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.MeasureEntropy.mass_fairShift. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy

-- ---- from OAI.MeasureTheory.SelfSimilar.MeasureEntropy ----
namespace OAI

universe uι uα uβ uγ uδ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace MeasureEntropy

theorem mass_map {α : Type uα} {β : Type uβ} {γ : Type uγ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSingletonClass γ]
    (μ : Measure α) (f : α → β) (hf : Measurable f) (g : β → γ) (hg : Measurable g) (c : γ) :
    mass (μ.map f) g c = mass μ (g ∘ f) c := by
  unfold mass Measure.real
  change ((μ.map f) (g ⁻¹' {c})).toReal = _
  rw [Measure.map_apply hf ((measurableSet_singleton c).preimage hg)]
  rfl

theorem mass_mixture {ι : Type uι} {α : Type uα} {β : Type uβ} [Fintype ι] [MeasurableSpace α]
    (μ : Measure α) (ν : ι → Measure α) [∀ i, IsFiniteMeasure (ν i)] (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hm : μ = ∑ i, ENNReal.ofReal (w i) • ν i) (f : α → β) (b : β) :
    mass μ f b = ∑ i, w i*mass (ν i) f b := by
  unfold mass
  rw [hm]
  simp only [Measure.real_def, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    smul_eq_mul]
  rw [ENNReal.toReal_sum (fun i _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))]
  apply Finset.sum_congr rfl
  intro i _
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hw i)]

theorem label_add_scale {s : ℝ} (hs : s ≠ 0) (u x : ℝ) :
    label s u (x+s) = label s u x+1 := by
  dsimp only [label]
  rw [add_div, div_self hs]
  convert Int.floor_add_one (x/s+u) using 1
  congr 1
  ring

theorem mass_fairShift (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {s : ℝ} (hs : 0 < s) (u : ℝ) (j : ℤ) :
    mass (fairShift μ s) (label s u) j =
      (mass μ (label s u) j+mass μ (label s u) (j-1))/2 := by
  have hi : ∀ i : Fin 2, IsProbabilityMeasure (μ.map (fun x => x+(i : ℝ)*s)) :=
    fun i => (Measure.isProbabilityMeasure_map_iff (measurable_id.add_const _).aemeasurable).2 inferInstance
  let := hi
  rw [mass_mixture (fairShift μ s) _ (fun _ : Fin 2 => 1/2) (by intro; positivity) rfl,
    Fin.sum_univ_two]
  simp only [Fin.val_zero, Nat.cast_zero, zero_mul, add_zero, Fin.val_one,
    Nat.cast_one, one_mul]
  rw [mass_map μ (fun x => x) measurable_id (label s u) (label_measurable s u),
    mass_map μ (fun x => x+s) (measurable_id.add_const s) (label s u) (label_measurable s u)]
  have he : mass μ ((label s u) ∘ (fun x => x+s)) j = mass μ (label s u) (j-1) := by
    unfold mass
    congr 1
    ext x
    simp only [Set.mem_ofPred_eq, Function.comp_apply, label_add_scale hs.ne']
    omega
  rw [he]
  change (1/2)*mass μ (label s u) j+(1/2)*mass μ (label s u) (j-1) = _
  ring

end MeasureEntropy
end EntropyRateDimension
end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.MeasureEntropy
open scoped BigOperators ENNReal
open MeasureTheory


theorem solution : type_of% @_root_.OAI.EntropyRateDimension.MeasureEntropy.mass_fairShift := @_root_.OAI.EntropyRateDimension.MeasureEntropy.mass_fairShift
