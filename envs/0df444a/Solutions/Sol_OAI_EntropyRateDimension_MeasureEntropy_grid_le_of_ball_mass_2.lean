-- Prove2me | solution 2 for OAI.EntropyRateDimension.MeasureEntropy.grid_le_of_ball_mass
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T07:05:33.124786+00:00
-- url     : https://prove2.me/submissions/42641165-e9fc-4d2a-994f-1529ab95c8b7

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/LocalEntropy.lean:L182-L213
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.MeasureEntropy.grid_le_of_ball_mass. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RandomGrid
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Boundary
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TranslationGain
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FairPairs
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ProductLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_GridCoupling
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteRefinement
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_SumsetBound
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WordTypes
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_DigitSumset
import Theorems.Thm_OAI_EntropyRateDimension_FiniteEntropy_entropy_le_log_card
import Theorems.Thm_OAI_EntropyRateDimension_FiniteEntropy_entropy_normalize
import Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_good_labels_card_bound

-- ---- from OAI.MeasureTheory.SelfSimilar.MeasureEntropy ----
namespace OAI

universe uι uα uβ uγ uδ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace MeasureEntropy

theorem entropy_eq_sum {α : Type uα} {β : Type uβ} [MeasurableSpace α] (μ : Measure α)
    (f : α → β) (s : Finset β) (hs : ∀ᵐ x ∂μ, f x ∈ s) :
    entropy μ f = ∑ b ∈ s, Real.negMulLog (mass μ f b) := by
  apply tsum_eq_sum
  intro b hb
  rw [mass_eq_zero_of_ae μ f s hs hb, Real.negMulLog_zero]

theorem label_ae_uniform (μ : Measure ℝ) {B s u : ℝ} (hs : 0 < s)
    (hB : μ (Set.Icc (-B) B)ᶜ = 0) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    ∀ᵐ x ∂μ, label s u x ∈ Finset.Icc ⌊-B/s⌋ ⌊B/s+1⌋ := by
  filter_upwards [label_ae_finite μ hs hB] with x hx
  obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hx
  exact Finset.mem_Icc.mpr ⟨(Int.floor_le_floor (by linarith [hu.1] : -B/s ≤ -B/s+u)).trans hlo,
    hhi.trans (Int.floor_le_floor (by linarith [hu.2] : B/s+u ≤ B/s+1))⟩

end MeasureEntropy
end EntropyRateDimension
end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.LocalEntropy ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

universe uι uα uβ

open scoped BigOperators ENNReal
open MeasureTheory

namespace EntropyRateDimension

namespace FiniteEntropy

theorem entropy_le_mass_log_card {α : Type uα} (s : Finset α) (p : α → ℝ)
    (hp : ∀ a ∈ s, 0 ≤ p a) :
    entropy s p ≤ Real.negMulLog (∑ a ∈ s, p a)+
      (∑ a ∈ s, p a)*Real.log (max 1 (s.card : ℝ)) := by
  let P := ∑ a ∈ s, p a
  have hP : 0 ≤ P := Finset.sum_nonneg hp
  rw [entropy_normalize s p hp]
  change Real.negMulLog P+P*entropy s (fun a => p a/P) ≤
    Real.negMulLog P+P*Real.log (max 1 (s.card : ℝ))
  rcases eq_or_lt_of_le hP with he | he
  · simp only [← he,zero_mul,add_zero,le_refl]
  have hs : 0 < s.card := Finset.card_pos.mpr (by
    by_contra h
    have hse : s=∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp only [P,hse,Finset.sum_empty] at he
    exact lt_irrefl _ he)
  have hh := entropy_le_log_card s (fun a => p a/P)
    (fun a ha => div_nonneg (hp a ha) hP) (by rw [← Finset.sum_div]; exact div_self he.ne')
  have hcard : max 1 (s.card : ℝ)=(s.card : ℝ) := max_eq_right (by exact_mod_cast hs)
  rw [hcard]
  exact add_le_add_right (mul_le_mul_of_nonneg_left hh hP) _

theorem entropy_split_bound {α : Type uα} [DecidableEq α] (s a : Finset α)
    (p : α → ℝ) (ha : a ⊆ s) (hp : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∑ i ∈ s, p i=1) :
    entropy s p ≤ Real.log 2+Real.log (max 1 (a.card : ℝ))+
      (∑ i ∈ s\a, p i)*Real.log (max 1 (s.card : ℝ)) := by
  classical
  let P := ∑ i ∈ a, p i
  let Q := ∑ i ∈ s\a, p i
  have hP : 0 ≤ P := Finset.sum_nonneg (fun i hi => hp i (ha hi))
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun i hi => hp i (Finset.mem_sdiff.mp hi).1)
  have hPQ : P+Q=1 := by
    change (∑ i ∈ a, p i)+(∑ i ∈ s\a, p i)=1
    rw [add_comm,Finset.sum_sdiff ha,hp1]
  have hPa := entropy_le_mass_log_card a p (fun i hi => hp i (ha hi))
  have hQb := entropy_le_mass_log_card (s\a) p (fun i hi => hp i (Finset.mem_sdiff.mp hi).1)
  have hnum := entropy_le_log_card (Finset.univ : Finset (Fin 2))
    (fun i => if i=0 then P else Q) (by intro i _; split <;> assumption)
    (by simpa [Fin.sum_univ_two] using hPQ)
  have hn : Real.negMulLog P+Real.negMulLog Q ≤ Real.log 2 := by
    simpa [entropy,Fin.sum_univ_two] using hnum
  have hlogA : 0 ≤ Real.log (max 1 (a.card : ℝ)) := Real.log_nonneg (le_max_left _ _)
  have hlogB : Real.log (max 1 ((s\a).card : ℝ)) ≤ Real.log (max 1 (s.card : ℝ)) := by
    apply Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
    exact max_le_max_left 1 (by exact_mod_cast Finset.card_le_card (Finset.sdiff_subset (s := s) (t := a)))
  have he : entropy s p=entropy a p+entropy (s\a) p := by
    unfold entropy
    rw [add_comm,Finset.sum_sdiff ha]
  rw [he]
  change entropy a p ≤ Real.negMulLog P+P*_ at hPa
  change entropy (s\a) p ≤ Real.negMulLog Q+Q*_ at hQb
  change _ ≤ Real.log 2+_+Q*_
  nlinarith [mul_le_mul_of_nonneg_left hlogB hQ,mul_nonneg hQ hlogA]

end FiniteEntropy

namespace MeasureEntropy

theorem entropy_subset_bound {α : Type uα} {β : Type uβ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] [DecidableEq β]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → β) (hf : Measurable f)
    (s a : Finset β) (ha : a ⊆ s) (hs : ∀ᵐ x ∂μ, f x ∈ s) {η : ℝ}
    (hη : μ.real {x | f x ∉ a} ≤ η) :
    entropy μ f ≤ Real.log 2+Real.log (max 1 (a.card : ℝ))+
      η*Real.log (max 1 (s.card : ℝ)) := by
  have hh := FiniteEntropy.entropy_split_bound s a (mass μ f) ha
    (fun i _ => mass_nonneg μ f i) (mass_sum μ f hf s hs)
  have hm : ∑ i ∈ s\a, mass μ f i = μ.real {x | f x ∉ a} := by
    have hd : (↑(s\a) : Set β).PairwiseDisjoint (fun b => {x | f x=b}) := by
      intro b _ c _ hbc
      exact Set.disjoint_left.mpr (fun _ hx hy => hbc (hx.symm.trans hy))
    have hie : (⋃ b ∈ s\a, {x | f x=b}) = {x | f x ∈ s\a} := by
      ext x
      simp only [Set.mem_iUnion,Set.mem_ofPred_eq]
      constructor
      · rintro ⟨b,hb,hxb⟩
        exact hxb ▸ hb
      · intro hx
        exact ⟨f x,hx,rfl⟩
    have he : (⋃ b ∈ s\a, {x | f x=b}) =ᵐ[μ] {x | f x ∉ a} := by
      rw [hie]
      filter_upwards [hs] with x hx
      apply propext
      show f x ∈ s \ a ↔ f x ∉ a
      simp only [Finset.mem_sdiff,hx,true_and]
    unfold mass
    rw [← measureReal_biUnion_finset (μ := μ) hd (fun b _ => hf (measurableSet_singleton b))]
    exact measureReal_congr he
  rw [entropy_eq_sum μ f s hs]
  rw [hm] at hh
  exact hh.trans (add_le_add_right (mul_le_mul_of_nonneg_right hη
    (Real.log_nonneg (le_max_left _ _))) _)

theorem grid_le_of_ball_mass (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {B s u q η : ℝ} (hs : 0 < s) (hq : 0 < q)
    (hB : μ (Set.Icc (-B) B)ᶜ = 0) (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (E : Set ℝ) (hη : μ.real Eᶜ ≤ η)
    (hball : ∀ x ∈ E, q ≤ μ.real (Metric.ball x (s/2))) :
    grid μ s u ≤ Real.log 2+Real.log (max 1 (3/q))+
      η*Real.log (max 1 ((Finset.Icc ⌊-B/s⌋ ⌊B/s+1⌋).card : ℝ)) := by
  classical
  let t := Finset.Icc ⌊-B/s⌋ ⌊B/s+1⌋
  let a := t.filter (fun i => ∃ x ∈ E, label s u x=i)
  have ha : a ⊆ t := Finset.filter_subset _ _
  have has : ∀ i ∈ a, ∃ x ∈ E, label s u x=i := fun i hi => (Finset.mem_filter.mp hi).2
  let x : ℤ → ℝ := fun i => if hi : i ∈ a then (has i hi).choose else 0
  have hx : ∀ i ∈ a, x i ∈ E ∧ label s u (x i)=i := by
    intro i hi
    dsimp only [x]
    rw [dite_eq_left hi]
    exact (has i hi).choose_spec
  have hcard := good_labels_card_bound μ hs a x
    (fun i hi => (hx i hi).2) (fun i hi => hball _ (hx i hi).1)
  have hm : μ.real {z | label s u z ∉ a} ≤ η := by
    have hae : {z | label s u z ∉ a} ≤ᵐ[μ] Eᶜ := by
      filter_upwards [label_ae_uniform μ hs hB hu] with z hz hza
      intro hzE
      exact hza (Finset.mem_filter.mpr ⟨hz,⟨z,hzE,rfl⟩⟩)
    exact (ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hae)).trans hη
  have hh := entropy_subset_bound μ (label s u) (label_measurable s u) t a ha
    (label_ae_uniform μ hs hB hu) hm
  have hlog : Real.log (max 1 (a.card : ℝ)) ≤ Real.log (max 1 (3/q)) := by
    apply Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
    exact max_le_max_left _ ((le_div_iff₀ hq).mpr hcard)
  exact hh.trans (by dsimp only [t]; linarith)

end MeasureEntropy
end EntropyRateDimension

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.MeasureEntropy
open scoped BigOperators ENNReal
open MeasureTheory


theorem solution : type_of% @_root_.OAI.EntropyRateDimension.MeasureEntropy.grid_le_of_ball_mass := @_root_.OAI.EntropyRateDimension.MeasureEntropy.grid_le_of_ball_mass
