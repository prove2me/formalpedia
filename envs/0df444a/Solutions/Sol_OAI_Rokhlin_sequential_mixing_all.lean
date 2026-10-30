-- Prove2me | solution 1 for OAI.Rokhlin.sequential_mixing_all
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T07:01:50.989975+00:00
-- url     : https://prove2.me/submissions/0d737021-9f26-42ba-92ae-54f4c9905ba7

import Mathlib
import Definitions.Def_OAIQ3Ro000
import Definitions.Def_OAIQ3Ro001
import Theorems.Thm_OAI_Rokhlin_last_centered_correlation_zero

section
-- module Solutions.OAIQ3_Rok.Compat
attribute [-instance] _root_.OAI.Rokhlin.StrongUnitary.measurableSpace _root_.OAI.Rokhlin.StrongUnitary.topology _root_.OAI.Rokhlin.submodule_completeSpace_inf
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_Tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

section
open MeasureTheory Filter
open scoped Topology BigOperators
variable {Ω : Type*} {I A : Type} [m₀ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
    [retained19 : Fintype A] [retained20 : Nonempty A] [MeasurableSpace A] [retained21 : MeasurableSingletonClass A]
    [retained22 : TopologicalSpace A] [retained23 : DiscreteTopology A] [retained24 : BorelSpace A]

lemma real_integrable_bound (μ : Measure Ω) [IsFiniteMeasure μ] {f : Ω → ℝ}
    (hf : Measurable f) (C : ℝ) (hb : ∀ x, |f x| ≤ C) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable C
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hb x)

end

open MeasureTheory Filter
open scoped Topology BigOperators

end Rokhlin

end

end OAI
end

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

section
open MeasureTheory Filter
open scoped Topology BigOperators
variable {Ω : Type*} [MeasurableSpace Ω]

lemma proper_rectangles_of_induction (μ : Measure Ω) (T : Ω ≃ᵐ Ω) {k : ℕ}
    (ih : ∀ n < k, SequentialMixing μ T n) (d : ℕ → Fin k → ℕ) (hd : Spaced d) :
    ∀ J : Finset (Fin k), J ≠ Finset.univ → ∀ s : J → Set Ω,
      (∀ j, MeasurableSet (s j)) → Tendsto
        (fun r => μ (⋂ j : J, (T^[d r j]) ⁻¹' s j)) atTop
        (𝓝 (∏ j : J, μ (s j))) := by
  intro J hJ s hs
  have hcard : J.card < k := by
    simpa only [Finset.card_univ,Fintype.card_fin] using Finset.card_lt_card
      (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ J,hJ⟩)
  let e : Fin J.card ≃o J := J.orderIsoOfFin rfl
  have he : Spaced (fun r i => d r (e i)) := by
    intro r i j hij
    exact hd r _ _ (e.strictMono hij)
  have ht := ih J.card hcard _ he (fun i => s (e i)) (fun i => hs (e i))
  have hi r : (⋂ i : Fin J.card, (T^[d r (e i)]) ⁻¹' s (e i)) = ⋂ j : J, (T^[d r j]) ⁻¹' s j :=
    e.surjective.iInter_comp (fun j : J => (T^[d r j]) ⁻¹' s j)
  have hp : (∏ i : Fin J.card, μ (s (e i))) = ∏ j : J, μ (s j) := e.toEquiv.prod_comp (fun j : J => μ (s j))
  simpa only [hi,hp] using ht

lemma sequential_zero (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω ≃ᵐ Ω) :
    SequentialMixing μ T 0 := by
  intro d hd A hA
  simp

lemma sequential_one (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω ≃ᵐ Ω)
    (hT : MeasurePreserving T μ μ) : SequentialMixing μ T 1 := by
  intro d hd A hA
  have he r : μ (⋂ i, (T^[d r i]) ⁻¹' A i) = μ (A 0) := by
    have he : (⋂ i : Fin 1, (T^[d r i]) ⁻¹' A i) = (T^[d r 0]) ⁻¹' A 0 := by
      ext x
      simp
    rw [he]
    exact (hT.iterate _).measure_preimage (hA 0).nullMeasurableSet
  simpa only [he,Fin.prod_univ_one] using (tendsto_const_nhds (x := μ (A 0)))

lemma shifted_pair (μ : Measure Ω) (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T μ μ)
    (s t : Set Ω) (hs : MeasurableSet s) (ht : MeasurableSet t) (a b : ℕ) (hab : a ≤ b) :
    μ ((T^[a]) ⁻¹' s ∩ (T^[b]) ⁻¹' t) = μ (s ∩ (T^[b-a]) ⁻¹' t) := by
  have he : (T^[a]) ⁻¹' s ∩ (T^[b]) ⁻¹' t = (T^[a]) ⁻¹' (s ∩ (T^[b-a]) ⁻¹' t) := by
    rw [Set.preimage_inter,←Set.preimage_comp,←Function.iterate_add]
    rw [Nat.sub_add_cancel hab]
  rw [he]
  exact (hT.iterate a).measure_preimage (hs.inter (ht.preimage (T.measurable.iterate _))).nullMeasurableSet

lemma sequential_two (μ : Measure Ω) (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T μ μ)
    (hmix : ∀ s t : Set Ω, MeasurableSet s → MeasurableSet t →
      Tendsto (fun n : ℕ => μ (s ∩ (T^[n]) ⁻¹' t)) atTop (𝓝 (μ s*μ t))) :
    SequentialMixing μ T 2 := by
  intro d hd A hA
  have hb r : d r 0 ≤ d r 1 := by have := hd r 0 1 (by decide); omega
  have hc : Tendsto (fun r => d r 1-d r 0) atTop atTop := by
    apply tendsto_atTop_mono (fun r => Nat.le_of_lt ?_) tendsto_id
    have hh := hd r 0 1 (by decide)
    change r < d r 1-d r 0
    omega
  have ht := (hmix (A 0) (A 1) (hA 0) (hA 1)).comp hc
  change Tendsto (fun r => μ (A 0 ∩ (T^[d r 1-d r 0]) ⁻¹' A 1)) atTop (𝓝 (μ (A 0)*μ (A 1))) at ht
  have he r : (⋂ i : Fin 2, (T^[d r i]) ⁻¹' A i) =
      (T^[d r 0]) ⁻¹' A 0 ∩ (T^[d r 1]) ⁻¹' A 1 := by
    ext x
    simp [Fin.forall_fin_two]
  simpa only [he,Fin.prod_univ_two,shifted_pair μ T hT _ _ (hA 0) (hA 1) _ _ (hb _),Function.comp_apply] using ht
end

section
open MeasureTheory Filter
open scoped Topology BigOperators
variable {Ω I : Type*} [retained25 : MeasurableSpace Ω] [Fintype I]

include retained25 in
lemma setIndicator_bounds (s : Set Ω) (x : Ω) : setIndicator s x ∈ Set.Icc (0:ℝ) 1 := by
  let _ := retained25
  unfold setIndicator
  split_ifs <;> norm_num
lemma setIndicator_measurable {s : Set Ω} (hs : MeasurableSet s) : Measurable (setIndicator s) := by
  exact Measurable.ite hs measurable_const measurable_const
include retained25 in
lemma prod_setIndicator (s : I → Set Ω) (x : Ω) :
    (∏ i, setIndicator (s i) x) = setIndicator (⋂ i, s i) x := by
  let _ := retained25
  classical
  by_cases hx : x ∈ ⋂ i, s i
  · have hmem i : x ∈ s i := Set.mem_iInter.mp hx i
    simp [setIndicator,hx,hmem]
  · have hn : ∃ i, x ∉ s i := by simpa only [Set.mem_iInter,not_forall] using hx
    obtain ⟨i,hi⟩ := hn
    rw [setIndicator,ite_eq_right hx]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [setIndicator,hi])
lemma integral_setIndicator (μ : Measure Ω) {s : Set Ω} (hs : MeasurableSet s) :
    (∫ x, setIndicator s x ∂μ) = (μ s).toReal := by
  have he : setIndicator s = s.indicator (1 : Ω → ℝ) := by
    funext x
    simp [setIndicator,Set.indicator]
  rw [he]
  exact integral_indicator_one hs
lemma integral_prod_setIndicator (μ : Measure Ω) (s : I → Set Ω) (hs : ∀ i, MeasurableSet (s i)) :
    (∫ x, ∏ i, setIndicator (s i) x ∂μ) = (μ (⋂ i, s i)).toReal := by
  simp_rw [prod_setIndicator]
  exact integral_setIndicator μ (MeasurableSet.iInter hs)
include retained25 in
lemma setIndicator_preimage (s : Set Ω) (U : Ω → Ω) (x : Ω) :
    setIndicator s (U x) = setIndicator (U ⁻¹' s) x := by
  let _ := retained25
  rfl
end

section
open MeasureTheory Filter
open scoped Topology BigOperators ENNReal
variable {Ω : Type*} [MeasurableSpace Ω]

lemma sequential_step (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T μ μ)
    (hmix : ∀ s t : Set Ω, MeasurableSet s → MeasurableSet t →
      Tendsto (fun n : ℕ => μ (s ∩ (T^[n]) ⁻¹' t)) atTop (𝓝 (μ s*μ t)))
    {k : ℕ} (hk : 3 ≤ k) (ih : ∀ n < k, SequentialMixing μ T n) : SequentialMixing μ T k := by
  classical
  intro d hd S hS
  let i : Fin k := ⟨k-1,by omega⟩
  have hremote r j (hj : j ≠ i) : d r j+r < d r i := by
    apply hd r j i
    have hne : j.val ≠ k-1 := fun h => hj (Fin.ext h)
    have := j.isLt
    change j.val < k-1
    omega
  let a : Ω → (Fin k → Bool) := fun x j => if x ∈ S j then true else false
  have ha : Measurable a := Measurable.of_eval fun j =>
    Measurable.ite (hS j) measurable_const measurable_const
  let f : Fin k → (Fin k → Bool) → ℝ := fun j z => if z j then 1 else 0
  have hf j z : f j z ∈ Set.Icc (0:ℝ) 1 := by dsimp [f]; split_ifs <;> norm_num
  have hfa j x : f j (a x) = setIndicator (S j) x := by
    by_cases hx : x ∈ S j <;> simp [f,a,setIndicator,hx]
  have hrect := proper_rectangles_of_induction μ T ih d hd
  have ht := last_centered_correlation_zero μ T hT hmix (by simpa using hk) d hrect i hremote a ha f hf
  simp_rw [hfa] at ht
  rw [integral_setIndicator μ (hS i)] at ht
  let J : Finset (Fin k) := Finset.univ.erase i
  have hJ : J ≠ Finset.univ := by
    intro h
    have : i ∈ J := h ▸ Finset.mem_univ i
    exact Finset.notMem_erase i Finset.univ this
  have hp := hrect J hJ (fun j => S j) (fun j => hS j)
  have hpR := (ENNReal.continuousAt_toReal (show (∏ j : J, μ (S j)) ≠ ∞ from ENNReal.prod_ne_top (fun _ _ => measure_ne_top μ _))).tendsto.comp hp
  let w r x := ∏ j ∈ J, setIndicator (S j) ((T^[d r j]) x)
  have hwmeas r : Measurable (w r) := Finset.measurable_prod _ fun j _ =>
    (setIndicator_measurable (hS j)).comp (T.measurable.iterate _)
  have hwb r x : |w r x| ≤ 1 := by
    dsimp [w]
    rw [Finset.abs_prod]
    apply Finset.prod_le_one (fun _ _ => abs_nonneg _)
    intro j hj
    have hh := setIndicator_bounds (S j) ((T^[d r j]) x)
    rw [abs_of_nonneg hh.1]
    exact hh.2
  have hwi r : Integrable (w r) μ := real_integrable_bound μ (hwmeas r) 1 (hwb r)
  have hew r : (∫ x, w r x ∂μ) = (μ (⋂ j : J, (T^[d r j]) ⁻¹' S j)).toReal := by
    have he : w r = fun x => ∏ j : J, setIndicator (S j) ((T^[d r j]) x) := by
      funext x
      exact (Finset.prod_coe_sort J (fun j => setIndicator (S j) ((T^[d r j]) x))).symm
    rw [he]
    simp_rw [setIndicator_preimage]
    exact integral_prod_setIndicator μ _ (fun j => (hS j).preimage (T.measurable.iterate _))
  have hpR' : Tendsto (fun r => ∫ x, w r x ∂μ) atTop (𝓝 (∏ j ∈ J, (μ (S j)).toReal)) := by
    change Tendsto (fun r => (μ (⋂ j : J, (T^[d r j]) ⁻¹' S j)).toReal) atTop
      (𝓝 ((∏ j : J, μ (S j)).toReal)) at hpR
    rw [ENNReal.toReal_prod,Finset.prod_coe_sort J (fun j => (μ (S j)).toReal)] at hpR
    simpa only [hew] using hpR
  have hwhole r : (∫ x, ∏ j, setIndicator (S j) ((T^[d r j]) x) ∂μ) =
      (μ (⋂ j, (T^[d r j]) ⁻¹' S j)).toReal := by
    simp_rw [setIndicator_preimage]
    exact integral_prod_setIndicator μ _ (fun j => (hS j).preimage (T.measurable.iterate _))
  have hsplit r : (∫ x, (setIndicator (S i) ((T^[d r i]) x)-(μ (S i)).toReal)*w r x ∂μ) =
      (μ (⋂ j, (T^[d r j]) ⁻¹' S j)).toReal - (μ (S i)).toReal*(∫ x, w r x ∂μ) := by
    have hi : Integrable (fun x => setIndicator (S i) ((T^[d r i]) x)*w r x) μ := by
      apply real_integrable_bound μ (((setIndicator_measurable (hS i)).comp (T.measurable.iterate _)).mul (hwmeas r)) 1
      intro x
      change |setIndicator (S i) ((T^[d r i]) x)*w r x| ≤ 1
      rw [abs_mul]
      apply (fun leftBound rightNonneg rightBound => (mul_le_of_le_one_left rightNonneg leftBound).trans rightBound) _ (abs_nonneg _) (hwb r x)
      have hh := setIndicator_bounds (S i) ((T^[d r i]) x)
      rw [abs_of_nonneg hh.1]
      exact hh.2
    simp_rw [sub_mul]
    rw [integral_sub hi ((hwi r).const_mul _),integral_const_mul]
    congr 1
    rw [←hwhole]
    apply integral_congr_ae
    filter_upwards with x
    exact Finset.mul_prod_erase Finset.univ (fun j => setIndicator (S j) ((T^[d r j]) x)) (Finset.mem_univ i)
  change Tendsto (fun r => ∫ x, (setIndicator (S i) ((T^[d r i]) x)-(μ (S i)).toReal)*w r x ∂μ) atTop (𝓝 0) at ht
  simp_rw [hsplit] at ht
  have hconst : Tendsto (fun _ : ℕ => (μ (S i)).toReal) atTop (𝓝 ((μ (S i)).toReal)) := tendsto_const_nhds
  have hsum := ht.add (hconst.mul hpR')
  change Tendsto (fun r => ((μ (⋂ j, (T^[d r j]) ⁻¹' S j)).toReal -
    (μ (S i)).toReal*(∫ x, w r x ∂μ))+(μ (S i)).toReal*(∫ x, w r x ∂μ)) atTop
    (𝓝 (0+(μ (S i)).toReal*(∏ j ∈ J, (μ (S j)).toReal))) at hsum
  simp only [sub_add_cancel,zero_add] at hsum
  have hprod : (μ (S i)).toReal*(∏ j ∈ J, (μ (S j)).toReal) = (∏ j, μ (S j)).toReal := by
    rw [ENNReal.toReal_prod]
    exact Finset.mul_prod_erase Finset.univ (fun j => (μ (S j)).toReal) (Finset.mem_univ i)
  rw [hprod] at hsum
  exact (ENNReal.tendsto_toReal_iff (fun _ => measure_ne_top μ _) (ENNReal.prod_ne_top (fun _ _ => measure_ne_top μ _))).mp hsum

theorem sequential_mixing_all_oai (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T μ μ)
    (hmix : ∀ s t : Set Ω, MeasurableSet s → MeasurableSet t →
      Tendsto (fun n : ℕ => μ (s ∩ (T^[n]) ⁻¹' t)) atTop (𝓝 (μ s*μ t))) :
    ∀ k, SequentialMixing μ T k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk : 3 ≤ k
    · exact sequential_step μ T hT hmix hk ih
    · interval_cases k
      · exact sequential_zero μ T
      · exact sequential_one μ T hT
      · exact sequential_two μ T hT hmix
end

open MeasureTheory Filter

end Rokhlin

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Rokhlin.sequential_mixing_all_oai.{u_1} := @OAI.Rokhlin.sequential_mixing_all_oai.{u_1}
