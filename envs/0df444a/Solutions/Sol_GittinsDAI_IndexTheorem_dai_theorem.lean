-- Prove2me | solution 1 for GittinsDAI.IndexTheorem.dai_theorem
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T17:59:29.310551+00:00
-- url     : https://prove2.me/submissions/e345394f-916f-44a3-a7a6-2e1685944a04
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_GittinsIndex
import Definitions.Def_AllocationIndices_Index
import Theorems.Thm_BanditAlgorithm_gittins_index_theorem
import Theorems.Thm_GittinsDAI_IndexTheorem_dai_theorem_only_if

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace GittinsDAIIfAux

variable {k : ℕ} {S : Type*} [MeasurableSpace S]

/-- the argmax set -/
def amax (g : S → ℝ) (y : Fin k → S) : Set (Fin k) := {a | ∀ j, g (y j) ≤ g (y a)}

open Classical in
lemma amax_nonempty [Nonempty (Fin k)] (g : S → ℝ) (y : Fin k → S) :
    (Finset.univ.filter (fun a => a ∈ amax g y)).Nonempty := by
  obtain ⟨a, -, ha⟩ := Finset.exists_max_image Finset.univ (fun a => g (y a)) Finset.univ_nonempty
  exact ⟨a, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun j => ha j (Finset.mem_univ _)⟩⟩

open Classical in
noncomputable def amaxChoice [Nonempty (Fin k)] (g : S → ℝ) (y : Fin k → S) : Fin k :=
  (Finset.univ.filter (fun a => a ∈ amax g y)).min' (amax_nonempty g y)

lemma amaxChoice_mem [Nonempty (Fin k)] (g : S → ℝ) (y : Fin k → S) :
    amaxChoice g y ∈ amax g y := by
  classical
  unfold amaxChoice
  exact (Finset.mem_filter.1 (Finset.min'_mem _ _)).2

lemma measurableSet_amax_mem {X : Type*} [MeasurableSpace X] {g : S → ℝ} (hg : Measurable g)
    {F : X → Fin k → S} (hF : Measurable F) (a : Fin k) :
    MeasurableSet {p | a ∈ amax g (F p)} := by
  have : {p | a ∈ amax g (F p)} = ⋂ j, {p | g (F p j) ≤ g (F p a)} := by
    ext p; simp [amax]
  rw [this]
  exact MeasurableSet.iInter fun j => measurableSet_le
    (hg.comp ((measurable_pi_apply j).comp hF)) (hg.comp ((measurable_pi_apply a).comp hF))

lemma measurable_amaxChoice [Nonempty (Fin k)] {g : S → ℝ} (hg : Measurable g) :
    Measurable (amaxChoice (k := k) g) := by
  classical
  refine measurable_to_countable' fun a => ?_
  have : amaxChoice (k := k) g ⁻¹' {a} =
      {y | a ∈ amax g y} ∩ ⋂ b ∈ Finset.univ.filter (fun b : Fin k => b < a),
        {y | b ∈ amax g y}ᶜ := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_setOf_eq,
      Set.mem_iInter, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_compl_iff]
    constructor
    · rintro rfl
      refine ⟨amaxChoice_mem g y, fun b hb hbm => ?_⟩
      have : amaxChoice g y ≤ b := by
        unfold amaxChoice
        exact Finset.min'_le _ b (Finset.mem_filter.2 ⟨Finset.mem_univ _, by convert hbm⟩)
      exact absurd hb (not_lt.2 this)
    · rintro ⟨ha, hb⟩
      have h1 : amaxChoice g y ≤ a := by
        unfold amaxChoice
        exact Finset.min'_le _ a (Finset.mem_filter.2 ⟨Finset.mem_univ _, by convert ha⟩)
      rcases h1.lt_or_eq with h1 | h1
      · exact absurd (amaxChoice_mem g y) (hb _ h1)
      · exact h1
  rw [this]
  refine (measurableSet_amax_mem hg measurable_id a).inter ?_
  refine Finset.measurableSet_biInter _ fun b _ => ?_
  exact (measurableSet_amax_mem hg measurable_id b).compl

lemma measurable_select_amax {g : S → ℝ} (hg : Measurable g) (π : MarkovBanditPolicy k S)
    (n : ℕ) : Measurable fun h : MarkovBanditHistory k S n => (π.select n) h (amax g h.2) := by
  have hT : MeasurableSet {p : MarkovBanditHistory k S n × Fin k | p.2 ∈ amax g p.1.2} := by
    have : {p : MarkovBanditHistory k S n × Fin k | p.2 ∈ amax g p.1.2} =
        ⋂ j, {p | g (p.1.2 j) ≤ g (p.1.2 p.2)} := by
      ext p; simp [amax]
    rw [this]
    refine MeasurableSet.iInter fun j => measurableSet_le ?_ ?_
    · have h1 : Measurable fun p : MarkovBanditHistory k S n × Fin k => p.1.2 j := by fun_prop
      exact hg.comp h1
    · exact hg.comp measurable_currentArmState
  exact Kernel.measurable_kernel_prodMk_left hT

/-- The set of histories at which `π` selects an argmax arm with probability one. -/
def goodSet (g : S → ℝ) (π : MarkovBanditPolicy k S) (n : ℕ) :
    Set (MarkovBanditHistory k S n) := {h | (π.select n) h (amax g h.2) = 1}

lemma measurableSet_goodSet {g : S → ℝ} (hg : Measurable g) (π : MarkovBanditPolicy k S)
    (n : ℕ) : MeasurableSet (goodSet g π n) :=
  measurable_select_amax hg π n (measurableSet_singleton 1)

open Classical in
noncomputable def modPolicy [Nonempty (Fin k)] {g : S → ℝ} (hg : Measurable g)
    (π : MarkovBanditPolicy k S) : MarkovBanditPolicy k S where
  select n := Kernel.piecewise (measurableSet_goodSet hg π n) (π.select n)
    (Kernel.deterministic (fun h => amaxChoice g h.2)
      ((measurable_amaxChoice hg).comp measurable_snd))
  markov n := by infer_instance

lemma modPolicy_select_of_mem [Nonempty (Fin k)] {g : S → ℝ} (hg : Measurable g)
    (π : MarkovBanditPolicy k S) (n : ℕ) (h : MarkovBanditHistory k S n)
    (hh : h ∈ goodSet g π n) : (modPolicy hg π).select n h = π.select n h := by
  classical
  simp only [modPolicy]
  rw [Kernel.piecewise_apply, if_pos hh]

lemma modPolicy_amax [Nonempty (Fin k)] {g : S → ℝ} (hg : Measurable g)
    (π : MarkovBanditPolicy k S) (n : ℕ) (h : MarkovBanditHistory k S n) :
    (modPolicy hg π).select n h (amax g h.2) = 1 := by
  classical
  by_cases hh : h ∈ goodSet g π n
  · rw [modPolicy_select_of_mem hg π n h hh]; exact hh
  · simp only [modPolicy]
    rw [Kernel.piecewise_apply, if_neg hh, Kernel.deterministic_apply,
      Measure.dirac_apply_of_mem (amaxChoice_mem g h.2)]

lemma measure_eq [Nonempty (Fin k)] (P : Kernel S S) [IsMarkovKernel P] {g : S → ℝ}
    (hg : Measurable g) (π : MarkovBanditPolicy k S) (x : Fin k → S)
    (hae : ∀ n : ℕ, ∀ᵐ h ∂(markovBanditMeasure P π x n), (π.select n) h (amax g h.2) = 1) :
    ∀ n, markovBanditMeasure P (modPolicy hg π) x n = markovBanditMeasure P π x n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [markovBanditMeasure, markovBanditMeasure, ih]
    congr 1
    refine Measure.compProd_congr ?_
    filter_upwards [hae n] with h hh
    ext s hs
    simp only [markovBanditStepKernel]
    rw [Kernel.compProd_apply hs, Kernel.compProd_apply hs,
      modPolicy_select_of_mem hg π n h hh]

end GittinsDAIIfAux

open GittinsDAIIfAux in
theorem dai_if {k : ℕ} {S : Type*} [MeasurableSpace S] [StandardBorelSpace S]
    (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ} (hr : Measurable r) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hint : DiscountedRewardIntegrable P r α)
    (hg : Measurable (gittinsIndex P r α))
    (π : MarkovBanditPolicy k S) (x : Fin k → S) :
    (∀ n : ℕ, ∀ᵐ h ∂(markovBanditMeasure P π x n),
        (π.select n) h {a | ∀ j, gittinsIndex P r α (h.2 j) ≤ gittinsIndex P r α (h.2 a)} = 1) →
    markovBanditDiscountedValue P r α π x =
        ⨆ π' : MarkovBanditPolicy k S, markovBanditDiscountedValue P r α π' x := by
  intro hae
  have : Nonempty (Fin k) :=
    nonempty_of_isProbabilityMeasure ((π.select 0) ((fun t => t.elim0, x) :
      MarkovBanditHistory k S 0))
  have hmeas := measure_eq P hg π x hae
  have hval : markovBanditDiscountedValue P r α (modPolicy hg π) x =
      markovBanditDiscountedValue P r α π x := by
    simp only [markovBanditDiscountedValue, markovBanditRoundReward, hmeas]
  rw [← hval]
  exact BanditAlgorithm.gittins_index_theorem P hr hα0 hα1 hint _
    (fun n h => modPolicy_amax hg π n h) x

theorem solution {k : ℕ} {S : Type*} [MeasurableSpace S] [StandardBorelSpace S]
    (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ} (hr : Measurable r) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hint : DiscountedRewardIntegrable P r α)
    (hg : Measurable (gittinsIndex P r α))
    (π : MarkovBanditPolicy k S) (x : Fin k → S) :
    markovBanditDiscountedValue P r α π x =
        ⨆ π' : MarkovBanditPolicy k S, markovBanditDiscountedValue P r α π' x ↔
      ∀ n : ℕ, ∀ᵐ h ∂(markovBanditMeasure P π x n),
        (π.select n) h {a | ∀ j, gittinsIndex P r α (h.2 j) ≤ gittinsIndex P r α (h.2 a)} = 1 :=
  ⟨fun hopt => GittinsDAI.IndexTheorem.dai_theorem_only_if P hr hα0 hα1 hint hg π x hopt,
    dai_if P hr hα0 hα1 hint hg π x⟩
