-- Prove2me | solution 1 for KMNewsvendor.optional_skipping_slln
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-10-28T08:52:34.973621+00:00
-- url     : https://prove2.me/submissions/4720c208-7f76-4826-bc52-ef55bafbf12f

import Mathlib

namespace Prove2SwarmSubmission
open MeasureTheory ProbabilityTheory Filter Finset Topology

namespace BacklogCuratorOptionalSkipping

def selectedCount (s : ℕ → Bool) (T : ℕ) : ℕ :=
  ((range T).filter (fun t => s t = true)).card

noncomputable def selectedIndex (s : ℕ → Bool) (k : ℕ) : ℕ :=
  Nat.nth (fun t => s t = true) k

def selectedSum (s : ℕ → Bool) (a : ℕ → ℝ) (T : ℕ) : ℝ :=
  ∑ t ∈ range T, if s t = true then a t else 0

noncomputable def skippedProcess {Ω : Type*} (D : ℕ → Ω → ℝ)
    (ξ : ℕ → Ω → Bool) (k : ℕ) (ω : Ω) : ℝ :=
  D (selectedIndex (fun t => ξ t ω) k) ω

end BacklogCuratorOptionalSkipping

namespace BacklogCuratorOptionalSkipping

/-- A genuine kth selection at time t. Unlike the default value of Nat.nth,
this event only inspects the selector up through time t. -/
def selectionHit {Ω : Type*} (ξ : ℕ → Ω → Bool) (k t : ℕ) : Set Ω :=
  {ω | ξ t ω = true ∧ selectedCount (fun i => ξ i ω) t = k}

theorem bridge_selectedCount_eq_nat_count (s : ℕ → Bool) (t : ℕ) :
    selectedCount s t = Nat.count (fun i => s i = true) t :=
  (Nat.count_eq_card_filter_range (fun i => s i = true) t).symm

/-- Rank inversion at a selected time needs no global infinity hypothesis. -/
theorem bridge_selectedIndex_eq_of_hit (s : ℕ → Bool) (k t : ℕ)
    (hs : s t = true) (hcount : selectedCount s t = k) :
    selectedIndex s k = t := by
  have hc : Nat.count (fun i => s i = true) t = k :=
    (Nat.count_eq_card_filter_range (fun i => s i = true) t).trans hcount
  change Nat.nth (fun i => s i = true) k = t
  rw [← hc]
  exact Nat.nth_count hs

theorem bridge_selectedIndex_lt_of_count (s : ℕ → Bool) {i t : ℕ}
    (hi : i < selectedCount s t) : selectedIndex s i < t := by
  change Nat.nth (fun j => s j = true) i < t
  apply Nat.nth_lt_of_lt_count
  rw [← bridge_selectedCount_eq_nat_count]
  exact hi

/-- A rank below the finite prefix count exists and has precisely that rank,
even when only finitely many points are ever selected. -/
theorem bridge_selectedIndex_hit_of_lt_count (s : ℕ → Bool) {i t : ℕ}
    (hi : i < selectedCount s t) :
    s (selectedIndex s i) = true ∧ selectedCount s (selectedIndex s i) = i := by
  let p : ℕ → Prop := fun j => s j = true
  have hi' : i < Nat.count p t := by
    rw [← bridge_selectedCount_eq_nat_count]
    exact hi
  have hvalid : ∀ hf : (Set.ofPred p).Finite, i < hf.toFinset.card :=
    fun hf => hi'.trans_le (Nat.count_le_card hf t)
  refine ⟨Nat.nth_mem i hvalid, ?_⟩
  rw [bridge_selectedCount_eq_nat_count]
  exact Nat.count_nth hvalid

/-- Before a kth selection, every earlier selected observation lies in the
strict past. This remains true on finite selected paths whenever the hit exists. -/
theorem bridge_previousIndex_lt_on_hit {Ω : Type*} (ξ : ℕ → Ω → Bool)
    {i k t : ℕ} {ω : Ω} (hi : i < k) (hω : ω ∈ selectionHit ξ k t) :
    selectedIndex (fun j => ξ j ω) i < t := by
  apply bridge_selectedIndex_lt_of_count
  rw [hω.2]
  exact hi

theorem bridge_selectedIndex_on_hit {Ω : Type*} (ξ : ℕ → Ω → Bool)
    {k t : ℕ} {ω : Ω} (hω : ω ∈ selectionHit ξ k t) :
    selectedIndex (fun j => ξ j ω) k = t :=
  bridge_selectedIndex_eq_of_hit _ k t hω.1 hω.2

/-- Genuine kth-hit events form a disjoint family, including on bad paths. -/
theorem bridge_selectionHit_pairwiseDisjoint {Ω : Type*}
    (ξ : ℕ → Ω → Bool) (k : ℕ) :
    Pairwise (fun t u => Disjoint (selectionHit ξ k t) (selectionHit ξ k u)) := by
  intro t u htu
  apply Set.disjoint_left.mpr
  intro ω ht hu
  exact htu ((bridge_selectedIndex_on_hit ξ ht).symm.trans
    (bridge_selectedIndex_on_hit ξ hu))

theorem bridge_skippedProcess_on_hit {Ω : Type*} (D : ℕ → Ω → ℝ)
    (ξ : ℕ → Ω → Bool) {k t : ℕ} {ω : Ω}
    (hω : ω ∈ selectionHit ξ k t) : skippedProcess D ξ k ω = D t ω := by
  change D (selectedIndex (fun j => ξ j ω) k) ω = D t ω
  rw [bridge_selectedIndex_on_hit ξ hω]

/-- On a later genuine hit, each earlier selected value is a finite masked
strict-past sum. This is the pointwise bridge used for fresh-demand independence. -/
theorem bridge_previous_skipped_eq_masked_sum {Ω : Type*} (D : ℕ → Ω → ℝ)
    (ξ : ℕ → Ω → Bool) {i k t : ℕ} {ω : Ω}
    (hi : i < k) (hω : ω ∈ selectionHit ξ k t) :
    skippedProcess D ξ i ω =
      ∑ s ∈ range t,
        if ξ s ω = true ∧ selectedCount (fun j => ξ j ω) s = i
          then D s ω else 0 := by
  classical
  let r : ℕ := selectedIndex (fun j => ξ j ω) i
  have hrlt : r < t := bridge_previousIndex_lt_on_hit ξ hi hω
  have hicount : i < selectedCount (fun j => ξ j ω) t := by
    rw [hω.2]
    exact hi
  have hrhit : ξ r ω = true ∧ selectedCount (fun j => ξ j ω) r = i :=
    bridge_selectedIndex_hit_of_lt_count _ hicount
  change D r ω = _
  symm
  rw [Finset.sum_eq_single r]
  · exact if_pos hrhit
  · intro s _hs hsr
    by_cases hs : ξ s ω = true ∧ selectedCount (fun j => ξ j ω) s = i
    · have hrs : r = s := bridge_selectedIndex_eq_of_hit _ i s hs.1 hs.2
      exact (hsr hrs.symm).elim
    · exact if_neg hs
  · intro hr
    exact (hr (Finset.mem_range.mpr hrlt)).elim

theorem bridge_selectionHit_exists_of_infinite (s : ℕ → Bool)
    (hinf : {t : ℕ | s t = true}.Infinite) (k : ℕ) :
    ∃ t, s t = true ∧ selectedCount s t = k := by
  refine ⟨selectedIndex s k, Nat.nth_mem_of_infinite hinf k, ?_⟩
  rw [bridge_selectedCount_eq_nat_count]
  exact Nat.count_nth_of_infinite hinf k

/-- The literal frequent-selection hypothesis gives an infinite selected set. -/
theorem bridge_infinite_of_frequently (s : ℕ → Bool)
    (hfreq : ∃ᶠ t in atTop, s t = true) : {t : ℕ | s t = true}.Infinite := by
  classical
  by_contra h
  have hfin : {t : ℕ | s t = true}.Finite := Set.not_infinite.mp h
  obtain ⟨b, hb⟩ := hfin.bddAbove
  have hnone : ∀ᶠ t : ℕ in atTop, ¬s t = true := by
    refine eventually_atTop.mpr ⟨b + 1, ?_⟩
    intro t ht hs
    have htb : t ≤ b := hb hs
    omega
  exact hfreq hnone

/-- Genuine-hit events cover almost surely under the exact frozen hypothesis;
there is no additional global infiniteness premise on every path. -/
theorem bridge_ae_selectionHit_exists {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (ξ : ℕ → Ω → Bool)
    (hinf : ∀ᵐ ω ∂μ, ∃ᶠ t in atTop, ξ t ω = true) (k : ℕ) :
    ∀ᵐ ω ∂μ, ∃ t, ω ∈ selectionHit ξ k t := by
  filter_upwards [hinf] with ω hω
  exact bridge_selectionHit_exists_of_infinite (fun t => ξ t ω)
    (bridge_infinite_of_frequently _ hω) k

end BacklogCuratorOptionalSkipping

namespace BacklogCuratorOptionalSkipping.SelectionBridge

/-- Exactly the sigma-algebra generated by demands with index strictly below `t`. -/
@[instance_reducible] noncomputable def demandPast {Ω : Type*} (D : ℕ → Ω → ℝ) (t : ℕ) : MeasurableSpace Ω :=
  ⨆ n ∈ Set.Iio t, MeasurableSpace.comap (D n) inferInstance

def demandPrefix {Ω : Type*} (D : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : Fin t → ℝ :=
  fun i => D i ω

def selectionEvent {Ω : Type*} (ξ : ℕ → Ω → Bool) (k t : ℕ) : Set Ω :=
  {ω | ξ t ω = true ∧ selectedCount (fun n => ξ n ω) t = k}

/-- Count the true bits of a finite prefix by extending it with false bits. -/
def prefixCount (t : ℕ) (s : Fin t → Bool) : ℕ :=
  selectedCount (fun n => if h : n < t then s ⟨n, h⟩ else false) t

/-- The earlier `i`th selected value, truncated before `t`; it is zero if absent. -/
def earlierSelectedValue {Ω : Type*} (D : ℕ → Ω → ℝ)
    (ξ : ℕ → Ω → Bool) (i t : ℕ) (ω : Ω) : ℝ :=
  ∑ s ∈ range t,
    if ξ s ω = true ∧ selectedCount (fun n => ξ n ω) s = i then D s ω else 0

theorem selectedCount_eq_prefixCount (s : ℕ → Bool) (t : ℕ) :
    selectedCount s t = prefixCount t (fun i => s i) := by
  unfold prefixCount selectedCount
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro n hn
  simp only [dif_pos (Finset.mem_range.mp hn)]

theorem demandPast_mono {Ω : Type*} (D : ℕ → Ω → ℝ) {s t : ℕ} (hst : s ≤ t) :
    demandPast D s ≤ demandPast D t := by
  unfold demandPast
  refine iSup_le fun n => iSup_le fun hn => ?_
  exact le_iSup_of_le n (le_iSup_of_le (lt_of_lt_of_le hn hst) le_rfl)

theorem demandPast_le {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (D : ℕ → Ω → ℝ) (hmeas : ∀ n, Measurable (D n)) (t : ℕ) :
    demandPast D t ≤ mΩ := by
  unfold demandPast
  exact iSup_le fun n => iSup_le fun _hn => (hmeas n).comap_le

theorem measurable_demand_past {Ω : Type*} (D : ℕ → Ω → ℝ)
    (t n : ℕ) (hnt : n < t) : Measurable[demandPast D t] (D n) := by
  apply Measurable.of_comap_le
  exact le_iSup_of_le n (le_iSup_of_le hnt le_rfl)

theorem measurable_demandPrefix_past {Ω : Type*} (D : ℕ → Ω → ℝ) (t : ℕ) :
    Measurable[demandPast D t] (demandPrefix D t) := by
  let : MeasurableSpace Ω := demandPast D t
  exact measurable_pi_iff.mpr fun i => measurable_demand_past D t i i.isLt

/-- No completed or augmented filtration is introduced: this is literal comap equality. -/
theorem demandPast_eq_comap_prefix {Ω : Type*} (D : ℕ → Ω → ℝ) (t : ℕ) :
    demandPast D t = MeasurableSpace.comap (demandPrefix D t) inferInstance := by
  apply le_antisymm
  · unfold demandPast
    refine iSup_le fun n => iSup_le fun hn => ?_
    have hcoord :
        Measurable[MeasurableSpace.comap (demandPrefix D t) inferInstance] (D n) :=
      (measurable_pi_apply (⟨n, hn⟩ : Fin t)).comp (comap_measurable (demandPrefix D t))
    exact hcoord.comap_le
  · exact (measurable_demandPrefix_past D t).comap_le

/-- A predictable selector at time `t` is measurable in the strict demand past. -/
theorem measurable_selector_past {Ω : Type*} (D : ℕ → Ω → ℝ)
    (ξ : ℕ → Ω → Bool)
    (hξ : ∀ t, ∃ g : (Fin t → ℝ) → Bool, Measurable g ∧
      ξ t = fun ω => g (fun i => D i ω)) (t : ℕ) :
    Measurable[demandPast D t] (ξ t) := by
  obtain ⟨g, hg, hfactor⟩ := hξ t
  rw [hfactor]
  exact hg.comp (measurable_demandPrefix_past D t)

theorem measurable_selector_le_past {Ω : Type*} (D : ℕ → Ω → ℝ)
    (ξ : ℕ → Ω → Bool)
    (hξ : ∀ t, ∃ g : (Fin t → ℝ) → Bool, Measurable g ∧
      ξ t = fun ω => g (fun i => D i ω)) (s t : ℕ) (hst : s ≤ t) :
    Measurable[demandPast D t] (ξ s) :=
  (measurable_selector_past D ξ hξ s).mono (demandPast_mono D hst) le_rfl

/-- The exact filtered-range count is measurable, using only a finite Boolean prefix. -/
theorem measurable_selectedCount_past {Ω : Type*} (D : ℕ → Ω → ℝ)
    (ξ : ℕ → Ω → Bool)
    (hξ : ∀ t, ∃ g : (Fin t → ℝ) → Bool, Measurable g ∧
      ξ t = fun ω => g (fun i => D i ω)) (t : ℕ) :
    Measurable[demandPast D t] (fun ω => selectedCount (fun n => ξ n ω) t) := by
  have hbool : Measurable[demandPast D t] (fun ω (i : Fin t) => ξ i ω) := by
    let : MeasurableSpace Ω := demandPast D t
    exact measurable_pi_iff.mpr fun i =>
      measurable_selector_le_past D ξ hξ i t (Nat.le_of_lt i.isLt)
  have hfactor :
      (fun ω => selectedCount (fun n => ξ n ω) t) =
        fun ω => prefixCount t (fun i => ξ i ω) := by
    funext ω
    exact selectedCount_eq_prefixCount (fun n => ξ n ω) t
  rw [hfactor]
  exact (measurable_of_countable (prefixCount t)).comp hbool

theorem measurableSet_selectionEvent_past {Ω : Type*} (D : ℕ → Ω → ℝ)
    (ξ : ℕ → Ω → Bool)
    (hξ : ∀ t, ∃ g : (Fin t → ℝ) → Bool, Measurable g ∧
      ξ t = fun ω => g (fun i => D i ω)) (k t : ℕ) :
    MeasurableSet[demandPast D t] (selectionEvent ξ k t) := by
  have htrue := (measurable_selector_past D ξ hξ t) (measurableSet_singleton true)
  have hcount := (measurable_selectedCount_past D ξ hξ t) (measurableSet_singleton k)
  exact htrue.inter hcount

theorem measurableSet_selectionEvent {Ω : Type*} [MeasurableSpace Ω]
    (D : ℕ → Ω → ℝ) (hmeas : ∀ n, Measurable (D n))
    (ξ : ℕ → Ω → Bool)
    (hξ : ∀ t, ∃ g : (Fin t → ℝ) → Bool, Measurable g ∧
      ξ t = fun ω => g (fun i => D i ω)) (k t : ℕ) :
    MeasurableSet (selectionEvent ξ k t) :=
  (demandPast_le D hmeas t) _ (measurableSet_selectionEvent_past D ξ hξ k t)

/-- Fresh demand is independent of the entire sigma-algebra of the strict past. -/
theorem demand_indep_past {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (D : ℕ → Ω → ℝ) (hmeas : ∀ n, Measurable (D n))
    (hindep : iIndepFun D μ) (t : ℕ) :
    Indep (MeasurableSpace.comap (D t) inferInstance) (demandPast D t) μ := by
  have hdisj : Disjoint ({t} : Set ℕ) (Set.Iio t) := by simp
  have h := indep_iSup_of_disjoint
    (m := fun n : ℕ => MeasurableSpace.comap (D n) inferInstance)
    (fun n => (hmeas n).comap_le) hindep.iIndep hdisj
  refine indep_of_indep_of_le_left h ?_
  exact le_iSup_of_le t
    (le_iSup_of_le (show t ∈ ({t} : Set ℕ) from rfl) le_rfl)

/-- In particular, any finite-prefix observable is independent of the new demand. -/
theorem demand_indepFun_of_past_measurable {Ω β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace β] (μ : Measure Ω)
    (D : ℕ → Ω → ℝ) (hmeas : ∀ n, Measurable (D n))
    (hindep : iIndepFun D μ) (t : ℕ) (Y : Ω → β)
    (hY : Measurable[demandPast D t] Y) : IndepFun (D t) Y μ := by
  rw [IndepFun_iff_Indep]
  exact indep_of_indep_of_le_right (demand_indep_past μ D hmeas hindep t) hY.comap_le

theorem demand_indepFun_prefix {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (D : ℕ → Ω → ℝ) (hmeas : ∀ n, Measurable (D n))
    (hindep : iIndepFun D μ) (t : ℕ) : IndepFun (D t) (demandPrefix D t) μ :=
  demand_indepFun_of_past_measurable μ D hmeas hindep t _
    (measurable_demandPrefix_past D t)

/-- The exact event factorization needed for a countable selection-time partition. -/
theorem demand_past_event_factor {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (D : ℕ → Ω → ℝ) (hmeas : ∀ n, Measurable (D n))
    (hindep : iIndepFun D μ) (t : ℕ) (A : Set ℝ) (hA : MeasurableSet A)
    (B : Set Ω) (hB : MeasurableSet[demandPast D t] B) :
    μ ((D t) ⁻¹' A ∩ B) = μ ((D t) ⁻¹' A) * μ B := by
  exact (Indep_iff _ _ _).1 (demand_indep_past μ D hmeas hindep t) _ _
    ((comap_measurable (D t)) hA) hB

theorem demand_selectionEvent_factor {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (D : ℕ → Ω → ℝ) (hmeas : ∀ n, Measurable (D n))
    (hindep : iIndepFun D μ) (ξ : ℕ → Ω → Bool)
    (hξ : ∀ t, ∃ g : (Fin t → ℝ) → Bool, Measurable g ∧
      ξ t = fun ω => g (fun i => D i ω)) (k t : ℕ)
    (A : Set ℝ) (hA : MeasurableSet A) :
    μ ((D t) ⁻¹' A ∩ selectionEvent ξ k t) =
      μ ((D t) ⁻¹' A) * μ (selectionEvent ξ k t) :=
  demand_past_event_factor μ D hmeas hindep t A hA _
    (measurableSet_selectionEvent_past D ξ hξ k t)

/-- A finite masked earlier selected value is genuinely strict-past measurable. -/
theorem measurable_earlierSelectedValue_past {Ω : Type*} (D : ℕ → Ω → ℝ)
    (ξ : ℕ → Ω → Bool)
    (hξ : ∀ t, ∃ g : (Fin t → ℝ) → Bool, Measurable g ∧
      ξ t = fun ω => g (fun i => D i ω)) (i t : ℕ) :
    Measurable[demandPast D t] (earlierSelectedValue D ξ i t) := by
  unfold earlierSelectedValue
  refine Finset.measurable_sum (range t) ?_
  intro s hs
  have hst : s < t := Finset.mem_range.mp hs
  have hevent : MeasurableSet[demandPast D t] (selectionEvent ξ i s) :=
    (demandPast_mono D (Nat.le_of_lt hst)) _
      (measurableSet_selectionEvent_past D ξ hξ i s)
  exact Measurable.ite hevent (measurable_demand_past D t s hst) measurable_const

/-- This is an actual measurable finite-prefix representation, not a new hypothesis. -/
theorem earlierSelectedValue_factor_prefix {Ω : Type*} (D : ℕ → Ω → ℝ)
    (ξ : ℕ → Ω → Bool)
    (hξ : ∀ t, ∃ g : (Fin t → ℝ) → Bool, Measurable g ∧
      ξ t = fun ω => g (fun i => D i ω)) (i t : ℕ) :
    ∃ g : (Fin t → ℝ) → ℝ, Measurable g ∧
      earlierSelectedValue D ξ i t = g ∘ demandPrefix D t := by
  have hm := measurable_earlierSelectedValue_past D ξ hξ i t
  rw [demandPast_eq_comap_prefix D t] at hm
  exact hm.exists_eq_measurable_comp

theorem demand_indepFun_earlierSelectedValue {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (D : ℕ → Ω → ℝ) (hmeas : ∀ n, Measurable (D n))
    (hindep : iIndepFun D μ) (ξ : ℕ → Ω → Bool)
    (hξ : ∀ t, ∃ g : (Fin t → ℝ) → Bool, Measurable g ∧
      ξ t = fun ω => g (fun i => D i ω)) (i t : ℕ) :
    IndepFun (D t) (earlierSelectedValue D ξ i t) μ :=
  demand_indepFun_of_past_measurable μ D hmeas hindep t _
    (measurable_earlierSelectedValue_past D ξ hξ i t)

/-- Pointwise reduction to one earlier selected time. Deterministic event uniqueness
and existence are the only premises; no independence assertion is assumed. -/
theorem earlierSelectedValue_eq_of_unique {Ω : Type*}
    (D : ℕ → Ω → ℝ) (ξ : ℕ → Ω → Bool) (i t : ℕ) (ω : Ω)
    (s : ℕ) (hst : s < t) (hevent : ω ∈ selectionEvent ξ i s)
    (hunique : ∀ r ∈ range t, ω ∈ selectionEvent ξ i r → r = s) :
    earlierSelectedValue D ξ i t ω = D s ω := by
  unfold earlierSelectedValue
  rw [Finset.sum_eq_single s]
  · exact if_pos hevent
  · intro r hr hrs
    by_cases h : ω ∈ selectionEvent ξ i r
    · exact False.elim (hrs (hunique r hr h))
    · exact if_neg h
  · intro hs
    exact False.elim (hs (Finset.mem_range.mpr hst))

/-- Adapter for the owner's deterministic Nat.nth characterization. In applications
on E(j,t), i<j supplies exactly these finite-time hypotheses. -/
theorem earlierSelectedValue_eq_skippedProcess_of_rank {Ω : Type*}
    (D : ℕ → Ω → ℝ) (ξ : ℕ → Ω → Bool) (i t : ℕ) (ω : Ω)
    (hnth : selectedIndex (fun n => ξ n ω) i < t)
    (hrank : ∀ r < t, (ω ∈ selectionEvent ξ i r) ↔
      r = selectedIndex (fun n => ξ n ω) i) :
    earlierSelectedValue D ξ i t ω = skippedProcess D ξ i ω := by
  exact earlierSelectedValue_eq_of_unique D ξ i t ω _ hnth
    ((hrank _ hnth).2 rfl)
    (fun r hr he => (hrank r (Finset.mem_range.mp hr)).1 he)

/-- Joint factorization with an earlier selected observation restricted to E(j,t). -/
theorem demand_selectionEvent_earlier_factor {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (D : ℕ → Ω → ℝ) (hmeas : ∀ n, Measurable (D n))
    (hindep : iIndepFun D μ) (ξ : ℕ → Ω → Bool)
    (hξ : ∀ t, ∃ g : (Fin t → ℝ) → Bool, Measurable g ∧
      ξ t = fun ω => g (fun i => D i ω)) (i j t : ℕ)
    (A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    μ ((D t) ⁻¹' A ∩ (selectionEvent ξ j t ∩ (earlierSelectedValue D ξ i t) ⁻¹' B)) =
      μ ((D t) ⁻¹' A) *
        μ (selectionEvent ξ j t ∩ (earlierSelectedValue D ξ i t) ⁻¹' B) := by
  apply demand_past_event_factor μ D hmeas hindep t A hA
  exact (measurableSet_selectionEvent_past D ξ hξ j t).inter
    ((measurable_earlierSelectedValue_past D ξ hξ i t) hB)

end BacklogCuratorOptionalSkipping.SelectionBridge

namespace BacklogCuratorOptionalSkipping

/-- Countable gluing on an a.e. cover. Bad paths are left arbitrary in `Y`;
only its measurable representative is patched by `b0` outside the cover. -/
theorem partition_aemeasurable {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (μ : Measure Ω) (E : ℕ → Set Ω) (X : ℕ → Ω → β) (Y : Ω → β) (b0 : β)
    (hE : ∀ t, MeasurableSet (E t))
    (hcover : ∀ᵐ ω ∂μ, ∃ t, ω ∈ E t)
    (hX : ∀ t, Measurable (X t))
    (hYX : ∀ t ω, ω ∈ E t → Y ω = X t ω) :
    AEMeasurable Y μ := by
  classical
  let C : Set Ω := ⋃ t, E t
  let Y' : Ω → β := fun ω => if ω ∈ C then Y ω else b0
  have hC : MeasurableSet C := MeasurableSet.iUnion hE
  have hpre : ∀ B : Set β,
      Y' ⁻¹' B = (⋃ t, E t ∩ (X t) ⁻¹' B) ∪
        (Cᶜ ∩ (fun _ : Ω => b0) ⁻¹' B) := by
    intro B
    ext ω
    change (if ω ∈ C then Y ω else b0) ∈ B ↔ _
    by_cases hωC : ω ∈ C
    · rw [if_pos hωC]
      constructor
      · intro hY
        rcases Set.mem_iUnion.mp hωC with ⟨t, ht⟩
        refine Or.inl (Set.mem_iUnion.mpr ⟨t, ht, ?_⟩)
        change X t ω ∈ B
        rw [← hYX t ω ht]
        exact hY
      · rintro (hparts | hbad)
        · rcases Set.mem_iUnion.mp hparts with ⟨t, ht, hXt⟩
          rw [hYX t ω ht]
          exact hXt
        · exact (hbad.1 hωC).elim
    · rw [if_neg hωC]
      constructor
      · intro h0
        exact Or.inr ⟨hωC, h0⟩
      · rintro (hparts | hbad)
        · rcases Set.mem_iUnion.mp hparts with ⟨t, ht, _hXt⟩
          exact (hωC (Set.mem_iUnion.mpr ⟨t, ht⟩)).elim
        · exact hbad.2
  have hY' : Measurable Y' := by
    intro B hB
    rw [hpre B]
    exact (MeasurableSet.iUnion (fun t => (hE t).inter ((hX t) hB))).union
      (hC.compl.inter (measurable_const hB))
  refine ⟨Y', hY', ?_⟩
  filter_upwards [hcover] with ω hω
  have hωC : ω ∈ C := Set.mem_iUnion.mpr hω
  change Y ω = if ω ∈ C then Y ω else b0
  rw [if_pos hωC]

/-- Distribution calculation from disjoint measurable selection-time events.
Each local law is factored against the event weight before summation. -/
theorem partition_preimage_measure {Ω β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace β]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : ℕ → Set Ω) (X : ℕ → Ω → β) (Y : Ω → β)
    (hE : ∀ t, MeasurableSet (E t))
    (hdisj : Pairwise (fun s t : ℕ => Disjoint (E s) (E t)))
    (hcover : ∀ᵐ ω ∂μ, ∃ t, ω ∈ E t)
    (hX : ∀ t, Measurable (X t))
    (hYX : ∀ t ω, ω ∈ E t → Y ω = X t ω)
    (B : Set β) (hB : MeasurableSet B) (p : ENNReal)
    (hfactor : ∀ t, μ (E t ∩ (X t) ⁻¹' B) = μ (E t) * p) :
    μ (Y ⁻¹' B) = p := by
  have hpre : Y ⁻¹' B =ᵐ[μ] ⋃ t, E t ∩ (X t) ⁻¹' B := by
    filter_upwards [hcover] with ω hω
    apply propext
    constructor
    · intro hY
      rcases hω with ⟨t, ht⟩
      refine Set.mem_iUnion.mpr ⟨t, ht, ?_⟩
      change X t ω ∈ B
      rw [← hYX t ω ht]
      exact hY
    · intro hparts
      rcases Set.mem_iUnion.mp hparts with ⟨t, ht, hXt⟩
      change Y ω ∈ B
      rw [hYX t ω ht]
      exact hXt
  have hC : (⋃ t, E t) =ᵐ[μ] Set.univ := by
    filter_upwards [hcover] with ω hω
    apply propext
    exact ⟨fun _ => Set.mem_univ ω, fun _ => Set.mem_iUnion.mpr hω⟩
  have hweights : (∑' t, μ (E t)) = 1 := by
    calc
      (∑' t, μ (E t)) = μ (⋃ t, E t) := (measure_iUnion hdisj hE).symm
      _ = μ Set.univ := measure_congr hC
      _ = 1 := measure_univ
  have hparts : Pairwise (fun s t : ℕ =>
      Disjoint (E s ∩ (X s) ⁻¹' B) (E t ∩ (X t) ⁻¹' B)) := by
    intro s t hst
    exact (hdisj hst).mono Set.inter_subset_left Set.inter_subset_left
  calc
    μ (Y ⁻¹' B) = μ (⋃ t, E t ∩ (X t) ⁻¹' B) := measure_congr hpre
    _ = ∑' t, μ (E t ∩ (X t) ⁻¹' B) :=
      measure_iUnion hparts (fun t => (hE t).inter ((hX t) hB))
    _ = ∑' t, μ (E t) * p := tsum_congr hfactor
    _ = (∑' t, μ (E t)) * p := ENNReal.tsum_mul_right
    _ = p := by rw [hweights, one_mul]

/-- Equal marginal laws for a predictably selected variable, once the
selection events have been shown independent of their own fresh coordinate. -/
theorem partition_identDistrib {Ω β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace β]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : ℕ → Set Ω) (X : ℕ → Ω → β) (Y X0 : Ω → β) (b0 : β)
    (hE : ∀ t, MeasurableSet (E t))
    (hdisj : Pairwise (fun s t : ℕ => Disjoint (E s) (E t)))
    (hcover : ∀ᵐ ω ∂μ, ∃ t, ω ∈ E t)
    (hX : ∀ t, Measurable (X t)) (hX0 : Measurable X0)
    (hYX : ∀ t ω, ω ∈ E t → Y ω = X t ω)
    (hlaw : ∀ t, IdentDistrib (X t) X0 μ μ)
    (hind : ∀ t (B : Set β), MeasurableSet B →
      μ (E t ∩ (X t) ⁻¹' B) = μ (E t) * μ ((X t) ⁻¹' B)) :
    IdentDistrib Y X0 μ μ := by
  have hY : AEMeasurable Y μ := partition_aemeasurable μ E X Y b0 hE hcover hX hYX
  refine ⟨hY, hX0.aemeasurable, ?_⟩
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply_of_aemeasurable hY hB,
    Measure.map_apply_of_aemeasurable hX0.aemeasurable hB]
  apply partition_preimage_measure μ E X Y hE hdisj hcover hX hYX B hB
  intro t
  rw [hind t B hB, (hlaw t).measure_mem_eq hB]

/-- Measurability interface for the exact `Nat.nth`-defined skipped process.
Only almost-sure event coverage is required. -/
theorem skippedProcess_aemeasurable_of_partition {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (D : ℕ → Ω → ℝ) (ξ : ℕ → Ω → Bool) (k : ℕ)
    (E : ℕ → Set Ω) (hE : ∀ t, MeasurableSet (E t))
    (hcover : ∀ᵐ ω ∂μ, ∃ t, ω ∈ E t)
    (hmeas : ∀ t, Measurable (D t))
    (hindex : ∀ t ω, ω ∈ E t → selectedIndex (fun s => ξ s ω) k = t) :
    AEMeasurable (skippedProcess D ξ k) μ := by
  apply partition_aemeasurable μ E D (skippedProcess D ξ k) 0 hE hcover hmeas
  intro t ω hω
  unfold skippedProcess
  rw [hindex t ω hω]

/-- Marginal-law interface preserving the original skipped process on bad paths. -/
theorem skippedProcess_identDistrib_of_partition {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : ℕ → Ω → ℝ) (ξ : ℕ → Ω → Bool) (k : ℕ)
    (E : ℕ → Set Ω) (hE : ∀ t, MeasurableSet (E t))
    (hdisj : Pairwise (fun s t : ℕ => Disjoint (E s) (E t)))
    (hcover : ∀ᵐ ω ∂μ, ∃ t, ω ∈ E t)
    (hmeas : ∀ t, Measurable (D t))
    (hindex : ∀ t ω, ω ∈ E t → selectedIndex (fun s => ξ s ω) k = t)
    (hident : ∀ t, IdentDistrib (D t) (D 0) μ μ)
    (hind : ∀ t (B : Set ℝ), MeasurableSet B →
      μ (E t ∩ (D t) ⁻¹' B) = μ (E t) * μ ((D t) ⁻¹' B)) :
    IdentDistrib (skippedProcess D ξ k) (D 0) μ μ := by
  apply partition_identDistrib μ E D (skippedProcess D ξ k) (D 0) 0
    hE hdisj hcover hmeas (hmeas 0)
  · intro t ω hω
    unfold skippedProcess
    rw [hindex t ω hω]
  · exact hident
  · exact hind

end BacklogCuratorOptionalSkipping

namespace BacklogCuratorOptionalSkipping

/-- Countable partition factorization with a fixed measurable past event.
The cover only holds almost everywhere; the selected value is not changed on bad paths. -/
theorem partition_inter_preimage_measure {Ω β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace β]
    (μ : Measure Ω) (E : ℕ → Set Ω) (X : ℕ → Ω → β) (Y : Ω → β)
    (C : Set Ω) (hC : MeasurableSet C)
    (hE : ∀ t, MeasurableSet (E t))
    (hdisj : Pairwise (fun s t : ℕ => Disjoint (E s) (E t)))
    (hcover : ∀ᵐ ω ∂μ, ∃ t, ω ∈ E t)
    (hX : ∀ t, Measurable (X t))
    (hYX : ∀ t ω, ω ∈ E t → Y ω = X t ω)
    (B : Set β) (hB : MeasurableSet B) (p : ENNReal)
    (hfactor : ∀ t, μ ((E t ∩ C) ∩ (X t) ⁻¹' B) = μ (E t ∩ C) * p) :
    μ (C ∩ Y ⁻¹' B) = μ C * p := by
  have hpre : (C ∩ Y ⁻¹' B : Set Ω) =ᵐ[μ] ⋃ t, (E t ∩ C) ∩ (X t) ⁻¹' B := by
    filter_upwards [hcover] with ω hω
    apply propext
    constructor
    · rintro ⟨hωC, hY⟩
      rcases hω with ⟨t, ht⟩
      refine Set.mem_iUnion.mpr ⟨t, ⟨ht, hωC⟩, ?_⟩
      change X t ω ∈ B
      rw [← hYX t ω ht]
      exact hY
    · intro hparts
      rcases Set.mem_iUnion.mp hparts with ⟨t, ⟨ht, hωC⟩, hXt⟩
      refine ⟨hωC, ?_⟩
      change Y ω ∈ B
      rw [hYX t ω ht]
      exact hXt
  have hcoverC : (⋃ t, E t ∩ C) =ᵐ[μ] C := by
    filter_upwards [hcover] with ω hω
    apply propext
    constructor
    · intro hparts
      rcases Set.mem_iUnion.mp hparts with ⟨t, ht, hωC⟩
      exact hωC
    · intro hωC
      rcases hω with ⟨t, ht⟩
      exact Set.mem_iUnion.mpr ⟨t, ht, hωC⟩
  have hdisjC : Pairwise (fun s t : ℕ => Disjoint (E s ∩ C) (E t ∩ C)) := by
    intro s t hst
    exact (hdisj hst).mono Set.inter_subset_left Set.inter_subset_left
  have hweights : (∑' t, μ (E t ∩ C)) = μ C := by
    calc
      (∑' t, μ (E t ∩ C)) = μ (⋃ t, E t ∩ C) :=
        (measure_iUnion hdisjC (fun t => (hE t).inter hC)).symm
      _ = μ C := measure_congr hcoverC
  have hparts : Pairwise (fun s t : ℕ =>
      Disjoint ((E s ∩ C) ∩ (X s) ⁻¹' B) ((E t ∩ C) ∩ (X t) ⁻¹' B)) := by
    intro s t hst
    exact (hdisjC hst).mono Set.inter_subset_left Set.inter_subset_left
  calc
    μ (C ∩ Y ⁻¹' B) = μ (⋃ t, (E t ∩ C) ∩ (X t) ⁻¹' B) :=
      measure_congr hpre
    _ = ∑' t, μ ((E t ∩ C) ∩ (X t) ⁻¹' B) :=
      measure_iUnion hparts (fun t => ((hE t).inter hC).inter ((hX t) hB))
    _ = ∑' t, μ (E t ∩ C) * p := tsum_congr hfactor
    _ = (∑' t, μ (E t ∩ C)) * p := ENNReal.tsum_mul_right
    _ = μ C * p := by rw [hweights]

/-- Independence of a selected variable from an a.e.-measurable past variable.
The substantive freshness premise is localized to `E t ∩ Z ⁻¹' A`.
No pointwise measurable version or globally infinite selection path is assumed. -/
theorem partition_indepFun {Ω α β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : ℕ → Set Ω) (X : ℕ → Ω → β) (Y X0 : Ω → β) (Z : Ω → α)
    (hE : ∀ t, MeasurableSet (E t))
    (hdisj : Pairwise (fun s t : ℕ => Disjoint (E s) (E t)))
    (hcover : ∀ᵐ ω ∂μ, ∃ t, ω ∈ E t)
    (hX : ∀ t, Measurable (X t))
    (hYX : ∀ t ω, ω ∈ E t → Y ω = X t ω)
    (hZ : AEMeasurable Z μ)
    (hlaw : ∀ t, IdentDistrib (X t) X0 μ μ)
    (hlocal : ∀ t (A : Set α) (B : Set β), MeasurableSet A → MeasurableSet B →
      μ ((E t ∩ Z ⁻¹' A) ∩ (X t) ⁻¹' B) =
        μ (E t ∩ Z ⁻¹' A) * μ ((X t) ⁻¹' B)) :
    IndepFun Z Y μ := by
  rcases hZ with ⟨Z', hZ', hZZ'⟩
  have hlocal' : ∀ t (A : Set α) (B : Set β), MeasurableSet A → MeasurableSet B →
      μ ((E t ∩ Z' ⁻¹' A) ∩ (X t) ⁻¹' B) =
        μ (E t ∩ Z' ⁻¹' A) * μ ((X t) ⁻¹' B) := by
    intro t A B hA hB
    have hleft : μ ((E t ∩ Z' ⁻¹' A) ∩ (X t) ⁻¹' B) =
        μ ((E t ∩ Z ⁻¹' A) ∩ (X t) ⁻¹' B) := by
      apply measure_congr
      filter_upwards [hZZ'] with ω hω
      apply propext
      change ω ∈ (E t ∩ Z' ⁻¹' A) ∩ (X t) ⁻¹' B ↔ ω ∈ (E t ∩ Z ⁻¹' A) ∩ (X t) ⁻¹' B
      simp only [Set.mem_inter_iff, Set.mem_preimage, hω]
    have hright : μ (E t ∩ Z' ⁻¹' A) = μ (E t ∩ Z ⁻¹' A) := by
      apply measure_congr
      filter_upwards [hZZ'] with ω hω
      apply propext
      change ω ∈ E t ∩ Z' ⁻¹' A ↔ ω ∈ E t ∩ Z ⁻¹' A
      simp only [Set.mem_inter_iff, Set.mem_preimage, hω]
    rw [hleft, hright]
    exact hlocal t A B hA hB
  have hZ'Y : IndepFun Z' Y μ := by
    apply indepFun_iff_measure_inter_preimage_eq_mul.mpr
    intro A B hA hB
    have hYB : μ (Y ⁻¹' B) = μ (X0 ⁻¹' B) := by
      have hsum := partition_inter_preimage_measure μ E X Y Set.univ MeasurableSet.univ
        hE hdisj hcover hX hYX B hB (μ (X0 ⁻¹' B)) (by
          intro t
          have ht := hlocal' t Set.univ B MeasurableSet.univ hB
          simpa only [Set.preimage_univ, Set.inter_univ,
            (hlaw t).measure_mem_eq hB] using ht)
      simpa only [Set.univ_inter, measure_univ, one_mul] using hsum
    calc
      μ (Z' ⁻¹' A ∩ Y ⁻¹' B) = μ (Z' ⁻¹' A) * μ (X0 ⁻¹' B) := by
        apply partition_inter_preimage_measure μ E X Y (Z' ⁻¹' A) (hZ' hA)
          hE hdisj hcover hX hYX B hB
        intro t
        rw [hlocal' t A B hA hB, (hlaw t).measure_mem_eq hB]
      _ = μ (Z' ⁻¹' A) * μ (Y ⁻¹' B) := by rw [hYB]
  exact hZ'Y.congr hZZ'.symm (Filter.Eventually.of_forall (fun _ => rfl))

/-- Exact `Nat.nth` wrapper. The earlier selected process need only be a.e. measurable.
All remaining local independence assertions refer to the original fresh coordinate `D t`. -/
theorem skippedProcess_indepFun_of_partition {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : ℕ → Ω → ℝ) (ξ : ℕ → Ω → Bool) (i j : ℕ)
    (E : ℕ → Set Ω) (hE : ∀ t, MeasurableSet (E t))
    (hdisj : Pairwise (fun s t : ℕ => Disjoint (E s) (E t)))
    (hcover : ∀ᵐ ω ∂μ, ∃ t, ω ∈ E t)
    (hmeas : ∀ t, Measurable (D t))
    (hindex : ∀ t ω, ω ∈ E t → selectedIndex (fun s => ξ s ω) j = t)
    (hZi : AEMeasurable (skippedProcess D ξ i) μ)
    (hident : ∀ t, IdentDistrib (D t) (D 0) μ μ)
    (hlocal : ∀ t (A B : Set ℝ), MeasurableSet A → MeasurableSet B →
      μ ((E t ∩ (skippedProcess D ξ i) ⁻¹' A) ∩ (D t) ⁻¹' B) =
        μ (E t ∩ (skippedProcess D ξ i) ⁻¹' A) * μ ((D t) ⁻¹' B)) :
    IndepFun (skippedProcess D ξ i) (skippedProcess D ξ j) μ := by
  apply partition_indepFun μ E D (skippedProcess D ξ j) (D 0)
    (skippedProcess D ξ i) hE hdisj hcover hmeas
  · intro t ω hω
    unfold skippedProcess
    rw [hindex t ω hω]
  · exact hZi
  · exact hident
  · exact hlocal

end BacklogCuratorOptionalSkipping

namespace BacklogCuratorOptionalSkipping.SelectionBridge

/-- On a later genuine hit, the finite strict-past observable is the actual earlier
skipped value. This uses the parent's proved finite-hit identity, not global infinity. -/
theorem earlierSelectedValue_eq_skippedProcess_on_hit {Ω : Type*}
    (D : ℕ → Ω → ℝ) (ξ : ℕ → Ω → Bool) {i j t : ℕ} {ω : Ω}
    (hij : i < j) (hω : ω ∈ selectionHit ξ j t) :
    earlierSelectedValue D ξ i t ω = skippedProcess D ξ i ω := by
  exact (bridge_previous_skipped_eq_masked_sum D ξ hij hω).symm

/-- Only the intersection with the hit event is rewritten. No global measurability
or global finite-prefix representation of the actual skipped process is assumed. -/
theorem selectionHit_inter_skipped_preimage_eq {Ω : Type*}
    (D : ℕ → Ω → ℝ) (ξ : ℕ → Ω → Bool) (i j t : ℕ) (hij : i < j)
    (A : Set ℝ) :
    selectionHit ξ j t ∩ (skippedProcess D ξ i) ⁻¹' A =
      selectionEvent ξ j t ∩ (earlierSelectedValue D ξ i t) ⁻¹' A := by
  ext ω
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    change earlierSelectedValue D ξ i t ω ∈ A
    rw [earlierSelectedValue_eq_skippedProcess_on_hit D ξ hij h.1]
    exact h.2
  · intro h
    refine ⟨h.1, ?_⟩
    change skippedProcess D ξ i ω ∈ A
    rw [← earlierSelectedValue_eq_skippedProcess_on_hit D ξ hij h.1]
    exact h.2

/-- A restricted earlier skipped observation is measurable in the strict past even
though no measurability assertion for the unrestricted skipped process is used. -/
theorem measurableSet_selectionHit_skipped_preimage_past {Ω : Type*}
    (D : ℕ → Ω → ℝ) (ξ : ℕ → Ω → Bool)
    (hξ : ∀ t, ∃ g : (Fin t → ℝ) → Bool, Measurable g ∧
      ξ t = fun ω => g (fun i => D i ω))
    (i j t : ℕ) (hij : i < j) (A : Set ℝ) (hA : MeasurableSet A) :
    MeasurableSet[demandPast D t]
      (selectionHit ξ j t ∩ (skippedProcess D ξ i) ⁻¹' A) := by
  rw [selectionHit_inter_skipped_preimage_eq D ξ i j t hij A]
  exact (measurableSet_selectionEvent_past D ξ hξ j t).inter
    ((measurable_earlierSelectedValue_past D ξ hξ i t) hA)

/-- Local fresh-demand factorization for the actual earlier selected observation,
restricted to a later genuine hit. The full skipped-process pairwise law is separate. -/
theorem selectionHit_skipped_demand_factor {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (D : ℕ → Ω → ℝ) (hmeas : ∀ n, Measurable (D n))
    (hindep : iIndepFun D μ) (ξ : ℕ → Ω → Bool)
    (hξ : ∀ t, ∃ g : (Fin t → ℝ) → Bool, Measurable g ∧
      ξ t = fun ω => g (fun i => D i ω))
    (i j t : ℕ) (hij : i < j) (A B : Set ℝ)
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    μ ((selectionHit ξ j t ∩ (skippedProcess D ξ i) ⁻¹' A) ∩ (D t) ⁻¹' B) =
      μ (selectionHit ξ j t ∩ (skippedProcess D ξ i) ⁻¹' A) * μ ((D t) ⁻¹' B) := by
  have hset := selectionHit_inter_skipped_preimage_eq D ξ i j t hij A
  calc
    μ ((selectionHit ξ j t ∩ (skippedProcess D ξ i) ⁻¹' A) ∩ (D t) ⁻¹' B) =
        μ ((D t) ⁻¹' B ∩
          (selectionEvent ξ j t ∩ (earlierSelectedValue D ξ i t) ⁻¹' A)) := by
      rw [hset]
      exact congrArg μ (Set.inter_comm _ _)
    _ = μ ((D t) ⁻¹' B) *
        μ (selectionEvent ξ j t ∩ (earlierSelectedValue D ξ i t) ⁻¹' A) :=
      demand_selectionEvent_earlier_factor μ D hmeas hindep ξ hξ i j t B A hB hA
    _ = μ (selectionHit ξ j t ∩ (skippedProcess D ξ i) ⁻¹' A) *
        μ ((D t) ⁻¹' B) := by
      rw [← hset]
      exact mul_comm _ _

end BacklogCuratorOptionalSkipping.SelectionBridge

namespace BacklogCuratorOptionalSkipping

/-- A genuinely selected observation has exactly the original marginal law.
All hypotheses are from the frozen target; no selected-law premise is added. -/
theorem skippedProcess_identDistrib {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : ℕ → Ω → ℝ) (hmeas : ∀ t, Measurable (D t))
    (hindep : iIndepFun D μ)
    (hident : ∀ t, IdentDistrib (D t) (D 0) μ μ)
    (ξ : ℕ → Ω → Bool)
    (hξ : ∀ t, ∃ g : (Fin t → ℝ) → Bool, Measurable g ∧
      ξ t = fun ω => g (fun i => D i ω))
    (hinf : ∀ᵐ ω ∂μ, ∃ᶠ t in atTop, ξ t ω = true) (k : ℕ) :
    IdentDistrib (skippedProcess D ξ k) (D 0) μ μ := by
  apply skippedProcess_identDistrib_of_partition μ D ξ k (selectionHit ξ k)
  · intro t
    exact SelectionBridge.measurableSet_selectionEvent D hmeas ξ hξ k t
  · exact bridge_selectionHit_pairwiseDisjoint ξ k
  · exact bridge_ae_selectionHit_exists μ ξ hinf k
  · exact hmeas
  · intro t ω hω
    exact bridge_selectedIndex_on_hit ξ hω
  · exact hident
  · intro t B hB
    calc
      μ (selectionHit ξ k t ∩ (D t) ⁻¹' B) =
          μ ((D t) ⁻¹' B ∩ SelectionBridge.selectionEvent ξ k t) :=
        congrArg μ (Set.inter_comm _ _)
      _ = μ ((D t) ⁻¹' B) * μ (SelectionBridge.selectionEvent ξ k t) :=
        SelectionBridge.demand_selectionEvent_factor μ D hmeas hindep ξ hξ k t B hB
      _ = μ (selectionHit ξ k t) * μ ((D t) ⁻¹' B) := mul_comm _ _

/-- Each earlier skipped variable is independent of a later one. Strict-past
measurability is used only on the later variable's genuine-hit events. -/
theorem skippedProcess_indepFun_of_lt {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : ℕ → Ω → ℝ) (hmeas : ∀ t, Measurable (D t))
    (hindep : iIndepFun D μ)
    (hident : ∀ t, IdentDistrib (D t) (D 0) μ μ)
    (ξ : ℕ → Ω → Bool)
    (hξ : ∀ t, ∃ g : (Fin t → ℝ) → Bool, Measurable g ∧
      ξ t = fun ω => g (fun i => D i ω))
    (hinf : ∀ᵐ ω ∂μ, ∃ᶠ t in atTop, ξ t ω = true)
    {i j : ℕ} (hij : i < j) :
    IndepFun (skippedProcess D ξ i) (skippedProcess D ξ j) μ := by
  apply skippedProcess_indepFun_of_partition μ D ξ i j (selectionHit ξ j)
  · intro t
    exact SelectionBridge.measurableSet_selectionEvent D hmeas ξ hξ j t
  · exact bridge_selectionHit_pairwiseDisjoint ξ j
  · exact bridge_ae_selectionHit_exists μ ξ hinf j
  · exact hmeas
  · intro t ω hω
    exact bridge_selectedIndex_on_hit ξ hω
  · exact (skippedProcess_identDistrib μ D hmeas hindep hident ξ hξ hinf i).aemeasurable_fst
  · exact hident
  · intro t A B hA hB
    exact SelectionBridge.selectionHit_skipped_demand_factor
      μ D hmeas hindep ξ hξ i j t hij A B hA hB

/-- The pairwise independence required by the pinned Mathlib strong law.
The original `Nat.nth` process is retained on every path. -/
theorem skippedProcess_pairwise_indepFun {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : ℕ → Ω → ℝ) (hmeas : ∀ t, Measurable (D t))
    (hindep : iIndepFun D μ)
    (hident : ∀ t, IdentDistrib (D t) (D 0) μ μ)
    (ξ : ℕ → Ω → Bool)
    (hξ : ∀ t, ∃ g : (Fin t → ℝ) → Bool, Measurable g ∧
      ξ t = fun ω => g (fun i => D i ω))
    (hinf : ∀ᵐ ω ∂μ, ∃ᶠ t in atTop, ξ t ω = true) :
    Pairwise (fun i j =>
      IndepFun (skippedProcess D ξ i) (skippedProcess D ξ j) μ) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact skippedProcess_indepFun_of_lt μ D hmeas hindep hident ξ hξ hinf hlt
  · exact (skippedProcess_indepFun_of_lt μ D hmeas hindep hident ξ hξ hinf hgt).symm

end BacklogCuratorOptionalSkipping


/-!
Deterministic count/cofinality and composition helpers.
SOURCE ONLY: no Lean compilation or independent verification has been performed.
The Base.lean prefix above is copied verbatim.
-/

namespace BacklogCuratorOptionalSkipping

/-- The literal filtered-range cardinality is the standard predicate count. -/
theorem selectedCount_eq_nat_count (s : ℕ → Bool) (T : ℕ) :
    selectedCount s T = Nat.count (fun t => s t = true) T := by
  exact (Nat.count_eq_card_filter_range (fun t => s t = true) T).symm

/-- Selection counts increase with the horizon, without any infinitude premise. -/
theorem selectedCount_monotone (s : ℕ → Bool) : Monotone (selectedCount s) := by
  intro T U hTU
  simpa only [selectedCount_eq_nat_count] using
    (Nat.count_monotone (fun t => s t = true)) hTU

/-- Frequently true selections form an infinite subset of the natural numbers. -/
theorem infinite_true_set_of_frequently (s : ℕ → Bool)
    (hinf : ∃ᶠ t in atTop, s t = true) :
    {t : ℕ | s t = true}.Infinite := by
  intro hfinite
  obtain ⟨N, hN⟩ := hfinite.bddAbove
  obtain ⟨t, htN, ht⟩ := (Filter.frequently_atTop.mp hinf) (N + 1)
  have htupper : t ≤ N := hN ht
  omega

/-- Every finite count occurs on an infinite selection path. -/
theorem selectedCount_surjective_of_infinite (s : ℕ → Bool)
    (hinf : {t : ℕ | s t = true}.Infinite) :
    Function.Surjective (selectedCount s) := by
  intro n
  obtain ⟨T, hT⟩ :=
    (Nat.surjective_count_of_infinite_setOfPred (p := fun t => s t = true) hinf) n
  exact ⟨T, (selectedCount_eq_nat_count s T).trans hT⟩

/-- Monotonicity and cofinality give divergence of the literal selection count. -/
theorem selectedCount_tendsto_atTop_of_infinite (s : ℕ → Bool)
    (hinf : {t : ℕ | s t = true}.Infinite) :
    Tendsto (selectedCount s) atTop atTop := by
  apply (selectedCount_monotone s).tendsto_atTop_atTop
  intro n
  obtain ⟨T, hT⟩ := selectedCount_surjective_of_infinite s hinf n
  exact ⟨T, hT.symm.le⟩

/-- This is the pathwise form matching the frozen almost-sure infinity assumption. -/
theorem selectedCount_tendsto_atTop_of_frequently (s : ℕ → Bool)
    (hinf : ∃ᶠ t in atTop, s t = true) :
    Tendsto (selectedCount s) atTop atTop :=
  selectedCount_tendsto_atTop_of_infinite s (infinite_true_set_of_frequently s hinf)

/-- The corresponding real-valued denominator also diverges. -/
theorem selectedCount_real_tendsto_atTop (s : ℕ → Bool)
    (hinf : ∃ᶠ t in atTop, s t = true) :
    Tendsto (fun T : ℕ => (selectedCount s T : ℝ)) atTop atTop :=
  (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp
    (selectedCount_tendsto_atTop_of_frequently s hinf)

/-- General count-subsequence composition, with an arbitrary target filter. -/
theorem tendsto_comp_selectedCount {α : Type*} {l : Filter α}
    (s : ℕ → Bool) (hinf : ∃ᶠ t in atTop, s t = true)
    (u : ℕ → α) (hu : Tendsto u atTop l) :
    Tendsto (fun T => u (selectedCount s T)) atTop l :=
  hu.comp (selectedCount_tendsto_atTop_of_frequently s hinf)

/-- Composition of the ordinary Cesaro limit with the exact filtered-cardinality
real denominator appearing in the frozen target. The numerator here is the
selected-index prefix sum, to be identified with selectedSum by enumeration. -/
theorem tendsto_counted_average (s : ℕ → Bool) (a : ℕ → ℝ) (L : ℝ)
    (hinf : ∃ᶠ t in atTop, s t = true)
    (havg : Tendsto (fun n : ℕ => (∑ k ∈ range n, a k) / (n : ℝ))
      atTop (𝓝 L)) :
    Tendsto (fun T : ℕ =>
      (∑ k ∈ range (selectedCount s T), a k) /
        (((range T).filter (fun t => s t = true)).card : ℝ))
      atTop (𝓝 L) := by
  exact havg.comp (selectedCount_tendsto_atTop_of_frequently s hinf)

end BacklogCuratorOptionalSkipping


namespace BacklogCuratorOptionalSkipping

/-- The literal filtered cardinality is Mathlib's count below T. -/
theorem enumeration_count_eq_natCount (s : ℕ → Bool) (T : ℕ) :
    selectedCount s T = Nat.count (fun t => s t = true) T := by
  unfold selectedCount
  exact (Nat.count_eq_card_filter_range (fun t => s t = true) T).symm

theorem selectedIndex_selected (s : ℕ → Bool)
    (hinf : {t | s t = true}.Infinite) (k : ℕ) :
    s (selectedIndex s k) = true := by
  change s (Nat.nth (fun t => s t = true) k) = true
  exact Nat.nth_mem_of_infinite hinf k

theorem selectedIndex_injective (s : ℕ → Bool)
    (hinf : {t | s t = true}.Infinite) :
    Function.Injective (selectedIndex s) := by
  change Function.Injective (Nat.nth (fun t => s t = true))
  exact Nat.nth_injective hinf

/-- A rank below the finite selected count has its selection before T.
This direction does not need infinitely many selections. -/
theorem selectedIndex_lt_of_lt_count (s : ℕ → Bool) {T k : ℕ}
    (hk : k < selectedCount s T) : selectedIndex s k < T := by
  change Nat.nth (fun t => s t = true) k < T
  apply Nat.nth_lt_of_lt_count
  rw [← enumeration_count_eq_natCount s T]
  exact hk

/-- The rank of a selected time enumerates back to that exact time. -/
theorem selectedIndex_at_count (s : ℕ → Bool) {t : ℕ} (ht : s t = true) :
    selectedIndex s (selectedCount s t) = t := by
  unfold selectedIndex
  rw [enumeration_count_eq_natCount]
  exact Nat.nth_count ht

/-- On infinite selection paths, counting below the kth selected time gives k. -/
theorem selectedCount_at_index (s : ℕ → Bool)
    (hinf : {t | s t = true}.Infinite) (k : ℕ) :
    selectedCount s (selectedIndex s k) = k := by
  rw [enumeration_count_eq_natCount]
  change Nat.count (fun t => s t = true) (Nat.nth (fun t => s t = true) k) = k
  exact Nat.count_nth_of_infinite hinf k

theorem selectedSum_eq_filter_sum (s : ℕ → Bool) (a : ℕ → ℝ) (T : ℕ) :
    selectedSum s a T = ∑ t ∈ (range T).filter (fun t => s t = true), a t := by
  unfold selectedSum
  rw [Finset.sum_filter]

/-- The selected sum up to the original clock T is exactly the prefix sum
of the first selectedCount(s,T) enumerated observations. -/
theorem selectedSum_reindex (s : ℕ → Bool) (a : ℕ → ℝ)
    (hinf : {t | s t = true}.Infinite) (T : ℕ) :
    selectedSum s a T =
      ∑ k ∈ range (selectedCount s T), a (selectedIndex s k) := by
  rw [selectedSum_eq_filter_sum]
  symm
  refine Finset.sum_bij (fun k _hk => selectedIndex s k) ?_ ?_ ?_ ?_
  · intro k hk
    exact mem_filter.mpr
      ⟨mem_range.mpr (selectedIndex_lt_of_lt_count s (mem_range.mp hk)),
        selectedIndex_selected s hinf k⟩
  · intro k _hk j _hj hkj
    exact selectedIndex_injective s hinf hkj
  · intro t ht
    rcases mem_filter.mp ht with ⟨htT, hselected⟩
    refine ⟨selectedCount s t, ?_, selectedIndex_at_count s hselected⟩
    apply mem_range.mpr
    rw [enumeration_count_eq_natCount s t, enumeration_count_eq_natCount s T]
    exact Nat.count_strict_mono hselected (mem_range.mp htT)
  · intro k _hk
    rfl

end BacklogCuratorOptionalSkipping


namespace BacklogCuratorOptionalSkipping

/-! ## Piece 73 (dependency-planner): generic real SLLN bridge

Everything above this block is `Base.lean` (sha256 `a8c6fcd1…`) verbatim; paste only this block.
Uses the pinned `ProbabilityTheory.strong_law_ae_real` (Etemadi, pairwise independence). -/

/-- Pairwise independence from mutual independence. -/
theorem pairwise_indepFun_of_iIndepFun {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (Y : ℕ → Ω → ℝ) (h : iIndepFun Y μ) :
    Pairwise (fun i j => IndepFun (Y i) (Y j) μ) :=
  fun _ _ hij => h.indepFun hij

/-- Strong law for `f ∘ Y` when every `Y k` has the law of `D0` and the `Y k` are pairwise
independent: `(∑_{k<n} f (Y k ω)) / n → ∫ f ∘ D0` almost surely. -/
theorem slln_comp_bridge {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (D0 : Ω → ℝ) (Y : ℕ → Ω → ℝ)
    (hindep : Pairwise (fun i j => IndepFun (Y i) (Y j) μ))
    (hident : ∀ k, IdentDistrib (Y k) D0 μ μ)
    (f : ℝ → ℝ) (hf : Measurable f) (hint : Integrable (fun ω => f (D0 ω)) μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (∑ k ∈ range n, f (Y k ω)) / (n : ℝ)) atTop
      (𝓝 (∫ ω, f (D0 ω) ∂μ)) := by
  have hXid : ∀ k, IdentDistrib (fun ω => f (Y k ω)) (fun ω => f (D0 ω)) μ μ :=
    fun k => (hident k).comp hf
  have hXint : Integrable (fun ω => f (Y 0 ω)) μ := (hXid 0).integrable_iff.mpr hint
  have hXindep : Pairwise (fun i j => IndepFun (fun ω => f (Y i ω)) (fun ω => f (Y j ω)) μ) :=
    fun i j hij => (hindep hij : IndepFun (Y i) (Y j) μ).comp hf hf
  have hXident : ∀ k, IdentDistrib (fun ω => f (Y k ω)) (fun ω => f (Y 0 ω)) μ μ :=
    fun k => (hXid k).trans (hXid 0).symm
  have hlim := strong_law_ae_real (fun k ω => f (Y k ω)) hXint hXindep hXident
  filter_upwards [hlim] with ω hω
  rw [← (hXid 0).integral_eq]
  exact hω

/-- The bridge specialised to the selected process of `Base.lean`. -/
theorem skippedProcess_slln {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (D : ℕ → Ω → ℝ) (ξ : ℕ → Ω → Bool)
    (hindepS : Pairwise (fun i j =>
      IndepFun (skippedProcess D ξ i) (skippedProcess D ξ j) μ))
    (hidentS : ∀ k, IdentDistrib (skippedProcess D ξ k) (D 0) μ μ)
    (f : ℝ → ℝ) (hf : Measurable f) (hint : Integrable (fun ω => f (D 0 ω)) μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (∑ k ∈ range n, f (skippedProcess D ξ k ω)) / (n : ℝ))
      atTop (𝓝 (∫ ω, f (D 0 ω) ∂μ)) :=
  slln_comp_bridge μ (D 0) (skippedProcess D ξ) hindepS hidentS f hf hint

end BacklogCuratorOptionalSkipping


namespace BacklogCuratorOptionalSkipping

/-- Conditional final assembly: the two selected-law facts remain an explicit obligation,
not new premises of the frozen target. Count growth and the exact raw denominator are proved. -/
theorem optional_skipping_slln_of_selected_laws {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (D : ℕ → Ω → ℝ) (ξ : ℕ → Ω → Bool)
    (hinf : ∀ᵐ ω ∂μ, ∃ᶠ t in atTop, ξ t ω = true)
    (hindepS : Pairwise (fun i j =>
      IndepFun (skippedProcess D ξ i) (skippedProcess D ξ j) μ))
    (hidentS : ∀ k, IdentDistrib (skippedProcess D ξ k) (D 0) μ μ)
    (f : ℝ → ℝ) (hf : Measurable f) (hint : Integrable (fun ω => f (D 0 ω)) μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun T : ℕ =>
        (∑ t ∈ range T, if ξ t ω = true then f (D t ω) else 0) /
          (((range T).filter (fun t => ξ t ω = true)).card : ℝ))
      atTop (𝓝 (∫ ω, f (D 0 ω) ∂μ)) := by
  have hslln := skippedProcess_slln μ D ξ hindepS hidentS f hf hint
  filter_upwards [hinf, hslln] with ω hfreq hlim
  have hinfinite := infinite_true_set_of_frequently (fun t => ξ t ω) hfreq
  have hcounted := tendsto_counted_average (fun t => ξ t ω)
    (fun k => f (skippedProcess D ξ k ω)) (∫ ω, f (D 0 ω) ∂μ) hfreq hlim
  have hsum : ∀ T : ℕ,
      (∑ t ∈ range T, if ξ t ω = true then f (D t ω) else 0) =
        ∑ k ∈ range (selectedCount (fun t => ξ t ω) T), f (skippedProcess D ξ k ω) := by
    intro T
    exact selectedSum_reindex (fun t => ξ t ω) (fun t => f (D t ω)) hinfinite T
  simpa only [hsum] using hcounted

end BacklogCuratorOptionalSkipping

namespace KMNewsvendor

/-- Lemma 1 (p. 934): the strong law of large numbers along a predictably selected subsequence.
`ξ t` (Lean period `t`, the paper's `ξ_{t+1}`) is a deterministic measurable function of
the demands `D i`, `i < t`; infinitely many periods are selected almost surely; `f (D)` is integrable. -/
theorem optional_skipping_slln {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (D : ℕ → Ω → ℝ) (hmeas : ∀ t, Measurable (D t)) (hindep : iIndepFun D μ)
    (hident : ∀ t, IdentDistrib (D t) (D 0) μ μ)
    (ξ : ℕ → Ω → Bool)
    (hξ : ∀ t, ∃ g : (Fin t → ℝ) → Bool, Measurable g ∧ ξ t = fun ω => g (fun i => D i ω))
    (hinf : ∀ᵐ ω ∂μ, ∃ᶠ t in atTop, ξ t ω = true)
    (f : ℝ → ℝ) (hf : Measurable f) (hint : Integrable (fun ω => f (D 0 ω)) μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun T : ℕ =>
        (∑ t ∈ range T, if ξ t ω = true then f (D t ω) else 0) /
          (((range T).filter (fun t => ξ t ω = true)).card : ℝ))
      atTop (𝓝 (∫ ω, f (D 0 ω) ∂μ)) := by
  exact BacklogCuratorOptionalSkipping.optional_skipping_slln_of_selected_laws μ D ξ hinf
    (BacklogCuratorOptionalSkipping.skippedProcess_pairwise_indepFun
      μ D hmeas hindep hident ξ hξ hinf)
    (BacklogCuratorOptionalSkipping.skippedProcess_identDistrib
      μ D hmeas hindep hident ξ hξ hinf)
    f hf hint

end KMNewsvendor

end Prove2SwarmSubmission

open MeasureTheory ProbabilityTheory Filter Finset Topology
theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (D : ℕ → Ω → ℝ) (hmeas : ∀ t, Measurable (D t)) (hindep : iIndepFun D μ)
    (hident : ∀ t, IdentDistrib (D t) (D 0) μ μ)
    (ξ : ℕ → Ω → Bool)
    (hξ : ∀ t, ∃ g : (Fin t → ℝ) → Bool, Measurable g ∧ ξ t = fun ω => g (fun i => D i ω))
    (hinf : ∀ᵐ ω ∂μ, ∃ᶠ t in atTop, ξ t ω = true)
    (f : ℝ → ℝ) (hf : Measurable f) (hint : Integrable (fun ω => f (D 0 ω)) μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun T : ℕ =>
        (∑ t ∈ range T, if ξ t ω = true then f (D t ω) else 0) /
          (((range T).filter (fun t => ξ t ω = true)).card : ℝ))
      atTop (𝓝 (∫ ω, f (D 0 ω) ∂μ)) := by
  exact Prove2SwarmSubmission.KMNewsvendor.optional_skipping_slln μ D hmeas hindep hident ξ hξ hinf f hf hint
