-- Prove2me | solution 1 for MDPFinance.Semicontinuous.usc_maximizer_existence
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T03:34:46.673008+00:00
-- url     : https://prove2.me/submissions/d8eda88a-3332-45a7-85ad-7b1c90ee02d9

import Mathlib
import Definitions.Def_MDPFinance_Semicontinuous_Model
import Definitions.Def_MDPFinance_Semicontinuous_Policy
import Definitions.Def_MDPFinance_Semicontinuous_Operators
import Definitions.Def_MDPFinance_Semicontinuous_BoundingFunction
import Definitions.Def_MDPFinance_Semicontinuous_SetValued

open MeasureTheory ProbabilityTheory MDPFinance.Semicontinuous


namespace MDPFinance.Semicontinuous

open Filter Topology Set

namespace MDPSel

/-- one lexicographic step -/
def stepK {E A : Type*} (φ : A → ℝ) (K : E → Set A) (x : E) : Set A :=
  {a | a ∈ K x ∧ ∀ b ∈ K x, φ a ≤ φ b}

lemma stepK_props {E A : Type*} [MeasurableSpace E] [TopologicalSpace A] [T2Space A]
    (φ : A → ℝ) (hφ : Continuous φ) (K : E → Set A)
    (hK : ∀ x, IsCompact (K x)) (hne : ∀ x, (K x).Nonempty)
    (hm : ∀ F, IsClosed F → MeasurableSet {x | (K x ∩ F).Nonempty}) :
    (∀ x, IsCompact (stepK φ K x)) ∧ (∀ x, (stepK φ K x).Nonempty) ∧
    (∀ F, IsClosed F → MeasurableSet {x | (stepK φ K x ∩ F).Nonempty}) := by
  have hcl : ∀ x, IsClosed (stepK φ K x) := by
    intro x
    have : stepK φ K x = K x ∩ ⋂ b ∈ K x, {a | φ a ≤ φ b} := by
      ext a; simp [stepK]
    rw [this]
    exact (hK x).isClosed.inter (isClosed_biInter fun b _ => isClosed_le hφ continuous_const)
  refine ⟨fun x => (hK x).of_isClosed_subset (hcl x) (fun a ha => ha.1), fun x => ?_, ?_⟩
  · obtain ⟨a, ha, hmin⟩ := (hK x).exists_isMinOn (hne x) hφ.continuousOn
    exact ⟨a, ha, fun b hb => hmin hb⟩
  · intro F hF
    -- characterization
    have key : {x | (stepK φ K x ∩ F).Nonempty} =
        ⋂ j : ℕ, ⋂ q : ℚ, ({x | (K x ∩ {a | φ a ≤ q}).Nonempty}ᶜ ∪
          {x | (K x ∩ (F ∩ {a | φ a ≤ (q : ℝ) + 1 / ((j : ℝ) + 1)})).Nonempty}) := by
      ext x
      simp only [mem_setOf_eq, mem_iInter, mem_union, mem_compl_iff]
      constructor
      · rintro ⟨a, ⟨haK, hamin⟩, haF⟩ j q
        by_cases h : (K x ∩ {a | φ a ≤ q}).Nonempty
        · right
          obtain ⟨b, hbK, hbq⟩ := h
          refine ⟨a, haK, haF, ?_⟩
          have := hamin b hbK
          simp only [mem_setOf_eq] at hbq ⊢
          have : (0:ℝ) < 1 / ((j:ℝ) + 1) := by positivity
          linarith
        · left; exact h
      · intro H
        obtain ⟨a0, ha0, hmin0⟩ := (hK x).exists_isMinOn (hne x) hφ.continuousOn
        obtain ⟨q0, hq0⟩ := exists_rat_gt (φ a0)
        have hKF : (K x ∩ F).Nonempty := by
          rcases H 0 q0 with h | h
          · exact absurd ⟨a0, ha0, hq0.le⟩ h
          · obtain ⟨a, haK, haF, _⟩ := h
            exact ⟨a, haK, haF⟩
        obtain ⟨b, ⟨hbK, hbF⟩, hbmin⟩ :=
          ((hK x).inter_right hF).exists_isMinOn hKF hφ.continuousOn
        refine ⟨b, ⟨hbK, fun c hc => ?_⟩, hbF⟩
        have hc0 : φ a0 ≤ φ c := hmin0 hc
        suffices φ b ≤ φ a0 by linarith
        by_contra hlt
        push_neg at hlt
        obtain ⟨j, hj⟩ := exists_nat_gt (2 / (φ b - φ a0))
        have hpos : 0 < φ b - φ a0 := by linarith
        have hj' : 2 / ((j:ℝ) + 1) < φ b - φ a0 := by
          rw [div_lt_iff₀ (by positivity)]
          rw [div_lt_iff₀ hpos] at hj
          nlinarith
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show φ a0 < φ a0 + 1 / ((j:ℝ) + 1) by
          have : (0:ℝ) < 1 / ((j:ℝ) + 1) := by positivity
          linarith)
        rcases H j q with h | h
        · exact h ⟨a0, ha0, hq1.le⟩
        · obtain ⟨c, hcK, hcF, hcq⟩ := h
          have := hbmin ⟨hcK, hcF⟩
          simp only [mem_setOf_eq] at hcq this
          have e : 2 / ((j:ℝ) + 1) = 1 / ((j:ℝ) + 1) + 1 / ((j:ℝ) + 1) := by ring
          linarith
    rw [key]
    refine MeasurableSet.iInter fun j => MeasurableSet.iInter fun q => ?_
    exact (hm _ (isClosed_le hφ continuous_const)).compl.union
      (hm _ (hF.inter (isClosed_le hφ continuous_const)))

def iterK {E A : Type*} (φ : ℕ → A → ℝ) (K : E → Set A) : ℕ → E → Set A
  | 0 => K
  | i + 1 => stepK (φ i) (iterK φ K i)

theorem select {E A : Type*} [MeasurableSpace E] [TopologicalSpace A]
    [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A]
    (K : E → Set A) (hK : ∀ x, IsCompact (K x)) (hne : ∀ x, (K x).Nonempty)
    (hm : ∀ F, IsClosed F → MeasurableSet {x | (K x ∩ F).Nonempty}) :
    ∃ f : E → A, Measurable f ∧ ∀ x, f x ∈ K x := by
  by_cases hE : Nonempty E
  swap
  · refine ⟨fun x => (hE ⟨x⟩).elim, ?_, fun x => (hE ⟨x⟩).elim⟩
    exact fun s _ => by
      have : (fun x : E => (hE ⟨x⟩).elim : E → A) ⁻¹' s = ∅ := by
        ext x; exact (hE ⟨x⟩).elim
      rw [this]; exact MeasurableSet.empty
  obtain ⟨x0⟩ := hE
  haveI : Nonempty A := ⟨(hne x0).some⟩
  letI := TopologicalSpace.metrizableSpaceMetric A
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq A
  let φ : ℕ → A → ℝ := fun i a => dist a (d i)
  have hφc : ∀ i, Continuous (φ i) := fun i => continuous_id.dist continuous_const
  have hsep : ∀ a b : A, (∀ i, φ i a = φ i b) → a = b := by
    intro a b h
    have : ∀ ε > 0, dist a b < ε := by
      intro ε hε
      obtain ⟨i, hi⟩ := hd.exists_dist_lt a (half_pos hε)
      have h1 := h i
      simp only [φ] at h1
      calc dist a b ≤ dist a (d i) + dist (d i) b := dist_triangle _ _ _
        _ = dist a (d i) + dist a (d i) := by rw [dist_comm (d i) b, ← h1]
        _ < ε := by have := dist_comm a (d i); linarith
    exact dist_le_zero.1 (le_of_forall_gt_imp_ge_of_dense fun ε hε => (this ε hε).le) |> fun h => h
  have P : ∀ i, (∀ x, IsCompact (iterK φ K i x)) ∧ (∀ x, (iterK φ K i x).Nonempty) ∧
      (∀ F, IsClosed F → MeasurableSet {x | (iterK φ K i x ∩ F).Nonempty}) := by
    intro i
    induction i with
    | zero => exact ⟨hK, hne, hm⟩
    | succ i ih => exact stepK_props (φ i) (hφc i) _ ih.1 ih.2.1 ih.2.2
  have hsub : ∀ x i, iterK φ K (i + 1) x ⊆ iterK φ K i x := fun x i a ha => ha.1
  have hinter : ∀ x F, IsClosed F → (∀ i, (iterK φ K i x ∩ F).Nonempty) →
      (⋂ i, (iterK φ K i x ∩ F)).Nonempty := by
    intro x F hF h
    apply IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    · intro i; exact inter_subset_inter_left _ (hsub x i)
    · exact h
    · exact ((P 0).1 x).inter_right hF
    · intro i; exact ((P i).1 x).isClosed.inter hF
  have huniq : ∀ x a b, (∀ i, a ∈ iterK φ K i x) → (∀ i, b ∈ iterK φ K i x) → a = b := by
    intro x a b ha hb
    apply hsep
    intro i
    exact le_antisymm ((ha (i+1)).2 b (hb i)) ((hb (i+1)).2 a (ha i))
  have hex : ∀ x, ∃ a, ∀ i, a ∈ iterK φ K i x := by
    intro x
    obtain ⟨a, ha⟩ := hinter x univ isClosed_univ (fun i => by simpa using (P i).2.1 x)
    exact ⟨a, fun i => (mem_iInter.1 ha i).1⟩
  choose f hf using hex
  refine ⟨f, ?_, fun x => hf x 0⟩
  apply measurable_of_isClosed
  intro F hF
  have : f ⁻¹' F = ⋂ i, {x | (iterK φ K i x ∩ F).Nonempty} := by
    ext x
    simp only [mem_preimage, mem_iInter, mem_setOf_eq]
    constructor
    · intro h i; exact ⟨f x, hf x i, h⟩
    · intro h
      obtain ⟨a, ha⟩ := hinter x F hF h
      have ha' : ∀ i, a ∈ iterK φ K i x ∩ F := fun i => mem_iInter.1 ha i
      have : a = f x := huniq x a (f x) (fun i => (ha' i).1) (hf x)
      rw [← this]; exact (ha' 0).2
  rw [this]
  exact MeasurableSet.iInter fun i => (P i).2.2 F hF

end MDPSel

open Filter Topology Set

namespace MDPGen

def Sec {E A : Type*} (D : Set (E × A)) (x : E) : Set A := {a | (x, a) ∈ D}

noncomputable def Tsup {E A : Type*} (D : Set (E × A)) (L : E × A → EReal) (x : E) : EReal :=
  ⨆ a ∈ Sec D x, L (x, a)

def USCSV {E A : Type*} [TopologicalSpace E] [TopologicalSpace A] (D : E → Set A) : Prop :=
  ∀ x : E, ∀ xs : ℕ → E, Tendsto xs atTop (𝓝 x) →
    ∀ as : ℕ → A, (∀ n, as n ∈ D (xs n)) → ∃ a ∈ D x, MapClusterPt a atTop as

lemma prod_freq {E A : Type*} [TopologicalSpace E] [TopologicalSpace A]
    {xs : ℕ → E} {x : E} (hx : Tendsto xs atTop (𝓝 x)) {as : ℕ → A} {a : A}
    (ha : MapClusterPt a atTop as) {P : E × A → Prop} (hP : ∀ᶠ q in 𝓝 (x, a), P q) :
    ∃ᶠ k in atTop, P (xs k, as k) := by
  rw [nhds_prod_eq, Filter.eventually_prod_iff] at hP
  obtain ⟨pa, hpa, pb, hpb, h⟩ := hP
  exact ((ha.frequently hpb).and_eventually (hx.eventually hpa)).mono
    fun k hk => h hk.2 hk.1

lemma sec_usc {E A : Type*} [TopologicalSpace E] [TopologicalSpace A]
    {D : Set (E × A)} {L : E × A → EReal} (hL : UpperSemicontinuousOn L D) (x : E) :
    UpperSemicontinuousOn (fun a => L (x, a)) (Sec D x) := by
  intro a ha y hy
  have h1 := hL (x, a) ha y hy
  have ht : Tendsto (fun b : A => (x, b)) (𝓝[Sec D x] a) (𝓝[D] (x, a)) :=
    (continuous_const.prodMk continuous_id).continuousWithinAt.tendsto_nhdsWithin
      (fun b hb => hb)
  exact ht.eventually h1

lemma tsup_attain {E A : Type*} [TopologicalSpace E] [TopologicalSpace A]
    {D : Set (E × A)} {L : E × A → EReal} (hDc : ∀ x, IsCompact (Sec D x))
    (hL : UpperSemicontinuousOn L D) (x : E) (hne : (Sec D x).Nonempty) :
    ∃ a ∈ Sec D x, L (x, a) = Tsup D L x := by
  obtain ⟨a, ha, hmax⟩ := (sec_usc hL x).exists_isMaxOn hne (hDc x)
  refine ⟨a, ha, le_antisymm (le_biSup (fun b => L (x, b)) ha) ?_⟩
  exact iSup₂_le fun b hb => hmax hb

lemma tsup_ne_bot {E A : Type*} {D : Set (E × A)} {L : E × A → EReal} {x : E}
    (h : Tsup D L x ≠ ⊥) : (Sec D x).Nonempty := by
  by_contra hc
  rw [not_nonempty_iff_eq_empty] at hc
  apply h
  simp [Tsup, hc]

lemma tsup_usc {E A : Type*} [TopologicalSpace E] [TopologicalSpace A]
    [FirstCountableTopology E]
    {D : Set (E × A)} {L : E × A → EReal} (hDc : ∀ x, IsCompact (Sec D x))
    (hDu : USCSV (Sec D)) (hL : UpperSemicontinuousOn L D) :
    UpperSemicontinuous (Tsup D L) := by
  intro x y hy
  by_contra h
  rw [Filter.not_eventually] at h
  obtain ⟨xs, hxs, hle⟩ := exists_seq_forall_of_frequently h
  simp only [not_lt] at hle
  have hne : ∀ k, (Sec D (xs k)).Nonempty := fun k =>
    tsup_ne_bot (ne_bot_of_gt (lt_of_lt_of_le hy (hle k)))
  choose as has hLa using fun k => tsup_attain hDc hL (xs k) (hne k)
  obtain ⟨a, ha, hcl⟩ := hDu x xs hxs as has
  have hLa_le : L (x, a) ≤ Tsup D L x := le_biSup (fun b => L (x, b)) ha
  have h1 := hL (x, a) ha y (lt_of_le_of_lt hLa_le hy)
  rw [eventually_nhdsWithin_iff] at h1
  obtain ⟨k, hk⟩ := (prod_freq hxs hcl h1).exists
  have : L (xs k, as k) < y := hk (has k)
  rw [hLa k] at this
  exact absurd (hle k) (not_le.2 this)

lemma tsup_select {E A : Type*} [TopologicalSpace E] [TopologicalSpace A]
    [TopologicalSpace.MetrizableSpace E] [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A]
    {D : Set (E × A)} {L : E × A → EReal} (hDc : ∀ x, IsCompact (Sec D x))
    (hDu : USCSV (Sec D)) (hL : UpperSemicontinuousOn L D)
    (hne : ∀ x, (Sec D x).Nonempty) :
    ∃ f : E → A, Measurable f ∧ ∀ x, (x, f x) ∈ D ∧ L (x, f x) = Tsup D L x := by
  let K : E → Set A := fun x => Sec D x ∩ (fun a => L (x, a)) ⁻¹' Ici (Tsup D L x)
  have hKc : ∀ x, IsCompact (K x) := fun x =>
    (sec_usc hL x).isCompact_inter_preimage_Ici (hDc x) _
  have hKne : ∀ x, (K x).Nonempty := by
    intro x
    obtain ⟨a, ha, h⟩ := tsup_attain hDc hL x (hne x)
    exact ⟨a, ha, by simp [h]⟩
  have hKm : ∀ F, IsClosed F → MeasurableSet {x | (K x ∩ F).Nonempty} := by
    intro F hF
    let DF : Set (E × A) := D ∩ {p | p.2 ∈ F}
    have hSecF : ∀ x, Sec DF x = Sec D x ∩ F := fun x => rfl
    have hDFc : ∀ x, IsCompact (Sec DF x) := fun x => (hDc x).inter_right hF
    have hDFu : USCSV (Sec DF) := by
      intro x xs hxs as has
      obtain ⟨a, ha, hcl⟩ := hDu x xs hxs as (fun k => (has k).1)
      exact ⟨a, ⟨ha, hF.mem_of_mapClusterPt hcl (Eventually.of_forall fun k => (has k).2)⟩, hcl⟩
    have hLF : UpperSemicontinuousOn L DF := hL.mono inter_subset_left
    have hTF := tsup_usc hDFc hDFu hLF
    have hT := tsup_usc hDc hDu hL
    have hSclosed : IsClosed {x | (Sec DF x).Nonempty} := by
      apply IsSeqClosed.isClosed
      intro xs x hmem hxs
      choose as has using hmem
      obtain ⟨a, ha, _⟩ := hDFu x xs hxs as has
      exact ⟨a, ha⟩
    have : {x | (K x ∩ F).Nonempty} =
        {x | (Sec DF x).Nonempty} ∩ {x | Tsup D L x ≤ Tsup DF L x} := by
      ext x
      simp only [mem_setOf_eq, mem_inter_iff]
      constructor
      · rintro ⟨a, ⟨haD, haT⟩, haF⟩
        refine ⟨⟨a, haD, haF⟩, le_trans haT ?_⟩
        exact le_biSup (fun b => L (x, b)) (show a ∈ Sec DF x from ⟨haD, haF⟩)
      · rintro ⟨hnF, hle⟩
        obtain ⟨b, hb, hbeq⟩ := tsup_attain hDFc hLF x hnF
        refine ⟨b, ⟨hb.1, ?_⟩, hb.2⟩
        show Tsup D L x ≤ L (x, b)
        rw [hbeq]; exact hle
    rw [this]
    exact hSclosed.measurableSet.inter (measurableSet_le hT.measurable hTF.measurable)
  obtain ⟨f, hfm, hfK⟩ := MDPSel.select K hKc hKne hKm
  refine ⟨f, hfm, fun x => ⟨(hfK x).1, le_antisymm ?_ (hfK x).2⟩⟩
  exact le_biSup (fun b => L (x, b)) (hfK x).1

end MDPGen


open Filter Topology Set

theorem usc_core {E A : Type*}
    [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E] [TopologicalSpace.MetrizableSpace E]
    [SecondCountableTopology E] [StandardBorelSpace E]
    [MeasurableSpace A] [TopologicalSpace A] [BorelSpace A] [TopologicalSpace.MetrizableSpace A]
    [SecondCountableTopology A] [StandardBorelSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (n : ℕ) (hn : n < N)
    (v : E → EReal)
    (hD_compact : ∀ x, IsCompact (M.Dx n x)) (hD_usc : USCSetValued (M.Dx n))
    (hL_usc : UpperSemicontinuousOn (fun p : E × A => L M n v p) (M.D n)) :
    UpperSemicontinuous (T M n v) ∧ ∃ f, IsMaximizer M n v f := by
  have hT : T M n v = MDPGen.Tsup (M.D n) (L M n v) := rfl
  have hc : ∀ x, IsCompact (MDPGen.Sec (M.D n) x) := hD_compact
  have hu : MDPGen.USCSV (MDPGen.Sec (M.D n)) := hD_usc
  refine ⟨hT ▸ MDPGen.tsup_usc hc hu hL_usc, ?_⟩
  have hne : ∀ x, (MDPGen.Sec (M.D n) x).Nonempty := by
    obtain ⟨f, _, hf⟩ := M.hD_sel n hn
    exact fun x => ⟨f x, hf x⟩
  obtain ⟨f, hfm, hf⟩ := MDPGen.tsup_select hc hu hL_usc hne
  exact ⟨f, ⟨hfm, fun x => (hf x).1⟩, funext fun x => (hf x).2⟩

end MDPFinance.Semicontinuous

open MDPFinance.Semicontinuous


theorem solution {E A : Type*}
    [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E] [TopologicalSpace.MetrizableSpace E]
    [SecondCountableTopology E] [StandardBorelSpace E]
    [MeasurableSpace A] [TopologicalSpace A] [BorelSpace A] [TopologicalSpace.MetrizableSpace A]
    [SecondCountableTopology A] [StandardBorelSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (b : E → ℝ) (cr cg αb : ℝ)
    (hb : IsUpperBoundingFunction M b cr cg αb) (n : ℕ) (hn : n < N)
    (v : E → EReal) (hv : v ∈ IBbPlus b) (hv_usc : UpperSemicontinuous v)
    (hD_compact : ∀ x, IsCompact (M.Dx n x)) (hD_usc : USCSetValued (M.Dx n))
    (hL_usc : UpperSemicontinuousOn (fun p : E × A => L M n v p) (M.D n)) :
    UpperSemicontinuous (T M n v) ∧ ∃ f, IsMaximizer M n v f := by
  exact usc_core M n hn v hD_compact hD_usc hL_usc
