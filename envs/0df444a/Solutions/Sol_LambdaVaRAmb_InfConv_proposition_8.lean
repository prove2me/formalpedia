-- Prove2me | solution 1 for LambdaVaRAmb.InfConv.proposition_8
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T10:20:25.257132+00:00
-- url     : https://prove2.me/submissions/fb38712b-ca4e-4b6f-99a4-1599b3332263

import Mathlib
import Definitions.Def_LambdaVaRAmb_InfConv_Setting

open LambdaVaRAmb.InfConv

namespace LVaRP8Aux

open LambdaVaRAmb.Robust

lemma coe_sum_le {ι : Type*} (s : Finset ι) (a : ι → EReal) (b : ι → ℝ)
    (h : ∀ i ∈ s, a i ≤ (b i : EReal)) : ∑ i ∈ s, a i ≤ ((∑ i ∈ s, b i : ℝ) : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, EReal.coe_add]
    exact add_le_add (h j (Finset.mem_insert_self _ _))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

lemma sum_lt_top {ι : Type*} (s : Finset ι) (a : ι → EReal) (h : ∀ i ∈ s, a i < ⊤) :
    ∑ i ∈ s, a i < ⊤ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact EReal.add_lt_top (h j (Finset.mem_insert_self _ _)).ne
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi))).ne

lemma split_two (a T : EReal) (ha : a < ⊤) (hT : T < ⊤) (r : ℝ) (h : a + T < r) :
    ∃ u : ℝ, a < u ∧ T < ((r - u : ℝ) : EReal) := by
  induction a using EReal.rec with
  | bot =>
    induction T using EReal.rec with
    | bot => exact ⟨0, EReal.bot_lt_coe _, EReal.bot_lt_coe _⟩
    | coe t => exact ⟨r - t - 1, EReal.bot_lt_coe _, by norm_cast; linarith⟩
    | top => exact absurd hT (lt_irrefl _)
  | coe c =>
    induction T using EReal.rec with
    | bot => exact ⟨c + 1, by norm_cast; linarith, EReal.bot_lt_coe _⟩
    | coe t =>
      have h' : c + t < r := by exact_mod_cast h
      refine ⟨(c + (r - t)) / 2, ?_, ?_⟩ <;> norm_cast <;> linarith
    | top => exact absurd hT (lt_irrefl _)
  | top => exact absurd ha (lt_irrefl _)

lemma exists_real_gt_sum {ι : Type*} (s : Finset ι) (a : ι → EReal) (ha : ∀ i ∈ s, a i < ⊤) :
    ∀ r : ℝ, ∑ i ∈ s, a i < r → ∃ b : ι → ℝ, (∀ i ∈ s, a i < b i) ∧ ∑ i ∈ s, b i < r := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro r hr
    refine ⟨0, by simp, ?_⟩
    simp only [Finset.sum_empty] at hr ⊢
    exact_mod_cast hr
  | insert j s hj ih =>
    intro r hr
    rw [Finset.sum_insert hj] at hr
    have hT := sum_lt_top s a (fun i hi => ha i (Finset.mem_insert_of_mem hi))
    obtain ⟨u, hu1, hu2⟩ := split_two _ _ (ha j (Finset.mem_insert_self _ _)) hT r hr
    obtain ⟨b, hb1, hb2⟩ := ih (fun i hi => ha i (Finset.mem_insert_of_mem hi)) (r - u) hu2
    refine ⟨Function.update b j u, ?_, ?_⟩
    · intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · simpa using hu1
      · have : i ≠ j := fun h => hj (h ▸ hi)
        simpa [Function.update_of_ne this] using hb1 i hi
    · rw [Finset.sum_insert hj, Function.update_self]
      have : ∑ i ∈ s, Function.update b j u i = ∑ i ∈ s, b i := by
        apply Finset.sum_congr rfl
        intro i hi
        have : i ≠ j := fun h => hj (h ▸ hi)
        simp [Function.update_of_ne this]
      rw [this]; linarith

variable {Ω : Type*} [MeasurableSpace Ω]

lemma LVaR_le_of_mem (Λ : ℝ → ℝ) (w : Set Ω → ℝ) (X : Ω → ℝ) (x : ℝ)
    (h : w {ω | x < X ω} ≤ Λ x) : LVaR Λ w X ≤ x :=
  sInf_le ⟨x, h, rfl⟩

lemma LVaR_lt_top (Λ : ℝ → ℝ) (w : Set Ω → ℝ) (X : Ω → ℝ) (hX : Measurable X)
    (hΛ : InH Λ) (hlow : 0 < sInf (Set.range Λ)) (hw : IsContinuousCapacity w) :
    LVaR Λ w X < ⊤ := by
  have hbdd : BddBelow (Set.range Λ) := ⟨0, by rintro _ ⟨x, rfl⟩; exact (hΛ x).1.le⟩
  have hB : Filter.Tendsto (fun n : ℕ => w {ω | (n : ℝ) < X ω}) Filter.atTop (nhds 0) := by
    apply hw.2
    · intro n; exact measurableSet_lt measurable_const hX
    · intro n m hnm ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      have : (n : ℝ) ≤ m := by exact_mod_cast hnm
      linarith
    · ext ω
      simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_forall,
        not_lt]
      obtain ⟨n, hn⟩ := exists_nat_gt (X ω)
      exact ⟨n, hn.le⟩
  obtain ⟨n, hn⟩ := (hB.eventually (gt_mem_nhds hlow)).exists
  have : w {ω | (n : ℝ) < X ω} ≤ Λ n := hn.le.trans (csInf_le hbdd ⟨n, rfl⟩)
  exact lt_of_le_of_lt (LVaR_le_of_mem Λ w X n this) (EReal.coe_lt_top _)

/-- Disjointification of a finite cover into a measurable partition. -/
lemma exists_partition {n : ℕ} (hn : 0 < n) (A : Fin n → Set Ω) (hA : ∀ i, MeasurableSet (A i)) :
    ∃ B : Fin n → Set Ω, IsMeasPartition B ∧ ∀ i, (⋃ j, A j) ∩ B i ⊆ A i := by
  classical
  let i0 : Fin n := ⟨0, hn⟩
  let B : Fin n → Set Ω := fun i =>
    (A i ∪ ((⋂ j, (A j)ᶜ) ∩ {_ω | i = i0})) ∩ ⋂ j, ⋂ (_ : j < i), (A j)ᶜ
  have hi0 : ∀ j : Fin n, ¬ j < i0 := fun j h => by
    have : (j : ℕ) < 0 := h
    omega
  refine ⟨B, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro i
    refine MeasurableSet.inter (MeasurableSet.union (hA i) (MeasurableSet.inter
      (MeasurableSet.iInter fun j => (hA j).compl) (MeasurableSet.const _)))
      (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => (hA j).compl)
  · ext ω
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    by_cases hex : ∃ j, ω ∈ A j
    · obtain ⟨j, hj, hmin⟩ := WellFounded.has_min wellFounded_lt {j | ω ∈ A j} hex
      refine ⟨j, ?_⟩
      simp only [B, Set.mem_inter_iff, Set.mem_union, Set.mem_iInter, Set.mem_compl_iff]
      exact ⟨Or.inl hj, fun k hk hkA => hmin k hkA hk⟩
    · push_neg at hex
      refine ⟨i0, ?_⟩
      simp only [B, Set.mem_inter_iff, Set.mem_union, Set.mem_iInter, Set.mem_compl_iff,
        Set.mem_setOf_eq]
      exact ⟨Or.inr ⟨hex, trivial⟩, fun k hk => absurd hk (hi0 k)⟩
  · have key : ∀ i j : Fin n, i < j → Disjoint (B i) (B j) := by
      intro i j hij
      rw [Set.disjoint_left]
      intro ω hi hj
      simp only [B, Set.mem_inter_iff, Set.mem_union, Set.mem_iInter, Set.mem_compl_iff,
        Set.mem_setOf_eq] at hi hj
      have hnA : ω ∉ A i := hj.2 i hij
      rcases hi.1 with h | ⟨hall, _⟩
      · exact hnA h
      · rcases hj.1 with h | ⟨_, hj0⟩
        · exact hall j h
        · exact hi0 i (hj0 ▸ hij)
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact key i j h
    · exact (key j i h).symm
  · intro i ω ⟨hU, hB⟩
    simp only [B, Set.mem_inter_iff, Set.mem_union, Set.mem_iInter, Set.mem_compl_iff,
      Set.mem_setOf_eq] at hB
    rcases hB.1 with h | ⟨hall, _⟩
    · exact h
    · obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hU
      exact absurd hk (hall k)

lemma sum_indicator_partition {n : ℕ} (B : Fin n → Set Ω) (hB : IsMeasPartition B) (ω : Ω) :
    ∑ i, (B i).indicator (1 : Ω → ℝ) ω = 1 := by
  classical
  have : ω ∈ ⋃ i, B i := by rw [hB.2.1]; trivial
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 this
  rw [Finset.sum_eq_single i]
  · simp [Set.indicator_of_mem hi]
  · intro j _ hji
    have : ω ∉ B j := fun hj => Set.disjoint_left.1 (hB.2.2 hji) hj hi
    simp [Set.indicator_of_notMem this]
  · intro h; exact absurd (Finset.mem_univ i) h

variable {n : ℕ} (Λ : Fin n → ℝ → ℝ) (w : Fin n → Set Ω → ℝ)

lemma tail_set (X : Ω → ℝ) (x : ℝ) (y : Fin n → ℝ) (B : Fin n → Set Ω) (i : Fin n) :
    {ω | y i < tailAllocation X x y B i ω} = {ω | x < X ω} ∩ B i := by
  ext ω
  simp only [tailAllocation, Set.mem_setOf_eq, Set.mem_inter_iff]
  by_cases hω : ω ∈ B i
  · simp only [Set.indicator_of_mem hω, Pi.one_apply, mul_one, hω, and_true]
    constructor <;> intro h <;> linarith
  · simp [hω]

lemma tail_mem_alloc (dom : Set (Ω → ℝ)) (hdom : IsRVDomain dom) (X : Ω → ℝ) (hX : X ∈ dom)
    (x : ℝ) (y : Fin n → ℝ) (B : Fin n → Set Ω) (hB : IsMeasPartition B) (hy : ∑ i, y i = x) :
    tailAllocation X x y B ∈ Allocations dom n X := by
  refine ⟨fun i => hdom.split_mem X hX (B i) (hB.1 i) x (y i), fun ω => ?_⟩
  simp only [tailAllocation]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_indicator_partition B hB ω, hy]
  ring

lemma tail_sum_le (X : Ω → ℝ) (x : ℝ) (y : Fin n → ℝ) (B : Fin n → Set Ω)
    (hy : ∑ i, y i = x) (h : ∀ i, w i ({ω | x < X ω} ∩ B i) ≤ Λ i (y i)) :
    ∑ i, LVaR (Λ i) (w i) (tailAllocation X x y B i) ≤ (x : EReal) := by
  have := coe_sum_le Finset.univ (fun i => LVaR (Λ i) (w i) (tailAllocation X x y B i)) y
    (fun i _ => LVaR_le_of_mem (Λ i) (w i) (tailAllocation X x y B i) (y i)
      (by rw [tail_set]; exact h i))
  rwa [hy] at this

lemma infConv_le_tail (dom : Set (Ω → ℝ)) (hdom : IsRVDomain dom) (X : Ω → ℝ) (hX : X ∈ dom)
    (x : ℝ) (y : Fin n → ℝ) (B : Fin n → Set Ω) (hB : IsMeasPartition B) (hy : ∑ i, y i = x)
    (h : ∀ i, w i ({ω | x < X ω} ∩ B i) ≤ Λ i (y i)) :
    infConv dom (fun i => LVaR (Λ i) (w i)) X ≤ ∑ i, LVaR (Λ i) (w i) (tailAllocation X x y B i) :=
  iInf₂_le (tailAllocation X x y B) (tail_mem_alloc dom hdom X hX x y B hB hy)

lemma part1 (hn : 0 < n) (dom : Set (Ω → ℝ)) (hdom : IsRVDomain dom)
    (hΛ : ∀ i, InH (Λ i)) (hlow : ∀ i, 0 < sInf (Set.range (Λ i)))
    (hw : ∀ i, IsContinuousCapacity (w i)) (X : Ω → ℝ) (hX : X ∈ dom) :
    infConv dom (fun i => LVaR (Λ i) (w i)) X = inducedRM (capFamily Λ w) X := by
  have hXm : Measurable X := hdom.measurable X hX
  apply le_antisymm
  · apply le_sInf
    rintro _ ⟨x, ⟨y, hy, A, hA, hE⟩, rfl⟩
    obtain ⟨B, hBp, hBsub⟩ := exists_partition hn A (fun i => (hA i).1)
    have hw' : ∀ i, w i ({ω | x < X ω} ∩ B i) ≤ Λ i (y i) := by
      intro i
      refine le_trans ((hw i).1.mono _ _ ((measurableSet_lt measurable_const hXm).inter (hBp.1 i))
        (hA i).1 ?_) (hA i).2
      rw [hE]; exact hBsub i
    exact (infConv_le_tail Λ w dom hdom X hX x y B hBp hy hw').trans
      (tail_sum_le Λ w X x y B hy hw')
  · apply le_iInf₂
    intro Xs hXs
    rw [← EReal.le_of_forall_lt_iff_le]
    intro r hr
    obtain ⟨b, hb1, hb2⟩ := exists_real_gt_sum Finset.univ _
      (fun i _ => LVaR_lt_top (Λ i) (w i) (Xs i) (hdom.measurable _ (hXs.1 i)) (hΛ i) (hlow i)
        (hw i)) r hr
    have hex : ∀ i, ∃ yi : ℝ, w i {ω | yi < Xs i ω} ≤ Λ i yi ∧ yi < b i := by
      intro i
      obtain ⟨_, ⟨yi, hyi, rfl⟩, hlt⟩ := sInf_lt_iff.1 (hb1 i (Finset.mem_univ i))
      exact ⟨yi, hyi, EReal.coe_lt_coe_iff.1 hlt⟩
    choose y hyS hyb using hex
    have hxr : ∑ i, y i ≤ r := by
      have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => (hyb i).le)
      linarith
    refine le_trans (sInf_le ⟨∑ i, y i, ⟨y, rfl, fun i => {ω | ∑ i, y i < X ω} ∩ {ω | y i < Xs i ω},
      fun i => ⟨?_, ?_⟩, ?_⟩, rfl⟩) (EReal.coe_le_coe_iff.2 hxr)
    · exact (measurableSet_lt measurable_const hXm).inter
        (measurableSet_lt measurable_const (hdom.measurable _ (hXs.1 i)))
    · exact ((hw i).1.mono _ _ ((measurableSet_lt measurable_const hXm).inter
        (measurableSet_lt measurable_const (hdom.measurable _ (hXs.1 i))))
        (measurableSet_lt measurable_const (hdom.measurable _ (hXs.1 i)))
        Set.inter_subset_right).trans (hyS i)
    · ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · intro hω
        by_contra hcon
        push_neg at hcon
        have : X ω ≤ ∑ i, y i := by
          rw [← hXs.2 ω]
          exact Finset.sum_le_sum (fun i _ => hcon i hω)
        linarith
      · rintro ⟨i, h, _⟩; exact h

lemma cap_down (hw : ∀ i, IsCapacity (w i)) {t : ℝ} {E F : Set Ω} (hE : E ∈ capFamily Λ w t)
    (hF : MeasurableSet F) (hFE : F ⊆ E) : F ∈ capFamily Λ w t := by
  obtain ⟨y, hy, A, hA, rfl⟩ := hE
  refine ⟨y, hy, fun i => F ∩ A i, fun i => ⟨hF.inter (hA i).1,
    ((hw i).mono _ _ (hF.inter (hA i).1) (hA i).1 Set.inter_subset_right).trans (hA i).2⟩, ?_⟩
  rw [← Set.inter_iUnion]; exact (Set.inter_eq_left.2 hFE).symm

lemma cap_mono (hn : 0 < n) (hmono : ∀ i, Monotone (Λ i)) {t t' : ℝ} {E : Set Ω} (htt : t ≤ t')
    (hE : E ∈ capFamily Λ w t) : E ∈ capFamily Λ w t' := by
  classical
  obtain ⟨y, hy, A, hA, rfl⟩ := hE
  let i0 : Fin n := ⟨0, hn⟩
  refine ⟨fun i => y i + if i = i0 then t' - t else 0, ?_, A,
    fun i => ⟨(hA i).1, (hA i).2.trans (hmono i ?_)⟩, rfl⟩
  · rw [Finset.sum_add_distrib, hy, Finset.sum_ite_eq']; simp
  · show y i ≤ y i + if i = i0 then t' - t else 0
    split_ifs <;> linarith

lemma cap_empty (hn : 0 < n) (hw : ∀ i, IsCapacity (w i)) (hΛ : ∀ i, InH (Λ i)) (t : ℝ) :
    (∅ : Set Ω) ∈ capFamily Λ w t := by
  classical
  let i0 : Fin n := ⟨0, hn⟩
  refine ⟨fun i => if i = i0 then t else 0, by simp, fun _ => ∅,
    fun i => ⟨MeasurableSet.empty, by rw [(hw i).empty]; exact (hΛ i _).1.le⟩, by simp⟩

/-- `τ(E) = inf {t | E ∈ 𝒜_t}`. -/
noncomputable def tau (𝒜 : ℝ → Set (Set Ω)) (E : Set Ω) : EReal :=
  sInf ((fun t : ℝ => (t : EReal)) '' {t | E ∈ 𝒜 t})

noncomputable def g (t : ℝ) : ℝ := 1 / 2 + Real.arctan t / Real.pi

lemma g_pos (t : ℝ) : 0 < g t := by
  have h1 := Real.neg_pi_div_two_lt_arctan t
  have hp := Real.pi_pos
  unfold g
  have : -(1 / 2 : ℝ) < Real.arctan t / Real.pi := by
    rw [lt_div_iff₀ hp]; linarith
  linarith

lemma g_lt_one (t : ℝ) : g t < 1 := by
  have h1 := Real.arctan_lt_pi_div_two t
  have hp := Real.pi_pos
  unfold g
  have : Real.arctan t / Real.pi < 1 / 2 := by
    rw [div_lt_iff₀ hp]; linarith
  linarith

lemma g_strictMono : StrictMono g := by
  intro a b hab
  unfold g
  have := Real.arctan_strictMono hab
  have hp := Real.pi_pos
  have : Real.arctan a / Real.pi < Real.arctan b / Real.pi := div_lt_div_of_pos_right this hp
  linarith

noncomputable def G (e : EReal) : ℝ := if e = ⊥ then 0 else if e = ⊤ then 1 else g e.toReal

lemma G_coe (t : ℝ) : G t = g t := by simp [G]

lemma G_le_g_iff (e : EReal) (x : ℝ) : G e ≤ g x ↔ e ≤ x := by
  induction e using EReal.rec with
  | bot => simp [G, (g_pos x).le]
  | coe t => rw [G_coe, g_strictMono.le_iff_le, EReal.coe_le_coe_iff]
  | top => simp [G, not_le.2 (g_lt_one x)]

lemma G_nonneg (e : EReal) : 0 ≤ G e := by
  unfold G; split_ifs
  · exact le_rfl
  · exact zero_le_one
  · exact (g_pos _).le

lemma G_le_one (e : EReal) : G e ≤ 1 := by
  unfold G; split_ifs
  · exact zero_le_one
  · exact le_rfl
  · exact (g_lt_one _).le

lemma G_mono {a b : EReal} (h : a ≤ b) : G a ≤ G b := by
  induction b using EReal.rec with
  | bot => rw [le_bot_iff.1 h]
  | coe t => rw [G_coe]; exact (G_le_g_iff a t).2 h
  | top => simp only [G, if_neg (show (⊤ : EReal) ≠ ⊥ by simp), if_pos rfl]; exact G_le_one a

lemma family_repr (𝒜 : ℝ → Set (Set Ω))
    (down : ∀ t (E F : Set Ω), E ∈ 𝒜 t → MeasurableSet F → F ⊆ E → F ∈ 𝒜 t)
    (mono : ∀ t t' (E : Set Ω), t ≤ t' → E ∈ 𝒜 t → E ∈ 𝒜 t')
    (hempty : ∀ t, (∅ : Set Ω) ∈ 𝒜 t) (hne : (∅ : Set Ω) ≠ Set.univ) :
    ∃ Λ' : ℝ → ℝ, InHStarI Λ' ∧ ∃ w' : Set Ω → ℝ, IsCapacity w' ∧
      ∀ X : Ω → ℝ, Measurable X → inducedRM 𝒜 X = LVaR Λ' w' X := by
  classical
  have tau_mono : ∀ E F : Set Ω, MeasurableSet E → E ⊆ F → tau 𝒜 E ≤ tau 𝒜 F := by
    intro E F hE hEF
    exact sInf_le_sInf (Set.image_mono (fun t ht => down t F E ht hE hEF))
  let Λ' : ℝ → ℝ := fun x => if tau 𝒜 Set.univ ≤ (x : EReal) then 1 else g x
  let w' : Set Ω → ℝ := fun E => if E = Set.univ then 1 else G (tau 𝒜 E)
  have w'_le_one : ∀ E, w' E ≤ 1 := by
    intro E; simp only [w']; split_ifs
    · exact le_rfl
    · exact G_le_one _
  have key : ∀ E : Set Ω, MeasurableSet E → ∀ x : ℝ, w' E ≤ Λ' x ↔ tau 𝒜 E ≤ x := by
    intro E hE x
    by_cases hEu : E = Set.univ
    · subst hEu
      simp only [w', Λ', if_pos rfl]
      by_cases hcx : tau 𝒜 Set.univ ≤ (x : EReal)
      · simp [hcx]
      · rw [if_neg hcx]
        exact ⟨fun h => absurd h (not_le.2 (g_lt_one x)), fun h => absurd h hcx⟩
    · simp only [w', if_neg hEu, Λ']
      by_cases hcx : tau 𝒜 Set.univ ≤ (x : EReal)
      · simp only [if_pos hcx]
        exact ⟨fun _ => (tau_mono E Set.univ hE (Set.subset_univ _)).trans hcx,
          fun _ => G_le_one _⟩
      · simp only [if_neg hcx]
        exact G_le_g_iff _ x
  refine ⟨Λ', ⟨fun x => ?_, ?_⟩, w', ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [Λ']; split_ifs
    · exact ⟨one_pos, le_rfl⟩
    · exact ⟨g_pos x, (g_lt_one x).le⟩
  · intro x x' hxx
    simp only [Λ']
    split_ifs with h1 h2 h2
    · exact le_rfl
    · exact absurd (h1.trans (EReal.coe_le_coe_iff.2 hxx)) h2
    · exact (g_lt_one x).le
    · exact g_strictMono.monotone hxx
  · intro A _; simp only [w']; split_ifs
    · exact zero_le_one
    · exact G_nonneg _
  · intro A _; exact w'_le_one A
  · intro A B hA _ hAB
    by_cases hB : B = Set.univ
    · simp only [w', if_pos hB]; exact w'_le_one A
    · have hA' : A ≠ Set.univ := fun h => hB (Set.eq_univ_of_univ_subset (h ▸ hAB))
      simp only [w', if_neg hB, if_neg hA']
      exact G_mono (tau_mono A B hA hAB)
  · have hbot : tau 𝒜 ∅ = ⊥ := by
      rw [EReal.eq_bot_iff_forall_lt]
      intro y
      refine lt_of_le_of_lt (sInf_le ⟨y - 1, hempty _, rfl⟩) ?_
      exact EReal.coe_lt_coe_iff.2 (by linarith)
    simp [w', hne, hbot, G]
  · simp only [w', if_pos rfl]
  · intro X hX
    have hmeas : ∀ x : ℝ, MeasurableSet {ω | x < X ω} :=
      fun x => measurableSet_lt measurable_const hX
    have hLV : LVaR Λ' w' X = sInf ((fun x : ℝ => (x : EReal)) '' {x : ℝ | tau 𝒜 {ω | x < X ω} ≤ x}) := by
      unfold LVaR
      congr 2
      ext x
      exact key _ (hmeas x) x
    rw [hLV]
    unfold inducedRM
    apply le_antisymm
    · apply le_sInf
      rintro _ ⟨x, hx, rfl⟩
      rw [← EReal.le_of_forall_lt_iff_le]
      intro z hz
      have hz' : x < z := EReal.coe_lt_coe_iff.1 hz
      obtain ⟨_, ⟨t, ht, rfl⟩, htz⟩ := sInf_lt_iff.1 (hx.trans_lt hz)
      have h1 : {ω | x < X ω} ∈ 𝒜 z := mono t z _ (EReal.coe_le_coe_iff.1 htz.le) ht
      have h2 : {ω | z < X ω} ∈ 𝒜 z := down z _ _ h1 (hmeas z)
        (fun ω (hω : z < X ω) => show x < X ω by linarith)
      exact sInf_le ⟨z, h2, rfl⟩
    · apply sInf_le_sInf
      apply Set.image_mono
      intro x hx
      exact sInf_le (show ((x : ℝ) : EReal) ∈ (fun t : ℝ => (t : EReal)) '' {t | {ω | x < X ω} ∈ 𝒜 t}
        from ⟨x, hx, rfl⟩)

end LVaRP8Aux

open LVaRP8Aux in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n)
    (dom : Set (Ω → ℝ)) (hdom : IsRVDomain dom) (Λ : Fin n → ℝ → ℝ) (w : Fin n → Set Ω → ℝ)
    (hΛ : ∀ i, LambdaVaRAmb.Robust.InH (Λ i)) (hlow : ∀ i, 0 < sInf (Set.range (Λ i)))
    (hw : ∀ i, IsContinuousCapacity (w i)) :
    (∀ X ∈ dom,
        infConv dom (fun i => LambdaVaRAmb.Robust.LVaR (Λ i) (w i)) X = inducedRM (capFamily Λ w) X) ∧
    (∀ X ∈ dom, ∀ xstar : ℝ,
      IsLeast {x : ℝ | {ω | x < X ω} ∈ capFamily Λ w x} xstar →
        (∃ (y : Fin n → ℝ) (A : Fin n → Set Ω), ∑ i, y i = xstar ∧ IsMeasPartition A ∧
            ∀ i, w i ({ω | xstar < X ω} ∩ A i) ≤ Λ i (y i)) ∧
        (∀ (y : Fin n → ℝ) (A : Fin n → Set Ω), ∑ i, y i = xstar → IsMeasPartition A →
            (∀ i, w i ({ω | xstar < X ω} ∩ A i) ≤ Λ i (y i)) →
            IsOptimalAllocation dom (fun i => LambdaVaRAmb.Robust.LVaR (Λ i) (w i)) X
              (tailAllocation X xstar y A))) ∧
    ((∀ i, Monotone (Λ i)) →
      ∃ Λ' : ℝ → ℝ, InHStarI Λ' ∧ ∃ w' : Set Ω → ℝ, LambdaVaRAmb.Robust.IsCapacity w' ∧
        ∀ X ∈ dom, infConv dom (fun i => LambdaVaRAmb.Robust.LVaR (Λ i) (w i)) X = LambdaVaRAmb.Robust.LVaR Λ' w' X) := by
  have hcap : ∀ i, LambdaVaRAmb.Robust.IsCapacity (w i) := fun i => (hw i).1
  refine ⟨fun X hX => part1 Λ w hn dom hdom hΛ hlow hw X hX, ?_, ?_⟩
  · intro X hX xstar hxs
    have hXm : Measurable X := hdom.measurable X hX
    have hEq : inducedRM (capFamily Λ w) X = xstar :=
      le_antisymm (sInf_le ⟨xstar, hxs.1, rfl⟩)
        (le_sInf (by rintro _ ⟨x, hx, rfl⟩; exact EReal.coe_le_coe_iff.2 (hxs.2 hx)))
    refine ⟨?_, ?_⟩
    · obtain ⟨y, hy, A, hA, hE⟩ := hxs.1
      obtain ⟨B, hBp, hBsub⟩ := exists_partition hn A (fun i => (hA i).1)
      refine ⟨y, B, hy, hBp, fun i => ?_⟩
      refine le_trans ((hcap i).mono _ _ ((measurableSet_lt measurable_const hXm).inter (hBp.1 i))
        (hA i).1 ?_) (hA i).2
      rw [hE]; exact hBsub i
    · intro y A hy hA h
      refine ⟨tail_mem_alloc dom hdom X hX xstar y A hA hy, le_antisymm ?_
        (infConv_le_tail Λ w dom hdom X hX xstar y A hA hy h)⟩
      rw [part1 Λ w hn dom hdom hΛ hlow hw X hX, hEq]
      exact tail_sum_le Λ w X xstar y A hy h
  · intro hmono
    have hne : (∅ : Set Ω) ≠ Set.univ := by
      intro h
      have h0 := (hcap ⟨0, hn⟩).empty
      rw [h, (hcap ⟨0, hn⟩).univ] at h0
      norm_num at h0
    obtain ⟨Λ', hΛ', w', hw', hrep⟩ := family_repr (capFamily Λ w)
      (fun t E F hE hF hFE => cap_down Λ w hcap hE hF hFE)
      (fun t t' E htt hE => cap_mono Λ w hn hmono htt hE)
      (cap_empty Λ w hn hcap hΛ) hne
    exact ⟨Λ', hΛ', w', hw', fun X hX =>
      (part1 Λ w hn dom hdom hΛ hlow hw X hX).trans (hrep X (hdom.measurable X hX))⟩
