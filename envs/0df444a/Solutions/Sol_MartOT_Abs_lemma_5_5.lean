-- Prove2me | solution 1 for MartOT.Abs.lemma_5_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T05:59:28.722265+00:00
-- url     : https://prove2.me/submissions/c91a52ca-0330-4e30-a2f2-c883fdcb2b55

import Mathlib
import Definitions.Def_MartOT_Var_Setting

open MeasureTheory

/-- Three distinct points cannot lie in a set with at most two elements. -/
lemma hn55_three {s : Set ℝ} (h : s.encard ≤ 2) {a b c : ℝ} (ha : a ∈ s) (hb : b ∈ s)
    (hc : c ∈ s) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : False := by
  have hsub : ({a, b, c} : Set ℝ) ⊆ s := by
    intro y hy
    rcases hy with rfl | rfl | rfl <;> assumption
  have h3 : ({a, b, c} : Set ℝ).encard = 3 := by
    rw [Set.encard_insert_of_notMem, Set.encard_pair hbc]
    · rfl
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hab, hac⟩
  have := (Set.encard_le_encard hsub).trans h
  rw [h3] at this
  exact absurd this (by decide)

/-- The points of `Γ` having a point of the same fibre strictly below (`side = true`) or strictly
above (`side = false`) form a Borel set: they are the injective continuous image of a Borel set. -/
lemma hn55_meas (Γ : Set (ℝ × ℝ)) (hΓ : MeasurableSet Γ)
    (h2 : ∀ x : ℝ, {y : ℝ | (x, y) ∈ Γ}.encard ≤ 2) (r : ℝ → ℝ → Prop)
    (hr : MeasurableSet {q : ℝ × ℝ × ℝ | r q.2.2 q.2.1})
    (hrirr : ∀ y, ¬ r y y) :
    MeasurableSet {p : ℝ × ℝ | p ∈ Γ ∧ ∃ y', (p.1, y') ∈ Γ ∧ r y' p.2} := by
  set W : Set (ℝ × ℝ × ℝ) :=
    {q | (q.1, q.2.1) ∈ Γ ∧ (q.1, q.2.2) ∈ Γ ∧ r q.2.2 q.2.1} with hW
  have hWm : MeasurableSet W := by
    refine (measurable_fst.prodMk (measurable_fst.comp measurable_snd) hΓ).inter
      ((measurable_fst.prodMk (measurable_snd.comp measurable_snd) hΓ).inter hr)
  have heq : {p : ℝ × ℝ | p ∈ Γ ∧ ∃ y', (p.1, y') ∈ Γ ∧ r y' p.2} =
      (fun q : ℝ × ℝ × ℝ => (q.1, q.2.1)) '' W := by
    ext ⟨x, y⟩
    constructor
    · rintro ⟨hp, y', hy', hr'⟩
      exact ⟨(x, y, y'), ⟨hp, hy', hr'⟩, rfl⟩
    · rintro ⟨⟨x', y1, y2⟩, ⟨h1, h2', h3⟩, he⟩
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨h1, y2, h2', h3⟩
  rw [heq]
  refine hWm.image_of_continuousOn_injOn (by fun_prop) ?_
  rintro ⟨x, y, y1⟩ ⟨ha, hb, hc⟩ ⟨x', y', y2⟩ ⟨ha', hb', hc'⟩ he
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  by_contra hne
  have hy12 : y1 ≠ y2 := fun h => hne (by rw [h])
  have hy1 : y1 ≠ y := fun h => hrirr y (h ▸ hc)
  have hy2 : y2 ≠ y := fun h => hrirr y (h ▸ hc')
  exact hn55_three (h2 x) (show y ∈ {y : ℝ | (x, y) ∈ Γ} from ha)
    (show y1 ∈ {y : ℝ | (x, y) ∈ Γ} from hb) (show y2 ∈ {y : ℝ | (x, y) ∈ Γ} from hb')
    hy1.symm hy2.symm hy12

theorem solution (Γ : Set (ℝ × ℝ)) (hΓ : MeasurableSet Γ)
    (h2 : ∀ x : ℝ, {y : ℝ | (x, y) ∈ Γ}.encard ≤ 2) :
    MeasurableSet (Prod.fst '' Γ) ∧
      ∃ T₁ T₂ : ℝ → ℝ, Measurable T₁ ∧ Measurable T₂ ∧
        (∀ x ∈ Prod.fst '' Γ, T₁ x ≤ T₂ x) ∧
        Γ = {p : ℝ × ℝ | p.1 ∈ Prod.fst '' Γ ∧ (p.2 = T₁ p.1 ∨ p.2 = T₂ p.1)} := by
  -- points with a smaller / larger neighbour in their fibre
  set Hi := {p : ℝ × ℝ | p ∈ Γ ∧ ∃ y', (p.1, y') ∈ Γ ∧ y' < p.2} with hHi
  set Lo := {p : ℝ × ℝ | p ∈ Γ ∧ ∃ y', (p.1, y') ∈ Γ ∧ p.2 < y'} with hLo
  have hHim : MeasurableSet Hi :=
    hn55_meas Γ hΓ h2 (fun a b => a < b)
      (measurableSet_lt (measurable_snd.comp measurable_snd) (measurable_fst.comp measurable_snd))
      (fun y => lt_irrefl y)
  have hLom : MeasurableSet Lo :=
    hn55_meas Γ hΓ h2 (fun a b => b < a)
      (measurableSet_lt (measurable_fst.comp measurable_snd) (measurable_snd.comp measurable_snd))
      (fun y => lt_irrefl y)
  set Gmin := Γ \ Hi with hGmin
  set Gmax := Γ \ Lo with hGmax
  have hGminm : MeasurableSet Gmin := hΓ.diff hHim
  have hGmaxm : MeasurableSet Gmax := hΓ.diff hLom
  -- fibre minima and maxima exist
  have hmin : ∀ x y, (x, y) ∈ Γ → ∃ y₀, (x, y₀) ∈ Gmin ∧ y₀ ≤ y := by
    intro x y hxy
    by_cases h : (x, y) ∈ Hi
    · obtain ⟨-, y', hy', hlt⟩ := h
      refine ⟨y', ⟨hy', ?_⟩, hlt.le⟩
      rintro ⟨-, y'', hy'', hlt'⟩
      exact hn55_three (h2 x) (show y ∈ {y : ℝ | (x, y) ∈ Γ} from hxy)
        (show y' ∈ {y : ℝ | (x, y) ∈ Γ} from hy') (show y'' ∈ {y : ℝ | (x, y) ∈ Γ} from hy'')
        (ne_of_gt hlt) (ne_of_gt (lt_trans hlt' hlt)) (ne_of_gt hlt')
    · exact ⟨y, ⟨hxy, h⟩, le_rfl⟩
  have hmax : ∀ x y, (x, y) ∈ Γ → ∃ y₀, (x, y₀) ∈ Gmax ∧ y ≤ y₀ := by
    intro x y hxy
    by_cases h : (x, y) ∈ Lo
    · obtain ⟨-, y', hy', hlt⟩ := h
      refine ⟨y', ⟨hy', ?_⟩, hlt.le⟩
      rintro ⟨-, y'', hy'', hlt'⟩
      exact hn55_three (h2 x) (show y ∈ {y : ℝ | (x, y) ∈ Γ} from hxy)
        (show y' ∈ {y : ℝ | (x, y) ∈ Γ} from hy') (show y'' ∈ {y : ℝ | (x, y) ∈ Γ} from hy'')
        (ne_of_lt hlt) (ne_of_lt (lt_trans hlt hlt')) (ne_of_lt hlt')
    · exact ⟨y, ⟨hxy, h⟩, le_rfl⟩
  have hinjmin : Set.InjOn Prod.fst Gmin := by
    rintro ⟨x, y⟩ ⟨h1, h1'⟩ ⟨x', y'⟩ ⟨h2', h2''⟩ he
    simp only at he
    subst he
    rcases lt_trichotomy y y' with h | h | h
    · exact absurd ⟨h2', y, h1, h⟩ h2''
    · rw [h]
    · exact absurd ⟨h1, y', h2', h⟩ h1'
  have hinjmax : Set.InjOn Prod.fst Gmax := by
    rintro ⟨x, y⟩ ⟨h1, h1'⟩ ⟨x', y'⟩ ⟨h2', h2''⟩ he
    simp only at he
    subst he
    rcases lt_trichotomy y y' with h | h | h
    · exact absurd ⟨h1, y', h2', h⟩ h1'
    · rw [h]
    · exact absurd ⟨h2', y, h1, h⟩ h2''
  have hSeq : Prod.fst '' Γ = Prod.fst '' Gmin := by
    ext x
    constructor
    · rintro ⟨⟨x', y⟩, hp, rfl⟩
      obtain ⟨y₀, hy₀, -⟩ := hmin x' y hp
      exact ⟨(x', y₀), hy₀, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, hp.1, rfl⟩
  have hSm : MeasurableSet (Prod.fst '' Γ) := by
    rw [hSeq]
    exact hGminm.image_of_continuousOn_injOn continuous_fst.continuousOn hinjmin
  -- the two Borel maps
  have e1 := ContinuousOn.measurableEmbedding hGminm continuous_fst.continuousOn hinjmin
  have e2 := ContinuousOn.measurableEmbedding hGmaxm continuous_fst.continuousOn hinjmax
  obtain ⟨T₁, hT₁m, hT₁⟩ := e1.exists_measurable_extend
    (g := fun p : Gmin => (p : ℝ × ℝ).2) (measurable_snd.comp measurable_subtype_coe)
    (fun _ => ⟨0⟩)
  obtain ⟨T₂, hT₂m, hT₂⟩ := e2.exists_measurable_extend
    (g := fun p : Gmax => (p : ℝ × ℝ).2) (measurable_snd.comp measurable_subtype_coe)
    (fun _ => ⟨0⟩)
  have hT₁v : ∀ x y, (x, y) ∈ Gmin → T₁ x = y := fun x y h =>
    congrFun hT₁ ⟨(x, y), h⟩
  have hT₂v : ∀ x y, (x, y) ∈ Gmax → T₂ x = y := fun x y h =>
    congrFun hT₂ ⟨(x, y), h⟩
  -- on `S`, `T₁ x` is the fibre minimum and `T₂ x` the fibre maximum
  have hfib : ∀ x ∈ Prod.fst '' Γ, (x, T₁ x) ∈ Gmin ∧ (x, T₂ x) ∈ Gmax := by
    rintro x ⟨⟨x', y⟩, hp, rfl⟩
    obtain ⟨y₁, hy₁, -⟩ := hmin x' y hp
    obtain ⟨y₂, hy₂, -⟩ := hmax x' y hp
    rw [hT₁v _ _ hy₁, hT₂v _ _ hy₂]
    exact ⟨hy₁, hy₂⟩
  refine ⟨hSm, T₁, T₂, hT₁m, hT₂m, ?_, ?_⟩
  · intro x hx
    obtain ⟨h1, h2'⟩ := hfib x hx
    by_contra hlt
    push Not at hlt
    exact h1.2 ⟨h1.1, T₂ x, h2'.1, hlt⟩
  · ext ⟨x, y⟩
    constructor
    · intro hp
      have hx : x ∈ Prod.fst '' Γ := ⟨(x, y), hp, rfl⟩
      refine ⟨hx, ?_⟩
      obtain ⟨h1, h2'⟩ := hfib x hx
      by_contra hne
      push Not at hne
      obtain ⟨hn1, hn2⟩ := hne
      have hle1 : T₁ x ≤ y := by
        by_contra hlt; push Not at hlt
        exact h1.2 ⟨h1.1, y, hp, hlt⟩
      have hle2 : y ≤ T₂ x := by
        by_contra hlt; push Not at hlt
        exact h2'.2 ⟨h2'.1, y, hp, hlt⟩
      have hlt1 : T₁ x < y := lt_of_le_of_ne hle1 (Ne.symm hn1)
      have hlt2 : y < T₂ x := lt_of_le_of_ne hle2 hn2
      exact hn55_three (h2 x) (show T₁ x ∈ {y : ℝ | (x, y) ∈ Γ} from h1.1)
        (show y ∈ {y : ℝ | (x, y) ∈ Γ} from hp) (show T₂ x ∈ {y : ℝ | (x, y) ∈ Γ} from h2'.1)
        (ne_of_lt hlt1) (ne_of_lt (lt_trans hlt1 hlt2)) (ne_of_lt hlt2)
    · rintro ⟨hx, hy | hy⟩
      · simp only at hy hx
        rw [hy]; exact (hfib x hx).1.1
      · simp only at hy hx
        rw [hy]; exact (hfib x hx).2.1
