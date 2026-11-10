-- Prove2me | solution 1 for GenericBudgetAudit.IdenticalPrefs.theorem_8_1_full
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-09T14:45:29.761372+00:00
-- url     : https://prove2.me/submissions/f930d203-ba57-4d63-b933-2c6786d7bbd2

import Mathlib
import Definitions.Def_GenericBudgets_AlmostEqual_Setting

set_option autoImplicit false

open scoped Classical
open GenericBudgets.AlmostEqual (bundle price IsCE)

noncomputable section

namespace GBA81F

open GenericBudgets.AlmostEqual

theorem bundle_of {m : ℕ} (S : Finset (Fin m)) (i : Fin 2) :
    ∃ σ : Fin m → Fin 2, bundle σ i = S := by
  refine ⟨fun j => if j ∈ S then i else (if i = 0 then 1 else 0), ?_⟩
  ext j
  have key : ∀ a : Fin 2, ¬ ((if a = 0 then (1 : Fin 2) else 0) = a) := by decide
  by_cases hj : j ∈ S
  · simp [bundle, hj]
  · simp only [bundle, Finset.mem_filter, Finset.mem_univ, true_and, if_neg hj]
    exact iff_of_false (key i) hj

theorem bundle_zero {m : ℕ} (σ : Fin m → Fin 2) : bundle σ 0 = (bundle σ 1)ᶜ := by
  ext j
  simp only [bundle, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]
  have key : ∀ a : Fin 2, a = 0 ↔ ¬ a = 1 := by decide
  exact key (σ j)

theorem core {m : ℕ} (w : Finset (Fin m) → ℝ) (hw0 : ∀ S, 0 ≤ w S) (hwe : w ∅ = 0)
    (hcompl : ∀ S, w Sᶜ = 1 - w S)
    (b0 b1 : ℝ) (hb0 : 0 < b0) (hb1 : 0 < b1) (hsum : b0 + b1 = 1)
    (hnex : ∀ S U : Finset (Fin m), w S < w U →
      (∀ V : Finset (Fin m), ¬ (w S < w V ∧ w V < w U)) → b0 * w U ≠ b1 * (1 - w S)) :
    ∃ S : Finset (Fin m), ∃ t : ℝ, 0 < t ∧ w S ≤ b1 * t ∧ 1 - w S ≤ b0 * t ∧
      (∀ T, w S < w T → b1 * t < w T) ∧ (∀ T, 1 - w S < w T → b0 * t < w T) ∧
      (∀ T, w T ≤ b1 → w T ≤ w S) ∧ (∀ T, w T ≤ b0 → w T ≤ 1 - w S) := by
  let L : Finset ℝ := (Finset.univ : Finset (Finset (Fin m))).image w
  have memL : ∀ S, w S ∈ L := fun S => Finset.mem_image_of_mem w (Finset.mem_univ S)
  have memL' : ∀ y ∈ L, ∃ S, w S = y := by
    intro y hy
    obtain ⟨S, -, hS⟩ := Finset.mem_image.mp hy
    exact ⟨S, hS⟩
  let P : Finset ℝ := L.filter (fun x => ∀ z ∈ L, z < x → b0 * x < b1 * (1 - z))
  have memP : ∀ S, (∀ V : Finset (Fin m), w V < w S → b0 * w S < b1 * (1 - w V)) → w S ∈ P := by
    intro S hS
    refine Finset.mem_filter.mpr ⟨memL S, ?_⟩
    intro z hz hzS
    obtain ⟨V, rfl⟩ := memL' z hz
    exact hS V hzS
  have hPne : P.Nonempty :=
    ⟨w ∅, memP ∅ (fun V hV => absurd hV (by rw [hwe]; exact not_lt.mpr (hw0 V)))⟩
  obtain ⟨S, hSx⟩ := memL' (P.max' hPne) (Finset.mem_filter.mp (P.max'_mem hPne)).1
  have hxP : ∀ V : Finset (Fin m), w V < w S → b0 * w S < b1 * (1 - w V) := by
    intro V hV
    have h := (Finset.mem_filter.mp (P.max'_mem hPne)).2 (w V) (memL V) (by rw [← hSx]; exact hV)
    rw [hSx]; exact h
  have hmax : ∀ T, w T ∈ P → w T ≤ w S := by
    intro T hT; rw [hSx]; exact P.le_max' _ hT
  obtain ⟨t, ht⟩ : ∃ t, t = max (w S / b1) ((1 - w S) / b0) := ⟨_, rfl⟩
  have hxt : w S ≤ b1 * t := by
    calc w S = b1 * (w S / b1) := by field_simp
      _ ≤ b1 * t := mul_le_mul_of_nonneg_left (by rw [ht]; exact le_max_left _ _) hb1.le
  have hyt : 1 - w S ≤ b0 * t := by
    calc 1 - w S = b0 * ((1 - w S) / b0) := by field_simp
      _ ≤ b0 * t := mul_le_mul_of_nonneg_left (by rw [ht]; exact le_max_right _ _) hb0.le
  have htt : b1 * t + b0 * t = t := by rw [← add_mul, add_comm b1, hsum, one_mul]
  have htpos : 0 < t := by linarith
  -- condition (I): the poorer agent 1 cannot afford anything better
  have hI : ∀ T, w S < w T → b1 * t < w T := by
    intro T hT
    have key : b1 * (1 - w S) < b0 * w T := by
      by_contra hcon
      push Not at hcon
      let Q : Finset ℝ := L.filter (fun y => w S < y ∧ b0 * y ≤ b1 * (1 - w S))
      have hQne : Q.Nonempty := ⟨w T, Finset.mem_filter.mpr ⟨memL T, hT, hcon⟩⟩
      obtain ⟨U, hUy⟩ := memL' (Q.min' hQne) (Finset.mem_filter.mp (Q.min'_mem hQne)).1
      have hUQ := (Finset.mem_filter.mp (Q.min'_mem hQne)).2
      rw [← hUy] at hUQ
      obtain ⟨hSU, hUle⟩ := hUQ
      have hmin : ∀ V, w S < w V → b0 * w V ≤ b1 * (1 - w S) → w U ≤ w V := by
        intro V h1 h2
        rw [hUy]
        exact Q.min'_le _ (Finset.mem_filter.mpr ⟨memL V, h1, h2⟩)
      have hcons : ∀ V : Finset (Fin m), ¬ (w S < w V ∧ w V < w U) := by
        rintro V ⟨h1, h2⟩
        have h3 : b0 * w V < b0 * w U := mul_lt_mul_of_pos_left h2 hb0
        have h4 := hmin V h1 (by linarith)
        linarith
      have hUP : w U ∈ P := by
        apply memP
        intro V hV
        rcases lt_trichotomy (w V) (w S) with h | h | h
        · have h5 : b1 * (1 - w S) < b1 * (1 - w V) := mul_lt_mul_of_pos_left (by linarith) hb1
          linarith
        · rw [h]; exact lt_of_le_of_ne hUle (hnex S U hSU hcons)
        · have h3 : b0 * w V < b0 * w U := mul_lt_mul_of_pos_left hV hb0
          have h4 := hmin V h (by linarith)
          linarith
      have := hmax U hUP
      linarith
    rw [ht, mul_max_of_nonneg _ _ hb1.le]
    apply max_lt
    · have e : b1 * (w S / b1) = w S := by field_simp
      rw [e]; exact hT
    · rw [show b1 * ((1 - w S) / b0) = b1 * (1 - w S) / b0 by ring, div_lt_iff₀ hb0]
      linarith
  -- condition (II): the richer agent 0 cannot afford anything better
  have hII : ∀ T, 1 - w S < w T → b0 * t < w T := by
    intro T hT
    have h1 : w Tᶜ < w S := by rw [hcompl]; linarith
    have key := hxP Tᶜ h1
    rw [hcompl] at key
    rw [ht, mul_max_of_nonneg _ _ hb0.le]
    apply max_lt
    · rw [show b0 * (w S / b1) = b0 * w S / b1 by ring, div_lt_iff₀ hb1]
      linarith
    · have e : b0 * ((1 - w S) / b0) = 1 - w S := by field_simp
      rw [e]; exact hT
  have hT1 : ∀ T, w T ≤ b1 → w T ≤ w S := by
    intro T hT
    apply hmax
    apply memP
    intro V hV
    have h5 : b1 * (1 - w T) < b1 * (1 - w V) := mul_lt_mul_of_pos_left (by linarith) hb1
    have hb0e : b0 = 1 - b1 := by linarith
    rw [hb0e]
    linarith
  have hT0 : ∀ T, w T ≤ b0 → w T ≤ 1 - w S := by
    intro T hT
    by_contra hcon
    push Not at hcon
    have h1 : w Tᶜ < w S := by rw [hcompl]; linarith
    have key := hxP Tᶜ h1
    rw [hcompl] at key
    have h2 : b1 * w T ≤ b1 * b0 := mul_le_mul_of_nonneg_left hT hb1.le
    have h3 : b0 * w S < b0 * b1 := by linarith
    have h4 := lt_of_mul_lt_mul_left h3 hb0.le
    linarith
  exact ⟨S, t, htpos, hxt, hyt, hI, hII, hT1, hT0⟩

end GBA81F

open scoped Classical in open GenericBudgets.AlmostEqual (bundle price IsCE) in
theorem solution {m : ℕ} :
  let IsAdditive (w : Finset (Fin m) → ℝ) : Prop :=
    (∀ j, 0 ≤ w {j}) ∧ (∀ S, w S = ∑ j ∈ S, w {j}) ∧ w Finset.univ = 1;
  let IsBudgets (b : Fin 2 → ℝ) : Prop :=
    (∀ i, 0 < b i) ∧ b 0 + b 1 = 1;
  let Efficient (v : Fin 2 → Finset (Fin m) → ℝ) (σ : Fin m → Fin 2) : Prop :=
    ∀ τ : Fin m → Fin 2, (∀ i, v i (bundle σ i) ≤ v i (bundle τ i)) →
      ∀ i, v i (bundle τ i) = v i (bundle σ i);
  let frontierLevels (v : Fin 2 → Finset (Fin m) → ℝ) (i : Fin 2) : Finset ℝ :=
    (Finset.univ.filter (Efficient v)).image (fun σ => v i (bundle σ i));
  let truncatedShare (v : Fin 2 → Finset (Fin m) → ℝ) (b : Fin 2 → ℝ)
      (i : Fin 2) : Option ℝ :=
    let levels := (frontierLevels v i).filter (fun x => x ≤ b i)
    if h : levels.Nonempty then some (levels.max' h) else none;
  let GetsTruncatedShare (v : Fin 2 → Finset (Fin m) → ℝ) (b : Fin 2 → ℝ)
      (σ : Fin m → Fin 2) (i : Fin 2) : Prop :=
    ∃ x : ℝ, truncatedShare v b i = some x ∧ x ≤ v i (bundle σ i);
  let EqualPrices (v : Fin 2 → Finset (Fin m) → ℝ) (p : Fin m → ℝ) : Prop :=
    ∀ j k, (∀ i, v i {j} = v i {k}) → p j = p k;
  let InExceptional (v : Fin 2 → Finset (Fin m) → ℝ) (b : Fin 2 → ℝ)
      (i : Fin 2) : Prop :=
    ∃ x ∈ frontierLevels v i, ∃ y ∈ frontierLevels v i, x < y ∧
      (∀ z ∈ frontierLevels v i, ¬ (x < z ∧ z < y)) ∧
      b i * (1 - x) = (1 - b i) * y;
  ∀ (v : Fin 2 → Finset (Fin m) → ℝ) (b : Fin 2 → ℝ),
    (∀ i, IsAdditive (v i)) → v 0 = v 1 → IsBudgets b → b 1 < b 0 →
    (∃ i : Fin 2, ¬ InExceptional v b i) →
    ∃ (σ : Fin m → Fin 2) (p : Fin m → ℝ),
      IsCE v b σ p ∧ EqualPrices v p ∧ ∀ j, GetsTruncatedShare v b σ j := by
  intro IsAdditive IsBudgets Efficient frontierLevels truncatedShare GetsTruncatedShare
    EqualPrices InExceptional v b hadd hv hb hlt hex
  obtain ⟨w, hw⟩ : ∃ w, v 0 = w := ⟨_, rfl⟩
  have hvi : ∀ i, v i = w := by
    rw [Fin.forall_fin_two]; exact ⟨hw, hv.symm.trans hw⟩
  obtain ⟨hw0s, hws, hw1⟩ : (∀ j, 0 ≤ v 0 {j}) ∧ (∀ S, v 0 S = ∑ j ∈ S, v 0 {j}) ∧
      v 0 Finset.univ = 1 := hadd 0
  rw [hw] at hw0s hws hw1
  obtain ⟨hbpos, hbsum⟩ : (∀ i, 0 < b i) ∧ b 0 + b 1 = 1 := hb
  have hw0 : ∀ S, 0 ≤ w S := by
    intro S; rw [hws S]; exact Finset.sum_nonneg (fun j _ => hw0s j)
  have hwe : w ∅ = 0 := by rw [hws ∅, Finset.sum_empty]
  have hcompl : ∀ S, w Sᶜ = 1 - w S := by
    intro S
    have h := Finset.sum_add_sum_compl S (fun j => w {j})
    rw [← hws, ← hws, ← hws, hw1] at h
    linarith
  have hsum01 : ∀ σ : Fin m → Fin 2, w (bundle σ 0) + w (bundle σ 1) = 1 := by
    intro σ; rw [GBA81F.bundle_zero, hcompl]; ring
  have hEff : ∀ σ, Efficient v σ := by
    intro σ
    show ∀ τ : Fin m → Fin 2, (∀ i, v i (bundle σ i) ≤ v i (bundle τ i)) →
      ∀ i, v i (bundle τ i) = v i (bundle σ i)
    intro τ hτ
    simp only [hvi] at hτ ⊢
    have h0 := hτ 0
    have h1 := hτ 1
    have s1 := hsum01 σ
    have s2 := hsum01 τ
    rw [Fin.forall_fin_two]
    constructor <;> linarith
  have memFL : ∀ i y, y ∈ frontierLevels v i ↔ ∃ S, w S = y := by
    intro i y
    show y ∈ (Finset.univ.filter (Efficient v)).image (fun σ => v i (bundle σ i)) ↔ _
    rw [Finset.mem_image]
    constructor
    · rintro ⟨σ, -, rfl⟩
      exact ⟨bundle σ i, by rw [hvi]⟩
    · rintro ⟨S, rfl⟩
      obtain ⟨σ, hσ⟩ := GBA81F.bundle_of S i
      exact ⟨σ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hEff σ⟩, by rw [hvi, hσ]⟩
  have hnex : ∀ S U : Finset (Fin m), w S < w U →
      (∀ V : Finset (Fin m), ¬ (w S < w V ∧ w V < w U)) → b 0 * w U ≠ b 1 * (1 - w S) := by
    intro S U hSU hcons heq
    rcases Fin.exists_fin_two.mp hex with h0 | h1
    · apply h0
      show ∃ x ∈ frontierLevels v 0, ∃ y ∈ frontierLevels v 0, x < y ∧
        (∀ z ∈ frontierLevels v 0, ¬ (x < z ∧ z < y)) ∧ b 0 * (1 - x) = (1 - b 0) * y
      refine ⟨w Uᶜ, (memFL 0 _).2 ⟨Uᶜ, rfl⟩, w Sᶜ, (memFL 0 _).2 ⟨Sᶜ, rfl⟩,
        by rw [hcompl, hcompl]; linarith, ?_, ?_⟩
      · intro z hz hzz
        obtain ⟨V, rfl⟩ := (memFL 0 z).1 hz
        rw [hcompl, hcompl] at hzz
        apply hcons Vᶜ
        rw [hcompl]
        constructor <;> linarith [hzz.1, hzz.2]
      · rw [hcompl, hcompl, show 1 - b 0 = b 1 by linarith]
        linarith
    · apply h1
      show ∃ x ∈ frontierLevels v 1, ∃ y ∈ frontierLevels v 1, x < y ∧
        (∀ z ∈ frontierLevels v 1, ¬ (x < z ∧ z < y)) ∧ b 1 * (1 - x) = (1 - b 1) * y
      refine ⟨w S, (memFL 1 _).2 ⟨S, rfl⟩, w U, (memFL 1 _).2 ⟨U, rfl⟩, hSU, ?_, ?_⟩
      · intro z hz
        obtain ⟨V, rfl⟩ := (memFL 1 z).1 hz
        exact hcons V
      · rw [show 1 - b 1 = b 0 by linarith]
        linarith
  obtain ⟨S, t, htpos, hxt, hyt, hI, hII, hT1, hT0⟩ :=
    GBA81F.core w hw0 hwe hcompl (b 0) (b 1) (hbpos 0) (hbpos 1) hbsum hnex
  obtain ⟨σ, hσ⟩ := GBA81F.bundle_of S 1
  have hσ0 : w (bundle σ 0) = 1 - w S := by
    have := hsum01 σ; rw [hσ] at this; linarith
  let p : Fin m → ℝ := fun j => w {j} / t
  have hprice : ∀ T, price p T = w T / t := by
    intro T
    show ∑ j ∈ T, w {j} / t = w T / t
    rw [← Finset.sum_div, ← hws]
  refine ⟨σ, p, ⟨fun j => div_nonneg (hw0s j) htpos.le, ?_⟩, ?_, ?_⟩
  · rw [Fin.forall_fin_two]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [hprice, hσ0, div_le_iff₀ htpos]; linarith
    · intro T hT
      rw [hvi, hσ0] at hT
      rw [hprice, lt_div_iff₀ htpos]
      exact hII T hT
    · rw [hprice, hσ, div_le_iff₀ htpos]; linarith
    · intro T hT
      rw [hvi, hσ] at hT
      rw [hprice, lt_div_iff₀ htpos]
      exact hI T hT
  · show ∀ j k, (∀ i, v i {j} = v i {k}) → p j = p k
    intro j k hjk
    have h := hjk 0
    rw [hw] at h
    show w {j} / t = w {k} / t
    rw [h]
  · have hfin : ∀ i T, w T ≤ b i → w T ≤ w (bundle σ i) := by
      rw [Fin.forall_fin_two]
      constructor
      · intro T hyb; rw [hσ0]; exact hT0 T hyb
      · intro T hyb; rw [hσ]; exact hT1 T hyb
    intro i
    show ∃ x : ℝ, truncatedShare v b i = some x ∧ x ≤ v i (bundle σ i)
    have hne : ((frontierLevels v i).filter (fun x => x ≤ b i)).Nonempty :=
      ⟨0, Finset.mem_filter.mpr ⟨(memFL i 0).2 ⟨∅, hwe⟩, (hbpos i).le⟩⟩
    refine ⟨((frontierLevels v i).filter (fun x => x ≤ b i)).max' hne, ?_, ?_⟩
    · show (if h : ((frontierLevels v i).filter (fun x => x ≤ b i)).Nonempty then
          some (((frontierLevels v i).filter (fun x => x ≤ b i)).max' h) else none) = _
      rw [dif_pos hne]
    · apply Finset.max'_le
      intro y hy
      obtain ⟨hyL, hyb⟩ := Finset.mem_filter.mp hy
      obtain ⟨T, rfl⟩ := (memFL i y).1 hyL
      rw [hvi]
      exact hfin i T hyb
