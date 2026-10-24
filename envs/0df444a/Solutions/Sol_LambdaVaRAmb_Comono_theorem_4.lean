-- Prove2me | solution 1 for LambdaVaRAmb.Comono.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T05:46:23.149141+00:00
-- url     : https://prove2.me/submissions/17fad9a5-7b97-45ad-97da-b3d312c20617

import Mathlib
import Definitions.Def_LambdaVaRAmb_Comono_Setting

namespace LVaR3Aux

open LambdaVaRAmb.Robust LambdaVaRAmb.InfConv LambdaVaRAmb.Comono

lemma ereal_sum_coe {ι : Type*} (s : Finset ι) (r : ι → ℝ) :
    (((∑ i ∈ s, r i : ℝ)) : EReal) = ∑ i ∈ s, (r i : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, EReal.coe_add, ih]

lemma ereal_sum_ne_bot {ι : Type*} (s : Finset ι) (a : ι → EReal) (h : ∀ i, a i ≠ ⊥) :
    ∑ i ∈ s, a i ≠ ⊥ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert b s hb ih => rw [Finset.sum_insert hb]; exact EReal.add_ne_bot_iff.2 ⟨h b, ih⟩

lemma ereal_sum_top {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → EReal)
    (h : ∀ i, a i ≠ ⊥) (j : ι) (hj : a j = ⊤) : ∑ i, a i = ⊤ := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), hj]
  exact EReal.top_add_of_ne_bot (ereal_sum_ne_bot _ _ h)

/-- Passing from real witnesses to the `EReal` infima. -/
lemma approx {n : ℕ} (hn : 0 < n) (S : Fin n → Set ℝ) (m : EReal)
    (h1 : ∀ y : Fin n → ℝ, (∀ i, y i ∈ S i) → m ≤ ((∑ i, y i : ℝ) : EReal))
    (h2 : (∃ i, sInf ((fun x : ℝ => (x : EReal)) '' S i) = ⊥) → m = ⊥) :
    m ≤ ∑ i, sInf ((fun x : ℝ => (x : EReal)) '' S i) := by
  classical
  set a : Fin n → EReal := fun i => sInf ((fun x : ℝ => (x : EReal)) '' S i) with ha_def
  by_cases hb : ∃ i, a i = ⊥
  · rw [h2 hb]; exact bot_le
  push Not at hb
  by_cases ht : ∃ i, a i = ⊤
  · obtain ⟨j, hj⟩ := ht
    rw [ereal_sum_top a hb j hj]; exact le_top
  push Not at ht
  have hr : ∀ i, ((a i).toReal : EReal) = a i := fun i => EReal.coe_toReal (ht i) (hb i)
  have hsum : ∑ i, a i = ((∑ i, (a i).toReal : ℝ) : EReal) := by
    rw [ereal_sum_coe]; exact Finset.sum_congr rfl (fun i _ => (hr i).symm)
  rw [hsum]
  by_contra hlt
  push Not at hlt
  obtain ⟨z, hz1, hz2⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
  have hz1' : ∑ i, (a i).toReal < z := by exact_mod_cast hz1
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  set ε : ℝ := (z - ∑ i, (a i).toReal) / n with hε
  have hεpos : 0 < ε := div_pos (by linarith) hnpos
  have hy : ∀ i, ∃ y ∈ S i, y < (a i).toReal + ε := by
    intro i
    have h0 : ((a i).toReal : EReal) < (((a i).toReal + ε : ℝ) : EReal) := by
      exact_mod_cast (by linarith : (a i).toReal < (a i).toReal + ε)
    rw [hr i] at h0
    obtain ⟨_, ⟨y, hyS, rfl⟩, hlt⟩ := sInf_lt_iff.1 h0
    exact ⟨y, hyS, EReal.coe_lt_coe_iff.1 hlt⟩
  choose y hyS hylt using hy
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hlt2 : ∑ i, y i < ∑ i, ((a i).toReal + ε) :=
    Finset.sum_lt_sum_of_nonempty hne (fun i _ => hylt i)
  have heq : ∑ i, ((a i).toReal + ε) = z := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, hε]
    field_simp
    ring
  have key := h1 y hyS
  have : ((∑ i, y i : ℝ) : EReal) < (z : EReal) := by exact_mod_cast (heq ▸ hlt2)
  exact absurd (lt_trans (lt_of_le_of_lt key this) hz2) (lt_irrefl _)

/-- Comonotonic covering: one index covers the whole set. -/
lemma cover {n : ℕ} {Ω : Type*} (X : Ω → ℝ) (Xs : Fin n → Ω → ℝ) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, Monotone (f i)) (hfX : ∀ i ω, f i (X ω) = Xs i ω)
    (I : Finset (Fin n)) (hI : I.Nonempty) (y : Fin n → ℝ) (D : Set Ω)
    (hD : ∀ ω ∈ D, ∃ i ∈ I, y i < Xs i ω) :
    ∃ j ∈ I, ∀ ω ∈ D, y j < Xs j ω := by
  by_contra hcon
  push Not at hcon
  obtain ⟨j0, hj0⟩ := hI
  obtain ⟨ω0, _, _⟩ := hcon j0 hj0
  have : Nonempty Ω := ⟨ω0⟩
  choose! g hgD hgle using hcon
  obtain ⟨k, hkI, hkmin⟩ := Finset.exists_min_image I (fun j => X (g j)) ⟨j0, hj0⟩
  obtain ⟨i, hiI, hi⟩ := hD (g k) (hgD k hkI)
  have h1 : Xs i (g k) ≤ Xs i (g i) := by
    rw [← hfX i, ← hfX i]; exact hf i (hkmin i hiI)
  linarith [hgle i hiI]

lemma lvar_le_of_mem {Ω : Type*} [MeasurableSpace Ω] (Λ : ℝ → ℝ) (w : Set Ω → ℝ) (Z : Ω → ℝ)
    (x : ℝ) (hx : w {ω | x < Z ω} ≤ Λ x) : LVaR Λ w Z ≤ (x : EReal) :=
  sInf_le ⟨x, hx, rfl⟩

lemma le_lvar {Ω : Type*} [MeasurableSpace Ω] (Λ : ℝ → ℝ) (w : Set Ω → ℝ) (Z : Ω → ℝ)
    (c : ℝ) (h : ∀ x : ℝ, w {ω | x < Z ω} ≤ Λ x → c ≤ x) : (c : EReal) ≤ LVaR Λ w Z := by
  apply le_sInf
  rintro _ ⟨x, hx, rfl⟩
  exact EReal.coe_le_coe_iff.2 (h x hx)

lemma lvar_zero {Ω : Type*} [MeasurableSpace Ω] (Λ : ℝ → ℝ) (w : Set Ω → ℝ)
    (hΛ : InH Λ) (hw : IsCapacity w) : LVaR Λ w (fun _ => (0:ℝ)) = 0 := by
  apply le_antisymm
  · have := lvar_le_of_mem Λ w (fun _ => (0:ℝ)) 0 (by
      simp only [lt_self_iff_false, Set.ofPred_false, hw.empty]
      exact (hΛ 0).1.le)
    simpa using this
  · have := le_lvar Λ w (fun _ => (0:ℝ)) 0 (by
      intro x hx
      by_contra hneg
      push Not at hneg
      simp only [hneg, Set.ofPred_true, hw.univ] at hx
      linarith [(hΛ x).2])
    simpa using this

lemma triv_mem {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (dom : Set (Ω → ℝ))
    (hdom : IsRVDomain dom) (X : Ω → ℝ) (hX : X ∈ dom) (j : Fin n) :
    (fun i => if i = j then X else fun _ => (0:ℝ)) ∈ ComonoAllocations dom n X := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro i
    by_cases h : i = j
    · simp [h, hX]
    · simp only [h, if_false]
      exact hdom.bounded_mem _ measurable_const ⟨0, fun _ => by simp⟩
  · intro ω
    simp [ite_apply]
  · refine ⟨fun i t => if i = j then t else 0, ?_, ?_⟩
    · intro i
      by_cases h : i = j
      · simp only [h, if_true]; exact monotone_id
      · simp only [h, if_false]; exact monotone_const
    · intro i ω
      by_cases h : i = j
      · simp [h, ite_apply]
      · simp [h]
  · intro i k ω
    by_cases h1 : i = j <;> by_cases h2 : k = j <;> simp [h1, h2, mul_self_nonneg]

lemma triv_sum {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (Λ : Fin n → ℝ → ℝ)
    (w : Fin n → Set Ω → ℝ) (hΛ : ∀ i, InHI (Λ i)) (hw : ∀ i, IsCapacity (w i))
    (X : Ω → ℝ) (j : Fin n) :
    ∑ i, LVaR (Λ i) (w i) ((fun i => if i = j then X else fun _ => (0:ℝ)) i) =
      LVaR (Λ j) (w j) X := by
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp only [hij, if_false]
    exact lvar_zero _ _ (hΛ i).1 (hw i)
  · intro h; exact absurd (Finset.mem_univ j) h

lemma upper {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (dom : Set (Ω → ℝ))
    (hdom : IsRVDomain dom) (Λ : Fin n → ℝ → ℝ)
    (w : Fin n → Set Ω → ℝ) (hΛ : ∀ i, InHI (Λ i)) (hw : ∀ i, IsCapacity (w i))
    (X : Ω → ℝ) (hX : X ∈ dom) :
    comonoInfConv dom (fun i => LVaR (Λ i) (w i)) X ≤ ⨅ i, LVaR (Λ i) (w i) X := by
  apply le_iInf
  intro j
  have h := biInf_le (fun Xs => ∑ i, (fun i => LVaR (Λ i) (w i)) i (Xs i))
    (triv_mem dom hdom X hX j)
  refine h.trans (le_of_eq ?_)
  exact triv_sum Λ w hΛ hw X j

lemma main {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n)
    (dom : Set (Ω → ℝ)) (hdom : IsRVDomain dom)
    (Λ : Fin n → ℝ → ℝ) (w : Fin n → Set Ω → ℝ)
    (hΛ : ∀ i, InHI (Λ i)) (hw : ∀ i, IsCapacity (w i))
    (X : Ω → ℝ) (hX : X ∈ dom) (Xs : Fin n → Ω → ℝ) (hXs : Xs ∈ ComonoAllocations dom n X)
    (H : (∀ i, 0 ≤ LVaR (Λ i) (w i) X) ∨ (∀ i, ∀ x y, x < 0 → y < 0 → Λ i x = Λ i y)) :
    ⨅ i, LVaR (Λ i) (w i) X ≤ ∑ i, LVaR (Λ i) (w i) (Xs i) := by
  classical
  obtain ⟨⟨hmem, hsum⟩, ⟨f, hf, hfX0⟩, hsign⟩ := hXs
  have hfX : ∀ i ω, f i (X ω) = Xs i ω := fun i ω => by rw [← hsum ω]; exact hfX0 i ω
  have hXm : Measurable X := hdom.measurable X hX
  have hXsm : ∀ i, Measurable (Xs i) := fun i => hdom.measurable _ (hmem i)
  -- sign facts
  have sg1 : ∀ i ω, Xs i ω < 0 → X ω ≤ Xs i ω := by
    intro i ω hi
    have hall : ∀ j, Xs j ω ≤ 0 := by
      intro j
      by_contra hj
      push Not at hj
      have := hsign i j ω
      nlinarith
    rw [← hsum ω, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have : ∑ x ∈ Finset.univ.erase i, Xs x ω ≤ 0 := Finset.sum_nonpos (fun j _ => hall j)
    linarith
  have sg2 : ∀ i ω, X ω < 0 → Xs i ω ≤ 0 := by
    intro i ω hX0
    by_contra hi
    push Not at hi
    have hall : ∀ j, 0 ≤ Xs j ω := by
      intro j
      by_contra hj
      push Not at hj
      have := hsign i j ω
      nlinarith
    have : 0 ≤ ∑ j, Xs j ω := Finset.sum_nonneg (fun j _ => hall j)
    rw [hsum ω] at this
    linarith
  have F0 : ∀ i ω (t : ℝ), t < 0 → t < X ω → t < Xs i ω := by
    intro i ω t ht htX
    by_cases h : Xs i ω < 0
    · linarith [sg1 i ω h]
    · push Not at h; linarith
  have transfer : ∀ i (t : ℝ), t < 0 → w i {ω | t < Xs i ω} ≤ Λ i t →
      w i {ω | t < X ω} ≤ Λ i t := by
    intro i t ht h
    refine le_trans ((hw i).mono _ _ (measurableSet_lt measurable_const hXm)
      (measurableSet_lt measurable_const (hXsm i)) ?_) h
    intro ω hω; exact F0 i ω t ht hω
  apply approx hn (fun i => {x : ℝ | w i {ω | x < Xs i ω} ≤ Λ i x})
  · intro y hy
    simp only [Set.mem_ofPred_eq] at hy
    by_cases hneg : ∃ j, y j < 0
    · rcases H with H1 | H2
      · exfalso
        obtain ⟨j, hj⟩ := hneg
        have hle := lvar_le_of_mem _ _ _ _ (transfer j (y j) hj (hy j))
        have h0 := H1 j
        have : ((y j : ℝ) : EReal) < 0 := by exact_mod_cast hj
        exact absurd (lt_of_le_of_lt (h0.trans hle) this) (lt_irrefl _)
      · obtain ⟨j0, hj0⟩ := hneg
        set I : Finset (Fin n) := Finset.univ.filter (fun i => y i < 0) with hI
        have hIne : I.Nonempty := ⟨j0, by simp [hI, hj0]⟩
        set t : ℝ := ∑ i ∈ I, y i with ht
        have htneg : t < 0 := by
          have : ∑ i ∈ I, y i < ∑ i ∈ I, (0:ℝ) :=
            Finset.sum_lt_sum_of_nonempty hIne (fun i hi => by simp [hI] at hi; exact hi)
          simpa using this
        have hD : ∀ ω ∈ {ω | t < X ω}, ∃ i ∈ I, y i < Xs i ω := by
          intro ω hω
          simp only [Set.mem_ofPred_eq] at hω
          by_cases hX0 : 0 ≤ X ω
          · exact ⟨j0, by simp [hI, hj0], F0 j0 ω (y j0) hj0 (by linarith)⟩
          · push Not at hX0
            by_contra hc
            push Not at hc
            have h1 : ∑ i ∈ I, Xs i ω ≤ t := Finset.sum_le_sum hc
            have h2 : ∑ i ∈ Finset.univ.filter (fun i => ¬ y i < 0), Xs i ω ≤ 0 :=
              Finset.sum_nonpos (fun i _ => sg2 i ω hX0)
            have h3 := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => y i < 0)
              (fun i => Xs i ω)
            rw [hsum ω] at h3
            rw [← hI] at h3
            linarith
        obtain ⟨j, hjI, hjD⟩ := cover X Xs f hf hfX I hIne y _ hD
        have hyj : y j < 0 := by simpa [hI] using hjI
        have hw1 : w j {ω | t < X ω} ≤ Λ j t := by
          have hsub : {ω | t < X ω} ⊆ {ω | y j < Xs j ω} := fun ω hω => hjD ω hω
          calc w j {ω | t < X ω} ≤ w j {ω | y j < Xs j ω} :=
                (hw j).mono _ _ (measurableSet_lt measurable_const hXm)
                  (measurableSet_lt measurable_const (hXsm j)) hsub
            _ ≤ Λ j (y j) := hy j
            _ = Λ j t := H2 j (y j) t hyj htneg
        have hts : t ≤ ∑ i, y i := by
          have h3 := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => y i < 0) y
          have h4 : 0 ≤ ∑ i ∈ Finset.univ.filter (fun i => ¬ y i < 0), y i :=
            Finset.sum_nonneg (fun i hi => by simp at hi; exact hi)
          rw [← hI] at h3
          linarith
        calc ⨅ i, LVaR (Λ i) (w i) X ≤ LVaR (Λ j) (w j) X := iInf_le _ j
          _ ≤ (t : EReal) := lvar_le_of_mem _ _ _ _ hw1
          _ ≤ ((∑ i, y i : ℝ) : EReal) := by exact_mod_cast hts
    · push Not at hneg
      set s : ℝ := ∑ i, y i with hs
      have hIne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
      have hD : ∀ ω ∈ {ω | s < X ω}, ∃ i ∈ Finset.univ, y i < Xs i ω := by
        intro ω hω
        simp only [Set.mem_ofPred_eq] at hω
        by_contra hc
        push Not at hc
        have : ∑ i, Xs i ω ≤ s := Finset.sum_le_sum (fun i _ => hc i (Finset.mem_univ i))
        rw [hsum ω] at this
        linarith
      obtain ⟨j, _, hjD⟩ := cover X Xs f hf hfX _ hIne y _ hD
      have hyjs : y j ≤ s := Finset.single_le_sum (fun i _ => hneg i) (Finset.mem_univ j)
      have hw1 : w j {ω | s < X ω} ≤ Λ j s := by
        have hsub : {ω | s < X ω} ⊆ {ω | y j < Xs j ω} := fun ω hω => hjD ω hω
        calc w j {ω | s < X ω} ≤ w j {ω | y j < Xs j ω} :=
              (hw j).mono _ _ (measurableSet_lt measurable_const hXm)
                (measurableSet_lt measurable_const (hXsm j)) hsub
          _ ≤ Λ j (y j) := hy j
          _ ≤ Λ j s := (hΛ j).2 hyjs
      calc ⨅ i, LVaR (Λ i) (w i) X ≤ LVaR (Λ j) (w j) X := iInf_le _ j
        _ ≤ (s : EReal) := lvar_le_of_mem _ _ _ _ hw1
  · rintro ⟨i, hi⟩
    rw [eq_bot_iff]
    refine (iInf_le _ i).trans ?_
    rw [le_bot_iff, EReal.eq_bot_iff_forall_lt]
    intro r
    have h0 : sInf ((fun x : ℝ => (x : EReal)) '' {x : ℝ | w i {ω | x < Xs i ω} ≤ Λ i x}) <
        ((min r 0 - 1 : ℝ) : EReal) := by
      rw [hi]; exact EReal.bot_lt_coe _
    obtain ⟨_, ⟨y, hyS, rfl⟩, hlt⟩ := sInf_lt_iff.1 h0
    have hlt' : y < min r 0 - 1 := EReal.coe_lt_coe_iff.1 hlt
    have hyneg : y < 0 := by linarith [min_le_right r 0]
    have hle := lvar_le_of_mem _ _ _ _ (transfer i y hyneg hyS)
    refine lt_of_le_of_lt hle ?_
    have : y < r := by linarith [min_le_left r 0]
    exact_mod_cast this

lemma lower {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n)
    (dom : Set (Ω → ℝ)) (hdom : IsRVDomain dom)
    (Λ : Fin n → ℝ → ℝ) (w : Fin n → Set Ω → ℝ)
    (hΛ : ∀ i, InHI (Λ i)) (hw : ∀ i, IsCapacity (w i))
    (X : Ω → ℝ) (hX : X ∈ dom)
    (H : (∀ i, 0 ≤ LVaR (Λ i) (w i) X) ∨ (∀ i, ∀ x y, x < 0 → y < 0 → Λ i x = Λ i y)) :
    ⨅ i, LVaR (Λ i) (w i) X ≤ comonoInfConv dom (fun i => LVaR (Λ i) (w i)) X := by
  unfold comonoInfConv
  refine le_iInf₂ (fun Xs hXs => ?_)
  exact main hn dom hdom Λ w hΛ hw X hX Xs hXs H

lemma eq_of {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n)
    (dom : Set (Ω → ℝ)) (hdom : IsRVDomain dom)
    (Λ : Fin n → ℝ → ℝ) (w : Fin n → Set Ω → ℝ)
    (hΛ : ∀ i, InHI (Λ i)) (hw : ∀ i, IsCapacity (w i))
    (X : Ω → ℝ) (hX : X ∈ dom)
    (H : (∀ i, 0 ≤ LVaR (Λ i) (w i) X) ∨ (∀ i, ∀ x y, x < 0 → y < 0 → Λ i x = Λ i y)) :
    comonoInfConv dom (fun i => LVaR (Λ i) (w i)) X = ⨅ i, LVaR (Λ i) (w i) X :=
  le_antisymm (upper dom hdom Λ w hΛ hw X hX) (lower hn dom hdom Λ w hΛ hw X hX H)


lemma lvar_congr {Ω : Type*} [MeasurableSpace Ω] (Λ Λ' : ℝ → ℝ) (w w' : Set Ω → ℝ) (Z : Ω → ℝ)
    (hZ : Measurable Z) (hΛ : Λ = Λ') (hw : ∀ A, MeasurableSet A → w A = w' A) :
    LVaR Λ w Z = LVaR Λ' w' Z := by
  have : ∀ x : ℝ, w {ω | x < Z ω} = w' {ω | x < Z ω} :=
    fun x => hw _ (measurableSet_lt measurable_const hZ)
  simp only [LVaR, this, hΛ]

lemma necessity {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (h2 : 2 ≤ n)
    (dom : Set (Ω → ℝ)) (hdom : IsRVDomain dom)
    (Λ : Fin n → ℝ → ℝ) (w : Fin n → Set Ω → ℝ)
    (hΛ : ∀ i, InHI (Λ i)) (hw : ∀ i, IsCapacity (w i))
    (hweq : ∀ i, ∀ A, MeasurableSet A → w i A = w ⟨0, hn⟩ A)
    (hat : IsAtomlessCapacity (w ⟨0, hn⟩)) (hΛeq : ∀ i, Λ i = Λ ⟨0, hn⟩)
    (hall : ∀ X ∈ dom, comonoInfConv dom (fun i => LVaR (Λ i) (w i)) X =
      ⨅ i, LVaR (Λ i) (w i) X) :
    ∀ x y, x < 0 → y < 0 → Λ ⟨0, hn⟩ x = Λ ⟨0, hn⟩ y := by
  classical
  have hL : InHI (Λ ⟨0, hn⟩) := hΛ ⟨0, hn⟩
  have hw0 : IsCapacity (w ⟨0, hn⟩) := hw ⟨0, hn⟩
  have key : ∀ a b, a < b → b < 0 → Λ ⟨0, hn⟩ a < Λ ⟨0, hn⟩ b → False := by
    intro a b hab hb hLab
    obtain ⟨Y, hYm, ⟨C, hC⟩, hcont⟩ := hat
    have hYb : ∀ ω, -|C| ≤ Y ω ∧ Y ω ≤ |C| := fun ω => abs_le.1 ((hC ω).trans (le_abs_self C))
    have hgl : w ⟨0, hn⟩ {ω | -|C| - 1 < Y ω} = 1 := by
      have : {ω | -|C| - 1 < Y ω} = Set.univ := by
        ext ω; simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
        linarith [(hYb ω).1]
      rw [this, hw0.univ]
    have hgr : w ⟨0, hn⟩ {ω | |C| < Y ω} = 0 := by
      have : {ω | |C| < Y ω} = ∅ := by
        ext ω; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
        exact (hYb ω).2
      rw [this, hw0.empty]
    have hq : Λ ⟨0, hn⟩ b ∈ Set.Icc ((fun x : ℝ => w ⟨0, hn⟩ {ω | x < Y ω}) |C|)
        ((fun x : ℝ => w ⟨0, hn⟩ {ω | x < Y ω}) (-|C| - 1)) := by
      simp only [hgl, hgr]; exact ⟨(hL.1 b).1.le, (hL.1 b).2.le⟩
    obtain ⟨t0, _, ht0⟩ := intermediate_value_Icc' (by linarith [abs_nonneg C])
      hcont.continuousOn hq
    have hAm : MeasurableSet {ω | t0 < Y ω} := measurableSet_lt measurable_const hYm
    have hwA : w ⟨0, hn⟩ {ω | t0 < Y ω} = Λ ⟨0, hn⟩ b := ht0
    have hTne : ({t : ℝ | Λ ⟨0, hn⟩ b ≤ Λ ⟨0, hn⟩ t}).Nonempty := ⟨b, by simp⟩
    have hTbdd : BddBelow {t : ℝ | Λ ⟨0, hn⟩ b ≤ Λ ⟨0, hn⟩ t} := ⟨a, fun t ht => by
      by_contra h; push Not at h
      have := hL.2 h.le; simp only [Set.mem_ofPred_eq] at ht; linarith⟩
    obtain ⟨τ, hτ⟩ : ∃ τ, τ = sInf {t : ℝ | Λ ⟨0, hn⟩ b ≤ Λ ⟨0, hn⟩ t} := ⟨_, rfl⟩
    have hτb : τ ≤ b := hτ ▸ csInf_le hTbdd (by simp : b ∈ {t : ℝ | Λ ⟨0, hn⟩ b ≤ Λ ⟨0, hn⟩ t})
    have hτneg : τ < 0 := lt_of_le_of_lt hτb hb
    have P1 : ∀ t, t < τ → Λ ⟨0, hn⟩ t < Λ ⟨0, hn⟩ b := by
      intro t ht; by_contra h; push Not at h
      exact absurd (hτ ▸ csInf_le hTbdd h) (not_le.2 ht)
    have P2 : ∀ t, τ < t → Λ ⟨0, hn⟩ b ≤ Λ ⟨0, hn⟩ t := by
      intro t ht
      rw [hτ] at ht
      obtain ⟨u, hu, hut⟩ := exists_lt_of_csInf_lt hTne ht
      exact le_trans hu (hL.2 hut.le)
    obtain ⟨X, hXd⟩ : ∃ X : Ω → ℝ, X = fun ω => if t0 < Y ω then 0 else 2 * τ := ⟨_, rfl⟩
    obtain ⟨Z, hZd⟩ : ∃ Z : Ω → ℝ, Z = fun ω => if t0 < Y ω then 0 else τ := ⟨_, rfl⟩
    have hXm : Measurable X := hXd ▸ Measurable.ite hAm measurable_const measurable_const
    have hZm : Measurable Z := hZd ▸ Measurable.ite hAm measurable_const measurable_const
    have hX : X ∈ dom := hdom.bounded_mem X hXm ⟨-2 * τ, fun ω => by
      rw [hXd]; dsimp only
      split_ifs
      · simp; linarith
      · rw [abs_of_neg (by linarith)]; try linarith⟩
    have hZ : Z ∈ dom := hdom.bounded_mem Z hZm ⟨-τ, fun ω => by
      rw [hZd]; dsimp only
      split_ifs
      · simp; linarith
      · rw [abs_of_neg (by linarith)]; try linarith⟩
    have h0 : (fun _ : Ω => (0:ℝ)) ∈ dom :=
      hdom.bounded_mem _ measurable_const ⟨0, fun _ => by simp⟩
    -- lower bound on ΛVaR(X)
    have hlow : (τ : EReal) ≤ LVaR (Λ ⟨0, hn⟩) (w ⟨0, hn⟩) X := by
      apply le_lvar
      intro x hx
      by_contra h; push Not at h
      by_cases hx2 : x < 2 * τ
      · have : {ω | x < X ω} = Set.univ := by
          ext ω; simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true, hXd]
          split_ifs <;> linarith
        rw [this, hw0.univ] at hx; linarith [(hL.1 x).2]
      · push Not at hx2
        have : {ω | x < X ω} = {ω | t0 < Y ω} := by
          ext ω; simp only [Set.mem_ofPred_eq, hXd]
          split_ifs with hω
          · exact iff_of_true (by linarith) hω
          · exact iff_of_false (by linarith) hω
        rw [this, hwA] at hx; linarith [P1 x h]
    -- upper bound on ΛVaR(Z)
    have hup : LVaR (Λ ⟨0, hn⟩) (w ⟨0, hn⟩) Z ≤ ((3 * τ / 4 : ℝ) : EReal) := by
      apply lvar_le_of_mem
      have : {ω | 3 * τ / 4 < Z ω} = {ω | t0 < Y ω} := by
        ext ω; simp only [Set.mem_ofPred_eq, hZd]
        split_ifs with hω
        · exact iff_of_true (by linarith) hω
        · exact iff_of_false (by linarith) hω
      rw [this, hwA]; exact P2 _ (by linarith)
    -- the allocation
    have hne : (⟨0, hn⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
    set Xs : Fin n → Ω → ℝ := fun i =>
      if i = ⟨0, hn⟩ ∨ i = ⟨1, by omega⟩ then Z else fun _ => (0:ℝ) with hXs
    have hsumXs : ∀ ω, ∑ i, Xs i ω = X ω := by
      intro ω
      rw [Fintype.sum_eq_add (⟨0, hn⟩ : Fin n) ⟨1, by omega⟩ hne]
      · simp only [hXs, true_or, or_true, if_true, hZd, hXd]
        split_ifs <;> ring
      · intro i ⟨h1, h2'⟩
        simp only [hXs, h1, h2', or_self, if_false]
    have hmem : Xs ∈ ComonoAllocations dom n X := by
      refine ⟨⟨?_, hsumXs⟩, ?_, ?_⟩
      · intro i
        simp only [hXs]
        split_ifs
        · exact hZ
        · exact h0
      · refine ⟨fun i t => if i = ⟨0, hn⟩ ∨ i = ⟨1, by omega⟩ then t / 2 else 0, ?_, ?_⟩
        · intro i
          dsimp only
          split_ifs
          · exact fun s t hst => by linarith
          · exact monotone_const
        · intro i ω
          rw [hsumXs ω]
          simp only [hXs]
          split_ifs
          · rw [hXd, hZd]; dsimp only; split_ifs <;> ring
          · rfl
      · intro i k ω
        simp only [hXs]
        split_ifs <;> simp [mul_self_nonneg]
    have hsumL : ∑ i, LVaR (Λ i) (w i) (Xs i) =
        LVaR (Λ ⟨0, hn⟩) (w ⟨0, hn⟩) Z + LVaR (Λ ⟨0, hn⟩) (w ⟨0, hn⟩) Z := by
      rw [Fintype.sum_eq_add (⟨0, hn⟩ : Fin n) ⟨1, by omega⟩ hne]
      · simp only [hXs, true_or, or_true, if_true]
        rw [lvar_congr (Λ ⟨1, by omega⟩) (Λ ⟨0, hn⟩) (w ⟨1, by omega⟩) (w ⟨0, hn⟩) Z hZm
          (hΛeq _) (hweq _)]
      · intro i ⟨h1, h2'⟩
        simp only [hXs, h1, h2', or_self, if_false]
        exact lvar_zero _ _ (hΛ i).1 (hw i)
    have hcic : comonoInfConv dom (fun i => LVaR (Λ i) (w i)) X ≤
        LVaR (Λ ⟨0, hn⟩) (w ⟨0, hn⟩) Z + LVaR (Λ ⟨0, hn⟩) (w ⟨0, hn⟩) Z := by
      have h := biInf_le (fun Xs => ∑ i, (fun i => LVaR (Λ i) (w i)) i (Xs i)) hmem
      exact h.trans (le_of_eq hsumL)
    have hinf : (τ : EReal) ≤ ⨅ i, LVaR (Λ i) (w i) X := by
      apply le_iInf
      intro i
      rw [lvar_congr (Λ i) (Λ ⟨0, hn⟩) (w i) (w ⟨0, hn⟩) X hXm (hΛeq i) (hweq i)]
      exact hlow
    have hfin : (τ : EReal) ≤ ((3 * τ / 4 + 3 * τ / 4 : ℝ) : EReal) := by
      rw [EReal.coe_add]
      calc (τ : EReal) ≤ ⨅ i, LVaR (Λ i) (w i) X := hinf
        _ = comonoInfConv dom (fun i => LVaR (Λ i) (w i)) X := (hall X hX).symm
        _ ≤ _ := hcic
        _ ≤ _ := add_le_add hup hup
    have := EReal.coe_le_coe_iff.1 hfin
    linarith
  intro x y hx hy
  by_contra hne
  rcases lt_trichotomy x y with h | h | h
  · exact key x y h hy (lt_of_le_of_ne (hL.2 h.le) hne)
  · exact hne (h ▸ rfl)
  · exact key y x h hx (lt_of_le_of_ne (hL.2 h.le) (Ne.symm hne))

end LVaR3Aux

open LambdaVaRAmb.Comono

theorem solution {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n)
    (dom : Set (Ω → ℝ)) (hdom : LambdaVaRAmb.InfConv.IsRVDomain dom)
    (Λ : Fin n → ℝ → ℝ) (w : Fin n → Set Ω → ℝ)
    (hΛ : ∀ i, LambdaVaRAmb.Robust.InHI (Λ i)) (hw : ∀ i, LambdaVaRAmb.InfConv.IsContinuousCapacity (w i)) :
    (∀ X ∈ dom, (∀ i, 0 ≤ LambdaVaRAmb.Robust.LVaR (Λ i) (w i) X) →
      comonoInfConv dom (fun i => LambdaVaRAmb.Robust.LVaR (Λ i) (w i)) X = ⨅ i, LambdaVaRAmb.Robust.LVaR (Λ i) (w i) X ∧
      ∀ i₀ : Fin n, LambdaVaRAmb.Robust.LVaR (Λ i₀) (w i₀) X = ⨅ i, LambdaVaRAmb.Robust.LVaR (Λ i) (w i) X →
        IsComonoOptimal dom (fun i => LambdaVaRAmb.Robust.LVaR (Λ i) (w i)) X
          (fun i => if i = i₀ then X else fun _ => 0)) ∧
    ((∀ i, ∀ x y, x < 0 → y < 0 → Λ i x = Λ i y) →
      ∀ X ∈ dom, comonoInfConv dom (fun i => LambdaVaRAmb.Robust.LVaR (Λ i) (w i)) X = ⨅ i, LambdaVaRAmb.Robust.LVaR (Λ i) (w i) X) ∧
    (2 ≤ n → (∀ i, ∀ A, MeasurableSet A → w i A = w ⟨0, hn⟩ A) →
      IsAtomlessCapacity (w ⟨0, hn⟩) → (∀ i, Λ i = Λ ⟨0, hn⟩) →
      ((∀ X ∈ dom, comonoInfConv dom (fun i => LambdaVaRAmb.Robust.LVaR (Λ i) (w i)) X = ⨅ i, LambdaVaRAmb.Robust.LVaR (Λ i) (w i) X) ↔
        ∀ x y, x < 0 → y < 0 → Λ ⟨0, hn⟩ x = Λ ⟨0, hn⟩ y)) := by
  have hw' : ∀ i, LambdaVaRAmb.Robust.IsCapacity (w i) := fun i => (hw i).1
  refine ⟨?_, ?_, ?_⟩
  · intro X hX hnn
    have heq := LVaR3Aux.eq_of hn dom hdom Λ w hΛ hw' X hX (Or.inl hnn)
    refine ⟨heq, fun i₀ hi₀ => ⟨LVaR3Aux.triv_mem dom hdom X hX i₀, ?_⟩⟩
    have h := LVaR3Aux.triv_sum Λ w hΛ hw' X i₀
    simp only at h ⊢
    rw [h, heq, hi₀]
  · intro hc X hX
    exact LVaR3Aux.eq_of hn dom hdom Λ w hΛ hw' X hX (Or.inr hc)
  · intro h2 hweq hat hΛeq
    constructor
    · exact LVaR3Aux.necessity hn h2 dom hdom Λ w hΛ hw' hweq hat hΛeq
    · intro hc X hX
      exact LVaR3Aux.eq_of hn dom hdom Λ w hΛ hw' X hX
        (Or.inr (fun i x y hx hy => by rw [hΛeq i]; exact hc x y hx hy))
