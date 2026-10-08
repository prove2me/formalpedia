-- Prove2me | solution 1 for GrahamAnomaly.General.sum_le_mul_finish
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T09:48:12.814451+00:00
-- url     : https://prove2.me/submissions/ac975ae8-d6ce-44d3-a943-0254376bf38b

import Mathlib
import Definitions.Def_GrahamAnomaly_General_Model



namespace GrahamAnomaly.General
open MeasureTheory

noncomputable def gind {r n : ℕ} {μ : Fin r → ℝ} {prec : Fin r → Fin r → Prop}
    (G : Schedule n μ prec) (j : Fin r) : ℝ → ℝ :=
  (Set.Ico (G.S j) (G.S j + μ j)).indicator (fun _ => (1:ℝ))

lemma gind_meas {r n : ℕ} {μ : Fin r → ℝ} {prec : Fin r → Fin r → Prop}
    (G : Schedule n μ prec) (j : Fin r) : Measurable (gind G j) :=
  (measurable_const.indicator measurableSet_Ico)

lemma gind_int {r n : ℕ} {μ : Fin r → ℝ} {prec : Fin r → Fin r → Prop}
    (G : Schedule n μ prec) (j : Fin r) : Integrable (gind G j) := by
  unfold gind
  rw [integrable_indicator_iff measurableSet_Ico]
  simp [IntegrableOn, integrableOn_const]

lemma gind_integral {r n : ℕ} {μ : Fin r → ℝ} {prec : Fin r → Fin r → Prop}
    (G : Schedule n μ prec) (hμ : ∀ j, 0 < μ j) (j : Fin r) : ∫ t, gind G j t = μ j := by
  unfold gind
  have := integral_indicator_const (μ := volume) (1:ℝ) (measurableSet_Ico (a := G.S j) (b := G.S j + μ j))
  rw [this]
  simp [Real.volume_real_Ico, (hμ j).le]

lemma gind_nonneg {r n : ℕ} {μ : Fin r → ℝ} {prec : Fin r → Fin r → Prop}
    (G : Schedule n μ prec) (j : Fin r) (t : ℝ) : 0 ≤ gind G j t := by
  unfold gind; apply Set.indicator_nonneg; intros; norm_num

lemma gind_eq_one {r n : ℕ} {μ : Fin r → ℝ} {prec : Fin r → Fin r → Prop}
    (G : Schedule n μ prec) (j : Fin r) (t : ℝ) (h : G.S j ≤ t ∧ t < G.S j + μ j) :
    gind G j t = 1 := by
  unfold gind; rw [Set.indicator_of_mem (by exact h)]

lemma gind_eq_zero {r n : ℕ} {μ : Fin r → ℝ} {prec : Fin r → Fin r → Prop}
    (G : Schedule n μ prec) (j : Fin r) (t : ℝ) (h : ¬ (G.S j ≤ t ∧ t < G.S j + μ j)) :
    gind G j t = 0 := by
  unfold gind; rw [Set.indicator_of_notMem (by exact h)]

/-- counting function -/
noncomputable def gcnt {r n : ℕ} {μ : Fin r → ℝ} {prec : Fin r → Fin r → Prop}
    (G : Schedule n μ prec) (t : ℝ) : ℝ := ∑ j, gind G j t

lemma gcnt_integral {r n : ℕ} {μ : Fin r → ℝ} {prec : Fin r → Fin r → Prop}
    (G : Schedule n μ prec) (hμ : ∀ j, 0 < μ j) : ∫ t, gcnt G t = ∑ j, μ j := by
  unfold gcnt
  rw [integral_finset_sum _ (fun j _ => gind_int G j)]
  exact Finset.sum_congr rfl fun j _ => gind_integral G hμ j

lemma gcnt_integrable {r n : ℕ} {μ : Fin r → ℝ} {prec : Fin r → Fin r → Prop}
    (G : Schedule n μ prec) : Integrable (gcnt G) :=
  integrable_finset_sum _ fun j _ => gind_int G j

lemma gcnt_eq_card {r n : ℕ} {μ : Fin r → ℝ} {prec : Fin r → Fin r → Prop}
    (G : Schedule n μ prec) (t : ℝ) :
    gcnt G t = ((Finset.univ.filter fun j => G.S j ≤ t ∧ t < G.S j + μ j).card : ℝ) := by
  classical
  unfold gcnt
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : G.S j ≤ t ∧ t < G.S j + μ j
  · rw [gind_eq_one G j t h]; simp [h]
  · rw [gind_eq_zero G j t h]; simp [h]

lemma gcnt_le {r n : ℕ} {μ : Fin r → ℝ} {prec : Fin r → Fin r → Prop}
    (G : Schedule n μ prec) (t : ℝ) : gcnt G t ≤ n := by
  classical
  rw [gcnt_eq_card]
  have : (Finset.univ.filter fun j => G.S j ≤ t ∧ t < G.S j + μ j).card ≤ n := by
    calc _ ≤ (Finset.univ : Finset (Fin n)).card := by
          apply Finset.card_le_card_of_injOn G.P (fun _ _ => Finset.mem_univ _)
          intro i hi j hj hij
          by_contra hne
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi hj
          rcases G.noOverlap i j hij hne with h | h <;> linarith [hi.1, hi.2, hj.1, hj.2]
      _ = n := by simp
  exact_mod_cast this

lemma gcnt_ge_of_allBusy {r n : ℕ} {μ : Fin r → ℝ} {prec : Fin r → Fin r → Prop}
    (G : Schedule n μ prec) (t : ℝ) (h : AllBusy G t) : (n : ℝ) ≤ gcnt G t := by
  classical
  rw [gcnt_eq_card]
  have : n ≤ (Finset.univ.filter fun j => G.S j ≤ t ∧ t < G.S j + μ j).card := by
    choose k hk using h
    have hinj : Function.Injective k := fun p q hpq => by
      have := (hk p).1; have h2 := (hk q).1; rw [← this, ← h2, hpq]
    calc n = (Finset.univ : Finset (Fin n)).card := by simp
      _ ≤ _ := by
        apply Finset.card_le_card_of_injOn k
        · intro p _
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, Finset.mem_filter]
          exact ⟨(hk p).2.1, (hk p).2.2⟩
        · exact hinj.injOn
  exact_mod_cast this

lemma finish_ge {r n : ℕ} {μ : Fin r → ℝ} {prec : Fin r → Fin r → Prop}
    (G : Schedule n μ prec) (j : Fin r) : G.S j + μ j ≤ G.finish := by
  unfold Schedule.finish
  rw [dif_pos ⟨j, Finset.mem_univ _⟩]
  exact Finset.le_sup' (fun j => G.S j + μ j) (Finset.mem_univ j)

lemma finish_nonneg {r n : ℕ} {μ : Fin r → ℝ} (hμ : ∀ j, 0 < μ j) {prec : Fin r → Fin r → Prop}
    (G : Schedule n μ prec) : 0 ≤ G.finish := by
  by_cases h : (Finset.univ : Finset (Fin r)).Nonempty
  · obtain ⟨j, -⟩ := h
    linarith [finish_ge G j, G.nonneg j, hμ j]
  · unfold Schedule.finish; rw [dif_neg h]

lemma gcnt_zero_outside {r n : ℕ} {μ : Fin r → ℝ} {prec : Fin r → Fin r → Prop}
    (G : Schedule n μ prec) (t : ℝ) (ht : ¬ (0 ≤ t ∧ t < G.finish)) : gcnt G t = 0 := by
  unfold gcnt
  apply Finset.sum_eq_zero
  intro j _
  apply gind_eq_zero
  rintro ⟨h1, h2⟩
  exact ht ⟨le_trans (G.nonneg j) h1, lt_of_lt_of_le h2 (finish_ge G j)⟩

theorem sum_le_mul_finish_core {r n : ℕ}
    (μ : Fin r → ℝ) (hμ : ∀ j, 0 < μ j)
    (prec : Fin r → Fin r → Prop) (G : Schedule n μ prec) :
    ∑ j, μ j ≤ (n : ℝ) * G.finish := by
  rw [← gcnt_integral G hμ]
  have h0 : ∫ t, gcnt G t = ∫ t in Set.Ico 0 G.finish, gcnt G t := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    apply gcnt_zero_outside
    intro h; exact ht h
  rw [h0]
  calc ∫ t in Set.Ico 0 G.finish, gcnt G t ≤ ∫ t in Set.Ico 0 G.finish, (n:ℝ) := by
        apply setIntegral_mono_on (gcnt_integrable G).integrableOn
        · simp [integrableOn_const]
        · exact measurableSet_Ico
        · intro t _; exact gcnt_le G t
    _ = n * G.finish := by
        simp [Measure.real, Real.volume_Ico, finish_nonneg hμ G, mul_comm]

theorem chain_sum_le_finish_core {r n : ℕ}
    (μ μ' : Fin r → ℝ) (hμ : ∀ j, 0 < μ j)
    (hle : ∀ j, μ' j ≤ μ j)
    (prec prec' : Fin r → Fin r → Prop)
    [IsStrictOrder (Fin r) prec] [IsStrictOrder (Fin r) prec']
    (hsub : ∀ i j, prec' i j → prec i j)
    (G : Schedule n μ prec) (c : List (Fin r)) (hc : c.Chain' prec') :
    (c.map μ').sum ≤ (c.map μ).sum ∧ (c.map μ).sum ≤ G.finish := by
  constructor
  · apply List.sum_le_sum
    intro x _; exact hle x
  · have key : ∀ (t : List (Fin r)) (a : Fin r), List.Chain' prec' (a :: t) →
        G.S a + ((a :: t).map μ).sum ≤ G.finish := by
      intro t
      induction t with
      | nil => intro a _; simpa using finish_ge G a
      | cons b t ih =>
        intro a h
        have hab : prec' a b := (List.isChain_cons_cons.1 h).1
        have hb := ih b (List.isChain_cons_cons.1 h).2
        have := G.precedence a b (hsub a b hab)
        simp only [List.map_cons, List.sum_cons] at hb ⊢
        linarith
    cases c with
    | nil => simpa using finish_nonneg hμ G
    | cons a t => linarith [key t a hc, G.nonneg a]


noncomputable def lsum {r n : ℕ} {μ : Fin r → ℝ} {prec : Fin r → Fin r → Prop}
    (G : Schedule n μ prec) (c : List (Fin r)) (t : ℝ) : ℝ := (c.map fun a => gind G a t).sum

lemma lsum_props {r n : ℕ} {μ : Fin r → ℝ} {prec : Fin r → Fin r → Prop}
    (G : Schedule n μ prec) (hμ : ∀ j, 0 < μ j) (c : List (Fin r)) :
    Integrable (lsum G c) ∧ ∫ t, lsum G c t = (c.map μ).sum := by
  induction c with
  | nil =>
    have : lsum G [] = fun _ => 0 := by funext t; simp [lsum]
    rw [this]; simp
  | cons a c ih =>
    have e : lsum G (a :: c) = fun t => gind G a t + lsum G c t := by
      funext t; simp [lsum]
    rw [e]
    refine ⟨(gind_int G a).add ih.1, ?_⟩
    rw [integral_add (gind_int G a) ih.1, ih.2, gind_integral G hμ]
    simp

lemma lsum_nonneg {r n : ℕ} {μ : Fin r → ℝ} {prec : Fin r → Fin r → Prop}
    (G : Schedule n μ prec) (c : List (Fin r)) (t : ℝ) : 0 ≤ lsum G c t := by
  unfold lsum
  apply List.sum_nonneg
  intro x hx
  obtain ⟨a, _, rfl⟩ := List.mem_map.1 hx
  exact gind_nonneg G a t

lemma lsum_ge {r n : ℕ} {μ : Fin r → ℝ} {prec : Fin r → Fin r → Prop}
    (G : Schedule n μ prec) (c : List (Fin r)) (t : ℝ) (a : Fin r) (ha : a ∈ c) :
    gind G a t ≤ lsum G c t := by
  unfold lsum
  apply List.single_le_sum
  · intro x hx
    obtain ⟨a, _, rfl⟩ := List.mem_map.1 hx
    exact gind_nonneg G a t
  · exact List.mem_map.2 ⟨a, ha, rfl⟩

theorem idle_time_le_core {r n' : ℕ} (hn' : 0 < n')
    (μ' : Fin r → ℝ) (hμ' : ∀ j, 0 < μ' j)
    (prec' : Fin r → Fin r → Prop) [IsStrictOrder (Fin r) prec']
    (G' : Schedule n' μ' prec') (c : List (Fin r))
    (hc : c.Chain' prec')
    (hcover : ∀ t : ℝ, 0 ≤ t → t < G'.finish → ¬ AllBusy G' t →
      ∃ a ∈ c, G'.S a ≤ t ∧ t < G'.S a + μ' a) :
    (n' : ℝ) * G'.finish - ∑ j, μ' j ≤
      ((n' : ℝ) - 1) * (c.map μ').sum := by
  obtain ⟨hli, hlint⟩ := lsum_props G' hμ' c
  have hn1 : (0:ℝ) ≤ (n':ℝ) - 1 := by
    have : (1:ℝ) ≤ n' := by exact_mod_cast hn'
    linarith
  have pt : ∀ t ∈ Set.Ico 0 G'.finish, (n':ℝ) ≤ gcnt G' t + ((n':ℝ) - 1) * lsum G' c t := by
    intro t ht
    by_cases hb : AllBusy G' t
    · have := gcnt_ge_of_allBusy G' t hb
      nlinarith [lsum_nonneg G' c t]
    · obtain ⟨a, ha, h1, h2⟩ := hcover t ht.1 ht.2 hb
      have e1 : gind G' a t = 1 := gind_eq_one G' a t ⟨h1, h2⟩
      have e2 : 1 ≤ lsum G' c t := e1 ▸ lsum_ge G' c t a ha
      have e3 : 1 ≤ gcnt G' t := by
        unfold gcnt
        calc (1:ℝ) = gind G' a t := e1.symm
          _ ≤ _ := Finset.single_le_sum (f := fun j => gind G' j t)
                (fun j _ => gind_nonneg G' j t) (Finset.mem_univ a)
      nlinarith
  have hf := finish_nonneg hμ' G'
  have step : ∫ t in Set.Ico 0 G'.finish, (n':ℝ) ≤
      ∫ t in Set.Ico 0 G'.finish, (gcnt G' t + ((n':ℝ) - 1) * lsum G' c t) := by
    apply setIntegral_mono_on
    · simp [integrableOn_const]
    · exact ((gcnt_integrable G').add (hli.const_mul _)).integrableOn
    · exact measurableSet_Ico
    · exact pt
  have i1 : ∫ t in Set.Ico 0 G'.finish, gcnt G' t ≤ ∑ j, μ' j := by
    rw [← gcnt_integral G' hμ']
    exact setIntegral_le_integral (gcnt_integrable G') (Filter.Eventually.of_forall fun t =>
      Finset.sum_nonneg fun j _ => gind_nonneg G' j t)
  have i2 : ∫ t in Set.Ico 0 G'.finish, lsum G' c t ≤ (c.map μ').sum := by
    rw [← hlint]
    exact setIntegral_le_integral hli (Filter.Eventually.of_forall fun t => lsum_nonneg G' c t)
  rw [integral_add (gcnt_integrable G').integrableOn (hli.const_mul _).integrableOn,
    integral_const_mul] at step
  have e : ∫ t in Set.Ico 0 G'.finish, (n':ℝ) = n' * G'.finish := by
    simp [Measure.real, Real.volume_Ico, hf, mul_comm]
  rw [e] at step
  nlinarith


lemma mem_of_gl {α : Type*} {l : List α} {a : α} (h : l.getLast? = some a) : a ∈ l := by
  have := List.mem_of_mem_getLast? (l := l) (a := a) (by rw [h]; rfl)
  exact this

lemma chain_claim {r n' : ℕ} (μ' : Fin r → ℝ) (hμ' : ∀ j, 0 < μ' j)
    (prec' : Fin r → Fin r → Prop) (L' : Fin r ≃ Fin r) (G' : Schedule n' μ' prec')
    (hG' : IsListSchedule L' G') :
    ∀ j, ∃ c : List (Fin r), c.Chain' prec' ∧ c.getLast? = some j ∧
      ∀ t : ℝ, 0 ≤ t → t < G'.S j → ¬ AllBusy G' t →
        ∃ a ∈ c, G'.S a ≤ t ∧ t < G'.S a + μ' a := by
  classical
  haveI : IsTrans (Fin r) (fun i j => G'.S i < G'.S j) := ⟨fun a b c h1 h2 => lt_trans h1 h2⟩
  haveI : IsIrrefl (Fin r) (fun i j => G'.S i < G'.S j) := ⟨fun a h => lt_irrefl _ h⟩
  intro j
  induction j using (Finite.wellFounded_of_trans_of_irrefl (fun i j : Fin r => G'.S i < G'.S j)).induction with
  | _ j IH =>
    by_cases hp : ∃ i, prec' i j
    · obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image (Finset.univ.filter fun i => prec' i j)
        (fun i => G'.S i + μ' i) (by obtain ⟨i, hi⟩ := hp; exact ⟨i, by simp [hi]⟩)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hmax
      have hpr := G'.precedence i j hi
      have hlt : G'.S i < G'.S j := by linarith [hμ' i]
      obtain ⟨ci, hci, hlast, hcov⟩ := IH i hlt
      refine ⟨ci ++ [j], ?_, by simp, ?_⟩
      · refine List.isChain_append.2 ⟨hci, by simp, ?_⟩
        intro x hx y hy
        rw [hlast] at hx
        simp only [Option.mem_def] at hx hy
        simp at hx hy
        subst hx; subst hy; exact hi
      · intro t ht0 htj hb
        have hnr : ¬ IsReady G' j t := fun h => hb (hG'.1 j t ht0 htj h)
        unfold IsReady at hnr
        push_neg at hnr
        obtain ⟨i', hi', hlt'⟩ := hnr
        have := hmax i' hi'
        by_cases hti : G'.S i ≤ t
        · refine ⟨i, ?_, hti, by linarith⟩
          exact List.mem_append_left _ (mem_of_gl hlast)
        · obtain ⟨a, ha, h⟩ := hcov t ht0 (by linarith) hb
          exact ⟨a, List.mem_append_left _ ha, h⟩
    · refine ⟨[j], List.isChain_singleton j, by simp, ?_⟩
      intro t ht0 htj hb
      exfalso
      apply hb
      apply hG'.1 j t ht0 htj
      intro i hi; exact absurd ⟨i, hi⟩ hp

theorem covering_chain_core {r n' : ℕ} (hr : 0 < r) (hn' : 0 < n')
    (μ' : Fin r → ℝ) (hμ' : ∀ j, 0 < μ' j)
    (prec' : Fin r → Fin r → Prop) [IsStrictOrder (Fin r) prec']
    (L' : Fin r ≃ Fin r) (G' : Schedule n' μ' prec')
    (hG' : IsListSchedule L' G') :
    ∃ c : List (Fin r), c.Chain' prec' ∧
      (∃ j ∈ c, G'.S j + μ' j = G'.finish) ∧
      ∀ t : ℝ, 0 ≤ t → t < G'.finish → ¬ AllBusy G' t →
        ∃ a ∈ c, G'.S a ≤ t ∧ t < G'.S a + μ' a := by
  have hne : (Finset.univ : Finset (Fin r)).Nonempty := ⟨⟨0, hr⟩, Finset.mem_univ _⟩
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup' hne (fun j => G'.S j + μ' j)
  have hfin : G'.finish = G'.S j + μ' j := by
    unfold Schedule.finish; rw [dif_pos hne]; exact hj
  obtain ⟨c, hc, hlast, hcov⟩ := chain_claim μ' hμ' prec' L' G' hG' j
  have hjc : j ∈ c := mem_of_gl hlast
  refine ⟨c, hc, ⟨j, hjc, hfin.symm⟩, ?_⟩
  intro t ht0 htf hb
  by_cases h : t < G'.S j
  · exact hcov t ht0 h hb
  · exact ⟨j, hjc, not_lt.1 h, by rw [← hfin]; exact htf⟩

theorem theorem_1_core {r n n' : ℕ} (hr : 0 < r) (hn : 0 < n) (hn' : 0 < n')
    (μ μ' : Fin r → ℝ) (hμ : ∀ j, 0 < μ j)
    (hμ' : ∀ j, 0 < μ' j) (hle : ∀ j, μ' j ≤ μ j)
    (prec prec' : Fin r → Fin r → Prop)
    [IsStrictOrder (Fin r) prec] [IsStrictOrder (Fin r) prec']
    (hsub : ∀ i j, prec' i j → prec i j)
    (L L' : Fin r ≃ Fin r)
    (G : Schedule n μ prec) (G' : Schedule n' μ' prec')
    (hG : IsListSchedule L G) (hG' : IsListSchedule L' G') :
    G'.finish / G.finish ≤ 1 + ((n : ℝ) - 1) / n' := by
  obtain ⟨c, hc, -, hcov⟩ := covering_chain_core hr hn' μ' hμ' prec' L' G' hG'
  have h1 := idle_time_le_core hn' μ' hμ' prec' G' c hc hcov
  obtain ⟨h2, h3⟩ := chain_sum_le_finish_core μ μ' hμ hle prec prec' hsub G c hc
  have h4 := sum_le_mul_finish_core μ hμ prec G
  have h5 : ∑ j, μ' j ≤ ∑ j, μ j := Finset.sum_le_sum fun j _ => hle j
  have hω : 0 < G.finish := by
    have : (⟨0, hr⟩ : Fin r) ∈ (Finset.univ : Finset (Fin r)) := Finset.mem_univ _
    linarith [finish_ge G ⟨0, hr⟩, G.nonneg ⟨0, hr⟩, hμ ⟨0, hr⟩]
  have hn1 : (0:ℝ) ≤ (n':ℝ) - 1 := by
    have : (1:ℝ) ≤ n' := by exact_mod_cast hn'
    linarith
  have hn'0 : (0:ℝ) < n' := by exact_mod_cast hn'
  rw [div_le_iff₀ hω]
  have key : (n':ℝ) * G'.finish ≤ ((n:ℝ) + n' - 1) * G.finish := by
    nlinarith
  have e : (1 + ((n : ℝ) - 1) / n') * G.finish = ((n:ℝ) + n' - 1) * G.finish / n' := by
    field_simp; ring
  rw [e, le_div_iff₀ hn'0]
  linarith

end GrahamAnomaly.General

open GrahamAnomaly.General


theorem solution {r n : ℕ}
    (μ : Fin r → ℝ) (hμ : ∀ j, 0 < μ j)
    (prec : Fin r → Fin r → Prop) (G : Schedule n μ prec) :
    ∑ j, μ j ≤ (n : ℝ) * G.finish := by
  exact sum_le_mul_finish_core μ hμ prec G
