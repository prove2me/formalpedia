-- Prove2me | solution 1 for HyperMatchDelay.Batching.condition_3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T02:05:59.874639+00:00
-- url     : https://prove2.me/submissions/0ef7ead9-4455-4b81-8529-76165f296275

import Mathlib
import Definitions.Def_HyperMatchDelay_Batching_Model

namespace HyperMatchDelay.Batching

theorem greedy_foldl_sub (l : List (Finset ℕ)) (A : Finset (Finset ℕ)) :
    A ⊆ l.foldl greedyStep A := by
  induction l generalizing A with
  | nil => exact le_rfl
  | cons x t ih =>
    simp only [List.foldl_cons]
    refine Finset.Subset.trans ?_ (ih _)
    unfold greedyStep
    split_ifs
    · exact Finset.subset_insert _ _
    · exact le_rfl

theorem greedy_foldl_sub2 (l : List (Finset ℕ)) (A : Finset (Finset ℕ)) :
    l.foldl greedyStep A ⊆ A ∪ l.toFinset := by
  induction l generalizing A with
  | nil => simp
  | cons x t ih =>
    simp only [List.foldl_cons]
    refine Finset.Subset.trans (ih _) ?_
    intro y hy
    rw [Finset.mem_union] at hy ⊢
    rcases hy with hy | hy
    · unfold greedyStep at hy
      split_ifs at hy
      · rw [Finset.mem_insert] at hy
        rcases hy with rfl | hy
        · right; simp
        · left; exact hy
      · left; exact hy
    · right; simp at hy ⊢; right; exact hy

theorem greedy_foldl_disj (l : List (Finset ℕ)) (A : Finset (Finset ℕ))
    (hA : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → Disjoint a b) :
    ∀ a ∈ l.foldl greedyStep A, ∀ b ∈ l.foldl greedyStep A, a ≠ b → Disjoint a b := by
  induction l generalizing A with
  | nil => exact hA
  | cons x t ih =>
    simp only [List.foldl_cons]
    apply ih
    unfold greedyStep
    split_ifs with h
    · intro a ha b hb hab
      rw [Finset.mem_insert] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact absurd rfl hab
      · exact h b hb
      · exact (h a ha).symm
      · exact hA a ha b hb hab
    · exact hA

theorem greedy_foldl_charge (w : Finset ℕ → ℝ) (l : List (Finset ℕ)) (A : Finset (Finset ℕ))
    (hl : l.Pairwise (fun a b => w b ≤ w a))
    (hA : ∀ a ∈ A, ∀ f ∈ l, w f ≤ w a) :
    ∀ f ∈ l, f ∈ l.foldl greedyStep A ∨
      ∃ g ∈ l.foldl greedyStep A, ¬ Disjoint f g ∧ w f ≤ w g := by
  induction l generalizing A with
  | nil => simp
  | cons x t ih =>
    intro f hf
    simp only [List.foldl_cons]
    rw [List.pairwise_cons] at hl
    rcases List.mem_cons.mp hf with rfl | hft
    · by_cases h : ∀ g ∈ A, Disjoint f g
      · left
        refine greedy_foldl_sub t _ ?_
        unfold greedyStep; rw [if_pos h]; exact Finset.mem_insert_self _ _
      · right
        push_neg at h
        obtain ⟨g, hg, hng⟩ := h
        refine ⟨g, greedy_foldl_sub t _ ?_, hng, hA g hg f (List.mem_cons_self)⟩
        unfold greedyStep
        split_ifs
        · exact Finset.mem_insert_of_mem hg
        · exact hg
    · apply ih _ hl.2 _ f hft
      intro a ha f' hf'
      unfold greedyStep at ha
      split_ifs at ha
      · rw [Finset.mem_insert] at ha
        rcases ha with rfl | ha
        · exact hl.1 f' hf'
        · exact hA a ha f' (List.mem_cons_of_mem _ hf')
      · exact hA a ha f' (List.mem_cons_of_mem _ hf')

theorem lemma_4 (k : ℕ) (hk : 1 ≤ k) (w : Finset ℕ → ℝ)
    (σ : Finset (Finset ℕ) → List (Finset ℕ)) (hσ : IsSortedOrder w σ)
    (S : Finset (Finset ℕ)) (hS : ∀ e ∈ S, e.card ≤ k ∧ 0 ≤ w e) :
    IsMatching S (greedy σ S) ∧
    ∀ M, IsMatching S M → (1 / (k : ℝ)) * weight w M ≤ weight w (greedy σ S) := by
  obtain ⟨hnd, hts, hpw⟩ := hσ S
  have hsub : greedy σ S ⊆ S := by
    have := greedy_foldl_sub2 (σ S) ∅
    rw [hts] at this
    simpa [greedy] using this
  have hdisj : ∀ a ∈ greedy σ S, ∀ b ∈ greedy σ S, a ≠ b → Disjoint a b :=
    greedy_foldl_disj (σ S) ∅ (by simp)
  refine ⟨⟨hsub, ?_⟩, ?_⟩
  · intro a ha b hb hab
    exact hdisj a ha b hb hab
  · intro M hM
    obtain ⟨hMS, hMd⟩ := hM
    have hcharge := greedy_foldl_charge w (σ S) ∅ hpw (by simp)
    have key : ∀ f ∈ M, ∃ g ∈ greedy σ S, (f = g ∨ ¬ Disjoint f g) ∧ w f ≤ w g := by
      intro f hf
      have hfl : f ∈ σ S := by rw [← List.mem_toFinset, hts]; exact hMS hf
      rcases hcharge f hfl with h | ⟨g, hg, hn, hw⟩
      · exact ⟨f, h, Or.inl rfl, le_rfl⟩
      · exact ⟨g, hg, Or.inr hn, hw⟩
    choose! φ hφ using key
    set G := greedy σ S with hG
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have step1 : weight w M ≤ ∑ f ∈ M, w (φ f) := by
      unfold weight
      exact Finset.sum_le_sum (fun f hf => (hφ f hf).2.2)
    have hfib : ∀ g ∈ G, (M.filter (fun f => φ f = g)).card ≤ k := by
      intro g hg
      by_cases hge : g = ∅
      · have : M.filter (fun f => φ f = g) ⊆ {g} := by
          intro f hf
          rw [Finset.mem_filter] at hf
          obtain ⟨hfM, hfg⟩ := hf
          have := (hφ f hfM).2.1
          rw [hfg] at this
          rcases this with h | h
          · simp [h]
          · exfalso; apply h; rw [hge]; exact Finset.disjoint_empty_right _
        calc _ ≤ ({g} : Finset (Finset ℕ)).card := Finset.card_le_card this
          _ = 1 := Finset.card_singleton _
          _ ≤ k := hk
      · have hgne : g.Nonempty := Finset.nonempty_iff_ne_empty.mpr hge
        have hnd : ∀ f ∈ M.filter (fun f => φ f = g), ¬ Disjoint f g := by
          intro f hf
          rw [Finset.mem_filter] at hf
          obtain ⟨hfM, hfg⟩ := hf
          have := (hφ f hfM).2.1
          rw [hfg] at this
          rcases this with h | h
          · rw [h]; rw [Finset.disjoint_self_iff_empty]; exact hge
          · exact h
        have hex : ∀ f ∈ M.filter (fun f => φ f = g), ∃ x, x ∈ f ∧ x ∈ g := by
          intro f hf
          have := hnd f hf
          rw [Finset.not_disjoint_iff] at this
          exact this
        choose! ψ hψ using hex
        calc (M.filter (fun f => φ f = g)).card ≤ g.card := by
              apply Finset.card_le_card_of_injOn ψ
              · intro f hf
                exact (hψ f hf).2
              · intro f1 hf1 f2 hf2 h
                by_contra hne
                have hf1' := hf1
                have hf2' := hf2
                simp only [Finset.coe_filter, Set.mem_setOf_eq] at hf1' hf2'
                have hd := hMd hf1'.1 hf2'.1 hne
                have h1 := (hψ f1 hf1).1
                have h2 := (hψ f2 hf2).1
                rw [h] at h1
                exact Finset.disjoint_left.mp hd h1 h2
          _ ≤ k := (hS g (hsub hg)).1
    have step2 : ∑ f ∈ M, w (φ f) ≤ k * weight w G := by
      rw [Finset.sum_comp]
      have himg : M.image φ ⊆ G := by
        intro g hg
        rw [Finset.mem_image] at hg
        obtain ⟨f, hf, rfl⟩ := hg
        exact (hφ f hf).1
      calc ∑ b ∈ M.image φ, (M.filter (fun f => φ f = b)).card • w b
          ≤ ∑ b ∈ G, (M.filter (fun f => φ f = b)).card • w b := by
            apply Finset.sum_le_sum_of_subset_of_nonneg himg
            intro i hi _
            exact nsmul_nonneg (hS i (hsub hi)).2 _
        _ ≤ ∑ b ∈ G, (k : ℝ) * w b := by
            apply Finset.sum_le_sum
            intro b hb
            rw [nsmul_eq_mul]
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hfib b hb) (hS b (hsub hb)).2
        _ = k * weight w G := by unfold weight; rw [Finset.mul_sum]
    calc (1 / (k : ℝ)) * weight w M ≤ (1 / (k : ℝ)) * (k * weight w G) := by
          apply mul_le_mul_of_nonneg_left (step1.trans step2)
          positivity
      _ = weight w G := by field_simp


theorem window_span (n d z : ℕ) (i : ℤ) {u v : ℕ} (hu : u ∈ window n d z i)
    (hv : v ∈ window n d z i) : (v : ℤ) - u ≤ (d : ℤ) - 1 := by
  unfold window at hu hv
  rw [Finset.mem_filter] at hu hv
  have h1 := hu.2.1
  have h2 := hv.2.2
  linarith

theorem long_edge_restricted (n d k : ℕ) (z : ℕ) (i : ℤ) (e : Finset ℕ)
    (hne : e.Nonempty) (hsub : e ⊆ window n d z i) (hlong : (d : ℤ) - k < (diam e : ℤ)) :
    (e ∩ firstK (window n d z i) k).Nonempty ∧ (e ∩ lastK (window n d z i) k).Nonempty := by
  set B := window n d z i with hB
  have hBne : B.Nonempty := hne.mono hsub
  set a := e.min' hne with ha
  set b := e.max' hne with hb
  have hdiam' : diam e = b - a := by simp [diam, hne, ha, hb]
  have hamem : a ∈ e := Finset.min'_mem e hne
  have hbmem : b ∈ e := Finset.max'_mem e hne
  have hab : a ≤ b := Finset.min'_le e b hbmem
  have haB : a ∈ B := hsub hamem
  have hbB : b ∈ B := hsub hbmem
  set lo := B.min' hBne with hlo
  set hi := B.max' hBne with hhi
  have hloB : lo ∈ B := Finset.min'_mem B hBne
  have hhiB : hi ∈ B := Finset.max'_mem B hBne
  have hlo_a : lo ≤ a := Finset.min'_le B a haB
  have hb_hi : b ≤ hi := Finset.le_max' B b hbB
  have hlo_hi := window_span n d z i hloB hhiB
  have hspan_b := window_span n d z i hloB hbB
  have hspan_a := window_span n d z i haB hhiB
  have hl : (d : ℤ) - k < (b : ℤ) - a := by
    rw [hdiam'] at hlong
    have : ((b - a : ℕ) : ℤ) = (b : ℤ) - a := by omega
    rw [this] at hlong; exact hlong
  constructor
  · refine ⟨a, Finset.mem_inter.mpr ⟨hamem, ?_⟩⟩
    unfold firstK
    rw [Finset.mem_filter]
    refine ⟨haB, ?_⟩
    have hsubs : B.filter (fun u => u < a) ⊆ Finset.Ico lo a := by
      intro u hu
      rw [Finset.mem_filter] at hu
      rw [Finset.mem_Ico]
      exact ⟨Finset.min'_le B u hu.1, hu.2⟩
    calc (B.filter (fun u => u < a)).card ≤ (Finset.Ico lo a).card := Finset.card_le_card hsubs
      _ = a - lo := Nat.card_Ico _ _
      _ < k := by omega
  · refine ⟨b, Finset.mem_inter.mpr ⟨hbmem, ?_⟩⟩
    unfold lastK
    rw [Finset.mem_filter]
    refine ⟨hbB, ?_⟩
    have hsubs : B.filter (fun u => b < u) ⊆ Finset.Ioc b hi := by
      intro u hu
      rw [Finset.mem_filter] at hu
      rw [Finset.mem_Ioc]
      exact ⟨hu.2, Finset.le_max' B u hu.1⟩
    calc (B.filter (fun u => b < u)).card ≤ (Finset.Ioc b hi).card := Finset.card_le_card hsubs
      _ = hi - b := Nat.card_Ioc _ _
      _ < k := by omega

theorem depthK_ge (σ : Finset (Finset ℕ) → List (Finset ℕ)) (w : Finset ℕ → ℝ) (k : ℕ)
    (B : Finset ℕ) (EB N : Finset (Finset ℕ))
    (hN : N ∈ restrictedMatchings EB (firstK B k) (lastK B k)) :
    weight w (N ∪ greedyAvoiding σ EB N) ≤ weight w (depthKGreedy σ w k B EB) := by
  have h := (Classical.choose_spec (Finset.exists_max_image
    (restrictedMatchings EB (firstK B k) (lastK B k))
    (fun M => weight w (M ∪ greedyAvoiding σ EB M))
    ⟨∅, empty_mem_restrictedMatchings EB _ _⟩)).2 N hN
  unfold depthKGreedy
  exact h

theorem weight_union_disj (w : Finset ℕ → ℝ) {A B : Finset (Finset ℕ)} (h : Disjoint A B) :
    weight w (A ∪ B) = weight w A + weight w B := by
  unfold weight
  exact Finset.sum_union h

theorem greedy_subset (σ : Finset (Finset ℕ) → List (Finset ℕ))
    (hσ : ∀ S, (σ S).toFinset = S) (S : Finset (Finset ℕ)) : greedy σ S ⊆ S := by
  have := greedy_foldl_sub2 (σ S) ∅
  rw [hσ S] at this
  simpa [greedy] using this

theorem disj_greedyAvoiding (σ : Finset (Finset ℕ) → List (Finset ℕ))
    (hσ : ∀ S, (σ S).toFinset = S) (EB N : Finset (Finset ℕ))
    (hne : ∀ e ∈ EB, e.Nonempty) (hN : N ⊆ EB) :
    Disjoint N (greedyAvoiding σ EB N) := by
  rw [Finset.disjoint_left]
  intro e heN heG
  have hG : e ∈ greedy σ (EB.filter (fun e => Disjoint e (vertices N))) := heG
  have h1 := greedy_subset σ hσ _ hG
  rw [Finset.mem_filter] at h1
  have h2 : e ⊆ vertices N := by
    intro x hx
    unfold vertices
    rw [Finset.mem_biUnion]
    exact ⟨e, heN, hx⟩
  have h3 : e = ∅ := by
    have := Finset.disjoint_of_subset_right h2 h1.2
    exact Finset.disjoint_self_iff_empty _ |>.mp this
  have := hne e (hN heN)
  rw [h3] at this
  exact Finset.not_nonempty_empty this

end HyperMatchDelay.Batching

open HyperMatchDelay.Batching

theorem solution (n d k : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (E : Finset (Finset ℕ))
    (w : Finset ℕ → ℝ) (hE : IsShareability n d k E w)
    (σ : Finset (Finset ℕ) → List (Finset ℕ)) (hσ : IsSortedOrder w σ)
    (Mt : Finset (Finset ℕ)) (hMt : IsMatching E Mt) (z : ℕ) (i : ℤ) :
    weight w (Mt.filter (fun e => (d : ℤ) - k < (diam e : ℤ)) ∩ batchEdges E n d z i) +
      (1 / (k : ℝ)) *
        weight w (Mt.filter (fun e => (diam e : ℤ) ≤ (d : ℤ) - k) ∩ batchEdges E n d z i) ≤
    weight w (depthKGreedy σ w k (window n d z i) (batchEdges E n d z i)) := by
  set EB := batchEdges E n d z i with hEB
  set B := window n d z i with hB
  have hEBE : EB ⊆ E := Finset.filter_subset _ _
  have hEBsub : ∀ e ∈ EB, e ⊆ B := fun e he => (Finset.mem_filter.mp he).2
  have hne : ∀ e ∈ EB, e.Nonempty := fun e he => (hE e (hEBE he)).2.1
  have hσ' : ∀ S, (σ S).toFinset = S := fun S => (hσ S).2.1
  set Nl := Mt.filter (fun e => (d : ℤ) - k < (diam e : ℤ)) ∩ EB with hNl
  set Ns := Mt.filter (fun e => (diam e : ℤ) ≤ (d : ℤ) - k) ∩ EB with hNs
  have hNlsub : Nl ⊆ EB := Finset.inter_subset_right
  have hNssub : Ns ⊆ EB := Finset.inter_subset_right
  have hMtd := hMt.2
  have hNlmem : Nl ∈ restrictedMatchings EB (firstK B k) (lastK B k) := by
    classical
    unfold restrictedMatchings
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_powerset.mpr hNlsub, ⟨hNlsub, ?_⟩, ?_⟩
    · intro a ha b hb hab
      have ha' := Finset.mem_inter.mp ha
      have hb' := Finset.mem_inter.mp hb
      exact hMtd (Finset.mem_filter.mp ha'.1).1 (Finset.mem_filter.mp hb'.1).1 hab
    · intro e he
      have he' := Finset.mem_inter.mp he
      exact long_edge_restricted n d k z i e (hne e he'.2) (hEBsub e he'.2)
        (Finset.mem_filter.mp he'.1).2
  have h1 := depthK_ge σ w k B EB Nl hNlmem
  have h2 := weight_union_disj w (disj_greedyAvoiding σ hσ' EB Nl hne hNlsub)
  -- apply lemma_4 to the avoiding edge set
  set S' := EB.filter (fun e => Disjoint e (vertices Nl)) with hS'
  have hS'sub : S' ⊆ EB := Finset.filter_subset _ _
  have hNsS' : IsMatching S' Ns := by
    refine ⟨?_, ?_⟩
    · intro e he
      have he' := Finset.mem_inter.mp he
      rw [hS', Finset.mem_filter]
      refine ⟨he'.2, ?_⟩
      unfold vertices
      rw [Finset.disjoint_biUnion_right]
      intro f hf
      have hf' := Finset.mem_inter.mp hf
      have hef : e ≠ f := by
        intro h
        have a1 := (Finset.mem_filter.mp he'.1).2
        have a2 := (Finset.mem_filter.mp hf'.1).2
        rw [h] at a1
        omega
      exact hMtd (Finset.mem_filter.mp he'.1).1 (Finset.mem_filter.mp hf'.1).1 hef
    · intro a ha b hb hab
      have ha' := Finset.mem_inter.mp ha
      have hb' := Finset.mem_inter.mp hb
      exact hMtd (Finset.mem_filter.mp ha'.1).1 (Finset.mem_filter.mp hb'.1).1 hab
  have hl4 := (lemma_4 k hk w σ hσ S' (fun e he => by
    have := hE e (hEBE (hS'sub he))
    exact ⟨this.2.2.2.1, this.2.2.2.2⟩)).2 Ns hNsS'
  have hG : greedyAvoiding σ EB Nl = greedy σ S' := rfl
  rw [hG] at h2 h1
  linarith
