-- Prove2me | solution 1 for KServer.server_to_evader_reduction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-01T08:51:01.711193+00:00
-- url     : https://prove2.me/submissions/3ac1164a-ef99-4f87-92f9-e2eda4b1f3bd

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_encoding

open KServer

private theorem cost_concat {k : ℕ} {M : Type*} [MetricSpace M]
    (X : OnlineAlgorithm k M) (l : List M) (r : M) :
    X.cost (l ++ [r]) = X.cost l + moveCost (X.conf l) (X.conf (l ++ [r])) := by
  unfold OnlineAlgorithm.cost
  have hlen : (l ++ [r]).length = l.length + 1 := by simp
  rw [hlen, Finset.sum_range_succ]
  congr 1
  · refine Finset.sum_congr rfl ?_
    intro j hj
    simp only [Finset.mem_range] at hj
    rw [List.take_append_of_le_length (by omega), List.take_append_of_le_length (by omega)]
  · rw [List.take_append_of_le_length (le_refl _), List.take_length,
      List.take_of_length_le (by simp)]

private theorem ecost_concat {M : Type*} [MetricSpace M]
    (E : EvaderAlgorithm M) (l : List (Set M)) (S : Set M) :
    E.cost (l ++ [S]) = E.cost l + dist (E.pos l) (E.pos (l ++ [S])) := by
  unfold EvaderAlgorithm.cost
  have hlen : (l ++ [S]).length = l.length + 1 := by simp
  rw [hlen, Finset.sum_range_succ]
  congr 1
  · refine Finset.sum_congr rfl ?_
    intro j hj
    simp only [Finset.mem_range] at hj
    rw [List.take_append_of_le_length (by omega), List.take_append_of_le_length (by omega)]
  · rw [List.take_append_of_le_length (le_refl _), List.take_length,
      List.take_of_length_le (by simp)]

private theorem cost_mono {k : ℕ} {M : Type*} [MetricSpace M]
    (X : OnlineAlgorithm k M) (l L : List M) : X.cost l ≤ X.cost (l ++ L) := by
  induction L using List.reverseRecOn with
  | nil => simp
  | append_singleton L r ih =>
    have h := cost_concat X (l ++ L) r
    have hmc : 0 ≤ moveCost (X.conf (l ++ L)) (X.conf (l ++ L ++ [r])) :=
      Finset.sum_nonneg fun _ _ => dist_nonneg
    rw [← List.append_assoc]
    linarith

private theorem encBlock_nodup {M : Type*} [Fintype M] (S : Set M) :
    (encBlock M S).Nodup := by
  unfold encBlock
  exact Finset.nodup_toList _

/-- **The k-server to evader reduction (online direction)** on a space of `k + 1`
points: from a lazy simple k-server algorithm one extracts an evader algorithm
whose cost on any request sequence is at most four times the server cost on the
encoded sequence, starting at the initial hole. -/
theorem solution (k : ℕ) (M : Type*) [MetricSpace M] [Fintype M]
    (hcard : Fintype.card M = k + 1)
    (δ Δ : ℝ) (hδ0 : 0 < δ) (hδ : ∀ x y : M, x ≠ y → δ ≤ dist x y)
    (hΔ : ∀ x y : M, dist x y ≤ Δ) (R : ℕ) (hR : Δ ≤ R * δ)
    (B : OnlineAlgorithm k M)
    (hBinj : ∀ l : List M, Function.Injective (B.conf l))
    (hlazy : ∀ (l : List M) (r : M), (∃ i, B.conf l i = r) → B.conf (l ++ [r]) = B.conf l)
    (hlazy2 : ∀ (l : List M) (r : M), ∃ i : Fin k,
      B.conf (l ++ [r]) = Function.update (B.conf l) i r) :
    ∃ E : EvaderAlgorithm M,
      (E.pos [] ∉ Set.range (B.conf [])) ∧
      ∀ σ : List (Set M), E.cost σ ≤ 4 * B.cost (encSeq M R σ) := by
  classical
  -- the unique hole of each configuration
  have exu : ∀ l : List M, ∃! x : M, x ∉ Set.range (B.conf l) := by
    intro l
    have hcardim : (Finset.univ.image (B.conf l)).card = k := by
      rw [Finset.card_image_of_injective _ (hBinj l), Finset.card_univ, Fintype.card_fin]
    have hcompl : ((Finset.univ.image (B.conf l))ᶜ : Finset M).card = 1 := by
      rw [Finset.card_compl, hcardim, hcard]
      omega
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcompl
    refine ⟨a, ?_, ?_⟩
    · have h1 : a ∈ (Finset.univ.image (B.conf l))ᶜ := by
        rw [ha]; exact Finset.mem_singleton_self a
      rw [Finset.mem_compl] at h1
      rintro ⟨i, hi⟩
      exact h1 (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩)
    · intro y hy
      have h1 : y ∈ (Finset.univ.image (B.conf l))ᶜ := by
        rw [Finset.mem_compl, Finset.mem_image]
        rintro ⟨i, -, hi⟩
        exact hy ⟨i, hi⟩
      rw [ha, Finset.mem_singleton] at h1
      exact h1
  set hb : List M → M := fun l => (exu l).choose with hhbdef
  have spec1 : ∀ l : List M, hb l ∉ Set.range (B.conf l) := fun l => (exu l).choose_spec.1
  have spec2 : ∀ (l : List M) (y : M), y ∉ Set.range (B.conf l) → y = hb l :=
    fun l => (exu l).choose_spec.2
  have hhb_congr : ∀ l l' : List M, B.conf l' = B.conf l → hb l' = hb l := by
    intro l l' he
    refine spec2 l (hb l') ?_
    rw [← he]
    exact spec1 l'
  -- a request away from the hole is covered and free
  have step_ne : ∀ (l : List M) (r : M), r ≠ hb l →
      B.conf (l ++ [r]) = B.conf l ∧ B.cost (l ++ [r]) = B.cost l := by
    intro l r hr
    have hcov : ∃ i, B.conf l i = r := by
      by_contra hc
      exact hr (spec2 l r (fun ⟨i, hi⟩ => hc ⟨i, hi⟩))
    have hstep := hlazy l r hcov
    refine ⟨hstep, ?_⟩
    rw [cost_concat B l r, hstep]
    have : moveCost (B.conf l) (B.conf l) = 0 := by
      unfold moveCost; simp
    rw [this, add_zero]
  -- a request at the hole moves it, paying exactly the hole's displacement
  have step_hit : ∀ l : List M,
      hb (l ++ [hb l]) ≠ hb l ∧
      B.cost (l ++ [hb l]) = B.cost l + dist (hb l) (hb (l ++ [hb l])) := by
    intro l
    obtain ⟨i, hi⟩ := hlazy2 l (hb l)
    have hxr : B.conf l i ≠ hb l := fun hc => (spec1 l) ⟨i, hc⟩
    have hxnew : B.conf l i ∉ Set.range (B.conf (l ++ [hb l])) := by
      rw [hi]
      rintro ⟨j, hj⟩
      by_cases hji : j = i
      · rw [hji, Function.update_self] at hj
        exact hxr hj.symm
      · rw [Function.update_of_ne hji] at hj
        exact hji (hBinj l hj)
    have hnew : hb (l ++ [hb l]) = B.conf l i := (spec2 (l ++ [hb l]) _ hxnew).symm
    constructor
    · rw [hnew]; exact fun hc => hxr hc
    · rw [cost_concat B l (hb l), hi, hnew]
      congr 1
      unfold moveCost
      rw [Finset.sum_eq_single i
        (fun j _ hji => by rw [Function.update_of_ne hji, dist_self])
        (fun hn => absurd (Finset.mem_univ i) hn)]
      rw [Function.update_self]
      exact dist_comm _ _
  -- the hole's displacement is dominated by the cost
  have disp : ∀ (L l : List M),
      dist (hb l) (hb (l ++ L)) ≤ B.cost (l ++ L) - B.cost l := by
    intro L
    induction L using List.reverseRecOn with
    | nil => intro l; simp
    | append_singleton L r ih =>
      intro l
      rw [← List.append_assoc]
      by_cases hr : r = hb (l ++ L)
      · subst hr
        have h := step_hit (l ++ L)
        have h1 := ih l
        calc dist (hb l) (hb (l ++ L ++ [hb (l ++ L)]))
            ≤ dist (hb l) (hb (l ++ L)) + dist (hb (l ++ L)) (hb (l ++ L ++ [hb (l ++ L)])) :=
              dist_triangle _ _ _
          _ ≤ B.cost (l ++ L ++ [hb (l ++ L)]) - B.cost l := by
              have := h.2
              linarith
      · have h := step_ne (l ++ L) r hr
        have h1 := ih l
        rw [hhb_congr (l ++ L) (l ++ L ++ [r]) h.1, h.2]
        exact h1
  -- a frozen stretch: requests avoiding the hole change nothing
  have frozen : ∀ (L l : List M), (∀ r ∈ L, r ≠ hb l) →
      B.conf (l ++ L) = B.conf l ∧ B.cost (l ++ L) = B.cost l := by
    intro L
    induction L with
    | nil => intro l _; simp
    | cons r L' ih =>
      intro l h
      have hr : r ≠ hb l := h r (by simp)
      have hstep := step_ne l r hr
      have hhb : hb (l ++ [r]) = hb l := hhb_congr l (l ++ [r]) hstep.1
      have hL' : ∀ r' ∈ L', r' ≠ hb (l ++ [r]) := by
        rw [hhb]
        exact fun r' hr' => h r' (by simp [hr'])
      have hih := ih (l ++ [r]) hL'
      have hassoc : l ++ r :: L' = (l ++ [r]) ++ L' := by simp
      rw [hassoc]
      exact ⟨hih.1.trans hstep.1, hih.2.trans hstep.2⟩
  -- one pass with the hole outside `S` costs at least `δ`
  have passC : ∀ (l : List M) (S : Set M), hb l ∉ S →
      B.cost l + δ ≤ B.cost (l ++ encBlock M S) := by
    intro l S hS
    have hmem : hb l ∈ encBlock M S := (mem_encBlock S _).mpr hS
    obtain ⟨L₁, L₂, hsplit⟩ := List.append_of_mem hmem
    have hnd : (encBlock M S).Nodup := encBlock_nodup S
    rw [hsplit] at hnd
    have hnotin : hb l ∉ L₁ := by
      intro hc
      exact List.disjoint_of_nodup_append hnd hc (by simp)
    have hfroz := frozen L₁ l (fun r hr hc => hnotin (hc ▸ hr))
    have hhb1 : hb (l ++ L₁) = hb l := hhb_congr l (l ++ L₁) hfroz.1
    have hhit := step_hit (l ++ L₁)
    have hδstep : δ ≤ dist (hb (l ++ L₁)) (hb (l ++ L₁ ++ [hb (l ++ L₁)])) :=
      hδ _ _ (Ne.symm hhit.1)
    have hmono := cost_mono B (l ++ L₁ ++ [hb (l ++ L₁)]) L₂
    have hcost1 : B.cost (l ++ L₁ ++ [hb (l ++ L₁)])
        = B.cost l + dist (hb (l ++ L₁)) (hb (l ++ L₁ ++ [hb (l ++ L₁)])) := by
      rw [hhit.2, hfroz.2]
    have heq : l ++ encBlock M S = l ++ L₁ ++ [hb (l ++ L₁)] ++ L₂ := by
      rw [hsplit, hhb1]
      simp
    rw [heq]
    linarith
  -- staying inside `S`: all passes are frozen
  have frozenS : ∀ (R' : ℕ) (l : List M) (S : Set M), hb l ∈ S →
      B.conf (l ++ (List.replicate R' (encBlock M S)).flatten) = B.conf l ∧
      B.cost (l ++ (List.replicate R' (encBlock M S)).flatten) = B.cost l := by
    intro R'
    induction R' with
    | zero => intro l S _; simp
    | succ R' ih =>
      intro l S hS
      have hflat : (List.replicate (R' + 1) (encBlock M S)).flatten
          = encBlock M S ++ (List.replicate R' (encBlock M S)).flatten := by
        rw [List.replicate_succ, List.flatten_cons]
      have hfroz := frozen (encBlock M S) l
        (fun r hr hc => (mem_encBlock S r).mp hr (by rw [hc]; exact hS))
      have hhb1 : hb (l ++ encBlock M S) = hb l := hhb_congr l _ hfroz.1
      have hS1 : hb (l ++ encBlock M S) ∈ S := by rw [hhb1]; exact hS
      have hih := ih (l ++ encBlock M S) S hS1
      rw [hflat, ← List.append_assoc]
      exact ⟨hih.1.trans hfroz.1, hih.2.trans hfroz.2⟩
  -- a block of `R` passes either drives the hole into `S` or pays `R·δ`
  have blockF : ∀ (R' : ℕ) (l : List M) (S : Set M),
      hb (l ++ (List.replicate R' (encBlock M S)).flatten) ∈ S ∨
      B.cost l + R' * δ ≤ B.cost (l ++ (List.replicate R' (encBlock M S)).flatten) := by
    intro R'
    induction R' with
    | zero =>
      intro l S
      right
      simp
    | succ R' ih =>
      intro l S
      have hflat : (List.replicate (R' + 1) (encBlock M S)).flatten
          = encBlock M S ++ (List.replicate R' (encBlock M S)).flatten := by
        rw [List.replicate_succ, List.flatten_cons]
      by_cases hS : hb l ∈ S
      · left
        have hfr := frozenS (R' + 1) l S hS
        have : hb (l ++ (List.replicate (R' + 1) (encBlock M S)).flatten) = hb l :=
          hhb_congr l _ hfr.1
        rw [this]
        exact hS
      · have hp := passC l S hS
        have hih := ih (l ++ encBlock M S) S
        rw [hflat, ← List.append_assoc]
        rcases hih with h | h
        · left; exact h
        · right
          have hmono := cost_mono B l (encBlock M S)
          have hcast : ((R' : ℝ) + 1) * δ = R' * δ + δ := by ring
          push_cast
          linarith
  -- the block form of the encoding
  have hencstep : ∀ (σ : List (Set M)) (S : Set M),
      encSeq M R (σ ++ [S]) = encSeq M R σ ++ (List.replicate R (encBlock M S)).flatten := by
    intro σ S
    rw [encSeq_append, encSeq_singleton]
  -- the evader: the hole, adjusted into the last requested set
  set adj : List (Set M) → M := fun σ =>
    match σ.getLast? with
    | none => hb (encSeq M R σ)
    | some S =>
      if hS : S.Nonempty then
        (if hb (encSeq M R σ) ∈ S then hb (encSeq M R σ) else hS.some)
      else hb (encSeq M R σ)
    with hadjdef
  have hadj_nil : adj [] = hb [] := by
    rw [hadjdef]
    rfl
  have hadj_concat : ∀ (σ : List (Set M)) (S : Set M),
      adj (σ ++ [S]) = if hS : S.Nonempty then
          (if hb (encSeq M R (σ ++ [S])) ∈ S then hb (encSeq M R (σ ++ [S])) else hS.some)
        else hb (encSeq M R (σ ++ [S])) := by
    intro σ S
    rw [hadjdef]
    simp only [List.getLast?_concat]
  have hserves : ∀ (l : List (Set M)) (S : Set M), S.Nonempty → adj (l ++ [S]) ∈ S := by
    intro l S hS
    rw [hadj_concat l S, dif_pos hS]
    by_cases h : hb (encSeq M R (l ++ [S])) ∈ S
    · rw [if_pos h]; exact h
    · rw [if_neg h]; exact hS.some_mem
  -- the adjustment is paid for by the block
  have hadjb : ∀ (σ : List (Set M)) (S : Set M),
      dist (adj (σ ++ [S])) (hb (encSeq M R (σ ++ [S])))
        ≤ B.cost (encSeq M R (σ ++ [S])) - B.cost (encSeq M R σ) := by
    intro σ S
    have hnn : 0 ≤ B.cost (encSeq M R (σ ++ [S])) - B.cost (encSeq M R σ) := by
      have := cost_mono B (encSeq M R σ) ((List.replicate R (encBlock M S)).flatten)
      rw [← hencstep σ S] at this
      linarith
    rw [hadj_concat σ S]
    by_cases hS : S.Nonempty
    · rw [dif_pos hS]
      by_cases h : hb (encSeq M R (σ ++ [S])) ∈ S
      · rw [if_pos h, dist_self]
        exact hnn
      · rw [if_neg h]
        have hbf := blockF R (encSeq M R σ) S
        rw [← hencstep σ S] at hbf
        rcases hbf with hbf | hbf
        · exact absurd hbf h
        · calc dist hS.some (hb (encSeq M R (σ ++ [S]))) ≤ Δ := hΔ _ _
            _ ≤ R * δ := hR
            _ ≤ B.cost (encSeq M R (σ ++ [S])) - B.cost (encSeq M R σ) := by linarith
    · rw [dif_neg hS, dist_self]
      exact hnn
  -- assemble the evader and the cost bound
  refine ⟨⟨adj, hserves⟩, ?_, ?_⟩
  · show adj [] ∉ Set.range (B.conf [])
    rw [hadj_nil]
    exact spec1 []
  · intro σ
    -- invariant: cost plus twice the standing adjustment is dominated
    have main : ∀ σ : List (Set M),
        (⟨adj, hserves⟩ : EvaderAlgorithm M).cost σ
          + 2 * dist (adj σ) (hb (encSeq M R σ)) ≤ 4 * B.cost (encSeq M R σ) := by
      intro τ
      induction τ using List.reverseRecOn with
      | nil =>
        have h1 : (⟨adj, hserves⟩ : EvaderAlgorithm M).cost [] = 0 := by
          unfold EvaderAlgorithm.cost
          simp
        have h2 : encSeq M R ([] : List (Set M)) = [] := rfl
        have h3 : B.cost [] = 0 := by
          unfold OnlineAlgorithm.cost
          simp
        rw [h1, h2, h3, hadj_nil, dist_self]
        norm_num
      | append_singleton τ S ih =>
        have hstep := ecost_concat (⟨adj, hserves⟩ : EvaderAlgorithm M) τ S
        have hpos : (⟨adj, hserves⟩ : EvaderAlgorithm M).pos = adj := rfl
        rw [hpos] at hstep
        set h₀ : M := hb (encSeq M R τ) with hh₀
        set h₁ : M := hb (encSeq M R (τ ++ [S])) with hh₁
        have hd01 : dist h₀ h₁ ≤ B.cost (encSeq M R (τ ++ [S])) - B.cost (encSeq M R τ) := by
          have := disp ((List.replicate R (encBlock M S)).flatten) (encSeq M R τ)
          rw [← hencstep τ S] at this
          exact this
        have hA₁ := hadjb τ S
        rw [← hh₁] at hA₁
        have htri : dist (adj τ) (adj (τ ++ [S]))
            ≤ dist (adj τ) h₀ + dist h₀ h₁ + dist (adj (τ ++ [S])) h₁ := by
          calc dist (adj τ) (adj (τ ++ [S]))
              ≤ dist (adj τ) h₁ + dist h₁ (adj (τ ++ [S])) := dist_triangle _ _ _
            _ ≤ dist (adj τ) h₀ + dist h₀ h₁ + dist h₁ (adj (τ ++ [S])) := by
                have := dist_triangle (adj τ) h₀ h₁
                linarith
            _ = dist (adj τ) h₀ + dist h₀ h₁ + dist (adj (τ ++ [S])) h₁ := by
                rw [dist_comm h₁ (adj (τ ++ [S]))]
        rw [hstep]
        have hc0 : 0 ≤ dist (adj τ) h₀ := dist_nonneg
        linarith
    have h := main σ
    have hd : 0 ≤ dist (adj σ) (hb (encSeq M R σ)) := dist_nonneg
    linarith
