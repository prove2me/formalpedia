-- Prove2me | solution 1 for NQueensComp.NPC.lemma_18
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T00:46:51.002157+00:00
-- url     : https://prove2.me/submissions/1f6e4ca2-5ddd-47a6-b108-3414c8eff45d

import Mathlib
import Definitions.Def_NQueensComp_NPC_Reductions

open NQueensComp.NPC

/-- Attacks, in integer form. -/
theorem attacks_int (q₁ q₂ : Queen) (h : Attacks q₁ q₂) :
    ¬ ((q₁.1 : ℤ) = q₂.1 ∧ (q₁.2 : ℤ) = q₂.2) ∧
    ((q₁.1 : ℤ) = q₂.1 ∨ (q₁.2 : ℤ) = q₂.2 ∨ (q₁.1 : ℤ) + q₁.2 = q₂.1 + q₂.2 ∨
      (q₁.1 : ℤ) - q₁.2 = q₂.1 - q₂.2) := by
  obtain ⟨hne, hl⟩ := h
  simp only [col, row, sumDiag, diffDiag] at hl
  refine ⟨fun h => hne (Prod.ext (by exact_mod_cast h.1) (by exact_mod_cast h.2)), ?_⟩
  rcases hl with h | h | h | h
  · exact Or.inl (by exact_mod_cast h)
  · exact Or.inr (Or.inl (by exact_mod_cast h))
  · exact Or.inr (Or.inr (Or.inl (by exact_mod_cast h)))
  · exact Or.inr (Or.inr (Or.inr h))

/-- Attacks from integer data. -/
theorem attacks_of_int (q₁ q₂ : Queen)
    (hne : ¬ ((q₁.1 : ℤ) = q₂.1 ∧ (q₁.2 : ℤ) = q₂.2))
    (hl : (q₁.1 : ℤ) = q₂.1 ∨ (q₁.2 : ℤ) = q₂.2 ∨ (q₁.1 : ℤ) + q₁.2 = q₂.1 + q₂.2 ∨
      (q₁.1 : ℤ) - q₁.2 = q₂.1 - q₂.2) : Attacks q₁ q₂ := by
  refine ⟨fun h => hne ⟨by rw [h], by rw [h]⟩, ?_⟩
  simp only [col, row, sumDiag, diffDiag]
  rcases hl with h | h | h | h
  · exact Or.inl (by exact_mod_cast h)
  · exact Or.inr (Or.inl (by exact_mod_cast h))
  · exact Or.inr (Or.inr (Or.inl (by exact_mod_cast h)))
  · exact Or.inr (Or.inr (Or.inr h))

theorem mem_QDm (M : Inst4) (hM : M.Valid) (q : Queen) (hq : q ∈ def16_QDm M) :
    ∃ d ∈ M.Dm, (q.1 : ℤ) = 6 * M.n - 3 - d ∧ (q.2 : ℤ) = 3 * M.n - 1 - 2 * d ∧
      -((M.n : ℤ) - 1) ≤ d ∧ d ≤ (M.n : ℤ) - 1 := by
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨hd1, hd2⟩ := hM.2.1 d hd
  refine ⟨d, hd, ?_, ?_, hd1, hd2⟩
  · simp only; rw [Int.toNat_of_nonneg (by omega)]
  · simp only; rw [Int.toNat_of_nonneg (by omega)]

theorem mem_QDp (M : Inst4) (hM : M.Valid) (q : Queen) (hq : q ∈ def16_QDp M) :
    ∃ d ∈ M.Dp, (q.1 : ℤ) = 2 * M.n - 2 - d ∧ (q.2 : ℤ) = M.n + 2 * d ∧
      (d : ℤ) ≤ 2 * (M.n : ℤ) - 2 := by
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hq
  have hd2 := hM.2.2 d hd
  refine ⟨d, hd, ?_, ?_, hd2⟩
  · simp only; rw [Int.toNat_of_nonneg (by omega)]
  · simp only; push_cast; ring

theorem QDm_queen_mem (M : Inst4) (d : ℤ) (hd : d ∈ M.Dm) :
    ((6 * (M.n : ℤ) - 3 - d).toNat, (3 * (M.n : ℤ) - 1 - 2 * d).toNat) ∈ def16_QDm M :=
  Finset.mem_image_of_mem _ hd

theorem QDp_queen_mem (M : Inst4) (d : ℕ) (hd : d ∈ M.Dp) :
    ((2 * (M.n : ℤ) - 2 - (d : ℤ)).toNat, M.n + 2 * d) ∈ def16_QDp M :=
  Finset.mem_image_of_mem _ hd

/-- Validity unpacked. -/
theorem valid_facts (M : Inst4) (hM : M.Valid) :
    1 ≤ M.n ∧ M.C.card = M.R.card ∧ (∀ c ∈ M.C, c < M.n) ∧ (∀ r ∈ M.R, r < M.n) := by
  obtain ⟨⟨⟨h1, _, _⟩, h2, _, h3, h4⟩, _, _⟩ := hM
  exact ⟨h1, h2, h3, h4⟩

/-- Solution facts unpacked. -/
theorem sol_facts (M : Inst4) (S : Finset Queen) (hS : M.IsSol S) :
    S.card = M.C.card ∧ NonAttacking S ∧ (∀ q ∈ S, col q ∈ M.C ∧ row q ∈ M.R) ∧
      ∀ q ∈ S, diffDiag q ∉ M.Dm ∧ sumDiag q ∉ M.Dp := by
  obtain ⟨⟨h1, _, h3, h4⟩, h5⟩ := hS
  simp only [Inst4.toInst3, Finset.card_empty, add_zero, Finset.sdiff_empty] at h1 h4
  exact ⟨h1, h3, h4, h5⟩

theorem solution (M : Inst4) (hM : M.Valid) (S₃ : Finset Queen) (hS : (def16 M).IsSol S₃) :
    M.IsSol (lemma18_map M S₃) := by
  obtain ⟨hn, hCR, hC, hR⟩ := valid_facts M hM
  obtain ⟨hcard, hPS, hNA, hcolrow⟩ := hS
  simp only [def16] at hcard hPS hNA hcolrow
  set P := def16_QDm M ∪ def16_QDp M with hP
  -- rows of P are ≥ n
  have hrowP : ∀ q ∈ P, (M.n : ℤ) ≤ q.2 := by
    intro q hq
    rcases Finset.mem_union.mp hq with hq | hq
    · obtain ⟨d, _, _, h2, h3, h4⟩ := mem_QDm M hM q hq; omega
    · obtain ⟨d, _, _, h2, _⟩ := mem_QDp M hM q hq; omega
  -- the filtered set is exactly S₃ \ P
  set F := S₃.filter (fun q => 3 * M.n - 2 ≤ q.1 ∧ q.2 < M.n) with hF
  have hFeq : F = S₃ \ P := by
    ext q
    rw [hF, Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · rintro ⟨hq, h1, h2⟩
      refine ⟨hq, fun hqP => ?_⟩
      have := hrowP q hqP
      omega
    · rintro ⟨hq, hqP⟩
      refine ⟨hq, ?_, ?_⟩
      · obtain ⟨hc, _⟩ := hcolrow q (Finset.mem_sdiff.mpr ⟨hq, hqP⟩)
        obtain ⟨c, _, hcq⟩ := Finset.mem_image.mp hc
        simp only [col] at hcq
        omega
      · obtain ⟨_, hr⟩ := hcolrow q (Finset.mem_sdiff.mpr ⟨hq, hqP⟩)
        exact hR _ hr
  have hmemF : ∀ q ∈ F, q ∈ S₃ ∧ q ∉ P ∧ 3 * M.n - 2 ≤ q.1 ∧ q.2 < M.n := by
    intro q hq
    have h1 := hFeq ▸ hq
    rw [Finset.mem_sdiff] at h1
    rw [hF, Finset.mem_filter] at hq
    exact ⟨h1.1, h1.2, hq.2.1, hq.2.2⟩
  have hinj : Set.InjOn (fun q : Queen => (q.1 - (3 * M.n - 2), q.2)) F := by
    intro a ha b hb hab
    obtain ⟨_, _, ha3, _⟩ := hmemF a ha
    obtain ⟨_, _, hb3, _⟩ := hmemF b hb
    simp only [Prod.mk.injEq] at hab
    exact Prod.ext (by omega) hab.2
  have hmemS : ∀ q ∈ lemma18_map M S₃, ∃ p ∈ F, q.1 = p.1 - (3 * M.n - 2) ∧ q.2 = p.2 := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    exact ⟨p, hp, rfl, rfl⟩
  refine ⟨⟨?_, Finset.empty_subset _, ?_, ?_⟩, ?_⟩
  · -- cardinality
    simp only [Inst4.toInst3, Finset.card_empty, add_zero]
    unfold lemma18_map
    rw [← hF, Finset.card_image_of_injOn hinj, hFeq, Finset.card_sdiff_of_subset hPS, hcard,
      Finset.card_image_of_injective _ (add_left_injective _)]
    omega
  · -- non-attacking
    intro q₁ h₁ q₂ h₂ hatt
    obtain ⟨hne, hl⟩ := attacks_int q₁ q₂ hatt
    obtain ⟨p₁, hp₁, e₁, f₁⟩ := hmemS q₁ h₁
    obtain ⟨p₂, hp₂, e₂, f₂⟩ := hmemS q₂ h₂
    obtain ⟨hp₁S, _, g₁, _⟩ := hmemF p₁ hp₁
    obtain ⟨hp₂S, _, g₂, _⟩ := hmemF p₂ hp₂
    have e₁' : (q₁.1 : ℤ) = p₁.1 - (3 * M.n - 2) := by
      rw [e₁]; push_cast [Nat.cast_sub g₁, Nat.cast_sub (by omega : 2 ≤ 3 * M.n)]; ring
    have e₂' : (q₂.1 : ℤ) = p₂.1 - (3 * M.n - 2) := by
      rw [e₂]; push_cast [Nat.cast_sub g₂, Nat.cast_sub (by omega : 2 ≤ 3 * M.n)]; ring
    have f₁' : (q₁.2 : ℤ) = p₁.2 := by rw [f₁]
    have f₂' : (q₂.2 : ℤ) = p₂.2 := by rw [f₂]
    apply hNA p₁ hp₁S p₂ hp₂S
    apply attacks_of_int
    · intro h; apply hne; omega
    · omega
  · -- columns and rows
    intro q hq
    simp only [Inst4.toInst3, Finset.sdiff_empty] at hq
    obtain ⟨p, hp, e, f⟩ := hmemS q hq
    obtain ⟨hpS, hpP, g, _⟩ := hmemF p hp
    obtain ⟨hc, hr⟩ := hcolrow p (Finset.mem_sdiff.mpr ⟨hpS, hpP⟩)
    obtain ⟨c, hcC, hcq⟩ := Finset.mem_image.mp hc
    simp only [col, row] at hcq hr ⊢
    refine ⟨?_, f ▸ hr⟩
    have : q.1 = c := by omega
    rw [this]; exact hcC
  · -- excluded diagonals
    intro q hq
    obtain ⟨p, hp, e, f⟩ := hmemS q hq
    obtain ⟨hpS, hpP, g, g'⟩ := hmemF p hp
    have e' : (q.1 : ℤ) = p.1 - (3 * M.n - 2) := by
      rw [e]; push_cast [Nat.cast_sub g, Nat.cast_sub (by omega : 2 ≤ 3 * M.n)]; ring
    have f' : (q.2 : ℤ) = p.2 := by rw [f]
    constructor
    · intro hd
      -- the queen of Q_{D⁻} for this diagonal attacks p
      set d := diffDiag q with hdq
      have hmem : ((6 * (M.n : ℤ) - 3 - d).toNat, (3 * (M.n : ℤ) - 1 - 2 * d).toNat) ∈ S₃ :=
        hPS (Finset.mem_union_left _ (QDm_queen_mem M d hd))
      obtain ⟨d', hd', e₂, f₂, g₂, g₂'⟩ := mem_QDm M hM _ (QDm_queen_mem M d hd)
      -- d' is the same diagonal
      simp only at e₂ f₂
      have hdd : d' = d := by
        have := hM.2.1 d hd
        rw [Int.toNat_of_nonneg (by omega)] at e₂
        omega
      subst hdd
      apply hNA p hpS _ hmem
      apply attacks_of_int
      · intro h; simp only [diffDiag] at hdq; omega
      · simp only [diffDiag] at hdq; omega
    · intro hd
      set d := sumDiag q with hdq
      have hmem : ((2 * (M.n : ℤ) - 2 - (d : ℤ)).toNat, M.n + 2 * d) ∈ S₃ :=
        hPS (Finset.mem_union_right _ (QDp_queen_mem M d hd))
      obtain ⟨d', hd', e₂, f₂, g₂⟩ := mem_QDp M hM _ (QDp_queen_mem M d hd)
      simp only at e₂ f₂
      have hdd : d' = d := by
        have := hM.2.2 d hd
        omega
      subst hdd
      apply hNA p hpS _ hmem
      apply attacks_of_int
      · intro h; simp only [sumDiag] at hdq; omega
      · simp only [sumDiag] at hdq; push_cast at hdq; omega
