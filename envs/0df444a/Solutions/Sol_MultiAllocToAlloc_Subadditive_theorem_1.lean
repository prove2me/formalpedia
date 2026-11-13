-- Prove2me | solution 1 for MultiAllocToAlloc.Subadditive.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:45:15.17475+00:00
-- url     : https://prove2.me/submissions/a93215e3-c431-4866-bd7c-ff3e7171bcda

import Mathlib
import Definitions.Def_SubmodOrder_Subadditive
import Definitions.Def_MultiAllocToAlloc_Subadditive_Valuation
import Definitions.Def_MultiAllocToAlloc_Subadditive_Allocation

section
set_option autoImplicit false

/-! Blueprint for Feige's rounding theorem (arXiv:2506.21493, Theorem 1).
Game values of the alternating picking game, the token process on the multigraph of a
2-multi-allocation, and the induction on copies. -/

namespace MultiAllocToAlloc.Subadditive.Dev.Feige

variable {α : Type*} [DecidableEq α]

/-- Value of the alternating picking game with fuel `n`: available items `Y`, the player's
holdings `H`; `b = true` means the player (maximizer of `v` of her final set) moves next. -/
noncomputable def gv (v : Finset α → ℝ) : ℕ → Bool → Finset α → Finset α → ℝ
  | 0, _, _, H => v H
  | n + 1, b, Y, H =>
    if h : Y.Nonempty then
      (if b then Y.sup' h (fun y => gv v n false (Y.erase y) (insert y H))
       else Y.inf' h (fun y => gv v n true (Y.erase y) H))
    else v H

/-- `ω(S_p, Y, v)` from holdings `H`: the player picks first. -/
noncomputable def first (v : Finset α → ℝ) (Y H : Finset α) : ℝ := gv v Y.card true Y H

/-- `ω(S_q, Y, v)` from holdings `H`: the opponent picks first. -/
noncomputable def second (v : Finset α → ℝ) (Y H : Finset α) : ℝ := gv v Y.card false Y H

theorem first_empty (v : Finset α → ℝ) (H : Finset α) : first v ∅ H = v H := by
  simp [first, gv]

theorem second_empty (v : Finset α → ℝ) (H : Finset α) : second v ∅ H = v H := by
  simp [second, gv]


theorem first_eq_sup' (v : Finset α → ℝ) (Y H : Finset α) (h : Y.Nonempty) :
    first v Y H = Y.sup' h (fun y => second v (Y.erase y) (insert y H)) := by
  obtain ⟨k, hk⟩ : ∃ k, Y.card = k + 1 := ⟨Y.card - 1, by have := h.card_pos; omega⟩
  unfold first
  rw [hk]
  simp only [gv, dif_pos h, if_true]
  refine Finset.sup'_congr h rfl (fun y hy => ?_)
  unfold second
  rw [Finset.card_erase_of_mem hy, hk]
  rfl

theorem second_eq_inf' (v : Finset α → ℝ) (Y H : Finset α) (h : Y.Nonempty) :
    second v Y H = Y.inf' h (fun y => first v (Y.erase y) H) := by
  obtain ⟨k, hk⟩ : ∃ k, Y.card = k + 1 := ⟨Y.card - 1, by have := h.card_pos; omega⟩
  unfold second
  rw [hk]
  simp only [gv, dif_pos h]
  refine Finset.inf'_congr h rfl (fun y hy => ?_)
  unfold first
  rw [Finset.card_erase_of_mem hy, hk]
  rfl

theorem upper_bound (v : Finset α → ℝ) (hmono : ∀ S T : Finset α, S ⊆ T → v S ≤ v T) :
    ∀ n (Y : Finset α), Y.card = n → ∀ H, first v Y H ≤ v (H ∪ Y) ∧ second v Y H ≤ v (H ∪ Y) := by
  intro n
  induction n with
  | zero =>
    intro Y hY H
    rw [Finset.card_eq_zero] at hY
    subst hY
    simp [first_empty, second_empty]
  | succ n ih =>
    intro Y hY H
    have hne : Y.Nonempty := by rw [← Finset.card_pos]; omega
    have hc : ∀ y ∈ Y, (Y.erase y).card = n := fun y hy => by
      rw [Finset.card_erase_of_mem hy]; omega
    constructor
    · rw [first_eq_sup' v Y H hne]
      refine Finset.sup'_le _ _ (fun y hy => ?_)
      have := (ih (Y.erase y) (hc y hy) (insert y H)).2
      have he : insert y H ∪ Y.erase y = H ∪ Y := by
        ext z; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
        constructor
        · rintro ((rfl | h) | ⟨_, h⟩) <;> tauto
        · rintro (h | h) <;> by_cases hz : z = y <;> tauto
      rwa [he] at this
    · rw [second_eq_inf' v Y H hne]
      obtain ⟨y, hy⟩ := hne
      refine (Finset.inf'_le _ hy).trans ?_
      refine (ih (Y.erase y) (hc y hy) H).1.trans (hmono _ _ ?_)
      exact Finset.union_subset_union (le_refl _) (Finset.erase_subset _ _)

theorem reserve (v : Finset α → ℝ) (hmono : ∀ S T : Finset α, S ⊆ T → v S ≤ v T) :
    ∀ n (Y : Finset α), Y.card = n →
      (∀ H R : Finset α, Disjoint Y R → second v (Y ∪ R) H ≤ second v Y (H ∪ R)) ∧
      (∀ H R : Finset α, Disjoint Y R → first v (Y ∪ R) H ≤ first v Y (H ∪ R)) ∧
      (∀ H : Finset α, second v Y H ≤ first v Y H) := by
  intro n
  induction n with
  | zero =>
    intro Y hY
    rw [Finset.card_eq_zero] at hY
    subst hY
    refine ⟨fun H R _ => ?_, fun H R _ => ?_, fun H => ?_⟩
    · rw [second_empty]; simpa using (upper_bound v hmono _ R rfl H).2
    · rw [first_empty]; simpa using (upper_bound v hmono _ R rfl H).1
    · rw [first_empty, second_empty]
  | succ n ih =>
    intro Y hY
    have hne : Y.Nonempty := by rw [← Finset.card_pos]; omega
    have hc : ∀ y ∈ Y, (Y.erase y).card = n := fun y hy => by
      rw [Finset.card_erase_of_mem hy]; omega
    have hera : ∀ R : Finset α, ∀ x ∈ Y, x ∉ R → (Y ∪ R).erase x = Y.erase x ∪ R := by
      intro R x _ hxR
      ext z; simp only [Finset.mem_erase, Finset.mem_union]
      constructor
      · rintro ⟨h1, h2 | h2⟩ <;> tauto
      · rintro (⟨h1, h2⟩ | h2)
        · exact ⟨h1, Or.inl h2⟩
        · exact ⟨fun h => hxR (h ▸ h2), Or.inr h2⟩
    have ha : ∀ H R : Finset α, Disjoint Y R → second v (Y ∪ R) H ≤ second v Y (H ∪ R) := by
      intro H R hYR
      have hne' : (Y ∪ R).Nonempty := hne.mono Finset.subset_union_left
      rw [second_eq_inf' v Y _ hne, second_eq_inf' v _ H hne']
      refine Finset.le_inf' _ _ (fun x hx => ?_)
      have hxR : x ∉ R := Finset.disjoint_left.mp hYR hx
      refine (Finset.inf'_le _ (Finset.mem_union_left R hx)).trans ?_
      rw [hera R x hx hxR]
      exact (ih (Y.erase x) (hc x hx)).2.1 H R
        (Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hYR)
    have hcur : ∀ H : Finset α, second v Y H ≤ first v Y H := by
      intro H
      obtain ⟨e, he⟩ := hne
      have hY' : Y = Y.erase e ∪ {e} := by
        rw [Finset.union_comm, ← Finset.insert_eq, Finset.insert_erase he]
      have h1 := (ih (Y.erase e) (hc e he)).1 H {e} (by simp)
      rw [← hY', Finset.union_comm H, ← Finset.insert_eq] at h1
      refine h1.trans ?_
      rw [first_eq_sup' v Y H ⟨e, he⟩]
      exact Finset.le_sup' (fun y => second v (Y.erase y) (insert y H)) he
    refine ⟨ha, fun H R hYR => ?_, hcur⟩
    have hne' : (Y ∪ R).Nonempty := hne.mono Finset.subset_union_left
    rw [first_eq_sup' v _ H hne']
    refine Finset.sup'_le _ _ (fun y hy => ?_)
    by_cases hyY : y ∈ Y
    · have hyR : y ∉ R := Finset.disjoint_left.mp hYR hyY
      rw [hera R y hyY hyR]
      refine ((ih (Y.erase y) (hc y hyY)).1 (insert y H) R
        (Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hYR)).trans ?_
      rw [first_eq_sup' v Y _ hne, Finset.insert_union]
      exact Finset.le_sup' (fun z => second v (Y.erase z) (insert z (H ∪ R))) hyY
    · have hyR : y ∈ R := by
        rcases Finset.mem_union.mp hy with h | h
        · exact absurd h hyY
        · exact h
      have he1 : (Y ∪ R).erase y = Y ∪ R.erase y := by
        ext z; simp only [Finset.mem_erase, Finset.mem_union]
        constructor
        · rintro ⟨h1, h2 | h2⟩ <;> tauto
        · rintro (h2 | ⟨h1, h2⟩)
          · exact ⟨fun h => hyY (h ▸ h2), Or.inl h2⟩
          · exact ⟨h1, Or.inr h2⟩
      have he2 : insert y H ∪ R.erase y = H ∪ R := by
        ext z; simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_insert]
        constructor
        · rintro ((rfl | h) | ⟨_, h⟩) <;> tauto
        · rintro (h | h) <;> by_cases hz : z = y <;> tauto
      rw [he1]
      refine (ha (insert y H) (R.erase y)
        (Finset.disjoint_of_subset_right (Finset.erase_subset _ _) hYR)).trans ?_
      rw [he2]
      exact hcur _

theorem second_le_first (v : Finset α → ℝ) (hmono : ∀ S T : Finset α, S ⊆ T → v S ≤ v T)
    (Y H : Finset α) : second v Y H ≤ first v Y H :=
  (reserve v hmono Y.card Y rfl).2.2 H

theorem inf'_const_sub {ι : Type*} (s : Finset ι) (h : s.Nonempty) (c : ℝ) (f : ι → ℝ) :
    s.inf' h (fun y => c - f y) = c - s.sup' h f := by
  apply le_antisymm
  · obtain ⟨y, hy, hmax⟩ := Finset.exists_mem_eq_sup' h f
    rw [hmax]; exact Finset.inf'_le _ hy
  · refine Finset.le_inf' _ _ (fun y hy => ?_)
    have := Finset.le_sup' f hy
    linarith

theorem sup'_const_sub {ι : Type*} (s : Finset ι) (h : s.Nonempty) (c : ℝ) (f : ι → ℝ) :
    s.sup' h (fun y => c - f y) = c - s.inf' h f := by
  apply le_antisymm
  · refine Finset.sup'_le _ _ (fun y hy => ?_)
    have := Finset.inf'_le f hy
    linarith
  · obtain ⟨y, hy, hmin⟩ := Finset.exists_mem_eq_inf' h f
    rw [hmin]; exact Finset.le_sup' (fun y => c - f y) hy

/-- Feige Prop 10: the game against the dual valuation is constant-sum. -/
theorem const_sum (v : Finset α → ℝ) (M : Finset α) :
    ∀ n (Y : Finset α), Y.card = n → ∀ H G : Finset α, Disjoint Y H → Disjoint (Y ∪ H) G →
      Y ∪ H ∪ G = M →
      first v Y H + second (fun T => v M - v (M \ T)) Y G = v M ∧
      second v Y H + first (fun T => v M - v (M \ T)) Y G = v M := by
  intro n
  induction n with
  | zero =>
    intro Y hY H G _ hHG hM
    rw [Finset.card_eq_zero] at hY
    subst hY
    simp only [Finset.empty_union] at hHG hM
    have : M \ G = H := by rw [← hM]; exact Finset.union_sdiff_cancel_right hHG
    simp [first_empty, second_empty, this]
  | succ n ih =>
    intro Y hY H G hYH hYHG hM
    have hne : Y.Nonempty := by rw [← Finset.card_pos]; omega
    have hc : ∀ y ∈ Y, (Y.erase y).card = n := fun y hy => by
      rw [Finset.card_erase_of_mem hy]; omega
    -- the two recursive configurations
    have hA : ∀ y ∈ Y, second v (Y.erase y) (insert y H)
        + first (fun T => v M - v (M \ T)) (Y.erase y) G = v M := by
      intro y hy
      refine (ih (Y.erase y) (hc y hy) (insert y H) G ?_ ?_ ?_).2
      · rw [Finset.disjoint_left]
        intro z hz hz'
        rw [Finset.mem_erase] at hz
        rcases Finset.mem_insert.mp hz' with h | h
        · exact hz.1 h
        · exact Finset.disjoint_left.mp hYH hz.2 h
      · rw [Finset.disjoint_left]
        intro z hz hz'
        apply Finset.disjoint_left.mp hYHG _ hz'
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase] at hz ⊢
        rcases hz with h | rfl | h <;> tauto
      · rw [← hM]; ext z
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
        by_cases hz : z = y
        · subst hz; tauto
        · tauto
    have hB : ∀ y ∈ Y, first v (Y.erase y) H
        + second (fun T => v M - v (M \ T)) (Y.erase y) (insert y G) = v M := by
      intro y hy
      refine (ih (Y.erase y) (hc y hy) H (insert y G) ?_ ?_ ?_).1
      · exact Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hYH
      · rw [Finset.disjoint_left]
        intro z hz hz'
        rw [Finset.mem_union, Finset.mem_erase] at hz
        rcases Finset.mem_insert.mp hz' with h | h
        · subst h
          rcases hz with h | h
          · exact h.1 rfl
          · exact Finset.disjoint_left.mp hYH hy h
        · apply Finset.disjoint_left.mp hYHG _ h
          rcases hz with h | h
          · exact Finset.mem_union_left _ h.2
          · exact Finset.mem_union_right _ h
      · rw [← hM]; ext z
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
        by_cases hz : z = y
        · subst hz; tauto
        · tauto
    constructor
    · rw [first_eq_sup' v Y H hne, second_eq_inf' _ Y G hne]
      rw [Finset.inf'_congr hne rfl (g := fun y => v M - second v (Y.erase y) (insert y H))
        (fun y hy => by have := hA y hy; linarith), inf'_const_sub]
      ring
    · rw [second_eq_inf' v Y H hne, first_eq_sup' _ Y G hne]
      rw [Finset.sup'_congr hne rfl (g := fun y => v M - first v (Y.erase y) H)
        (fun y hy => by have := hB y hy; linarith), sup'_const_sub]
      ring

theorem val_mono (w w' : Finset α → ℝ) (hw : ∀ T, w T ≤ w' T) :
    ∀ n (Y : Finset α), Y.card = n → ∀ H : Finset α,
      first w Y H ≤ first w' Y H ∧ second w Y H ≤ second w' Y H := by
  intro n
  induction n with
  | zero =>
    intro Y hY H
    rw [Finset.card_eq_zero] at hY
    subst hY
    simp only [first_empty, second_empty]
    exact ⟨hw H, hw H⟩
  | succ n ih =>
    intro Y hY H
    have hne : Y.Nonempty := by rw [← Finset.card_pos]; omega
    have hc : ∀ y ∈ Y, (Y.erase y).card = n := fun y hy => by
      rw [Finset.card_erase_of_mem hy]; omega
    constructor
    · rw [first_eq_sup' w Y H hne, first_eq_sup' w' Y H hne]
      refine Finset.sup'_le _ _ (fun y hy => ?_)
      exact ((ih _ (hc y hy) _).2).trans (Finset.le_sup' (fun y => second w' (Y.erase y) (insert y H)) hy)
    · rw [second_eq_inf' w Y H hne, second_eq_inf' w' Y H hne]
      refine Finset.le_inf' _ _ (fun y hy => ?_)
      exact (Finset.inf'_le _ hy).trans ((ih _ (hc y hy) _).1)

theorem second_ge (v : Finset α → ℝ) (hmono : ∀ S T : Finset α, S ⊆ T → v S ≤ v T)
    (hsub : SubmodOrder.Subadditive v) (Y : Finset α) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hv0 : 0 ≤ v ∅) (hδ : ∀ y ∈ Y, v {y} ≤ δ) :
    (v Y - δ) / 2 ≤ second v Y ∅ := by
  rcases Y.eq_empty_or_nonempty with hY | hne
  · subst hY
    rw [second_empty]
    linarith
  rw [second_eq_inf' v Y ∅ hne]
  refine Finset.le_inf' _ _ (fun x hx => ?_)
  set Y' := Y.erase x
  have hcs := (const_sum v Y' Y'.card Y' rfl ∅ ∅ (by simp) (by simp) (by simp)).1
  have hbar : ∀ T, v Y' - v (Y' \ T) ≤ v T := by
    intro T
    have h1 : v Y' ≤ v (T ∪ (Y' \ T)) := by
      rw [Finset.union_sdiff_self_eq_union]; exact hmono _ _ Finset.subset_union_right
    have h2 := hsub T (Y' \ T)
    linarith
  have h3 := (val_mono _ v hbar Y'.card Y' rfl ∅).2
  have h4 := second_le_first v hmono Y' ∅
  have h5 : v Y ≤ v (Y' ∪ {x}) := by
    apply hmono
    intro z hz
    by_cases hzx : z = x
    · subst hzx; simp
    · simp [Y', hzx, hz]
  have h6 := hsub Y' {x}
  have h7 := hδ x hx
  linarith

end MultiAllocToAlloc.Subadditive.Dev.Feige
end

section
set_option autoImplicit false

namespace MultiAllocToAlloc.Subadditive.Dev.Feige

/-- `δ` of a bundle for a valuation on an arbitrary item type (as `maxItemValue`). -/
noncomputable def maxItem {α : Type*} [DecidableEq α] (v : Finset α → ℝ) (S : Finset α) : ℝ :=
  if h : S.Nonempty then S.sup' h (fun e => v {e}) else 0

end MultiAllocToAlloc.Subadditive.Dev.Feige

namespace MultiAllocToAlloc.Subadditive.Dev.Feige.Token

open Finset

/-- The potential of agent `i`: the game value with `i` moving first iff it holds the token. -/
noncomputable def phi {α : Type*} [DecidableEq α] {n : ℕ} (v : Finset α → ℝ)
    (tok : Option (Fin n)) (i : Fin n) (Y H : Finset α) : ℝ :=
  if tok = some i then first v Y H else second v Y H

theorem key {α : Type*} [DecidableEq α] {n : ℕ} (A : Fin n → Finset α)
    (hA : ∀ e : α, (Finset.univ.filter (fun i : Fin n => e ∈ A i)).card ≤ 2)
    (v : Fin n → Finset α → ℝ)
    (hmono : ∀ i, ∀ S T : Finset α, S ⊆ T → v i S ≤ v i T) (c : Fin n → ℝ) :
    ∀ N : ℕ, ∀ (E : Finset α) (H : Fin n → Finset α) (tok : Option (Fin n)), E.card ≤ N →
      (∀ i, H i ⊆ A i) → (∀ i j, i ≠ j → Disjoint (H i) (H j)) →
      (∀ i, Disjoint (H i) E) → (∀ i, c i ≤ phi (v i) tok i (A i ∩ E) (H i)) →
      ∃ B : Fin n → Finset α, (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧ (∀ i, B i ⊆ A i) ∧
        ∀ i, c i ≤ v i (B i) := by
  -- the terminal case: nobody has an available item
  have done : ∀ (E : Finset α) (H : Fin n → Finset α) (tok : Option (Fin n)),
      (∀ k, ¬ (A k ∩ E).Nonempty) →
      (∀ i, H i ⊆ A i) → (∀ i j, i ≠ j → Disjoint (H i) (H j)) →
      (∀ i, c i ≤ phi (v i) tok i (A i ∩ E) (H i)) →
      ∃ B : Fin n → Finset α, (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧ (∀ i, B i ⊆ A i) ∧
        ∀ i, c i ≤ v i (B i) := by
    intro E H tok hemp hHA hHd hc
    refine ⟨H, hHd, hHA, fun i => ?_⟩
    have h0 : A i ∩ E = ∅ := Finset.not_nonempty_iff_eq_empty.mp (hemp i)
    have := hc i
    unfold phi at this
    rw [h0, first_empty, second_empty, ite_self] at this
    exact this
  intro N
  induction N with
  | zero =>
    intro E H tok hE hHA hHd _ hc
    have : E = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hE)
    subst this
    exact done ∅ H tok (fun k => by simp) hHA hHd hc
  | succ N ih =>
    intro E H tok hE hHA hHd hHE hc
    by_cases hex : ∃ k, (A k ∩ E).Nonempty
    swap
    · exact done E H tok (fun k hk => hex ⟨k, hk⟩) hHA hHd hc
    -- the mover
    obtain ⟨k, hk, hktok⟩ : ∃ k, (A k ∩ E).Nonempty ∧
        ∀ t, tok = some t → (A t ∩ E).Nonempty → k = t := by
      obtain ⟨k0, hk0⟩ := hex
      rcases tok with _ | t
      · exact ⟨k0, hk0, fun t ht => by simp at ht⟩
      · by_cases ht : (A t ∩ E).Nonempty
        · exact ⟨t, ht, fun t' ht' _ => by simpa using ht'⟩
        · exact ⟨k0, hk0, fun t' ht' h' => by
            simp only [Option.some.injEq] at ht'; subst ht'; exact absurd h' ht⟩
    -- the picked item
    obtain ⟨y, hy, hymax⟩ := Finset.exists_max_image (A k ∩ E)
      (fun y => second (v k) ((A k ∩ E).erase y) (insert y (H k))) hk
    have hfirst : first (v k) (A k ∩ E) (H k) ≤
        second (v k) ((A k ∩ E).erase y) (insert y (H k)) := by
      rw [first_eq_sup' _ _ _ hk]
      exact Finset.sup'_le _ _ hymax
    have hyA : y ∈ A k := (Finset.mem_inter.mp hy).1
    have hyE : y ∈ E := (Finset.mem_inter.mp hy).2
    -- the new token
    obtain ⟨tok', htk, htj, hts⟩ : ∃ tok' : Option (Fin n), tok' ≠ some k ∧
        (∀ j, j ≠ k → y ∈ A j → tok' = some j) ∧ (∀ j, tok' = some j → y ∈ A j) := by
      by_cases h : ∃ j, j ≠ k ∧ y ∈ A j
      · obtain ⟨j, hjk, hjy⟩ := h
        refine ⟨some j, by simpa using hjk, fun j' hj'k hj'y => ?_, fun j' hj' => ?_⟩
        · by_contra hne
          have hne' : j' ≠ j := fun h => hne (by rw [h])
          have hsub : ({k, j, j'} : Finset (Fin n)) ⊆
              Finset.univ.filter (fun i : Fin n => y ∈ A i) := by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl | rfl <;> simp [*]
          have hc3 := Finset.card_le_card hsub
          have : ({k, j, j'} : Finset (Fin n)).card = 3 := by
            rw [Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm hne')]
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨Ne.symm hjk, Ne.symm hj'k⟩
          have := hA y
          omega
        · simp only [Option.some.injEq] at hj'; subst hj'; exact hjy
      · push Not at h
        refine ⟨none, by simp, fun j hjk hjy => absurd (h j hjk) (by simp [hjy]), ?_⟩
        intro j hj; simp at hj
    set E' := E.erase y with hE'
    set H' := Function.update H k (insert y (H k)) with hH'
    have hYi : ∀ i, A i ∩ E' = (A i ∩ E).erase y := fun i => Finset.inter_erase _ _ _
    have hyH : ∀ i, y ∉ H i := fun i hyi => Finset.disjoint_left.mp (hHE i) hyi hyE
    refine ih E' H' tok' ?_ ?_ ?_ ?_ ?_
    · rw [Finset.card_erase_of_mem hyE]; omega
    · intro i
      rw [hH', Function.update_apply]
      split_ifs with hik
      · subst hik; exact Finset.insert_subset hyA (hHA i)
      · exact hHA i
    · intro i j hij
      rw [hH', Function.update_apply, Function.update_apply]
      split_ifs with hik hjk hjk
      · exact absurd (hik.trans hjk.symm) hij
      · rw [Finset.disjoint_insert_left]; exact ⟨hyH j, hik ▸ hHd i j hij⟩
      · rw [Finset.disjoint_insert_right]; exact ⟨hyH i, hjk ▸ hHd i j hij⟩
      · exact hHd i j hij
    · intro i
      rw [hH', Function.update_apply]
      split_ifs with hik
      · rw [Finset.disjoint_insert_left]
        exact ⟨by simp [hE'], Finset.disjoint_of_subset_right (Finset.erase_subset _ _) (hHE k)⟩
      · exact Finset.disjoint_of_subset_right (Finset.erase_subset _ _) (hHE i)
    · intro i
      have hci := hc i
      rw [hYi]
      by_cases hik : i = k
      · subst hik
        have hH'i : H' i = insert y (H i) := by simp [hH']
        rw [hH'i]
        unfold phi at hci ⊢
        rw [if_neg htk]
        split_ifs at hci
        · linarith
        · linarith [second_le_first (v i) (hmono i) (A i ∩ E) (H i)]
      have hH'i : H' i = H i := by simp [hH', hik]
      rw [hH'i]
      by_cases hyi : y ∈ A i
      · have htok : tok ≠ some i := fun h =>
          hik (hktok i h ⟨y, Finset.mem_inter.mpr ⟨hyi, hyE⟩⟩).symm
        have hyY : y ∈ A i ∩ E := Finset.mem_inter.mpr ⟨hyi, hyE⟩
        unfold phi at hci ⊢
        rw [if_neg htok] at hci
        rw [if_pos (htj i hik hyi)]
        refine hci.trans ?_
        rw [second_eq_inf' _ _ _ ⟨y, hyY⟩]
        exact Finset.inf'_le (fun z => first (v i) ((A i ∩ E).erase z) (H i)) hyY
      · have hyY : y ∉ A i ∩ E := fun h => hyi (Finset.mem_inter.mp h).1
        rw [Finset.erase_eq_of_notMem hyY]
        have ht' : tok' ≠ some i := fun h => hyi (hts i h)
        unfold phi at hci ⊢
        rw [if_neg ht']
        split_ifs at hci with htok
        · have he : ¬ (A i ∩ E).Nonempty := fun hne => hik (hktok i htok hne).symm
          rw [Finset.not_nonempty_iff_eq_empty.mp he, first_empty] at hci
          rw [Finset.not_nonempty_iff_eq_empty.mp he, second_empty]
          exact hci
        · exact hci

/-- The base case `d = 2` (Feige, Corollary 14): a 2-multi-allocation rounds to an allocation
inside it losing half the value and half the largest item. -/
theorem base_two {α : Type*} [DecidableEq α] {n : ℕ} (A : Fin n → Finset α)
    (hA : ∀ e : α, (Finset.univ.filter (fun i : Fin n => e ∈ A i)).card ≤ 2)
    (v : Fin n → Finset α → ℝ) (hnorm : ∀ i, v i ∅ = 0)
    (hmono : ∀ i, ∀ S T : Finset α, S ⊆ T → v i S ≤ v i T)
    (hsub : ∀ i, SubmodOrder.Subadditive (v i)) :
    ∃ B : Fin n → Finset α, (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧ (∀ i, B i ⊆ A i) ∧
      ∀ i, v i (A i) / 2 - 1 / 2 * maxItem (v i) (A i) ≤ v i (B i) := by
  set E := Finset.univ.biUnion A with hE
  refine key A hA v hmono (fun i => v i (A i) / 2 - 1 / 2 * maxItem (v i) (A i)) E.card E
    (fun _ => ∅) none le_rfl (fun i => Finset.empty_subset _) (fun i j _ => by simp)
    (fun i => by simp) (fun i => ?_)
  have hAE : A i ∩ E = A i :=
    Finset.inter_eq_left.mpr (Finset.subset_biUnion_of_mem A (Finset.mem_univ i))
  simp only [phi, reduceCtorEq, if_false, hAE]
  have hδ : ∀ y ∈ A i, v i {y} ≤ maxItem (v i) (A i) := by
    intro y hy
    unfold maxItem
    rw [dif_pos ⟨y, hy⟩]
    exact Finset.le_sup' (fun e => v i {e}) hy
  have hδ0 : 0 ≤ maxItem (v i) (A i) := by
    rcases (A i).eq_empty_or_nonempty with h | ⟨y, hy⟩
    · simp [maxItem, h]
    · have := hmono i ∅ {y} (Finset.empty_subset _)
      linarith [hδ y hy, hnorm i]
  have := second_ge (v i) (hmono i) (hsub i) (A i) _ hδ0 (by rw [hnorm i]) hδ
  linarith

end MultiAllocToAlloc.Subadditive.Dev.Feige.Token
end

section
set_option autoImplicit false

/-! Feige's induction on copies: `main_pow` (d = 2^k) from the base case `base_two` (d = 2). -/

namespace MultiAllocToAlloc.Subadditive.Dev.Feige.Copies

open MultiAllocToAlloc.Subadditive.Dev.Feige (maxItem)

theorem le_maxItem {α : Type*} [DecidableEq α] (v : Finset α → ℝ) {S : Finset α} {e : α}
    (he : e ∈ S) : v {e} ≤ maxItem v S := by
  unfold maxItem
  rw [dif_pos ⟨e, he⟩]
  exact Finset.le_sup' (fun e => v {e}) he

theorem maxItem_le {α : Type*} [DecidableEq α] (v : Finset α → ℝ) (S : Finset α) (c : ℝ)
    (h : ∀ e ∈ S, v {e} ≤ c) (hc : 0 ≤ c) : maxItem v S ≤ c := by
  unfold maxItem
  split_ifs with hS
  · exact Finset.sup'_le _ _ h
  · exact hc

theorem maxItem_nonneg {α : Type*} [DecidableEq α] (v : Finset α → ℝ) (hv : ∀ S, 0 ≤ v S)
    (S : Finset α) : 0 ≤ maxItem v S := by
  by_cases hS : S.Nonempty
  · obtain ⟨e, he⟩ := hS
    exact (hv _).trans (le_maxItem v he)
  · unfold maxItem
    rw [dif_neg hS]

/-- One halving step: a `2^(k+1)`-multi-allocation contains a `2^k`-multi-allocation losing
half the value and half the largest item. -/
theorem step {n : ℕ} (k : ℕ) {α : Type*} [DecidableEq α]
    (A : Fin n → Finset α)
    (hA : ∀ e : α, (Finset.univ.filter (fun i : Fin n => e ∈ A i)).card ≤ 2 ^ (k + 1))
    (v : Fin n → Finset α → ℝ) (hnorm : ∀ i, v i ∅ = 0)
    (hmono : ∀ i, ∀ S T : Finset α, S ⊆ T → v i S ≤ v i T)
    (hsub : ∀ i, SubmodOrder.Subadditive (v i)) :
    ∃ B : Fin n → Finset α, (∀ i, B i ⊆ A i) ∧
      (∀ e : α, (Finset.univ.filter (fun i : Fin n => e ∈ B i)).card ≤ 2 ^ k) ∧
      ∀ i, v i (A i) / 2 - 1 / 2 * maxItem (v i) (A i) ≤ v i (B i) := by
  classical
  have hv0 : ∀ i S, 0 ≤ v i S := fun i S => (hnorm i).symm.le.trans
    (hmono i ∅ S (Finset.empty_subset _))
  set hold : α → Finset (Fin n) := fun e => Finset.univ.filter (fun j : Fin n => e ∈ A j)
    with hhold
  set idx : Fin n → α → ℕ := fun i e => ((hold e).filter (· < i)).card with hidx
  have hpos : 0 < 2 ^ k := pow_pos (by norm_num) k
  -- idx is strictly monotone on `hold e`
  have idx_lt : ∀ e i j, i ∈ hold e → i < j → idx i e < idx j e := by
    intro e i j hi hij
    apply Finset.card_lt_card
    refine (Finset.ssubset_iff_of_subset ?_).2 ⟨i, ?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, hx.2.trans hij⟩
    · exact Finset.mem_filter.2 ⟨hi, hij⟩
    · simp
  have idx_inj : ∀ e, Set.InjOn (fun i => idx i e) (hold e : Set (Fin n)) := by
    intro e i hi j hj hij
    simp only at hij
    rcases lt_trichotomy i j with h | h | h
    · exact absurd hij (idx_lt e i j hi h).ne
    · exact h
    · exact absurd hij (idx_lt e j i hj h).ne'
  have idx_bound : ∀ e i, i ∈ hold e → idx i e < 2 ^ (k + 1) := by
    intro e i hi
    refine lt_of_lt_of_le ?_ (hA e)
    apply Finset.card_lt_card
    refine (Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)).2 ⟨i, hi, ?_⟩
    simp
  have half_lt : ∀ e i, i ∈ hold e → idx i e / 2 < 2 ^ k := by
    intro e i hi
    have := idx_bound e i hi
    rw [pow_succ] at this
    omega
  let c : Fin n → α → Fin (2 ^ k) := fun i e => ⟨idx i e / 2 % 2 ^ k, Nat.mod_lt _ hpos⟩
  let A' : Fin n → Finset (α × Fin (2 ^ k)) := fun i => (A i).image (fun e => (e, c i e))
  let v' : Fin n → Finset (α × Fin (2 ^ k)) → ℝ := fun i S => v i (S.image Prod.fst)
  have hA'fst : ∀ i, (A' i).image Prod.fst = A i := by
    intro i
    simp [A', Finset.image_image, Function.comp_def]
  have mem_A' : ∀ i (p : α × Fin (2 ^ k)), p ∈ A' i ↔ p.1 ∈ A i ∧ c i p.1 = p.2 := by
    intro i p
    simp only [A', Finset.mem_image]
    constructor
    · rintro ⟨e, he, rfl⟩
      exact ⟨he, rfl⟩
    · rintro ⟨h1, h2⟩
      exact ⟨p.1, h1, by rw [h2]⟩
  have hA' : ∀ p : α × Fin (2 ^ k),
      (Finset.univ.filter (fun i : Fin n => p ∈ A' i)).card ≤ 2 := by
    rintro ⟨e, c0⟩
    have hsub2 : (Finset.univ.filter (fun i : Fin n => (e, c0) ∈ A' i)) ⊆ hold e := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_A'] at hi
      simp [hhold, hi.1]
    calc (Finset.univ.filter (fun i : Fin n => (e, c0) ∈ A' i)).card
        ≤ ({2 * c0.val, 2 * c0.val + 1} : Finset ℕ).card := by
          apply Finset.card_le_card_of_injOn (fun i => idx i e)
          · intro i hi
            have hi' := hi
            simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
              mem_A'] at hi'
            have hh : i ∈ hold e := hsub2 (by simpa using hi)
            have h2 := hi'.2
            have h3 := half_lt e i hh
            simp only [c, Fin.ext_iff] at h2
            rw [Nat.mod_eq_of_lt h3] at h2
            simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
              Set.mem_singleton_iff]
            omega
          · exact (idx_inj e).mono (by
              intro i hi
              exact hsub2 (by simpa using hi))
      _ ≤ 2 := Finset.card_le_two
  obtain ⟨B', hB'disj, hB'sub, hB'val⟩ := Feige.Token.base_two A' hA' v'
    (fun i => by simp [v', hnorm])
    (fun i S T hST => hmono i _ _ (Finset.image_subset_image hST))
    (fun i S T => by
      simp only [v', Finset.image_union]
      exact hsub i _ _)
  refine ⟨fun i => (B' i).image Prod.fst, ?_, ?_, ?_⟩
  · intro i
    rw [← hA'fst i]
    exact Finset.image_subset_image (hB'sub i)
  · intro e
    calc (Finset.univ.filter (fun i : Fin n => e ∈ (B' i).image Prod.fst)).card
        ≤ (Finset.univ : Finset (Fin (2 ^ k))).card := by
          apply Finset.card_le_card_of_injOn
            (fun i => if h : ∃ c0, (e, c0) ∈ B' i then h.choose else 0)
          · intro i _
            simp
          · intro i hi j hj hij
            simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
              Finset.mem_image] at hi hj
            have hi' : ∃ c0, (e, c0) ∈ B' i := by
              obtain ⟨⟨e', c0⟩, hp, he⟩ := hi
              simp only at he
              exact ⟨c0, he ▸ hp⟩
            have hj' : ∃ c0, (e, c0) ∈ B' j := by
              obtain ⟨⟨e', c0⟩, hp, he⟩ := hj
              simp only at he
              exact ⟨c0, he ▸ hp⟩
            simp only [dif_pos hi', dif_pos hj'] at hij
            by_contra hne
            have hd := hB'disj i j hne
            have h1 := hi'.choose_spec
            have h2 := hj'.choose_spec
            rw [hij] at h1
            exact Finset.disjoint_left.1 hd h1 h2
      _ = 2 ^ k := by simp
  · intro i
    have hval := hB'val i
    have hvA : v' i (A' i) = v i (A i) := by simp only [v', hA'fst]
    have hm : maxItem (v' i) (A' i) ≤ maxItem (v i) (A i) := by
      apply maxItem_le _ _ _ _ (maxItem_nonneg _ (hv0 i) _)
      intro p hp
      have : v' i {p} = v i {p.1} := by simp [v']
      rw [this]
      exact le_maxItem _ ((mem_A' i p).1 hp).1
    have hvB : v' i (B' i) = v i ((B' i).image Prod.fst) := rfl
    rw [hvA, hvB] at hval
    linarith

/-- Feige's Theorem 1 over an arbitrary item type, `d = 2 ^ k`, `k ≥ 1`. -/
theorem main_pow {n : ℕ} (k : ℕ) (hk : 1 ≤ k) {α : Type*} [DecidableEq α]
    (A : Fin n → Finset α)
    (hA : ∀ e : α, (Finset.univ.filter (fun i : Fin n => e ∈ A i)).card ≤ 2 ^ k)
    (v : Fin n → Finset α → ℝ) (hnorm : ∀ i, v i ∅ = 0)
    (hmono : ∀ i, ∀ S T : Finset α, S ⊆ T → v i S ≤ v i T)
    (hsub : ∀ i, SubmodOrder.Subadditive (v i)) :
    ∃ B : Fin n → Finset α, (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧ (∀ i, B i ⊆ A i) ∧
      ∀ i, v i (A i) / (2 ^ k : ℝ) - ((2 ^ k : ℝ) - 1) / (2 ^ k : ℝ) * maxItem (v i) (A i) ≤
        v i (B i) := by
  have hv0 : ∀ i S, 0 ≤ v i S := fun i S => (hnorm i).symm.le.trans
    (hmono i ∅ S (Finset.empty_subset _))
  induction k, hk using Nat.le_induction generalizing A with
  | base =>
    obtain ⟨B, h1, h2, h3⟩ := Feige.Token.base_two A (by simpa using hA) v hnorm hmono hsub
    refine ⟨B, h1, h2, fun i => ?_⟩
    have := h3 i
    norm_num at this ⊢
    linarith
  | succ k hk ih =>
    obtain ⟨B, hBA, hB, hBv⟩ := step k A hA v hnorm hmono hsub
    obtain ⟨C, hC1, hC2, hC3⟩ := ih B hB
    refine ⟨C, hC1, fun i => (hC2 i).trans (hBA i), fun i => ?_⟩
    have hmB : maxItem (v i) (B i) ≤ maxItem (v i) (A i) :=
      maxItem_le _ _ _ (fun e he => le_maxItem _ (hBA i he)) (maxItem_nonneg _ (hv0 i) _)
    have hq : (0 : ℝ) < 2 ^ k := by positivity
    have hq1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    set q : ℝ := 2 ^ k with hqdef
    set m := maxItem (v i) (A i)
    have h1 : (q - 1) / q * maxItem (v i) (B i) ≤ (q - 1) / q * m :=
      mul_le_mul_of_nonneg_left hmB (div_nonneg (by linarith) hq.le)
    have h2 : (v i (A i) / 2 - 1 / 2 * m) / q ≤ v i (B i) / q :=
      div_le_div_of_nonneg_right (hBv i) hq.le
    have h3 := hC3 i
    have heq : v i (A i) / (2 ^ (k + 1) : ℝ) - ((2 ^ (k + 1) : ℝ) - 1) / (2 ^ (k + 1) : ℝ) * m
        = (v i (A i) / 2 - 1 / 2 * m) / q - (q - 1) / q * m := by
      rw [pow_succ, ← hqdef]
      field_simp
      ring
    rw [heq]
    linarith

end MultiAllocToAlloc.Subadditive.Dev.Feige.Copies
end

section
set_option autoImplicit false

namespace MultiAllocToAlloc.Subadditive

theorem chk_theorem_1 {n m : ℕ} (d : ℕ) (hd : ∃ k : ℕ, 1 ≤ k ∧ d = 2 ^ k)
    (A : Fin n → Finset (Fin m)) (hA : IsMultiAllocation d A)
    (v : Fin n → Finset (Fin m) → ℝ)
    (hnorm : ∀ i, IsNormalized (v i)) (hmono : ∀ i, IsMonotone (v i))
    (hsub : ∀ i, SubmodOrder.Subadditive (v i)) :
    ∃ A' : Fin n → Finset (Fin m), IsAllocation A' ∧ (∀ i, A' i ⊆ A i) ∧
      ∀ i : Fin n,
        v i (A i) / (d : ℝ) - ((d : ℝ) - 1) / (d : ℝ) * maxItemValue (v i) (A i) ≤
          v i (A' i) := by
  obtain ⟨k, hk, rfl⟩ := hd
  obtain ⟨B, hB1, hB2, hB3⟩ := Dev.Feige.Copies.main_pow k hk A hA v hnorm hmono hsub
  refine ⟨B, hB1, hB2, fun i => ?_⟩
  have := hB3 i
  simpa [Dev.Feige.maxItem, maxItemValue] using this

end MultiAllocToAlloc.Subadditive
end

theorem solution : type_of% @MultiAllocToAlloc.Subadditive.chk_theorem_1 := @MultiAllocToAlloc.Subadditive.chk_theorem_1
