-- Prove2me | solution 1 for IwataFF.SFM.fix_calls_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T06:21:55.099827+00:00
-- url     : https://prove2.me/submissions/5a7725c3-4594-4b61-935d-1d85e3cf16fb

import Mathlib
import Definitions.Def_IwataFF_SFM_Basic
import Definitions.Def_IwataFF_SFM_Phase
import Definitions.Def_IwataFF_SFM_Main

open IwataFF.SFM MainState

namespace X5FC

variable {n : ℕ}

theorem mem_reach {α : Type} [DecidableEq α] (V : Finset α) (F : Finset (α × α)) (v b : α) :
    b ∈ reach V F v ↔ b ∈ V ∧ Relation.ReflTransGen (fun a c => (a, c) ∈ F) v b := by
  simp only [reach, Finset.mem_filter]

/-- the relation counted by the potential -/
def RelF (B : Finset (Finset (Fin n))) (F : Finset (Finset (Fin n) × Finset (Fin n)))
    (acc : Finset (Fin n)) (a b : Fin n) : Prop :=
  a ∈ acc ∨ b ∈ acc ∨ ∃ A ∈ B, ∃ C ∈ B, a ∈ A ∧ b ∈ C ∧
    Relation.ReflTransGen (fun x y => (x, y) ∈ F) A C

open Classical in
noncomputable def pairs (B : Finset (Finset (Fin n))) (F : Finset (Finset (Fin n) × Finset (Fin n)))
    (acc : Finset (Fin n)) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p : Fin n × Fin n => p.1 ≠ p.2 ∧ RelF B F acc p.1 p.2)

noncomputable def Psi (s : MainState n) : ℕ := (pairs s.blocks s.arcs s.acc).card + s.acc.card

structure Inv (s : MainState n) : Prop where
  ne : ∀ A ∈ s.blocks, A.Nonempty
  disj : ∀ A ∈ s.blocks, ∀ B ∈ s.blocks, A ≠ B → Disjoint A B
  dacc : ∀ A ∈ s.blocks, Disjoint A s.acc
  arcs : ∀ e ∈ s.arcs, e.1 ∈ s.blocks ∧ e.2 ∈ s.blocks
  fixu : ∀ fr u η ph, s.mode = Mode.fix fr u η ph → u ∈ s.blocks

theorem mem_pairs (B F acc) (p : Fin n × Fin n) :
    p ∈ pairs B F acc ↔ p.1 ≠ p.2 ∧ RelF B F acc p.1 p.2 := by
  simp [pairs]

theorem pairs_card_le (B F acc) : (pairs (n := n) B F acc).card ≤ n * n - n := by
  have : pairs B F acc ⊆ (Finset.univ : Finset (Fin n)).offDiag := by
    intro p hp
    rw [mem_pairs] at hp
    simp [Finset.mem_offDiag, hp.1]
  have h := Finset.card_le_card this
  rw [Finset.offDiag_card] at h
  simpa using h

theorem psi_le (s : MainState n) : Psi s ≤ n * n := by
  unfold Psi
  have h1 := pairs_card_le s.blocks s.arcs s.acc
  have h2 : s.acc.card ≤ n := by simpa using Finset.card_le_univ s.acc
  have h3 : n ≤ n * n := Nat.le_mul_self n
  omega

theorem psi_lt (s : MainState n) (hI : Inv s) (hne : s.blocks.Nonempty) : Psi s + 1 ≤ n * n := by
  unfold Psi
  obtain ⟨A, hA⟩ := hne
  obtain ⟨a, ha⟩ := hI.ne A hA
  have hna : a ∉ s.acc := Finset.disjoint_left.mp (hI.dacc A hA) ha
  have h1 := pairs_card_le s.blocks s.arcs s.acc
  have h2 : s.acc.card ≤ n - 1 := by
    have : s.acc ⊆ Finset.univ.erase a := fun x hx =>
      Finset.mem_erase.mpr ⟨fun e => hna (e ▸ hx), Finset.mem_univ _⟩
    have := Finset.card_le_card this
    rw [Finset.card_erase_of_mem (Finset.mem_univ _)] at this
    simpa using this
  have h3 : n ≤ n * n := Nat.le_mul_self n
  have h4 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; exact a.elim0
    · exact h
  omega

theorem psi_mono (s s' : MainState n)
    (hmono : ∀ a b, RelF s.blocks s.arcs s.acc a b → RelF s'.blocks s'.arcs s'.acc a b)
    (hacc : s.acc ⊆ s'.acc) : Psi s ≤ Psi s' := by
  unfold Psi
  have : pairs s.blocks s.arcs s.acc ⊆ pairs s'.blocks s'.arcs s'.acc := by
    intro p hp; rw [mem_pairs] at hp ⊢; exact ⟨hp.1, hmono _ _ hp.2⟩
  have := Finset.card_le_card this
  have := Finset.card_le_card hacc
  omega

theorem psi_strict_pair (s s' : MainState n)
    (hmono : ∀ a b, RelF s.blocks s.arcs s.acc a b → RelF s'.blocks s'.arcs s'.acc a b)
    (hacc : s.acc ⊆ s'.acc) (a b : Fin n) (hab : a ≠ b)
    (h1 : ¬ RelF s.blocks s.arcs s.acc a b) (h2 : RelF s'.blocks s'.arcs s'.acc a b) :
    Psi s + 1 ≤ Psi s' := by
  unfold Psi
  have : pairs s.blocks s.arcs s.acc ⊂ pairs s'.blocks s'.arcs s'.acc := by
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨(a, b), ?_, ?_⟩
      · rw [mem_pairs]; exact ⟨hab, h2⟩
      · rw [mem_pairs]; exact fun h => h1 h.2
    · intro p hp; rw [mem_pairs] at hp ⊢; exact ⟨hp.1, hmono _ _ hp.2⟩
  have := Finset.card_lt_card this
  have := Finset.card_le_card hacc
  omega

theorem psi_strict_acc (s s' : MainState n)
    (hmono : ∀ a b, RelF s.blocks s.arcs s.acc a b → RelF s'.blocks s'.arcs s'.acc a b)
    (hacc : s.acc ⊂ s'.acc) : Psi s + 1 ≤ Psi s' := by
  unfold Psi
  have : pairs s.blocks s.arcs s.acc ⊆ pairs s'.blocks s'.arcs s'.acc := by
    intro p hp; rw [mem_pairs] at hp ⊢; exact ⟨hp.1, hmono _ _ hp.2⟩
  have := Finset.card_le_card this
  have := Finset.card_lt_card hacc
  omega

/-- the pair `(a, b)` with `a ∈ u`, `b ∈ w`, `w ∉ R(u)` is not yet related. -/
theorem not_rel (s : MainState n) (hI : Inv s) (u w : Finset (Fin n)) (hu : u ∈ s.blocks)
    (hw : w ∈ s.blocks) (hwu : w ∉ s.R u) (a b : Fin n) (ha : a ∈ u) (hb : b ∈ w) :
    ¬ RelF s.blocks s.arcs s.acc a b ∧ a ≠ b := by
  have huw : u ≠ w := by
    rintro rfl; apply hwu; unfold MainState.R; rw [mem_reach]; exact ⟨hu, Relation.ReflTransGen.refl⟩
  refine ⟨?_, ?_⟩
  · rintro (h | h | ⟨A, hA, C, hC, haA, hbC, hr⟩)
    · exact Finset.disjoint_left.mp (hI.dacc u hu) ha h
    · exact Finset.disjoint_left.mp (hI.dacc w hw) hb h
    · have e1 : A = u := by
        by_contra hne; exact Finset.disjoint_left.mp (hI.disj A hA u hu hne) haA ha
      have e2 : C = w := by
        by_contra hne; exact Finset.disjoint_left.mp (hI.disj C hC w hw hne) hbC hb
      subst e1 e2
      apply hwu; unfold MainState.R; rw [mem_reach]; exact ⟨hC, hr⟩
  · rintro rfl; exact Finset.disjoint_left.mp (hI.disj u hu w hw huw) ha hb

theorem addArc_step (s : MainState n) (hI : Inv s) (u w : Finset (Fin n)) (hu : u ∈ s.blocks)
    (hw : w ∈ s.blocks) (hwu : w ∉ s.R u) :
    Inv (s.addArc u w) ∧ Psi s + 1 ≤ Psi (s.addArc u w) := by
  refine ⟨⟨hI.ne, hI.disj, hI.dacc, ?_, ?_⟩, ?_⟩
  · intro e he
    simp only [addArc, Finset.mem_insert] at he
    rcases he with rfl | he
    · exact ⟨hu, hw⟩
    · exact hI.arcs e he
  · intro fr u' η ph h; simp [addArc] at h
  · obtain ⟨a, ha⟩ := hI.ne u hu
    obtain ⟨b, hb⟩ := hI.ne w hw
    obtain ⟨h1, hab⟩ := not_rel s hI u w hu hw hwu a b ha hb
    refine psi_strict_pair s _ ?_ subset_rfl a b hab h1 ?_
    · rintro a b (h | h | ⟨A, hA, C, hC, haA, hbC, hr⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨A, hA, C, hC, haA, hbC,
          Relation.ReflTransGen.mono (fun x y hxy => Finset.mem_insert_of_mem hxy) _ _ hr⟩)
    · exact Or.inr (Or.inr ⟨u, hu, w, hw, ha, hb,
        Relation.ReflTransGen.single (Finset.mem_insert_self _ _)⟩)

theorem contract_gen (s s' : MainState n) (hI : Inv s) (C : Finset (Finset (Fin n)))
    (hCb : C ⊆ s.blocks) (u w : Finset (Fin n)) (huC : u ∈ C) (hwC : w ∈ C) (hwu : w ∉ s.R u)
    (hbl : ∀ X, X ∈ s'.blocks ↔ X = C.biUnion id ∨ (X ∈ s.blocks ∧ X ∉ C))
    (harc : ∀ x y, (x, y) ∈ s'.arcs ↔ x ≠ y ∧ ∃ a b, (a, b) ∈ s.arcs ∧
      (if a ∈ C then C.biUnion id else a) = x ∧ (if b ∈ C then C.biUnion id else b) = y)
    (hacc : s'.acc = s.acc) (hmode : s'.mode = Mode.loop) :
    Inv s' ∧ Psi s + 1 ≤ Psi s' := by
  set B := C.biUnion id with hB
  set m : Finset (Fin n) → Finset (Fin n) := fun b => if b ∈ C then B else b with hm
  have hu := hCb huC
  have hw := hCb hwC
  have hBne : B.Nonempty := by
    obtain ⟨b, hb⟩ := hI.ne w hw
    exact ⟨b, Finset.mem_biUnion.mpr ⟨w, hwC, hb⟩⟩
  have hBdisj : ∀ D ∈ s.blocks, D ∉ C → Disjoint B D := by
    intro D hD hDC
    rw [hB, Finset.disjoint_biUnion_left]
    intro c hc
    exact hI.disj c (hCb hc) D hD (fun e => hDC (e ▸ hc))
  have hmB : ∀ A ∈ s.blocks, m A ∈ s'.blocks := by
    intro A hA
    rw [hbl]
    by_cases h : A ∈ C
    · left; simp [hm, h]
    · right; simp only [hm, if_neg h]; exact ⟨hA, h⟩
  have hsubm : ∀ A, A ⊆ m A := by
    intro A
    by_cases h : A ∈ C
    · simp only [hm, if_pos h]; exact Finset.subset_biUnion_of_mem id h
    · simp [hm, h]
  have hmono : ∀ a b, RelF s.blocks s.arcs s.acc a b → RelF s'.blocks s'.arcs s'.acc a b := by
    rintro a b (h | h | ⟨A, hA, D, hD, haA, hbD, hr⟩)
    · left; rw [hacc]; exact h
    · right; left; rw [hacc]; exact h
    · right; right
      refine ⟨m A, hmB A hA, m D, hmB D hD, hsubm A haA, hsubm D hbD, ?_⟩
      refine Relation.ReflTransGen.lift' m ?_ _ _ hr
      intro x y hxy
      show Relation.ReflTransGen _ (m x) (m y)
      by_cases hxy' : m x = m y
      · rw [hxy']
      · apply Relation.ReflTransGen.single
        rw [harc]
        exact ⟨hxy', x, y, hxy, rfl, rfl⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro A hA
    rcases (hbl A).mp hA with rfl | ⟨hA, _⟩
    · exact hBne
    · exact hI.ne A hA
  · intro X hX Y hY hXY
    rcases (hbl X).mp hX with rfl | ⟨hX, hXC⟩ <;> rcases (hbl Y).mp hY with rfl | ⟨hY, hYC⟩
    · exact absurd rfl hXY
    · exact hBdisj Y hY hYC
    · exact (hBdisj X hX hXC).symm
    · exact hI.disj X hX Y hY hXY
  · intro X hX
    rw [hacc]
    rcases (hbl X).mp hX with rfl | ⟨hX, _⟩
    · rw [hB, Finset.disjoint_biUnion_left]
      intro c hc; exact hI.dacc c (hCb hc)
    · exact hI.dacc X hX
  · rintro ⟨x, y⟩ he
    obtain ⟨_, a, b, hab, rfl, rfl⟩ := (harc x y).mp he
    exact ⟨hmB a (hI.arcs _ hab).1, hmB b (hI.arcs _ hab).2⟩
  · intro fr u' η ph h; rw [hmode] at h; cases h
  · obtain ⟨a, ha⟩ := hI.ne u hu
    obtain ⟨b, hb⟩ := hI.ne w hw
    obtain ⟨h1, hab⟩ := not_rel s hI u w hu hw hwu a b ha hb
    refine psi_strict_pair s _ hmono (by rw [hacc]) a b hab h1 ?_
    have hBm : B ∈ s'.blocks := (hbl B).mpr (Or.inl rfl)
    exact Or.inr (Or.inr ⟨B, hBm, B, hBm, Finset.mem_biUnion.mpr ⟨u, huC, ha⟩,
      Finset.mem_biUnion.mpr ⟨w, hwC, hb⟩, Relation.ReflTransGen.refl⟩)

theorem delete_gen (s s' : MainState n) (hI : Inv s) (w : Finset (Fin n)) (hw : w ∈ s.blocks)
    (hbl : ∀ X, X ∈ s'.blocks ↔ X ∈ s.blocks ∧ X ∉ s.R w)
    (harc : ∀ e, e ∈ s'.arcs ↔ e ∈ s.arcs ∧ e.1 ∉ s.R w ∧ e.2 ∉ s.R w)
    (hacc : s'.acc = s.acc ∪ (s.R w).biUnion id) (hmode : s'.mode = Mode.loop) :
    Inv s' ∧ Psi s + 1 ≤ Psi s' := by
  have hRb : ∀ X ∈ s.R w, X ∈ s.blocks := fun X hX => by
    unfold MainState.R at hX; rw [mem_reach] at hX; exact hX.1
  have hclosed : ∀ X Y, X ∈ s.R w → (X, Y) ∈ s.arcs → Y ∈ s.R w := by
    intro X Y hX hXY
    unfold MainState.R at hX ⊢; rw [mem_reach] at hX ⊢
    exact ⟨(hI.arcs _ hXY).2, hX.2.tail hXY⟩
  have hwR : w ∈ s.R w := by
    unfold MainState.R; rw [mem_reach]; exact ⟨hw, Relation.ReflTransGen.refl⟩
  -- paths avoiding the deleted part survive
  have hpath : ∀ A D, Relation.ReflTransGen (fun x y => (x, y) ∈ s.arcs) A D → D ∈ s.blocks →
      A ∉ s.R w → D ∈ s.R w ∨ Relation.ReflTransGen (fun x y => (x, y) ∈ s'.arcs) A D := by
    intro A D hr
    induction hr with
    | refl => intro _ _; right; exact Relation.ReflTransGen.refl
    | tail hr hyz ih =>
      rename_i Y Z
      intro hZ hA
      by_cases hZR : Z ∈ s.R w
      · left; exact hZR
      · rcases ih (hI.arcs _ hyz).1 hA with hYR | hr'
        · exact absurd (hclosed _ _ hYR hyz) hZR
        · by_cases hYR : Y ∈ s.R w
          · exact absurd (hclosed _ _ hYR hyz) hZR
          · right; exact hr'.tail ((harc _).mpr ⟨hyz, hYR, hZR⟩)
  have hmono : ∀ a b, RelF s.blocks s.arcs s.acc a b → RelF s'.blocks s'.arcs s'.acc a b := by
    rintro a b (h | h | ⟨A, hA, D, hD, haA, hbD, hr⟩)
    · left; rw [hacc]; exact Finset.mem_union_left _ h
    · right; left; rw [hacc]; exact Finset.mem_union_left _ h
    · by_cases hAR : A ∈ s.R w
      · left; rw [hacc]; exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨A, hAR, haA⟩)
      · rcases hpath A D hr hD hAR with hDR | hr'
        · right; left; rw [hacc]
          exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨D, hDR, hbD⟩)
        · by_cases hDR : D ∈ s.R w
          · right; left; rw [hacc]
            exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨D, hDR, hbD⟩)
          · right; right
            exact ⟨A, (hbl A).mpr ⟨hA, hAR⟩, D, (hbl D).mpr ⟨hD, hDR⟩, haA, hbD, hr'⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro A hA; exact hI.ne A ((hbl A).mp hA).1
  · intro X hX Y hY hXY; exact hI.disj X ((hbl X).mp hX).1 Y ((hbl Y).mp hY).1 hXY
  · intro X hX
    obtain ⟨hX, hXR⟩ := (hbl X).mp hX
    rw [hacc, Finset.disjoint_union_right]
    refine ⟨hI.dacc X hX, ?_⟩
    rw [Finset.disjoint_biUnion_right]
    intro c hc
    exact hI.disj X hX c (hRb c hc) (fun e => hXR (e ▸ hc))
  · intro e he
    obtain ⟨he, h1, h2⟩ := (harc e).mp he
    exact ⟨(hbl _).mpr ⟨(hI.arcs e he).1, h1⟩, (hbl _).mpr ⟨(hI.arcs e he).2, h2⟩⟩
  · intro fr u' η ph h; rw [hmode] at h; cases h
  · apply psi_strict_acc s _ hmono
    rw [hacc]
    obtain ⟨b, hb⟩ := hI.ne w hw
    rw [Finset.ssubset_iff_of_subset Finset.subset_union_left]
    refine ⟨b, Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨w, hwR, hb⟩), ?_⟩
    exact Finset.disjoint_left.mp (hI.dacc w hw) hb

end X5FC


open IwataFF.SFM MainState

namespace X5FC

variable {n : ℕ}

theorem inv_same (s s' : MainState n) (hI : Inv s) (hb : s'.blocks = s.blocks)
    (ha : s'.arcs = s.arcs) (hacc : s'.acc = s.acc)
    (hfix : ∀ fr u η ph, s'.mode = Mode.fix fr u η ph → u ∈ s.blocks) : Inv s' := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hb]; exact hI.ne
  · rw [hb]; exact hI.disj
  · rw [hb, hacc]; exact hI.dacc
  · rw [hb, ha]; exact hI.arcs
  · rw [hb]; exact hfix

theorem psi_eq (s s' : MainState n) (hb : s'.blocks = s.blocks)
    (ha : s'.arcs = s.arcs) (hacc : s'.acc = s.acc) : Psi s' = Psi s := by
  unfold Psi; rw [hb, ha, hacc]

open Classical in
theorem callCount_succ (s : ℕ → MainState n) (j : ℕ) :
    callCount s (j + 1) = callCount s j + if CallStep (s j) (s (j + 1)) then 1 else 0 := by
  unfold callCount
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · simp

theorem call_mode (s s' : MainState n) (h : CallStep s s') : s.mode = Mode.loop := h.1

theorem init_inv (f : Finset (Fin n) → ℝ) : Inv (initMain f) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro A hA
    simp only [initMain, Finset.mem_image] at hA
    obtain ⟨a, _, rfl⟩ := hA
    exact Finset.singleton_nonempty a
  · intro A hA B hB hAB
    simp only [initMain, Finset.mem_image] at hA hB
    obtain ⟨a, _, rfl⟩ := hA
    obtain ⟨b, _, rfl⟩ := hB
    rw [Finset.disjoint_singleton]
    intro e; exact hAB (by rw [e])
  · intro A _; simp [initMain]
  · intro e he; simp [initMain] at he
  · intro fr u η ph h; simp [initMain] at h

theorem return_step (s s' : MainState n) (hI : Inv s) (h : ReturnStep s s') :
    Inv s' ∧ Psi s + 1 ≤ Psi s' ∧ s'.mode = Mode.loop := by
  obtain ⟨fr, u, η, ph, w, hm, hout, hcase⟩ := h
  have hu : u ∈ s.blocks := hI.fixu fr u η ph hm
  have hwG : w ∈ s.fixGround fr u := hout.2.2.2.1
  have hRb : ∀ v X, X ∈ s.R v → X ∈ s.blocks := fun v X hX => by
    unfold MainState.R at hX; rw [mem_reach] at hX; exact hX.1
  have hself : ∀ X ∈ s.blocks, X ∈ s.R X := fun X hX => by
    unfold MainState.R; rw [mem_reach]; exact ⟨hX, Relation.ReflTransGen.refl⟩
  rcases hcase with ⟨hfr, huw, rfl⟩ | ⟨hfr, huw, rfl⟩ | ⟨hfr, rfl⟩
  · subst hfr
    have hwG' : w ∈ s.blocks \ s.R u := by simpa [MainState.fixGround] using hwG
    rw [Finset.mem_sdiff] at hwG'
    have r := contract_gen s (s.contract u w) hI ((s.R w).filter (fun v => u ∈ s.R v))
      (fun X hX => hRb w X (Finset.mem_filter.mp hX).1) u w
      (Finset.mem_filter.mpr ⟨huw, hself u hu⟩)
      (Finset.mem_filter.mpr ⟨hself w hwG'.1, huw⟩) hwG'.2
      (fun X => by
        unfold MainState.contract
        simp only [Finset.mem_insert, Finset.mem_sdiff])
      (fun x y => by
        unfold MainState.contract
        simp only [Finset.mem_filter, Finset.mem_image, Prod.mk.injEq, Prod.exists]
        tauto)
      rfl rfl
    exact ⟨r.1, r.2, rfl⟩
  · subst hfr
    have hwG' : w ∈ s.blocks \ s.R u := by simpa [MainState.fixGround] using hwG
    rw [Finset.mem_sdiff] at hwG'
    have r := addArc_step s hI u w hu hwG'.1 hwG'.2
    exact ⟨r.1, r.2, rfl⟩
  · subst hfr
    have hw : w ∈ s.blocks := by simpa [MainState.fixGround] using hwG
    have r := delete_gen s (s.delete w) hI w hw
      (fun X => by unfold MainState.delete; simp only [Finset.mem_sdiff])
      (fun e => by unfold MainState.delete; simp only [Finset.mem_filter])
      rfl rfl
    exact ⟨r.1, r.2, rfl⟩

end X5FC

open X5FC in
theorem solution {n : ℕ} (hn : 1 ≤ n) (f : Finset (Fin n) → ℝ)
    (hsub : SubmodularOn Finset.univ f) (hf0 : f ∅ = 0)
    (s : ℕ → MainState n) (k : ℕ) (hrun : IsRun f s k) :
    callCount s k ≤ n ^ 2 := by
  obtain ⟨h0, hstep⟩ := hrun
  have key : ∀ j, j ≤ k → Inv (s j) ∧ ((s j).mode = Mode.loop → callCount s j ≤ Psi (s j)) ∧
      (∀ fr u η ph, (s j).mode = Mode.fix fr u η ph →
        callCount s j ≤ Psi (s j) + 1 ∧ Psi (s j) + 1 ≤ n * n) ∧ callCount s j ≤ n * n := by
    intro j
    induction j with
    | zero =>
      intro _
      rw [h0]
      refine ⟨init_inv f, fun _ => by simp [callCount], ?_, by simp [callCount]⟩
      intro fr u η ph h; simp [initMain] at h
    | succ j ih =>
      intro hj
      obtain ⟨hI, hL, hF, _⟩ := ih (by omega)
      have hst := hstep j (by omega)
      rw [callCount_succ]
      rcases hst with hfin | hcall | hfix | hret
      · -- finish
        have hnc : ¬ CallStep (s j) (s (j + 1)) := by
          intro hc
          obtain ⟨_, _, _, u, L, _, _, rest⟩ := hc
          simp only at rest
          obtain ⟨_, _, e⟩ := rest
          rcases hfin with ⟨_, ⟨_, e'⟩ | ⟨_, _, e'⟩⟩ <;> rw [e'] at e <;>
            simpa using congrArg MainState.mode e
        rw [if_neg hnc, add_zero]
        obtain ⟨hm, hc⟩ := hfin
        have hc0 := hL hm
        have hle := psi_le (s j)
        rcases hc with ⟨_, e⟩ | ⟨_, _, e⟩
        · refine ⟨inv_same _ _ hI (by rw [e]) (by rw [e]) (by rw [e])
              (by intro fr u η ph h; rw [e] at h; simp at h), ?_, ?_, by omega⟩
          · intro h; rw [e] at h; simp at h
          · intro fr u η ph h; rw [e] at h; simp at h
        · refine ⟨inv_same _ _ hI (by rw [e]; rfl) (by rw [e]; rfl) (by rw [e]; rfl)
              (by intro fr u η ph h; rw [e] at h; simp at h), ?_, ?_, by omega⟩
          · intro h; rw [e] at h; simp at h
          · intro fr u η ph h; rw [e] at h; simp at h
      · -- call
        rw [if_pos hcall]
        obtain ⟨hm, hne, _, u, L, hu, _, rest⟩ := hcall
        simp only at rest
        obtain ⟨_, _, e⟩ := rest
        have hc0 := hL hm
        have hb : (s (j + 1)).blocks = (s j).blocks := by rw [e]; rfl
        have ha : (s (j + 1)).arcs = (s j).arcs := by rw [e]; rfl
        have hacc : (s (j + 1)).acc = (s j).acc := by rw [e]; rfl
        have hP := psi_eq _ _ hb ha hacc
        have hlt := psi_lt (s j) hI hne
        refine ⟨inv_same _ _ hI hb ha hacc ?_, ?_, ?_, by omega⟩
        · intro fr u' η ph h; rw [e] at h; simp only [Mode.fix.injEq] at h
          rw [← h.2.1]; exact hu
        · intro h; rw [e] at h; simp at h
        · intro fr u' η ph _; omega
      · -- a scaling step inside Fix
        have hnc : ¬ CallStep (s j) (s (j + 1)) := by
          intro hc
          obtain ⟨fr, u, η, ph, ph', hm, _, _⟩ := hfix
          rw [call_mode _ _ hc] at hm; simp at hm
        rw [if_neg hnc, add_zero]
        obtain ⟨fr, u, η, ph, ph', hm, _, e⟩ := hfix
        obtain ⟨h1, h2⟩ := hF fr u η ph hm
        have hb : (s (j + 1)).blocks = (s j).blocks := by rw [e]
        have ha : (s (j + 1)).arcs = (s j).arcs := by rw [e]
        have hacc : (s (j + 1)).acc = (s j).acc := by rw [e]
        have hP := psi_eq _ _ hb ha hacc
        refine ⟨inv_same _ _ hI hb ha hacc ?_, ?_, ?_, by omega⟩
        · intro fr' u' η' ph'' h; rw [e] at h; simp only [Mode.fix.injEq] at h
          rw [← h.2.1]; exact hI.fixu fr u η ph hm
        · intro h; rw [e] at h; simp at h
        · intro _ _ _ _ _; omega
      · -- return from Fix
        have hnc : ¬ CallStep (s j) (s (j + 1)) := by
          intro hc
          obtain ⟨fr, u, η, ph, w, hm, _⟩ := hret
          rw [call_mode _ _ hc] at hm; simp at hm
        rw [if_neg hnc, add_zero]
        obtain ⟨fr, u, η, ph, w, hm, _⟩ := id hret
        obtain ⟨h1, _⟩ := hF fr u η ph hm
        obtain ⟨hI', hP, hmode⟩ := return_step _ _ hI hret
        have hle := psi_le (s (j + 1))
        refine ⟨hI', fun _ => by omega, ?_, by omega⟩
        intro fr' u' η' ph' h; rw [hmode] at h; simp at h
  have := (key k le_rfl).2.2.2
  rw [sq]; exact this

