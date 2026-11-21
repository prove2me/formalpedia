-- Prove2me | solution 1 for MultiwayCut.observation_2_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T00:45:04.028153+00:00
-- url     : https://prove2.me/submissions/54747137-5acb-420f-b7fa-5393775ae934

import Mathlib
import Definitions.Def_MultiwayCut_CutDensity

namespace Aux_MultiwayCut_observation_2_1
open MultiwayCut

variable {k : ℕ}

lemma shA (z : Fin k → ℝ) (a b : Fin k) (ε : ℝ) (c : Fin k) :
    ijShift z a b ε c =
      z c + ε * ((if c = a then (1:ℝ) else 0) - (if c = b then (1:ℝ) else 0)) := by
  simp only [ijShift, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.single_apply, smul_eq_mul]

lemma sh_a (z : Fin k → ℝ) {a b : Fin k} (h : a ≠ b) (ε : ℝ) : ijShift z a b ε a = z a + ε := by
  rw [shA, if_pos rfl, if_neg h]; ring

lemma sh_b (z : Fin k → ℝ) {a b : Fin k} (h : a ≠ b) (ε : ℝ) : ijShift z a b ε b = z b - ε := by
  rw [shA, if_neg (Ne.symm h), if_pos rfl]; ring

lemma sh_o (z : Fin k → ℝ) {a b c : Fin k} (hca : c ≠ a) (hcb : c ≠ b) (ε : ℝ) :
    ijShift z a b ε c = z c := by
  rw [shA, if_neg hca, if_neg hcb]; ring

lemma sh_sum (z : Fin k → ℝ) (a b : Fin k) (ε : ℝ) : ∑ c, ijShift z a b ε c = ∑ c, z c := by
  simp only [shA]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_ite_eq',
    Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true, sub_self, mul_zero, add_zero]

lemma sh_mem (z : Fin k → ℝ) (hz : z ∈ stdSimplex ℝ (Fin k)) {a b : Fin k} (h : a ≠ b) {ε : ℝ}
    (hε : 0 ≤ ε) (hb : ε ≤ z b) : ijShift z a b ε ∈ stdSimplex ℝ (Fin k) := by
  refine ⟨fun c => ?_, ?_⟩
  · by_cases hca : c = a
    · rw [hca, sh_a z h]; linarith [hz.1 a]
    · by_cases hcb : c = b
      · rw [hcb, sh_b z h]; linarith
      · rw [sh_o z hca hcb]; exact hz.1 c
  · rw [sh_sum]; exact hz.2

lemma sh_comp (z : Fin k → ℝ) (a b : Fin k) (x y : ℝ) :
    ijShift (ijShift z a b x) a b y = ijShift z a b (x + y) := by
  funext c; simp only [shA]; ring

lemma sh_comp' (z : Fin k → ℝ) (a b : Fin k) (x y : ℝ) :
    ijShift (ijShift z a b x) b a y = ijShift z a b (x - y) := by
  funext c; simp only [shA]; ring

lemma sh_zero (z : Fin k → ℝ) (a b : Fin k) : ijShift z a b 0 = z := by
  funext c; simp only [shA]; ring

/-! ### Sorting permutation with tie-breaking -/

def tb (a b c : Fin k) : ℕ := if c = a then 0 else if c = b then 2 else 1

noncomputable def key (z : Fin k → ℝ) (a b : Fin k) (c : Fin k) : ℝ ×ₗ ℕ :=
  toLex (-z c, tb a b c)

lemma tb_a (a b : Fin k) : tb a b a = 0 := by simp [tb]

lemma tb_b {a b : Fin k} (h : a ≠ b) : tb a b b = 2 := by simp [tb, Ne.symm h]

lemma tb_le (a b c : Fin k) : tb a b c ≤ 2 := by
  unfold tb; split_ifs <;> omega

lemma tb_eq0 {a b c : Fin k} (h : tb a b c = 0) : c = a := by
  unfold tb at h
  split_ifs at h with h1 h2 <;> first | exact h1 | omega

lemma tb_eq2 {a b c : Fin k} (h : tb a b c = 2) : c = b := by
  unfold tb at h
  split_ifs at h with h1 h2 <;> first | exact h2 | omega

lemma key_le {z : Fin k → ℝ} {a b c d : Fin k} (h : key z a b c ≤ key z a b d) : z d ≤ z c := by
  unfold key at h
  rw [Prod.Lex.toLex_le_toLex] at h
  rcases h with h | ⟨h, _⟩
  · have h' : -z c < -z d := h
    linarith
  · have h' : -z c = -z d := h
    linarith

lemma key_ab {z : Fin k → ℝ} {a b : Fin k} (hab : a ≠ b) (hle : z b ≤ z a) :
    key z a b a < key z a b b := by
  unfold key
  rw [Prod.Lex.toLex_lt_toLex]
  rcases lt_or_eq_of_le hle with h | h
  · left
    show -z a < -z b
    linarith
  · right
    refine ⟨show -z a = -z b by rw [h], show tb a b a < tb a b b by simp [tb_a, tb_b hab]⟩

lemma key_up {z : Fin k → ℝ} {a b c : Fin k} (h : key z a b c ≤ key z a b a) (hc : c ≠ a) :
    z a < z c := by
  unfold key at h
  rw [Prod.Lex.toLex_le_toLex] at h
  rcases h with h | ⟨_, h⟩
  · have h' : -z c < -z a := h
    linarith
  · have h' : tb a b c ≤ tb a b a := h
    rw [tb_a] at h'
    exact absurd (tb_eq0 (a := a) (b := b) (c := c) (by omega)) hc

lemma key_dn {z : Fin k → ℝ} {a b c : Fin k} (hab : a ≠ b) (h : key z a b b ≤ key z a b c)
    (hc : c ≠ b) : z c < z b := by
  unfold key at h
  rw [Prod.Lex.toLex_le_toLex] at h
  rcases h with h | ⟨_, h⟩
  · have h' : -z b < -z c := h
    linarith
  · have h' : tb a b b ≤ tb a b c := h
    rw [tb_b hab] at h'
    have h2 := tb_le a b c
    exact absurd (tb_eq2 (a := a) (b := b) (c := c) (by omega)) hc

lemma edge_core (z : Fin k → ℝ) (hz : z ∈ stdSimplex ℝ (Fin k)) {a b : Fin k} (hab : a ≠ b)
    {ε : ℝ} (hε : 0 ≤ ε) (hz' : ijShift z a b ε ∈ stdSimplex ℝ (Fin k)) (hle : z b ≤ z a)
    (hup : ∀ c, c ≠ a → c ≠ b → z a < z c → z a + ε ≤ z c)
    (hdn : ∀ c, c ≠ a → c ≠ b → z c < z b → z c ≤ z b - ε) :
    ∃ (π : Equiv.Perm (Fin k)) (i j : Fin k), IsIJEdge π i j ε z (ijShift z a b ε) := by
  obtain ⟨π, hmono⟩ : ∃ π : Equiv.Perm (Fin k), Monotone (key z a b ∘ π) :=
    ⟨_, Tuple.monotone_sort _⟩
  have hπa : π (π.symm a) = a := π.apply_symm_apply a
  have hπb : π (π.symm b) = b := π.apply_symm_apply b
  refine ⟨π, π.symm a, π.symm b, ?_⟩
  unfold IsIJEdge
  refine ⟨hz, hz', ?_, hε, ?_, ?_, ?_, ?_⟩
  · by_contra hcon
    push_neg at hcon
    have h1 : key z a b (π (π.symm b)) ≤ key z a b (π (π.symm a)) := hmono hcon
    rw [hπa, hπb] at h1
    exact absurd h1 (not_le.mpr (key_ab hab hle))
  · intro r s hrs
    have h1 : key z a b (π r) ≤ key z a b (π s) := hmono hrs
    have h2 : z (π s) ≤ z (π r) := key_le h1
    exact h2
  · intro i' hi'
    rw [hπa]
    have hlt : i' < π.symm a := by rw [Fin.lt_iff_val_lt_val]; omega
    have h1 : key z a b (π i') ≤ key z a b (π (π.symm a)) := hmono hlt.le
    rw [hπa] at h1
    have hca : π i' ≠ a := by
      intro h
      apply hlt.ne
      rw [← h]
      simp
    have hz1 := key_up h1 hca
    have hcb : π i' ≠ b := by
      intro h
      rw [h] at hz1
      linarith
    exact hup _ hca hcb hz1
  · intro j' hj'
    rw [hπb]
    have hlt : π.symm b < j' := by rw [Fin.lt_iff_val_lt_val]; omega
    have h1 : key z a b (π (π.symm b)) ≤ key z a b (π j') := hmono hlt.le
    rw [hπb] at h1
    have hcb : π j' ≠ b := by
      intro h
      apply hlt.ne'
      rw [← h]
      simp
    have hz1 := key_dn hab h1 hcb
    have hca : π j' ≠ a := by
      intro h
      rw [h] at hz1
      linarith
    exact hdn _ hca hcb hz1
  · rw [hπa, hπb]

/-! ### Paths -/

def Reach (δ L : ℝ) (u v : Fin k → ℝ) : Prop :=
  ∃ (m : ℕ) (y : ℕ → Fin k → ℝ) (π : ℕ → Equiv.Perm (Fin k)) (i j : ℕ → Fin k) (ε : ℕ → ℝ),
    y 0 = u ∧ y m = v ∧
    (∀ s < m, ε s ≤ δ ∧ (IsIJEdge (π s) (i s) (j s) (ε s) (y s) (y (s + 1)) ∨
        IsIJEdge (π s) (i s) (j s) (ε s) (y (s + 1)) (y s))) ∧
    ∑ s ∈ Finset.range m, ε s = L

lemma reach_refl {δ : ℝ} {u : Fin k → ℝ} (hu : u ∈ stdSimplex ℝ (Fin k)) : Reach δ 0 u u := by
  obtain ⟨c⟩ : Nonempty (Fin k) := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0
      have h := hu.2
      simp at h
    · exact ⟨⟨0, h0⟩⟩
  exact ⟨0, fun _ => u, fun _ => Equiv.refl _, fun _ => c, fun _ => c, fun _ => 0, rfl, rfl,
    fun s hs => absurd hs (Nat.not_lt_zero _), by simp⟩

lemma reach_single {δ ε : ℝ} {π : Equiv.Perm (Fin k)} {i j : Fin k} {u v : Fin k → ℝ}
    (h : ε ≤ δ) (he : IsIJEdge π i j ε u v ∨ IsIJEdge π i j ε v u) : Reach δ ε u v := by
  refine ⟨1, fun r => if r = 0 then u else v, fun _ => π, fun _ => i, fun _ => j, fun _ => ε,
    by simp, by simp, fun s hs => ?_, by simp⟩
  refine ⟨h, ?_⟩
  have : s = 0 := by omega
  subst this
  simpa using he

lemma glue {α : Type*} (m1 : ℕ) (f g : ℕ → α) :
    ∃ F : ℕ → α, (∀ r < m1, F r = f r) ∧ ∀ r, F (m1 + r) = g r :=
  ⟨fun r => if r < m1 then f r else g (r - m1), fun r hr => by simp [hr],
    fun r => by
      show (if m1 + r < m1 then f (m1 + r) else g (m1 + r - m1)) = g r
      rw [if_neg (by omega), Nat.add_sub_cancel_left]⟩

lemma reach_trans {δ L1 L2 : ℝ} {u w v : Fin k → ℝ} (h1 : Reach δ L1 u w) (h2 : Reach δ L2 w v) :
    Reach δ (L1 + L2) u v := by
  obtain ⟨m1, y1, π1, i1, j1, ε1, h10, h1m, h1s, h1L⟩ := h1
  obtain ⟨m2, y2, π2, i2, j2, ε2, h20, h2m, h2s, h2L⟩ := h2
  obtain ⟨Y, hY1, hY2⟩ := glue m1 y1 y2
  obtain ⟨P, hP1, hP2⟩ := glue m1 π1 π2
  obtain ⟨I, hI1, hI2⟩ := glue m1 i1 i2
  obtain ⟨J, hJ1, hJ2⟩ := glue m1 j1 j2
  obtain ⟨E, hE1, hE2⟩ := glue m1 ε1 ε2
  have hY1' : ∀ r ≤ m1, Y r = y1 r := by
    intro r hr
    rcases lt_or_eq_of_le hr with h | h
    · exact hY1 r h
    · rw [h, h1m, ← h20, ← hY2 0, Nat.add_zero]
  refine ⟨m1 + m2, Y, P, I, J, E, ?_, ?_, ?_, ?_⟩
  · rw [hY1' 0 (Nat.zero_le _), h10]
  · rw [hY2, h2m]
  · intro s hs
    by_cases h : s < m1
    · rw [hY1' s h.le, hY1' (s + 1) h, hP1 s h, hI1 s h, hJ1 s h, hE1 s h]
      exact h1s s h
    · push_neg at h
      obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h
      have ht : t < m2 := by omega
      rw [hY2, show m1 + t + 1 = m1 + (t + 1) by ring, hY2, hP2, hI2, hJ2, hE2]
      exact h2s t ht
  · rw [Finset.sum_range_add, ← h1L, ← h2L]
    congr 1
    · exact Finset.sum_congr rfl (fun r hr => hE1 r (Finset.mem_range.mp hr))
    · exact Finset.sum_congr rfl (fun r _ => hE2 r)

/-! ### A single pair transfer -/

noncomputable def BP (z : Fin k → ℝ) (a b : Fin k) : Finset ℝ :=
  (Finset.univ.image fun c => z c - z a) ∪ (Finset.univ.image fun c => z b - z c) ∪
    {(z b - z a) / 2}

def Free (z : Fin k → ℝ) (a b : Fin k) (τ0 τ1 : ℝ) : Prop :=
  ∀ x ∈ BP z a b, ¬ (τ0 < x ∧ x < τ1)

lemma mem1 (z : Fin k → ℝ) (a b c : Fin k) : z c - z a ∈ BP z a b :=
  Finset.mem_union_left _ (Finset.mem_union_left _
    (Finset.mem_image_of_mem (fun c => z c - z a) (Finset.mem_univ c)))

lemma mem2 (z : Fin k → ℝ) (a b c : Fin k) : z b - z c ∈ BP z a b :=
  Finset.mem_union_left _ (Finset.mem_union_right _
    (Finset.mem_image_of_mem (fun c => z b - z c) (Finset.mem_univ c)))

lemma mem3 (z : Fin k → ℝ) (a b : Fin k) : (z b - z a) / 2 ∈ BP z a b :=
  Finset.mem_union_right _ (Finset.mem_singleton_self _)

lemma step (z : Fin k → ℝ) (hz : z ∈ stdSimplex ℝ (Fin k)) {a b : Fin k} (hab : a ≠ b)
    {t δ τ0 τ1 : ℝ} (htb : t ≤ z b) (h0 : 0 ≤ τ0) (h01 : τ0 ≤ τ1) (h1t : τ1 ≤ t)
    (hδ : τ1 - τ0 ≤ δ) (hfree : Free z a b τ0 τ1) :
    Reach δ (τ1 - τ0) (ijShift z a b τ0) (ijShift z a b τ1) := by
  have hm0 : ijShift z a b τ0 ∈ stdSimplex ℝ (Fin k) := sh_mem z hz hab h0 (by linarith)
  have hm1 : ijShift z a b τ1 ∈ stdSimplex ℝ (Fin k) :=
    sh_mem z hz hab (by linarith) (by linarith)
  have hp1 : ijShift (ijShift z a b τ0) a b (τ1 - τ0) = ijShift z a b τ1 := by
    rw [sh_comp]; congr 1; ring
  have hp0 : ijShift (ijShift z a b τ1) b a (τ1 - τ0) = ijShift z a b τ0 := by
    rw [sh_comp']; congr 1; ring
  have hε : 0 ≤ τ1 - τ0 := by linarith
  by_cases hcase : z b - τ0 ≤ z a + τ0
  · obtain ⟨π, i, j, he⟩ := edge_core (ijShift z a b τ0) hm0 hab hε (by rw [hp1]; exact hm1)
      (by rw [sh_a _ hab, sh_b _ hab]; linarith)
      (fun c hca hcb hlt => by
        rw [sh_a _ hab, sh_o _ hca hcb] at hlt ⊢
        have := hfree _ (mem1 z a b c)
        by_contra hcon
        exact this ⟨by linarith, by linarith⟩)
      (fun c hca hcb hlt => by
        rw [sh_b _ hab, sh_o _ hca hcb] at hlt ⊢
        have := hfree _ (mem2 z a b c)
        by_contra hcon
        exact this ⟨by linarith, by linarith⟩)
    rw [hp1] at he
    exact reach_single hδ (Or.inl he)
  · have hcl : z a + τ1 ≤ z b - τ1 := by
      by_contra hcon
      exact hfree _ (mem3 z a b) ⟨by linarith, by linarith⟩
    obtain ⟨π, i, j, he⟩ := edge_core (ijShift z a b τ1) hm1 (Ne.symm hab) hε
      (by rw [hp0]; exact hm0)
      (by rw [sh_a _ hab, sh_b _ hab]; linarith)
      (fun c hcb hca hlt => by
        rw [sh_b _ hab, sh_o _ hca hcb] at hlt ⊢
        have := hfree _ (mem2 z a b c)
        by_contra hcon
        exact this ⟨by linarith, by linarith⟩)
      (fun c hcb hca hlt => by
        rw [sh_a _ hab, sh_o _ hca hcb] at hlt ⊢
        have := hfree _ (mem1 z a b c)
        by_contra hcon
        exact this ⟨by linarith, by linarith⟩)
    rw [hp0] at he
    exact reach_single hδ (Or.inr he)

lemma grid (z : Fin k → ℝ) (hz : z ∈ stdSimplex ℝ (Fin k)) {a b : Fin k} (hab : a ≠ b)
    {t δ : ℝ} (hδ : 0 < δ) (htb : t ≤ z b) :
    ∀ N : ℕ, ∀ τ0 τ1 : ℝ, 0 ≤ τ0 → τ0 ≤ τ1 → τ1 ≤ t → τ1 - τ0 ≤ N * δ → Free z a b τ0 τ1 →
      Reach δ (τ1 - τ0) (ijShift z a b τ0) (ijShift z a b τ1) := by
  intro N
  induction N with
  | zero =>
    intro τ0 τ1 h0 h01 h1t hN hf
    rw [Nat.cast_zero, zero_mul] at hN
    exact step z hz hab htb h0 h01 h1t (by linarith) hf
  | succ N ih =>
    intro τ0 τ1 h0 h01 h1t hN hf
    by_cases hs : τ1 - τ0 ≤ δ
    · exact step z hz hab htb h0 h01 h1t hs hf
    · push_neg at hs
      rw [Nat.cast_succ, add_mul, one_mul] at hN
      have h1 := step z hz hab htb (δ := δ) (τ0 := τ0) (τ1 := τ0 + δ) h0 (by linarith) (by linarith)
        (by linarith) (fun x hx hc => hf x hx ⟨hc.1, by linarith [hc.2]⟩)
      have h2 := ih (τ0 + δ) τ1 (by linarith) (by linarith) h1t (by linarith)
        (fun x hx hc => hf x hx ⟨by linarith [hc.1], hc.2⟩)
      have := reach_trans h1 h2
      rwa [show τ0 + δ - τ0 + (τ1 - (τ0 + δ)) = τ1 - τ0 by ring] at this

lemma free_reach (z : Fin k → ℝ) (hz : z ∈ stdSimplex ℝ (Fin k)) {a b : Fin k} (hab : a ≠ b)
    {t δ : ℝ} (hδ : 0 < δ) (htb : t ≤ z b) {τ0 τ1 : ℝ} (h0 : 0 ≤ τ0) (h01 : τ0 ≤ τ1)
    (h1t : τ1 ≤ t) (hf : Free z a b τ0 τ1) :
    Reach δ (τ1 - τ0) (ijShift z a b τ0) (ijShift z a b τ1) := by
  obtain ⟨N, hN⟩ := exists_nat_ge ((τ1 - τ0) / δ)
  exact grid z hz hab hδ htb N τ0 τ1 h0 h01 h1t (by rwa [div_le_iff₀ hδ] at hN) hf

lemma cardInd (z : Fin k → ℝ) (hz : z ∈ stdSimplex ℝ (Fin k)) {a b : Fin k} (hab : a ≠ b)
    {t δ : ℝ} (hδ : 0 < δ) (htb : t ≤ z b) :
    ∀ n : ℕ, ∀ τ0 τ1 : ℝ, 0 ≤ τ0 → τ0 ≤ τ1 → τ1 ≤ t →
      ((BP z a b).filter (fun x => τ0 < x ∧ x < τ1)).card ≤ n →
      Reach δ (τ1 - τ0) (ijShift z a b τ0) (ijShift z a b τ1) := by
  intro n
  induction n with
  | zero =>
    intro τ0 τ1 h0 h01 h1t hc
    have hf : Free z a b τ0 τ1 := by
      intro x hx hx'
      have hmem : x ∈ (BP z a b).filter (fun x => τ0 < x ∧ x < τ1) :=
        Finset.mem_filter.mpr ⟨hx, hx'⟩
      have := Finset.card_pos.mpr ⟨x, hmem⟩
      omega
    exact free_reach z hz hab hδ htb h0 h01 h1t hf
  | succ n ih =>
    intro τ0 τ1 h0 h01 h1t hc
    by_cases hf : Free z a b τ0 τ1
    · exact free_reach z hz hab hδ htb h0 h01 h1t hf
    · unfold Free at hf
      push_neg at hf
      obtain ⟨x, hx, hx1, hx2⟩ := hf
      have hsub1 : (BP z a b).filter (fun y => τ0 < y ∧ y < x) ⊂
          (BP z a b).filter (fun y => τ0 < y ∧ y < τ1) := by
        have hs : (BP z a b).filter (fun y => τ0 < y ∧ y < x) ⊆
            (BP z a b).filter (fun y => τ0 < y ∧ y < τ1) := by
          intro y hy
          rw [Finset.mem_filter] at hy ⊢
          exact ⟨hy.1, hy.2.1, by linarith [hy.2.2]⟩
        exact (Finset.ssubset_iff_of_subset hs).mpr
          ⟨x, Finset.mem_filter.mpr ⟨hx, hx1, hx2⟩,
            fun h => lt_irrefl x (Finset.mem_filter.mp h).2.2⟩
      have hsub2 : (BP z a b).filter (fun y => x < y ∧ y < τ1) ⊂
          (BP z a b).filter (fun y => τ0 < y ∧ y < τ1) := by
        have hs : (BP z a b).filter (fun y => x < y ∧ y < τ1) ⊆
            (BP z a b).filter (fun y => τ0 < y ∧ y < τ1) := by
          intro y hy
          rw [Finset.mem_filter] at hy ⊢
          exact ⟨hy.1, by linarith [hy.2.1], hy.2.2⟩
        exact (Finset.ssubset_iff_of_subset hs).mpr
          ⟨x, Finset.mem_filter.mpr ⟨hx, hx1, hx2⟩,
            fun h => lt_irrefl x (Finset.mem_filter.mp h).2.1⟩
      have c1 := Finset.card_lt_card hsub1
      have c2 := Finset.card_lt_card hsub2
      have r1 := ih τ0 x h0 hx1.le (by linarith) (by omega)
      have r2 := ih x τ1 (by linarith) hx2.le h1t (by omega)
      have := reach_trans r1 r2
      rwa [show x - τ0 + (τ1 - x) = τ1 - τ0 by ring] at this

lemma pair (z : Fin k → ℝ) (hz : z ∈ stdSimplex ℝ (Fin k)) {a b : Fin k} (hab : a ≠ b)
    {t δ : ℝ} (hδ : 0 < δ) (ht : 0 ≤ t) (htb : t ≤ z b) :
    Reach δ t z (ijShift z a b t) := by
  have := cardInd z hz hab hδ htb _ 0 t le_rfl ht le_rfl le_rfl
  rwa [sub_zero, sh_zero] at this

/-! ### Transportation decomposition -/

lemma decrease {δ : ℝ} (hδ : 0 < δ) (u v : Fin k → ℝ) (hu : u ∈ stdSimplex ℝ (Fin k))
    (hv : v ∈ stdSimplex ℝ (Fin k)) (hne : u ≠ v) :
    ∃ w t, w ∈ stdSimplex ℝ (Fin k) ∧ Reach δ t u w ∧
      (Finset.univ.filter (fun ℓ => w ℓ ≠ v ℓ)).card <
        (Finset.univ.filter (fun ℓ => u ℓ ≠ v ℓ)).card ∧
      1 / 2 * ∑ ℓ, |u ℓ - v ℓ| = t + 1 / 2 * ∑ ℓ, |w ℓ - v ℓ| := by
  have hb : ∃ b, v b < u b := by
    by_contra h
    push_neg at h
    apply hne
    funext ℓ
    have := (Finset.sum_eq_sum_iff_of_le (fun i _ => h i)).mp (by rw [hu.2, hv.2])
    exact this ℓ (Finset.mem_univ ℓ)
  have ha : ∃ a, u a < v a := by
    by_contra h
    push_neg at h
    apply hne
    funext ℓ
    have := (Finset.sum_eq_sum_iff_of_le (fun i _ => h i)).mp (by rw [hu.2, hv.2])
    exact (this ℓ (Finset.mem_univ ℓ)).symm
  obtain ⟨b, hb⟩ := hb
  obtain ⟨a, ha⟩ := ha
  have hab : a ≠ b := by
    rintro rfl
    linarith
  obtain ⟨t, ht⟩ : ∃ t, t = min (u b - v b) (v a - u a) := ⟨_, rfl⟩
  have ht1 : t ≤ u b - v b := by rw [ht]; exact min_le_left _ _
  have ht2 : t ≤ v a - u a := by rw [ht]; exact min_le_right _ _
  have htpos : 0 < t := by rw [ht]; exact lt_min (by linarith) (by linarith)
  have hvb := hv.1 b
  refine ⟨ijShift u a b t, t, sh_mem u hu hab htpos.le (by linarith),
    pair u hu hab hδ htpos.le (by linarith), ?_, ?_⟩
  · apply Finset.card_lt_card
    have hs : (Finset.univ.filter (fun ℓ => ijShift u a b t ℓ ≠ v ℓ)) ⊆
        (Finset.univ.filter (fun ℓ => u ℓ ≠ v ℓ)) := by
      intro ℓ hℓ
      rw [Finset.mem_filter] at hℓ ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      by_cases h1 : ℓ = a
      · rw [h1]; exact ha.ne
      · by_cases h2 : ℓ = b
        · rw [h2]; exact hb.ne'
        · rw [sh_o _ h1 h2] at hℓ; exact hℓ.2
    rw [Finset.ssubset_iff_of_subset hs]
    rcases le_total (u b - v b) (v a - u a) with h | h
    · refine ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb.ne'⟩, ?_⟩
      rw [Finset.mem_filter, sh_b _ hab, ht, min_eq_left h]
      simp
    · refine ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha.ne⟩, ?_⟩
      rw [Finset.mem_filter, sh_a _ hab, ht, min_eq_right h]
      simp
  · have hpt : ∀ ℓ, |u ℓ - v ℓ| = |ijShift u a b t ℓ - v ℓ| +
        t * ((if ℓ = a then (1:ℝ) else 0) + (if ℓ = b then (1:ℝ) else 0)) := by
      intro ℓ
      by_cases h1 : ℓ = a
      · rw [h1, sh_a _ hab, if_pos rfl, if_neg hab,
          abs_of_neg (show u a - v a < 0 by linarith),
          abs_of_nonpos (show u a + t - v a ≤ 0 by linarith)]
        ring
      · by_cases h2 : ℓ = b
        · rw [h2, sh_b _ hab, if_neg (Ne.symm hab), if_pos rfl,
            abs_of_pos (show (0:ℝ) < u b - v b by linarith),
            abs_of_nonneg (show (0:ℝ) ≤ u b - t - v b by linarith)]
          ring
        · rw [sh_o _ h1 h2, if_neg h1, if_neg h2]
          ring
    rw [Finset.sum_congr rfl (fun ℓ _ => hpt ℓ), Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true]
    ring

lemma transport {δ : ℝ} (hδ : 0 < δ) : ∀ n : ℕ, ∀ u v : Fin k → ℝ,
    u ∈ stdSimplex ℝ (Fin k) → v ∈ stdSimplex ℝ (Fin k) →
    (Finset.univ.filter (fun ℓ => u ℓ ≠ v ℓ)).card ≤ n →
    Reach δ (1 / 2 * ∑ ℓ, |u ℓ - v ℓ|) u v := by
  intro n
  induction n with
  | zero =>
    intro u v hu hv hc
    by_cases heq : u = v
    · subst heq
      simpa using (reach_refl hu : Reach δ 0 u u)
    · obtain ⟨w, t, hw, hr, hcard, hsum⟩ := decrease hδ u v hu hv heq
      omega
  | succ n ih =>
    intro u v hu hv hc
    by_cases heq : u = v
    · subst heq
      simpa using (reach_refl hu : Reach δ 0 u u)
    · obtain ⟨w, t, hw, hr, hcard, hsum⟩ := decrease hδ u v hu hv heq
      rw [hsum]
      exact reach_trans hr (ih w v hw hv (by omega))

lemma reach_main (u v : Fin k → ℝ) (hu : u ∈ stdSimplex ℝ (Fin k))
    (hv : v ∈ stdSimplex ℝ (Fin k)) (δ : ℝ) (hδ : 0 < δ) :
    Reach δ (1 / 2 * ∑ ℓ, |u ℓ - v ℓ|) u v :=
  transport hδ _ u v hu hv le_rfl

end Aux_MultiwayCut_observation_2_1

open MultiwayCut in
theorem solution {k : ℕ} (u v : Fin k → ℝ) (hu : u ∈ stdSimplex ℝ (Fin k))
    (hv : v ∈ stdSimplex ℝ (Fin k)) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (m : ℕ) (y : Fin (m + 1) → Fin k → ℝ) (π : Fin m → Equiv.Perm (Fin k))
      (i j : Fin m → Fin k) (ε : Fin m → ℝ),
      y 0 = u ∧ y (Fin.last m) = v ∧
      (∀ s : Fin m, ε s ≤ δ ∧
        (IsIJEdge (π s) (i s) (j s) (ε s) (y s.castSucc) (y s.succ) ∨
          IsIJEdge (π s) (i s) (j s) (ε s) (y s.succ) (y s.castSucc))) ∧
      ∑ s, ε s = 1 / 2 * ∑ ℓ, |u ℓ - v ℓ| := by
  obtain ⟨m, y, π, i, j, ε, h0, hm, hs, hL⟩ :=
    Aux_MultiwayCut_observation_2_1.reach_main u v hu hv δ hδ
  refine ⟨m, fun r => y r.val, fun s => π s.val, fun s => i s.val, fun s => j s.val,
    fun s => ε s.val, by simpa using h0, by simpa using hm, fun s => ?_, ?_⟩
  · have := hs s.val s.isLt
    simpa [Fin.val_succ] using this
  · rw [← hL]
    exact Fin.sum_univ_eq_sum_range ε m
