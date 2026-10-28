-- Prove2me | solution 1 for Kurodoko.NPC.compress_preconnected_iff
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-26T23:14:54.57167+00:00
-- url     : https://prove2.me/submissions/bcd9fbf1-23c1-4226-8f91-1bf47455aaee

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_Kurodoko_NPC_Puzzle

open CookPvsNP ProjSchedTW.Complexity Kurodoko.NPC

namespace KuroCompress

theorem liftR {α β : Type} {r : α → α → Prop} {p : β → β → Prop} (f : α → β)
    (h : ∀ a b, r a b → Relation.ReflTransGen p (f a) (f b)) {a b : α}
    (hab : Relation.ReflTransGen r a b) : Relation.ReflTransGen p (f a) (f b) := by
  induction hab with
  | refl => exact .refl
  | tail _ hbc ih => exact ih.trans (h _ _ hbc)

def fR (r : ℕ) (v : Cell) : Cell := if r < v.1 then (v.1 - 1, v.2) else v
def gR (r : ℕ) (v : Cell) : Cell := if r < v.1 then (v.1 + 1, v.2) else v

theorem rows_iff (w h : ℕ) (B : Finset Cell) (r : ℕ) (hr : r + 1 < h)
    (hfree : ∀ v ∈ B, v.1 ≠ r ∧ v.1 ≠ r + 1) :
    Rule3 w h B ↔ Rule3 w (h - 1) (B.image (fR r)) := by
  set B' := B.image (fR r) with hB'
  have hfg : ∀ y, fR r (gR r y) = y := by
    rintro ⟨a, b⟩; simp only [fR, gR]; split_ifs <;> simp_all <;> omega
  have whiteF : ∀ u, White w h B u → White w (h - 1) B' (fR r u) := by
    rintro ⟨u1, u2⟩ ⟨⟨hu1, hu2⟩, huB⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp only [fR]; split_ifs <;> simp <;> omega
    · simp only [fR]; split_ifs <;> simp <;> omega
    · intro hm
      rcases Finset.mem_image.1 hm with ⟨⟨b1, b2⟩, hb, hbe⟩
      have hf := hfree _ hb
      simp only at hf
      have : u1 = b1 ∧ u2 = b2 := by
        simp only [fR] at hbe
        split_ifs at hbe <;> simp [Prod.ext_iff] at hbe <;> omega
      obtain ⟨rfl, rfl⟩ := this
      exact huB hb
  have whiteG : ∀ y, White w (h - 1) B' y → White w h B (gR r y) := by
    rintro ⟨y1, y2⟩ ⟨⟨hy1, hy2⟩, hyB⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp only [gR]; split_ifs <;> simp <;> omega
    · simp only [gR]; split_ifs <;> simp <;> omega
    · intro hm
      apply hyB
      rw [← hfg (y1, y2)]
      exact Finset.mem_image_of_mem _ hm
  have adjF : ∀ u v, Adj u v → fR r u = fR r v ∨ Adj (fR r u) (fR r v) := by
    rintro ⟨u1, u2⟩ ⟨v1, v2⟩ huv
    simp only [Adj, fR] at huv ⊢
    split_ifs <;> simp only [Prod.ext_iff] <;> omega
  have stepG : ∀ a b, (Adj a b ∧ White w (h - 1) B' a ∧ White w (h - 1) B' b) →
      Relation.ReflTransGen (fun a b => Adj a b ∧ White w h B a ∧ White w h B b)
        (gR r a) (gR r b) := by
    rintro a b ⟨hab, ha, hb⟩
    by_cases hA : Adj (gR r a) (gR r b)
    · exact Relation.ReflTransGen.single ⟨hA, whiteG a ha, whiteG b hb⟩
    · obtain ⟨a1, a2⟩ := a
      obtain ⟨b1, b2⟩ := b
      have ha2 : a2 < w := ha.1.2
      have hc : a2 = b2 ∧ ((a1 = r ∧ b1 = r + 1) ∨ (a1 = r + 1 ∧ b1 = r)) := by
        simp only [Adj, gR] at hab hA
        split_ifs at hA <;> simp only at hA <;> omega
      obtain ⟨rfl, hc⟩ := hc
      have hm : White w h B (r + 1, a2) := by
        refine ⟨⟨hr, ha2⟩, fun hm => (hfree _ hm).2 rfl⟩
      have hga := whiteG _ ha
      have hgb := whiteG _ hb
      rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have e1 : gR a1 (a1, a2) = (a1, a2) := by simp [gR]
        have e2 : gR a1 (a1 + 1, a2) = (a1 + 2, a2) := by simp [gR]
        rw [e1] at hga ⊢
        rw [e2] at hgb ⊢
        refine Relation.ReflTransGen.tail (Relation.ReflTransGen.single ⟨?_, hga, hm⟩) ⟨?_, hm, hgb⟩
        · simp [Adj]
        · simp [Adj]
      · have e1 : gR b1 (b1, a2) = (b1, a2) := by simp [gR]
        have e2 : gR b1 (b1 + 1, a2) = (b1 + 2, a2) := by simp [gR]
        rw [e2] at hga ⊢
        rw [e1] at hgb ⊢
        refine Relation.ReflTransGen.tail (Relation.ReflTransGen.single ⟨?_, hga, hm⟩) ⟨?_, hm, hgb⟩
        · simp [Adj]
        · simp [Adj]
  have back : ∀ u, White w h B u →
      Relation.ReflTransGen (fun a b => Adj a b ∧ White w h B a ∧ White w h B b) u (gR r (fR r u)) ∧
      Relation.ReflTransGen (fun a b => Adj a b ∧ White w h B a ∧ White w h B b) (gR r (fR r u)) u := by
    rintro ⟨u1, u2⟩ hu
    by_cases h1 : u1 = r + 1
    · subst h1
      have e : gR r (fR r (r + 1, u2)) = (r, u2) := by simp [gR, fR]
      rw [e]
      have hm : White w h B (r, u2) := ⟨⟨by omega, hu.1.2⟩, fun hm => (hfree _ hm).1 rfl⟩
      exact ⟨Relation.ReflTransGen.single ⟨by simp [Adj], hu, hm⟩,
        Relation.ReflTransGen.single ⟨by simp [Adj], hm, hu⟩⟩
    · have e : gR r (fR r (u1, u2)) = (u1, u2) := by
        simp only [gR, fR]; split_ifs <;> simp <;> omega
      rw [e]
      exact ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  constructor
  · intro H y1 y2 hy1 hy2
    have p := H _ _ (whiteG _ hy1) (whiteG _ hy2)
    have q := liftR (fR r) (p := fun a b => Adj a b ∧ White w (h - 1) B' a ∧ White w (h - 1) B' b) (fun a b hab => by
      rcases adjF a b hab.1 with he | hadj
      · rw [he]
      · exact Relation.ReflTransGen.single ⟨hadj, whiteF a hab.2.1, whiteF b hab.2.2⟩) p
    rwa [hfg, hfg] at q
  · intro H u v hu hv
    have p := H _ _ (whiteF _ hu) (whiteF _ hv)
    have q := liftR (gR r) stepG p
    exact ((back u hu).1.trans q).trans (back v hv).2


theorem white_swap (w h : ℕ) (B : Finset Cell) (y : Cell) :
    White h w (B.image Prod.swap) y ↔ White w h B y.swap := by
  obtain ⟨a, b⟩ := y
  simp only [White, OnBoard, Prod.swap_prod_mk, Finset.mem_image, Prod.exists, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h2, h1⟩, fun hm => h3 ⟨b, a, hm, rfl, rfl⟩⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨h2, h1⟩, ?_⟩
    rintro ⟨x, y, hm, rfl, rfl⟩
    exact h3 hm

theorem rule3_swap_imp (w h : ℕ) (B : Finset Cell) (H : Rule3 w h B) :
    Rule3 h w (B.image Prod.swap) := by
  intro y1 y2 hy1 hy2
  have p := H _ _ ((white_swap w h B y1).1 hy1) ((white_swap w h B y2).1 hy2)
  have q := liftR Prod.swap
    (p := fun a b => Adj a b ∧ White h w (B.image Prod.swap) a ∧ White h w (B.image Prod.swap) b)
    (fun a b hab => by
      refine Relation.ReflTransGen.single ⟨?_, ?_, ?_⟩
      · obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := (⟨a, b⟩ : Cell × Cell)
        have := hab.1
        simp only [Adj, Prod.fst_swap, Prod.snd_swap] at this ⊢
        omega
      · rw [white_swap]; simpa using hab.2.1
      · rw [white_swap]; simpa using hab.2.2) p
  simpa using q

theorem rule3_swap (w h : ℕ) (B : Finset Cell) :
    Rule3 w h B ↔ Rule3 h w (B.image Prod.swap) := by
  refine ⟨rule3_swap_imp w h B, fun H => ?_⟩
  have := rule3_swap_imp h w _ H
  rwa [Finset.image_image, show Prod.swap ∘ Prod.swap = (id : Cell → Cell) from
    funext fun x => by simp, Finset.image_id] at this

theorem cols_iff (w h : ℕ) (B : Finset Cell) (c : ℕ) (hc : c + 1 < w)
    (hfree : ∀ v ∈ B, v.2 ≠ c ∧ v.2 ≠ c + 1) :
    Rule3 w h B ↔
      Rule3 (w - 1) h (B.image fun v => if c < v.2 then (v.1, v.2 - 1) else v) := by
  rw [rule3_swap, rows_iff h w _ c hc (by
      intro v hv
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hv
      simpa using hfree u hu), rule3_swap, Finset.image_image, Finset.image_image]
  congr! 2
  funext ⟨a, b⟩
  simp only [Function.comp, fR, Prod.swap_prod_mk]
  split_ifs <;> rfl

theorem rows_bound (h : ℕ) (B : Finset Cell)
    (H : ∀ r, r + 1 < h → ∃ v ∈ B, v.1 = r ∨ v.1 = r + 1) : h ≤ 2 * B.card + 1 := by
  have hsub : Finset.range (h - 1) ⊆ B.biUnion fun b => ({b.1 - 1, b.1} : Finset ℕ) := by
    intro r hr
    rw [Finset.mem_range] at hr
    obtain ⟨v, hv, hv'⟩ := H r (by omega)
    rw [Finset.mem_biUnion]
    refine ⟨v, hv, ?_⟩
    rcases hv' with h1 | h1 <;> simp <;> omega
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_biUnion_le (s := B) (t := fun b => ({b.1 - 1, b.1} : Finset ℕ))
  have h3 : ∑ b ∈ B, ({b.1 - 1, b.1} : Finset ℕ).card ≤ ∑ _b ∈ B, 2 :=
    Finset.sum_le_sum fun b _ => Finset.card_le_two
  simp only [Finset.sum_const, smul_eq_mul, Finset.card_range] at h1 h3
  omega

end KuroCompress

theorem solution (w h : ℕ) (B : Finset Cell) (hB : ∀ v ∈ B, OnBoard w h v) :
    (∀ r, r + 1 < h → (∀ v ∈ B, v.1 ≠ r ∧ v.1 ≠ r + 1) →
      (Rule3 w h B ↔
        Rule3 w (h - 1) (B.image fun v => if r < v.1 then (v.1 - 1, v.2) else v))) ∧
    (∀ c, c + 1 < w → (∀ v ∈ B, v.2 ≠ c ∧ v.2 ≠ c + 1) →
      (Rule3 w h B ↔
        Rule3 (w - 1) h (B.image fun v => if c < v.2 then (v.1, v.2 - 1) else v))) ∧
    ((∀ r, r + 1 < h → ∃ v ∈ B, v.1 = r ∨ v.1 = r + 1) → h ≤ 2 * B.card + 1) ∧
    ((∀ c, c + 1 < w → ∃ v ∈ B, v.2 = c ∨ v.2 = c + 1) → w ≤ 2 * B.card + 1) := by
  refine ⟨fun r hr hf => KuroCompress.rows_iff w h B r hr hf,
    fun c hc hf => KuroCompress.cols_iff w h B c hc hf,
    fun H => KuroCompress.rows_bound h B H, fun H => ?_⟩
  have := KuroCompress.rows_bound w (B.image Prod.swap) (by
    intro c hc
    obtain ⟨v, hv, hv'⟩ := H c hc
    exact ⟨v.swap, Finset.mem_image_of_mem _ hv, by simpa using hv'⟩)
  have hc : (B.image Prod.swap).card = B.card :=
    Finset.card_image_of_injective _ Prod.swap_injective
  omega

