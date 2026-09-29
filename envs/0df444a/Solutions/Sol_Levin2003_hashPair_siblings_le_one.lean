-- Prove2me | solution 1 for Levin2003.hashPair_siblings_le_one
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T22:16:51.860952+00:00
-- url     : https://prove2.me/submissions/b1b5fc70-9172-4c41-bdcb-3d75d028f44c

import Definitions.Def_Levin2003_tiling_expansion

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
open Levin2003

theorem solution (n : ℕ) (hn : n ≠ 0)
    (f : GaloisField 2 n → GaloisField 2 n) :
    {pq : (GaloisField 2 n × GaloisField 2 n) × (GaloisField 2 n × GaloisField 2 n) |
        pq.1 ≠ pq.2 ∧ hashPair f pq.1 = hashPair f pq.2}.ncard
      ≤ Nat.card (GaloisField 2 n × GaloisField 2 n) := by
  classical
  rw [← Set.ncard_univ]
  refine Set.ncard_le_ncard_of_injOn (fun pq => (pq.1.2, pq.2.2))
    (fun _ _ => Set.mem_univ _) ?_ (Set.toFinite _)
  rintro ⟨⟨a, x⟩, ⟨b, y⟩⟩ ⟨hne, hh⟩ ⟨⟨a', x'⟩, ⟨b', y'⟩⟩ ⟨hne', hh'⟩ heq
  simp only [hashPair, Prod.mk.injEq] at hh hh' heq hne hne' ⊢
  obtain ⟨hx, hy⟩ := heq
  obtain ⟨hab, h1⟩ := hh
  obtain ⟨hab', h2⟩ := hh'
  have hxy : x - y ≠ 0 := fun h => hne (by rw [hab, sub_eq_zero.mp h])
  rw [← hab] at h1
  rw [← hab', ← hx, ← hy] at h2
  have hm : (a - a') * (x - y) = 0 := by linear_combination h1 - h2
  rcases mul_eq_zero.mp hm with h | h
  · have aa : a = a' := sub_eq_zero.mp h
    exact ⟨⟨aa, hx⟩, ⟨hab.symm.trans (aa.trans hab'), hy⟩⟩
  · exact absurd h hxy

theorem W3b_Levin2003_allBits_len : ∀ (l : ℕ) (b : Bits), b ∈ allBits l → b.length = l
  | 0, b, h => by
    simp only [allBits, List.mem_singleton] at h
    simp [h]
  | l + 1, b, h => by
    simp only [allBits, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at h
    obtain ⟨a, ha, rfl | rfl⟩ := h <;> simp [W3b_Levin2003_allBits_len l a ha]

theorem W3b_Levin2003_allTiles_len (l : ℕ) (t : Tile Bits) (h : t ∈ allTiles l) :
    t.tl.length = l ∧ t.tr.length = l ∧ t.bl.length = l ∧ t.br.length = l := by
  simp only [allTiles, List.mem_flatMap, List.mem_map] at h
  obtain ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ := h
  exact ⟨W3b_Levin2003_allBits_len _ _ ha, W3b_Levin2003_allBits_len _ _ hb,
    W3b_Levin2003_allBits_len _ _ hc, W3b_Levin2003_allBits_len _ _ hd⟩

theorem W3b_Levin2003_forced_mem {T : List (Tile Bits)} {lab : Lab Bits} {i j : ℕ}
    {t : Tile Bits} (h : forcedTile T lab i j = some t) : t ∈ T := by
  unfold forcedTile at h
  split at h
  next t' heq =>
    have hm : t' ∈ [t'] := List.mem_singleton_self t'
    rw [← heq] at hm
    rw [← Option.some.inj h]
    exact (List.mem_filter.mp hm).1
  next => simp at h

theorem W3b_Levin2003_cell {N : ℕ} {T : List (Tile Bits)} {lab : Lab Bits} {a b : ℕ}
    {t : Tile Bits} (h : (if a < N ∧ b < N then forcedTile T lab a b else none) = some t) :
    t ∈ T := by
  split_ifs at h <;> first | exact W3b_Levin2003_forced_mem h | simp at h

theorem W3b_Levin2003_orElse {o₁ o₂ : Option Bits} {a : Bits}
    (h : (o₁.orElse fun _ => o₂) = some a) : o₁ = some a ∨ o₂ = some a := by
  cases o₁ <;> simp_all [Option.orElse]

theorem W3b_Levin2003_map {T : List (Tile Bits)} {l : ℕ} {g : Tile Bits → Bits}
    {o : Option (Tile Bits)} {a : Bits}
    (hg : ∀ t ∈ T, (g t).length = l) (ho : ∀ t, o = some t → t ∈ T)
    (h : o.map g = some a) : a.length = l := by
  obtain _ | t := o
  · simp at h
  · simp at h
    subst h
    exact hg t (ho t rfl)

theorem W3b_Levin2003_mapif {T : List (Tile Bits)} {l : ℕ} {g : Tile Bits → Bits}
    {c : Prop} [Decidable c] {o : Option (Tile Bits)} {a : Bits}
    (hg : ∀ t ∈ T, (g t).length = l) (ho : ∀ t, o = some t → t ∈ T)
    (h : (if c then o.map g else none) = some a) : a.length = l := by
  split_ifs at h <;> first | exact W3b_Levin2003_map hg ho h | simp at h

theorem W3b_Levin2003_step_inv (N l : ℕ) (T : List (Tile Bits))
    (hT : ∀ t ∈ T, t.tl.length = l ∧ t.tr.length = l ∧ t.bl.length = l ∧ t.br.length = l)
    (lab : Lab Bits) (hlab : ∀ p a, lab p = some a → a.length = l) :
    ∀ p a, stepLab N T lab p = some a → a.length = l := by
  intro p a h
  cases hp : lab p with
  | some b =>
    simp only [stepLab, hp] at h
    cases h
    exact hlab p _ hp
  | none =>
    simp only [stepLab, hp] at h
    rcases W3b_Levin2003_orElse h with h | h
    · exact W3b_Levin2003_map (fun t ht => (hT t ht).1) (fun t ht => W3b_Levin2003_cell ht) h
    rcases W3b_Levin2003_orElse h with h | h
    · exact W3b_Levin2003_mapif (fun t ht => (hT t ht).2.1)
        (fun t ht => W3b_Levin2003_cell ht) h
    rcases W3b_Levin2003_orElse h with h | h
    · exact W3b_Levin2003_mapif (fun t ht => (hT t ht).2.2.1)
        (fun t ht => W3b_Levin2003_cell ht) h
    · exact W3b_Levin2003_mapif (fun t ht => (hT t ht).2.2.2)
        (fun t ht => W3b_Levin2003_cell ht) h

theorem W3b_Levin2003_iter_inv (N l : ℕ) (T : List (Tile Bits))
    (hT : ∀ t ∈ T, t.tl.length = l ∧ t.tr.length = l ∧ t.bl.length = l ∧ t.br.length = l)
    (lab : Lab Bits) (hlab : ∀ p a, lab p = some a → a.length = l) :
    ∀ k p a, iterLab N T lab k p = some a → a.length = l := by
  intro k
  induction k with
  | zero => exact hlab
  | succ k ih => exact W3b_Levin2003_step_inv N l T hT _ ih

theorem W3b_Levin2003_chunks_len (l : ℕ) :
    ∀ (k : ℕ) (x : Bits), k * l ≤ x.length → ∀ c ∈ chunks l k x, c.length = l
  | 0, x, _, c, hc => by simp [chunks] at hc
  | k + 1, x, hx, c, hc => by
    simp only [chunks, List.mem_cons] at hc
    rw [add_mul, one_mul] at hx
    rcases hc with rfl | hc
    · simp only [List.length_take]
      omega
    · exact W3b_Levin2003_chunks_len l k (x.drop l)
        (by simp only [List.length_drop]; omega) c hc

theorem W3b_Levin2003_getD_len {l : ℕ} :
    ∀ (L : List Bits) (j : ℕ) (d : Bits), (∀ c ∈ L, c.length = l) → d.length = l →
      (L.getD j d).length = l
  | [], j, d, _, hd => by simpa using hd
  | c :: L, 0, d, hL, _ => by simpa using hL c (by simp)
  | c :: L, j + 1, d, hL, hd => by
    simpa using W3b_Levin2003_getD_len L j d (fun c' hc' => hL c' (by simp [hc'])) hd

theorem W3b_Levin2003_flat_len (l : ℕ) :
    ∀ (L : List Bits), (∀ c ∈ L, c.length = l) → L.flatten.length = L.length * l
  | [], _ => by simp
  | c :: L, h => by
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    rw [h c (by simp), W3b_Levin2003_flat_len l L (fun c' hc' => h c' (by simp [hc']))]
    ring

theorem W3b_Levin2003_getD_opt {l : ℕ} (o : Option Bits) (d : Bits) (hd : d.length = l)
    (ho : ∀ a, o = some a → a.length = l) : (o.getD d).length = l := by
  cases o with
  | none => simpa using hd
  | some a => simpa using ho a rfl

theorem W3b_Levin2003_tilingExpansion_lengthPreserving : LengthPreserving tilingExpansion := by
  intro x
  unfold tilingExpansion
  split
  · rfl
  · rename_i l mask body hparse
    simp only [parse] at hparse
    split_ifs at hparse with h1 h2
    · simp only [Option.some.injEq, Prod.mk.injEq] at hparse
      obtain ⟨hl, hmask, hbody⟩ := hparse
      rw [hbody] at h2
      have hbl : body.length = x.length - (leadingOnes x + 1) - 2 ^ (4 * leadingOnes x) := by
        rw [← hbody]; simp only [List.length_drop]
      have hml : mask.length = 2 ^ (4 * leadingOnes x) := by
        rw [← hmask]; simp only [List.length_take, List.length_drop]; omega
      subst hl
      have hdvd : body.length / leadingOnes x * leadingOnes x = body.length :=
        Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h2.2)
      have hT : ∀ t ∈ tileSet (leadingOnes x) mask, t.tl.length = leadingOnes x ∧
          t.tr.length = leadingOnes x ∧ t.bl.length = leadingOnes x ∧
          t.br.length = leadingOnes x := fun t ht =>
        W3b_Levin2003_allTiles_len _ t (List.mem_filter.mp ht).1
      have hblank : (List.replicate (leadingOnes x) false).length = leadingOnes x := by simp
      have htop : ∀ c ∈ chunks (leadingOnes x) (body.length / leadingOnes x) body,
          c.length = leadingOnes x :=
        W3b_Levin2003_chunks_len _ _ _ (by rw [hdvd])
      simp only [expansion, List.length_append, List.length_replicate, List.length_cons]
      rw [W3b_Levin2003_flat_len (leadingOnes x) _ ?hall]
      · simp only [List.length_map, List.length_range]
        rw [hdvd]
        omega
      · intro c hc
        rw [List.mem_map] at hc
        obtain ⟨j, -, rfl⟩ := hc
        apply W3b_Levin2003_getD_opt _ _ hblank
        intro a ha
        refine W3b_Levin2003_iter_inv _ _ _ hT _ ?_ _ _ _ ha
        intro p a' h
        (try simp only at h)
        split_ifs at h
        cases h
        exact W3b_Levin2003_getD_len _ _ _ htop hblank
