-- Prove2me | solution 1 for LNTopology.Hermetization.theorem_3_8_hermetizable_polytime
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-05T01:49:00.585101+00:00
-- url     : https://prove2.me/submissions/7a2d761e-4277-4378-bdbf-eca1ba8be8a7

import Mathlib
import Definitions.Def_LNTopology_Hermetization_IsLN
import Definitions.Def_LNTopology_Hermetization_CostAxioms
import Definitions.Def_LNTopology_Hermetization_avgDeg
import Definitions.Def_LNTopology_Hermetization_disc
import Definitions.Def_LNTopology_Hermetization_Hermetizable
import Definitions.Def_LNTopology_Hermetization_LNHermetizable
import Definitions.Def_LNTopology_Hermetization_findHermetizable

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LNC

open LNTopology.Hermetization

/-! ## A weakest-precondition calculus for tick-counting programs -/

def WP {α : Type} (m : StateM ℕ α) (P : α → ℕ → Prop) : Prop :=
  ∀ s : ℕ, ∃ k : ℕ, (m.run s).2 = s + k ∧ P (m.run s).1 k

theorem WP_pure {α : Type} {a : α} {P : α → ℕ → Prop} (h : P a 0) :
    WP (pure a : StateM ℕ α) P := fun _ => ⟨0, rfl, h⟩

theorem WP_mono {α : Type} {m : StateM ℕ α} {P Q : α → ℕ → Prop} (h : WP m P)
    (hPQ : ∀ a k, P a k → Q a k) : WP m Q := fun s =>
  let ⟨k, h1, h2⟩ := h s
  ⟨k, h1, hPQ _ _ h2⟩

theorem WP_bind {α β : Type} {m : StateM ℕ α} {f : α → StateM ℕ β} {P : β → ℕ → Prop}
    (h : WP m (fun a k1 => WP (f a) (fun b k2 => P b (k1 + k2)))) : WP (m >>= f) P := by
  intro s
  obtain ⟨k1, h1, h2⟩ := h s
  obtain ⟨k2, h3, h4⟩ := h2 (m.run s).2
  have e : (m >>= f).run s = (f (m.run s).1).run (m.run s).2 := by
    simp only [StateT.run_bind]; rfl
  refine ⟨k1 + k2, ?_, ?_⟩
  · rw [e, h3, h1, Nat.add_assoc]
  · rw [e]; exact h4

theorem WP_ite {α : Type} {c : Prop} [Decidable c] {A B : StateM ℕ α} {P : α → ℕ → Prop}
    (h1 : c → WP A P) (h2 : ¬ c → WP B P) : WP (if c then A else B) P := by
  by_cases hc : c
  · rw [if_pos hc]; exact h1 hc
  · rw [if_neg hc]; exact h2 hc

theorem tick_wp (j : ℕ) : WP (tick j) (fun _ k => k = j) := fun _ => ⟨j, rfl, rfl⟩

theorem WP_tick_bind {β : Type} {j : ℕ} {f : Unit → StateM ℕ β} {P : β → ℕ → Prop}
    (h : WP (f ()) (fun b k2 => P b (j + k2))) : WP (tick j >>= f) P :=
  WP_bind (WP_mono (tick_wp j) (fun _ k hk => by subst hk; exact h))

theorem prim_bind {α β : Type} {m : StateM ℕ α} {x : α} {f : α → StateM ℕ β}
    {P : β → ℕ → Prop} (hm : WP m (fun a k => a = x ∧ k = 1))
    (h : WP (f x) (fun b k2 => P b (1 + k2))) : WP (m >>= f) P :=
  WP_bind (WP_mono hm (fun a k hak => by obtain ⟨ha, hk⟩ := hak; subst ha; subst hk; exact h))

theorem lamAt_wp {V : Type} (lam : V → V → ℝ) (i j : V) :
    WP (lamAt lam i j) (fun a k => a = lam i j ∧ k = 1) := by
  unfold lamAt; exact WP_tick_bind (WP_pure ⟨rfl, rfl⟩)
theorem cAt_wp (c : ℝ → ℝ) (x : ℝ) : WP (cAt c x) (fun a k => a = c x ∧ k = 1) := by
  unfold cAt; exact WP_tick_bind (WP_pure ⟨rfl, rfl⟩)
theorem gAt_wp (g : ℝ → ℝ) (x : ℝ) : WP (gAt g x) (fun a k => a = g x ∧ k = 1) := by
  unfold gAt; exact WP_tick_bind (WP_pure ⟨rfl, rfl⟩)
theorem rlt_wp (x y : ℝ) : WP (rlt x y) (fun a k => a = decide (x < y) ∧ k = 1) := by
  unfold rlt; exact WP_tick_bind (WP_pure ⟨rfl, rfl⟩)
theorem rle_wp (x y : ℝ) : WP (rle x y) (fun a k => a = decide (x ≤ y) ∧ k = 1) := by
  unfold rle; exact WP_tick_bind (WP_pure ⟨rfl, rfl⟩)
theorem req_wp (x y : ℝ) : WP (req x y) (fun a k => a = decide (x = y) ∧ k = 1) := by
  unfold req; exact WP_tick_bind (WP_pure ⟨rfl, rfl⟩)
theorem rabs_wp (x : ℝ) : WP (rabs x) (fun a k => a = |x| ∧ k = 1) := by
  unfold rabs; exact WP_tick_bind (WP_pure ⟨rfl, rfl⟩)
theorem rmul_wp (x y : ℝ) : WP (rmul x y) (fun a k => a = x * y ∧ k = 1) := by
  unfold rmul; exact WP_tick_bind (WP_pure ⟨rfl, rfl⟩)
theorem rdiv_wp (x y : ℝ) : WP (rdiv x y) (fun a k => a = x / y ∧ k = 1) := by
  unfold rdiv; exact WP_tick_bind (WP_pure ⟨rfl, rfl⟩)
theorem badAt_wp (bad : ℕ → Prop) [DecidablePred bad] (d : ℕ) :
    WP (badAt bad d) (fun a k => a = decide (bad d) ∧ k = 1) := by
  unfold badAt; exact WP_tick_bind (WP_pure ⟨rfl, rfl⟩)

theorem WP_forIn_aux {α β : Type} (xs : List α) (f : α → β → StateM ℕ (ForInStep β))
    (I : List α → β → ℕ → Prop)
    (hs : ∀ pre x suf b k, pre ++ x :: suf = xs → I pre b k →
        WP (f x b) (fun r k' => ∃ b', r = ForInStep.yield b' ∧ I (pre ++ [x]) b' (k + k'))) :
    ∀ (suf pre : List α) (b : β) (k : ℕ), pre ++ suf = xs → I pre b k →
      WP (forIn suf b f) (fun r k' => I xs r (k + k')) := by
  intro suf
  induction suf with
  | nil =>
    intro pre b k hpre hI
    rw [List.forIn_nil]
    refine WP_pure ?_
    simp only [List.append_nil] at hpre
    subst hpre
    simpa using hI
  | cons x suf ih =>
    intro pre b k hpre hI
    rw [List.forIn_cons]
    refine WP_bind (WP_mono (hs pre x suf b k hpre hI) ?_)
    rintro r k' ⟨b', rfl, hI'⟩
    have := ih (pre ++ [x]) b' (k + k') (by rw [← hpre]; simp) hI'
    refine WP_mono this ?_
    intro r k2 h
    simpa [Nat.add_assoc] using h

theorem WP_forIn_bind {α β γ : Type} {xs : List α} {b : β} {f : α → β → StateM ℕ (ForInStep β)}
    {g : β → StateM ℕ γ} {P : γ → ℕ → Prop} (I : List α → β → ℕ → Prop) (h0 : I [] b 0)
    (hs : ∀ pre x suf b k, pre ++ x :: suf = xs → I pre b k →
        WP (f x b) (fun r k' => ∃ b', r = ForInStep.yield b' ∧ I (pre ++ [x]) b' (k + k')))
    (hg : ∀ r k, I xs r k → WP (g r) (fun c k2 => P c (k + k2))) :
    WP (forIn xs b f >>= g) P := by
  refine WP_bind (WP_mono (WP_forIn_aux xs f I hs xs [] b 0 (by simp) h0) ?_)
  intro r k h
  exact hg r k (by simpa using h)

theorem not_mem_pre {α : Type} {xs pre suf : List α} {x : α} (hnd : xs.Nodup)
    (h : pre ++ x :: suf = xs) : x ∉ pre := by
  subst h
  have := List.nodup_middle.mp hnd
  intro hx
  exact (List.nodup_cons.mp this).1 (List.mem_append_left _ hx)

/-! ## Bookkeeping for the peeling algorithm -/

section Peel
variable {n : ℕ}

def decN (adj : Fin n → List (Fin n)) (rem : Fin n → Bool) (x : Fin n) : ℕ :=
  (Finset.univ.filter (fun v => rem v = true ∧ x ∈ adj v)).card

def cntN (adj : Fin n → List (Fin n)) (rem : Fin n → Bool) (x : Fin n) : ℕ :=
  (Finset.univ.filter (fun y => y ∈ adj x ∧ rem y = false)).card

def asum (adj : Fin n → List (Fin n)) (rem : Fin n → Bool) : ℕ :=
  ∑ x, if rem x = false then (adj x).length - decN adj rem x else 0

def ncard (rem : Fin n → Bool) : ℕ := (Finset.univ.filter (fun v => rem v = true)).card

theorem decN_update (adj : Fin n → List (Fin n)) (rem : Fin n → Bool) (v x : Fin n)
    (hv : rem v = false) :
    decN adj (Function.update rem v true) x = decN adj rem x + (if x ∈ adj v then 1 else 0) := by
  unfold decN
  split_ifs with hx
  · have e : Finset.univ.filter (fun u => Function.update rem v true u = true ∧ x ∈ adj u)
        = insert v (Finset.univ.filter (fun u => rem u = true ∧ x ∈ adj u)) := by
      ext u
      by_cases huv : u = v
      · subst huv; simp [hx]
      · simp [Function.update_apply, huv]
    rw [e, Finset.card_insert_of_notMem (by simp [hv])]
  · have e : Finset.univ.filter (fun u => Function.update rem v true u = true ∧ x ∈ adj u)
        = Finset.univ.filter (fun u => rem u = true ∧ x ∈ adj u) := by
      ext u
      by_cases huv : u = v
      · subst huv; simp [hx, hv]
      · simp [Function.update_apply, huv]
    rw [e, add_zero]

theorem ncard_update (rem : Fin n → Bool) (v : Fin n) (hv : rem v = false) :
    ncard (Function.update rem v true) = ncard rem + 1 := by
  unfold ncard
  have e : Finset.univ.filter (fun u => Function.update rem v true u = true)
      = insert v (Finset.univ.filter (fun u => rem u = true)) := by
    ext u
    by_cases huv : u = v
    · subst huv; simp
    · simp [Function.update_apply, huv]
  rw [e, Finset.card_insert_of_notMem (by simp [hv])]

theorem ncard_le (rem : Fin n → Bool) : ncard rem ≤ n := by
  unfold ncard
  exact (Finset.card_le_univ _).trans (by simp)

theorem cnt_eq (adj : Fin n → List (Fin n)) (hnd : ∀ v, (adj v).Nodup)
    (hsym : ∀ v w, w ∈ adj v ↔ v ∈ adj w) (rem : Fin n → Bool) (x : Fin n) :
    (adj x).length - decN adj rem x = cntN adj rem x := by
  have h1 : (adj x).length = (Finset.univ.filter (fun y => y ∈ adj x)).card := by
    rw [← List.toFinset_card_of_nodup (hnd x)]
    congr 1
    ext y
    simp
  have h2 : (Finset.univ.filter (fun y => y ∈ adj x)).card =
      (Finset.univ.filter (fun y => y ∈ adj x ∧ rem y = true)).card + cntN adj rem x := by
    unfold cntN
    rw [← Finset.card_filter_add_card_filter_not (s := Finset.univ.filter (fun y => y ∈ adj x))
      (fun y => rem y = true)]
    simp only [Finset.filter_filter, Bool.not_eq_true]
  have h3 : decN adj rem x = (Finset.univ.filter (fun y => y ∈ adj x ∧ rem y = true)).card := by
    unfold decN
    congr 1
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hsym y x]
    exact and_comm
  omega

theorem asum_update (adj : Fin n → List (Fin n)) (hnd : ∀ v, (adj v).Nodup)
    (hsym : ∀ v w, w ∈ adj v ↔ v ∈ adj w) (rem : Fin n → Bool) (v : Fin n)
    (hv : rem v = false) :
    asum adj rem ≤ asum adj (Function.update rem v true) + 2 * ((adj v).length - decN adj rem v) := by
  have hE : ∀ r : Fin n → Bool, asum adj r = ∑ x, if r x = false then cntN adj r x else 0 := by
    intro r
    unfold asum
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [cnt_eq adj hnd hsym r x]
  rw [hE, hE, cnt_eq adj hnd hsym rem v]
  have key : ∀ x, (if rem x = false then cntN adj rem x else 0) ≤
      (if Function.update rem v true x = false then cntN adj (Function.update rem v true) x else 0)
      + (if x = v then cntN adj rem v else 0)
      + (if rem x = false ∧ x ∈ adj v then 1 else 0) := by
    intro x
    by_cases hxv : x = v
    · subst hxv; simp [hv]
    · have hux : Function.update rem v true x = rem x := Function.update_of_ne hxv _ _
      rw [hux]
      by_cases hrx : rem x = false
      · simp only [hrx, if_true, hxv, if_false, true_and, add_zero]
        unfold cntN
        by_cases hxa : x ∈ adj v
        · rw [if_pos hxa]
          calc (Finset.univ.filter (fun y => y ∈ adj x ∧ rem y = false)).card
              ≤ (insert v (Finset.univ.filter
                  (fun y => y ∈ adj x ∧ Function.update rem v true y = false))).card := by
                apply Finset.card_le_card
                intro y hy
                simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert] at hy ⊢
                by_cases hyv : y = v
                · left; exact hyv
                · right; refine ⟨hy.1, ?_⟩
                  rw [Function.update_of_ne hyv]; exact hy.2
            _ ≤ _ := Finset.card_insert_le _ _
        · rw [if_neg hxa, add_zero]
          apply Finset.card_le_card
          intro y hy
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
          refine ⟨hy.1, ?_⟩
          have hyv : y ≠ v := by
            rintro rfl
            exact hxa ((hsym x y).mp hy.1)
          rw [Function.update_of_ne hyv]; exact hy.2
      · simp [hrx]
  have hsum := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset (Fin n))) => key x)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  have hA : (∑ x : Fin n, if x = v then cntN adj rem v else 0) = cntN adj rem v := by
    simp
  have hB : (∑ x : Fin n, if rem x = false ∧ x ∈ adj v then 1 else 0) = cntN adj rem v := by
    rw [← Finset.card_filter]
    unfold cntN
    congr 1
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_comm
  rw [hA, hB] at hsum
  omega

theorem peel_spec (adj : Fin n → List (Fin n)) (bad : ℕ → Prop) [DecidablePred bad]
    (hlen : ∀ v, (adj v).length ≤ n) (hnd : ∀ v, (adj v).Nodup) :
    WP (peel adj bad) (fun H k => k ≤ 3 * n * n + 6 * n + 1 ∧
      ((∀ v w, w ∈ adj v ↔ v ∈ adj w) →
        (∀ v ∈ H, ¬ bad ((H.filter (fun w => w ∈ adj v)).card)) ∧
        (∀ t : ℝ, (∀ d, bad d → (d : ℝ) ≤ t) →
          2 * t * n < ∑ v, ((adj v).length : ℝ) → H.Nonempty))) := by
  unfold peel
  try dsimp only
  refine WP_forIn_bind (fun pre (deg : Fin n → ℕ) k => k ≤ pre.length * (1 + n) ∧
      (∀ v ∈ pre, deg v = (adj v).length) ∧ ∀ v, v ∉ pre → deg v = 0)
    (by simp) ?_ ?_
  · -- loop A: degrees
    intro pre v suf deg k hpre hI
    obtain ⟨hk, hin, hout⟩ := hI
    have hv : v ∉ pre := not_mem_pre (List.nodup_finRange n) hpre
    try dsimp only
    refine WP_tick_bind ?_
    refine WP_forIn_bind (fun p (d : Fin n → ℕ) k' => k' ≤ p.length ∧ d v = p.length ∧
        ∀ u, u ≠ v → d u = deg u) (by simp [hout v hv]) ?_ ?_
    · intro p w s d k' _ hJ
      obtain ⟨hk', hdv, hdu⟩ := hJ
      try dsimp only
      refine WP_tick_bind (WP_pure ⟨_, rfl, ?_, ?_, ?_⟩)
      · simp only [List.length_append, List.length_singleton]; omega
      · simp [hdv]
      · intro u hu; simp [Function.update_apply, hu, hdu u hu]
    · intro d k' hJ
      obtain ⟨hk', hdv, hdu⟩ := hJ
      refine WP_pure ⟨_, rfl, ?_, ?_, ?_⟩
      · have := hlen v
        simp only [List.length_append, List.length_singleton]
        nlinarith
      · intro u hu
        rcases List.mem_append.mp hu with hu | hu
        · have huv : u ≠ v := fun h => hv (h ▸ hu)
          rw [hdu u huv]; exact hin u hu
        · rw [List.mem_singleton.mp hu]; exact hdv
      · intro u hu
        have huv : u ≠ v := fun h => hu (by simp [h])
        have hup : u ∉ pre := fun h => hu (by simp [h])
        rw [hdu u huv]; exact hout u hup
  · intro deg kA hIA
    obtain ⟨hkA, hinA, -⟩ := hIA
    have hdeg : ∀ v, deg v = (adj v).length := fun v => hinA v (List.mem_finRange v)
    simp only [List.length_finRange] at hkA
    try dsimp only
    refine WP_forIn_bind (fun pre (st : (Fin n → Bool) × List (Fin n)) k => match st with
      | (qd, qu) =>
        k ≤ pre.length * 2 ∧
        (∀ x, qd x = true ↔ (x ∈ pre ∧ bad (deg x))) ∧
        (∀ x, x ∈ qu ↔ (x ∈ pre ∧ bad (deg x))) ∧ qu.Nodup)
      (by simp) ?_ ?_
    · -- loop B: initial queue
      rintro pre v suf ⟨queued, queue⟩ k hpre ⟨hk, hq, hQ, hQnd⟩
      have hv : v ∉ pre := not_mem_pre (List.nodup_finRange n) hpre
      try dsimp only at hk hq hQ hQnd ⊢
      refine WP_tick_bind (prim_bind (badAt_wp _ _) ?_)
      try dsimp only
      refine WP_ite (fun hb => WP_pure ⟨_, rfl, ?_, ?_, ?_, ?_⟩)
        (fun hb => WP_pure ⟨_, rfl, ?_, ?_, ?_, ?_⟩)
      · simp only [List.length_append, List.length_singleton]; omega
      · have hb' : bad (deg v) := of_decide_eq_true hb
        intro x
        by_cases hxv : x = v
        · subst hxv; simp [hb']
        · simp [Function.update_apply, hxv, hq x]
      · have hb' : bad (deg v) := of_decide_eq_true hb
        intro x
        by_cases hxv : x = v
        · subst hxv; simp [hb']
        · simp [hxv, hQ x]
      · exact List.nodup_cons.mpr ⟨fun h => hv ((hQ v).mp h).1, hQnd⟩
      · simp only [List.length_append, List.length_singleton]; omega
      · have hb' : ¬ bad (deg v) := fun h => hb (decide_eq_true h)
        intro x
        by_cases hxv : x = v
        · subst hxv; simp [hb', hq x, hv]
        · simp [hxv, hq x]
      · have hb' : ¬ bad (deg v) := fun h => hb (decide_eq_true h)
        intro x
        by_cases hxv : x = v
        · subst hxv; simp [hb', hQ x, hv]
        · simp [hxv, hQ x]
      · exact hQnd
    · rintro ⟨queued, queue⟩ kB ⟨hkB, hq, hQ, hQnd⟩
      simp only [List.length_finRange] at hkB
      try dsimp only at hq hQ hQnd ⊢
      refine WP_forIn_bind (fun pre (st : (Fin n → ℕ) × (Fin n → Bool) × List (Fin n) × (Fin n → Bool)) k =>
          match st with
        | (deg, queued, queue, removed) =>
          k ≤ pre.length * (1 + 2 * n) ∧
          (∀ x, removed x = false → deg x = (adj x).length - decN adj removed x) ∧
          (∀ x, x ∈ queue ↔ (queued x = true ∧ removed x = false)) ∧
          queue.Nodup ∧
          (∀ x, queued x = false → removed x = false ∧ ¬ bad (deg x)) ∧
          (∀ x, queued x = true → removed x = false → ∃ d0, bad d0 ∧ deg x ≤ d0) ∧
          (queue = [] ∨ pre.length ≤ ncard removed) ∧
          ((∀ v w, w ∈ adj v ↔ v ∈ adj w) → ∀ t : ℝ, (∀ d, bad d → (d : ℝ) ≤ t) →
            (∑ x, ((adj x).length : ℝ)) ≤ (asum adj removed : ℝ) + 2 * t * (ncard removed : ℝ)))
        ?_ ?_ ?_
      · -- init of loop C
        refine ⟨by simp, ?_, ?_, hQnd, ?_, ?_, Or.inr (by simp), ?_⟩
        · intro x _
          simp [decN, hdeg x]
        · intro x
          rw [hQ x, hq x]
          simp
        · intro x hx
          refine ⟨rfl, fun hb => ?_⟩
          have := (hq x).mpr ⟨List.mem_finRange x, hb⟩
          rw [hx] at this; exact absurd this (by simp)
        · intro x hx _
          exact ⟨deg x, ((hq x).mp hx).2, le_refl _⟩
        · intro _ t _
          simp [asum, decN, ncard]
      · -- loop C: rounds
        rintro pre r suf ⟨deg, queued, queue, removed⟩ k hpre hI
        obtain ⟨hk, C1, C2, C3, C4, C5, C6, C7⟩ := hI
        try dsimp only at hk C1 C2 C3 C4 C5 C6 C7 ⊢
        refine WP_tick_bind ?_
        rcases queue with _ | ⟨v, rest⟩
        · dsimp only
          refine WP_pure ⟨_, rfl, ?_, C1, C2, C3, C4, C5, Or.inl rfl, C7⟩
          simp only [List.length_append, List.length_singleton]
          nlinarith
        · dsimp only
          obtain ⟨hqv, hrv⟩ := (C2 v).mp List.mem_cons_self
          have hvrest : v ∉ rest := (List.nodup_cons.mp C3).1
          have hrem : ∀ x, Function.update removed v true x = false ↔ (x ≠ v ∧ removed x = false) := by
            intro x
            by_cases hxv : x = v
            · subst hxv; simp
            · simp [Function.update_apply, hxv]
          refine WP_forIn_bind (fun p (st : (Fin n → ℕ) × (Fin n → Bool) × List (Fin n)) k' =>
              match st with
            | (dg, qd, qu) =>
              k' ≤ p.length * 2 ∧
              (∀ x, Function.update removed v true x = false →
                dg x = (adj x).length - decN adj removed x - (if x ∈ p then 1 else 0)) ∧
              (∀ x, x ∈ qu ↔ (qd x = true ∧ Function.update removed v true x = false)) ∧
              qu.Nodup ∧
              (∀ x, qd x = false → Function.update removed v true x = false ∧ ¬ bad (dg x)) ∧
              (∀ x, qd x = true → Function.update removed v true x = false →
                ∃ d0, bad d0 ∧ dg x ≤ d0))
            ?_ ?_ ?_
          · -- init of the inner loop
            refine ⟨by simp, ?_, ?_, (List.nodup_cons.mp C3).2, ?_, ?_⟩
            · intro x hx
              obtain ⟨_, hx2⟩ := (hrem x).mp hx
              simp [C1 x hx2]
            · intro x
              rw [hrem x]
              constructor
              · intro hx
                have hxv : x ≠ v := fun h => hvrest (h ▸ hx)
                obtain ⟨h1, h2⟩ := (C2 x).mp (List.mem_cons_of_mem _ hx)
                exact ⟨h1, hxv, h2⟩
              · rintro ⟨h1, hxv, h2⟩
                have := (C2 x).mpr ⟨h1, h2⟩
                rcases List.mem_cons.mp this with h | h
                · exact absurd h hxv
                · exact h
            · intro x hx
              have hxv : x ≠ v := by rintro rfl; rw [hqv] at hx; exact absurd hx (by simp)
              obtain ⟨h1, h2⟩ := C4 x hx
              exact ⟨(hrem x).mpr ⟨hxv, h1⟩, h2⟩
            · intro x hx hx'
              exact C5 x hx ((hrem x).mp hx').2
          · -- step of the inner loop
            rintro p w s ⟨dg, qd, qu⟩ k' hp hK
            obtain ⟨hk', K1, K2, K3, K4, K5⟩ := hK
            try dsimp only at hk' K1 K2 K3 K4 K5 ⊢
            have hwp : w ∉ p := not_mem_pre (hnd v) hp
            refine WP_tick_bind ?_
            refine WP_ite (fun hc => ?_) (fun hc => ?_)
            · have hw : Function.update removed v true w = false := by simpa using hc
              have K1w := K1 w hw
              rw [if_neg hwp, Nat.sub_zero] at K1w
              have K1' : ∀ x, Function.update removed v true x = false →
                  Function.update dg w (dg w - 1) x =
                    (adj x).length - decN adj removed x - (if x ∈ p ++ [w] then 1 else 0) := by
                intro x hx
                by_cases hxw : x = w
                · subst hxw; simp [K1w]
                · simp [Function.update_apply, hxw, K1 x hx]
              try dsimp only
              refine WP_ite (fun hq => ?_) (fun hq => ?_)
              · have hq' : qd w = false := by simpa using hq
                refine prim_bind (badAt_wp _ _) ?_
                try dsimp only
                refine WP_ite (fun hb => WP_pure ⟨_, rfl, ?_, K1', ?_, ?_, ?_, ?_⟩)
                  (fun hb => WP_pure ⟨_, rfl, ?_, K1', K2, K3, ?_, ?_⟩)
                · simp only [List.length_append, List.length_singleton]; omega
                · intro x
                  by_cases hxw : x = w
                  · subst hxw; simp [hw]
                  · simp [Function.update_apply, hxw, K2 x]
                · refine List.nodup_cons.mpr ⟨fun h => ?_, K3⟩
                  have := ((K2 w).mp h).1
                  rw [hq'] at this; exact absurd this (by simp)
                · intro x hx
                  have hxw : x ≠ w := by rintro rfl; simp at hx
                  simp only [Function.update_of_ne hxw] at hx ⊢
                  exact K4 x hx
                · intro x hx hrx
                  by_cases hxw : x = w
                  · subst hxw
                    have hb' : bad (dg x - 1) := by simpa using hb
                    exact ⟨_, hb', by simp⟩
                  · simp only [Function.update_of_ne hxw] at hx ⊢
                    exact K5 x hx hrx
                · simp only [List.length_append, List.length_singleton]; omega
                · intro x hx
                  by_cases hxw : x = w
                  · subst hxw
                    have hb' : ¬ bad (dg x - 1) := by simpa using hb
                    exact ⟨hw, by simpa using hb'⟩
                  · simp only [Function.update_of_ne hxw]
                    exact K4 x hx
                · intro x hx hrx
                  have hxw : x ≠ w := by rintro rfl; dsimp only at hx; rw [hq'] at hx; exact absurd hx (by simp)
                  simp only [Function.update_of_ne hxw]
                  exact K5 x hx hrx
              · have hq' : qd w = true := by simpa using hq
                refine WP_pure ⟨_, rfl, ?_, K1', K2, K3, ?_, ?_⟩
                · simp only [List.length_append, List.length_singleton]; omega
                · intro x hx
                  have hxw : x ≠ w := by rintro rfl; dsimp only at hx; rw [hq'] at hx; exact absurd hx (by simp)
                  simp only [Function.update_of_ne hxw]
                  exact K4 x hx
                · intro x hx hrx
                  by_cases hxw : x = w
                  · subst hxw
                    obtain ⟨d0, hd0, hle⟩ := K5 x hx hrx
                    exact ⟨d0, hd0, by simp; omega⟩
                  · simp only [Function.update_of_ne hxw]
                    exact K5 x hx hrx
            · have hw : Function.update removed v true w = true := by simpa using hc
              refine WP_pure ⟨_, rfl, ?_, ?_, K2, K3, K4, K5⟩
              · simp only [List.length_append, List.length_singleton]; omega
              · intro x hx
                have hxw : x ≠ w := by rintro rfl; rw [hw] at hx; exact absurd hx (by simp)
                dsimp only
                rw [K1 x hx]
                simp [hxw]
          · -- after the inner loop
            rintro ⟨dg, qd, qu⟩ k' hK
            obtain ⟨hk', K1, K2, K3, K4, K5⟩ := hK
            try dsimp only at hk' K1 K2 K3 K4 K5 ⊢
            refine WP_pure ⟨_, rfl, ?_, ?_, K2, K3, K4, K5, ?_, ?_⟩
            · have := hlen v
              simp only [List.length_append, List.length_singleton]
              nlinarith
            · intro x hx
              dsimp only
              rw [decN_update adj removed v x hrv, K1 x hx, Nat.sub_sub]
            · right
              rw [ncard_update removed v hrv]
              simp only [List.length_append, List.length_singleton]
              rcases C6 with h | h
              · exact absurd h (List.cons_ne_nil _ _)
              · omega
            · intro hsym t ht
              have h1 := C7 hsym t ht
              have h2 := asum_update adj hnd hsym removed v hrv
              have h3 := C1 v hrv
              obtain ⟨d0, hd0, hle⟩ := C5 v hqv hrv
              have h4 := ht d0 hd0
              rw [ncard_update removed v hrv]
              set m := (adj v).length - decN adj removed v with hm
              have h5 : m ≤ d0 := h3 ▸ hle
              have h6 : (m : ℝ) ≤ t := le_trans (by exact_mod_cast h5) h4
              have h7 : (asum adj removed : ℝ) ≤ asum adj (Function.update removed v true) + 2 * (m : ℝ) := by
                exact_mod_cast h2
              push_cast
              linarith
      · -- after loop C
        rintro ⟨deg', queued', queue', removed'⟩ kC hI
        obtain ⟨hkC, C1, C2, C3, C4, C5, C6, C7⟩ := hI
        try dsimp only at hkC C1 C2 C3 C4 C5 C6 C7 ⊢
        simp only [List.length_range] at hkC C6
        refine WP_pure ⟨?_, fun hsym => ⟨?_, ?_⟩⟩
        · nlinarith
        · have hqe : queue' = [] := by
            rcases C6 with h | h
            · exact h
            · have := ncard_le removed'; omega
          intro v hv
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
          have hqv : queued' v = false := by
            cases h : queued' v
            · rfl
            · exfalso
              have := (C2 v).mpr ⟨h, hv⟩
              rw [hqe] at this; exact absurd this (by simp)
          have hnb := (C4 v hqv).2
          rw [C1 v hv, cnt_eq adj hnd hsym removed' v] at hnb
          have e : (Finset.filter (fun w => w ∈ adj v)
              (Finset.filter (fun v => removed' v = false) Finset.univ)).card = cntN adj removed' v := by
            unfold cntN
            rw [Finset.filter_filter]
            congr 1
            ext y
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact and_comm
          rw [e]; exact hnb
        · intro t ht hsum
          by_contra hne
          rw [Finset.not_nonempty_iff_eq_empty] at hne
          have hall : ∀ x, removed' x = true := by
            intro x
            by_contra h
            have hx : x ∈ Finset.filter (fun v => removed' v = false) Finset.univ := by
              simpa using h
            rw [hne] at hx; simp at hx
          have ha : asum adj removed' = 0 := by
            unfold asum; simp [hall]
          have hn : ncard removed' = n := by
            unfold ncard; simp [hall]
          have := C7 hsym t ht
          rw [ha, hn] at this
          push_cast at this
          linarith

end Peel

end LNC

namespace LNC

open LNTopology.Hermetization

section Find
variable {n : ℕ}

abbrev PRow (lam : Fin n → Fin n → ℝ) (v : Fin n) (p : List (Fin n)) (d : ℕ) (s l : ℝ)
    (a : List (Fin n)) : Prop :=
  a.Nodup ∧ (∀ j, j ∈ a ↔ (j ∈ p ∧ lam v j ≠ 0)) ∧ a.length = d ∧
  (∀ j ∈ p, |lam v j| ≤ l) ∧ 0 ≤ l ∧ (l = 0 ∨ ∃ j, l = |lam v j|) ∧
  (d ≠ 0 → (∃ j, lam v j ≠ 0 ∧ s = |lam v j|) ∧ ∀ j ∈ p, lam v j ≠ 0 → s ≤ |lam v j|)

theorem L_up {lam : Fin n → Fin n → ℝ} {v j : Fin n} {p : List (Fin n)} {d : ℕ} {s l : ℝ}
    {a : List (Fin n)} (hrow : PRow lam v p d s l a) (hb : l < |lam v j|) :
    (∀ i ∈ p ++ [j], |lam v i| ≤ |lam v j|) ∧ 0 ≤ |lam v j| ∧
      (|lam v j| = 0 ∨ ∃ i, |lam v j| = |lam v i|) := by
  refine ⟨fun i hi => ?_, abs_nonneg _, Or.inr ⟨j, rfl⟩⟩
  rcases List.mem_append.mp hi with hi | hi
  · exact (hrow.2.2.2.1 i hi).trans hb.le
  · rw [List.mem_singleton.mp hi]

theorem L_keep {lam : Fin n → Fin n → ℝ} {v j : Fin n} {p : List (Fin n)} {d : ℕ} {s l : ℝ}
    {a : List (Fin n)} (hrow : PRow lam v p d s l a) (hb : ¬ l < |lam v j|) :
    (∀ i ∈ p ++ [j], |lam v i| ≤ l) ∧ 0 ≤ l ∧ (l = 0 ∨ ∃ i, l = |lam v i|) := by
  refine ⟨fun i hi => ?_, hrow.2.2.2.2.1, hrow.2.2.2.2.2.1⟩
  rcases List.mem_append.mp hi with hi | hi
  · exact hrow.2.2.2.1 i hi
  · rw [List.mem_singleton.mp hi]; exact not_lt.mp hb

theorem S_first {lam : Fin n → Fin n → ℝ} {v j : Fin n} {p : List (Fin n)} {d : ℕ} {s l : ℝ}
    {a : List (Fin n)} (hrow : PRow lam v p d s l a) (hd : d = 0) (hz : lam v j ≠ 0) :
    (∃ i, lam v i ≠ 0 ∧ |lam v j| = |lam v i|) ∧
      ∀ i ∈ p ++ [j], lam v i ≠ 0 → |lam v j| ≤ |lam v i| := by
  refine ⟨⟨j, hz, rfl⟩, fun i hi hi0 => ?_⟩
  rcases List.mem_append.mp hi with hi | hi
  · exfalso
    have ha : a = [] := List.eq_nil_of_length_eq_zero (hrow.2.2.1.trans hd)
    have := (hrow.2.1 i).mpr ⟨hi, hi0⟩
    rw [ha] at this; simp at this
  · rw [List.mem_singleton.mp hi]

theorem S_smaller {lam : Fin n → Fin n → ℝ} {v j : Fin n} {p : List (Fin n)} {d : ℕ} {s l : ℝ}
    {a : List (Fin n)} (hrow : PRow lam v p d s l a) (hd : d ≠ 0) (hs : |lam v j| < s)
    (hz : lam v j ≠ 0) :
    (∃ i, lam v i ≠ 0 ∧ |lam v j| = |lam v i|) ∧
      ∀ i ∈ p ++ [j], lam v i ≠ 0 → |lam v j| ≤ |lam v i| := by
  refine ⟨⟨j, hz, rfl⟩, fun i hi hi0 => ?_⟩
  rcases List.mem_append.mp hi with hi | hi
  · exact hs.le.trans ((hrow.2.2.2.2.2.2 hd).2 i hi hi0)
  · rw [List.mem_singleton.mp hi]

theorem S_keep {lam : Fin n → Fin n → ℝ} {v j : Fin n} {p : List (Fin n)} {d : ℕ} {s l : ℝ}
    {a : List (Fin n)} (hrow : PRow lam v p d s l a) (hd : d ≠ 0) (hs : ¬ |lam v j| < s) :
    (∃ i, lam v i ≠ 0 ∧ s = |lam v i|) ∧ ∀ i ∈ p ++ [j], lam v i ≠ 0 → s ≤ |lam v i| := by
  refine ⟨(hrow.2.2.2.2.2.2 hd).1, fun i hi hi0 => ?_⟩
  rcases List.mem_append.mp hi with hi | hi
  · exact (hrow.2.2.2.2.2.2 hd).2 i hi hi0
  · rw [List.mem_singleton.mp hi]; exact not_lt.mp hs

theorem prow_step_nz {lam : Fin n → Fin n → ℝ} {v j : Fin n} {p : List (Fin n)} {d : ℕ}
    {s l : ℝ} {a : List (Fin n)} (hrow : PRow lam v p d s l a) (hjp : j ∉ p)
    (hz : lam v j ≠ 0) {S L : ℝ}
    (hL : (∀ i ∈ p ++ [j], |lam v i| ≤ L) ∧ 0 ≤ L ∧ (L = 0 ∨ ∃ i, L = |lam v i|))
    (hS : (∃ i, lam v i ≠ 0 ∧ S = |lam v i|) ∧ ∀ i ∈ p ++ [j], lam v i ≠ 0 → S ≤ |lam v i|) :
    PRow lam v (p ++ [j]) (d + 1) S L (j :: a) := by
  obtain ⟨hnd, hmem, hlen, -, -, -, -⟩ := hrow
  refine ⟨List.nodup_cons.mpr ⟨fun h => hjp ((hmem j).mp h).1, hnd⟩, ?_, by simp [hlen],
    hL.1, hL.2.1, hL.2.2, fun _ => hS⟩
  intro i
  rw [List.mem_cons, hmem i, List.mem_append, List.mem_singleton]
  constructor
  · rintro (rfl | ⟨h1, h2⟩)
    · exact ⟨Or.inr rfl, hz⟩
    · exact ⟨Or.inl h1, h2⟩
  · rintro ⟨h1 | rfl, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact Or.inl rfl

theorem prow_step_z {lam : Fin n → Fin n → ℝ} {v j : Fin n} {p : List (Fin n)} {d : ℕ}
    {s l : ℝ} {a : List (Fin n)} (hrow : PRow lam v p d s l a)
    (hz : lam v j = 0) {L : ℝ}
    (hL : (∀ i ∈ p ++ [j], |lam v i| ≤ L) ∧ 0 ≤ L ∧ (L = 0 ∨ ∃ i, L = |lam v i|)) :
    PRow lam v (p ++ [j]) d s L a := by
  obtain ⟨hnd, hmem, hlen, -, -, -, hS⟩ := hrow
  refine ⟨hnd, ?_, hlen, hL.1, hL.2.1, hL.2.2, fun hd => ⟨(hS hd).1, fun i hi hi0 => ?_⟩⟩
  · intro i
    rw [hmem i, List.mem_append, List.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨Or.inl h1, h2⟩
    · rintro ⟨h1 | rfl, h2⟩
      · exact ⟨h1, h2⟩
      · exact absurd hz h2
  · rcases List.mem_append.mp hi with hi | hi
    · exact (hS hd).2 i hi hi0
    · rw [List.mem_singleton.mp hi] at hi0; exact absurd hz hi0

/-! ## Cost facts -/

theorem c_abs {c g : ℝ → ℝ} (hc : CostAxioms c g) (x : ℝ) : c |x| = c x := by
  rcases abs_choice x with h | h <;> rw [h]
  exact hc.symm x

theorem c_mono_le {c g : ℝ → ℝ} (hc : CostAxioms c g) {x y : ℝ} (hy : 0 ≤ y) (hxy : y ≤ x) :
    c y ≤ c x := by
  rcases eq_or_lt_of_le hxy with h | h
  · rw [h]
  · exact (hc.mono x y hy h).le

theorem c_pos {c g : ℝ → ℝ} (hc : CostAxioms c g) {x : ℝ} (hx : 0 < x) : 0 < c x := by
  have := hc.mono x 0 le_rfl hx
  rwa [hc.zero] at this

theorem c_nonneg {c g : ℝ → ℝ} (hc : CostAxioms c g) (x : ℝ) : 0 ≤ c x := by
  have h := c_mono_le hc (le_refl (0 : ℝ)) (abs_nonneg x)
  rw [hc.zero, c_abs hc] at h
  exact h

theorem cost_herm {c g : ℝ → ℝ} (hc : CostAxioms c g) (Λ : Fin n → Fin n → ℝ) (U : Finset (Fin n)) :
    cost c (hermetize Λ U) = cost c Λ + ∑ i ∈ U, c (∑ j ∈ U, Λ i j)
      - (1 / 2) * ∑ i ∈ U, ∑ j ∈ U, c (Λ i j) := by
  have h1 : ∀ j, c (if j ∈ U then -∑ i ∈ U, Λ j i else 0)
      = if j ∈ U then c (∑ i ∈ U, Λ j i) else 0 := by
    intro j; split_ifs <;> simp [hc.symm, hc.zero]
  have h2 : ∀ i, c (if i ∈ U then ∑ j ∈ U, Λ i j else 0)
      = if i ∈ U then c (∑ j ∈ U, Λ i j) else 0 := by
    intro i; split_ifs <;> simp [hc.zero]
  have h3 : ∀ i j, c (if i ∈ U ∧ j ∈ U then 0 else Λ i j)
      = c (Λ i j) - if i ∈ U ∧ j ∈ U then c (Λ i j) else 0 := by
    intro i j; split_ifs <;> simp [hc.zero]
  have h4 : ∑ i, ∑ j, (if i ∈ U ∧ j ∈ U then c (Λ i j) else 0)
      = ∑ i ∈ U, ∑ j ∈ U, c (Λ i j) := by
    calc ∑ i, ∑ j, (if i ∈ U ∧ j ∈ U then c (Λ i j) else 0)
        = ∑ i, if i ∈ U then ∑ j ∈ U, c (Λ i j) else 0 := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          by_cases hi : i ∈ U
          · simp [hi, Finset.sum_ite_mem]
          · simp [hi]
      _ = ∑ i ∈ U, ∑ j ∈ U, c (Λ i j) := by
          rw [Finset.sum_ite_mem, Finset.univ_inter]
  have E : ∑ a : Option (Fin n), ∑ b : Option (Fin n), c (hermetize Λ U a b)
      = 2 * ∑ i ∈ U, c (∑ j ∈ U, Λ i j) + ∑ i, ∑ j, c (Λ i j)
        - ∑ i ∈ U, ∑ j ∈ U, c (Λ i j) := by
    simp only [Fintype.sum_option, hermetize, hc.zero, h1, h2, h3, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, h4, Finset.sum_ite_mem, Finset.univ_inter]
    ring
  unfold cost
  rw [E]
  ring

theorem node_bound' {c g : ℝ → ℝ} (hc : CostAxioms c g) (lam : Fin n → Fin n → ℝ)
    (U : Finset (Fin n)) (i : Fin n) (L s D : ℝ)
    (hL : ∀ j, |lam i j| ≤ L) (hs0 : 0 < s) (hs : ∀ j, lam i j ≠ 0 → s ≤ |lam i j|)
    (hLD : c L ≤ D * c s) (hd : 1 ≤ degIn lam U i) (hgd : 2 * D < g (degIn lam U i)) :
    c (∑ j ∈ U, lam i j) < (1 / 2) * ∑ j ∈ U, c (lam i j) := by
  set F := U.filter (fun j => lam i j ≠ 0) with hFdef
  have hdF : degIn lam U i = F.card := rfl
  have hFne : F.Nonempty := by rw [← Finset.card_pos, ← hdF]; omega
  obtain ⟨j0, hj0F⟩ := hFne
  have hj0 : lam i j0 ≠ 0 := (Finset.mem_filter.mp hj0F).2
  have hLpos : 0 < L := lt_of_lt_of_le (abs_pos.mpr hj0) (hL j0)
  set d : ℝ := (degIn lam U i : ℝ) with hddef
  have hd1 : (1 : ℝ) ≤ d := by rw [hddef]; exact_mod_cast hd
  have hcs : 0 < c s := c_pos hc hs0
  have hcL : 0 ≤ c L := c_nonneg hc L
  have hD0 : 0 ≤ D := by
    by_contra h
    push_neg at h
    nlinarith
  have hgpos : 0 < g d := by linarith
  have hT : |∑ j ∈ U, lam i j| ≤ d * L := by
    calc |∑ j ∈ U, lam i j| ≤ ∑ j ∈ U, |lam i j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j ∈ F, |lam i j| := by
          rw [hFdef]
          exact (Finset.sum_filter_of_ne (fun x _ hx => abs_ne_zero.mp hx)).symm
      _ ≤ F.card • L := Finset.sum_le_card_nsmul _ _ _ (fun k _ => hL k)
      _ = d * L := by rw [nsmul_eq_mul, hddef, hdF]
  have hsum : d * c s ≤ ∑ j ∈ U, c (lam i j) := by
    calc d * c s = F.card • c s := by rw [nsmul_eq_mul, hddef, hdF]
      _ ≤ ∑ j ∈ F, c (lam i j) := by
          apply Finset.card_nsmul_le_sum
          intro k hk
          rw [← c_abs hc (lam i k)]
          exact c_mono_le hc hs0.le (hs k (Finset.mem_filter.mp hk).2)
      _ ≤ ∑ j ∈ U, c (lam i j) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro k _ _
          exact c_nonneg hc _
  have h1 : c (∑ j ∈ U, lam i j) ≤ c (d * L) := by
    rw [← c_abs hc]
    exact c_mono_le hc (abs_nonneg _) hT
  have h2 : c (d * L) < d / g d * c L := hc.subadd_plus (degIn lam U i) hd L hLpos
  have h4 : d / g d * c L ≤ d / g d * (D * c s) :=
    mul_le_mul_of_nonneg_left hLD (div_nonneg (by linarith) hgpos.le)
  have h5 : d / g d * (D * c s) ≤ d / 2 * c s := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hgpos]
    have : 0 ≤ d * c s * (g d - 2 * D) :=
      mul_nonneg (mul_nonneg (by linarith) hcs.le) (by linarith)
    nlinarith
  have : d / 2 * c s = (1 / 2) * (d * c s) := by ring
  linarith

theorem final_math (lam : Fin n → Fin n → ℝ) (c g : ℝ → ℝ) (dg : Fin n → ℕ)
    (sm lg : Fin n → ℝ) (adj : Fin n → List (Fin n)) (D : ℝ) (fails : ℕ → Bool)
    (H : Finset (Fin n))
    (hrow : ∀ v, PRow lam v (List.finRange n).reverse (dg v) (sm v) (lg v) (adj v))
    (hD1 : D = 0 ∨ ∃ u, dg u ≠ 0 ∧ D = c (lg u) / c (sm u))
    (hD2 : ∀ u, dg u ≠ 0 → c (lg u) / c (sm u) ≤ D)
    (hf : ∀ d, d ≤ n → fails d = decide (g d ≤ 2 * D))
    (hpeel : (∀ v w, w ∈ adj v ↔ v ∈ adj w) →
        (∀ v ∈ H, ¬ (((H.filter (fun w => w ∈ adj v)).card = 0) ∨
            ((H.filter (fun w => w ∈ adj v)).card ≤ n ∧
              fails (H.filter (fun w => w ∈ adj v)).card = true))) ∧
        (∀ t : ℝ, (∀ d : ℕ, (d = 0 ∨ d ≤ n ∧ fails d = true) → (d : ℝ) ≤ t) →
          2 * t * n < ∑ v, ((adj v).length : ℝ) → H.Nonempty))
    (hLN : IsLN lam) (hc : CostAxioms c g)
    (ht : ∃ t : ℝ, 0 ≤ t ∧ 2 * disc c lam ≤ g t ∧ 2 * t < avgDeg lam) :
    Hermetizable c lam H := by
  obtain ⟨t, ht0, htd, htavg⟩ := ht
  have hmem : ∀ v j, j ∈ adj v ↔ lam v j ≠ 0 := fun v j => by
    rw [(hrow v).2.1 j]; simp
  have hsym : ∀ v w, w ∈ adj v ↔ v ∈ adj w := by
    intro v w; rw [hmem, hmem, hLN v w, neg_ne_zero]
  have hdeg : ∀ v, dg v = degIn lam Finset.univ v := by
    intro v
    rw [← (hrow v).2.2.1, ← List.toFinset_card_of_nodup (hrow v).1]
    unfold degIn
    congr 1
    ext j
    simp [hmem]
  have hcnt : ∀ v, (H.filter (fun w => w ∈ adj v)).card = degIn lam H v := by
    intro v; unfold degIn; congr 1; ext j; simp [hmem]
  have hratio : ∀ u, dg u ≠ 0 → c (lg u) / c (sm u) ≤ disc c lam := by
    intro u hu
    obtain ⟨_, _, _, hL1, _, hL2, hS⟩ := hrow u
    obtain ⟨⟨j0, hj0, hsm⟩, _⟩ := hS hu
    have hL1' : ∀ j, |lam u j| ≤ lg u := fun j => hL1 j (by simp)
    have hlgpos : 0 < lg u := lt_of_lt_of_le (abs_pos.mpr hj0) (hL1' j0)
    obtain ⟨j1, hj1⟩ : ∃ j1, lg u = |lam u j1| := by
      rcases hL2 with h | h
      · exact absurd h hlgpos.ne'
      · exact h
    have hSIn : |lam u j1| ≤ SIn lam Finset.univ u := by
      unfold SIn
      exact le_ciSup (f := fun w : {w : Fin n // w ∈ Finset.univ} => |lam u w|)
        (Finite.bddAbove_range _) ⟨j1, Finset.mem_univ _⟩
    have hsIn : sIn lam Finset.univ u ≤ |lam u j0| := by
      unfold sIn
      exact ciInf_le (f := fun w : {w : Fin n // w ∈ Finset.univ ∧ lam u w ≠ 0} => |lam u w|)
        (Finite.bddBelow_range _) ⟨j0, Finset.mem_univ _, hj0⟩
    have hsInpos : 0 < sIn lam Finset.univ u := by
      haveI : Nonempty {w : Fin n // w ∈ Finset.univ ∧ lam u w ≠ 0} :=
        ⟨⟨j0, Finset.mem_univ _, hj0⟩⟩
      obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite
        (f := fun w : {w : Fin n // w ∈ Finset.univ ∧ lam u w ≠ 0} => |lam u w|)
      unfold sIn
      rw [← hi]
      exact abs_pos.mpr i.2.2
    have hc1 : c (lg u) ≤ c (SIn lam Finset.univ u) :=
      c_mono_le hc hlgpos.le (by rw [hj1]; exact hSIn)
    have hc2 : c (sIn lam Finset.univ u) ≤ c (sm u) :=
      c_mono_le hc hsInpos.le (by rw [hsm]; exact hsIn)
    have hc3 : 0 < c (sIn lam Finset.univ u) := c_pos hc hsInpos
    have hc4 : 0 < c (sm u) := lt_of_lt_of_le hc3 hc2
    have hc5 : 0 ≤ c (SIn lam Finset.univ u) := c_nonneg hc _
    have step1 : c (lg u) / c (sm u) ≤ c (SIn lam Finset.univ u) / c (sIn lam Finset.univ u) := by
      rw [div_le_div_iff₀ hc4 hc3]
      exact mul_le_mul hc1 hc2 hc3.le hc5
    refine step1.trans ?_
    have hdu : degIn lam Finset.univ u ≠ 0 := by rw [← hdeg]; exact hu
    unfold disc discIn
    exact le_ciSup (f := fun v : {v : Fin n // v ∈ Finset.univ ∧ degIn lam Finset.univ v ≠ 0} =>
      c (SIn lam Finset.univ v) / c (sIn lam Finset.univ v))
      (Finite.bddAbove_range _) ⟨u, Finset.mem_univ _, hdu⟩
  have hdisc0 : 0 ≤ disc c lam := by
    unfold disc discIn
    exact Real.iSup_nonneg (fun _ => div_nonneg (c_nonneg hc _) (c_nonneg hc _))
  have hDdisc : D ≤ disc c lam := by
    rcases hD1 with h | ⟨u, hu, h⟩
    · rw [h]; exact hdisc0
    · rw [h]; exact hratio u hu
  have hbad : ∀ d : ℕ, (d = 0 ∨ d ≤ n ∧ fails d = true) → (d : ℝ) ≤ t := by
    rintro d (rfl | ⟨hdn, hfd⟩)
    · simpa using ht0
    · rw [hf d hdn] at hfd
      have hgd : g d ≤ 2 * D := of_decide_eq_true hfd
      by_contra hlt
      push_neg at hlt
      have := hc.g_strictMonoOn (Set.mem_Ici.mpr ht0) (Set.mem_Ici.mpr (Nat.cast_nonneg d)) hlt
      linarith
  have hsumlen : 2 * t * n < ∑ v, ((adj v).length : ℝ) := by
    have e : ∑ v, ((adj v).length : ℝ) = ∑ v, (deg lam v : ℝ) := by
      refine Finset.sum_congr rfl (fun v _ => ?_)
      rw [(hrow v).2.2.1, hdeg v]
      rfl
    rw [e]
    have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · exfalso
        subst h
        unfold avgDeg at htavg
        simp at htavg
        linarith
      · exact h
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    unfold avgDeg at htavg
    rw [Fintype.card_fin, lt_div_iff₀ hnR] at htavg
    linarith
  obtain ⟨hHbad, hHne⟩ := hpeel hsym
  have hne := hHne t hbad hsumlen
  unfold Hermetizable
  rw [cost_herm hc]
  have hlt : ∑ i ∈ H, c (∑ j ∈ H, lam i j) < ∑ i ∈ H, (1 / 2) * ∑ j ∈ H, c (lam i j) := by
    apply Finset.sum_lt_sum_of_nonempty hne
    intro i hi
    have hb := hHbad i hi
    rw [hcnt i] at hb
    have hdn : degIn lam H i ≤ n := by
      unfold degIn
      exact (Finset.card_le_univ _).trans (by simp)
    have hd1 : 1 ≤ degIn lam H i := by
      by_contra h
      push_neg at h
      exact hb (Or.inl (by omega))
    have hgd : 2 * D < g (degIn lam H i) := by
      by_contra h
      push_neg at h
      exact hb (Or.inr ⟨hdn, by rw [hf _ hdn]; exact decide_eq_true h⟩)
    have hdgi : dg i ≠ 0 := by
      rw [hdeg i]
      intro h0
      have : degIn lam H i ≤ degIn lam Finset.univ i := by
        unfold degIn
        exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))
      omega
    obtain ⟨_, _, _, hL1, _, _, hS⟩ := hrow i
    obtain ⟨⟨j0, hj0, hsm⟩, hS2⟩ := hS hdgi
    have hs0 : 0 < sm i := by rw [hsm]; exact abs_pos.mpr hj0
    have hcs : 0 < c (sm i) := c_pos hc hs0
    have hLD : c (lg i) ≤ D * c (sm i) := by
      have := hD2 i hdgi
      rwa [div_le_iff₀ hcs] at this
    exact node_bound' hc lam H i (lg i) (sm i) D (fun j => hL1 j (by simp)) hs0
      (fun j hj => hS2 j (by simp) hj) hLD hd1 hgd
  rw [← Finset.mul_sum] at hlt
  linarith

end Find

end LNC

namespace LNC

open LNTopology.Hermetization

theorem find_spec {n : ℕ} (lam : Fin n → Fin n → ℝ) (c g : ℝ → ℝ) :
    WP (findHermetizable lam c g) (fun H k => k ≤ 20 * (n + 1) ^ 2 ∧
      (IsLN lam → CostAxioms c g →
        (∃ t : ℝ, 0 ≤ t ∧ 2 * disc c lam ≤ g t ∧ 2 * t < avgDeg lam) →
        Hermetizable c lam H)) := by
  unfold findHermetizable
  try dsimp only
  refine WP_forIn_bind (fun pre (st : (Fin n → ℕ) × (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → List (Fin n))) k =>
      match st with
      | (dg, sm, lg, adj) =>
        k ≤ pre.length * (1 + 6 * n) ∧
        (∀ v ∈ pre, PRow lam v (List.finRange n).reverse (dg v) (sm v) (lg v) (adj v)) ∧
        (∀ v, v ∉ pre → dg v = 0 ∧ adj v = [] ∧ lg v = 0))
    (by simp) ?_ ?_
  · -- loop 1, one row
    rintro pre v suf ⟨dg, sm, lg, adj⟩ k hpre hI
    obtain ⟨hk, hin, hout⟩ := hI
    have hv : v ∉ pre := not_mem_pre (List.nodup_finRange n) hpre
    obtain ⟨hd0, ha0, hl0⟩ := hout v hv
    try dsimp only
    refine WP_tick_bind ?_
    refine WP_forIn_bind (fun p (st : (Fin n → ℕ) × (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → List (Fin n))) k' =>
        match st with
        | (dg', sm', lg', adj') =>
          k' ≤ p.length * 6 ∧
          (∀ u, u ≠ v → dg' u = dg u ∧ sm' u = sm u ∧ lg' u = lg u ∧ adj' u = adj u) ∧
          PRow lam v p (dg' v) (sm' v) (lg' v) (adj' v))
      ⟨by simp, fun _ _ => ⟨rfl, rfl, rfl, rfl⟩, ?_⟩ ?_ ?_
    · refine ⟨by rw [ha0]; exact List.nodup_nil, ?_, by rw [ha0, hd0]; rfl, by simp,
        le_of_eq hl0.symm, Or.inl hl0, fun h => absurd hd0 h⟩
      intro j; rw [ha0]; simp
    · rintro p j s ⟨dg', sm', lg', adj'⟩ k' hp hJ
      obtain ⟨hk', hoff, hrow⟩ := hJ
      have hjp : j ∉ p := not_mem_pre (List.nodup_reverse.mpr (List.nodup_finRange n)) hp
      try dsimp only
      refine WP_tick_bind (prim_bind (lamAt_wp _ _ _) (prim_bind (rabs_wp _)
        (prim_bind (rlt_wp _ _) ?_)))
      try dsimp only
      refine WP_ite (fun hb => ?_) (fun hb => ?_)
      · have hL := L_up hrow (of_decide_eq_true hb)
        refine prim_bind (req_wp _ _) ?_
        try dsimp only
        refine WP_ite (fun hz => ?_) (fun hz => ?_)
        · have hz' : lam v j ≠ 0 := by simpa using hz
          refine WP_ite (fun hd => ?_) (fun hd => ?_)
          · exact WP_pure ⟨_, rfl, by simp only [List.length_append, List.length_singleton]; omega,
              fun u hu => by simpa only [Function.update_of_ne hu] using hoff u hu,
              by simpa only [Function.update_self] using
                prow_step_nz hrow hjp hz' hL (S_first hrow hd hz')⟩
          · refine prim_bind (rlt_wp _ _) ?_
            try dsimp only
            refine WP_ite (fun hs => ?_) (fun hs => ?_)
            · exact WP_pure ⟨_, rfl, by simp only [List.length_append, List.length_singleton]; omega,
                fun u hu => by simpa only [Function.update_of_ne hu] using hoff u hu,
                by simpa only [Function.update_self] using
                  prow_step_nz hrow hjp hz' hL (S_smaller hrow hd (of_decide_eq_true hs) hz')⟩
            · exact WP_pure ⟨_, rfl, by simp only [List.length_append, List.length_singleton]; omega,
                fun u hu => by simpa only [Function.update_of_ne hu] using hoff u hu,
                by simpa only [Function.update_self] using
                  prow_step_nz hrow hjp hz' hL (S_keep hrow hd (fun h => hs (decide_eq_true h)))⟩
        · have hz' : lam v j = 0 := by simpa using hz
          exact WP_pure ⟨_, rfl, by simp only [List.length_append, List.length_singleton]; omega,
            fun u hu => by simpa only [Function.update_of_ne hu] using hoff u hu,
            by simpa only [Function.update_self] using prow_step_z hrow hz' hL⟩
      · have hL := L_keep hrow (fun h => hb (decide_eq_true h))
        refine prim_bind (req_wp _ _) ?_
        try dsimp only
        refine WP_ite (fun hz => ?_) (fun hz => ?_)
        · have hz' : lam v j ≠ 0 := by simpa using hz
          refine WP_ite (fun hd => ?_) (fun hd => ?_)
          · exact WP_pure ⟨_, rfl, by simp only [List.length_append, List.length_singleton]; omega,
              fun u hu => by simpa only [Function.update_of_ne hu] using hoff u hu,
              by simpa only [Function.update_self] using
                prow_step_nz hrow hjp hz' hL (S_first hrow hd hz')⟩
          · refine prim_bind (rlt_wp _ _) ?_
            try dsimp only
            refine WP_ite (fun hs => ?_) (fun hs => ?_)
            · exact WP_pure ⟨_, rfl, by simp only [List.length_append, List.length_singleton]; omega,
                fun u hu => by simpa only [Function.update_of_ne hu] using hoff u hu,
                by simpa only [Function.update_self] using
                  prow_step_nz hrow hjp hz' hL (S_smaller hrow hd (of_decide_eq_true hs) hz')⟩
            · exact WP_pure ⟨_, rfl, by simp only [List.length_append, List.length_singleton]; omega,
                fun u hu => by simpa only [Function.update_of_ne hu] using hoff u hu,
                by simpa only [Function.update_self] using
                  prow_step_nz hrow hjp hz' hL (S_keep hrow hd (fun h => hs (decide_eq_true h)))⟩
        · have hz' : lam v j = 0 := by simpa using hz
          exact WP_pure ⟨_, rfl, by simp only [List.length_append, List.length_singleton]; omega,
            hoff, prow_step_z hrow hz' hL⟩
    · rintro ⟨dg', sm', lg', adj'⟩ k' hJ
      obtain ⟨hk', hoff, hrow⟩ := hJ
      simp only [List.length_reverse, List.length_finRange] at hk'
      try dsimp only
      refine WP_pure ⟨_, rfl, ?_, ?_, ?_⟩
      · simp only [List.length_append, List.length_singleton]
        nlinarith
      · intro u hu
        rcases List.mem_append.mp hu with hu | hu
        · have huv : u ≠ v := fun h => hv (h ▸ hu)
          obtain ⟨e1, e2, e3, e4⟩ := hoff u huv
          dsimp only
          rw [e1, e2, e3, e4]; exact hin u hu
        · rw [List.mem_singleton.mp hu]; exact hrow
      · intro u hu
        have huv : u ≠ v := fun h => hu (by simp [h])
        have hup : u ∉ pre := fun h => hu (by simp [h])
        obtain ⟨e1, -, e3, e4⟩ := hoff u huv
        dsimp only
        rw [e1, e3, e4]; exact hout u hup
  · rintro ⟨dg, sm, lg, adj⟩ k1 hI1
    obtain ⟨hk1, hrow, -⟩ := hI1
    simp only [List.length_finRange] at hk1
    have hrow' : ∀ v, PRow lam v (List.finRange n).reverse (dg v) (sm v) (lg v) (adj v) :=
      fun v => hrow v (List.mem_finRange v)
    try dsimp only
    refine WP_forIn_bind (fun pre (st : ℝ × Bool) k => match st with
        | (D, found) =>
          k ≤ pre.length * 5 ∧ (found = false → D = 0 ∧ ∀ u ∈ pre, dg u = 0) ∧
          (found = true → ∃ u, dg u ≠ 0 ∧ D = c (lg u) / c (sm u)) ∧
          ∀ u ∈ pre, dg u ≠ 0 → c (lg u) / c (sm u) ≤ D)
      (by simp) ?_ ?_
    · -- loop 2: the discrepancy
      rintro pre v suf ⟨D, found⟩ k _ hI
      obtain ⟨hk, hF, hT, hle⟩ := hI
      try dsimp only
      refine WP_tick_bind ?_
      refine WP_ite (fun hdv => ?_) (fun hdv => ?_)
      · refine prim_bind (cAt_wp _ _) (prim_bind (cAt_wp _ _) (prim_bind (rdiv_wp _ _) ?_))
        try dsimp only
        refine WP_ite (fun hf => ?_) (fun hf => ?_)
        · refine prim_bind (rlt_wp _ _) ?_
          try dsimp only
          refine WP_ite (fun hu => WP_pure ⟨_, rfl, ?_, ?_, ?_, ?_⟩)
            (fun hu => WP_pure ⟨_, rfl, ?_, ?_, ?_, ?_⟩)
          · simp only [List.length_append, List.length_singleton]; omega
          · intro h; rw [hf] at h; exact absurd h (by simp)
          · intro _; exact ⟨v, hdv, rfl⟩
          · have hu' : D < c (lg v) / c (sm v) := of_decide_eq_true hu
            intro u hu2 hdu
            rcases List.mem_append.mp hu2 with hu2 | hu2
            · exact (hle u hu2 hdu).trans hu'.le
            · rw [List.mem_singleton.mp hu2]
          · simp only [List.length_append, List.length_singleton]; omega
          · intro h; rw [hf] at h; exact absurd h (by simp)
          · exact hT
          · have hu' : ¬ D < c (lg v) / c (sm v) := fun h => hu (decide_eq_true h)
            intro u hu2 hdu
            rcases List.mem_append.mp hu2 with hu2 | hu2
            · exact hle u hu2 hdu
            · rw [List.mem_singleton.mp hu2]; exact not_lt.mp hu'
        · have hf' : found = false := by simpa using hf
          refine WP_pure ⟨_, rfl, ?_, ?_, ?_, ?_⟩
          · simp only [List.length_append, List.length_singleton]; omega
          · intro h; exact absurd h (by simp)
          · intro _; exact ⟨v, hdv, rfl⟩
          · intro u hu2 hdu
            rcases List.mem_append.mp hu2 with hu2 | hu2
            · exact absurd ((hF hf').2 u hu2) hdu
            · rw [List.mem_singleton.mp hu2]
      · have hdv' : dg v = 0 := not_not.mp hdv
        refine WP_pure ⟨_, rfl, ?_, ?_, hT, ?_⟩
        · simp only [List.length_append, List.length_singleton]; omega
        · intro h
          refine ⟨(hF h).1, fun u hu2 => ?_⟩
          rcases List.mem_append.mp hu2 with hu2 | hu2
          · exact (hF h).2 u hu2
          · rw [List.mem_singleton.mp hu2]; exact hdv'
        · intro u hu2 hdu
          rcases List.mem_append.mp hu2 with hu2 | hu2
          · exact hle u hu2 hdu
          · rw [List.mem_singleton.mp hu2] at hdu; exact absurd hdv' hdu
    · rintro ⟨D, found⟩ k2 hI2
      obtain ⟨hk2, hF, hT, hle⟩ := hI2
      simp only [List.length_finRange] at hk2
      have hD1 : D = 0 ∨ ∃ u, dg u ≠ 0 ∧ D = c (lg u) / c (sm u) := by
        cases found
        · exact Or.inl (hF rfl).1
        · exact Or.inr (hT rfl)
      have hD2 : ∀ u, dg u ≠ 0 → c (lg u) / c (sm u) ≤ D := fun u => hle u (List.mem_finRange u)
      try dsimp only
      refine prim_bind (rmul_wp _ _) ?_
      try dsimp only
      refine WP_forIn_bind (fun pre (fails : ℕ → Bool) k => k ≤ pre.length * 3 ∧
          ∀ d ∈ pre, fails d = decide (g d ≤ 2 * D)) (by simp) ?_ ?_
      · -- loop 3: the degree table
        intro pre d suf fails k _ hI
        obtain ⟨hk, hf⟩ := hI
        try dsimp only
        refine WP_tick_bind (prim_bind (gAt_wp _ _) (prim_bind (rle_wp _ _)
          (WP_pure ⟨_, rfl, ?_, ?_⟩)))
        · simp only [List.length_append, List.length_singleton]; omega
        · intro d' hd'
          by_cases hdd : d' = d
          · subst hdd; simp
          · rw [Function.update_of_ne hdd]
            refine hf d' ?_
            rcases List.mem_append.mp hd' with h | h
            · exact h
            · exact absurd (List.mem_singleton.mp h) hdd
      · intro fails k3 hI3
        obtain ⟨hk3, hf⟩ := hI3
        simp only [List.length_range] at hk3
        have hf' : ∀ d, d ≤ n → fails d = decide (g d ≤ 2 * D) :=
          fun d hd => hf d (List.mem_range.mpr (by omega))
        have hnd : ∀ v, (adj v).Nodup := fun v => (hrow' v).1
        have hlen : ∀ v, (adj v).length ≤ n := fun v => by
          have := (hnd v).length_le_card
          simpa using this
        try dsimp only
        refine WP_mono (peel_spec adj _ hlen hnd) ?_
        rintro H k4 ⟨hk4, hpeel⟩
        refine ⟨by nlinarith, fun hLN hCA ht => ?_⟩
        exact final_math lam c g dg sm lg adj D fails H hrow' hD1 hD2 hf' hpeel hLN hCA ht

end LNC

open LNTopology.Hermetization in
theorem solution :
    ∃ C k : ℕ, ∀ (n : ℕ) (lam : Fin n → Fin n → ℝ) (c g : ℝ → ℝ),
      ((findHermetizable lam c g).run 0).2 ≤ C * (n + 1) ^ k ∧
      (IsLN lam → CostAxioms c g →
        (∃ t : ℝ, 0 ≤ t ∧ 2 * disc c lam ≤ g t ∧ 2 * t < avgDeg lam) →
        LNHermetizable c lam ∧
          Hermetizable c lam ((findHermetizable lam c g).run 0).1) := by
  refine ⟨20, 2, fun n lam c g => ?_⟩
  obtain ⟨k, hk, hb, hP⟩ := LNC.find_spec lam c g 0
  refine ⟨?_, fun h1 h2 h3 => ⟨⟨_, hP h1 h2 h3⟩, hP h1 h2 h3⟩⟩
  rw [hk]
  omega
