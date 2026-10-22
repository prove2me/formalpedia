-- Prove2me | solution 1 for IwataFF.SFM.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:27:41.648643+00:00
-- url     : https://prove2.me/submissions/58096196-1b0c-49a2-9cb7-5875448d601e

import Mathlib
import Definitions.Def_IwataFF_SFM_Basic
import Definitions.Def_IwataFF_SFM_Phase
open IwataFF.SFM

theorem g69g_take_succ_toFinset {α : Type} [DecidableEq α] (L : List α) (k : ℕ)
    (hk : k < L.length) : (L.take (k + 1)).toFinset = insert L[k] (L.take k).toFinset := by
  rw [List.take_succ_eq_append_getElem hk, List.toFinset_append]
  ext b; simp [or_comm]

theorem g69g_greedy_prefix_sum {α : Type} [DecidableEq α] (V : Finset α)
    (f : Finset α → ℝ) (L : List α) (hL : IsOrdering V L) :
    ∀ k, k ≤ L.length → ∑ v ∈ (L.take k).toFinset, greedy f L v =
      f (L.take k).toFinset - f ∅ := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have hkl : k < L.length := by omega
    have haL : L[k] ∈ L := List.getElem_mem hkl
    have hidx : L.idxOf L[k] = k := hL.1.idxOf_getElem k hkl
    have hnot : L[k] ∉ (L.take k).toFinset := by
      rw [List.mem_toFinset, List.mem_take_iff_idxOf_lt haL, hidx]; omega
    have hg : greedy f L L[k] = f (insert L[k] (L.take k).toFinset) - f (L.take k).toFinset := by
      unfold greedy; rw [if_pos haL, hidx, g69g_take_succ_toFinset L k hkl]
    rw [g69g_take_succ_toFinset L k hkl, Finset.sum_insert hnot, ih (by omega), hg]
    ring

theorem g69g_xsum_conv {α : Type} [DecidableEq α] (f : Finset α → ℝ) (W : Finset α) (c : ℝ) :
    ∀ l : List (List α × ℝ), (∀ p ∈ l, ∑ a ∈ W, greedy f p.1 a = c) →
      ∑ a ∈ W, (l.map (fun p => p.2 * greedy f p.1 a)).sum = (l.map Prod.snd).sum * c := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons p l ih =>
    intro h
    simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [h p (List.mem_cons_self), ih (fun q hq => h q (List.mem_cons_of_mem _ hq))]
    ring

theorem g69g_full_sum {α : Type} [DecidableEq α] (V : Finset α)
    (f : Finset α → ℝ) (hf0 : f ∅ = 0) (L : List α) (hL : IsOrdering V L) :
    ∑ v ∈ V, greedy f L v = f V := by
  have := g69g_greedy_prefix_sum V f L hL L.length le_rfl
  rw [List.take_length, hf0, sub_zero] at this
  have e : L.toFinset = V := by ext b; rw [List.mem_toFinset]; exact hL.2 b
  rwa [e] at this

theorem g69g_xOf_V {α : Type} [DecidableEq α] (V : Finset α)
    (f : Finset α → ℝ) (hf0 : f ∅ = 0) (st : PhaseState α) (hinv : PhaseInv V st) :
    xsum (xOf f st) V = f V := by
  unfold xsum xOf
  rw [g69g_xsum_conv f V (f V) st.idx (fun p hp => g69g_full_sum V f hf0 p.1 (hinv.2.2.1 p hp).1),
    hinv.2.2.2.1, one_mul]

theorem g69g_skew_sum_zero {α : Type} (X : Finset α) (phi : α → α → ℝ)
    (hskew : ∀ u ∈ X, ∀ v ∈ X, phi u v + phi v u = 0) :
    ∑ v ∈ X, ∑ u ∈ X, phi u v = 0 := by
  have h1 : ∑ v ∈ X, ∑ u ∈ X, phi u v = ∑ v ∈ X, ∑ u ∈ X, phi v u := Finset.sum_comm
  have h2 : ∑ v ∈ X, ∑ u ∈ X, phi u v + ∑ v ∈ X, ∑ u ∈ X, phi v u = 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero; intro v hv
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero; intro u hu
    exact hskew u hu v hv
  linarith

theorem g69g_bdry_bound {α : Type} [DecidableEq α] (V : Finset α) (st : PhaseState α)
    (hinv : PhaseInv V st) (v : α) (hv : v ∈ V) :
    -(((V.card : ℝ) - 1) * st.delta) ≤ bdry V st v ∧ bdry V st v ≤ ((V.card : ℝ) - 1) * st.delta := by
  have hvv : st.phi v v = 0 := by have := hinv.2.2.2.2.1 v hv v hv; linarith
  have hsplit : bdry V st v = ∑ u ∈ V.erase v, st.phi u v := by
    unfold bdry; rw [← Finset.add_sum_erase _ _ hv, hvv, zero_add]
  have hc : ((V.erase v).card : ℝ) = (V.card : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem hv, Nat.cast_sub (Finset.card_pos.mpr ⟨v, hv⟩)]; simp
  rw [hsplit]
  constructor
  · have : ∑ u ∈ V.erase v, (-st.delta) ≤ ∑ u ∈ V.erase v, st.phi u v :=
      Finset.sum_le_sum (fun u hu => (hinv.2.2.2.2.2 u (Finset.mem_of_mem_erase hu) v hv).1)
    rw [Finset.sum_const, nsmul_eq_mul, hc] at this; linarith
  · have : ∑ u ∈ V.erase v, st.phi u v ≤ ∑ u ∈ V.erase v, st.delta :=
      Finset.sum_le_sum (fun u hu => (hinv.2.2.2.2.2 u (Finset.mem_of_mem_erase hu) v hv).2)
    rw [Finset.sum_const, nsmul_eq_mul, hc] at this; linarith

theorem g69g_bound_general {α : Type} [DecidableEq α] (V : Finset α) (f : Finset α → ℝ)
    (st : PhaseState α) (hinv : PhaseInv V st) (W : Finset α) (hW : W ⊆ V)
    (h1 : ∀ v ∈ W, zOf f V st v < st.delta)
    (h2 : ∀ v ∈ V, v ∉ W → -st.delta < zOf f V st v)
    (h3 : ∀ u ∈ V, u ∉ W → ∀ v ∈ W, st.phi u v ≤ 0) :
    xsum (xOf f st) W - (V.card : ℝ) ^ 2 * st.delta ≤ xsum (xneg (xOf f st)) V ∧
      xsum (xOf f st) W - (V.card : ℝ) * st.delta ≤ xsum (xneg (zOf f V st)) V := by
  have hδ := hinv.1
  set n : ℝ := (V.card : ℝ) with hn
  have hcard : (W.card : ℝ) + ((V \ W).card : ℝ) = n := by
    rw [hn, ← Nat.cast_add, add_comm, Finset.card_sdiff_add_card_eq_card hW]
  have hn1 : (1 : ℝ) ≤ n ∨ V = ∅ := by
    rcases V.eq_empty_or_nonempty with h | h
    · right; exact h
    · left; rw [hn]; exact_mod_cast Finset.card_pos.mpr h
  have hxz : ∀ v, xOf f st v = zOf f V st v + bdry V st v := by
    intro v; unfold zOf; ring
  unfold xsum xneg
  rw [← Finset.sum_sdiff hW, ← Finset.sum_sdiff hW (f := fun a => min 0 (zOf f V st a))]
  constructor
  · have a1 : ∀ v ∈ W, xOf f st v - n * st.delta ≤ min 0 (xOf f st v) := by
      intro v hv
      have := (g69g_bdry_bound V st hinv v (hW hv)).2
      have := h1 v hv
      have := hxz v
      rcases le_total (xOf f st v) 0 with h | h
      · rw [min_eq_right h]; nlinarith
      · rw [min_eq_left h]; linarith
    have a2 : ∀ v ∈ V \ W, -(n * st.delta) ≤ min 0 (xOf f st v) := by
      intro v hv
      rw [Finset.mem_sdiff] at hv
      have := (g69g_bdry_bound V st hinv v hv.1).1
      have := h2 v hv.1 hv.2
      have := hxz v
      have hnn : 0 ≤ n * st.delta := by positivity
      apply le_min (by linarith) (by linarith)
    have s1 := Finset.sum_le_sum a1
    have s2 := Finset.sum_le_sum a2
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at s1
    rw [Finset.sum_const, nsmul_eq_mul] at s2
    have : (W.card : ℝ) * (n * st.delta) + ((V \ W).card : ℝ) * (n * st.delta) = n ^ 2 * st.delta := by
      rw [← add_mul, hcard]; ring
    linarith
  · have a1 : ∀ v ∈ W, zOf f V st v - st.delta ≤ min 0 (zOf f V st v) := by
      intro v hv
      have := h1 v hv
      rcases le_total (zOf f V st v) 0 with h | h
      · rw [min_eq_right h]; linarith
      · rw [min_eq_left h]; linarith
    have a2 : ∀ v ∈ V \ W, -st.delta ≤ min 0 (zOf f V st v) := by
      intro v hv
      rw [Finset.mem_sdiff] at hv
      have := h2 v hv.1 hv.2
      apply le_min (by linarith) (by linarith)
    have s1 := Finset.sum_le_sum a1
    have s2 := Finset.sum_le_sum a2
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at s1
    rw [Finset.sum_const, nsmul_eq_mul] at s2
    have hzW : ∑ v ∈ W, xOf f st v ≤ ∑ v ∈ W, zOf f V st v := by
      have e : ∑ v ∈ W, zOf f V st v = ∑ v ∈ W, xOf f st v - ∑ v ∈ W, bdry V st v := by
        unfold zOf; rw [Finset.sum_sub_distrib]
      have hb : ∑ v ∈ W, bdry V st v ≤ 0 := by
        unfold bdry
        have s4 : ∑ v ∈ W, ∑ u ∈ V, st.phi u v =
            ∑ v ∈ W, ∑ u ∈ W, st.phi u v + ∑ v ∈ W, ∑ u ∈ V \ W, st.phi u v := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro v _
          rw [add_comm, Finset.sum_sdiff hW]
        rw [s4, g69g_skew_sum_zero W st.phi
          (fun u hu v hv => hinv.2.2.2.2.1 u (hW hu) v (hW hv)), zero_add]
        apply Finset.sum_nonpos; intro v hv; apply Finset.sum_nonpos; intro u hu
        rw [Finset.mem_sdiff] at hu
        exact h3 u hu.1 hu.2 v hv
      linarith
    have : (W.card : ℝ) * st.delta + ((V \ W).card : ℝ) * st.delta = n * st.delta := by
      rw [← add_mul, hcard]
    linarith

theorem g69g_notS {α : Type} [DecidableEq α] (V : Finset α) (f : Finset α → ℝ)
    (st : PhaseState α) (v : α) (hv : v ∈ V) (h : v ∉ Sset f V st) :
    -st.delta < zOf f V st v := by
  unfold Sset at h; rw [Finset.mem_filter] at h
  unfold zOf; push Not at h; have := h hv; linarith

theorem g69g_notT {α : Type} [DecidableEq α] (V : Finset α) (f : Finset α → ℝ)
    (st : PhaseState α) (v : α) (hv : v ∈ V) (h : v ∉ Tset f V st) :
    zOf f V st v < st.delta := by
  unfold Tset at h; rw [Finset.mem_filter] at h
  unfold zOf; push Not at h; have := h hv; linarith

theorem g69g_S_sub_W {α : Type} [DecidableEq α] (V : Finset α) (f : Finset α → ℝ)
    (st : PhaseState α) : Sset f V st ⊆ Wset f V st := by
  classical
  intro s hs
  unfold Wset; rw [Finset.mem_filter]
  refine ⟨?_, s, hs, Relation.ReflTransGen.refl⟩
  unfold Sset at hs; exact (Finset.mem_filter.mp hs).1

theorem g69g_W_sub_V {α : Type} [DecidableEq α] (V : Finset α) (f : Finset α → ℝ)
    (st : PhaseState α) : Wset f V st ⊆ V := by
  classical
  unfold Wset; exact Finset.filter_subset _ _

theorem g69g_W_closed {α : Type} [DecidableEq α] (V : Finset α) (f : Finset α → ℝ)
    (st : PhaseState α) (hinv : PhaseInv V st) :
    ∀ u ∈ V, u ∉ Wset f V st → ∀ v ∈ Wset f V st, st.phi u v ≤ 0 := by
  classical
  intro u hu huW v hvW
  by_contra hpos
  push Not at hpos
  have hvV := g69g_W_sub_V V f st hvW
  have hsk := hinv.2.2.2.2.1 u hu v hvV
  apply huW
  have hv' := hvW
  unfold Wset at hv' ⊢; rw [Finset.mem_filter] at hv' ⊢
  obtain ⟨-, s, hs, hr⟩ := hv'
  refine ⟨hu, s, hs, hr.tail ⟨hvV, hu, ?_, by linarith⟩⟩
  rintro rfl; exact huW hvW

theorem g69g_WT_empty {α : Type} [DecidableEq α] (V : Finset α) (f : Finset α → ℝ)
    (st : PhaseState α) (hend : PhaseEnd f V st) : Wset f V st ∩ Tset f V st = ∅ := by
  classical
  rcases hend with h | h | h
  · have : Wset f V st = ∅ := by
      unfold Wset; rw [h]
      apply Finset.filter_false_of_mem
      rintro v - ⟨s, hs, -⟩; simp at hs
    rw [this, Finset.empty_inter]
  · rw [h, Finset.inter_empty]
  · exact h.2

theorem g69g_lemma_3_3 {α : Type} [DecidableEq α] (V : Finset α)
    (f : Finset α → ℝ) (hf0 : f ∅ = 0)
    (st : PhaseState α) (hinv : PhaseInv V st) (hend : PhaseEnd f V st) :
    (Sset f V st = ∅ →
        f ∅ - (V.card : ℝ) ^ 2 * st.delta ≤ xsum (xneg (xOf f st)) V ∧
        f ∅ - (V.card : ℝ) * st.delta ≤ xsum (xneg (zOf f V st)) V) ∧
      (Tset f V st = ∅ →
        f V - (V.card : ℝ) ^ 2 * st.delta ≤ xsum (xneg (xOf f st)) V ∧
        f V - (V.card : ℝ) * st.delta ≤ xsum (xneg (zOf f V st)) V) ∧
      (xsum (xOf f st) (Wset f V st) = f (Wset f V st) →
        f (Wset f V st) - (V.card : ℝ) ^ 2 * st.delta ≤ xsum (xneg (xOf f st)) V ∧
        f (Wset f V st) - (V.card : ℝ) * st.delta ≤ xsum (xneg (zOf f V st)) V) := by
  refine ⟨fun hS => ?_, fun hT => ?_, fun hW => ?_⟩
  · have := g69g_bound_general V f st hinv ∅ (Finset.empty_subset _)
      (fun v hv => absurd hv (Finset.notMem_empty v))
      (fun v hv _ => g69g_notS V f st v hv (by rw [hS]; exact Finset.notMem_empty v))
      (fun u _ _ v hv => absurd hv (Finset.notMem_empty v))
    have e : xsum (xOf f st) ∅ = f ∅ := by rw [hf0]; simp [xsum]
    rwa [e] at this
  · have := g69g_bound_general V f st hinv V (subset_refl _)
      (fun v hv => g69g_notT V f st v hv (by rw [hT]; exact Finset.notMem_empty v))
      (fun v hv hv' => absurd hv hv')
      (fun u hu hu' _ _ => absurd hu hu')
    rwa [g69g_xOf_V V f hf0 st hinv] at this
  · have hWT := g69g_WT_empty V f st hend
    have := g69g_bound_general V f st hinv (Wset f V st) (g69g_W_sub_V V f st)
      (fun v hv => g69g_notT V f st v (g69g_W_sub_V V f st hv) (by
        intro hT
        have : v ∈ Wset f V st ∩ Tset f V st := Finset.mem_inter.mpr ⟨hv, hT⟩
        rw [hWT] at this; exact Finset.notMem_empty v this))
      (fun v hv hvW => g69g_notS V f st v hv (fun hS => hvW (g69g_S_sub_W V f st hS)))
      (g69g_W_closed V f st hinv)
    rwa [hW] at this

theorem g69g_prefix_of_closed {α : Type} [DecidableEq α] (V : Finset α) (L : List α)
    (hL : IsOrdering V L) (W : Finset α) (hW : W ⊆ V)
    (hcl : ∀ v ∈ V, v ∉ W → W ⊆ prefixSet L v) :
    ∃ k, k ≤ L.length ∧ (L.take k).toFinset = W := by
  classical
  by_cases hex : ∃ j, ∃ h : j < L.length, L[j] ∉ W
  · refine ⟨Nat.find hex, (Nat.find_spec hex).1.le, ?_⟩
    obtain ⟨hk, hvW⟩ := Nat.find_spec hex
    set k := Nat.find hex
    ext b
    rw [List.mem_toFinset]
    constructor
    · intro hb
      have hbL := List.mem_of_mem_take hb
      have hi := (List.mem_take_iff_idxOf_lt hbL).mp hb
      have hmin := Nat.find_min hex hi
      push Not at hmin
      have hl : L.idxOf b < L.length := List.idxOf_lt_length_iff.mpr hbL
      have := hmin hl
      rwa [List.getElem_idxOf] at this
    · intro hbW
      have hbL : b ∈ L := (hL.2 b).mpr (hW hbW)
      have hvL : L[k] ∈ L := List.getElem_mem hk
      have hvV : L[k] ∈ V := (hL.2 _).mp hvL
      have hsub := hcl _ hvV hvW hbW
      unfold prefixSet at hsub
      rw [List.mem_toFinset, List.mem_take_iff_idxOf_lt hbL, hL.1.idxOf_getElem k hk] at hsub
      rw [List.mem_take_iff_idxOf_lt hbL]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hsub with h | h
      · exact h
      · exfalso
        have : b = L[k] := by
          rw [← hL.1.idxOf_getElem k hk] at h
          exact (List.idxOf_inj hbL).mp h
        rw [this] at hbW; exact hvW hbW
  · push Not at hex
    refine ⟨L.length, le_rfl, ?_⟩
    rw [List.take_length]
    ext b; rw [List.mem_toFinset]
    constructor
    · intro hb
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
      exact hex j hj
    · intro hb; exact (hL.2 b).mpr (hW hb)

theorem g69g_closed_of_noZ {α : Type} [DecidableEq α] (V : Finset α) (f : Finset α → ℝ)
    (st : PhaseState α) (hZ : ¬ ZNonempty f V st) :
    ∀ p ∈ st.idx, ∀ v ∈ V, v ∉ Wset f V st → Wset f V st ⊆ prefixSet p.1 v := by
  classical
  intro p hp
  by_contra hcon
  push Not at hcon
  set W := Wset f V st
  set A := V.filter (fun v => v ∉ W ∧ (W \ prefixSet p.1 v).Nonempty)
  have hA : A.Nonempty := by
    obtain ⟨v, hv, hvW, hns⟩ := hcon
    refine ⟨v, Finset.mem_filter.mpr ⟨hv, hvW, ?_⟩⟩
    obtain ⟨w, hw, hw'⟩ := Finset.not_subset.mp hns
    exact ⟨w, Finset.mem_sdiff.mpr ⟨hw, hw'⟩⟩
  obtain ⟨v, hvA, hmax⟩ := Finset.exists_max_image A (fun v => p.1.idxOf v) hA
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hp
  rw [Finset.mem_filter] at hvA
  apply hZ
  refine ⟨i, v, p, hi, hvA.1, hvA.2.1, hvA.2.2, fun v' hv' hv'W hne => ?_⟩
  exact hmax v' (Finset.mem_filter.mpr ⟨hv', hv'W, hne⟩)

theorem g69g_lemma_3_1 {α : Type} [DecidableEq α] (V : Finset α)
    (f : Finset α → ℝ) (hf0 : f ∅ = 0)
    (st : PhaseState α) (hinv : PhaseInv V st) (hZ : ¬ ZNonempty f V st) :
    xsum (xOf f st) (Wset f V st) = f (Wset f V st) := by
  unfold xsum xOf
  rw [g69g_xsum_conv f (Wset f V st) (f (Wset f V st)) st.idx, hinv.2.2.2.1, one_mul]
  intro p hp
  have hL := (hinv.2.2.1 p hp).1
  obtain ⟨k, hk, hkW⟩ := g69g_prefix_of_closed V p.1 hL (Wset f V st) (g69g_W_sub_V V f st)
    (g69g_closed_of_noZ V f st hZ p hp)
  have := g69g_greedy_prefix_sum V f p.1 hL k hk
  rw [hkW, hf0, sub_zero] at this
  exact this

theorem g69g_greedy_le {α : Type} [DecidableEq α] (V : Finset α)
    (f : Finset α → ℝ) (hsub : SubmodularOn V f) (hf0 : f ∅ = 0)
    (L : List α) (hL : IsOrdering V L) (X : Finset α) (hX : X ⊆ V) :
    ∑ v ∈ X, greedy f L v ≤ f X := by
  have hsubV : ∀ k, (L.take k).toFinset ⊆ V := by
    intro k b hb
    rw [List.mem_toFinset] at hb
    exact (hL.2 b).mp (List.mem_of_mem_take hb)
  have key : ∀ k, k ≤ L.length →
      ∑ v ∈ X ∩ (L.take k).toFinset, greedy f L v ≤ f (X ∩ (L.take k).toFinset) - f ∅ := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hkl : k < L.length := by omega
      have ih' := ih (by omega)
      have haL : L[k] ∈ L := List.getElem_mem hkl
      have haV : L[k] ∈ V := (hL.2 _).mp haL
      have hidx : L.idxOf L[k] = k := hL.1.idxOf_getElem k hkl
      have hnot : L[k] ∉ (L.take k).toFinset := by
        rw [List.mem_toFinset, List.mem_take_iff_idxOf_lt haL, hidx]; omega
      have hg : greedy f L L[k] =
          f (insert L[k] (L.take k).toFinset) - f (L.take k).toFinset := by
        unfold greedy; rw [if_pos haL, hidx, g69g_take_succ_toFinset L k hkl]
      rw [g69g_take_succ_toFinset L k hkl]
      by_cases haX : L[k] ∈ X
      · rw [Finset.inter_insert_of_mem haX]
        have hn2 : L[k] ∉ X ∩ (L.take k).toFinset := fun h => hnot (Finset.mem_inter.mp h).2
        rw [Finset.sum_insert hn2, hg]
        have hA : insert L[k] (X ∩ (L.take k).toFinset) ⊆ V :=
          Finset.insert_subset haV (fun b hb => hX (Finset.mem_inter.mp hb).1)
        have := hsub _ hA _ (hsubV k)
        have e1 : insert L[k] (X ∩ (L.take k).toFinset) ∪ (L.take k).toFinset =
            insert L[k] (L.take k).toFinset := by
          ext b; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_inter]; tauto
        have e2 : insert L[k] (X ∩ (L.take k).toFinset) ∩ (L.take k).toFinset =
            X ∩ (L.take k).toFinset := by
          ext b; simp only [Finset.mem_insert, Finset.mem_inter]
          constructor
          · rintro ⟨rfl | h, h2⟩
            · exact absurd h2 hnot
            · exact h
          · rintro h; exact ⟨Or.inr h, h.2⟩
        rw [e1, e2] at this
        linarith
      · rw [Finset.inter_insert_of_notMem haX]; exact ih'
  have := key L.length le_rfl
  rw [List.take_length] at this
  have e : X ∩ L.toFinset = X := by
    ext b; rw [Finset.mem_inter, List.mem_toFinset, hL.2]; exact ⟨fun h => h.1, fun h => ⟨h, hX h⟩⟩
  rw [e, hf0, sub_zero] at this
  exact this

theorem g69g_xsum_conv_le {α : Type} [DecidableEq α] (f : Finset α → ℝ) (W : Finset α) (c : ℝ) :
    ∀ l : List (List α × ℝ), (∀ p ∈ l, 0 < p.2 ∧ ∑ a ∈ W, greedy f p.1 a ≤ c) →
      ∑ a ∈ W, (l.map (fun p => p.2 * greedy f p.1 a)).sum ≤ (l.map Prod.snd).sum * c := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons p l ih =>
    intro h
    simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ← Finset.mul_sum]
    have h1 := h p (List.mem_cons_self)
    have h2 := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    have : p.2 * ∑ a ∈ W, greedy f p.1 a ≤ p.2 * c := mul_le_mul_of_nonneg_left h1.2 h1.1.le
    nlinarith

theorem g69g_x_le {α : Type} [DecidableEq α] (V : Finset α)
    (f : Finset α → ℝ) (hsub : SubmodularOn V f) (hf0 : f ∅ = 0)
    (st : PhaseState α) (hinv : PhaseInv V st) (X : Finset α) (hX : X ⊆ V) :
    xsum (xOf f st) X ≤ f X := by
  unfold xsum xOf
  have := g69g_xsum_conv_le f X (f X) st.idx (fun p hp =>
    ⟨(hinv.2.2.1 p hp).2, g69g_greedy_le V f hsub hf0 p.1 (hinv.2.2.1 p hp).1 X hX⟩)
  rwa [hinv.2.2.2.1, one_mul] at this

theorem g69g_lemma_4_1 {α : Type} [DecidableEq α] (V : Finset α)
    (f : Finset α → ℝ) (hsub : SubmodularOn V f) (hf0 : f ∅ = 0)
    (st : PhaseState α) (hinv : PhaseInv V st) (hend : PhaseEnd f V st)
    (w : α) (hw : w ∈ V) (hxw : xOf f st w < -((V.card : ℝ) ^ 2) * st.delta) :
    ∀ X : Finset α, IsMinimizer V f X → w ∈ X := by
  have hY : ∃ Y ⊆ V, f Y - (V.card : ℝ) ^ 2 * st.delta ≤ xsum (xneg (xOf f st)) V := by
    have h33 := g69g_lemma_3_3 V f hf0 st hinv hend
    rcases hend with h | h | h
    · exact ⟨∅, Finset.empty_subset _, (h33.1 h).1⟩
    · exact ⟨V, subset_refl _, (h33.2.1 h).1⟩
    · exact ⟨Wset f V st, g69g_W_sub_V V f st,
        (h33.2.2 (g69g_lemma_3_1 V f hf0 st hinv h.1)).1⟩
  obtain ⟨Y, hYV, hYb⟩ := hY
  intro X hXmin
  by_contra hwX
  have hXV := hXmin.1
  have hfXY := hXmin.2 Y hYV
  have hxX := g69g_x_le V f hsub hf0 st hinv X hXV
  have hsplit : xsum (xneg (xOf f st)) V ≤ xsum (xOf f st) X + xOf f st w := by
    unfold xsum xneg
    rw [← Finset.sum_sdiff hXV]
    have hwV : w ∈ V \ X := Finset.mem_sdiff.mpr ⟨hw, hwX⟩
    rw [← Finset.add_sum_erase _ _ hwV]
    have a1 : ∑ v ∈ (V \ X).erase w, min 0 (xOf f st v) ≤ 0 :=
      Finset.sum_nonpos (fun i _ => min_le_left _ _)
    have a2 : ∑ v ∈ X, min 0 (xOf f st v) ≤ ∑ v ∈ X, xOf f st v :=
      Finset.sum_le_sum (fun i _ => min_le_right _ _)
    have a3 : min 0 (xOf f st w) ≤ xOf f st w := min_le_right _ _
    linarith
  linarith

theorem solution {α : Type} [DecidableEq α] (V : Finset α) (hV : V.Nonempty)
    (f : Finset α → ℝ) (hsub : SubmodularOn V f) (hf0 : f ∅ = 0)
    (st : PhaseState α) (hinv : PhaseInv V st) (hend : PhaseEnd f V st)
    (w : α) (hw : w ∈ V) (hxw : xOf f st w < -((V.card : ℝ) ^ 2) * st.delta) :
    ∀ X : Finset α, IsMinimizer V f X → w ∈ X :=
  g69g_lemma_4_1 V f hsub hf0 st hinv hend w hw hxw
