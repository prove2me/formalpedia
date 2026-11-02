-- Prove2me | solution 1 for IwataFF.SFM.theorem_4_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T15:09:07.762846+00:00
-- url     : https://prove2.me/submissions/a0218bd7-b66b-4811-bcc5-d6f0d3fec926

import Mathlib
import Definitions.Def_IwataFF_SFM_Basic
import Definitions.Def_IwataFF_SFM_Phase
import Definitions.Def_IwataFF_SFM_Main
import Theorems.Thm_IwataFF_SFM_lemma_2_1
import Theorems.Thm_IwataFF_SFM_lemma_4_1
import Theorems.Thm_IwataFF_SFM_eta_nonpos
import Theorems.Thm_IwataFF_SFM_lemma_3_1
import Theorems.Thm_IwataFF_SFM_lemma_3_2
import Theorems.Thm_IwataFF_SFM_lemma_3_3
import Theorems.Thm_IwataFF_SFM_consistent_base_bound
import Theorems.Thm_IwataFF_SFM_fix_calls_le

open IwataFF.SFM

namespace X5IW

theorem list_sum_set {β : Type*} (g : β → ℝ) :
    ∀ (l : List β) (i : ℕ) (p q : β), l[i]? = some p →
      ((l.set i q).map g).sum = (l.map g).sum - g p + g q
  | [], i, p, q, h => by simp at h
  | a :: l, 0, p, q, h => by
      simp at h; subst h; simp; ring
  | a :: l, i + 1, p, q, h => by
      simp only [List.getElem?_cons_succ] at h
      simp only [List.set_cons_succ, List.map_cons, List.sum_cons]
      rw [list_sum_set g l i p q h]; ring

theorem mem_of_getElem? {β : Type*} {l : List β} {i : ℕ} {p : β} (h : l[i]? = some p) :
    p ∈ l := by
  rcases List.getElem?_eq_some_iff.mp h with ⟨hi, rfl⟩
  exact List.getElem_mem hi

theorem ec_nonneg {α : Type} [DecidableEq α] (V : Finset α) (f : Finset α → ℝ)
    (y : α → ℝ) (hy : y ∈ basePoly V f) (u v : α) : 0 ≤ ec V f y u v := by
  unfold ec
  by_cases hb : BddAbove {t : ℝ | y + t • (chi u - chi v) ∈ basePoly V f}
  · apply le_csSup hb; simpa using hy
  · rw [Real.sSup_of_not_bddAbove hb]

theorem take_succ_toFinset {α : Type} [DecidableEq α] (L : List α) (k : ℕ)
    (hk : k < L.length) : (L.take (k + 1)).toFinset = insert L[k] (L.take k).toFinset := by
  rw [List.take_succ_eq_append_getElem hk, List.toFinset_append]
  ext b; simp [or_comm]

theorem greedy_prefix_sum {α : Type} [DecidableEq α] (V : Finset α)
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
      unfold greedy; rw [if_pos haL, hidx, take_succ_toFinset L k hkl]
    rw [take_succ_toFinset L k hkl, Finset.sum_insert hnot, ih (by omega), hg]
    ring

theorem greedy_le {α : Type} [DecidableEq α] (V : Finset α)
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
        unfold greedy; rw [if_pos haL, hidx, take_succ_toFinset L k hkl]
      rw [take_succ_toFinset L k hkl]
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

theorem greedy_base {α : Type} [DecidableEq α] (V : Finset α)
    (f : Finset α → ℝ) (hsub : SubmodularOn V f) (hf0 : f ∅ = 0)
    (L : List α) (hL : IsOrdering V L) : greedy f L ∈ basePoly V f := by
  refine ⟨fun a ha => ?_, ?_, fun X hX => greedy_le V f hsub hf0 L hL X hX⟩
  · unfold greedy; rw [if_neg (fun h => ha ((hL.2 a).mp h))]
  · have := greedy_prefix_sum V f L hL L.length le_rfl
    rw [List.take_length, hf0, sub_zero] at this
    have e : L.toFinset = V := by ext b; rw [List.mem_toFinset]; exact hL.2 b
    rw [e] at this; exact this

/-- a convex combination of greedy bases of orderings lies in `B(f)`. -/
theorem xOf_base {α : Type} [DecidableEq α] (V : Finset α)
    (f : Finset α → ℝ) (hsub : SubmodularOn V f) (hf0 : f ∅ = 0)
    (st : PhaseState α) (hord : ∀ p ∈ st.idx, IsOrdering V p.1 ∧ 0 < p.2)
    (hsum : (st.idx.map Prod.snd).sum = 1) : xOf f st ∈ basePoly V f := by
  -- general statement over lists
  have key : ∀ l : List (List α × ℝ), (∀ p ∈ l, IsOrdering V p.1 ∧ 0 < p.2) →
      (∀ a, a ∉ V → (l.map (fun p => p.2 * greedy f p.1 a)).sum = 0) ∧
      (∑ v ∈ V, (l.map (fun p => p.2 * greedy f p.1 v)).sum = (l.map Prod.snd).sum * f V) ∧
      (∀ X ⊆ V, ∑ v ∈ X, (l.map (fun p => p.2 * greedy f p.1 v)).sum ≤
          (l.map Prod.snd).sum * f X) := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons p l ih =>
      intro h
      obtain ⟨h1, h2, h3⟩ := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
      obtain ⟨hp1, hp2⟩ := h p List.mem_cons_self
      have hb := greedy_base V f hsub hf0 p.1 hp1
      refine ⟨fun a ha => ?_, ?_, fun X hX => ?_⟩
      · simp only [List.map_cons, List.sum_cons]; rw [h1 a ha, hb.1 a ha]; ring
      · simp only [List.map_cons, List.sum_cons]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, h2]
        have := hb.2.1; unfold xsum at this; rw [this]; ring
      · simp only [List.map_cons, List.sum_cons]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        have := hb.2.2 X hX; unfold xsum at this
        have := mul_le_mul_of_nonneg_left this hp2.le
        have := h3 X hX
        linarith
  obtain ⟨h1, h2, h3⟩ := key st.idx hord
  rw [hsum] at h2 h3
  refine ⟨h1, ?_, fun X hX => ?_⟩
  · unfold xsum xOf; simpa using h2
  · unfold xsum xOf; simpa using h3 X hX

theorem skew_sum_zero {α : Type} (X : Finset α) (phi : α → α → ℝ)
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

/-- clipping: `z⁻` drops by at most `C(n,2) δ`. -/
theorem clip_zneg {α : Type} [DecidableEq α] (V : Finset α) (x : α → ℝ) (phi : α → α → ℝ)
    (d : ℝ) (hd : 0 < d)
    (hskew : ∀ u ∈ V, ∀ v ∈ V, phi u v + phi v u = 0)
    (hfeas : ∀ u ∈ V, ∀ v ∈ V, -(2 * d) ≤ phi u v ∧ phi u v ≤ 2 * d) :
    xsum (xneg (fun v => x v - ∑ u ∈ V, phi u v)) V - ((V.card.choose 2 : ℕ) : ℝ) * d ≤
      xsum (xneg (fun v => x v - ∑ u ∈ V, clip phi d u v)) V := by
  set D : α → α → ℝ := fun u v => clip phi d u v - phi u v with hD
  have hDskew : ∀ u ∈ V, ∀ v ∈ V, D u v + D v u = 0 := by
    intro u hu v hv
    have := hskew u hu v hv
    have e : phi v u = - phi u v := by linarith
    simp only [hD, clip, e]
    rcases le_total d (phi u v) with h | h <;> rcases le_total (-d) (phi u v) with h' | h' <;>
    simp only [min_def, max_def] <;> split_ifs <;> linarith
  have hDabs : ∀ u ∈ V, ∀ v ∈ V, |D u v| ≤ if u = v then 0 else d := by
    intro u hu v hv
    split_ifs with huv
    · subst huv
      have := hskew u hu u hu
      have h0 : phi u u = 0 := by linarith
      simp [hD, clip, h0, hd.le]
    · have := hfeas u hu v hv
      simp only [hD, clip]
      rw [abs_le]
      simp only [min_def, max_def]; split_ifs <;> constructor <;> linarith
  -- pointwise
  have hpt : ∀ v ∈ V, min 0 (x v - ∑ u ∈ V, phi u v) - ∑ u ∈ V, max 0 (D u v) ≤
      min 0 (x v - ∑ u ∈ V, clip phi d u v) := by
    intro v hv
    have e : ∑ u ∈ V, clip phi d u v = ∑ u ∈ V, phi u v + ∑ u ∈ V, D u v := by
      rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro u _; simp [hD]
    have hle : ∑ u ∈ V, D u v ≤ ∑ u ∈ V, max 0 (D u v) :=
      Finset.sum_le_sum (fun u _ => le_max_right _ _)
    have hnn : 0 ≤ ∑ u ∈ V, max 0 (D u v) := Finset.sum_nonneg (fun u _ => le_max_left _ _)
    rw [e]
    simp only [min_def]; split_ifs <;> linarith
  have hsumD : ∑ v ∈ V, ∑ u ∈ V, D u v = 0 := skew_sum_zero V D hDskew
  have hmax : ∀ t : ℝ, max 0 t = (|t| + t) / 2 := by
    intro t; rcases le_total 0 t with h | h
    · rw [max_eq_right h, abs_of_nonneg h]; ring
    · rw [max_eq_left h, abs_of_nonpos h]; ring
  have habs : ∑ v ∈ V, ∑ u ∈ V, |D u v| ≤ ((V.card : ℝ) * ((V.card : ℝ) - 1)) * d := by
    calc ∑ v ∈ V, ∑ u ∈ V, |D u v| ≤ ∑ v ∈ V, ∑ u ∈ V, (if u = v then 0 else d) :=
          Finset.sum_le_sum (fun v hv => Finset.sum_le_sum (fun u hu => hDabs u hu v hv))
      _ = ∑ v ∈ V, ((V.card : ℝ) - 1) * d := by
          apply Finset.sum_congr rfl; intro v hv
          rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul]
          have : (V.filter (fun u => ¬ u = v)) = V.erase v := by
            ext u; simp [Finset.mem_erase, and_comm]
          rw [this, Finset.card_erase_of_mem hv]
          have : 1 ≤ V.card := Finset.card_pos.mpr ⟨v, hv⟩
          push_cast [this]; ring
      _ = ((V.card : ℝ) * ((V.card : ℝ) - 1)) * d := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hmaxsum : ∑ v ∈ V, ∑ u ∈ V, max 0 (D u v) ≤ ((V.card.choose 2 : ℕ) : ℝ) * d := by
    have : ∑ v ∈ V, ∑ u ∈ V, max 0 (D u v) =
        (∑ v ∈ V, ∑ u ∈ V, |D u v| + ∑ v ∈ V, ∑ u ∈ V, D u v) / 2 := by
      simp only [hmax]
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      apply Finset.sum_congr rfl; intro v _
      rw [← Finset.sum_add_distrib, Finset.sum_div]
    rw [this, hsumD, Nat.cast_choose_two]
    linarith
  unfold xsum xneg
  have := Finset.sum_le_sum hpt
  rw [Finset.sum_sub_distrib] at this
  linarith

end X5IW


open IwataFF.SFM

namespace X5IW

theorem swapAdj_eq {α : Type} [DecidableEq α] (L : List α) (u v : α) :
    swapAdj L u v = L.map (Equiv.swap u v) := by
  unfold swapAdj; congr 1

theorem swapAdj_ordering {α : Type} [DecidableEq α] (V : Finset α) (L : List α)
    (hL : IsOrdering V L) (u v : α) (hu : u ∈ V) (hv : v ∈ V) :
    IsOrdering V (swapAdj L u v) := by
  rw [swapAdj_eq]
  refine ⟨hL.1.map (Equiv.injective _), fun a => ?_⟩
  rw [List.mem_map]
  constructor
  · rintro ⟨b, hb, rfl⟩
    have hbV := (hL.2 b).mp hb
    rw [Equiv.swap_apply_def]; split_ifs <;> assumption
  · intro ha
    refine ⟨Equiv.swap u v a, (hL.2 _).mpr ?_, by simp⟩
    rw [Equiv.swap_apply_def]; split_ifs <;> assumption

theorem bdry_phiPush {α : Type} [DecidableEq α] (V : Finset α) (phi : α → α → ℝ)
    (u v : α) (hu : u ∈ V) (hv : v ∈ V) (huv : u ≠ v) (a : ℝ) (w : α) :
    ∑ p ∈ V, phiPush phi u v a p w =
      ∑ p ∈ V, phi p w + a * (chi u w - chi v w) := by
  have hpt : ∀ p, phiPush phi u v a p w =
      phi p w + ((if p = v then (if w = u then a else 0) else 0) -
        (if p = u then (if w = v then a else 0) else 0)) := by
    intro p
    unfold phiPush
    by_cases h1 : p = u <;> by_cases h2 : w = v <;> by_cases h3 : p = v <;>
      by_cases h4 : w = u <;> simp_all [sub_eq_add_neg]
  simp only [hpt]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq' V v,
    Finset.sum_ite_eq' V u, if_pos hv, if_pos hu]
  unfold chi
  by_cases h4 : w = u
  · subst h4; simp [huv]
  · by_cases h2 : w = v
    · subst h2; simp [h4]
    · simp [h4, h2]

set_option maxHeartbeats 400000 in
theorem push_step {α : Type} [DecidableEq α] (V : Finset α) (hV : V.Nonempty)
    (f : Finset α → ℝ) (hsub : SubmodularOn V f) (hf0 : f ∅ = 0)
    (st st' : PhaseState α) (hinv : PhaseInv V st) (h : PushStep f V st st') :
    PhaseInv V st' ∧ st'.delta = st.delta ∧ zOf f V st' = zOf f V st := by
  obtain ⟨_, _, _, i, L, lam, u, v, hi, hact, hsucc, rfl⟩ := h
  obtain ⟨hδ, _, hord, hsum, hskew, hfeas⟩ := hinv
  obtain ⟨hL, hlam⟩ := hord _ (mem_of_getElem? hi)
  obtain ⟨p, hp, hvV, hvW, hne', hmax⟩ := hact
  rw [hi] at hp; cases hp
  obtain ⟨hvL, hsu⟩ := hsucc
  set k := L.idxOf v with hk
  obtain ⟨hk1, hku⟩ := List.getElem?_eq_some_iff.mp hsu
  have huL : u ∈ L := by rw [← hku]; exact List.getElem_mem hk1
  have huV : u ∈ V := (hL.2 u).mp huL
  have hidxu : L.idxOf u = k + 1 := by rw [← hku]; exact hL.1.idxOf_getElem _ hk1
  have huv : u ≠ v := by
    intro e; rw [e] at hidxu; omega
  -- u ∈ W
  have huW : u ∈ Wset f V st := by
    by_contra huW
    have hpre : prefixSet L u = insert u (prefixSet L v) := by
      unfold prefixSet; rw [hidxu, ← hk]
      have := take_succ_toFinset L (k + 1) hk1
      rw [hku] at this; exact this
    have hne2 : (Wset f V st \ prefixSet L u).Nonempty := by
      rw [hpre]; obtain ⟨w, hw⟩ := hne'
      refine ⟨w, ?_⟩
      rw [Finset.mem_sdiff] at hw ⊢
      refine ⟨hw.1, ?_⟩
      rw [Finset.mem_insert]; rintro (rfl | h); exact huW hw.1; exact hw.2 h
    have := hmax u huV huW hne2
    simp only at this
    omega
  have hphi : 0 < st.phi u v := by
    by_contra hneg
    apply hvW
    simp only [Wset, Finset.mem_filter] at huW ⊢
    obtain ⟨_, s, hs, hr⟩ := huW
    exact ⟨hvV, s, hs, hr.tail ⟨huV, hvV, huv, le_of_not_gt hneg⟩⟩
  -- exchange capacity
  have hyb := greedy_base V f hsub hf0 L hL
  set e := ec V f (greedy f L) u v with he_def
  have he : 0 ≤ e := ec_nonneg V f _ hyb u v
  obtain ⟨hg, hec⟩ := lemma_2_1 V hV f hsub hf0 L hL u v ⟨hvL, hsu⟩
  rw [← hec] at hg
  set a := min st.delta (lam * e) with ha_def
  have ha0 : 0 ≤ a := le_min hδ.le (mul_nonneg hlam.le he)
  have haδ : a ≤ st.delta := min_le_left _ _
  have hL' := swapAdj_ordering V L hL u v huV hvV
  have hfeas' := hfeas u huV v hvV
  have hsk := hskew u huV v hvV
  -- phi part of the invariant
  have hskew' : ∀ p ∈ V, ∀ q ∈ V, phiPush st.phi u v a p q + phiPush st.phi u v a q p = 0 := by
    intro p hp q hq
    have := hskew p hp q hq
    unfold phiPush
    by_cases h1 : p = u <;> by_cases h2 : q = v <;> by_cases h3 : p = v <;>
      by_cases h4 : q = u <;> simp_all <;> linarith
  have hfeas2 : ∀ p ∈ V, ∀ q ∈ V, -st.delta ≤ phiPush st.phi u v a p q ∧
      phiPush st.phi u v a p q ≤ st.delta := by
    intro p hp q hq
    have := hfeas p hp q hq
    unfold phiPush
    split_ifs with h1 h2
    · obtain ⟨rfl, rfl⟩ := h1; constructor <;> linarith
    · obtain ⟨rfl, rfl⟩ := h2; constructor <;> linarith
    · exact this
  -- x part
  have hx : ∀ w, xOf f (pushResult f V st i L lam u v) w =
      xOf f st w + a * (chi u w - chi v w) := by
    intro w
    have hgw : greedy f (swapAdj L u v) w = greedy f L w + e * (chi u w - chi v w) := by
      rw [hg]; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, he_def]
    unfold xOf pushResult
    simp only
    rw [← he_def, ← ha_def]
    split_ifs with hs
    · rw [List.map_append, List.sum_append,
        list_sum_set (fun p => p.2 * greedy f p.1 w) _ i _ _ hi]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hgw]
      have hepos : 0 < e := by
        by_contra hh
        have : e = 0 := le_antisymm (not_lt.mp hh) he
        rw [this, mul_zero] at hs; linarith
      field_simp
      ring
    · have hae : a = lam * e := le_antisymm (min_le_right _ _) (not_lt.mp hs)
      rw [list_sum_set (fun p => p.2 * greedy f p.1 w) _ i _ _ hi]
      simp only [hgw, hae]; ring
  -- bookkeeping on the index list
  have hidx : (∀ p ∈ (pushResult f V st i L lam u v).idx, IsOrdering V p.1 ∧ 0 < p.2) ∧
      ((pushResult f V st i L lam u v).idx.map Prod.snd).sum = 1 := by
    unfold pushResult
    simp only
    rw [← he_def, ← ha_def]
    split_ifs with hs
    · have hapos : 0 < a := by
        have : a = st.delta := by
          rcases min_choice st.delta (lam * e) with h | h
          · exact h
          · rw [← ha_def] at h; rw [h] at hs; exact absurd hs (lt_irrefl _)
        rw [this]; exact hδ
      have hepos : 0 < e := by
        by_contra hh
        have : e = 0 := le_antisymm (not_lt.mp hh) he
        rw [this, mul_zero] at hs; linarith
      refine ⟨fun p hp => ?_, ?_⟩
      · rw [List.mem_append] at hp
        rcases hp with hp | hp
        · rcases List.mem_or_eq_of_mem_set hp with hp | rfl
          · exact hord p hp
          · exact ⟨hL', div_pos hapos hepos⟩
        · rw [List.mem_singleton] at hp; subst hp
          refine ⟨hL, ?_⟩
          simp only
          rw [sub_pos, div_lt_iff₀ hepos]; linarith
      · rw [List.map_append, List.sum_append, list_sum_set Prod.snd _ i _ _ hi, hsum]
        simp
    · refine ⟨fun p hp => ?_, ?_⟩
      · rcases List.mem_or_eq_of_mem_set hp with hp | rfl
        · exact hord p hp
        · exact ⟨hL', hlam⟩
      · rw [list_sum_set Prod.snd _ i _ _ hi, hsum]; simp
  refine ⟨⟨hδ, ?_, hidx.1, hidx.2, hskew', hfeas2⟩, rfl, ?_⟩
  · intro hnil; have := hidx.2; rw [hnil] at this; simp at this
  · funext w
    unfold zOf bdry
    rw [hx w]
    simp only [pushResult]
    rw [bdry_phiPush V st.phi u v huV hvV huv a w]
    ring

end X5IW


open IwataFF.SFM

namespace X5IW

theorem chain_zip {β : Type*} (R : β → β → Prop) :
    ∀ P : List β, P.IsChain R → ∀ a b, (a, b) ∈ P.zip P.tail → R a b
  | [], _, a, b, h => by simp at h
  | [_], _, a, b, h => by simp at h
  | x :: y :: rest, hc, a, b, h => by
      rw [List.isChain_cons_cons] at hc
      have e : (x :: y :: rest).zip (x :: y :: rest).tail =
          (x, y) :: (y :: rest).zip (y :: rest).tail := by simp
      rw [e, List.mem_cons] at h
      rcases h with h | h
      · cases h; exact hc.1
      · exact chain_zip R (y :: rest) hc.2 a b h

theorem chain_mem {β : Type*} (R : β → β → Prop) (V : Set β)
    (hR : ∀ a b, R a b → b ∈ V) :
    ∀ P : List β, P.IsChain R → (∀ a ∈ P.head?, a ∈ V) → ∀ x ∈ P, x ∈ V
  | [], _, _, x, h => by simp at h
  | [y], _, hh, x, h => by
      simp at h; subst h; exact hh _ rfl
  | y :: z :: rest, hc, hh, x, h => by
      rw [List.isChain_cons_cons] at hc
      rw [List.mem_cons] at h
      rcases h with rfl | h
      · exact hh _ rfl
      · exact chain_mem R V hR (z :: rest) hc.2 (fun a ha => by
          simp at ha; subst ha; exact hR _ _ hc.1) x h

open Classical in
theorem path_div {α : Type} [DecidableEq α] (V : Finset α) :
    ∀ P : List α, P ≠ [] → P.Nodup → (∀ x ∈ P, x ∈ V) → ∀ w,
      ∑ u ∈ V, ((if (u, w) ∈ P.zip P.tail then (1 : ℝ) else 0) -
        (if (w, u) ∈ P.zip P.tail then (1 : ℝ) else 0)) =
      (if P.getLast? = some w then 1 else 0) - (if P.head? = some w then 1 else 0)
  | [], h, _, _, _ => absurd rfl h
  | [x], _, _, _, w => by simp
  | x :: y :: rest, _, hnd, hV, w => by
      have e : (x :: y :: rest).zip (x :: y :: rest).tail =
          (x, y) :: (y :: rest).zip (y :: rest).tail := by simp
      have hxQ : x ∉ y :: rest := (List.nodup_cons.mp hnd).1
      have hnd' : (y :: rest).Nodup := (List.nodup_cons.mp hnd).2
      have ih := path_div V (y :: rest) (by simp) hnd' (fun z hz => hV z (List.mem_cons_of_mem _ hz)) w
      have hxV : x ∈ V := hV x List.mem_cons_self
      have hyV : y ∈ V := hV y (by simp)
      have hnot : ∀ b, (x, b) ∉ (y :: rest).zip (y :: rest).tail :=
        fun b hb => hxQ (List.of_mem_zip hb).1
      have hpt : ∀ u, ((if (u, w) ∈ (x :: y :: rest).zip (x :: y :: rest).tail then (1 : ℝ) else 0) -
          (if (w, u) ∈ (x :: y :: rest).zip (x :: y :: rest).tail then (1 : ℝ) else 0)) =
          ((if u = x then (if w = y then (1 : ℝ) else 0) else 0) -
            (if u = y then (if w = x then (1 : ℝ) else 0) else 0)) +
          ((if (u, w) ∈ (y :: rest).zip (y :: rest).tail then (1 : ℝ) else 0) -
            (if (w, u) ∈ (y :: rest).zip (y :: rest).tail then (1 : ℝ) else 0)) := by
        intro u
        rw [e]
        have h1 : ((u, w) ∈ (x, y) :: (y :: rest).zip (y :: rest).tail) ↔
            (u = x ∧ w = y) ∨ (u, w) ∈ (y :: rest).zip (y :: rest).tail := by
          rw [List.mem_cons, Prod.mk.injEq]
        have h2 : ((w, u) ∈ (x, y) :: (y :: rest).zip (y :: rest).tail) ↔
            (w = x ∧ u = y) ∨ (w, u) ∈ (y :: rest).zip (y :: rest).tail := by
          rw [List.mem_cons, Prod.mk.injEq]
        by_cases a1 : u = x
        · subst a1
          have := hnot w
          by_cases a2 : w = y <;> by_cases a3 : (w, u) ∈ (y :: rest).zip (y :: rest).tail <;>
            by_cases a4 : u = y <;> simp_all
        · by_cases a2 : w = x
          · subst a2
            have := hnot u
            by_cases a4 : u = y <;> by_cases a5 : (u, w) ∈ (y :: rest).zip (y :: rest).tail <;>
              simp_all
          · simp only [h1, h2, a1, a2, false_and, false_or, if_false]
            split_ifs <;> simp
      rw [Finset.sum_congr rfl (fun u _ => hpt u), Finset.sum_add_distrib, ih,
        Finset.sum_sub_distrib, Finset.sum_ite_eq' V x, Finset.sum_ite_eq' V y, if_pos hxV,
        if_pos hyV, List.getLast?_cons_cons]
      simp only [List.head?_cons, Option.some.injEq]
      have hxy : x ≠ y := fun h => hxQ (h ▸ List.mem_cons_self)
      split_ifs <;> first | (exfalso; subst_vars; tauto) | linarith | norm_num

end X5IW

namespace X5IW

theorem aug_step {α : Type} [DecidableEq α] (V : Finset α)
    (f : Finset α → ℝ) (st st' : PhaseState α) (hinv : PhaseInv V st) (h : AugStep f V st st') :
    PhaseInv V st' ∧ st'.delta = st.delta ∧
      xsum (xneg (zOf f V st')) V = xsum (xneg (zOf f V st)) V + st.delta := by
  obtain ⟨_, _, _, P, hP, hred⟩ := h
  obtain ⟨hδ, _, hord, hsum, hskew, hfeas⟩ := hinv
  obtain ⟨hphi', hdel', _, hsl, hpos', hsum', hx', _⟩ := hred
  simp only at hphi' hdel'
  obtain ⟨hnd, ⟨s, hs, hsS⟩, ⟨t, ht, htT⟩, hch⟩ := hP
  have hsV : s ∈ V := (Finset.mem_filter.mp hsS).1
  have hzs : zOf f V st s ≤ -st.delta := by
    have := (Finset.mem_filter.mp hsS).2; unfold zOf; linarith
  have hzt : st.delta ≤ zOf f V st t := by
    have := (Finset.mem_filter.mp htT).2; unfold zOf; linarith
  have hst : s ≠ t := by intro e; subst e; linarith
  have hPV : ∀ x ∈ P, x ∈ V := chain_mem (resArc V st) (↑V) (fun a b h => h.2.1) P hch
    (fun a ha => by rw [hs] at ha; cases ha; exact hsV)
  have hPne : P ≠ [] := by intro e; rw [e] at hs; simp at hs
  have harc := chain_zip (resArc V st) P hch
  -- orderings
  have hord' : ∀ p ∈ st'.idx, IsOrdering V p.1 ∧ 0 < p.2 := by
    intro p hp
    refine ⟨?_, hpos' p hp⟩
    have : p.1 ∈ st'.idx.map Prod.fst := List.mem_map_of_mem hp
    have := hsl.subset this
    rw [List.mem_map] at this
    obtain ⟨q, hq, hq1⟩ := this
    rw [← hq1]; exact (hord q hq).1
  -- the new flow
  have hphi_eq : st'.phi = augPhi st.phi st.delta P := hphi'
  have hskew' : ∀ p ∈ V, ∀ q ∈ V, st'.phi p q + st'.phi q p = 0 := by
    intro p hp q hq
    rw [hphi_eq]; unfold augPhi
    have := hskew p hp q hq
    linarith
  have hfeas' : ∀ p ∈ V, ∀ q ∈ V, -st'.delta ≤ st'.phi p q ∧ st'.phi p q ≤ st'.delta := by
    intro p hp q hq
    rw [hphi_eq, hdel']; unfold augPhi
    have h1 := hfeas p hp q hq
    have h2 := hskew p hp q hq
    split_ifs with a1 a2 a2
    · constructor <;> linarith
    · have := (harc p q a1).2.2.2; constructor <;> linarith
    · have := (harc q p a2).2.2.2; constructor <;> linarith
    · constructor <;> linarith
  refine ⟨⟨hdel' ▸ hδ, ?_, hord', hsum', hskew', hfeas'⟩, hdel', ?_⟩
  · intro hnil; rw [hnil] at hsum'; simp at hsum'
  -- z⁻ increases by δ
  have hz : ∀ w, zOf f V st' w = zOf f V st w + (if w = s then st.delta else 0) -
      (if w = t then st.delta else 0) := by
    intro w
    have hd := path_div V P hPne hnd hPV w
    rw [ht, hs] at hd
    have hxw : xOf f st' w = xOf f st w := by rw [hx']; rfl
    unfold zOf bdry
    rw [hxw, hphi_eq]
    unfold augPhi
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hd]
    simp only [Option.some.injEq]
    split_ifs <;> first | (exfalso; subst_vars; tauto) | linarith | norm_num
  unfold xsum xneg
  have hpt : ∀ w ∈ V, min 0 (zOf f V st' w) = min 0 (zOf f V st w) +
      (if w = s then st.delta else 0) := by
    intro w _
    rw [hz w]
    by_cases a1 : w = s
    · have a2 : ¬ w = t := by rintro rfl; exact hst a1.symm
      rw [if_pos a1, if_neg a2, a1]
      rw [min_eq_right (by linarith), min_eq_right (by linarith)]; ring
    · by_cases a2 : w = t
      · rw [if_pos a2, if_neg a1, a2]
        rw [min_eq_left (by linarith), min_eq_left (by linarith)]; ring
      · simp [a1, a2]
  rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_ite_eq' V s, if_pos hsV]

end X5IW


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



open IwataFF.SFM MainState

namespace X5TC

variable {n : ℕ}

theorem biU_inter (P : Finset (Finset (Fin n)))
    (hP : ∀ A ∈ P, ∀ B ∈ P, A ≠ B → Disjoint A B) (X Y : Finset (Finset (Fin n)))
    (hX : X ⊆ P) (hY : Y ⊆ P) : (X ∩ Y).biUnion id = X.biUnion id ∩ Y.biUnion id := by
  ext a
  simp only [Finset.mem_biUnion, Finset.mem_inter, id]
  constructor
  · rintro ⟨A, ⟨h1, h2⟩, ha⟩; exact ⟨⟨A, h1, ha⟩, ⟨A, h2, ha⟩⟩
  · rintro ⟨⟨A, h1, ha⟩, ⟨B, h2, hb⟩⟩
    by_cases hAB : A = B
    · subst hAB; exact ⟨A, ⟨h1, h2⟩, ha⟩
    · exact absurd hb (Finset.disjoint_left.mp (hP A (hX h1) B (hY h2) hAB) ha)

theorem mem_of_biU (P : Finset (Finset (Fin n)))
    (hP : ∀ A ∈ P, ∀ B ∈ P, A ≠ B → Disjoint A B) (hne : ∀ A ∈ P, A.Nonempty)
    (X : Finset (Finset (Fin n))) (hX : X ⊆ P) (b : Finset (Fin n)) (hb : b ∈ P)
    (h : b ⊆ X.biUnion id) : b ∈ X := by
  obtain ⟨a, ha⟩ := hne b hb
  obtain ⟨A, hA, haA⟩ := Finset.mem_biUnion.mp (h ha)
  by_cases e : A = b
  · exact e ▸ hA
  · exact absurd ha (Finset.disjoint_left.mp (hP A (hX hA) b hb e) haA)

theorem exists_min (V : Finset (Finset (Fin n))) (f : Finset (Finset (Fin n)) → ℝ) :
    ∃ X, IsMinimizer V f X := by
  obtain ⟨X, hX, hmin⟩ := Finset.exists_min_image V.powerset f ⟨∅, Finset.empty_mem_powerset V⟩
  exact ⟨X, Finset.mem_powerset.mp hX, fun Y hY => hmin Y (Finset.mem_powerset.mpr hY)⟩

theorem clip_inv {α : Type} [DecidableEq α] (V : Finset α) (st : PhaseState α)
    (hinv : PhaseInv V st) :
    PhaseInv V (PhaseState.mk st.idx (clip st.phi (st.delta / 2)) (st.delta / 2) true) := by
  obtain ⟨hδ, hne, hord, hsum, hskew, hfeas⟩ := hinv
  refine ⟨by simp only; linarith, hne, hord, hsum, ?_, ?_⟩
  · intro u hu v hv
    have := hskew u hu v hv
    have e : st.phi v u = - st.phi u v := by linarith
    simp only [clip, e]
    rcases le_total (st.delta / 2) (st.phi u v) with h | h <;>
      rcases le_total (-(st.delta / 2)) (st.phi u v) with h' | h' <;>
      simp only [min_def, max_def] <;> split_ifs <;> linarith
  · intro u _ v _
    simp only [clip]
    constructor
    · exact le_max_left _ _
    · apply max_le (by linarith) (min_le_left _ _)

structure GInv (s : MainState n) : Prop where
  base : X5FC.Inv s
  sub : SubmodularOn s.blocks s.curFun
  zero : s.curFun ∅ = 0
  compat : ∀ e ∈ s.arcs, Compatible s.blocks s.curFun e.1 e.2
  phase : ∀ fr u η ph, s.mode = Mode.fix fr u η ph → PhaseInv (s.fixGround fr u) ph

theorem R_sub (s : MainState n) (v : Finset (Fin n)) : s.R v ⊆ s.blocks := fun X hX => by
  unfold MainState.R at hX; rw [X5FC.mem_reach] at hX; exact hX.1

theorem R_self (s : MainState n) (v : Finset (Fin n)) (hv : v ∈ s.blocks) : v ∈ s.R v := by
  unfold MainState.R; rw [X5FC.mem_reach]; exact ⟨hv, Relation.ReflTransGen.refl⟩

theorem closure (s : MainState n) (hG : GInv s) (X : Finset (Finset (Fin n)))
    (hX : IsMinimizer s.blocks s.curFun X) (a : Finset (Fin n)) (ha : a ∈ X) : s.R a ⊆ X := by
  intro b hb
  unfold MainState.R at hb; rw [X5FC.mem_reach] at hb
  obtain ⟨hbB, hr⟩ := hb
  revert hbB
  induction hr with
  | refl => intro _; exact ha
  | tail _ hyz ih =>
    intro _
    exact hG.compat _ hyz X hX (ih (hG.base.arcs _ hyz).1)

theorem fix_sub (s : MainState n) (hG : GInv s) (fr : Bool) (u : Finset (Fin n)) :
    SubmodularOn (s.fixGround fr u) (s.fixFun fr u) ∧ s.fixFun fr u ∅ = 0 := by
  have hR := R_sub s u
  cases fr
  · simp only [MainState.fixGround, MainState.fixFun, Bool.false_eq_true, ↓reduceIte]
    exact ⟨hG.sub, hG.zero⟩
  · simp only [MainState.fixGround, MainState.fixFun, ↓reduceIte]
    refine ⟨fun X hX Y hY => ?_, by simp [restrictFun]⟩
    unfold restrictFun
    have h1 : X ∪ s.R u ⊆ s.blocks := Finset.union_subset (hX.trans Finset.sdiff_subset) hR
    have h2 : Y ∪ s.R u ⊆ s.blocks := Finset.union_subset (hY.trans Finset.sdiff_subset) hR
    have := hG.sub _ h1 _ h2
    have e1 : X ∪ Y ∪ s.R u = (X ∪ s.R u) ∪ (Y ∪ s.R u) := by
      ext; simp only [Finset.mem_union]; tauto
    have e2 : X ∩ Y ∪ s.R u = (X ∪ s.R u) ∩ (Y ∪ s.R u) := by
      ext; simp only [Finset.mem_union, Finset.mem_inter]; tauto
    rw [e1, e2]; linarith

theorem return_facts (s : MainState n) (hG : GInv s) (fr : Bool) (u : Finset (Fin n)) (η : ℝ)
    (ph : PhaseState (Finset (Fin n))) (hm : s.mode = Mode.fix fr u η ph) (w : Finset (Fin n))
    (hw : FixOutput (s.fixFun fr u) (s.fixGround fr u) (η / 2) ph w) :
    (fr = true → w ∈ s.blocks \ s.R u ∧ Compatible s.blocks s.curFun u w) ∧
      (fr = false → ∀ X, IsMinimizer s.blocks s.curFun X → w ∈ X ∧ s.R w ⊆ X) := by
  obtain ⟨_, hend, _, hwV, hx⟩ := hw
  obtain ⟨hsub', hz'⟩ := fix_sub s hG fr u
  have L := lemma_4_1 (s.fixGround fr u) ⟨w, hwV⟩ (s.fixFun fr u) hsub' hz' ph
    (hG.phase fr u η ph hm) hend w hwV hx
  have hR := R_sub s u
  refine ⟨fun hfr => ?_, fun hfr => ?_⟩
  · subst hfr
    have hwV' : w ∈ s.blocks \ s.R u := by
      simpa only [MainState.fixGround, ↓reduceIte] using hwV
    refine ⟨hwV', fun X hX huX => ?_⟩
    have hRX := closure s hG X hX u huX
    have hmin : IsMinimizer (s.fixGround true u) (s.fixFun true u) (X \ s.R u) := by
      simp only [MainState.fixGround, MainState.fixFun, ↓reduceIte]
      refine ⟨Finset.sdiff_subset_sdiff hX.1 subset_rfl, fun Y hY => ?_⟩
      unfold restrictFun
      rw [Finset.sdiff_union_of_subset hRX]
      have hYR : Y ∪ s.R u ⊆ s.blocks := Finset.union_subset (hY.trans Finset.sdiff_subset) hR
      linarith [hX.2 _ hYR]
    exact (Finset.mem_sdiff.mp (L _ hmin)).1
  · subst hfr
    intro X hX
    have hmin : IsMinimizer (s.fixGround false u) (s.fixFun false u) X := by
      simp only [MainState.fixGround, MainState.fixFun, Bool.false_eq_true, ↓reduceIte]
      exact hX
    have := L X hmin
    exact ⟨this, closure s hG X hX w this⟩

/-- the cap `f(V) ← 0` keeps submodularity, `f(∅) = 0` and compatibility of arcs. -/
theorem cap_parts (s : MainState n) (hG : GInv s) :
    SubmodularOn s.cap.blocks s.cap.curFun ∧ s.cap.curFun ∅ = 0 ∧
      ∀ e ∈ s.cap.arcs, Compatible s.cap.blocks s.cap.curFun e.1 e.2 := by
  set T := s.blocks.biUnion id with hT
  set g : Finset (Fin n) → ℝ := fun S => if S = T ∧ 0 < s.h S then 0 else s.h S with hg
  have hcf : ∀ X, s.cap.curFun X = g (X.biUnion id) := fun X => rfl
  have hof : ∀ X, s.curFun X = s.h (X.biUnion id) := fun X => rfl
  have hb : s.cap.blocks = s.blocks := rfl
  have ha : s.cap.arcs = s.arcs := rfl
  have hgle : ∀ S, g S ≤ s.h S := by
    intro S; simp only [hg]; split_ifs with h
    · exact h.2.le
    · exact le_rfl
  have hsubT : ∀ X ⊆ s.blocks, X.biUnion id ⊆ T := fun X hX =>
    Finset.biUnion_subset_biUnion_of_subset_left _ hX
  have hdisj := hG.base.disj
  refine ⟨?_, ?_, ?_⟩
  · intro X hX Y hY
    rw [hb] at hX hY
    rw [hcf, hcf, hcf, hcf, Finset.union_biUnion, biU_inter s.blocks hdisj X Y hX hY]
    have hold := hG.sub X hX Y hY
    rw [hof, hof, hof, hof, Finset.union_biUnion, biU_inter s.blocks hdisj X Y hX hY] at hold
    set SX := X.biUnion id
    set SY := Y.biUnion id
    by_cases hx : SX = T ∧ 0 < s.h SX
    · have e1 : SX ∪ SY = T := by rw [hx.1]; exact Finset.union_eq_left.mpr (hsubT Y hY)
      have e2 : SX ∩ SY = SY := by rw [hx.1]; exact Finset.inter_eq_right.mpr (hsubT Y hY)
      have g1 : g T = 0 := by simp only [hg]; rw [if_pos ⟨trivial, by rw [← hx.1]; exact hx.2⟩]
      have g2 : g SX = 0 := by rw [hx.1, g1]
      rw [e1, e2, g1, g2] <;> linarith
    · by_cases hy : SY = T ∧ 0 < s.h SY
      · have e1 : SX ∪ SY = T := by rw [hy.1]; exact Finset.union_eq_right.mpr (hsubT X hX)
        have e2 : SX ∩ SY = SX := by rw [hy.1]; exact Finset.inter_eq_left.mpr (hsubT X hX)
        have g1 : g T = 0 := by simp only [hg]; rw [if_pos ⟨trivial, by rw [← hy.1]; exact hy.2⟩]
        have g2 : g SY = 0 := by rw [hy.1, g1]
        rw [e1, e2, g1, g2] <;> linarith
      · have g1 : g SX = s.h SX := by simp only [hg]; rw [if_neg hx]
        have g2 : g SY = s.h SY := by simp only [hg]; rw [if_neg hy]
        rw [g1, g2]
        linarith [hgle (SX ∪ SY), hgle (SX ∩ SY)]
  · rw [hcf]
    have h0 : s.h ∅ = 0 := hG.zero
    simp only [Finset.biUnion_empty, hg, h0, lt_irrefl, and_false, ↓reduceIte]
  · intro e he X hX h1
    rw [ha] at he
    rw [hb] at hX
    have heb := hG.base.arcs e he
    by_cases hTX : X.biUnion id = T
    · apply mem_of_biU s.blocks hdisj hG.base.ne X hX.1 e.2 heb.2
      rw [hTX]; exact Finset.subset_biUnion_of_mem id heb.2
    · have hXmin : IsMinimizer s.blocks s.curFun X := by
        refine ⟨hX.1, fun Y hY => ?_⟩
        have := hX.2 Y hY
        rw [hcf, hcf] at this
        rw [hof, hof]
        have e1 : g (X.biUnion id) = s.h (X.biUnion id) := by
          simp only [hg]; rw [if_neg (fun h => hTX h.1)]
        linarith [hgle (Y.biUnion id)]
      exact hG.compat e he X hXmin h1

end X5TC


open IwataFF.SFM MainState

namespace X5TC

variable {n : ℕ}

theorem contract_parts (s s' : MainState n) (hG : GInv s) (hI' : X5FC.Inv s')
    (C : Finset (Finset (Fin n))) (hCb : C ⊆ s.blocks) (hCne : C.Nonempty)
    (hbl : ∀ X, X ∈ s'.blocks ↔ X = C.biUnion id ∨ (X ∈ s.blocks ∧ X ∉ C))
    (harc : ∀ x y, (x, y) ∈ s'.arcs ↔ x ≠ y ∧ ∃ a b, (a, b) ∈ s.arcs ∧
      (if a ∈ C then C.biUnion id else a) = x ∧ (if b ∈ C then C.biUnion id else b) = y)
    (hh : s'.h = s.h)
    (hP : ∀ X, IsMinimizer s.blocks s.curFun X → C ⊆ X ∨ Disjoint C X) :
    SubmodularOn s'.blocks s'.curFun ∧ s'.curFun ∅ = 0 ∧
      ∀ e ∈ s'.arcs, Compatible s'.blocks s'.curFun e.1 e.2 := by
  set B := C.biUnion id with hB
  have hDB : ∀ D ∈ s.blocks, D ∉ C → D ≠ B := by
    intro D hD hDC e
    obtain ⟨c, hc⟩ := hCne
    obtain ⟨a, ha⟩ := hG.base.ne c (hCb hc)
    have hcD : c ≠ D := fun e' => hDC (e' ▸ hc)
    have : a ∈ D := by rw [e]; exact Finset.mem_biUnion.mpr ⟨c, hc, ha⟩
    exact Finset.disjoint_left.mp (hG.base.disj c (hCb hc) D hD hcD) ha this
  set E : Finset (Finset (Fin n)) → Finset (Finset (Fin n)) :=
    fun X' => X'.erase B ∪ (if B ∈ X' then C else ∅) with hE
  have hEsub : ∀ X' ⊆ s'.blocks, E X' ⊆ s.blocks := by
    intro X' hX' D hD
    simp only [hE, Finset.mem_union, Finset.mem_erase] at hD
    rcases hD with ⟨hDB', hD⟩ | hD
    · rcases (hbl D).mp (hX' hD) with e | ⟨hD, _⟩
      · exact absurd e hDB'
      · exact hD
    · split_ifs at hD with h
      · exact hCb hD
      · simp at hD
  have hEU : ∀ X' ⊆ s'.blocks, (E X').biUnion id = X'.biUnion id := by
    intro X' hX'
    ext a
    simp only [Finset.mem_biUnion, hE, Finset.mem_union, Finset.mem_erase, id]
    constructor
    · rintro ⟨D, hD, ha⟩
      rcases hD with ⟨_, hD⟩ | hD
      · exact ⟨D, hD, ha⟩
      · split_ifs at hD with h
        · exact ⟨B, h, Finset.mem_biUnion.mpr ⟨D, hD, ha⟩⟩
        · simp at hD
    · rintro ⟨D, hD, ha⟩
      by_cases e : D = B
      · rw [e] at ha hD
        obtain ⟨c, hc, hac⟩ := Finset.mem_biUnion.mp ha
        exact ⟨c, Or.inr (by rw [if_pos hD]; exact hc), hac⟩
      · exact ⟨D, Or.inl ⟨e, hD⟩, ha⟩
  have hcf : ∀ X' ⊆ s'.blocks, s'.curFun X' = s.curFun (E X') := by
    intro X' hX'
    show s'.h (X'.biUnion id) = s.h ((E X').biUnion id)
    rw [hh, hEU X' hX']
  obtain ⟨X0, hX0⟩ := exists_min s.blocks s.curFun
  set m : Finset (Fin n) → Finset (Fin n) := fun b => if b ∈ C then B else b with hm
  have hX0' : X0.image m ⊆ s'.blocks := by
    intro D hD
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hD
    rw [hbl]
    by_cases h : b ∈ C
    · left; simp [hm, h]
    · right; simp only [hm, if_neg h]; exact ⟨hX0.1 hb, h⟩
  have hX0U : (X0.image m).biUnion id = X0.biUnion id := by
    ext a
    simp only [Finset.mem_biUnion, Finset.mem_image, id]
    constructor
    · rintro ⟨D, ⟨b, hb, rfl⟩, ha⟩
      by_cases h : b ∈ C
      · simp only [hm, if_pos h] at ha
        obtain ⟨c, hc, hac⟩ := Finset.mem_biUnion.mp ha
        have hCX : C ⊆ X0 := by
          rcases hP X0 hX0 with h' | h'
          · exact h'
          · exact absurd hb (Finset.disjoint_left.mp h' h)
        exact ⟨c, hCX hc, hac⟩
      · simp only [hm, if_neg h] at ha; exact ⟨b, hb, ha⟩
    · rintro ⟨b, hb, ha⟩
      refine ⟨m b, ⟨b, hb, rfl⟩, ?_⟩
      by_cases h : b ∈ C
      · simp only [hm, if_pos h]; exact Finset.mem_biUnion.mpr ⟨b, h, ha⟩
      · simp only [hm, if_neg h]; exact ha
  have hEmin : ∀ X', IsMinimizer s'.blocks s'.curFun X' →
      IsMinimizer s.blocks s.curFun (E X') := by
    intro X' hX'
    refine ⟨hEsub X' hX'.1, fun Y hY => ?_⟩
    have h1 := hX'.2 _ hX0'
    rw [hcf X' hX'.1] at h1
    have h2 : s'.curFun (X0.image m) = s.curFun X0 := by
      show s'.h _ = s.h _; rw [hh, hX0U]
    have h3 := hX0.2 Y hY
    linarith
  refine ⟨?_, ?_, ?_⟩
  · intro X' hX' Y' hY'
    have hu1 : s'.curFun (X' ∪ Y') = s.curFun (E X' ∪ E Y') := by
      show s'.h _ = s.h _
      rw [hh, Finset.union_biUnion, Finset.union_biUnion, hEU X' hX', hEU Y' hY']
    have hu2 : s'.curFun (X' ∩ Y') = s.curFun (E X' ∩ E Y') := by
      show s'.h _ = s.h _
      rw [hh, biU_inter s'.blocks hI'.disj X' Y' hX' hY',
        biU_inter s.blocks hG.base.disj _ _ (hEsub X' hX') (hEsub Y' hY'), hEU X' hX', hEU Y' hY']
    rw [hu1, hu2, hcf X' hX', hcf Y' hY']
    exact hG.sub _ (hEsub X' hX') _ (hEsub Y' hY')
  · show s'.h _ = 0
    rw [hh]; exact hG.zero
  · rintro ⟨x, y⟩ he X' hX' hx
    obtain ⟨_, a, b, hab, rfl, rfl⟩ := (harc x y).mp he
    have hEX := hEmin X' hX'
    have hab' := hG.base.arcs _ hab
    have haE : a ∈ E X' := by
      simp only [hE, Finset.mem_union, Finset.mem_erase]
      by_cases h : a ∈ C
      · simp only [if_pos h] at hx; right; rw [if_pos hx]; exact h
      · simp only [if_neg h] at hx; left; exact ⟨hDB a hab'.1 h, hx⟩
    have hbE := hG.compat _ hab (E X') hEX haE
    simp only [hE, Finset.mem_union, Finset.mem_erase] at hbE
    show (if b ∈ C then B else b) ∈ X'
    by_cases h : b ∈ C
    · rw [if_pos h]
      rcases hbE with ⟨_, hbX⟩ | hbX
      · rcases (hbl b).mp (hX'.1 hbX) with e | ⟨_, hbC⟩
        · rw [← e]; exact hbX
        · exact absurd h hbC
      · split_ifs at hbX with hB'
        · exact hB'
        · simp at hbX
    · rw [if_neg h]
      rcases hbE with ⟨_, hbX⟩ | hbX
      · exact hbX
      · split_ifs at hbX
        · exact absurd hbX h
        · simp at hbX

theorem delete_parts (s s' : MainState n) (hG : GInv s) (Rw : Finset (Finset (Fin n)))
    (hRb : Rw ⊆ s.blocks)
    (hbl : ∀ X, X ∈ s'.blocks ↔ X ∈ s.blocks ∧ X ∉ Rw)
    (harc : ∀ e, e ∈ s'.arcs ↔ e ∈ s.arcs ∧ e.1 ∉ Rw ∧ e.2 ∉ Rw)
    (hh : s'.h = fun S => s.h (S ∪ Rw.biUnion id) - s.h (Rw.biUnion id))
    (hP : ∀ X, IsMinimizer s.blocks s.curFun X → Rw ⊆ X) :
    SubmodularOn s'.blocks s'.curFun ∧ s'.curFun ∅ = 0 ∧
      ∀ e ∈ s'.arcs, Compatible s'.blocks s'.curFun e.1 e.2 := by
  have hcf : ∀ X', s'.curFun X' = s.curFun (X' ∪ Rw) - s.curFun Rw := by
    intro X'
    show s'.h _ = s.h _ - s.h _
    rw [hh, Finset.union_biUnion]
  have hsub' : ∀ X' ⊆ s'.blocks, X' ∪ Rw ⊆ s.blocks := fun X' hX' =>
    Finset.union_subset (fun D hD => ((hbl D).mp (hX' hD)).1) hRb
  obtain ⟨X0, hX0⟩ := exists_min s.blocks s.curFun
  have hRX0 := hP X0 hX0
  have hX0' : X0 \ Rw ⊆ s'.blocks := fun D hD =>
    (hbl D).mpr ⟨hX0.1 (Finset.mem_sdiff.mp hD).1, (Finset.mem_sdiff.mp hD).2⟩
  have hmin : ∀ X', IsMinimizer s'.blocks s'.curFun X' →
      IsMinimizer s.blocks s.curFun (X' ∪ Rw) := by
    intro X' hX'
    refine ⟨hsub' X' hX'.1, fun Y hY => ?_⟩
    have h1 := hX'.2 _ hX0'
    rw [hcf, hcf, Finset.sdiff_union_of_subset hRX0] at h1
    linarith [hX0.2 Y hY]
  refine ⟨fun X' hX' Y' hY' => ?_, ?_, ?_⟩
  · rw [hcf, hcf, hcf, hcf]
    have e1 : X' ∪ Y' ∪ Rw = (X' ∪ Rw) ∪ (Y' ∪ Rw) := by
      ext; simp only [Finset.mem_union]; tauto
    have e2 : X' ∩ Y' ∪ Rw = (X' ∪ Rw) ∩ (Y' ∪ Rw) := by
      ext; simp only [Finset.mem_union, Finset.mem_inter]; tauto
    rw [e1, e2]
    linarith [hG.sub _ (hsub' X' hX') _ (hsub' Y' hY')]
  · rw [hcf, Finset.empty_union]; ring
  · intro e he X' hX' hx
    obtain ⟨he, _, h2⟩ := (harc e).mp he
    have := hG.compat e he _ (hmin X' hX') (Finset.mem_union_left _ hx)
    rcases Finset.mem_union.mp this with h | h
    · exact h
    · exact absurd h h2

theorem inner_step (V : Finset (Finset (Fin n))) (f : Finset (Finset (Fin n)) → ℝ)
    (hsub : SubmodularOn V f) (hf0 : f ∅ = 0) (κ : ℝ) (ph ph' : PhaseState (Finset (Fin n)))
    (hI : PhaseInv V ph) (h : FixInnerStep f V κ ph ph') : PhaseInv V ph' := by
  rcases h with ⟨⟨_, rfl⟩, _⟩ | h | h
  · exact clip_inv V ph hI
  · have hV : V.Nonempty := by
      obtain ⟨_, _, _, i, L, lam, u, v, _, hact, _, _⟩ := h
      obtain ⟨p, _, hv, _⟩ := hact
      exact ⟨v, hv⟩
    exact (X5IW.push_step V hV f hsub hf0 ph ph' hI h).1
  · exact (X5IW.aug_step V f ph ph' hI h).1

theorem step_ginv (s s' : MainState n) (hG : GInv s) (h : Step s s') : GInv s' := by
  rcases h with hfin | hcall | hfix | hret
  · obtain ⟨_, ⟨_, e⟩ | ⟨_, _, e⟩⟩ := hfin
    · subst e
      exact ⟨X5FC.inv_same _ _ hG.base rfl rfl rfl (by intro fr u η ph h; simp at h),
        hG.sub, hG.zero, hG.compat, by intro fr u η ph h; simp at h⟩
    · subst e
      obtain ⟨h1, h2, h3⟩ := cap_parts s hG
      exact ⟨X5FC.inv_same _ _ hG.base rfl rfl rfl (by intro fr u η ph h; simp at h),
        h1, h2, h3, by intro fr u η ph h; simp at h⟩
  · obtain ⟨_, _, hη, u, L, hu, _, rest⟩ := hcall
    simp only at rest
    obtain ⟨hL, _, e⟩ := rest
    subst e
    obtain ⟨h1, h2, h3⟩ := cap_parts s hG
    refine ⟨X5FC.inv_same _ _ hG.base rfl rfl rfl ?_, h1, h2, h3, ?_⟩
    · intro fr u' η ph h
      simp only [Mode.fix.injEq] at h
      rw [← h.2.1]; exact hu
    · intro fr u' η' ph h
      simp only [Mode.fix.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      refine ⟨hη, by simp [initPhase], ?_, by simp [initPhase], ?_, ?_⟩
      · intro p hp
        simp only [initPhase, List.mem_singleton] at hp
        subst hp
        exact ⟨hL, one_pos⟩
      · intro a _ b _; simp [initPhase]
      · intro a _ b _; simp only [initPhase]; constructor <;> linarith
  · obtain ⟨fr, u, η, ph, ph', hm, hstep, e⟩ := hfix
    subst e
    have hphase := hG.phase fr u η ph hm
    obtain ⟨hs', hz'⟩ := fix_sub s hG fr u
    have hnew := inner_step _ _ hs' hz' _ ph ph' hphase hstep
    refine ⟨X5FC.inv_same _ _ hG.base rfl rfl rfl ?_, hG.sub, hG.zero, hG.compat, ?_⟩
    · intro fr' u' η' ph'' h
      simp only [Mode.fix.injEq] at h
      rw [← h.2.1]; exact hG.base.fixu fr u η ph hm
    · intro fr' u' η' ph'' h
      simp only [Mode.fix.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact hnew
  · have hI' := (X5FC.return_step s s' hG.base hret).1
    obtain ⟨fr, u, η, ph, w, hm, hout, hcase⟩ := hret
    obtain ⟨hF1, hF2⟩ := return_facts s hG fr u η ph hm w hout
    have hu : u ∈ s.blocks := hG.base.fixu fr u η ph hm
    rcases hcase with ⟨hfr, huw, rfl⟩ | ⟨hfr, huw, rfl⟩ | ⟨hfr, rfl⟩
    · obtain ⟨hwV, hcomp⟩ := hF1 hfr
      rw [Finset.mem_sdiff] at hwV
      have hparts := contract_parts s (s.contract u w) hG hI'
        ((s.R w).filter (fun v => u ∈ s.R v))
        (fun X hX => R_sub s w (Finset.mem_filter.mp hX).1)
        ⟨w, Finset.mem_filter.mpr ⟨R_self s w hwV.1, huw⟩⟩
        (fun X => by
          unfold MainState.contract
          simp only [Finset.mem_insert, Finset.mem_sdiff])
        (fun x y => by
          unfold MainState.contract
          simp only [Finset.mem_filter, Finset.mem_image, Prod.mk.injEq, Prod.exists]
          tauto)
        rfl
        (fun X hX => by
          by_cases hc : ∃ v ∈ (s.R w).filter (fun v => u ∈ s.R v), v ∈ X
          · left
            obtain ⟨v, hv, hvX⟩ := hc
            have huX : u ∈ X := closure s hG X hX v hvX (Finset.mem_filter.mp hv).2
            have hwX : w ∈ X := hcomp X hX huX
            intro c hc'
            exact closure s hG X hX w hwX (Finset.mem_filter.mp hc').1
          · right
            rw [Finset.disjoint_left]
            intro c hc' hcX
            exact hc ⟨c, hc', hcX⟩)
      exact ⟨hI', hparts.1, hparts.2.1, hparts.2.2,
        by intro fr' u' η' ph' h; simp [MainState.contract] at h⟩
    · refine ⟨hI', hG.sub, hG.zero, ?_, by intro fr' u' η' ph' h; simp [MainState.addArc] at h⟩
      intro e he
      simp only [MainState.addArc, Finset.mem_insert] at he
      rcases he with rfl | he
      · exact (hF1 hfr).2
      · exact hG.compat e he
    · have hparts := delete_parts s (s.delete w) hG (s.R w) (R_sub s w)
        (fun X => by unfold MainState.delete; simp only [Finset.mem_sdiff])
        (fun e => by unfold MainState.delete; simp only [Finset.mem_filter])
        rfl
        (fun X hX => (hF2 hfr X hX).2)
      exact ⟨hI', hparts.1, hparts.2.1, hparts.2.2,
        by intro fr' u' η' ph' h; simp [MainState.delete] at h⟩

theorem init_ginv (f : Finset (Fin n) → ℝ) (hsub : SubmodularOn Finset.univ f) (hf0 : f ∅ = 0) :
    GInv (initMain f) := by
  have hI := X5FC.init_inv f
  refine ⟨hI, ?_, ?_, ?_, ?_⟩
  · intro X hX Y hY
    show f ((X ∪ Y).biUnion id) + f ((X ∩ Y).biUnion id) ≤ f (X.biUnion id) + f (Y.biUnion id)
    rw [Finset.union_biUnion, biU_inter _ hI.disj X Y hX hY]
    exact hsub _ (Finset.subset_univ _) _ (Finset.subset_univ _)
  · show f ((∅ : Finset (Finset (Fin n))).biUnion id) = 0
    simpa using hf0
  · intro e he; simp [initMain] at he
  · intro fr u η ph h; simp [initMain] at h

theorem reach_ginv (f : Finset (Fin n) → ℝ) (hsub : SubmodularOn Finset.univ f) (hf0 : f ∅ = 0)
    (s : MainState n) (hs : Relation.ReflTransGen Step (initMain f) s) : GInv s := by
  induction hs with
  | refl => exact init_ginv f hsub hf0
  | tail _ hst ih => exact step_ginv _ _ ih hst

end X5TC




open IwataFF.SFM MainState

namespace IFA

section Gen
variable {β : Type} [DecidableEq β]

/-- the arc relation of a finite set of arcs -/
def ar (F : Finset (β × β)) : β → β → Prop := fun a c => (a, c) ∈ F

theorem rtg_mono {F G : Finset (β × β)} (h : F ⊆ G) {x y : β}
    (hr : Relation.ReflTransGen (ar F) x y) : Relation.ReflTransGen (ar G) x y := by
  induction hr with
  | refl => exact .refl
  | tail _ hbc ih => exact ih.tail (h hbc)

/-- last-use decomposition of a path in `F ∪ {(u, w)}`. -/
theorem rtg_insert (F : Finset (β × β)) (u w x y : β)
    (h : Relation.ReflTransGen (ar (insert (u, w) F)) x y) :
    Relation.ReflTransGen (ar F) x y ∨
      (Relation.ReflTransGen (ar F) x u ∧ Relation.ReflTransGen (ar F) w y) := by
  induction h with
  | refl => left; exact Relation.ReflTransGen.refl
  | @tail c y _ hcy ih =>
    have hcy' : (c, y) = (u, w) ∨ (c, y) ∈ F := Finset.mem_insert.mp hcy
    rcases hcy' with e | hF
    · simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      rcases ih with h1 | ⟨h1, _⟩
      · right; exact ⟨h1, Relation.ReflTransGen.refl⟩
      · right; exact ⟨h1, Relation.ReflTransGen.refl⟩
    · rcases ih with h1 | ⟨h1, h2⟩
      · left; exact h1.tail hF
      · right; exact ⟨h1, h2.tail hF⟩

def AcycF (F : Finset (β × β)) : Prop := ∀ e ∈ F, ¬ Relation.ReflTransGen (ar F) e.2 e.1

theorem acyc_insert (F : Finset (β × β)) (hF : AcycF F) (u w : β)
    (hwu : ¬ Relation.ReflTransGen (ar F) w u) : AcycF (insert (u, w) F) := by
  intro e he hr
  rcases rtg_insert F u w _ _ hr with h | ⟨h1, h2⟩
  · rcases Finset.mem_insert.mp he with rfl | he
    · exact hwu h
    · exact hF e he h
  · rcases Finset.mem_insert.mp he with rfl | he
    · exact hwu h2
    · exact hwu ((h2.tail he).trans h1)

theorem acyc_sub (F G : Finset (β × β)) (hF : AcycF F) (hGF : G ⊆ F) : AcycF G := by
  intro e he hr
  exact hF e (hGF he) (rtg_mono hGF hr)

/-- an acyclic digraph has a consistent linear ordering of every finite vertex set. -/
theorem exists_consistent (F : Finset (β × β)) (hF : AcycF F) :
    ∀ W : Finset β, ∃ L : List β, IsOrdering W L ∧ IsConsistent F L := by
  intro W
  induction W using Finset.strongInduction with
  | H W ih =>
    rcases W.eq_empty_or_nonempty with rfl | hne
    · refine ⟨[], ⟨List.nodup_nil, fun a => by simp⟩, ?_⟩
      intro i j _ a b ha; simp at ha
    · classical
      obtain ⟨v, hvW, hmin⟩ := Finset.exists_min_image W
        (fun v => (W.filter (fun b => Relation.ReflTransGen (ar F) v b)).card) hne
      obtain ⟨L', hL', hc'⟩ := ih (W.erase v) (Finset.erase_ssubset hvW)
      refine ⟨v :: L', ⟨?_, fun a => ?_⟩, ?_⟩
      · refine List.nodup_cons.mpr ⟨fun h => ?_, hL'.1⟩
        have := (hL'.2 v).mp h; simp at this
      · rw [List.mem_cons, hL'.2 a, Finset.mem_erase]
        constructor
        · intro h
          rcases h with h | h
          · rw [h]; exact hvW
          · exact h.2
        · intro h; by_cases e : a = v
          · exact Or.inl e
          · exact Or.inr ⟨e, h⟩
      · intro i j hij a b ha hb hab
        cases i with
        | zero =>
          cases j with
          | zero => omega
          | succ j =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at ha
            subst ha
            simp only [List.getElem?_cons_succ] at hb
            have hbL : b ∈ L' := List.mem_of_getElem? hb
            have hbW := (hL'.2 b).mp hbL
            rw [Finset.mem_erase] at hbW
            have h1 := hmin b hbW.2
            have hsub : W.filter (fun c => Relation.ReflTransGen (ar F) b c) ⊂
                W.filter (fun c => Relation.ReflTransGen (ar F) v c) := by
              rw [Finset.ssubset_iff_of_subset]
              · refine ⟨v, Finset.mem_filter.mpr ⟨hvW, Relation.ReflTransGen.refl⟩, ?_⟩
                intro h
                exact hF (v, b) hab (Finset.mem_filter.mp h).2
              · intro c hc
                rw [Finset.mem_filter] at hc ⊢
                exact ⟨hc.1, (Relation.ReflTransGen.single hab).trans hc.2⟩
            have := Finset.card_lt_card hsub
            omega
        | succ i =>
          cases j with
          | zero => omega
          | succ j =>
            simp only [List.getElem?_cons_succ] at ha hb
            exact hc' i j (by omega) a b ha hb hab

end Gen

variable {n : ℕ}

def Acyc (s : MainState n) : Prop := AcycF s.arcs

theorem mem_R (s : MainState n) (v b : Finset (Fin n)) :
    b ∈ s.R v ↔ b ∈ s.blocks ∧ Relation.ReflTransGen (ar s.arcs) v b := by
  unfold MainState.R; rw [X5FC.mem_reach]; rfl

/-- acyclicity after contraction (Figure 3). -/
theorem acyc_contract (s : MainState n) (hI : X5FC.Inv s) (hA : Acyc s)
    (u w : Finset (Fin n)) (hu : u ∈ s.blocks) (hw : w ∈ s.blocks) (huw : u ∈ s.R w) :
    Acyc (s.contract u w) := by
  classical
  set C := (s.R w).filter (fun v => u ∈ s.R v) with hC
  set B := C.biUnion id with hB
  set m : Finset (Fin n) → Finset (Fin n) := fun b => if b ∈ C then B else b with hm
  have hCb : C ⊆ s.blocks := fun X hX => ((mem_R s w X).mp (Finset.mem_filter.mp hX).1).1
  have hDB : ∀ D ∈ s.blocks, D ∉ C → D ≠ B := by
    intro D hD hDC e
    have hwC : w ∈ C := Finset.mem_filter.mpr ⟨(mem_R s w w).mpr ⟨hw, .refl⟩, huw⟩
    obtain ⟨a, ha⟩ := hI.ne w hw
    have hcD : w ≠ D := fun e' => hDC (e' ▸ hwC)
    have : a ∈ D := by rw [e]; exact Finset.mem_biUnion.mpr ⟨w, hwC, ha⟩
    exact Finset.disjoint_left.mp (hI.disj w hw D hD hcD) ha this
  have harcs : (s.contract u w).arcs =
      (s.arcs.image (fun e => (m e.1, m e.2))).filter (fun e => e.1 ≠ e.2) := rfl
  -- the old relation with jumps inside `C`
  let G : Finset (Fin n) → Finset (Fin n) → Prop := fun a b => (a, b) ∈ s.arcs ∨ (a ∈ C ∧ b ∈ C)
  have hsame : ∀ a0 a, a0 ∈ s.blocks → a ∈ s.blocks → m a0 = m a →
      Relation.ReflTransGen G a0 a := by
    intro a0 a h0 h1 e
    by_cases c0 : a0 ∈ C <;> by_cases c1 : a ∈ C
    · exact Relation.ReflTransGen.single (Or.inr ⟨c0, c1⟩)
    · simp only [hm, if_pos c0, if_neg c1] at e
      exact absurd e.symm (hDB a h1 c1)
    · simp only [hm, if_neg c0, if_pos c1] at e
      exact absurd e (hDB a0 h0 c0)
    · simp only [hm, if_neg c0, if_neg c1] at e
      rw [e]
  have hlift : ∀ x y, Relation.ReflTransGen (ar (s.contract u w).arcs) x y →
      ∀ a0 ∈ s.blocks, m a0 = x → ∃ b0 ∈ s.blocks, m b0 = y ∧ Relation.ReflTransGen G a0 b0 := by
    intro x y h
    induction h with
    | refl => intro a0 ha0 e; exact ⟨a0, ha0, e, .refl⟩
    | tail _ hcy ih =>
      intro a0 ha0 e
      obtain ⟨c0, hc0, ec, hr⟩ := ih a0 ha0 e
      have hcy' := hcy
      unfold ar at hcy'
      rw [harcs, Finset.mem_filter, Finset.mem_image] at hcy'
      obtain ⟨⟨⟨a, b⟩, hab, eab⟩, _⟩ := hcy'
      simp only [Prod.mk.injEq] at eab
      have hab' := hI.arcs _ hab
      refine ⟨b, hab'.2, eab.2, ?_⟩
      have h1 := hsame c0 a hc0 hab'.1 (by rw [ec, eab.1])
      exact (hr.trans h1).tail (Or.inl hab)
  -- G-paths are paths in F ∪ {(u, w)}
  have hGF : ∀ a b, Relation.ReflTransGen G a b →
      Relation.ReflTransGen (ar (insert (u, w) s.arcs)) a b := by
    intro a b h
    induction h with
    | refl => exact .refl
    | @tail c d _ hst ih =>
      rcases hst with h | ⟨hc, hd⟩
      · exact ih.tail (Finset.mem_insert_of_mem h)
      · have h1 : Relation.ReflTransGen (ar s.arcs) c u :=
          ((mem_R s c u).mp (Finset.mem_filter.mp hc).2).2
        have h2 : Relation.ReflTransGen (ar s.arcs) w d :=
          ((mem_R s w d).mp (Finset.mem_filter.mp hd).1).2
        refine ih.trans ((rtg_mono (Finset.subset_insert _ _) h1).trans ?_)
        exact Relation.ReflTransGen.head (Finset.mem_insert_self _ _)
          (rtg_mono (Finset.subset_insert _ _) h2)
  intro e he hr
  have he' := he
  rw [harcs, Finset.mem_filter, Finset.mem_image] at he'
  obtain ⟨⟨⟨a, b⟩, hab, eab⟩, hne⟩ := he'
  have hab' := hI.arcs _ hab
  rw [← eab] at hr hne
  simp only at hr hne
  obtain ⟨a', ha', ea', hr'⟩ := hlift _ _ hr b hab'.2 rfl
  have h1 := hsame a' a ha' hab'.1 ea'
  have hba := hGF _ _ (hr'.trans h1)
  rcases rtg_insert s.arcs u w b a hba with h | ⟨hbu, hwa⟩
  · exact hA (a, b) hab h
  · have hau : Relation.ReflTransGen (ar s.arcs) a u := Relation.ReflTransGen.head hab hbu
    have hwb : Relation.ReflTransGen (ar s.arcs) w b := hwa.tail hab
    have haC : a ∈ C := Finset.mem_filter.mpr ⟨(mem_R s w a).mpr ⟨hab'.1, hwa⟩,
      (mem_R s a u).mpr ⟨hu, hau⟩⟩
    have hbC : b ∈ C := Finset.mem_filter.mpr ⟨(mem_R s w b).mpr ⟨hab'.2, hwb⟩,
      (mem_R s b u).mpr ⟨hu, hbu⟩⟩
    apply hne
    simp only [hm, if_pos haC, if_pos hbC]

theorem acyc_addArc (s : MainState n) (hA : Acyc s) (u w : Finset (Fin n)) (hu : u ∈ s.blocks)
    (huw : u ∉ s.R w) : Acyc (s.addArc u w) := by
  apply acyc_insert s.arcs hA u w
  intro h; exact huw ((mem_R s w u).mpr ⟨hu, h⟩)

theorem acyc_delete (s : MainState n) (hA : Acyc s) (w : Finset (Fin n)) :
    Acyc (s.delete w) := by
  apply acyc_sub s.arcs _ hA
  intro e he
  unfold MainState.delete at he
  exact (Finset.mem_filter.mp he).1

end IFA



open IwataFF.SFM MainState

namespace IFP

section Gen
variable {β : Type} [DecidableEq β]

/-- a reflexive-transitive path can be shortened to a duplicate-free chain. -/
theorem nodup_path (r : β → β → Prop) (a b : β) (h : Relation.ReflTransGen r a b) :
    ∃ P : List β, P.Nodup ∧ P.head? = some a ∧ P.getLast? = some b ∧ P.IsChain r := by
  induction h with
  | refl => exact ⟨[a], List.nodup_singleton a, rfl, rfl, List.isChain_singleton a⟩
  | @tail c d _ hcd ih =>
    obtain ⟨P, hnd, hh, hl, hc⟩ := ih
    by_cases hdP : d ∈ P
    · refine ⟨P.take (P.idxOf d + 1), hnd.sublist (List.take_sublist _ _), ?_, ?_, hc.take _⟩
      · rw [List.head?_take]; simp [hh]
      · have hlt : P.idxOf d < P.length := List.idxOf_lt_length_iff.mpr hdP
        rw [List.getLast?_take]
        simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
        rw [List.getElem?_eq_getElem hlt, List.getElem_idxOf hlt]; rfl
    · refine ⟨P ++ [d], ?_, ?_, ?_, ?_⟩
      · rw [List.nodup_append]
        refine ⟨hnd, List.nodup_singleton d, ?_⟩
        intro x hx y hy; rw [List.mem_singleton] at hy; subst hy; rintro rfl; exact hdP hx
      · rw [List.head?_append, hh]; rfl
      · simp
      · apply hc.append (List.isChain_singleton d)
        intro x hx y hy
        rw [hl] at hx; cases hx
        simp at hy; subst hy; exact hcd

end Gen

variable {α : Type} [DecidableEq α]

/-- existence of the reduction of the convex combination (Carathéodory). -/
theorem exists_reduce (f : Finset α → ℝ) (st : PhaseState α)
    (hpos : ∀ p ∈ st.idx, 0 < p.2) (hsum : (st.idx.map Prod.snd).sum = 1) :
    ∃ st', Reduces f st st' := by
  classical
  set len := st.idx.length
  set P : Fin len → (α → ℝ) := fun k => greedy f (st.idx.get k).1 with hP
  have hx : xOf f st = ∑ k : Fin len, (st.idx.get k).2 • P k := by
    funext a
    rw [Finset.sum_apply]
    unfold xOf
    simp only [Pi.smul_apply, smul_eq_mul, hP, List.get_eq_getElem]
    exact (Fin.sum_univ_fun_getElem st.idx (fun p => p.2 * greedy f p.1 a)).symm
  have hmem : xOf f st ∈ convexHull ℝ (Set.range P) := by
    rw [hx]
    apply (convex_convexHull ℝ _).sum_mem
    · intro k _; exact (hpos _ (List.get_mem _ _)).le
    · rw [← hsum]
      simp only [List.get_eq_getElem]
      exact Fin.sum_univ_fun_getElem st.idx Prod.snd
    · intro k _; exact subset_convexHull ℝ _ ⟨k, rfl⟩
  obtain ⟨ι, _, z, w, hzr, hzai, hwpos, hw1, hwx⟩ := eq_pos_convex_span_of_mem_convexHull hmem
  have hzinj : Function.Injective z := hzai.injective
  have hj : ∀ i, ∃ k, P k = z i := fun i => hzr ⟨i, rfl⟩
  choose j hjz using hj
  have hjinj : Function.Injective j := by
    intro i1 i2 e; apply hzinj; rw [← hjz, ← hjz, e]
  set J : Finset (Fin len) := Finset.univ.image j with hJ
  have hinv : ∀ k ∈ J, ∃ i, j i = k := by
    intro k hk; obtain ⟨i, _, e⟩ := Finset.mem_image.mp hk; exact ⟨i, e⟩
  set W : Fin len → ℝ := fun k => ∑ i, if j i = k then w i else 0 with hW
  have hWj : ∀ i, W (j i) = w i := by
    intro i
    simp only [hW]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb; rw [if_neg (fun e => hb (hjinj e))]
    · intro h; exact absurd (Finset.mem_univ i) h
  set ks : List (Fin len) := (List.finRange len).filter (fun k => decide (k ∈ J)) with hks
  have hksnd : ks.Nodup := (List.nodup_finRange len).filter _
  have hksJ : ks.toFinset = J := by
    ext k; simp [hks]
  -- sums over `J` are sums over `ι`
  have hsumJ : ∀ g : Fin len → ℝ, ∑ k ∈ J, W k * g k = ∑ i, w i * g (j i) := by
    intro g
    rw [hJ, Finset.sum_image (fun a _ b _ e => hjinj e)]
    apply Finset.sum_congr rfl; intro i _; rw [hWj]
  set idx' : List (List α × ℝ) := ks.map (fun k => ((st.idx.get k).1, W k)) with hidx'
  refine ⟨⟨idx', st.phi, st.delta, st.begun⟩, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · -- sublist
    simp only [hidx', List.map_map]
    have : st.idx.map Prod.fst = (List.finRange len).map (fun k => (st.idx.get k).1) := by
      conv_lhs => rw [← List.map_get_finRange st.idx]
      rw [List.map_map]; rfl
    rw [this]
    exact (List.filter_sublist).map _
  · intro p hp
    simp only [hidx', List.mem_map] at hp
    obtain ⟨k, hk, rfl⟩ := hp
    have hkJ : k ∈ J := by simpa [hks] using hk
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hkJ
    simp only; rw [hWj]; exact hwpos i
  · simp only [hidx', List.map_map]
    have : ((fun p : List α × ℝ => p.2) ∘ fun k => ((st.idx.get k).1, W k)) = W := rfl
    rw [this, ← List.sum_toFinset W hksnd, hksJ]
    have := hsumJ (fun _ => 1)
    simp only [mul_one] at this
    rw [this, hw1]
  · funext a
    have h1 := congrFun hwx a
    rw [Finset.sum_apply] at h1
    simp only [Pi.smul_apply, smul_eq_mul] at h1
    unfold xOf
    simp only [hidx', List.map_map]
    have : ((fun p : List α × ℝ => p.2 * greedy f p.1 a) ∘ fun k => ((st.idx.get k).1, W k)) =
        fun k => W k * P k a := rfl
    rw [this, ← List.sum_toFinset _ hksnd, hksJ, hsumJ (fun k => P k a)]
    have h2 : (st.idx.map (fun p => p.2 * greedy f p.1 a)).sum = xOf f st a := rfl
    rw [h2, ← h1]
    apply Finset.sum_congr rfl; intro i _; rw [hjz]
  · -- affine independence
    set q : Fin idx'.length → (α → ℝ) := fun t => greedy f (idx'.get t).1 with hq
    have hlen : idx'.length = ks.length := by simp [hidx']
    have hqk : ∀ t : Fin idx'.length, q t = P (ks.get (Fin.cast hlen t)) := by
      intro t; simp [hq, hidx', hP]
    have hPinj : ∀ k1 ∈ J, ∀ k2 ∈ J, P k1 = P k2 → k1 = k2 := by
      intro k1 h1 k2 h2 e
      obtain ⟨i1, _, rfl⟩ := Finset.mem_image.mp h1
      obtain ⟨i2, _, rfl⟩ := Finset.mem_image.mp h2
      rw [hjz, hjz] at e; rw [hzinj e]
    have hksmem : ∀ t : Fin ks.length, ks.get t ∈ J := by
      intro t
      have : ks.get t ∈ ks := List.get_mem _ _
      have := (List.mem_filter.mp this).2
      simpa using this
    have hqinj : Function.Injective q := by
      intro t1 t2 e
      rw [hqk, hqk] at e
      have := hPinj _ (hksmem _) _ (hksmem _) e
      have := (List.Nodup.get_inj_iff hksnd).mp this
      exact Fin.cast_injective hlen this
    apply AffineIndependent.of_set_of_injective _ hqinj
    apply hzai.range.mono
    rintro _ ⟨t, rfl⟩
    rw [hqk]
    obtain ⟨i, _, e⟩ := Finset.mem_image.mp (hksmem (Fin.cast hlen t))
    rw [← e, hjz]; exact ⟨i, rfl⟩


theorem exists_aug (f : Finset α → ℝ) (V : Finset α) (st : PhaseState α) (hinv : PhaseInv V st)
    (hb : st.begun = true) (hg : Guard f V st) (hwt : (Wset f V st ∩ Tset f V st).Nonempty) :
    ∃ st', AugStep f V st st' := by
  obtain ⟨t, ht⟩ := hwt
  rw [Finset.mem_inter] at ht
  have htW := ht.1
  simp only [Wset, Finset.mem_filter] at htW
  obtain ⟨_, s, hs, hr⟩ := htW
  obtain ⟨P, hnd, hh, hl, hc⟩ := nodup_path _ _ _ hr
  obtain ⟨_, _, hord, hsum, _, _⟩ := hinv
  obtain ⟨st', hred⟩ := exists_reduce f { st with phi := augPhi st.phi st.delta P }
    (fun p hp => (hord p hp).2) hsum
  exact ⟨st', hb, hg, ⟨t, Finset.mem_inter.mpr ht⟩, P, ⟨hnd, ⟨s, hh, hs⟩, ⟨t, hl, ht.2⟩, hc⟩, hred⟩

theorem exists_push (f : Finset α → ℝ) (V : Finset α) (st : PhaseState α) (hinv : PhaseInv V st)
    (hb : st.begun = true) (hg : Guard f V st) (hwt : Wset f V st ∩ Tset f V st = ∅)
    (hz : ZNonempty f V st) : ∃ st', PushStep f V st st' := by
  obtain ⟨i, v, hact⟩ := hz
  have hact' := hact
  obtain ⟨p, hp, hvV, _, ⟨w, hw⟩, _⟩ := hact'
  obtain ⟨L, lam⟩ := p
  obtain ⟨_, _, hord, _, _, _⟩ := hinv
  have hL := (hord _ (X5IW.mem_of_getElem? hp)).1
  simp only at hw
  rw [Finset.mem_sdiff] at hw
  have hwV : w ∈ V := by
    have := hw.1; simp only [Wset, Finset.mem_filter] at this; exact this.1
  have hwL : w ∈ L := (hL.2 w).mpr hwV
  have hvL : v ∈ L := (hL.2 v).mpr hvV
  have hlt : L.idxOf v + 1 < L.length := by
    have h1 : w ∉ L.take (L.idxOf v + 1) := by
      intro h; apply hw.2; unfold prefixSet; exact List.mem_toFinset.mpr h
    rw [List.mem_take_iff_idxOf_lt hwL] at h1
    have := List.idxOf_lt_length_iff.mpr hwL
    omega
  refine ⟨pushResult f V st i L lam L[L.idxOf v + 1] v, hb, hg, hwt, i, L, lam,
    L[L.idxOf v + 1], v, hp, hact, ⟨hvL, List.getElem?_eq_getElem hlt⟩, rfl⟩

/-- `Fix` can return: some `w ∈ Y` has `x(w) < −n²δ` once `δ < κ/n³` and `f(Y) ≤ −κ`. -/
theorem exists_output (f : Finset α → ℝ) (V : Finset α) (hsub : SubmodularOn V f) (hf0 : f ∅ = 0)
    (κ : ℝ) (hκ : 0 < κ) (Y : Finset α) (hY : Y ⊆ V) (hfY : f Y ≤ -κ)
    (st : PhaseState α) (hinv : PhaseInv V st) (hb : st.begun = true) (hend : PhaseEnd f V st)
    (hδ : st.delta < κ / (V.card : ℝ) ^ 3) : ∃ w, FixOutput f V κ st w := by
  obtain ⟨hδ0, _, hord, hsum, _, _⟩ := hinv
  have hx := X5IW.xOf_base V f hsub hf0 st hord hsum
  have hxY := hx.2.2 Y hY
  unfold xsum at hxY
  have hYne : Y.Nonempty := by
    rcases Y.eq_empty_or_nonempty with rfl | h
    · rw [hf0] at hfY; linarith
    · exact h
  have hYc : (0 : ℝ) < Y.card := by exact_mod_cast hYne.card_pos
  have hVc : (Y.card : ℝ) ≤ V.card := by exact_mod_cast Finset.card_le_card hY
  have hVc0 : (0 : ℝ) < V.card := lt_of_lt_of_le hYc hVc
  obtain ⟨w, hwY, hw⟩ := Finset.exists_le_of_sum_le hYne
    (show ∑ y ∈ Y, xOf f st y ≤ ∑ y ∈ Y, (-κ / Y.card) by
      rw [Finset.sum_const, nsmul_eq_mul]; field_simp; linarith)
  refine ⟨w, hb, hend, hδ, hY hwY, ?_⟩
  have h1 : -κ / (Y.card : ℝ) ≤ -κ / V.card := by
    rw [div_le_div_iff₀ hYc hVc0]; nlinarith
  have h2 : (V.card : ℝ) ^ 2 * st.delta < κ / V.card := by
    rw [lt_div_iff₀ hVc0]
    have := (lt_div_iff₀ (by positivity : (0:ℝ) < (V.card : ℝ) ^ 3)).mp hδ
    nlinarith
  have h3 : -κ / (V.card : ℝ) = -(κ / V.card) := by ring
  linarith


theorem phaseEnd_of_not_guard (f : Finset α → ℝ) (V : Finset α) (st : PhaseState α)
    (h : ¬ Guard f V st) : PhaseEnd f V st := by
  unfold PhaseEnd
  rcases (Sset f V st).eq_empty_or_nonempty with h1 | h1
  · left; exact h1
  rcases (Tset f V st).eq_empty_or_nonempty with h2 | h2
  · right; left; exact h2
  right; right
  refine ⟨fun hz => h ⟨h1, h2, Or.inl hz⟩, ?_⟩
  rw [← Finset.not_nonempty_iff_eq_empty]
  exact fun hwt => h ⟨h1, h2, Or.inr hwt⟩

end IFP

namespace IFP

variable {n : ℕ}

/-- the data recorded when `Fix` is called (Figure 3, (4.1) and the cap). -/
def FixInfo (s : MainState n) : Prop :=
  ∀ fr u η ph, s.mode = Mode.fix fr u η ph →
    0 < η ∧ s.curFun (s.R u) - s.curFun ((s.R u).erase u) = η ∧
      fr = decide (η / 2 ≤ s.curFun (s.R u)) ∧ s.curFun s.blocks ≤ 0

structure PInv (s : MainState n) : Prop where
  g : X5TC.GInv s
  acyc : IFA.Acyc s
  fi : FixInfo s

theorem cap_top_le (s : MainState n) : s.cap.curFun s.cap.blocks ≤ 0 := by
  show (if s.blocks.biUnion id = s.blocks.biUnion id ∧ 0 < s.h (s.blocks.biUnion id) then 0
    else s.h (s.blocks.biUnion id)) ≤ 0
  split_ifs with h
  · exact le_rfl
  · push_neg at h; exact h rfl

theorem step_pinv (s s' : MainState n) (hP : PInv s) (h : Step s s') : PInv s' := by
  have hg' := X5TC.step_ginv s s' hP.g h
  rcases h with hfin | hcall | hfix | hret
  · obtain ⟨_, ⟨_, e⟩ | ⟨_, _, e⟩⟩ := hfin
    · subst e
      exact ⟨hg', hP.acyc, by intro fr u η ph h; simp at h⟩
    · subst e
      exact ⟨hg', hP.acyc, by intro fr u η ph h; simp at h⟩
  · obtain ⟨_, _, hη, u, L, hu, hmax, rest⟩ := hcall
    simp only at rest
    obtain ⟨_, _, e⟩ := rest
    subst e
    refine ⟨hg', hP.acyc, ?_⟩
    intro fr u' η' ph h
    simp only [Mode.fix.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact ⟨hη, hmax, rfl, cap_top_le s⟩
  · obtain ⟨fr, u, η, ph, ph', hm, _, e⟩ := hfix
    subst e
    refine ⟨hg', hP.acyc, ?_⟩
    intro fr' u' η' ph'' h
    simp only [Mode.fix.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact hP.fi fr u η ph hm
  · obtain ⟨fr, u, η, ph, w, hm, hout, hcase⟩ := hret
    have hu : u ∈ s.blocks := hP.g.base.fixu fr u η ph hm
    have hwG : w ∈ s.fixGround fr u := hout.2.2.2.1
    rcases hcase with ⟨hfr, huw, rfl⟩ | ⟨hfr, huw, rfl⟩ | ⟨hfr, rfl⟩
    · subst hfr
      have hwG' : w ∈ s.blocks \ s.R u := by simpa [MainState.fixGround] using hwG
      refine ⟨hg', IFA.acyc_contract s hP.g.base hP.acyc u w hu (Finset.mem_sdiff.mp hwG').1 huw,
        by intro fr u η ph h; simp [MainState.contract] at h⟩
    · exact ⟨hg', IFA.acyc_addArc s hP.acyc u w hu huw,
        by intro fr u η ph h; simp [MainState.addArc] at h⟩
    · exact ⟨hg', IFA.acyc_delete s hP.acyc w,
        by intro fr u η ph h; simp [MainState.delete] at h⟩

theorem reach_pinv (f : Finset (Fin n) → ℝ) (hsub : SubmodularOn Finset.univ f) (hf0 : f ∅ = 0)
    (s : MainState n) (hs : Relation.ReflTransGen Step (initMain f) s) : PInv s := by
  induction hs with
  | refl =>
    refine ⟨X5TC.init_ginv f hsub hf0, ?_, by intro fr u η ph h; simp [initMain] at h⟩
    intro e he; simp [initMain] at he
  | tail _ hst ih => exact step_pinv _ _ ih hst

/-- Progress: every reachable non-final state of Figure 3 has a successor. -/
theorem progress {n : ℕ} (f : Finset (Fin n) → ℝ)
    (hsub : SubmodularOn Finset.univ f) (hf0 : f ∅ = 0)
    (s : MainState n) (hs : Relation.ReflTransGen Step (initMain f) s) (hnf : ¬ IsFinal s) :
    ∃ s', Step s s' := by
  have hP := reach_pinv f hsub hf0 s hs
  cases hm : s.mode with
  | done X => exact absurd ⟨X, hm⟩ hnf
  | loop =>
    rcases s.blocks.eq_empty_or_nonempty with hb | hne
    · exact ⟨_, Or.inl ⟨hm, Or.inl ⟨hb, rfl⟩⟩⟩
    by_cases hη : etaVal s.cap.blocks s.cap.arcs s.cap.curFun ≤ 0
    · exact ⟨_, Or.inl ⟨hm, Or.inr ⟨hne, hη, rfl⟩⟩⟩
    push_neg at hη
    have hne' : s.cap.blocks.Nonempty := hne
    obtain ⟨u, hu, heq⟩ := Finset.exists_mem_eq_sup' hne'
      (fun v => s.cap.curFun (reach s.cap.blocks s.cap.arcs v) -
        s.cap.curFun ((reach s.cap.blocks s.cap.arcs v).erase v))
    have hη' : etaVal s.cap.blocks s.cap.arcs s.cap.curFun =
        s.cap.curFun (s.cap.R u) - s.cap.curFun ((s.cap.R u).erase u) := by
      unfold etaVal; rw [dif_pos hne', heq]; rfl
    obtain ⟨L, hL, hc⟩ := IFA.exists_consistent s.arcs hP.acyc
      (s.cap.fixGround (decide (etaVal s.cap.blocks s.cap.arcs s.cap.curFun / 2 ≤
        s.cap.curFun (s.cap.R u))) u)
    exact ⟨_, Or.inr (Or.inl ⟨hm, hne, hη, u, L, hu, hη'.symm, hL, hc, rfl⟩)⟩
  | fix fr u η ph =>
    obtain ⟨hη, hRu, hfr, htop⟩ := hP.fi fr u η ph hm
    have hph := hP.g.phase fr u η ph hm
    obtain ⟨hsub', hz'⟩ := X5TC.fix_sub s hP.g fr u
    have huB := hP.g.base.fixu fr u η ph hm
    have hRb := X5TC.R_sub s u
    by_cases hbg : ph.begun = true
    · by_cases hg : Guard (s.fixFun fr u) (s.fixGround fr u) ph
      · by_cases hwt : (Wset (s.fixFun fr u) (s.fixGround fr u) ph ∩
            Tset (s.fixFun fr u) (s.fixGround fr u) ph).Nonempty
        · obtain ⟨ph', h'⟩ := exists_aug _ _ ph hph hbg hg hwt
          exact ⟨_, Or.inr (Or.inr (Or.inl ⟨fr, u, η, ph, ph', hm, Or.inr (Or.inr h'), rfl⟩))⟩
        · rw [Finset.not_nonempty_iff_eq_empty] at hwt
          have hz : ZNonempty (s.fixFun fr u) (s.fixGround fr u) ph := by
            rcases hg.2.2 with h | h
            · exact h
            · rw [hwt] at h; simp at h
          obtain ⟨ph', h'⟩ := exists_push _ _ ph hph hbg hg hwt hz
          exact ⟨_, Or.inr (Or.inr (Or.inl ⟨fr, u, η, ph, ph', hm, Or.inr (Or.inl h'), rfl⟩))⟩
      · have hend := phaseEnd_of_not_guard _ _ ph hg
        by_cases hδ : η / 2 / ((s.fixGround fr u).card : ℝ) ^ 3 ≤ ph.delta
        · exact ⟨_, Or.inr (Or.inr (Or.inl ⟨fr, u, η, ph, _, hm,
            Or.inl ⟨⟨Or.inr hend, rfl⟩, Or.inr hδ⟩, rfl⟩))⟩
        push_neg at hδ
        -- a set of value at most `-η/2`
        obtain ⟨Y, hY, hfY⟩ : ∃ Y ⊆ s.fixGround fr u, s.fixFun fr u Y ≤ -(η / 2) := by
          cases fr with
          | true =>
            refine ⟨s.blocks \ s.R u, by simp [MainState.fixGround], ?_⟩
            simp only [MainState.fixFun, ↓reduceIte, restrictFun]
            rw [Finset.sdiff_union_of_subset hRb]
            have : η / 2 ≤ s.curFun (s.R u) := by simpa using hfr.symm
            linarith
          | false =>
            refine ⟨(s.R u).erase u, ?_, ?_⟩
            · simp only [MainState.fixGround, Bool.false_eq_true, ↓reduceIte]
              exact (Finset.erase_subset _ _).trans hRb
            · simp only [MainState.fixFun, Bool.false_eq_true, ↓reduceIte]
              have : ¬ (η / 2 ≤ s.curFun (s.R u)) := by simpa using hfr.symm
              push_neg at this
              linarith
        obtain ⟨w, hw⟩ := exists_output _ _ hsub' hz' (η / 2) (by linarith) Y hY hfY ph hph
          hbg hend hδ
        cases fr with
        | true =>
          by_cases huw : u ∈ s.R w
          · exact ⟨_, Or.inr (Or.inr (Or.inr ⟨true, u, η, ph, w, hm, hw,
              Or.inl ⟨rfl, huw, rfl⟩⟩))⟩
          · exact ⟨_, Or.inr (Or.inr (Or.inr ⟨true, u, η, ph, w, hm, hw,
              Or.inr (Or.inl ⟨rfl, huw, rfl⟩)⟩))⟩
        | false =>
          exact ⟨_, Or.inr (Or.inr (Or.inr ⟨false, u, η, ph, w, hm, hw,
            Or.inr (Or.inr ⟨rfl, rfl⟩)⟩))⟩
    · have hb' : ph.begun = false := by simpa using hbg
      exact ⟨_, Or.inr (Or.inr (Or.inl ⟨fr, u, η, ph, _, hm,
        Or.inl ⟨⟨Or.inl hb', rfl⟩, Or.inl hb'⟩, rfl⟩))⟩

end IFP



open IwataFF.SFM MainState

namespace IFC

variable {n : ℕ}


/-- the invariant relating the current function to the original `f` (proof of Theorem 4.2). -/
structure Core (f : Finset (Fin n) → ℝ) (s : MainState n) : Prop where
  part : s.acc ∪ (Finset.biUnion s.blocks id) = Finset.univ
  exact : ∀ S ⊆ s.blocks, (Finset.biUnion S id) ≠ (Finset.biUnion s.blocks id) → s.h (Finset.biUnion S id) = f ((Finset.biUnion S id) ∪ s.acc) - f s.acc
  fake : s.h (Finset.biUnion s.blocks id) ≠ f Finset.univ - f s.acc →
    (∃ S ⊆ s.blocks, s.h (Finset.biUnion S id) < s.h (Finset.biUnion s.blocks id)) ∨
      (s.h (Finset.biUnion s.blocks id) = 0 ∧ ∀ S ⊆ s.blocks, 0 ≤ s.h (Finset.biUnion S id))
  lower : ∀ Y, ∃ S ⊆ s.blocks, f s.acc + s.h (Finset.biUnion S id) ≤ f Y

theorem transfer (f : Finset (Fin n) → ℝ) (s s' : MainState n) (hC : Core f s)
    (hacc : s'.acc = s.acc) (hh : s'.h = s.h) (hV : (Finset.biUnion s'.blocks id) = (Finset.biUnion s.blocks id))
    (hU : ∀ S' ⊆ s'.blocks, ∃ S ⊆ s.blocks, (Finset.biUnion S id) = (Finset.biUnion S' id))
    (hM : ∀ S ⊆ s.blocks, ∃ M' ⊆ s'.blocks, s.h (Finset.biUnion M' id) ≤ s.h (Finset.biUnion S id)) : Core f s' := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hacc, hV]; exact hC.part
  · intro S' hS' hne
    obtain ⟨S, hS, e⟩ := hU S' hS'
    rw [hh, hacc, ← e]
    exact hC.exact S hS (by rw [e, ← hV]; exact hne)
  · intro hfk
    rw [hh, hacc, hV] at hfk
    rw [hh, hV]
    rcases hC.fake hfk with ⟨S, hS, hlt⟩ | ⟨h0, hall⟩
    · left
      obtain ⟨M', hM', hle⟩ := hM S hS
      exact ⟨M', hM', lt_of_le_of_lt hle hlt⟩
    · right
      refine ⟨h0, fun S' hS' => ?_⟩
      obtain ⟨S, hS, e⟩ := hU S' hS'
      rw [← e]; exact hall S hS
  · intro Y
    obtain ⟨S, hS, hle⟩ := hC.lower Y
    obtain ⟨M', hM', hle'⟩ := hM S hS
    refine ⟨M', hM', ?_⟩
    rw [hacc, hh]; linarith

theorem core_cap (f : Finset (Fin n) → ℝ) (s : MainState n) (hC : Core f s) : Core f s.cap := by
  have hb : s.cap.blocks = s.blocks := rfl
  have hacc : s.cap.acc = s.acc := rfl
  have hcap : ∀ S, s.cap.h S = if S = (Finset.biUnion s.blocks id) ∧ 0 < s.h S then 0 else s.h S := fun S => rfl
  have hle : ∀ S, s.cap.h S ≤ s.h S := by
    intro S; rw [hcap]; split_ifs with h; exact h.2.le; exact le_rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hC.part
  · intro S hS hne
    rw [hcap, if_neg (fun h => hne h.1)]
    exact hC.exact S hS hne
  · intro hfk
    rw [hb]
    by_cases hpos : 0 < s.h (Finset.biUnion s.blocks id)
    · by_cases hex : ∃ S ⊆ s.blocks, s.cap.h (Finset.biUnion S id) < 0
      · left
        obtain ⟨S, hS, h⟩ := hex
        refine ⟨S, hS, ?_⟩
        rw [hcap (Finset.biUnion s.blocks id), if_pos ⟨rfl, hpos⟩]; exact h
      · right
        push_neg at hex
        refine ⟨by rw [hcap, if_pos ⟨rfl, hpos⟩], hex⟩
    · have hsame : ∀ S, s.cap.h S = s.h S := by
        intro S; rw [hcap]; split_ifs with h
        · exact absurd (h.1 ▸ h.2) hpos
        · rfl
      have hfk' : s.h (Finset.biUnion s.blocks id) ≠ f Finset.univ - f s.acc := by
        rw [← hsame]; exact hfk
      rcases hC.fake hfk' with ⟨S, hS, hlt⟩ | ⟨h0, hall⟩
      · left; exact ⟨S, hS, by rw [hsame, hsame]; exact hlt⟩
      · right; exact ⟨by rw [hsame]; exact h0, fun S hS => by rw [hsame]; exact hall S hS⟩
  · intro Y
    obtain ⟨S, hS, h⟩ := hC.lower Y
    exact ⟨S, hS, by rw [hacc]; linarith [hle (Finset.biUnion S id)]⟩


theorem contract_U (B : Finset (Finset (Fin n))) (C : Finset (Finset (Fin n))) (hCB : C ⊆ B) :
    (Finset.biUnion (insert (Finset.biUnion C id) (B \ C)) id) = (Finset.biUnion B id) ∧
    (∀ S' ⊆ insert (Finset.biUnion C id) (B \ C), ∃ S ⊆ B, (Finset.biUnion S id) = (Finset.biUnion S' id)) ∧
    (∀ M ⊆ B, (C ⊆ M ∨ Disjoint C M) →
      ∃ M' ⊆ insert (Finset.biUnion C id) (B \ C), (Finset.biUnion M' id) = (Finset.biUnion M id)) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · ext a
    simp only [Finset.mem_biUnion, Finset.mem_insert, Finset.mem_sdiff, id]
    constructor
    · rintro ⟨D, hD, ha⟩
      rcases hD with rfl | ⟨hD, _⟩
      · obtain ⟨c, hc, hac⟩ := Finset.mem_biUnion.mp ha
        exact ⟨c, hCB hc, hac⟩
      · exact ⟨D, hD, ha⟩
    · rintro ⟨D, hD, ha⟩
      by_cases hDC : D ∈ C
      · exact ⟨Finset.biUnion C id, Or.inl rfl, Finset.mem_biUnion.mpr ⟨D, hDC, ha⟩⟩
      · exact ⟨D, Or.inr ⟨hD, hDC⟩, ha⟩
  · intro S' hS'
    refine ⟨(S'.filter (fun D => D ∈ B \ C)) ∪ (if (Finset.biUnion C id) ∈ S' then C else ∅), ?_, ?_⟩
    · intro D hD
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff] at hD
      rcases hD with ⟨_, h, _⟩ | hD
      · exact h
      · split_ifs at hD
        · exact hCB hD
        · simp at hD
    · ext a
      simp only [Finset.mem_biUnion, Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff, id]
      constructor
      · rintro ⟨D, hD, ha⟩
        rcases hD with ⟨hD, _⟩ | hD
        · exact ⟨D, hD, ha⟩
        · split_ifs at hD with h
          · exact ⟨Finset.biUnion C id, h, Finset.mem_biUnion.mpr ⟨D, hD, ha⟩⟩
          · simp at hD
      · rintro ⟨D, hD, ha⟩
        rcases Finset.mem_insert.mp (hS' hD) with e | hD'
        · subst e
          obtain ⟨c, hc, hac⟩ := Finset.mem_biUnion.mp ha
          exact ⟨c, Or.inr (by rw [if_pos hD]; exact hc), hac⟩
        · exact ⟨D, Or.inl ⟨hD, Finset.mem_sdiff.mp hD'⟩, ha⟩
  · intro M hM hCM
    refine ⟨M.image (fun b => if b ∈ C then (Finset.biUnion C id) else b), ?_, ?_⟩
    · intro D hD
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hD
      by_cases h : b ∈ C
      · rw [if_pos h]; exact Finset.mem_insert_self _ _
      · rw [if_neg h]; exact Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨hM hb, h⟩)
    · ext a
      simp only [Finset.mem_biUnion, Finset.mem_image, id]
      constructor
      · rintro ⟨D, ⟨b, hb, rfl⟩, ha⟩
        by_cases h : b ∈ C
        · rw [if_pos h] at ha
          obtain ⟨c, hc, hac⟩ := Finset.mem_biUnion.mp ha
          have hCX : C ⊆ M := by
            rcases hCM with h' | h'
            · exact h'
            · exact absurd hb (Finset.disjoint_left.mp h' h)
          exact ⟨c, hCX hc, hac⟩
        · rw [if_neg h] at ha; exact ⟨b, hb, ha⟩
      · rintro ⟨b, hb, ha⟩
        refine ⟨_, ⟨b, hb, rfl⟩, ?_⟩
        by_cases h : b ∈ C
        · rw [if_pos h]; exact Finset.mem_biUnion.mpr ⟨b, h, ha⟩
        · rw [if_neg h]; exact ha


theorem U_inj (s : MainState n) (hI : X5FC.Inv s) (S T : Finset (Finset (Fin n)))
    (hS : S ⊆ s.blocks) (hT : T ⊆ s.blocks) (e : (Finset.biUnion S id) = (Finset.biUnion T id)) : S = T := by
  ext b
  constructor
  · intro hb
    exact X5TC.mem_of_biU s.blocks hI.disj hI.ne T hT b (hS hb)
      (by rw [← e]; exact Finset.subset_biUnion_of_mem id hb)
  · intro hb
    exact X5TC.mem_of_biU s.blocks hI.disj hI.ne S hS b (hT hb)
      (by rw [e]; exact Finset.subset_biUnion_of_mem id hb)

theorem core_delete (f : Finset (Fin n) → ℝ) (s : MainState n) (hG : X5TC.GInv s)
    (hC : Core f s) (w : Finset (Fin n)) (hw : w ∈ s.blocks)
    (hP : ∀ X, IsMinimizer s.blocks s.curFun X → s.R w ⊆ X) : Core f (s.delete w) := by
  classical
  have hI := hG.base
  set Rw := s.R w with hRw
  set Q := (Finset.biUnion Rw id) with hQ
  have hRb : Rw ⊆ s.blocks := X5TC.R_sub s w
  have hwR : w ∈ Rw := X5TC.R_self s w hw
  have hb' : (s.delete w).blocks = s.blocks \ Rw := rfl
  have hacc' : (s.delete w).acc = s.acc ∪ Q := rfl
  have hh' : ∀ S, (s.delete w).h S = s.h (S ∪ Q) - s.h Q := fun S => rfl
  have hUu : ∀ S T : Finset (Finset (Fin n)), (Finset.biUnion (S ∪ T) id) = (Finset.biUnion S id) ∪ (Finset.biUnion T id) :=
    fun S T => Finset.union_biUnion
  have hdisj : ∀ S ⊆ s.blocks \ Rw, Disjoint (Finset.biUnion S id) Q := by
    intro S hS
    rw [Finset.disjoint_biUnion_left]
    intro c hc
    rw [Finset.disjoint_biUnion_right]
    intro d hd
    have hc' := Finset.mem_sdiff.mp (hS hc)
    exact hI.disj c hc'.1 d (hRb hd) (fun e => hc'.2 (e ▸ hd))
  have hsplit : (Finset.biUnion s.blocks id) = (Finset.biUnion (s.blocks \ Rw) id) ∪ Q := by
    rw [hQ, ← hUu, Finset.sdiff_union_of_subset hRb]
  obtain ⟨M, hM⟩ := X5TC.exists_min s.blocks s.curFun
  have hRM := hP M hM
  have hMmin : ∀ S ⊆ s.blocks, s.h (Finset.biUnion M id) ≤ s.h (Finset.biUnion S id) := fun S hS => hM.2 S hS
  have hMsplit : (Finset.biUnion (M \ Rw) id) ∪ Q = (Finset.biUnion M id) := by
    rw [hQ, ← hUu, Finset.sdiff_union_of_subset hRM]
  have hMb : M \ Rw ⊆ s.blocks \ Rw := Finset.sdiff_subset_sdiff hM.1 subset_rfl
  -- the empty set is not a minimizer
  have hnot0 : ¬ ∀ S ⊆ s.blocks, 0 ≤ s.h (Finset.biUnion S id) := by
    intro hall
    have h0 : s.h (Finset.biUnion (∅ : Finset (Finset (Fin n))) id) = 0 := hG.zero
    have hmin0 : IsMinimizer s.blocks s.curFun ∅ :=
      ⟨Finset.empty_subset _, fun S hS => by
        show s.h (Finset.biUnion (∅ : Finset (Finset (Fin n))) id) ≤ s.h (Finset.biUnion S id); rw [h0]; exact hall S hS⟩
    have := hP ∅ hmin0 hwR
    simp at this
  by_cases hfull : Rw = s.blocks
  · -- everything is deleted
    have hb0 : (s.delete w).blocks = ∅ := by rw [hb', hfull, Finset.sdiff_self]
    have haccU : s.acc ∪ Q = Finset.univ := by rw [hQ, hfull]; exact hC.part
    have hMb' : M = s.blocks := Finset.Subset.antisymm hM.1 (hfull ▸ hRM)
    have hnf : s.h (Finset.biUnion s.blocks id) = f Finset.univ - f s.acc := by
      by_contra hfk
      rcases hC.fake hfk with ⟨S, hS, hlt⟩ | ⟨_, hall⟩
      · have := hMmin S hS; rw [hMb'] at this; linarith
      · exact hnot0 hall
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hb0, hacc']; simpa using haccU
    · intro S hS hne
      rw [hb0] at hS hne
      rw [Finset.subset_empty.mp hS] at hne; exact absurd rfl hne
    · intro hfk
      exfalso; apply hfk
      rw [hb0, hh', hacc', haccU]; simp
    · intro Y
      refine ⟨∅, Finset.empty_subset _, ?_⟩
      rw [hacc', haccU, hh']
      obtain ⟨S, hS, hle⟩ := hC.lower Y
      have := hMmin S hS
      rw [hMb', hnf] at this
      simp only [Finset.biUnion_empty, Finset.empty_union, sub_self, add_zero]
      linarith
  · have hQne : Q ≠ (Finset.biUnion s.blocks id) := by
      intro e; exact hfull (U_inj s hI Rw s.blocks hRb subset_rfl e)
    have hhQ : s.h Q = f (Q ∪ s.acc) - f s.acc := hC.exact Rw hRb hQne
    have hacc'' : f (s.acc ∪ Q) = f s.acc + s.h Q := by
      rw [hhQ, Finset.union_comm]; ring
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hb', hacc', Finset.union_assoc, Finset.union_comm Q, ← hsplit]; exact hC.part
    · intro S hS hne
      rw [hb'] at hS hne
      have hSR : S ∪ Rw ⊆ s.blocks := Finset.union_subset (hS.trans Finset.sdiff_subset) hRb
      have hne2 : (Finset.biUnion (S ∪ Rw) id) ≠ (Finset.biUnion s.blocks id) := by
        intro e
        have e2 := U_inj s hI _ _ hSR subset_rfl e
        apply hne
        congr 1
        ext b; constructor
        · intro hb; exact hS hb
        · intro hb
          rw [Finset.mem_sdiff] at hb
          rw [← e2] at hb
          rcases Finset.mem_union.mp hb.1 with h | h
          · exact h
          · exact absurd h hb.2
      have h1 := hC.exact _ hSR hne2
      rw [hUu] at h1
      rw [hh', h1, hhQ, hacc']
      have e3 : (Finset.biUnion S id) ∪ Q ∪ s.acc = (Finset.biUnion S id) ∪ (s.acc ∪ Q) := by
        ext; simp only [Finset.mem_union]; tauto
      rw [e3, Finset.union_comm Q s.acc]; ring
    · intro hfk
      rw [hb', hh', hacc', hacc'', ← hsplit] at hfk
      rw [hb', hh', ← hsplit]
      have hfk' : s.h (Finset.biUnion s.blocks id) ≠ f Finset.univ - f s.acc := by
        intro e; apply hfk; rw [e]; ring
      rcases hC.fake hfk' with ⟨S, hS, hlt⟩ | ⟨_, hall⟩
      · left
        refine ⟨M \ Rw, hMb, ?_⟩
        rw [hh', hMsplit]
        have := hMmin S hS
        linarith
      · exact absurd hall hnot0
    · intro Y
      obtain ⟨S, hS, hle⟩ := hC.lower Y
      refine ⟨M \ Rw, by rw [hb']; exact hMb, ?_⟩
      rw [hacc', hacc'', hh', hMsplit]
      have := hMmin S hS
      linarith


theorem core_init (f : Finset (Fin n) → ℝ) (hf0 : f ∅ = 0) : Core f (initMain f) := by
  classical
  have hb : (initMain f).blocks = Finset.univ.image (fun a => ({a} : Finset (Fin n))) := rfl
  have hUall : ∀ Y : Finset (Fin n), (Finset.biUnion (Y.image (fun a => ({a} : Finset (Fin n)))) id) = Y := by
    intro Y; ext a; simp
  have hsub : ∀ Y : Finset (Fin n), Y.image (fun a => ({a} : Finset (Fin n))) ⊆ (initMain f).blocks := by
    intro Y; rw [hb]; exact Finset.image_subset_image (Finset.subset_univ _)
  have hacc : (initMain f).acc = ∅ := rfl
  have hh : (initMain f).h = f := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hacc, hb, hUall]; simp
  · intro S _ _; rw [hh, hacc, hf0]; simp
  · intro hfk; exfalso; apply hfk; rw [hh, hacc, hf0, hb, hUall]; simp
  · intro Y
    refine ⟨_, hsub Y, ?_⟩
    rw [hh, hacc, hf0, hUall]; simp

theorem reach_core (f : Finset (Fin n) → ℝ) (hsub : SubmodularOn Finset.univ f) (hf0 : f ∅ = 0)
    (s : MainState n) (hs : Relation.ReflTransGen Step (initMain f) s) :
    Core f s ∧ ∀ X, s.mode = Mode.done X → ∀ Y, f X ≤ f Y := by
  induction hs with
  | refl => exact ⟨core_init f hf0, by intro X h; simp [initMain] at h⟩
  | @tail s s' hr hst ih =>
    obtain ⟨hC, _⟩ := ih
    have hP := IFP.reach_pinv f hsub hf0 s hr
    have hG := hP.g
    rcases hst with hfin | hcall | hfix | hret
    · obtain ⟨_, ⟨hb0, e⟩ | ⟨hne, hη, e⟩⟩ := hfin
      · subst e
        refine ⟨⟨hC.part, hC.exact, hC.fake, hC.lower⟩, ?_⟩
        intro X hX Y
        simp only [Mode.done.injEq] at hX
        subst hX
        have h0 : s.h (Finset.biUnion (∅ : Finset (Finset (Fin n))) id) = 0 := hG.zero
        have hfo : finalOut s = s.acc := by
          unfold finalOut
          have : ¬ (s.h (s.blocks.biUnion id) < 0) := by
            rw [hb0, h0]; exact lt_irrefl 0
          rw [if_neg this]; simp
        rw [hfo]
        obtain ⟨S, hS, hle⟩ := hC.lower Y
        rw [hb0, Finset.subset_empty] at hS
        rw [hS, h0] at hle; linarith
      · subst e
        have hCc := core_cap f s hC
        refine ⟨⟨hCc.part, hCc.exact, hCc.fake, hCc.lower⟩, ?_⟩
        intro X hX Y
        simp only [Mode.done.injEq] at hX
        subst hX
        obtain ⟨hsubc, hzc, _⟩ := X5TC.cap_parts s hG
        obtain ⟨L, hL, hcons⟩ := IFA.exists_consistent s.arcs hP.acyc s.blocks
        have hmin := (eta_nonpos s.cap.blocks hne s.cap.curFun hsubc hzc s.cap.arcs
          hG.base.arcs L hL hcons hη).2
        have hminS : ∀ S ⊆ s.blocks, s.cap.h (Finset.biUnion s.blocks id) ≤ s.cap.h (Finset.biUnion S id) :=
          fun S hS => hmin.2 S hS
        obtain ⟨S, hS, hle⟩ := hCc.lower Y
        have h1 := hminS S hS
        have hacc : s.cap.acc = s.acc := rfl
        have hbc : s.cap.blocks = s.blocks := rfl
        rw [hacc] at hle
        unfold finalOut
        rw [hacc, hbc]
        split_ifs with hneg
        · have hnf : s.cap.h (Finset.biUnion s.blocks id) = f Finset.univ - f s.acc := by
            by_contra hfk
            rcases hCc.fake hfk with ⟨S', hS', hlt⟩ | ⟨h0, _⟩
            · have := hminS S' (hbc ▸ hS'); rw [hbc] at hlt; linarith
            · rw [hbc] at h0; linarith
          rw [hC.part]
          linarith
        · simp only [Finset.union_empty]
          push_neg at hneg
          linarith
    · obtain ⟨_, _, _, u, L, _, _, rest⟩ := hcall
      simp only at rest
      obtain ⟨_, _, e⟩ := rest
      subst e
      have hCc := core_cap f s hC
      exact ⟨⟨hCc.part, hCc.exact, hCc.fake, hCc.lower⟩, by intro X h; simp at h⟩
    · obtain ⟨fr, u, η, ph, ph', hm, _, e⟩ := hfix
      subst e
      exact ⟨⟨hC.part, hC.exact, hC.fake, hC.lower⟩, by intro X h; simp at h⟩
    · obtain ⟨fr, u, η, ph, w, hm, hout, hcase⟩ := hret
      obtain ⟨hF1, hF2⟩ := X5TC.return_facts s hG fr u η ph hm w hout
      have hwG : w ∈ s.fixGround fr u := hout.2.2.2.1
      rcases hcase with ⟨hfr, huw, rfl⟩ | ⟨hfr, huw, rfl⟩ | ⟨hfr, rfl⟩
      · refine ⟨?_, by intro X h; simp [MainState.contract] at h⟩
        obtain ⟨hwV, hcomp⟩ := hF1 hfr
        rw [Finset.mem_sdiff] at hwV
        set C := (s.R w).filter (fun v => u ∈ s.R v) with hCdef
        have hCb : C ⊆ s.blocks := fun X hX => X5TC.R_sub s w (Finset.mem_filter.mp hX).1
        obtain ⟨h1, h2, h3⟩ := contract_U s.blocks C hCb
        have hbl : (s.contract u w).blocks = insert (Finset.biUnion C id) (s.blocks \ C) := rfl
        apply transfer f s (s.contract u w) hC rfl rfl (by rw [hbl]; exact h1) (by rw [hbl]; exact h2)
        intro S hS
        obtain ⟨M, hM⟩ := X5TC.exists_min s.blocks s.curFun
        have hCM : C ⊆ M ∨ Disjoint C M := by
          by_cases hc : ∃ v ∈ C, v ∈ M
          · left
            obtain ⟨v, hv, hvX⟩ := hc
            have huX : u ∈ M := X5TC.closure s hG M hM v hvX (Finset.mem_filter.mp hv).2
            have hwX : w ∈ M := hcomp M hM huX
            intro c hc'
            exact X5TC.closure s hG M hM w hwX (Finset.mem_filter.mp hc').1
          · right
            rw [Finset.disjoint_left]
            intro c hc' hcX
            exact hc ⟨c, hc', hcX⟩
        obtain ⟨M', hM', e⟩ := h3 M hM.1 hCM
        refine ⟨M', by rw [hbl]; exact hM', ?_⟩
        rw [e]; exact hM.2 S hS
      · exact ⟨⟨hC.part, hC.exact, hC.fake, hC.lower⟩, by intro X h; simp [MainState.addArc] at h⟩
      · refine ⟨?_, by intro X h; simp [MainState.delete] at h⟩
        have hw : w ∈ s.blocks := by simpa [MainState.fixGround, hfr] using hwG
        exact core_delete f s hG hC w hw (fun X hX => (hF2 hfr X hX).2)

/-- Correctness: every final state reachable from the initial state outputs a minimizer. -/
theorem correct {n : ℕ} (f : Finset (Fin n) → ℝ)
    (hsub : SubmodularOn Finset.univ f) (hf0 : f ∅ = 0)
    (s : MainState n) (X : Finset (Fin n)) (hs : Relation.ReflTransGen Step (initMain f) s)
    (hX : s.mode = Mode.done X) : ∀ Y : Finset (Fin n), f X ≤ f Y :=
  (reach_core f hsub hf0 s hs).2 X hX

end IFC



open IwataFF.SFM

namespace IFT

/-! ## Counting along a run -/

section Count
variable {σ : Type}

open Classical in
noncomputable def cnt (s : ℕ → σ) (P : σ → σ → Prop) (k : ℕ) : ℕ :=
  ((Finset.range k).filter (fun j => P (s j) (s (j + 1)))).card

open Classical in
theorem cnt_succ (s : ℕ → σ) (P : σ → σ → Prop) (k : ℕ) :
    cnt s P (k + 1) = cnt s P k + if P (s k) (s (k + 1)) then 1 else 0 := by
  unfold cnt
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · simp

open Classical in
/-- a potential that drops on `A`-steps and is reset to at most `G₁` / `G₂` on `B₁` / `B₂`-steps. -/
theorem count_le (s : ℕ → σ) (k : ℕ) (A B₁ B₂ : σ → σ → Prop) (g : σ → ℕ) (G₁ G₂ : ℕ)
    (h : ∀ j < k, g (s (j + 1)) + (if A (s j) (s (j + 1)) then 1 else 0) ≤
      g (s j) + (if B₁ (s j) (s (j + 1)) then G₁ else 0) +
        (if B₂ (s j) (s (j + 1)) then G₂ else 0)) :
    cnt s A k + g (s k) ≤ g (s 0) + G₁ * cnt s B₁ k + G₂ * cnt s B₂ k := by
  induction k with
  | zero => simp [cnt]
  | succ k ih =>
    have ih' := ih (fun j hj => h j (by omega))
    have hk := h k (by omega)
    rw [cnt_succ, cnt_succ, cnt_succ]
    split_ifs at hk ⊢ <;> nlinarith

open Classical in
theorem cnt_mono (s : ℕ → σ) (P Q : σ → σ → Prop) (k : ℕ)
    (h : ∀ j < k, P (s j) (s (j + 1)) → Q (s j) (s (j + 1))) : cnt s P k ≤ cnt s Q k := by
  unfold cnt
  apply Finset.card_le_card
  intro j hj
  rw [Finset.mem_filter] at hj ⊢
  exact ⟨hj.1, h j (Finset.mem_range.mp hj.1) hj.2⟩

open Classical in
theorem cnt_or (s : ℕ → σ) (P Q : σ → σ → Prop) (k : ℕ) :
    cnt s (fun a b => P a b ∨ Q a b) k ≤ cnt s P k + cnt s Q k := by
  unfold cnt
  simp only
  rw [Finset.filter_or]
  exact Finset.card_union_le _ _

open Classical in
theorem cnt_all (s : ℕ → σ) (P : σ → σ → Prop) (k : ℕ) (h : ∀ j < k, P (s j) (s (j + 1))) :
    k = cnt s P k := by
  unfold cnt
  rw [Finset.filter_true_of_mem (fun j hj => h j (Finset.mem_range.mp hj)), Finset.card_range]

end Count

/-! ## Affinely independent families of vectors supported on `V` -/

theorem card_le_of_affInd {α : Type} [DecidableEq α] (V : Finset α) {N : ℕ}
    (p : Fin N → (α → ℝ)) (hp : AffineIndependent ℝ p) (hV : ∀ j a, a ∉ V → p j a = 0) :
    N ≤ V.card + 1 := by
  have h1 := hp.card_le_finrank_succ
  rw [Fintype.card_fin] at h1
  let Wsub : Submodule ℝ (α → ℝ) :=
    { carrier := {x | ∀ a, a ∉ V → x a = 0}
      add_mem' := by
        intro x y hx hy a ha
        simp only [Set.mem_ofPred_eq] at hx hy
        simp [hx a ha, hy a ha]
      zero_mem' := by intro a _; rfl
      smul_mem' := by
        intro c x hx a ha
        simp only [Set.mem_ofPred_eq] at hx
        simp [hx a ha] }
  have hle : vectorSpan ℝ (Set.range p) ≤ Wsub := by
    rw [vectorSpan_def]
    apply Submodule.span_le.mpr
    rintro _ ⟨x, ⟨i, rfl⟩, y, ⟨j, rfl⟩, rfl⟩
    intro a ha
    simp [hV i a ha, hV j a ha]
  let R : (vectorSpan ℝ (Set.range p)) →ₗ[ℝ] (V → ℝ) :=
    { toFun := fun x v => (x : α → ℝ) v
      map_add' := by intro x y; rfl
      map_smul' := by intro c x; rfl }
  have hR : Function.Injective R := by
    intro x y hxy
    apply Subtype.ext
    funext a
    by_cases ha : a ∈ V
    · exact congrFun hxy ⟨a, ha⟩
    · rw [hle x.2 a ha, hle y.2 a ha]
  have h2 := LinearMap.finrank_le_finrank_of_injective hR
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h2
  omega


/-! ## Pushes -/

section Push
variable {α : Type} [DecidableEq α]

theorem push_data (V : Finset α) (f : Finset α → ℝ) (st st' : PhaseState α)
    (hinv : PhaseInv V st) (h : PushStep f V st st') :
    ∃ i L lam u v, st.idx[i]? = some (L, lam) ∧ IsOrdering V L ∧ 0 < lam ∧ ImmSucc L u v ∧
      L.idxOf u = L.idxOf v + 1 ∧ u ∈ V ∧ v ∈ V ∧ u ≠ v ∧ u ∈ Wset f V st ∧
      v ∉ Wset f V st ∧ 0 < st.phi u v ∧ st' = pushResult f V st i L lam u v := by
  obtain ⟨_, _, _, i, L, lam, u, v, hi, hact, hsucc, rfl⟩ := h
  obtain ⟨hδ, _, hord, hsum, hskew, hfeas⟩ := hinv
  obtain ⟨hL, hlam⟩ := hord _ (X5IW.mem_of_getElem? hi)
  obtain ⟨p, hp, hvV, hvW, hne', hmax⟩ := hact
  rw [hi] at hp; cases hp
  obtain ⟨hvL, hsu⟩ := hsucc
  set k := L.idxOf v with hk
  obtain ⟨hk1, hku⟩ := List.getElem?_eq_some_iff.mp hsu
  have huL : u ∈ L := by rw [← hku]; exact List.getElem_mem hk1
  have huV : u ∈ V := (hL.2 u).mp huL
  have hidxu : L.idxOf u = k + 1 := by rw [← hku]; exact hL.1.idxOf_getElem _ hk1
  have huv : u ≠ v := by
    intro e; rw [e] at hidxu; omega
  have huW : u ∈ Wset f V st := by
    by_contra huW
    have hpre : prefixSet L u = insert u (prefixSet L v) := by
      unfold prefixSet; rw [hidxu, ← hk]
      have := X5IW.take_succ_toFinset L (k + 1) hk1
      rw [hku] at this; exact this
    have hne2 : (Wset f V st \ prefixSet L u).Nonempty := by
      rw [hpre]; obtain ⟨w, hw⟩ := hne'
      refine ⟨w, ?_⟩
      rw [Finset.mem_sdiff] at hw ⊢
      refine ⟨hw.1, ?_⟩
      rw [Finset.mem_insert]; rintro (rfl | h); exact huW hw.1; exact hw.2 h
    have := hmax u huV huW hne2
    simp only at this
    omega
  have hphi : 0 < st.phi u v := by
    by_contra hneg
    apply hvW
    simp only [Wset, Finset.mem_filter] at huW ⊢
    obtain ⟨_, s, hs, hr⟩ := huW
    exact ⟨hvV, s, hs, hr.tail ⟨huV, hvV, huv, le_of_not_gt hneg⟩⟩
  exact ⟨i, L, lam, u, v, hi, hL, hlam, ⟨hvL, hsu⟩, hidxu, huV, hvV, huv, huW, hvW, hphi, rfl⟩

theorem idxOf_map_inj (g : α → α) (hg : Function.Injective g) :
    ∀ (L : List α) (a : α), (L.map g).idxOf (g a) = L.idxOf a
  | [], a => by simp
  | b :: L, a => by
    by_cases h : b = a
    · subst h; simp
    · have h' : g b ≠ g a := fun e => h (hg e)
      rw [List.map_cons, List.idxOf_cons_ne _ h', List.idxOf_cons_ne _ h, idxOf_map_inj g hg L a]

theorem swap_pos (L : List α) (u v w : α) :
    (swapAdj L u v).idxOf w = L.idxOf (Equiv.swap u v w) := by
  rw [X5IW.swapAdj_eq]
  conv_lhs => rw [show w = Equiv.swap u v (Equiv.swap u v w) by simp]
  exact idxOf_map_inj _ (Equiv.injective _) L _

theorem sum_pos_swap (L : List α) (W : Finset α) (u v : α) (hu : u ∈ W) (hv : v ∉ W)
    (hpos : L.idxOf u = L.idxOf v + 1) :
    ∑ w ∈ W, (swapAdj L u v).idxOf w + 1 = ∑ w ∈ W, L.idxOf w := by
  rw [← Finset.add_sum_erase W _ hu, ← Finset.add_sum_erase W _ hu, swap_pos,
    Equiv.swap_apply_left]
  have : ∑ w ∈ W.erase u, (swapAdj L u v).idxOf w = ∑ w ∈ W.erase u, L.idxOf w := by
    apply Finset.sum_congr rfl
    intro w hw
    rw [swap_pos, Equiv.swap_apply_of_ne_of_ne (Finset.ne_of_mem_erase hw)
      (fun e => hv (by rw [← e]; exact Finset.mem_of_mem_erase hw))]
  rw [this]; omega

theorem Sset_congr (f : Finset α → ℝ) (V : Finset α) (st st' : PhaseState α)
    (hz : zOf f V st' = zOf f V st) (hd : st'.delta = st.delta) :
    Sset f V st' = Sset f V st ∧ Tset f V st' = Tset f V st := by
  have hz' : ∀ v, xOf f st' v - bdry V st' v = xOf f st v - bdry V st v :=
    fun v => congrFun hz v
  constructor
  · unfold Sset; apply Finset.filter_congr; intro v _
    have := hz' v; rw [hd]; constructor <;> intro h <;> linarith
  · unfold Tset; apply Finset.filter_congr; intro v _
    have := hz' v; rw [hd]; constructor <;> intro h <;> linarith

theorem push_amount (V : Finset α) (hV : V.Nonempty) (f : Finset α → ℝ)
    (hsub : SubmodularOn V f) (hf0 : f ∅ = 0) (st : PhaseState α) (hinv : PhaseInv V st)
    (L : List α) (hL : IsOrdering V L) (lam : ℝ) (hlam : 0 < lam) (u v : α) :
    0 ≤ min st.delta (lam * ec V f (greedy f L) u v) := by
  have he := X5IW.ec_nonneg V f _ (X5IW.greedy_base V f hsub hf0 L hL) u v
  exact le_min hinv.1.le (mul_nonneg hlam.le he)

/-- pushes only enlarge `W` -/
theorem push_W_mono (V : Finset α) (hV : V.Nonempty) (f : Finset α → ℝ)
    (hsub : SubmodularOn V f) (hf0 : f ∅ = 0) (st st' : PhaseState α) (hinv : PhaseInv V st)
    (h : PushStep f V st st') : Wset f V st ⊆ Wset f V st' := by
  obtain ⟨_, _, hz⟩ := X5IW.push_step V hV f hsub hf0 st st' hinv h
  obtain ⟨i, L, lam, u, v, hi, hL, hlam, _, _, huV, hvV, huv, huW, hvW, _, rfl⟩ :=
    push_data V f st st' hinv h
  have hd : (pushResult f V st i L lam u v).delta = st.delta := rfl
  have hS := (Sset_congr f V st _ hz hd).1
  have ha := push_amount V hV f hsub hf0 st hinv L hL lam hlam u v
  intro t ht
  simp only [Wset, Finset.mem_filter] at ht ⊢
  obtain ⟨htV, s, hs, hr⟩ := ht
  refine ⟨htV, s, by rw [hS]; exact hs, ?_⟩
  have hsV : s ∈ V := (Finset.mem_filter.mp hs).1
  -- every vertex on an old path from `S` is in `W`, hence not `v`
  have key : ∀ c, Relation.ReflTransGen (resArc V st) s c →
      Relation.ReflTransGen (resArc V (pushResult f V st i L lam u v)) s c := by
    intro c hc
    induction hc with
    | refl => exact .refl
    | @tail b c hb hbc ih =>
      refine ih.tail ?_
      obtain ⟨hbV, hcV, hbc', hphi⟩ := hbc
      have hbW : b ∈ Wset f V st := by
        simp only [Wset, Finset.mem_filter]; exact ⟨hbV, s, hs, hb⟩
      have hbv : b ≠ v := fun e => hvW (e ▸ hbW)
      refine ⟨hbV, hcV, hbc', ?_⟩
      simp only [pushResult, phiPush]
      split_ifs with h1 h2
      · linarith
      · exact absurd h2.1 hbv
      · exact hphi
  exact key t hr

/-- a push that creates a new index puts `v` into `W` -/
theorem push_new_v (V : Finset α) (hV : V.Nonempty) (f : Finset α → ℝ)
    (hsub : SubmodularOn V f) (hf0 : f ∅ = 0) (st : PhaseState α) (hinv : PhaseInv V st)
    (i : ℕ) (L : List α) (lam : ℝ) (u v : α) (hpush : PushStep f V st (pushResult f V st i L lam u v))
    (huV : u ∈ V) (hvV : v ∈ V) (huv : u ≠ v) (huW : u ∈ Wset f V st)
    (hns : min st.delta (lam * ec V f (greedy f L) u v) < lam * ec V f (greedy f L) u v) :
    v ∈ Wset f V (pushResult f V st i L lam u v) := by
  have hmono := push_W_mono V hV f hsub hf0 st _ hinv hpush
  have ha : min st.delta (lam * ec V f (greedy f L) u v) = st.delta := by
    rcases min_choice st.delta (lam * ec V f (greedy f L) u v) with h | h
    · exact h
    · rw [h] at hns; exact absurd hns (lt_irrefl _)
  have hfe := (hinv.2.2.2.2.2 u huV v hvV).2
  have huW' := hmono huW
  simp only [Wset, Finset.mem_filter] at huW' ⊢
  obtain ⟨_, s, hs, hr⟩ := huW'
  refine ⟨hvV, s, hs, hr.tail ⟨huV, hvV, huv, ?_⟩⟩
  simp only [pushResult, phiPush, and_self, if_true]
  rw [ha]; linarith


theorem list_sum_set_nat {β : Type*} (g : β → ℕ) :
    ∀ (l : List β) (i : ℕ) (p q : β), l[i]? = some p →
      ((l.set i q).map g).sum + g p = (l.map g).sum + g q
  | [], i, p, q, h => by simp at h
  | a :: l, 0, p, q, h => by
      simp at h; subst h; simp; ring
  | a :: l, i + 1, p, q, h => by
      simp only [List.getElem?_cons_succ] at h
      simp only [List.set_cons_succ, List.map_cons, List.sum_cons]
      have := list_sum_set_nat g l i p q h
      omega

/-- `Φ = ∑_{i ∈ I} ∑_{w ∈ W} (position of w in L_i)` -/
def Phi (idx : List (List α × ℝ)) (W : Finset α) : ℕ :=
  (idx.map (fun p => ∑ w ∈ W, p.1.idxOf w)).sum

theorem pos_lt (V : Finset α) (L : List α) (hL : IsOrdering V L) (w : α) (hw : w ∈ V) :
    L.idxOf w < V.card := by
  have h1 := List.idxOf_lt_length_of_mem ((hL.2 w).mpr hw)
  have h2 : L.toFinset = V := by ext b; rw [List.mem_toFinset]; exact hL.2 b
  have h3 := List.toFinset_card_of_nodup hL.1
  rw [h2] at h3; omega

theorem Phi_le (V : Finset α) (W : Finset α) (hW : W ⊆ V) :
    ∀ idx : List (List α × ℝ), (∀ p ∈ idx, IsOrdering V p.1) →
      Phi idx W ≤ idx.length * (W.card * V.card)
  | [], _ => by simp [Phi]
  | p :: l, h => by
    have ih := Phi_le V W hW l (fun q hq => h q (List.mem_cons_of_mem _ hq))
    have hp : ∑ w ∈ W, p.1.idxOf w ≤ W.card * V.card := by
      calc ∑ w ∈ W, p.1.idxOf w ≤ ∑ w ∈ W, V.card :=
            Finset.sum_le_sum (fun w hw => (pos_lt V p.1 (h p List.mem_cons_self) w (hW hw)).le)
        _ = W.card * V.card := by rw [Finset.sum_const, smul_eq_mul]
    simp only [Phi, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    nlinarith

theorem Phi_split (W W' : Finset α) (h : W ⊆ W') :
    ∀ idx : List (List α × ℝ), Phi idx W' = Phi idx W + Phi idx (W' \ W)
  | [] => by simp [Phi]
  | p :: l => by
    have ih := Phi_split W W' h l
    simp only [Phi, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, ← Finset.sum_sdiff h]; ring

theorem Phi_append (W : Finset α) (l : List (List α × ℝ)) (q : List α × ℝ) :
    Phi (l ++ [q]) W = Phi l W + ∑ w ∈ W, q.1.idxOf w := by
  simp [Phi]

/-- the potential bounding the number of pushes -/
noncomputable def Psi (f : Finset α → ℝ) (V : Finset α) (st : PhaseState α) : ℕ :=
  Phi st.idx (Wset f V st) + st.idx.length * V.card * (V.card - (Wset f V st).card) +
    2 * V.card * V.card * (V.card - (Wset f V st).card)

theorem W_sub (f : Finset α → ℝ) (V : Finset α) (st : PhaseState α) : Wset f V st ⊆ V := by
  intro x hx; simp only [Wset, Finset.mem_filter] at hx; exact hx.1

theorem Psi_le (f : Finset α → ℝ) (V : Finset α) (st : PhaseState α)
    (hord : ∀ p ∈ st.idx, IsOrdering V p.1) :
    Psi f V st ≤ 2 * V.card * V.card * (st.idx.length + V.card) := by
  have h1 := Phi_le V _ (W_sub f V st) st.idx hord
  have h2 := Finset.card_le_card (W_sub f V st)
  unfold Psi
  set m := V.card
  set w := (Wset f V st).card
  set I := st.idx.length
  have h3 : w * m ≤ m * m := Nat.mul_le_mul_right _ h2
  have h4 : m - w ≤ m := Nat.sub_le _ _
  have h5 : I * m * (m - w) ≤ I * m * m := Nat.mul_le_mul_left _ h4
  have h6 : 2 * m * m * (m - w) ≤ 2 * m * m * m := Nat.mul_le_mul_left _ h4
  have h7 : I * (w * m) ≤ I * (m * m) := Nat.mul_le_mul_left _ h3
  nlinarith

theorem arith_sat (Φ Φ1 X I m w0 w1 : ℕ) (h01 : w0 ≤ w1) (h1m : w1 ≤ m) (hP : Φ1 + 1 = Φ)
    (hX : X ≤ I * ((w1 - w0) * m)) :
    Φ1 + X + I * m * (m - w1) + 2 * m * m * (m - w1) + 1 ≤
      Φ + I * m * (m - w0) + 2 * m * m * (m - w0) := by
  obtain ⟨A, rfl⟩ : ∃ A, m = w1 + A := ⟨m - w1, by omega⟩
  obtain ⟨B, rfl⟩ : ∃ B, w1 = w0 + B := ⟨w1 - w0, by omega⟩
  have e1 : w0 + B + A - (w0 + B) = A := by omega
  have e2 : w0 + B + A - w0 = A + B := by omega
  have e3 : w0 + B - w0 = B := by omega
  rw [e1, e2]
  rw [e3] at hX
  set m := w0 + B + A
  have r1 : I * (B * m) = I * m * B := by ring
  have r2 : I * m * (A + B) = I * m * A + I * m * B := by ring
  have r3 : 2 * m * m * (A + B) = 2 * m * m * A + 2 * m * m * B := by ring
  rw [r2, r3]
  rw [r1] at hX
  omega

theorem arith_ns (Φ Φ1 X I m w0 w1 P : ℕ) (h01 : w0 + 1 ≤ w1) (h1m : w1 ≤ m)
    (hP : Φ1 + 1 = Φ + P) (hPm : P ≤ m * m) (hX : X ≤ (I + 1) * ((w1 - w0) * m)) :
    Φ1 + X + (I + 1) * m * (m - w1) + 2 * m * m * (m - w1) + 1 ≤
      Φ + I * m * (m - w0) + 2 * m * m * (m - w0) := by
  obtain ⟨A, rfl⟩ : ∃ A, m = w1 + A := ⟨m - w1, by omega⟩
  obtain ⟨B, rfl⟩ : ∃ B, w1 = w0 + B + 1 := ⟨w1 - w0 - 1, by omega⟩
  have e1 : w0 + B + 1 + A - (w0 + B + 1) = A := by omega
  have e2 : w0 + B + 1 + A - w0 = A + B + 1 := by omega
  have e3 : w0 + B + 1 - w0 = B + 1 := by omega
  rw [e1, e2]
  rw [e3] at hX
  set m := w0 + B + 1 + A with hm
  have hle : A + B + 1 ≤ m := by omega
  have h5 : m * (A + B + 1) ≤ m * m := Nat.mul_le_mul_left _ hle
  have r1 : (I + 1) * ((B + 1) * m) = I * m * B + I * m + m * B + m := by ring
  have r2 : (I + 1) * m * A = I * m * A + m * A := by ring
  have r3 : I * m * (A + B + 1) = I * m * A + I * m * B + I * m := by ring
  have r4 : 2 * m * m * (A + B + 1) = 2 * (m * m * A) + 2 * (m * m * B) + 2 * (m * m) := by ring
  have r5 : 2 * m * m * A = 2 * (m * m * A) := by ring
  have r6 : m * (A + B + 1) = m * A + m * B + m := by ring
  rw [r1] at hX
  rw [r6] at h5
  rw [r2, r3, r4, r5]
  omega

/-- each push decreases `Ψ`, and `|I| − |W|` does not increase -/
theorem push_psi (V : Finset α) (hV : V.Nonempty) (f : Finset α → ℝ)
    (hsub : SubmodularOn V f) (hf0 : f ∅ = 0) (st st' : PhaseState α) (hinv : PhaseInv V st)
    (h : PushStep f V st st') :
    Psi f V st' + 1 ≤ Psi f V st ∧
      st'.idx.length + (Wset f V st).card ≤ st.idx.length + (Wset f V st').card := by
  have hps := X5IW.push_step V hV f hsub hf0 st st' hinv h
  have hmono := push_W_mono V hV f hsub hf0 st st' hinv h
  have hpush := h
  obtain ⟨i, L, lam, u, v, hi, hL, hlam, _, hpos, huV, hvV, huv, huW, hvW, _, rfl⟩ :=
    push_data V f st st' hinv h
  have hord' : ∀ p ∈ (pushResult f V st i L lam u v).idx, IsOrdering V p.1 :=
    fun p hp => (hps.1.2.2.1 p hp).1
  set W := Wset f V st with hW
  set W' := Wset f V (pushResult f V st i L lam u v) with hW'
  set m := V.card with hm
  have hw01 := Finset.card_le_card hmono
  have hw1m : W'.card ≤ m := Finset.card_le_card (W_sub f V (pushResult f V st i L lam u v))
  have hX := Phi_le V (W' \ W) (Finset.sdiff_subset.trans (W_sub f V _)) _ hord'
  rw [Finset.card_sdiff_of_subset hmono] at hX
  have hsplit := Phi_split W W' hmono (pushResult f V st i L lam u v).idx
  have hswap := sum_pos_swap L W u v huW hvW hpos
  have hPL : ∑ w ∈ W, L.idxOf w ≤ m * m := by
    have := Phi_le V W (W_sub f V st) [(L, lam)]
      (by intro p hp; rw [List.mem_singleton] at hp; rw [hp]; exact hL)
    simp [Phi] at this
    nlinarith [Finset.card_le_card (W_sub f V st)]
  unfold Psi
  rw [← hW, ← hW', hsplit]
  set e := ec V f (greedy f L) u v
  set a := min st.delta (lam * e)
  by_cases hns : a < lam * e
  · have hv' : v ∈ W' := push_new_v V hV f hsub hf0 st hinv i L lam u v hpush huV hvV huv huW hns
    have hw1 : W.card + 1 ≤ W'.card := by
      have : insert v W ⊆ W' := Finset.insert_subset hv' hmono
      have := Finset.card_le_card this
      rw [Finset.card_insert_of_notMem hvW] at this; exact this
    have hidx : (pushResult f V st i L lam u v).idx =
        st.idx.set i (swapAdj L u v, a / e) ++ [(L, lam - a / e)] := by
      simp only [pushResult]; rw [if_pos hns]
    have hlen : (pushResult f V st i L lam u v).idx.length = st.idx.length + 1 := by
      rw [hidx]; simp
    have hset := list_sum_set_nat (fun p : List α × ℝ => ∑ w ∈ W, p.1.idxOf w) st.idx i
      (L, lam) (swapAdj L u v, a / e) hi
    have hPhi : Phi (pushResult f V st i L lam u v).idx W + 1 =
        Phi st.idx W + ∑ w ∈ W, L.idxOf w := by
      rw [hidx, Phi_append]; unfold Phi; dsimp only at hset ⊢; omega
    have hsecond : (pushResult f V st i L lam u v).idx.length + W.card ≤
        st.idx.length + W'.card := by rw [hlen]; omega
    rw [hlen] at hX ⊢
    refine ⟨?_, by rw [hlen] at hsecond; exact hsecond⟩
    exact arith_ns _ _ _ _ _ _ _ _ hw1 hw1m hPhi hPL hX
  · have hidx : (pushResult f V st i L lam u v).idx = st.idx.set i (swapAdj L u v, lam) := by
      simp only [pushResult]; rw [if_neg hns]
    have hlen : (pushResult f V st i L lam u v).idx.length = st.idx.length := by
      rw [hidx]; simp
    have hset := list_sum_set_nat (fun p : List α × ℝ => ∑ w ∈ W, p.1.idxOf w) st.idx i
      (L, lam) (swapAdj L u v, lam) hi
    have hPhi : Phi (pushResult f V st i L lam u v).idx W + 1 = Phi st.idx W := by
      rw [hidx]; unfold Phi; dsimp only at hset ⊢; omega
    have hsecond : (pushResult f V st i L lam u v).idx.length + W.card ≤
        st.idx.length + W'.card := by rw [hlen]; omega
    rw [hlen] at hX ⊢
    refine ⟨?_, by rw [hlen] at hsecond; exact hsecond⟩
    exact arith_sat _ _ _ _ _ _ _ hw01 hw1m hPhi hX

end Push


/-! ## Augmentations and phase starts -/

section Aug
variable {α : Type} [DecidableEq α]

/-- `z⁻(V)` -/
noncomputable def zneg (f : Finset α → ℝ) (V : Finset α) (st : PhaseState α) : ℝ :=
  xsum (xneg (zOf f V st)) V

theorem zsum (V : Finset α) (f : Finset α → ℝ) (hsub : SubmodularOn V f) (hf0 : f ∅ = 0)
    (st : PhaseState α) (hinv : PhaseInv V st) : ∑ v ∈ V, zOf f V st v = f V := by
  obtain ⟨_, _, hord, hsum, hskew, _⟩ := hinv
  have hx := X5IW.xOf_base V f hsub hf0 st hord hsum
  have h1 := hx.2.1
  unfold xsum at h1
  unfold zOf bdry
  rw [Finset.sum_sub_distrib, h1, X5IW.skew_sum_zero V st.phi hskew, sub_zero]

theorem zneg_le (V : Finset α) (f : Finset α → ℝ) (hsub : SubmodularOn V f) (hf0 : f ∅ = 0)
    (st : PhaseState α) (hinv : PhaseInv V st) : zneg f V st ≤ f V := by
  rw [← zsum V f hsub hf0 st hinv]
  unfold zneg xsum xneg
  exact Finset.sum_le_sum (fun v _ => min_le_right _ _)

theorem floor_step (K z δ : ℝ) (hδ : 0 < δ) (h : 0 ≤ (K - (z + δ)) / δ) :
    ⌊(K - (z + δ)) / δ⌋₊ + 1 = ⌊(K - z) / δ⌋₊ := by
  have e : (K - z) / δ = (K - (z + δ)) / δ + 1 := by field_simp; ring
  rw [e, Nat.floor_add_one h]

/-- the minimum value of `f` over the subsets of `V` -/
noncomputable def fmin (f : Finset α → ℝ) (V : Finset α) : ℝ :=
  V.powerset.inf' ⟨∅, Finset.empty_mem_powerset V⟩ f

theorem fmin_le (f : Finset α → ℝ) (V : Finset α) (X : Finset α) (hX : X ⊆ V) :
    fmin f V ≤ f X :=
  Finset.inf'_le _ (Finset.mem_powerset.mpr hX)

theorem fmin_mem (f : Finset α → ℝ) (V : Finset α) : ∃ X ⊆ V, f X = fmin f V := by
  obtain ⟨X, hX, e⟩ := Finset.exists_mem_eq_inf' ⟨∅, Finset.empty_mem_powerset V⟩ f
  exact ⟨X, Finset.mem_powerset.mp hX, e.symm⟩

/-- the two potentials bounding the augmentations: `⌊z⁺(V)/δ⌋` and
`⌊(min f + C(n,2)δ − z⁻(V))/δ⌋` -/
noncomputable def potP (f : Finset α → ℝ) (V : Finset α) (st : PhaseState α) : ℕ :=
  ⌊(f V - zneg f V st) / st.delta⌋₊

noncomputable def potM (f : Finset α → ℝ) (V : Finset α) (st : PhaseState α) : ℕ :=
  ⌊(fmin f V + ((V.card.choose 2 : ℕ) : ℝ) * st.delta - zneg f V st) / st.delta⌋₊

theorem aug_pot (V : Finset α) (hV : V.Nonempty) (f : Finset α → ℝ)
    (hsub : SubmodularOn V f) (hf0 : f ∅ = 0) (st st' : PhaseState α) (hinv : PhaseInv V st)
    (h : AugStep f V st st') :
    potP f V st' + 1 = potP f V st ∧ potM f V st' + 1 = potM f V st := by
  obtain ⟨hinv', hd, hz⟩ := X5IW.aug_step V f st st' hinv h
  have hδ := hinv.1
  have hz' : zneg f V st' = zneg f V st + st.delta := hz
  unfold potP potM
  rw [hd, hz']
  constructor
  · apply floor_step _ _ _ hδ
    apply div_nonneg _ hδ.le
    have := zneg_le V f hsub hf0 st' hinv'
    rw [hz'] at this; linarith
  · have e : fmin f V + ((V.card.choose 2 : ℕ) : ℝ) * st.delta - zneg f V st =
        (fmin f V + ((V.card.choose 2 : ℕ) : ℝ) * st.delta) - zneg f V st := rfl
    rw [e]
    apply floor_step _ _ _ hδ
    apply div_nonneg _ hδ.le
    obtain ⟨X, hX, hfX⟩ := fmin_mem f V
    obtain ⟨hδ', _, hord, hsum, hskew, hfeas⟩ := hinv'
    have hx := X5IW.xOf_base V f hsub hf0 st' hord hsum
    have := lemma_3_2 V hV f hsub hf0 _ hx st'.phi st'.delta hδ' hskew hfeas X hX
    have e2 : zneg f V st' = xsum (xneg (fun v => xOf f st' v - ∑ u ∈ V, st'.phi u v)) V := rfl
    rw [← e2, hz', hd, hfX] at this
    linarith

theorem push_pot (V : Finset α) (hV : V.Nonempty) (f : Finset α → ℝ)
    (hsub : SubmodularOn V f) (hf0 : f ∅ = 0) (st st' : PhaseState α) (hinv : PhaseInv V st)
    (h : PushStep f V st st') : potP f V st' = potP f V st ∧ potM f V st' = potM f V st := by
  obtain ⟨_, hd, hz⟩ := X5IW.push_step V hV f hsub hf0 st st' hinv h
  unfold potP potM zneg
  rw [hd, hz]; exact ⟨rfl, rfl⟩

/-- after the start of a phase that follows a completed phase, `potM ≤ n² + n` -/
theorem start_potM (V : Finset α) (hV : V.Nonempty) (f : Finset α → ℝ)
    (hsub : SubmodularOn V f) (hf0 : f ∅ = 0) (st : PhaseState α) (hinv : PhaseInv V st)
    (hend : PhaseEnd f V st) :
    potM f V (PhaseState.mk st.idx (clip st.phi (st.delta / 2)) (st.delta / 2) true) ≤
      V.card ^ 2 + V.card := by
  have hδ := hinv.1
  set st' : PhaseState α := PhaseState.mk st.idx (clip st.phi (st.delta / 2)) (st.delta / 2) true
  -- z⁻ at the end of the phase
  have hend' : fmin f V - (V.card : ℝ) * st.delta ≤ zneg f V st := by
    have L33 := lemma_3_3 V hV f hsub hf0 st hinv hend
    rcases hend with h | h | ⟨hZ, _⟩
    · have := (L33.1 h).2; unfold zneg; linarith [fmin_le f V ∅ (Finset.empty_subset _)]
    · have := (L33.2.1 h).2; unfold zneg; linarith [fmin_le f V V subset_rfl]
    · have ht := lemma_3_1 V hV f hsub hf0 st hinv hZ
      have := (L33.2.2 ht).2; unfold zneg; linarith [fmin_le f V _ (W_sub f V st)]
  -- clipping
  have hclip : zneg f V st - ((V.card.choose 2 : ℕ) : ℝ) * (st.delta / 2) ≤ zneg f V st' := by
    obtain ⟨_, _, _, _, hskew, hfeas⟩ := hinv
    have := X5IW.clip_zneg V (xOf f st) st.phi (st.delta / 2) (by linarith) hskew
      (fun u hu v hv => by
        have := hfeas u hu v hv; constructor <;> linarith)
    exact this
  unfold potM
  apply Nat.floor_le_of_le
  have hδ2 : (0 : ℝ) < st'.delta := by show 0 < st.delta / 2; linarith
  rw [div_le_iff₀ hδ2]
  have hc : ((V.card.choose 2 : ℕ) : ℝ) = (V.card : ℝ) * ((V.card : ℝ) - 1) / 2 :=
    Nat.cast_choose_two ℝ V.card
  show fmin f V + ((V.card.choose 2 : ℕ) : ℝ) * (st.delta / 2) - zneg f V st' ≤
    (((V.card ^ 2 + V.card : ℕ) : ℝ)) * (st.delta / 2)
  push_cast
  rw [hc] at hclip ⊢
  nlinarith

/-- after the first phase start, `potP ≤ 2n` -/
theorem start_potP (V : Finset α) (f : Finset α → ℝ) (hsub : SubmodularOn V f) (hf0 : f ∅ = 0)
    (L : List α) (hL : IsOrdering V L) (η : ℝ) (hη : 0 < η)
    (hxη : ∀ v ∈ V, greedy f L v ≤ η) :
    potP f V (PhaseState.mk [(L, 1)] (clip (fun _ _ => 0) (η / 2)) (η / 2) true) ≤
      2 * V.card := by
  set st' : PhaseState α := PhaseState.mk [(L, 1)] (clip (fun _ _ => 0) (η / 2)) (η / 2) true
  have hz : ∀ v, zOf f V st' v = greedy f L v := by
    intro v
    unfold zOf bdry xOf
    simp [st', clip]
    have : max (-(η / 2)) (min (η / 2) 0) = 0 := by
      rw [min_eq_right (by linarith), max_eq_right (by linarith)]
    simp [this]
  have hb := X5IW.greedy_base V f hsub hf0 L hL
  have hfV : f V = ∑ v ∈ V, greedy f L v := hb.2.1.symm
  unfold potP
  apply Nat.floor_le_of_le
  have hδ2 : (0 : ℝ) < st'.delta := by show 0 < η / 2; linarith
  rw [div_le_iff₀ hδ2]
  show f V - zneg f V st' ≤ ((2 * V.card : ℕ) : ℝ) * (η / 2)
  unfold zneg xsum xneg
  simp only [hz]
  rw [hfV, ← Finset.sum_sub_distrib]
  have : ∀ v ∈ V, greedy f L v - min 0 (greedy f L v) ≤ η := by
    intro v hv
    have := hxη v hv
    rcases le_total 0 (greedy f L v) with h | h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h]; linarith
  calc ∑ v ∈ V, (greedy f L v - min 0 (greedy f L v)) ≤ ∑ v ∈ V, η := Finset.sum_le_sum this
    _ = ((2 * V.card : ℕ) : ℝ) * (η / 2) := by
      rw [Finset.sum_const, nsmul_eq_mul]; push_cast; ring

/-- after a reduction, at most `n + 1` indices remain -/
theorem aug_card (V : Finset α) (f : Finset α → ℝ) (st st' : PhaseState α)
    (hinv : PhaseInv V st) (h : AugStep f V st st') : st'.idx.length ≤ V.card + 1 := by
  have hinv' := (X5IW.aug_step V f st st' hinv h).1
  obtain ⟨_, _, _, P, _, hred⟩ := h
  obtain ⟨_, _, _, _, _, _, _, hai⟩ := hred
  apply card_le_of_affInd V _ hai
  intro j a ha
  have hL := (hinv'.2.2.1 (st'.idx.get j) (List.get_mem _ _)).1
  unfold greedy
  rw [if_neg (fun h => ha ((hL.2 a).mp h))]

end Aug

end IFT



open IwataFF.SFM MainState

namespace IFT

variable {n : ℕ}

theorem neg_set (s : MainState n) (hP : IFP.PInv s) (fr : Bool) (u : Finset (Fin n)) (η : ℝ)
    (ph : PhaseState (Finset (Fin n))) (hm : s.mode = Mode.fix fr u η ph) :
    ∃ Y ⊆ s.fixGround fr u, s.fixFun fr u Y ≤ -(η / 2) := by
  obtain ⟨hη, hRu, hfr, htop⟩ := hP.fi fr u η ph hm
  have hRb := X5TC.R_sub s u
  cases fr with
  | true =>
    refine ⟨s.blocks \ s.R u, by simp [MainState.fixGround], ?_⟩
    simp only [MainState.fixFun, ↓reduceIte, restrictFun]
    rw [Finset.sdiff_union_of_subset hRb]
    have : η / 2 ≤ s.curFun (s.R u) := by simpa using hfr.symm
    linarith
  | false =>
    refine ⟨(s.R u).erase u, ?_, ?_⟩
    · simp only [MainState.fixGround, Bool.false_eq_true, ↓reduceIte]
      exact (Finset.erase_subset _ _).trans hRb
    · simp only [MainState.fixFun, Bool.false_eq_true, ↓reduceIte]
      have : ¬ (η / 2 ≤ s.curFun (s.R u)) := by simpa using hfr.symm
      push_neg at this
      linarith

theorem ground_nonempty (s : MainState n) (hP : IFP.PInv s) (fr : Bool) (u : Finset (Fin n))
    (η : ℝ) (ph : PhaseState (Finset (Fin n))) (hm : s.mode = Mode.fix fr u η ph) :
    (s.fixGround fr u).Nonempty := by
  obtain ⟨Y, hY, hfY⟩ := neg_set s hP fr u η ph hm
  have hη := (hP.fi fr u η ph hm).1
  rcases Y.eq_empty_or_nonempty with rfl | ⟨y, hy⟩
  · have := (X5TC.fix_sub s hP.g fr u).2; rw [this] at hfY; linarith
  · exact ⟨y, hY hy⟩

theorem blocks_card (s : MainState n) (hI : X5FC.Inv s) : s.blocks.card ≤ n := by
  have h1 : (s.blocks.biUnion id).card = ∑ A ∈ s.blocks, A.card :=
    Finset.card_biUnion (fun A hA B hB hAB => hI.disj A hA B hB hAB)
  have h2 : ∑ A ∈ s.blocks, 1 ≤ ∑ A ∈ s.blocks, A.card :=
    Finset.sum_le_sum (fun A hA => (hI.ne A hA).card_pos)
  have h3 : (s.blocks.biUnion id).card ≤ n := by
    simpa using Finset.card_le_univ (s.blocks.biUnion id)
  simp at h2
  omega

theorem ground_card (s : MainState n) (hI : X5FC.Inv s) (fr : Bool) (u : Finset (Fin n)) :
    (s.fixGround fr u).card ≤ n := by
  have : s.fixGround fr u ⊆ s.blocks := by
    unfold MainState.fixGround; split_ifs
    · exact Finset.sdiff_subset
    · exact subset_rfl
  exact (Finset.card_le_card this).trans (blocks_card s hI)

/-- the extreme base `Fix` starts from satisfies `x(v) ≤ η` (§4, p. 13). -/
theorem first_bound (t : MainState n) (hG : X5TC.GInv t) (fr : Bool) (u : Finset (Fin n))
    (hu : u ∈ t.blocks) (L : List (Finset (Fin n))) (hL : IsOrdering (t.fixGround fr u) L)
    (hcons : IsConsistent t.arcs L) :
    ∀ v ∈ t.fixGround fr u, greedy (t.fixFun fr u) L v ≤ etaVal t.blocks t.arcs t.curFun := by
  intro v hv
  have hne : t.blocks.Nonempty := ⟨u, hu⟩
  have heta : t.curFun (t.R v) - t.curFun ((t.R v).erase v) ≤
      etaVal t.blocks t.arcs t.curFun := by
    have hvb : v ∈ t.blocks := by
      unfold MainState.fixGround at hv; split_ifs at hv
      · exact (Finset.mem_sdiff.mp hv).1
      · exact hv
    unfold etaVal; rw [dif_pos hne]
    exact Finset.le_sup' (fun v => t.curFun (reach t.blocks t.arcs v) -
      t.curFun ((reach t.blocks t.arcs v).erase v)) hvb
  obtain ⟨hsub', hz'⟩ := X5TC.fix_sub t hG fr u
  have hV' : (t.fixGround fr u).Nonempty := ⟨v, hv⟩
  cases fr with
  | false =>
    have hF : ∀ e ∈ t.arcs, e.1 ∈ t.fixGround false u ∧ e.2 ∈ t.fixGround false u := by
      intro e he; simpa [MainState.fixGround] using hG.base.arcs e he
    have := consistent_base_bound _ hV' _ hsub' hz' t.arcs hF L hL hcons v hv
    simp only [MainState.fixGround, MainState.fixFun, Bool.false_eq_true, ↓reduceIte] at this
    exact this.trans heta
  | true =>
    classical
    set V' := t.fixGround true u with hV'def
    have hV'e : V' = t.blocks \ t.R u := by simp [hV'def, MainState.fixGround]
    set F' := t.arcs.filter (fun e => e.1 ∈ V' ∧ e.2 ∈ V') with hF'
    have hF : ∀ e ∈ F', e.1 ∈ V' ∧ e.2 ∈ V' := fun e he => (Finset.mem_filter.mp he).2
    have hcons' : IsConsistent F' L := by
      intro i j hij a b ha hb hab
      exact hcons i j hij a b ha hb (Finset.mem_filter.mp hab).1
    have hcb := consistent_base_bound _ hV' _ hsub' hz' F' hF L hL hcons' v hv
    refine hcb.trans (le_trans ?_ heta)
    set R' := reach V' F' v with hR'
    simp only [MainState.fixFun, ↓reduceIte, restrictFun]
    have hRu := X5TC.R_sub t u
    have hvV : v ∈ t.blocks \ t.R u := hV'e ▸ hv
    rw [Finset.mem_sdiff] at hvV
    have hvR' : v ∈ R' := by
      rw [hR', X5FC.mem_reach]; exact ⟨hv, .refl⟩
    have hR'V : R' ⊆ V' := by
      intro b hb; rw [hR', X5FC.mem_reach] at hb; exact hb.1
    -- R(v) \ {v} ⊆ (R' \ {v}) ∪ R(u)
    have hclosed : ∀ X Y, X ∈ t.R u → (X, Y) ∈ t.arcs → Y ∈ t.R u := by
      intro X Y hX hXY
      rw [IFA.mem_R] at hX ⊢
      exact ⟨(hG.base.arcs _ hXY).2, hX.2.tail hXY⟩
    have hpath : ∀ c, Relation.ReflTransGen (IFA.ar t.arcs) v c → c ∉ t.R u →
        Relation.ReflTransGen (fun a c => (a, c) ∈ F') v c := by
      intro c hc
      induction hc with
      | refl => intro _; exact .refl
      | @tail b c hb hbc ih =>
        intro hcR
        have hbR : b ∉ t.R u := fun h => hcR (hclosed _ _ h hbc)
        refine (ih hbR).tail ?_
        have hbc' := hG.base.arcs _ hbc
        rw [hF', Finset.mem_filter, hV'e]
        exact ⟨hbc, Finset.mem_sdiff.mpr ⟨hbc'.1, hbR⟩, Finset.mem_sdiff.mpr ⟨hbc'.2, hcR⟩⟩
    have hA : (t.R v).erase v ⊆ R'.erase v ∪ t.R u := by
      intro b hb
      rw [Finset.mem_erase] at hb
      by_cases hbR : b ∈ t.R u
      · exact Finset.mem_union_right _ hbR
      · apply Finset.mem_union_left
        rw [Finset.mem_erase]
        refine ⟨hb.1, ?_⟩
        rw [IFA.mem_R] at hb
        rw [hR', X5FC.mem_reach]
        exact ⟨hV'e ▸ Finset.mem_sdiff.mpr ⟨hb.2.1, hbR⟩, hpath b hb.2.2 hbR⟩
    have hvB : v ∉ R'.erase v ∪ t.R u := by
      rw [Finset.mem_union, Finset.mem_erase]; push_neg; exact ⟨fun h => absurd rfl h, hvV.2⟩
    have hRvb : t.R v ⊆ t.blocks := X5TC.R_sub t v
    have hBb : R'.erase v ∪ t.R u ⊆ t.blocks := by
      apply Finset.union_subset _ hRu
      intro b hb; exact (Finset.mem_sdiff.mp (hV'e ▸ hR'V (Finset.mem_of_mem_erase hb))).1
    have hsm := hG.sub (t.R v) hRvb (R'.erase v ∪ t.R u) hBb
    have e1 : t.R v ∪ (R'.erase v ∪ t.R u) = R' ∪ t.R u := by
      ext b
      simp only [Finset.mem_union, Finset.mem_erase]
      constructor
      · rintro (h | ⟨_, h⟩ | h)
        · by_cases hbv : b = v
          · left; rw [hbv]; exact hvR'
          · rcases Finset.mem_union.mp (hA (Finset.mem_erase.mpr ⟨hbv, h⟩)) with h' | h'
            · left; exact Finset.mem_of_mem_erase h'
            · right; exact h'
        · left; exact h
        · right; exact h
      · rintro (h | h)
        · by_cases hbv : b = v
          · left; rw [hbv]; exact X5TC.R_self t v hvV.1
          · right; left; exact ⟨hbv, h⟩
        · right; right; exact h
    have e2 : t.R v ∩ (R'.erase v ∪ t.R u) = (t.R v).erase v := by
      ext b
      constructor
      · intro h
        rw [Finset.mem_inter] at h
        rw [Finset.mem_erase]
        exact ⟨fun e => hvB (e ▸ h.2), h.1⟩
      · intro h
        exact Finset.mem_inter.mpr ⟨Finset.mem_of_mem_erase h, hA h⟩
    rw [e1, e2] at hsm
    have e3 : R'.erase v ∪ t.R u = (R'.erase v) ∪ t.R u := rfl
    linarith


/-! ## The potentials of one call of `Fix` -/

def hl (q : ℕ) : ℕ := if q = 0 then 0 else Nat.log 2 q + 1

theorem hl_half (q : ℕ) (hq : 1 ≤ q) : hl (q / 2) + 1 = hl q := by
  unfold hl
  rcases Nat.lt_or_ge q 2 with h | h
  · have : q = 1 := by omega
    subst this; simp
  · have h1 : q / 2 ≠ 0 := by omega
    have h2 : 0 < Nat.log 2 q := Nat.log_pos (by norm_num) h
    rw [if_neg h1, if_neg (by omega), Nat.log_div_base]; omega

theorem hl_mono {a b : ℕ} (h : a ≤ b) : hl a ≤ hl b := by
  unfold hl
  split_ifs with h1 h2
  · exact le_rfl
  · exact Nat.zero_le _
  · omega
  · have := Nat.log_mono_right (b := 2) h; omega

section Session
variable {α : Type} [DecidableEq α]

/-- `⌊2 n³ δ / η⌋`: the phases still allowed in this call of `Fix` -/
noncomputable def qS (V : Finset α) (η : ℝ) (ph : PhaseState α) : ℕ :=
  ⌊2 * (V.card : ℝ) ^ 3 * ph.delta / η⌋₊

noncomputable def gA' (f : Finset α → ℝ) (V : Finset α) (ph : PhaseState α) : ℕ :=
  if ph.begun then min (potP f V ph) (potM f V ph) else 0

/-- the invariant of a call of `Fix` -/
structure J (f : Finset α → ℝ) (V : Finset α) (η : ℝ) (ph : PhaseState α) : Prop where
  inv : PhaseInv V ph
  first : ph.begun = false → ∃ L, ph = initPhase L η ∧ IsOrdering V L ∧
    ∀ v ∈ V, greedy f L v ≤ η
  qle : hl (qS V η ph) ≤ hl (2 * V.card ^ 3)
  card : ph.idx.length ≤ (Wset f V ph).card +
    (V.card + 1) * (hl (2 * V.card ^ 3) + 1 - hl (qS V η ph))

variable (V : Finset α) (hV : V.Nonempty) (f : Finset α → ℝ) (hsub : SubmodularOn V f)
  (hf0 : f ∅ = 0) (η : ℝ) (hη : 0 < η)
include hV hsub hf0 hη

theorem J_init (L : List α) (hL : IsOrdering V L) (hb : ∀ v ∈ V, greedy f L v ≤ η) :
    J f V η (initPhase L η) ∧ hl (qS V η (initPhase L η)) = hl (2 * V.card ^ 3) ∧
      gA' f V (initPhase L η) = 0 ∧ Psi f V (initPhase L η) ≤ 2 * V.card * V.card * (1 + V.card) := by
  have hq : qS V η (initPhase L η) = 2 * V.card ^ 3 := by
    unfold qS
    have : 2 * (V.card : ℝ) ^ 3 * (initPhase L η).delta / η = ((2 * V.card ^ 3 : ℕ) : ℝ) := by
      simp only [initPhase]; push_cast; field_simp
    rw [this, Nat.floor_natCast]
  have hinv : PhaseInv V (initPhase L η) := by
    refine ⟨hη, by simp [initPhase], ?_, by simp [initPhase], ?_, ?_⟩
    · intro p hp
      simp only [initPhase, List.mem_singleton] at hp
      subst hp
      exact ⟨hL, one_pos⟩
    · intro a _ b _; simp [initPhase]
    · intro a _ b _; simp only [initPhase]; constructor <;> linarith
  refine ⟨⟨hinv, fun _ => ⟨L, rfl, hL, hb⟩, by rw [hq], ?_⟩, by rw [hq], by simp [gA', initPhase], ?_⟩
  · rw [hq]; simp [initPhase]; omega
  · have := Psi_le f V (initPhase L η) (fun p hp => (hinv.2.2.1 p hp).1)
    simpa [initPhase] using this

theorem J_start (ph ph' : PhaseState α) (hJ : J f V η ph) (h : StartStep f V ph ph')
    (hc : ph.begun = false ∨ η / 2 / (V.card : ℝ) ^ 3 ≤ ph.delta) :
    J f V η ph' ∧ hl (qS V η ph') + 1 = hl (qS V η ph) ∧ gA' f V ph' ≤ V.card ^ 2 + V.card ∧
      Psi f V ph' ≤ 2 * V.card * V.card *
        ((V.card + (V.card + 1) * (hl (2 * V.card ^ 3) + 1)) + V.card) := by
  obtain ⟨hcond, rfl⟩ := h
  have hδ := hJ.inv.1
  have hm1 : 1 ≤ V.card := hV.card_pos
  have hm1' : (1 : ℝ) ≤ V.card := by exact_mod_cast hm1
  set ph' : PhaseState α := PhaseState.mk ph.idx (clip ph.phi (ph.delta / 2)) (ph.delta / 2)
    true with hph'
  have hinv' : PhaseInv V ph' := X5TC.clip_inv V ph hJ.inv
  -- the phase counter halves
  have hq : qS V η ph' = qS V η ph / 2 := by
    unfold qS
    have : 2 * (V.card : ℝ) ^ 3 * ph'.delta / η = (2 * (V.card : ℝ) ^ 3 * ph.delta / η) / (2 : ℕ) := by
      simp only [hph']; push_cast; ring
    rw [this, Nat.floor_div_natCast]
  have hq1 : 1 ≤ qS V η ph := by
    unfold qS
    rw [Nat.one_le_floor_iff]
    rcases hc with hb | hd
    · obtain ⟨L, rfl, _, _⟩ := hJ.first hb
      simp only [initPhase]
      rw [le_div_iff₀ hη]
      have : (1 : ℝ) ≤ (V.card : ℝ) ^ 3 := one_le_pow₀ hm1'
      nlinarith
    · rw [le_div_iff₀ hη]
      have hc3 : (0 : ℝ) < (V.card : ℝ) ^ 3 := by positivity
      rw [div_le_iff₀ hc3] at hd
      nlinarith
  have hhl : hl (qS V η ph') + 1 = hl (qS V η ph) := by rw [hq]; exact hl_half _ hq1
  have hJq := hJ.qle
  have hJc := hJ.card
  have hWm : (Wset f V ph).card ≤ V.card := Finset.card_le_card (W_sub f V ph)
  have hlen : ph'.idx.length ≤ V.card + (V.card + 1) * (hl (2 * V.card ^ 3) + 1) := by
    have : (V.card + 1) * (hl (2 * V.card ^ 3) + 1 - hl (qS V η ph)) ≤
        (V.card + 1) * (hl (2 * V.card ^ 3) + 1) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    show ph.idx.length ≤ _
    omega
  refine ⟨⟨hinv', fun h => by simp [hph'] at h, by omega, ?_⟩, hhl, ?_, ?_⟩
  · show ph.idx.length ≤ _
    have e : hl (2 * V.card ^ 3) + 1 - hl (qS V η ph') =
        (hl (2 * V.card ^ 3) + 1 - hl (qS V η ph)) + 1 := by omega
    rw [e, Nat.mul_add, Nat.mul_one]
    omega
  · unfold gA'
    simp only [hph', if_true]
    rcases hcond with hb | hend
    · obtain ⟨L, hL0, hLo, hLb⟩ := hJ.first hb
      subst hL0
      have := start_potP V f hsub hf0 L hLo η hη hLb
      simp only [initPhase] at this ⊢
      have h2 : 2 * V.card ≤ V.card ^ 2 + V.card := by nlinarith
      exact (min_le_left _ _).trans (this.trans h2)
    · exact (min_le_right _ _).trans (start_potM V hV f hsub hf0 ph hJ.inv hend)
  · have := Psi_le f V ph' (fun p hp => (hinv'.2.2.1 p hp).1)
    exact this.trans (Nat.mul_le_mul_left _ (by omega))

theorem J_push (ph ph' : PhaseState α) (hJ : J f V η ph) (h : PushStep f V ph ph') :
    J f V η ph' ∧ qS V η ph' = qS V η ph ∧ gA' f V ph' = gA' f V ph ∧
      Psi f V ph' + 1 ≤ Psi f V ph := by
  obtain ⟨hinv', hd, _⟩ := X5IW.push_step V hV f hsub hf0 ph ph' hJ.inv h
  obtain ⟨hpsi, hcard⟩ := push_psi V hV f hsub hf0 ph ph' hJ.inv h
  obtain ⟨hpP, hpM⟩ := push_pot V hV f hsub hf0 ph ph' hJ.inv h
  have hbeg : ph'.begun = ph.begun := by
    obtain ⟨i, L, lam, u, v, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := push_data V f ph ph' hJ.inv h
    rfl
  have hq : qS V η ph' = qS V η ph := by unfold qS; rw [hd]
  have hb : ph.begun = true := h.1
  refine ⟨⟨hinv', (fun h' => by rw [hbeg, hb] at h'; cases h'), (by rw [hq]; exact hJ.qle), ?_⟩,
    hq, (by unfold gA'; rw [hbeg, hpP, hpM]), hpsi⟩
  rw [hq]
  have := hJ.card
  omega

theorem J_aug (ph ph' : PhaseState α) (hJ : J f V η ph) (h : AugStep f V ph ph') :
    J f V η ph' ∧ qS V η ph' = qS V η ph ∧ gA' f V ph' + 1 = gA' f V ph ∧
      Psi f V ph' ≤ 2 * V.card * V.card * ((V.card + 1) + V.card) := by
  obtain ⟨hinv', hd, _⟩ := X5IW.aug_step V f ph ph' hJ.inv h
  obtain ⟨hpP, hpM⟩ := aug_pot V hV f hsub hf0 ph ph' hJ.inv h
  have hcard := aug_card V f ph ph' hJ.inv h
  have hb : ph.begun = true := h.1
  have hbeg : ph'.begun = ph.begun := by
    obtain ⟨_, _, _, P, _, hred⟩ := h
    exact hred.2.2.1
  have hq : qS V η ph' = qS V η ph := by unfold qS; rw [hd]
  have hJq := hJ.qle
  refine ⟨⟨hinv', (fun h' => by rw [hbeg, hb] at h'; cases h'), (by rw [hq]; exact hJ.qle), ?_⟩,
    hq, ?_, ?_⟩
  · rw [hq]
    have : V.card + 1 ≤ (V.card + 1) * (hl (2 * V.card ^ 3) + 1 - hl (qS V η ph)) :=
      Nat.le_mul_of_pos_right _ (by omega)
    omega
  · unfold gA'; rw [hbeg, hb, if_pos rfl, if_pos rfl, ← hpP, ← hpM, min_add_add_right]
  · have := Psi_le f V ph' (fun p hp => (hinv'.2.2.1 p hp).1)
    exact this.trans (Nat.mul_le_mul_left _ (by omega))

end Session


/-! ## Potentials on the states of Figure 3 -/

noncomputable def gS (s : MainState n) : ℕ :=
  match s.mode with
  | Mode.fix fr u η ph => hl (qS (s.fixGround fr u) η ph)
  | _ => 0

noncomputable def gA (s : MainState n) : ℕ :=
  match s.mode with
  | Mode.fix fr u _ ph => gA' (s.fixFun fr u) (s.fixGround fr u) ph
  | _ => 0

noncomputable def gP (s : MainState n) : ℕ :=
  match s.mode with
  | Mode.fix fr u _ ph => Psi (s.fixFun fr u) (s.fixGround fr u) ph
  | _ => 0

def isFix (s : MainState n) : ℕ :=
  match s.mode with
  | Mode.fix _ _ _ _ => 1
  | _ => 0

def notDone (s : MainState n) : ℕ :=
  match s.mode with
  | Mode.done _ => 0
  | _ => 1

theorem gS_fix (s : MainState n) (fr u η ph) (hm : s.mode = Mode.fix fr u η ph) :
    gS s = hl (qS (s.fixGround fr u) η ph) := by simp [gS, hm]
theorem gA_fix (s : MainState n) (fr u η ph) (hm : s.mode = Mode.fix fr u η ph) :
    gA s = gA' (s.fixFun fr u) (s.fixGround fr u) ph := by simp [gA, hm]
theorem gP_fix (s : MainState n) (fr u η ph) (hm : s.mode = Mode.fix fr u η ph) :
    gP s = Psi (s.fixFun fr u) (s.fixGround fr u) ph := by simp [gP, hm]
theorem gS_loop (s : MainState n) (hm : s.mode = Mode.loop) : gS s = 0 := by simp [gS, hm]
theorem gA_loop (s : MainState n) (hm : s.mode = Mode.loop) : gA s = 0 := by simp [gA, hm]
theorem gP_loop (s : MainState n) (hm : s.mode = Mode.loop) : gP s = 0 := by simp [gP, hm]
theorem gS_done (s : MainState n) (X) (hm : s.mode = Mode.done X) : gS s = 0 := by simp [gS, hm]
theorem gA_done (s : MainState n) (X) (hm : s.mode = Mode.done X) : gA s = 0 := by simp [gA, hm]
theorem gP_done (s : MainState n) (X) (hm : s.mode = Mode.done X) : gP s = 0 := by simp [gP, hm]

def TInv (s : MainState n) : Prop :=
  ∀ fr u η ph, s.mode = Mode.fix fr u η ph → J (s.fixFun fr u) (s.fixGround fr u) η ph

def StartK (s s' : MainState n) : Prop :=
  ∃ fr u η ph ph', s.mode = Mode.fix fr u η ph ∧
    StartStep (s.fixFun fr u) (s.fixGround fr u) ph ph' ∧
    (ph.begun = false ∨ η / 2 / ((s.fixGround fr u).card : ℝ) ^ 3 ≤ ph.delta) ∧
    s' = { s with mode := Mode.fix fr u η ph' }

def PushK (s s' : MainState n) : Prop :=
  ∃ fr u η ph ph', s.mode = Mode.fix fr u η ph ∧
    PushStep (s.fixFun fr u) (s.fixGround fr u) ph ph' ∧ s' = { s with mode := Mode.fix fr u η ph' }

def AugK (s s' : MainState n) : Prop :=
  ∃ fr u η ph ph', s.mode = Mode.fix fr u η ph ∧
    AugStep (s.fixFun fr u) (s.fixGround fr u) ph ph' ∧ s' = { s with mode := Mode.fix fr u η ph' }

theorem fix_kinds (s s' : MainState n) (h : FixPhaseStep s s') :
    StartK s s' ∨ PushK s s' ∨ AugK s s' := by
  obtain ⟨fr, u, η, ph, ph', hm, hin, rfl⟩ := h
  rcases hin with ⟨h1, h2⟩ | h1 | h1
  · left; exact ⟨fr, u, η, ph, ph', hm, h1, h2, rfl⟩
  · right; left; exact ⟨fr, u, η, ph, ph', hm, h1, rfl⟩
  · right; right; exact ⟨fr, u, η, ph, ph', hm, h1, rfl⟩

/-- the data for one call of `Fix` in a reachable state -/
theorem fix_ctx (s : MainState n) (hP : IFP.PInv s) (fr u η ph)
    (hm : s.mode = Mode.fix fr u η ph) :
    (s.fixGround fr u).Nonempty ∧ SubmodularOn (s.fixGround fr u) (s.fixFun fr u) ∧
      s.fixFun fr u ∅ = 0 ∧ 0 < η ∧ (s.fixGround fr u).card ≤ n :=
  ⟨ground_nonempty s hP fr u η ph hm, (X5TC.fix_sub s hP.g fr u).1, (X5TC.fix_sub s hP.g fr u).2,
    (hP.fi fr u η ph hm).1, ground_card s hP.g.base fr u⟩

theorem step_tinv (s s' : MainState n) (hP : IFP.PInv s) (hT : TInv s) (h : Step s s') :
    TInv s' := by
  have hP' := IFP.step_pinv s s' hP h
  rcases h with hfin | hcall | hfix | hret
  · obtain ⟨_, ⟨_, e⟩ | ⟨_, _, e⟩⟩ := hfin <;> subst e <;> intro fr u η ph h <;> simp at h
  · obtain ⟨_, _, _, u, L, hu, _, rest⟩ := hcall
    simp only at rest
    obtain ⟨hL, hcons, e⟩ := rest
    intro fr' u' η' ph' hm'
    have hm'' := hm'
    rw [e] at hm''
    simp only [Mode.fix.injEq] at hm''
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hm''
    obtain ⟨hV, hsub, hz, hη, _⟩ := fix_ctx s' hP' _ _ _ _ hm'
    subst e
    exact (J_init _ hV _ hsub hz _ hη L hL
      (first_bound _ hP'.g _ u hu L hL hcons)).1
  · obtain ⟨fr, u, η, ph, ph', hm, hin, e⟩ := hfix
    obtain ⟨hV, hsub, hz, hη, _⟩ := fix_ctx s hP fr u η ph hm
    have hJ := hT fr u η ph hm
    intro fr' u' η' ph'' hm'
    rw [e] at hm'
    simp only [Mode.fix.injEq] at hm'
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hm'
    subst e
    rcases hin with ⟨h1, h2⟩ | h1 | h1
    · exact (J_start _ hV _ hsub hz _ hη ph _ hJ h1 h2).1
    · exact (J_push _ hV _ hsub hz _ hη ph _ hJ h1).1
    · exact (J_aug _ hV _ hsub hz _ hη ph _ hJ h1).1
  · obtain ⟨fr, u, η, ph, w, hm, hout, hcase⟩ := hret
    rcases hcase with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, rfl⟩ <;> intro fr u η ph h <;>
      simp [MainState.contract, MainState.addArc, MainState.delete] at h

theorem reach_inv (f : Finset (Fin n) → ℝ) (hsub : SubmodularOn Finset.univ f) (hf0 : f ∅ = 0)
    (s : MainState n) (hs : Relation.ReflTransGen Step (initMain f) s) :
    IFP.PInv s ∧ TInv s := by
  induction hs with
  | refl =>
    exact ⟨IFP.reach_pinv f hsub hf0 _ .refl, by intro fr u η ph h; simp [initMain] at h⟩
  | @tail a b hr hst ih => exact ⟨IFP.step_pinv _ _ ih.1 hst, step_tinv _ _ ih.1 ih.2 hst⟩

end IFT



open IwataFF.SFM MainState

namespace IFT

variable {n : ℕ}

theorem step_cases (s s' : MainState n) (h : Step s s') :
    FinishStep s s' ∨ CallStep s s' ∨ StartK s s' ∨ PushK s s' ∨ AugK s s' ∨ ReturnStep s s' := by
  rcases h with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · rcases fix_kinds s s' h with h | h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

theorem finish_mode (s s' : MainState n) (h : FinishStep s s') : ∃ X, s'.mode = Mode.done X := by
  obtain ⟨_, ⟨_, e⟩ | ⟨_, _, e⟩⟩ := h <;> subst e <;> exact ⟨_, rfl⟩

theorem return_mode (s s' : MainState n) (h : ReturnStep s s') : s'.mode = Mode.loop := by
  obtain ⟨fr, u, η, ph, w, hm, hout, hcase⟩ := h
  rcases hcase with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, rfl⟩ <;> rfl

/-- the facts about a call of `Fix` -/
theorem call_facts (s s' : MainState n) (hP : IFP.PInv s) (h : CallStep s s') :
    s.mode = Mode.loop ∧ gS s' ≤ hl (2 * n ^ 3) ∧ gA s' = 0 ∧
      gP s' ≤ 2 * n * n * (1 + n) ∧ isFix s' = 1 ∧ notDone s' = 1 := by
  have hP' := IFP.step_pinv s s' hP (Or.inr (Or.inl h))
  obtain ⟨hm, _, _, u, L, hu, _, rest⟩ := h
  simp only at rest
  obtain ⟨hL, hcons, e⟩ := rest
  set η := etaVal s.cap.blocks s.cap.arcs s.cap.curFun
  set fr := decide (η / 2 ≤ s.cap.curFun (s.cap.R u))
  have hm' : s'.mode = Mode.fix fr u η (initPhase L η) := by rw [e]
  obtain ⟨hV, hsub, hz, hη, hmn⟩ := fix_ctx s' hP' _ _ _ _ hm'
  have hfb := first_bound s' hP'.g fr u (by rw [e]; exact hu) L (by rw [e]; exact hL)
    (by rw [e]; exact hcons)
  have hη' : etaVal s'.blocks s'.arcs s'.curFun = η := by rw [e]; rfl
  rw [hη'] at hfb
  obtain ⟨_, h1, h2, h3⟩ := J_init _ hV _ hsub hz _ hη L (by rw [e]; exact hL) hfb
  refine ⟨hm, ?_, ?_, ?_, by simp [isFix, hm'], by simp [notDone, hm']⟩
  · rw [gS_fix s' _ _ _ _ hm', h1]
    exact hl_mono (by have := Nat.pow_le_pow_left hmn 3; omega)
  · rw [gA_fix s' _ _ _ _ hm', h2]
  · rw [gP_fix s' _ _ _ _ hm']
    refine h3.trans ?_
    have := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hmn) hmn) (Nat.add_le_add_left hmn 1)
    simpa [mul_assoc] using this

theorem start_facts (s s' : MainState n) (hP : IFP.PInv s) (hT : TInv s) (h : StartK s s') :
    gS s' + 1 = gS s ∧ gA s' ≤ n ^ 2 + n ∧
      gP s' ≤ 2 * n * n * ((n + (n + 1) * (hl (2 * n ^ 3) + 1)) + n) ∧
      isFix s' = isFix s ∧ notDone s' = notDone s := by
  obtain ⟨fr, u, η, ph, ph', hm, hst, hc, rfl⟩ := h
  obtain ⟨hV, hsub, hz, hη, hmn⟩ := fix_ctx s hP fr u η ph hm
  obtain ⟨_, h1, h2, h3⟩ := J_start _ hV _ hsub hz _ hη ph ph' (hT fr u η ph hm) hst hc
  have hm' : ({ s with mode := Mode.fix fr u η ph' } : MainState n).mode = Mode.fix fr u η ph' := rfl
  refine ⟨?_, ?_, ?_, by simp [isFix, hm], by simp [notDone, hm]⟩
  · rw [gS_fix _ _ _ _ _ hm', gS_fix s _ _ _ _ hm]; exact h1
  · rw [gA_fix _ _ _ _ _ hm']
    refine h2.trans ?_
    have := Nat.pow_le_pow_left hmn 2; omega
  · rw [gP_fix _ _ _ _ _ hm']
    refine h3.trans ?_
    set m := (s.fixGround fr u).card
    have hh : hl (2 * m ^ 3) ≤ hl (2 * n ^ 3) :=
      hl_mono (by have := Nat.pow_le_pow_left hmn 3; omega)
    have k1 : (m + (m + 1) * (hl (2 * m ^ 3) + 1)) + m ≤
        (n + (n + 1) * (hl (2 * n ^ 3) + 1)) + n := by
      have := Nat.mul_le_mul (Nat.add_le_add_right hmn 1) (Nat.add_le_add_right hh 1)
      omega
    exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hmn) hmn) k1

theorem push_facts (s s' : MainState n) (hP : IFP.PInv s) (hT : TInv s) (h : PushK s s') :
    gS s' = gS s ∧ gA s' = gA s ∧ gP s' + 1 ≤ gP s ∧ isFix s' = isFix s ∧
      notDone s' = notDone s := by
  obtain ⟨fr, u, η, ph, ph', hm, hst, rfl⟩ := h
  obtain ⟨hV, hsub, hz, hη, hmn⟩ := fix_ctx s hP fr u η ph hm
  obtain ⟨_, h1, h2, h3⟩ := J_push _ hV _ hsub hz _ hη ph ph' (hT fr u η ph hm) hst
  have hm' : ({ s with mode := Mode.fix fr u η ph' } : MainState n).mode = Mode.fix fr u η ph' := rfl
  refine ⟨?_, ?_, ?_, by simp [isFix, hm], by simp [notDone, hm]⟩
  · rw [gS_fix _ _ _ _ _ hm', gS_fix s _ _ _ _ hm]; exact congrArg hl h1
  · rw [gA_fix _ _ _ _ _ hm', gA_fix s _ _ _ _ hm]; exact h2
  · rw [gP_fix _ _ _ _ _ hm', gP_fix s _ _ _ _ hm]; exact h3

theorem aug_facts (s s' : MainState n) (hP : IFP.PInv s) (hT : TInv s) (h : AugK s s') :
    gS s' = gS s ∧ gA s' + 1 = gA s ∧ gP s' ≤ 2 * n * n * ((n + 1) + n) ∧
      isFix s' = isFix s ∧ notDone s' = notDone s := by
  obtain ⟨fr, u, η, ph, ph', hm, hst, rfl⟩ := h
  obtain ⟨hV, hsub, hz, hη, hmn⟩ := fix_ctx s hP fr u η ph hm
  obtain ⟨_, h1, h2, h3⟩ := J_aug _ hV _ hsub hz _ hη ph ph' (hT fr u η ph hm) hst
  have hm' : ({ s with mode := Mode.fix fr u η ph' } : MainState n).mode = Mode.fix fr u η ph' := rfl
  refine ⟨?_, ?_, ?_, by simp [isFix, hm], by simp [notDone, hm]⟩
  · rw [gS_fix _ _ _ _ _ hm', gS_fix s _ _ _ _ hm]; exact congrArg hl h1
  · rw [gA_fix _ _ _ _ _ hm', gA_fix s _ _ _ _ hm]; exact h2
  · rw [gP_fix _ _ _ _ _ hm']
    refine h3.trans ?_
    exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hmn) hmn) (by omega)

theorem finish_facts (s s' : MainState n) (h : FinishStep s s') :
    gS s' = 0 ∧ gA s' = 0 ∧ gP s' = 0 ∧ isFix s' = 0 ∧ isFix s = 0 ∧ notDone s' = 0 ∧
      notDone s = 1 := by
  obtain ⟨X, hX⟩ := finish_mode s s' h
  have hm : s.mode = Mode.loop := h.1
  exact ⟨gS_done _ _ hX, gA_done _ _ hX, gP_done _ _ hX, by simp [isFix, hX],
    by simp [isFix, hm], by simp [notDone, hX], by simp [notDone, hm]⟩

theorem return_facts' (s s' : MainState n) (h : ReturnStep s s') :
    gS s' = 0 ∧ gA s' = 0 ∧ gP s' = 0 ∧ isFix s' = 0 ∧ isFix s = 1 ∧ notDone s' = 1 ∧
      notDone s = 1 := by
  have hm' := return_mode s s' h
  obtain ⟨fr, u, η, ph, w, hm, _⟩ := h
  exact ⟨gS_loop _ hm', gA_loop _ hm', gP_loop _ hm', by simp [isFix, hm'],
    by simp [isFix, hm], by simp [notDone, hm'], by simp [notDone, hm]⟩


/-! ## The per-step inequalities -/

section Levels
open Classical

variable (s s' : MainState n) (hP : IFP.PInv s) (hT : TInv s) (h : Step s s')
include hP hT h

theorem lvF :
    notDone s' + (if FinishStep s s' then 1 else 0) ≤
      notDone s + @ite ℕ False (Classical.propDecidable False) 0 0 + @ite ℕ False (Classical.propDecidable False) 0 0 := by
  by_cases hA : FinishStep s s'
  · rw [if_pos hA]; have := finish_facts s s' hA; omega
  · rw [if_neg hA]
    rcases step_cases s s' h with hx | hx | hx | hx | hx | hx
    · exact absurd hx hA
    · have := call_facts s s' hP hx
      have : notDone s = 1 := by simp [notDone, this.1]
      omega
    · have := start_facts s s' hP hT hx; omega
    · have := push_facts s s' hP hT hx; omega
    · have := aug_facts s s' hP hT hx; omega
    · have := return_facts' s s' hx; omega

theorem lvR :
    isFix s' + (if ReturnStep s s' then 1 else 0) ≤
      isFix s + (if CallStep s s' then 1 else 0) + @ite ℕ False (Classical.propDecidable False) 0 0 := by
  by_cases hA : ReturnStep s s'
  · rw [if_pos hA]; have := return_facts' s s' hA; omega
  · rw [if_neg hA]
    by_cases hB : CallStep s s'
    · rw [if_pos hB]; have := call_facts s s' hP hB; omega
    · rw [if_neg hB]
      rcases step_cases s s' h with hx | hx | hx | hx | hx | hx
      · have := finish_facts s s' hx; omega
      · exact absurd hx hB
      · have := start_facts s s' hP hT hx; omega
      · have := push_facts s s' hP hT hx; omega
      · have := aug_facts s s' hP hT hx; omega
      · exact absurd hx hA

theorem lvS :
    gS s' + (if StartK s s' then 1 else 0) ≤
      gS s + (if CallStep s s' then hl (2 * n ^ 3) else 0) + @ite ℕ False (Classical.propDecidable False) 0 0 := by
  by_cases hA : StartK s s'
  · rw [if_pos hA]; have := start_facts s s' hP hT hA; omega
  · rw [if_neg hA]
    by_cases hB : CallStep s s'
    · rw [if_pos hB]; have := call_facts s s' hP hB; omega
    · rw [if_neg hB]
      rcases step_cases s s' h with hx | hx | hx | hx | hx | hx
      · have := finish_facts s s' hx; omega
      · exact absurd hx hB
      · exact absurd hx hA
      · have := push_facts s s' hP hT hx; omega
      · have := aug_facts s s' hP hT hx; omega
      · have := return_facts' s s' hx; omega

theorem lvA :
    gA s' + (if AugK s s' then 1 else 0) ≤
      gA s + (if StartK s s' then n ^ 2 + n else 0) + (if CallStep s s' then 0 else 0) := by
  by_cases hA : AugK s s'
  · rw [if_pos hA]; have := aug_facts s s' hP hT hA; omega
  · rw [if_neg hA]
    by_cases hB : StartK s s'
    · rw [if_pos hB]; have := start_facts s s' hP hT hB; omega
    · rw [if_neg hB]
      rcases step_cases s s' h with hx | hx | hx | hx | hx | hx
      · have := finish_facts s s' hx; omega
      · have := call_facts s s' hP hx; omega
      · exact absurd hx hB
      · have := push_facts s s' hP hT hx; omega
      · exact absurd hx hA
      · have := return_facts' s s' hx; omega

theorem lvP :
    gP s' + (if PushK s s' then 1 else 0) ≤
      gP s + (if AugK s s' then 2 * n * n * ((n + 1) + n) else 0) +
        @ite ℕ (StartK s s' ∨ CallStep s s') (Classical.propDecidable _)
          (2 * n * n * ((n + (n + 1) * (hl (2 * n ^ 3) + 1)) + n)) 0 := by
  by_cases hA : PushK s s'
  · rw [if_pos hA]; have := push_facts s s' hP hT hA; omega
  · rw [if_neg hA]
    by_cases hB : AugK s s'
    · rw [if_pos hB]; have := aug_facts s s' hP hT hB; omega
    · rw [if_neg hB]
      by_cases hC : StartK s s' ∨ CallStep s s'
      · rw [if_pos hC]
        rcases hC with hC | hC
        · have := start_facts s s' hP hT hC; omega
        · have := call_facts s s' hP hC
          have k : 2 * n * n * (1 + n) ≤ 2 * n * n * ((n + (n + 1) * (hl (2 * n ^ 3) + 1)) + n) :=
            Nat.mul_le_mul_left _ (by nlinarith)
          omega
      · rw [if_neg hC]
        rcases step_cases s s' h with hx | hx | hx | hx | hx | hx
        · have := finish_facts s s' hx; omega
        · exact absurd (Or.inr hx) hC
        · exact absurd (Or.inl hx) hC
        · exact absurd hx hA
        · exact absurd hx hB
        · have := return_facts' s s' hx; omega

end Levels


/-! ## Arithmetic -/

theorem hl_bound (n : ℕ) (hn : 1 ≤ n) : hl (2 * n ^ 3) ≤ 4 * (Nat.log 2 n + 1) := by
  set l := Nat.log 2 n
  have h1 : n < 2 ^ (l + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have h2 : n ^ 3 < (2 ^ (l + 1)) ^ 3 := Nat.pow_lt_pow_left h1 (by norm_num)
  have h3 : 2 * n ^ 3 < 2 ^ (3 * l + 4) := by
    rw [← pow_mul] at h2
    have : 2 ^ (3 * l + 4) = 2 * 2 ^ ((l + 1) * 3) := by rw [← pow_succ']; ring_nf
    rw [this]; omega
  have h4 : Nat.log 2 (2 * n ^ 3) < 3 * l + 4 :=
    Nat.log_lt_of_lt_pow (by positivity) h3
  unfold hl
  split_ifs <;> omega

theorem log_lt_self' (n : ℕ) (hn : 1 ≤ n) : Nat.log 2 n + 1 ≤ n := by
  have h1 := Nat.pow_log_le_self 2 (show n ≠ 0 by omega)
  have h2 : Nat.log 2 n < 2 ^ Nat.log 2 n := Nat.lt_two_pow_self
  omega

theorem final_arith (n L c st a p r fi GS : ℕ) (hn : 1 ≤ n) (hL1 : 1 ≤ L) (hLn : L ≤ n)
    (hGS : GS ≤ 4 * L) (hc : c ≤ n ^ 2) (hst : st ≤ GS * c) (ha : a ≤ (n ^ 2 + n) * st)
    (hp : p ≤ 2 * n * n * ((n + 1) + n) * a +
      2 * n * n * ((n + (n + 1) * (GS + 1)) + n) * (st + c))
    (hr : r ≤ c) (hfi : fi ≤ 1) :
    fi + c + st + p + a + r ≤ 200 * n ^ 7 * L := by
  have h1 : st ≤ 4 * L * n ^ 2 := hst.trans (Nat.mul_le_mul hGS hc)
  have hn2 : n ≤ n ^ 2 := Nat.le_self_pow (by norm_num) n
  have hnn : n ^ 2 + n ≤ 2 * n ^ 2 := by omega
  have h2 : a ≤ 8 * L * n ^ 4 := by
    have := ha.trans (Nat.mul_le_mul hnn h1)
    have e : 2 * n ^ 2 * (4 * L * n ^ 2) = 8 * L * n ^ 4 := by ring
    omega
  have h3 : 2 * n * n * ((n + 1) + n) ≤ 6 * n ^ 3 := by
    have e : 2 * n * n * ((n + 1) + n) = 4 * n ^ 3 + 2 * n ^ 2 := by ring
    have : n ^ 2 ≤ n ^ 3 := Nat.pow_le_pow_right hn (by norm_num)
    omega
  have h4 : 2 * n * n * ((n + (n + 1) * (GS + 1)) + n) ≤ 24 * n ^ 3 * L := by
    have k1 : (n + 1) * (GS + 1) ≤ (2 * n) * (5 * L) := Nat.mul_le_mul (by omega) (by omega)
    have k2 : (n + (n + 1) * (GS + 1)) + n ≤ 12 * n * L := by
      have k3 : n ≤ n * L := Nat.le_mul_of_pos_right _ hL1
      have e1 : (2 * n) * (5 * L) = 10 * (n * L) := by ring
      have e2 : 12 * n * L = 12 * (n * L) := by ring
      omega
    have := Nat.mul_le_mul_left (2 * n * n) k2
    have e : 2 * n * n * (12 * n * L) = 24 * n ^ 3 * L := by ring
    omega
  have h5 : st + c ≤ 5 * L * n ^ 2 := by
    have k : n ^ 2 ≤ L * n ^ 2 := Nat.le_mul_of_pos_left _ hL1
    have e1 : 4 * L * n ^ 2 = 4 * (L * n ^ 2) := by ring
    have e2 : 5 * L * n ^ 2 = 5 * (L * n ^ 2) := by ring
    omega
  have hp' : p ≤ 6 * n ^ 3 * (8 * L * n ^ 4) + 24 * n ^ 3 * L * (5 * L * n ^ 2) :=
    hp.trans (Nat.add_le_add (Nat.mul_le_mul h3 h2) (Nat.mul_le_mul h4 h5))
  have hLL : L * L ≤ L * n ^ 2 := Nat.mul_le_mul_left _ (hLn.trans hn2)
  have q1 : n ^ 2 ≤ n ^ 7 := Nat.pow_le_pow_right hn (by norm_num)
  have q2 : n ^ 4 ≤ n ^ 7 := Nat.pow_le_pow_right hn (by norm_num)
  have q3 : n ^ 2 * L ≤ n ^ 7 * L := Nat.mul_le_mul_right _ q1
  have q4 : n ^ 4 * L ≤ n ^ 7 * L := Nat.mul_le_mul_right _ q2
  have q5 : n ^ 7 ≤ n ^ 7 * L := Nat.le_mul_of_pos_right _ hL1
  have q6 : 1 ≤ n ^ 7 := Nat.one_le_pow _ _ hn
  have e1 : 6 * n ^ 3 * (8 * L * n ^ 4) + 24 * n ^ 3 * L * (5 * L * n ^ 2) =
      48 * (n ^ 7 * L) + 120 * (n ^ 5 * (L * L)) := by ring
  have q7 : n ^ 5 * (L * L) ≤ n ^ 7 * L := by
    have := Nat.mul_le_mul_left (n ^ 5) hLL
    have e : n ^ 5 * (L * n ^ 2) = n ^ 7 * L := by ring
    omega
  have e2 : 200 * n ^ 7 * L = 200 * (n ^ 7 * L) := by ring
  have e3 : 4 * L * n ^ 2 = 4 * (n ^ 2 * L) := by ring
  have e4 : 8 * L * n ^ 4 = 8 * (n ^ 4 * L) := by ring
  omega

/-- Running time: every run of Figure 3 has at most `200 n⁷ (⌊log₂ n⌋ + 1)` steps. -/
theorem run_bound {n : ℕ} (hn : 1 ≤ n) (f : Finset (Fin n) → ℝ)
    (hsub : SubmodularOn Finset.univ f) (hf0 : f ∅ = 0)
    (s : ℕ → MainState n) (k : ℕ) (hrun : IsRun f s k) :
    k ≤ 200 * n ^ 7 * (Nat.log 2 n + 1) := by
  classical
  obtain ⟨h0, hst⟩ := hrun
  have hreach : ∀ j ≤ k, Relation.ReflTransGen Step (initMain f) (s j) := by
    intro j
    induction j with
    | zero => intro _; rw [h0]
    | succ j ih => intro hj; exact (ih (by omega)).tail (hst j (by omega))
  have hinv : ∀ j < k, IFP.PInv (s j) ∧ TInv (s j) :=
    fun j hj => reach_inv f hsub hf0 _ (hreach j hj.le)
  have hini : s 0 = initMain f := h0
  have hm0 : (s 0).mode = Mode.loop := by rw [hini]; rfl
  -- the counts
  have cF := count_le s k FinishStep (fun _ _ => False) (fun _ _ => False) notDone 0 0
    (fun j hj => lvF (s j) (s (j + 1)) (hinv j hj).1 (hinv j hj).2 (hst j hj))
  have cR := count_le s k ReturnStep CallStep (fun _ _ => False) isFix 1 0
    (fun j hj => lvR (s j) (s (j + 1)) (hinv j hj).1 (hinv j hj).2 (hst j hj))
  have cS := count_le s k StartK CallStep (fun _ _ => False) gS (hl (2 * n ^ 3)) 0
    (fun j hj => lvS (s j) (s (j + 1)) (hinv j hj).1 (hinv j hj).2 (hst j hj))
  have cA := count_le s k AugK StartK CallStep gA (n ^ 2 + n) 0
    (fun j hj => lvA (s j) (s (j + 1)) (hinv j hj).1 (hinv j hj).2 (hst j hj))
  have cP := count_le s k PushK AugK (fun a b => StartK a b ∨ CallStep a b) gP
    (2 * n * n * ((n + 1) + n)) (2 * n * n * ((n + (n + 1) * (hl (2 * n ^ 3) + 1)) + n))
    (fun j hj => lvP (s j) (s (j + 1)) (hinv j hj).1 (hinv j hj).2 (hst j hj))
  have g0 : notDone (s 0) = 1 ∧ isFix (s 0) = 0 ∧ gS (s 0) = 0 ∧ gA (s 0) = 0 ∧ gP (s 0) = 0 :=
    ⟨by simp [notDone, hm0], by simp [isFix, hm0], gS_loop _ hm0, gA_loop _ hm0, gP_loop _ hm0⟩
  have hcalls : cnt s CallStep k ≤ n ^ 2 := by
    have := fix_calls_le hn f hsub hf0 s k ⟨h0, hst⟩
    unfold callCount at this; unfold cnt; exact this
  have hor : cnt s (fun a b => StartK a b ∨ CallStep a b) k ≤ cnt s StartK k + cnt s CallStep k :=
    cnt_or s _ _ k
  -- every step is of one of the kinds
  have hall : k ≤ cnt s FinishStep k + cnt s CallStep k + cnt s StartK k + cnt s PushK k +
      cnt s AugK k + cnt s ReturnStep k := by
    have e := cnt_all s Step k hst
    have m1 := cnt_mono s Step (fun a b => FinishStep a b ∨ CallStep a b ∨ StartK a b ∨
      PushK a b ∨ AugK a b ∨ ReturnStep a b) k (fun j _ h => step_cases _ _ h)
    have o1 := cnt_or s FinishStep (fun a b => CallStep a b ∨ StartK a b ∨ PushK a b ∨
      AugK a b ∨ ReturnStep a b) k
    have o2 := cnt_or s CallStep (fun a b => StartK a b ∨ PushK a b ∨ AugK a b ∨ ReturnStep a b) k
    have o3 := cnt_or s StartK (fun a b => PushK a b ∨ AugK a b ∨ ReturnStep a b) k
    have o4 := cnt_or s PushK (fun a b => AugK a b ∨ ReturnStep a b) k
    have o5 := cnt_or s AugK ReturnStep k
    omega
  obtain ⟨g1, g2, g3, g4, g5⟩ := g0
  rw [g1] at cF; rw [g2] at cR; rw [g3] at cS; rw [g4] at cA; rw [g5] at cP
  generalize cnt s FinishStep k = fi at cF hall
  generalize cnt s CallStep k = c at cR cS cA hor hall hcalls
  generalize cnt s StartK k = st at cS cA hor hall
  generalize cnt s AugK k = a at cA cP hall
  generalize cnt s PushK k = p at cP hall
  generalize cnt s ReturnStep k = r at cR hall
  generalize cnt s (fun a b => StartK a b ∨ CallStep a b) k = sc at cP hor
  generalize cnt s (fun _ _ => False) k = z at cF cR cS
  have hGS := hl_bound n hn
  have hLn := log_lt_self' n hn
  set GS := hl (2 * n ^ 3)
  have hp : p ≤ 2 * n * n * ((n + 1) + n) * a +
      2 * n * n * ((n + (n + 1) * (GS + 1)) + n) * (st + c) := by
    have k1 := Nat.mul_le_mul_left (2 * n * n * ((n + (n + 1) * (GS + 1)) + n)) hor
    set X := 2 * n * n * ((n + (n + 1) * (GS + 1)) + n)
    set Y := 2 * n * n * ((n + 1) + n)
    omega
  have := final_arith n (Nat.log 2 n + 1) c st a p r fi GS hn (by omega) hLn
    hGS hcalls (by omega) (by omega) hp (by omega) (by omega)
  omega

end IFT



open IwataFF.SFM

theorem solution :
    ∃ C : ℕ, ∀ n : ℕ, 1 ≤ n → ∀ f : Finset (Fin n) → ℝ,
      SubmodularOn Finset.univ f → f ∅ = 0 →
      (∀ s : MainState n, Relation.ReflTransGen Step (initMain f) s → ¬ IsFinal s →
          ∃ s' : MainState n, Step s s') ∧
      (∀ (s : ℕ → MainState n) (k : ℕ), IsRun f s k → k ≤ C * n ^ 7 * (Nat.log 2 n + 1)) ∧
      (∀ (s : MainState n) (X : Finset (Fin n)), Relation.ReflTransGen Step (initMain f) s →
          s.mode = Mode.done X → ∀ Y : Finset (Fin n), f X ≤ f Y) :=
  ⟨200, fun n hn f hsub hf0 =>
    ⟨fun s hs hnf => IFP.progress f hsub hf0 s hs hnf,
     fun s k hrun => IFT.run_bound hn f hsub hf0 s k hrun,
     fun s X hs hX => IFC.correct f hsub hf0 s X hs hX⟩⟩


