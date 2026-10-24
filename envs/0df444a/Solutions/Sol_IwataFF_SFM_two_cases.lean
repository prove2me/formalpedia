-- Prove2me | solution 1 for IwataFF.SFM.two_cases
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T06:43:53.232753+00:00
-- url     : https://prove2.me/submissions/9f05dc94-58a0-401f-9cdb-1fcb88622725

import Mathlib
import Definitions.Def_IwataFF_SFM_Basic
import Definitions.Def_IwataFF_SFM_Phase
import Definitions.Def_IwataFF_SFM_Main
import Theorems.Thm_IwataFF_SFM_lemma_2_1
import Theorems.Thm_IwataFF_SFM_lemma_4_1

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

open X5TC in
theorem solution {n : ℕ} (hn : 1 ≤ n) (f : Finset (Fin n) → ℝ)
    (hsub : SubmodularOn Finset.univ f) (hf0 : f ∅ = 0)
    (s : MainState n) (hs : Relation.ReflTransGen Step (initMain f) s)
    (former : Bool) (u : Finset (Fin n)) (η : ℝ) (ph : PhaseState (Finset (Fin n)))
    (hmode : s.mode = Mode.fix former u η ph) (w : Finset (Fin n))
    (hw : FixOutput (s.fixFun former u) (s.fixGround former u) (η / 2) ph w) :
    (former = true → w ∈ s.blocks \ s.R u ∧ Compatible s.blocks s.curFun u w) ∧
      (former = false → ∀ X, IsMinimizer s.blocks s.curFun X → w ∈ X ∧ s.R w ⊆ X) :=
  return_facts s (reach_ginv f hsub hf0 s hs) former u η ph hmode w hw

