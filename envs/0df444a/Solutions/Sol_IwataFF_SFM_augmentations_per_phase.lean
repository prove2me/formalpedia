-- Prove2me | solution 1 for IwataFF.SFM.augmentations_per_phase
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T06:09:59.748372+00:00
-- url     : https://prove2.me/submissions/8b06274b-fcf9-45e4-b8c8-e04e80d4262a

import Mathlib
import Definitions.Def_IwataFF_SFM_Basic
import Definitions.Def_IwataFF_SFM_Phase
import Theorems.Thm_IwataFF_SFM_lemma_2_1
import Theorems.Thm_IwataFF_SFM_lemma_3_1
import Theorems.Thm_IwataFF_SFM_lemma_3_2
import Theorems.Thm_IwataFF_SFM_lemma_3_3

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


open IwataFF.SFM

namespace X5IW

theorem guard_not_end {α : Type} [DecidableEq α] (V : Finset α) (f : Finset α → ℝ)
    (st : PhaseState α) (hG : Guard f V st) (hE : PhaseEnd f V st) : False := by
  obtain ⟨hS, hT, hZ⟩ := hG
  rcases hE with h | h | ⟨h1, h2⟩
  · rw [h] at hS; simp at hS
  · rw [h] at hT; simp at hT
  · rcases hZ with h | h
    · exact h1 h
    · rw [h2] at h; simp at h

open Classical in
theorem augCount_succ {α : Type} [DecidableEq α] (V : Finset α) (f : Finset α → ℝ)
    (s : ℕ → PhaseState α) (j : ℕ) :
    ((augCount f V s (j + 1) : ℕ) : ℝ) = (augCount f V s j : ℝ) +
      (if AugStep f V (s j) (s (j + 1)) then 1 else 0) := by
  classical
  unfold augCount
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]; push_cast; ring
  · simp

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

end X5IW

open X5IW in
theorem solution {α : Type} [DecidableEq α] (V : Finset α) (hV : V.Nonempty)
    (f : Finset α → ℝ) (hsub : SubmodularOn V f) (hf0 : f ∅ = 0)
    (s : ℕ → PhaseState α) (m : ℕ) (hinv : PhaseInv V (s 0)) (hrun : IsPhaseRun f V s m) :
    augCount f V s m ≤ V.card ^ 2 + V.card := by
  obtain ⟨hm, _, hend, hstart, hsteps⟩ := hrun
  obtain ⟨_, hs1⟩ := hstart
  set δ0 := (s 0).delta with hδ0
  have hδ0pos : 0 < δ0 := hinv.1
  have hinv1 : PhaseInv V (s 1) := by rw [hs1]; exact clip_inv V (s 0) hinv
  have hd1 : (s 1).delta = δ0 / 2 := by rw [hs1]
  set zn : PhaseState α → ℝ := fun st => xsum (xneg (zOf f V st)) V with hzn
  -- the run
  have hc1 : augCount f V s 1 = 0 := by
    classical
    unfold augCount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x hx
    rw [Finset.mem_range, Nat.lt_one_iff] at hx
    subst hx
    intro h
    exact guard_not_end V f (s 0) h.2.1 hend
  have key : ∀ j, 1 ≤ j → j ≤ m → PhaseInv V (s j) ∧ (s j).delta = δ0 / 2 ∧
      zn (s j) = zn (s 1) + (δ0 / 2) * (augCount f V s j : ℝ) := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => intro _; refine ⟨hinv1, hd1, ?_⟩; rw [hc1]; simp
    | succ j hj ih =>
      intro hjm
      obtain ⟨hI, hD, hZ⟩ := ih (by omega)
      rw [augCount_succ]
      rcases hsteps j hj (by omega) with h | h
      · obtain ⟨h1, h2, h3⟩ := push_step V hV f hsub hf0 _ _ hI h
        have hna : ¬ AugStep f V (s j) (s (j + 1)) := by
          intro ha
          have := ha.2.2.1
          rw [h.2.2.1] at this; simp at this
        refine ⟨h1, h2.trans hD, ?_⟩
        rw [if_neg hna]
        simp only [hzn] at hZ ⊢
        rw [h3, hZ]; ring
      · obtain ⟨h1, h2, h3⟩ := aug_step V f _ _ hI h
        refine ⟨h1, h2.trans hD, ?_⟩
        rw [if_pos h]
        simp only [hzn] at hZ ⊢
        rw [h3, hZ, hD]; ring
  obtain ⟨hIm, hDm, hZm⟩ := key m hm le_rfl
  -- lower bound at the end of the previous phase
  have hlow : ∃ X ⊆ V, f X - (V.card : ℝ) * δ0 ≤ zn (s 0) := by
    have L3 := lemma_3_3 V hV f hsub hf0 (s 0) hinv hend
    rcases hend with h | h | ⟨h1, _⟩
    · exact ⟨∅, Finset.empty_subset _, (L3.1 h).2⟩
    · exact ⟨V, subset_rfl, (L3.2.1 h).2⟩
    · have ht := lemma_3_1 V hV f hsub hf0 (s 0) hinv h1
      exact ⟨Wset f V (s 0), (fun x hx => by simp only [Wset, Finset.mem_filter] at hx; exact hx.1), (L3.2.2 ht).2⟩
  obtain ⟨X, hX, hlowX⟩ := hlow
  -- clipping
  have hclip : zn (s 0) - ((V.card.choose 2 : ℕ) : ℝ) * (δ0 / 2) ≤ zn (s 1) := by
    have := clip_zneg V (xOf f (s 0)) (s 0).phi (δ0 / 2) (by linarith) hinv.2.2.2.2.1
      (fun u hu v hv => by
        have := hinv.2.2.2.2.2 u hu v hv
        constructor <;> linarith [this.1, this.2])
    simp only [hzn]
    unfold zOf bdry
    rw [hs1]
    exact this
  -- upper bound (Lemma 3.2) at the current state
  have hup : zn (s m) ≤ f X + ((V.card.choose 2 : ℕ) : ℝ) * (δ0 / 2) := by
    have hx := xOf_base V f hsub hf0 (s m) hIm.2.2.1 hIm.2.2.2.1
    have := lemma_3_2 V hV f hsub hf0 (xOf f (s m)) hx (s m).phi (δ0 / 2) (by linarith)
      hIm.2.2.2.2.1 (by rw [← hDm]; exact hIm.2.2.2.2.2) X hX
    exact this
  rw [hZm] at hup
  have hC : ((V.card.choose 2 : ℕ) : ℝ) = (V.card : ℝ) * ((V.card : ℝ) - 1) / 2 :=
    Nat.cast_choose_two ℝ V.card
  rw [hC] at hup hclip
  have hfin : (δ0 / 2) * (augCount f V s m : ℝ) ≤
      (δ0 / 2) * ((V.card : ℝ) ^ 2 + V.card) := by
    nlinarith
  have := le_of_mul_le_mul_left hfin (by linarith)
  exact_mod_cast this


