-- Prove2me | solution 1 for MetricTSPSublinear.net_size_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T04:16:03.410232+00:00
-- url     : https://prove2.me/submissions/afe6501e-b668-422d-8872-8d1d74be792e

import Mathlib
import Definitions.Def_DoublingMST_IsMetric
import Definitions.Def_DoublingMST_mstWeight
import Definitions.Def_MetricTSP_model
import Theorems.Thm_MetricTSPSublinear_claim_3_2
import Theorems.Thm_MetricTSPSublinear_claim_3_3

/-!
Tour bound: `m` points pairwise at distance `≥ τ` force `m * τ ≤ 2 * M`.
-/

open scoped Classical

namespace MTSPMst
open Finset

section path
variable {α : Type*} (d : α → α → ℝ)

/-- Cost of the path `a → l₁ → l₂ → ⋯`. -/
noncomputable def pc : α → List α → ℝ
  | _, [] => 0
  | a, b :: l => d a b + pc b l

variable {d}

lemma pc_cons_le (htri : ∀ x y z, d x z ≤ d x y + d y z) (a c : α) (X : List α) (hX : X ≠ []) :
    pc d a X ≤ d a c + pc d c X := by
  cases X with
  | nil => exact absurd rfl hX
  | cons x X' => simp only [pc]; linarith [htri a c x]

lemma pc_filter_le (htri : ∀ x y z, d x z ≤ d x y + d y z) (p : α → Bool) (b : α) :
    ∀ (l : List α) (a : α), pc d a (l.filter p ++ [b]) ≤ pc d a (l ++ [b])
  | [], _ => le_refl _
  | c :: l, a => by
    have ih := pc_filter_le htri p b l c
    by_cases hc : p c = true
    · simp only [List.filter_cons, hc, if_true, List.cons_append, pc]; linarith
    · simp only [List.filter_cons, hc, List.cons_append, pc]
      simp only [Bool.false_eq_true, if_false]
      have := pc_cons_le htri a c (l.filter p ++ [b]) (by simp)
      linarith

lemma pc_append_last (htri : ∀ x y z, d x z ≤ d x y + d y z) (a z : α) :
    ∀ (Y : List α) (x : α), pc d x (Y ++ [z]) ≤ pc d x (Y ++ [a]) + d a z
  | [], x => by simp only [List.nil_append, pc]; linarith [htri x a z]
  | y :: Y, x => by
    simp only [List.cons_append, pc]
    linarith [pc_append_last htri a z Y y]

lemma pc_closed (R : Finset α) (τ : ℝ) (hR : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → τ ≤ d a b) (z : α)
    (hz : z ∈ R) : ∀ (Y : List α) (x : α), x ∈ R → (∀ y ∈ Y, y ∈ R) → (x :: Y).Nodup → z ∉ Y →
      (Y ≠ [] ∨ x ≠ z) → τ * (Y.length + 1) ≤ pc d x (Y ++ [z])
  | [], x, hx, _, _, _, hne => by
    simp only [List.nil_append, pc, List.length_nil]
    have : x ≠ z := by simpa using hne
    norm_num
    linarith [hR x hx z hz this]
  | y :: Y, x, hx, hY, hnd, hzY, _ => by
    simp only [List.cons_append, pc, List.length_cons]
    have hxy : x ≠ y := by
      intro h; subst h; simp at hnd
    have hyR : y ∈ R := hY y (by simp)
    have hyz : y ≠ z := by intro h; subst h; simp at hzY
    have ih := pc_closed R τ hR z hz Y y hyR (fun w hw => hY w (by simp [hw]))
      (List.nodup_cons.mp hnd).2 (by intro h; exact hzY (by simp [h])) (Or.inr hyz)
    have := hR x hx y hyR hxy
    push_cast
    linarith

lemma pc_range (g : ℕ → α) : ∀ k : ℕ,
    pc d (g 0) ((List.range k).map (fun i => g (i + 1))) =
      ∑ i ∈ Finset.range k, d (g i) (g (i + 1))
  | 0 => by simp [pc]
  | k + 1 => by
    rw [List.range_succ_eq_map, Finset.sum_range_succ']
    simp only [List.map_cons, List.map_map, pc]
    have := pc_range (fun j => g (j + 1)) k
    simp only [Function.comp_def, Nat.succ_eq_add_one, zero_add] at this ⊢
    rw [this]; ring

end path

variable {n : ℕ}

/-- Every tour through `R` (pairwise `≥ τ`, `|R| ≥ 2`) costs at least `|R| τ`. -/
lemma tourCost_ge (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d)
    (R : Finset (Fin n)) (τ : ℝ) (hτ : 0 ≤ τ) (hR2 : 2 ≤ R.card)
    (hR : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → τ ≤ d a b) (π : Equiv.Perm (Fin n)) :
    (R.card : ℝ) * τ ≤ MetricTSP.tourCost d π := by
  have htri : ∀ x y z, d x z ≤ d x y + d y z := hd.2.2
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; have := Finset.card_le_univ R; simp only [Fintype.card_fin] at this; omega
    · exact h
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨f, hf⟩ : ∃ f : ℕ → Fin (m + 1),
      ∀ i, f i = π ⟨i % (m + 1), Nat.mod_lt _ (by omega)⟩ := ⟨_, fun _ => rfl⟩
  -- tour cost as a path
  have hcost : MetricTSP.tourCost d π = ∑ i ∈ Finset.range (m + 1), d (f i) (f (i + 1)) := by
    unfold MetricTSP.tourCost
    rw [← Fin.sum_univ_eq_sum_range (fun i => d (f i) (f (i + 1)))]
    apply Finset.sum_congr rfl
    intro i _
    rw [hf, hf]
    congr 2
    · ext; simp [Nat.mod_eq_of_lt i.isLt]
    · rw [finRotate_apply]; ext
      simp [Fin.val_add]
  set a := f 0 with ha
  set L' := (List.range m).map (fun i => f (i + 1)) with hL'
  have hpath : MetricTSP.tourCost d π = pc d a (L' ++ [a]) := by
    rw [hcost, ← pc_range (d := d) f (m + 1), List.range_succ, List.map_append]
    simp only [List.map_cons, List.map_nil]
    congr 2
    rw [ha, hf, hf]; congr 1; ext; simp
  -- nodup and membership
  have hfinj : ∀ x ∈ List.range (m + 1), ∀ y ∈ List.range (m + 1), f x = f y → x = y := by
    intro x hx y hy hxy
    simp only [List.mem_range] at hx hy
    rw [hf, hf] at hxy
    have := π.injective hxy
    simp only [Fin.mk.injEq] at this
    rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this
  have hnd : (a :: L').Nodup := by
    have := (List.nodup_range).map_on hfinj
    rw [List.range_succ_eq_map] at this
    simpa [hL', ha, List.map_map, Function.comp_def] using this
  have hmem : ∀ x, x ≠ a → x ∈ L' := by
    intro x hx
    set j := π.symm x with hj
    have hj0 : (j : ℕ) ≠ 0 := by
      intro h0
      apply hx
      have : j = ⟨0 % (m + 1), Nat.mod_lt _ (by omega)⟩ := by ext; simp [h0]
      rw [ha, hf, ← this, hj, Equiv.apply_symm_apply]
    simp only [hL', List.mem_map, List.mem_range]
    refine ⟨(j : ℕ) - 1, by omega, ?_⟩
    rw [hf]
    have : (⟨((j : ℕ) - 1 + 1) % (m + 1), Nat.mod_lt _ (by omega)⟩ : Fin (m + 1)) = j := by
      ext; simp only; rw [Nat.sub_add_cancel (by omega), Nat.mod_eq_of_lt j.isLt]
    rw [this, hj, Equiv.apply_symm_apply]
  set F := L'.filter (fun x => decide (x ∈ R)) with hF
  have hFnd : F.Nodup := (List.nodup_cons.mp hnd).2.filter _
  have haF : a ∉ F := fun h => (List.nodup_cons.mp hnd).1 (List.mem_of_mem_filter h)
  have hFR : ∀ y ∈ F, y ∈ R := fun y hy => by simpa using (List.mem_filter.mp hy).2
  have hFlen : (R.erase a).card ≤ F.length := by
    rw [← List.toFinset_card_of_nodup hFnd]
    apply Finset.card_le_card
    intro x hx
    obtain ⟨hxa, hxR⟩ := Finset.mem_erase.mp hx
    simp only [List.mem_toFinset, hF, List.mem_filter]
    exact ⟨hmem x hxa, by simpa using hxR⟩
  have hshort : pc d a (F ++ [a]) ≤ MetricTSP.tourCost d π := by
    rw [hpath]; exact pc_filter_le htri _ a L' a
  by_cases haR : a ∈ R
  · have hcard : (R.erase a).card + 1 = R.card := Finset.card_erase_add_one haR
    have hFne : F ≠ [] := by
      intro h; rw [h] at hFlen; simp only [List.length_nil] at hFlen; omega
    have := pc_closed R τ hR a haR F a haR hFR (List.nodup_cons.mpr ⟨haF, hFnd⟩) haF (Or.inl hFne)
    have h1 : (R.card : ℝ) ≤ F.length + 1 := by
      have : R.card ≤ F.length + 1 := by omega
      exact_mod_cast this
    nlinarith
  · have hcard : (R.erase a).card = R.card := by rw [Finset.erase_eq_of_notMem haR]
    obtain ⟨f1, F', hF1⟩ : ∃ f1 F', F = f1 :: F' := by
      cases hc : F with
      | nil => rw [hc] at hFlen; simp only [List.length_nil] at hFlen; omega
      | cons f1 F' => exact ⟨f1, F', rfl⟩
    rw [hF1] at hFlen hFnd hFR
    have hf1R : f1 ∈ R := hFR f1 (by simp)
    have hF'ne : F' ≠ [] := by
      intro h; rw [h] at hFlen; simp only [List.length_cons, List.length_nil] at hFlen; omega
    have h2 := pc_closed R τ hR f1 hf1R F' f1 hf1R (fun y hy => hFR y (by simp [hy])) hFnd
      (List.nodup_cons.mp hFnd).1 (Or.inl hF'ne)
    have h3 := pc_append_last htri a f1 F' f1
    have h4 : pc d a (F ++ [a]) = d a f1 + pc d f1 (F' ++ [a]) := by
      rw [hF1]; simp [pc]
    have h1 : (R.card : ℝ) ≤ F'.length + 1 := by
      have : R.card ≤ F'.length + 1 := by simp only [List.length_cons] at hFlen; omega
      exact_mod_cast this
    nlinarith

/-- `TSP ≤ 2 M` from Claims 3.2 and 3.3. -/
lemma tsp_le_two_mst (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d) :
    MetricTSP.tspOpt d ≤ 2 * DoublingMST.mstWeight d := by
  have h2 := MetricTSPSublinear.claim_3_2 d hd
  have h3 := MetricTSPSublinear.claim_3_3 d hd
  linarith [h2.2, h3.2]

end MTSPMst

open MTSPMst in
theorem solution {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d)
    (R : Finset (Fin n)) (τ : ℝ) (hτ : 0 ≤ τ) (hR2 : 2 ≤ R.card)
    (hR : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → τ ≤ d a b) :
    (R.card : ℝ) * τ ≤ 2 * DoublingMST.mstWeight d := by
  refine le_trans ?_ (tsp_le_two_mst d hd)
  unfold MetricTSP.tspOpt
  refine le_csInf ⟨MetricTSP.tourCost d 1, 1, rfl⟩ ?_
  rintro _ ⟨π, rfl⟩
  exact tourCost_ge d hd R τ hτ hR2 hR π
