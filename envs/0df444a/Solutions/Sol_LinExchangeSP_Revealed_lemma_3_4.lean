-- Prove2me | solution 1 for LinExchangeSP.Revealed.lemma_3_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T10:31:11.51156+00:00
-- url     : https://prove2.me/submissions/fdedbd61-c05b-4364-b40c-6b493f47648a

import Mathlib
import Definitions.Def_LinExchangeSP_Revealed_Market
import Definitions.Def_LinExchangeSP_Revealed_Setting

set_option autoImplicit false

namespace LinExchangeSP.Revealed

theorem col_eq_of_L1 {n : ℕ} {p : Fin n → ℝ} {f : Fin n → Fin n → ℝ}
    (h : surplusL1 p f = 0) (j : Fin n) : ∑ i, f i j = p j := by
  unfold surplusL1 at h
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => abs_nonneg (goodSurplus p f j))).1 h j
    (Finset.mem_univ _)
  unfold goodSurplus at this
  rw [abs_eq_zero, sub_eq_zero] at this
  linarith

theorem row_eq_of_L1 {n : ℕ} {p : Fin n → ℝ} {f : Fin n → Fin n → ℝ}
    (hrow : ∀ i, ∑ j, f i j ≤ p i) (h : surplusL1 p f = 0) (i : Fin n) :
    ∑ j, f i j = p i := by
  have htot : ∑ i, (p i - ∑ j, f i j) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_comm]
    simp [col_eq_of_L1 h]
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sub_nonneg.2 (hrow i))).1 htot i
    (Finset.mem_univ _)
  linarith

end LinExchangeSP.Revealed

open LinExchangeSP.Revealed in
theorem solution {n : ℕ} (M : Market n) (F : Set (Fin n × Fin n)) (hF : F ⊆ M.Fstar)
    (hex : ∃ p' f', M.IsMarketEquilibrium p' f')
    (p : Fin n → ℝ) (f : Fin n → Fin n → ℝ) (hpf : M.IsFEquilibrium F p f) :
    ∃ f' : Fin n → Fin n → ℝ, M.IsMarketEquilibrium p f' := by
  classical
  obtain ⟨p', g, hg⟩ := hex
  have hg' := hg
  obtain ⟨⟨hp'pos, hg0, hgsupp, hgrow, _hgcol⟩, hgL1⟩ := hg'
  obtain ⟨⟨hppos, hfF, hfsupp, hfrow, _hfcol⟩, hfL1⟩ := hpf
  have hfc : ∀ j, ∑ i, f i j = p j := col_eq_of_L1 hfL1
  have hfr : ∀ i, ∑ j, f i j = p i := row_eq_of_L1 hfrow hfL1
  have hgc : ∀ j, ∑ i, g i j = p' j := col_eq_of_L1 hgL1
  have hgr : ∀ i, ∑ j, g i j = p' i := row_eq_of_L1 hgrow hgL1
  obtain ⟨β, hβ⟩ : ∃ β : Fin n → ℝ, β = fun i => ⨆ k, M.u i k / p k := ⟨_, rfl⟩
  obtain ⟨β', hβ'⟩ : ∃ β' : Fin n → ℝ, β' = fun i => ⨆ k, M.u i k / p' k := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : Fin n → ℝ, r = fun k => p' k / p k := ⟨_, rfl⟩
  have le_β : ∀ i k, M.u i k / p k ≤ β i := fun i k => by
    subst hβ; exact le_ciSup (f := fun k => M.u i k / p k) (Set.finite_range _).bddAbove k
  have le_β' : ∀ i k, M.u i k / p' k ≤ β' i := fun i k => by
    subst hβ'; exact le_ciSup (f := fun k => M.u i k / p' k) (Set.finite_range _).bddAbove k
  have β_eq : ∀ i k, (i, k) ∈ M.MBB p → β i = M.u i k / p k := fun i k h => by
    have : Nonempty (Fin n) := ⟨i⟩
    refine le_antisymm ?_ (le_β i k)
    subst hβ; exact ciSup_le h.2
  have β'_eq : ∀ i k, (i, k) ∈ M.MBB p' → β' i = M.u i k / p' k := fun i k h => by
    have : Nonempty (Fin n) := ⟨i⟩
    refine le_antisymm ?_ (le_β' i k)
    subst hβ'; exact ciSup_le h.2
  have βpos : ∀ i, 0 < β i := fun i => by
    obtain ⟨j, hj⟩ := M.agent_edge i
    exact lt_of_lt_of_le (div_pos hj (hppos j)) (le_β i j)
  have β'pos : ∀ i, 0 < β' i := fun i => by
    obtain ⟨j, hj⟩ := M.agent_edge i
    exact lt_of_lt_of_le (div_pos hj (hp'pos j)) (le_β' i j)
  have rpos : ∀ k, 0 < r k := fun k => by subst hr; exact div_pos (hp'pos k) (hppos k)
  have hp'r : ∀ k, p' k = r k * p k := fun k => by
    subst hr; field_simp [(hppos k).ne']
  have key : ∀ i k, M.u i k / p k = r k * (M.u i k / p' k) := fun i k => by
    subst hr; field_simp [(hppos k).ne', (hp'pos k).ne']
  obtain ⟨γ, hγ⟩ : ∃ γ : Fin n → ℝ, γ = fun i => β i / β' i := ⟨_, rfl⟩
  have γpos : ∀ i, 0 < γ i := fun i => by subst hγ; exact div_pos (βpos i) (β'pos i)
  -- F1: money-carrying edges of f have r ≥ γ
  have F1 : ∀ i k, f i k ≠ 0 → γ i ≤ r k := fun i k hne => by
    have hm : (i, k) ∈ M.MBB p := hfsupp (Set.mem_union_left _ hne)
    have h1 := β_eq i k hm
    have h2 := le_β' i k
    subst hγ
    show β i / β' i ≤ r k
    rw [div_le_iff₀ (β'pos i), h1, key]
    exact mul_le_mul_of_nonneg_left h2 (rpos k).le
  -- core: MBB(p') edges have r ≤ γ
  have core : ∀ i k, (i, k) ∈ M.MBB p' → r k ≤ γ i := fun i k hm => by
    have h1 := β'_eq i k hm
    have h2 := le_β i k
    subst hγ
    show r k ≤ β i / β' i
    rw [le_div_iff₀ (β'pos i), h1, ← key]
    exact h2
  have F2 : ∀ i k, f i k < 0 → r k ≤ γ i := fun i k hneg => by
    have hm : (i, k) ∈ M.MBB p := hfsupp (Set.mem_union_left _ (ne_of_lt hneg))
    have hiF : (i, k) ∈ F := by
      by_contra hnF
      have := hfF (i, k) ⟨hm.1, hnF⟩
      exact absurd this (not_le.2 hneg)
    exact core i k ((hF hiF).2 p' g hg)
  have F4 : ∀ i j, (i, j) ∈ M.MBB p' → γ i ≤ r j → (i, j) ∈ M.MBB p := fun i j hm hle => by
    refine ⟨hm.1, fun l => ?_⟩
    have h1 := β'_eq i j hm
    have hγi : β i = γ i * β' i := by
      subst hγ; field_simp [(β'pos i).ne']
    calc M.u i l / p l ≤ β i := le_β i l
      _ = γ i * β' i := hγi
      _ ≤ r j * β' i := mul_le_mul_of_nonneg_right hle (β'pos i).le
      _ = M.u i j / p j := by rw [h1, key]
  -- inequality (1)
  have S1 : 0 ≤ ∑ i, ∑ j, f i j * (r j ^ 2 - γ i ^ 2) := by
    refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
    rcases lt_trichotomy (f i j) 0 with h | h | h
    · have e : r j = γ i := le_antisymm (F2 i j h) (F1 i j h.ne)
      rw [e]; simp
    · rw [h]; simp
    · have hle := F1 i j h.ne'
      have : γ i ^ 2 ≤ r j ^ 2 := pow_le_pow_left₀ (γpos i).le hle 2
      exact mul_nonneg h.le (sub_nonneg.2 this)
  have S1e : ∑ i, ∑ j, f i j * (r j ^ 2 - γ i ^ 2)
      = ∑ j, p j * r j ^ 2 - ∑ i, p i * γ i ^ 2 := by
    have e1 : ∑ i, ∑ j, f i j * r j ^ 2 = ∑ j, p j * r j ^ 2 := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.sum_mul, hfc j]
    have e2 : ∑ i, ∑ j, f i j * γ i ^ 2 = ∑ i, p i * γ i ^ 2 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_mul, hfr i]
    rw [← e1, ← e2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  -- inequality (2)
  have S2 : 0 ≤ ∑ i, ∑ j, g i j * (γ i - r j) := by
    refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
    rcases (hg0 i j).lt_or_eq with h | h
    · exact mul_nonneg h.le (sub_nonneg.2 (core i j (hgsupp h.ne')))
    · rw [← h]; simp
  have S2e : ∑ i, ∑ j, g i j * (γ i - r j)
      = ∑ i, p i * r i * γ i - ∑ j, p j * r j ^ 2 := by
    have e1 : ∑ i, ∑ j, g i j * γ i = ∑ i, p i * r i * γ i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_mul, hgr i, hp'r i]; ring
    have e2 : ∑ i, ∑ j, g i j * r j = ∑ j, p j * r j ^ 2 := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.sum_mul, hgc j, hp'r j]; ring
    rw [← e1, ← e2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have Q : ∑ i, p i * (r i - γ i) ^ 2
      = ∑ i, p i * r i ^ 2 - 2 * ∑ i, p i * r i * γ i + ∑ i, p i * γ i ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have Qle : ∑ i, p i * (r i - γ i) ^ 2 ≤ 0 := by
    rw [Q]; linarith
  have Qnn : ∀ i ∈ Finset.univ, 0 ≤ p i * (r i - γ i) ^ 2 :=
    fun i _ => mul_nonneg (hppos i).le (sq_nonneg _)
  have Q0 : ∑ i, p i * (r i - γ i) ^ 2 = 0 := le_antisymm Qle (Finset.sum_nonneg Qnn)
  have hrγ : ∀ i, r i = γ i := fun i => by
    have h := (Finset.sum_eq_zero_iff_of_nonneg Qnn).1 Q0 i (Finset.mem_univ _)
    rcases mul_eq_zero.1 h with h | h
    · exact absurd h (hppos i).ne'
    · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h
      linarith
  -- equality in (2): every g-edge has γ i = r j
  have S20 : ∑ i, ∑ j, g i j * (γ i - r j) = 0 := by
    rw [S2e]
    have : ∑ i, p i * r i * γ i = ∑ j, p j * r j ^ 2 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hrγ i]; ring
    rw [this, sub_self]
  have Tnn : ∀ i j, 0 ≤ g i j * (γ i - r j) := fun i j => by
    rcases (hg0 i j).lt_or_eq with h | h
    · exact mul_nonneg h.le (sub_nonneg.2 (core i j (hgsupp h.ne')))
    · rw [← h]; simp
  have edge : ∀ i j, g i j ≠ 0 → γ i = r j := fun i j hne => by
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Finset.sum_nonneg fun j _ => Tnn i j)).1 S20 i (Finset.mem_univ _)
    have hij := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Tnn i j)).1 hi j
      (Finset.mem_univ _)
    rcases mul_eq_zero.1 hij with h | h
    · exact absurd h hne
    · linarith
  have hsame : ∀ i j, g i j / r i = g i j / r j := fun i j => by
    by_cases h : g i j = 0
    · simp [h]
    · rw [hrγ i, edge i j h]
  refine ⟨fun i j => g i j / r i, ⟨hppos, fun i j => div_nonneg (hg0 i j) (rpos i).le, ?_, ?_, ?_⟩, ?_⟩
  · intro e he
    have hne : g e.1 e.2 ≠ 0 := by
      intro h0; exact he (by show g e.1 e.2 / r e.1 = 0; rw [h0, zero_div])
    exact F4 e.1 e.2 (hgsupp hne) (le_of_eq (edge e.1 e.2 hne))
  · intro i
    rw [← Finset.sum_div, hgr i, hp'r i, mul_div_cancel_left₀ _ (rpos i).ne']
  · intro j
    simp_rw [hsame _ j]
    rw [← Finset.sum_div, hgc j, hp'r j, mul_div_cancel_left₀ _ (rpos j).ne']
  · unfold surplusL1 goodSurplus
    refine Finset.sum_eq_zero fun j _ => ?_
    simp_rw [hsame _ j]
    rw [← Finset.sum_div, hgc j, hp'r j, mul_div_cancel_left₀ _ (rpos j).ne', sub_self, abs_zero]
