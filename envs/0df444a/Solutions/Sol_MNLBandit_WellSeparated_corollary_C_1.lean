-- Prove2me | solution 1 for MNLBandit.WellSeparated.corollary_C_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T07:07:50.597993+00:00
-- url     : https://prove2.me/submissions/acad7fdd-1a6d-4e93-aae4-232bfa4a8660

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_MNLBandit_WellSeparated_Setting



namespace MNLBandit.WellSeparated

open ChoiceCDLP.MNL

theorem g58_Tcount_step {N T : ℕ} (r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (h : Fin T → Option (Fin N)) (i : Fin N) (ℓ m ℓ' : ℕ) (h1 : ℓ < m) (h2 : m ≤ ℓ')
    (hi : i ∈ epochSet r sel h m) :
    Tcount r sel h i ℓ + 1 ≤ Tcount r sel h i ℓ' := by
  classical
  unfold Tcount
  have hm : m ∉ (Finset.Icc 1 ℓ).filter (fun τ => i ∈ epochSet r sel h τ) := by
    simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  rw [← Finset.card_insert_of_notMem hm]
  convert Finset.card_le_card (s := insert m ((Finset.Icc 1 ℓ).filter (fun τ => i ∈ epochSet r sel h τ)))
    (t := (Finset.Icc 1 ℓ').filter (fun τ => i ∈ epochSet r sel h τ)) ?_
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_Icc] at hx ⊢
  rcases hx with rfl | ⟨⟨a, b⟩, c⟩
  · exact ⟨⟨by omega, h2⟩, hi⟩
  · exact ⟨⟨a, by omega⟩, c⟩

theorem g58_card_bad (lam : ℝ) (hlam : 0 ≤ lam) :
    (((Finset.Ico 1 ⌈lam⌉₊).card : ℕ) : ℝ) ≤ lam := by
  rw [Nat.card_Ico]
  rcases Nat.eq_zero_or_pos ⌈lam⌉₊ with h0 | hpos
  · simp [h0, hlam]
  · have := Nat.ceil_lt_add_one hlam
    rw [Nat.cast_sub (by omega)]
    push_cast
    linarith

theorem corollary_C_1_core (N : ℕ) (v r : Fin N → ℝ) (𝒮 : Finset (Finset (Fin N)))
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (T : ℕ) (h : Fin T → Option (Fin N)) :
    (((Finset.Icc 1 (epochsStarted r sel h)).filter (fun ℓ =>
        ∃ i ∈ epochSet r sel h ℓ, (Tcount r sel h i ℓ : ℝ) < Real.log (N * T))).card : ℝ)
      ≤ N * Real.log (N * T) := by
  classical
  set lam := Real.log (N * T) with hlamdef
  have hlam : 0 ≤ lam := by
    rw [hlamdef]; exact_mod_cast Real.log_natCast_nonneg (N * T)
  set F := (Finset.Icc 1 (epochsStarted r sel h)).filter (fun ℓ =>
        ∃ i ∈ epochSet r sel h ℓ, (Tcount r sel h i ℓ : ℝ) < lam) with hF
  have hsub : F ⊆ Finset.univ.biUnion (fun i : Fin N =>
      (Finset.Icc 1 (epochsStarted r sel h)).filter (fun ℓ =>
        i ∈ epochSet r sel h ℓ ∧ (Tcount r sel h i ℓ : ℝ) < lam)) := by
    intro ℓ hℓ
    simp only [hF, Finset.mem_filter] at hℓ
    obtain ⟨h1, i, hi1, hi2⟩ := hℓ
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
    exact ⟨i, h1, hi1, hi2⟩
  have hfib : ∀ i : Fin N, ((Finset.Icc 1 (epochsStarted r sel h)).filter (fun ℓ =>
        i ∈ epochSet r sel h ℓ ∧ (Tcount r sel h i ℓ : ℝ) < lam)).card ≤
        (Finset.Ico 1 ⌈lam⌉₊).card := by
    intro i
    apply Finset.card_le_card_of_injOn (fun ℓ => Tcount r sel h i ℓ)
    · intro ℓ hℓ
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Icc] at hℓ
      simp only [Finset.coe_Ico, Set.mem_Ico]
      refine ⟨?_, Nat.lt_ceil.2 hℓ.2.2⟩
      have := g58_Tcount_step r sel h i 0 ℓ ℓ (by omega) le_rfl hℓ.2.1
      simp [Tcount] at this ⊢
      exact this
    · intro a ha b hb hab
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha hb
      simp only at hab
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have := g58_Tcount_step r sel h i a b b hlt le_rfl hb.2.1
        omega
      · have := g58_Tcount_step r sel h i b a a hlt le_rfl ha.2.1
        omega
  have hcard : F.card ≤ N * (Finset.Ico 1 ⌈lam⌉₊).card := by
    calc F.card ≤ _ := Finset.card_le_card hsub
      _ ≤ _ := Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin N, (Finset.Ico 1 ⌈lam⌉₊).card := Finset.sum_le_sum (fun i _ => hfib i)
      _ = _ := by simp
  calc (F.card : ℝ) ≤ ((N * (Finset.Ico 1 ⌈lam⌉₊).card : ℕ) : ℝ) := by exact_mod_cast hcard
    _ ≤ N * lam := by
      push_cast
      exact mul_le_mul_of_nonneg_left (g58_card_bad lam hlam) (by positivity)

end MNLBandit.WellSeparated

open MNLBandit.WellSeparated
open ChoiceCDLP.MNL

theorem solution (N : ℕ) (v r : Fin N → ℝ) (𝒮 : Finset (Finset (Fin N)))
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (hTU : MNLBandit.UCB.IsTU 𝒮) (hdown : MNLBandit.UCB.DownClosed 𝒮) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1)
    (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1) (hsel : MNLBandit.UCB.IsArgmaxSel 𝒮 sel)
    (T : ℕ) (h : Fin T → Option (Fin N)) :
    (((Finset.Icc 1 (epochsStarted r sel h)).filter (fun ℓ =>
        ∃ i ∈ epochSet r sel h ℓ, (Tcount r sel h i ℓ : ℝ) < Real.log (N * T))).card : ℝ)
      ≤ N * Real.log (N * T) := by
  exact corollary_C_1_core N v r 𝒮 sel T h
