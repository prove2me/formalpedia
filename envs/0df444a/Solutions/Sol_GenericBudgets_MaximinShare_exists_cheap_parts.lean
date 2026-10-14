-- Prove2me | solution 1 for GenericBudgets.MaximinShare.exists_cheap_parts
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T03:09:23.646711+00:00
-- url     : https://prove2.me/submissions/d89210b9-5db3-46c6-bd83-a50d95db6853

import Mathlib
import Definitions.Def_GenericBudgets_MaximinShare_Setting

open GenericBudgets.MaximinShare

theorem solution {m d : ℕ} (p : Fin m → ℝ)
    (T : Fin m → Fin d) (ℓ : ℕ) (hd : 0 < d) (hℓ : ℓ ≤ d) :
    ∃ L : Finset (Fin d), L.card = ℓ ∧
      GenericBudgets.AlmostEqual.price p (partsUnion T L) ≤ ((ℓ : ℝ) / d) * GenericBudgets.AlmostEqual.price p Finset.univ := by
  classical
  let w : Fin d → ℝ := fun k => ∑ j ∈ Finset.univ.filter (fun j => T j = k), p j
  have hs (L : Finset (Fin d)) :
      GenericBudgets.AlmostEqual.price p (partsUnion T L) = ∑ k ∈ L, w k := by
    simp only [GenericBudgets.AlmostEqual.price, partsUnion, w, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    simp
  have htot : (∑ k, w k) = GenericBudgets.AlmostEqual.price p Finset.univ := by
    simpa [partsUnion] using (hs Finset.univ).symm
  have hex : (Finset.univ.powersetCard ℓ : Finset (Finset (Fin d))).Nonempty := by
    apply Finset.powersetCard_nonempty.mpr
    simpa using hℓ
  obtain ⟨L, hL, hmin⟩ := Finset.exists_min_image
    (Finset.univ.powersetCard ℓ) (fun K : Finset (Fin d) => ∑ k ∈ K, w k) hex
  have hcard : L.card = ℓ := (Finset.mem_powersetCard.mp hL).2
  have hlow (a : Fin d) (ha : a ∈ L) (b : Fin d) (hb : b ∉ L) : w a ≤ w b := by
    have hb' : b ∉ L.erase a := fun h => hb (Finset.mem_of_mem_erase h)
    have hc : insert b (L.erase a) ∈ (Finset.univ : Finset (Fin d)).powersetCard ℓ := by
      apply Finset.mem_powersetCard.mpr
      refine ⟨Finset.subset_univ _, ?_⟩
      rw [Finset.card_insert_of_notMem hb', Finset.card_erase_of_mem ha, hcard]
      have : 0 < ℓ := hcard ▸ Finset.card_pos.mpr ⟨a,ha⟩
      omega
    have hi := hmin _ hc
    rw [Finset.sum_insert hb'] at hi
    have he := Finset.sum_erase_add L w ha
    linarith
  have hpairs : (∑ a ∈ L, ∑ b ∈ Lᶜ, w a) ≤ ∑ a ∈ L, ∑ b ∈ Lᶜ, w b := by
    apply Finset.sum_le_sum
    intro a ha
    apply Finset.sum_le_sum
    intro b hb
    exact hlow a ha b (Finset.mem_compl.mp hb)
  have hcomp : ((Lᶜ.card : ℕ) : ℝ) = (d : ℝ) - ℓ := by
    rw [Finset.card_compl, Fintype.card_fin, hcard, Nat.cast_sub hℓ]
  have hpairs' : ((d : ℝ)-ℓ) * (∑ a ∈ L, w a) ≤ (ℓ : ℝ) * (∑ b ∈ Lᶜ, w b) := by
    simpa only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, hcomp, hcard] using hpairs
  have hadd : (∑ a ∈ L, w a) + (∑ b ∈ Lᶜ, w b) = ∑ k, w k :=
    Finset.sum_add_sum_compl L w
  refine ⟨L,hcard,?_⟩
  rw [hs, ← htot, div_mul_eq_mul_div]
  apply (le_div_iff₀ (by exact_mod_cast hd : (0:ℝ)<d)).2
  nlinarith
