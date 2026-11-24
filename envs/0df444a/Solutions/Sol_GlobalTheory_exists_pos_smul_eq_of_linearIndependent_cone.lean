-- Prove2me | solution 1 for GlobalTheory.exists_pos_smul_eq_of_linearIndependent_cone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:45:44.766557+00:00
-- url     : https://prove2.me/submissions/c5ab4994-6f05-476e-884f-992ccab79dcb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsPosSmulEqOfLinearIndependentCone

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {L : Type} [AddCommGroup L] {m m' : ℕ}
    (δ : Fin m → L) (γ : Fin m' → L) (i : Fin m) (k : ℕ)
    (a : Fin m' → ℕ) (hδ : LinearIndependent ℤ δ) (hk : 0 < k) (hsum : k • δ i = ∑ j, a j • γ j)
    (hγ : ∀ j, 0 < a j → ∃ (k' : ℕ) (b : Fin m → ℕ), 0 < k' ∧ k' • γ j = ∑ l, b l • δ l) :
    ∃ (j : Fin m') (p r : ℕ), 0 < p ∧ 0 < r ∧ p • δ i = r • γ j := by
  classical
  have hγ' : ∀ j, ∃ (k' : ℕ) (b : Fin m → ℕ), 0 < k' ∧ (0 < a j → k' • γ j = ∑ l, b l • δ l) := by
    intro j
    by_cases hj : 0 < a j
    · obtain ⟨k', b, hk', h⟩ := hγ j hj
      exact ⟨k', b, hk', fun _ => h⟩
    · exact ⟨1, 0, one_pos, fun h => absurd h hj⟩
  choose kk b hkk hb using hγ'
  let c : Fin m' → ℕ := fun j => ∏ j' ∈ univ.erase j, kk j'
  let K : ℕ := ∏ j, kk j
  have hcK : ∀ j, c j * kk j = K := fun j => by
    rw [mul_comm]; exact Finset.mul_prod_erase _ _ (mem_univ j)
  have hcpos : ∀ j, 0 < c j := fun j => Finset.prod_pos (fun j' _ => hkk j')
  have hKpos : 0 < K := Finset.prod_pos (fun j _ => hkk j)
  have hterm : ∀ j, (K * a j) • γ j = (a j * c j) • ∑ l, b j l • δ l := by
    intro j
    by_cases hj : 0 < a j
    · rw [← hb j hj, smul_smul, ← hcK j]; congr 1; ring
    · have : a j = 0 := Nat.eq_zero_of_not_pos hj
      simp [this]
  have key : (K * k) • δ i = ∑ l, (∑ j, a j * c j * b j l) • δ l := by
    calc (K * k) • δ i = K • (k • δ i) := mul_smul _ _ _
      _ = ∑ j, (K * a j) • γ j := by rw [hsum, Finset.smul_sum]; simp_rw [smul_smul]
      _ = ∑ j, (a j * c j) • ∑ l, b j l • δ l := Finset.sum_congr rfl (fun j _ => hterm j)
      _ = ∑ l, (∑ j, a j * c j * b j l) • δ l := by
          simp_rw [Finset.smul_sum, smul_smul, Finset.sum_smul]
          rw [Finset.sum_comm]
  let N : Fin m → ℕ := fun l => ∑ j, a j * c j * b j l
  let g : Fin m → ℤ := fun l => (N l : ℤ) - (if l = i then ((K * k : ℕ) : ℤ) else 0)
  have hg : ∑ l, g l • δ l = 0 := by
    simp only [g, sub_smul, Finset.sum_sub_distrib, ite_smul, zero_smul, Finset.sum_ite_eq',
      mem_univ, if_true, natCast_zsmul]
    rw [key]; exact sub_self _
  have hg0 := Fintype.linearIndependent_iff.mp hδ g hg
  have hN : ∀ l, N l = if l = i then K * k else 0 := by
    intro l
    have := hg0 l
    simp only [g] at this
    split_ifs at this ⊢ <;> omega
  have hNi : N i ≠ 0 := by rw [hN i, if_pos rfl]; exact (Nat.mul_pos hKpos hk).ne'
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hNi
  have haj : 0 < a j := Nat.pos_of_ne_zero (fun h => hj (by simp [h]))
  have hbji : 0 < b j i := Nat.pos_of_ne_zero (fun h => hj (by simp [h]))
  have hbjl : ∀ l, l ≠ i → b j l = 0 := by
    intro l hl
    have h0 : N l = 0 := by rw [hN l, if_neg hl]
    have := (Finset.sum_eq_zero_iff.mp h0) j (mem_univ j)
    rcases Nat.mul_eq_zero.mp this with h | h
    · rcases Nat.mul_eq_zero.mp h with h | h
      · omega
      · exact absurd h (hcpos j).ne'
    · exact h
  have hγj : kk j • γ j = b j i • δ i := by
    rw [hb j haj, Finset.sum_eq_single i]
    · intro l _ hl; rw [hbjl l hl, zero_smul]
    · intro h; exact absurd (mem_univ i) h
  exact ⟨j, b j i, kk j, hbji, hkk j, hγj.symm⟩
end GlobalTheory
