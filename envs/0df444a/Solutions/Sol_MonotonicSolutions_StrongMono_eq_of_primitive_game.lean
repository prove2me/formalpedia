-- Prove2me | solution 1 for MonotonicSolutions.StrongMono.eq_of_primitive_game
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:00:57.475328+00:00
-- url     : https://prove2.me/submissions/61960e64-2ac0-4a64-b8ea-090d325266a6

import Mathlib
import Definitions.Def_MonotonicSolutions_StrongMono_Game
import Definitions.Def_MonotonicSolutions_StrongMono_Axioms
import Definitions.Def_MonotonicSolutions_StrongMono_Unanimity

namespace MonotonicSolutions.StrongMono

/-- The zero game. -/
def aux_epg_zero (n : ℕ) : Game n := ⟨fun _ => 0, rfl⟩

lemma aux_epg_zero_val {n : ℕ} (i : Fin n) :
    ∀ φ : Game n → Fin n → ℝ, IsAllocationProcedure φ → IsSymmetric φ →
      φ (aux_epg_zero n) i = 0 := by
  intro φ hA hS
  have hperm : ∀ σ : Equiv.Perm (Fin n), permGame σ (aux_epg_zero n) = aux_epg_zero n := by
    intro σ
    apply Subtype.ext
    funext T
    rfl
  have hall : ∀ j, φ (aux_epg_zero n) j = φ (aux_epg_zero n) i := by
    intro j
    have h := hS (Equiv.swap i j) (aux_epg_zero n) i
    rw [hperm, Equiv.swap_apply_left] at h
    exact h
  have hsum := hA (aux_epg_zero n)
  rw [Finset.sum_congr rfl (fun j _ => hall j)] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hn : (n : ℝ) ≠ 0 := by
    have : 0 < n := Fin.pos i
    exact_mod_cast this.ne'
  change _ = (0 : ℝ) at hsum
  rcases mul_eq_zero.mp hsum with h | h
  · exact absurd h hn
  · exact h

lemma aux_epg_perm {n : ℕ} (R : Finset (Fin n)) (c : ℝ) (v : Game n)
    (hv : ∀ S : Finset (Fin n), v.1 S = c * unanimity R S) (i j : Fin n)
    (hi : i ∈ R) (hj : j ∈ R) : permGame (Equiv.swap i j) v = v := by
  apply Subtype.ext
  funext T
  show v.1 (T.map (Equiv.swap i j).symm.toEmbedding) = v.1 T
  rw [hv, hv]
  unfold unanimity
  have hmemR : ∀ x ∈ R, Equiv.swap i j x ∈ R := by
    intro x hx
    rw [Equiv.swap_apply_def]
    split_ifs
    · exact hj
    · exact hi
    · exact hx
  have key : R ⊆ T.map (Equiv.swap i j).symm.toEmbedding ↔ R ⊆ T := by
    constructor
    · intro h y hy
      have := h (hmemR y hy)
      rw [Finset.mem_map_equiv, Equiv.symm_symm, Equiv.swap_apply_self] at this
      exact this
    · intro h x hx
      rw [Finset.mem_map_equiv, Equiv.symm_symm]
      exact h (hmemR x hx)
  by_cases hT : R ⊆ T
  · rw [if_pos (key.mpr hT), if_pos hT]
  · rw [if_neg (fun h => hT (key.mp h)), if_neg hT]

end MonotonicSolutions.StrongMono

open MonotonicSolutions.StrongMono

theorem solution {n : ℕ} (φ : Game n → Fin n → ℝ)
    (hA : IsAllocationProcedure φ) (hS : IsSymmetric φ) (hM : IsMarginal φ)
    (R : Finset (Fin n)) (hR : R.Nonempty) (c : ℝ) (v : Game n)
    (hv : ∀ S : Finset (Fin n), v.1 S = c * unanimity R S) (i : Fin n) :
    φ v i = if i ∈ R then c / R.card else 0 := by
  -- players outside R get 0
  have hout : ∀ k, k ∉ R → φ v k = 0 := by
    intro k hk
    have h := hM v (aux_epg_zero n) k (by
      intro S
      unfold marginal
      show _ = (if k ∈ S then (0:ℝ) - 0 else 0 - 0)
      split_ifs with hkS
      · rw [hv, hv]
        unfold unanimity
        simp [Finset.subset_erase, hk]
      · rw [hv, hv]
        unfold unanimity
        simp [Finset.subset_insert_iff_of_notMem hk])
    rw [h]
    exact aux_epg_zero_val k φ hA hS
  -- players inside R get equal amounts
  have hin : ∀ k j, k ∈ R → j ∈ R → φ v j = φ v k := by
    intro k j hk hj
    have h := hS (Equiv.swap k j) v k
    rw [aux_epg_perm R c v hv k j hk hj, Equiv.swap_apply_left] at h
    exact h
  split_ifs with hi
  · have hall : ∀ k, φ v k = if k ∈ R then φ v i else 0 := by
      intro k
      split_ifs with hk
      · exact hin i k hi hk
      · exact hout k hk
    have hsum := hA v
    rw [Finset.sum_congr rfl (fun k _ => hall k), hv] at hsum
    unfold unanimity at hsum
    rw [if_pos (Finset.subset_univ R), mul_one] at hsum
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul] at hsum
    have hc : (R.card : ℝ) ≠ 0 := by
      exact_mod_cast (Finset.card_pos.mpr hR).ne'
    rw [eq_div_iff hc, ← hsum, mul_comm]
  · exact hout i hi
