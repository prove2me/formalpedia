-- Prove2me | solution 2 for MatousekLP.Integrality.incidenceMatrix_totallyUnimodular
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T00:54:04.052455+00:00
-- url     : https://prove2.me/submissions/96f612df-6b2c-42bd-b906-8e4ceb5d6692

import Mathlib
import Definitions.Def_MatousekLP_Integrality_BipartiteGraph
import Definitions.Def_MatousekLP_Integrality_IncidenceMatrix

set_option autoImplicit false

namespace IncidenceTU

open Matrix

/-- A zero-one matrix with at most one nonzero of each color in each column
has all square minors in `{-1, 0, 1}`. -/
private lemma det_two_colors (k : ℕ) (A : Matrix (Fin k) (Fin k) ℝ)
    (p : Fin k → Bool) (hentry : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hsame : ∀ j i l, p i = p l → A i j ≠ 0 → A l j ≠ 0 → i = l) :
    A.det ∈ Set.range SignType.cast := by
  classical
  induction k with
  | zero => exact ⟨1, by simp⟩
  | succ k ih =>
    by_cases hsparse : ∃ j i, ∀ r, r ≠ i → A r j = 0
    · obtain ⟨j, i, hi⟩ := hsparse
      rw [det_succ_column A j, Fintype.sum_eq_single i (fun r hr => by simp [hi r hr])]
      have hminor := ih (A.submatrix i.succAbove j.succAbove) (p ∘ i.succAbove)
        (fun r c => hentry _ _)
        (fun c r s h hrs hss => Fin.succAbove_right_injective
          (hsame _ _ _ h hrs hss))
      change _ ∈ MonoidHom.mrange SignType.castHom.toMonoidHom
      refine mul_mem (mul_mem ?_ ?_) hminor
      · exact pow_mem (show (-1 : ℝ) ∈ MonoidHom.mrange SignType.castHom.toMonoidHom
          from ⟨-1, by simp⟩) _
      · rcases hentry i j with h | h <;> rw [h]
        · exact ⟨0, by simp⟩
        · exact ⟨1, by simp⟩
    · have hpair : ∀ j, ∃ i l, i ≠ l ∧ A i j = 1 ∧ A l j = 1 ∧
          p i ≠ p l ∧ ∀ r, r ≠ i → r ≠ l → A r j = 0 := by
        intro j
        have hex : ∃ i, A i j ≠ 0 := by
          by_contra h
          push_neg at h
          exact hsparse ⟨j, 0, fun r _ => h r⟩
        obtain ⟨i, hi⟩ := hex
        have hex' : ∃ l, l ≠ i ∧ A l j ≠ 0 := by
          by_contra h
          push_neg at h
          exact hsparse ⟨j, i, h⟩
        obtain ⟨l, hli, hl⟩ := hex'
        have hp : p i ≠ p l := fun h => hli (hsame j i l h hi hl).symm
        refine ⟨i, l, hli.symm, (hentry i j).resolve_left hi,
          (hentry l j).resolve_left hl, hp, ?_⟩
        intro r hri hrl
        by_contra hr
        by_cases hpi : p r = p i
        · exact hri (hsame j r i hpi hr hi)
        · have hpl : p r = p l := by
            cases hpr : p r <;> cases hpi' : p i <;> cases hpl' : p l <;>
              simp [hpr, hpi', hpl'] at hpi hp ⊢
          exact hrl (hsame j r l hpl hr hl)
      let s : Fin (k + 1) → ℝ := fun r => if p r then 1 else -1
      have hkernel : s ᵥ* A = 0 := by
        funext j
        obtain ⟨i, l, hil, hi, hl, hp, hzero⟩ := hpair j
        change (∑ r, s r * A r j) = 0
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
        rw [Finset.sum_eq_single l]
        · rw [hi, hl]
          cases hpi : p i <;> cases hpl : p l <;> simp [s, hpi, hpl] at hp ⊢
        · intro r hr hrl
          have hri : r ≠ i := (Finset.mem_erase.mp hr).1
          simp [hzero r hri hrl]
        · simp [hil.symm]
      have hz : A.det = 0 := by
        by_contra hd
        have hs := Matrix.eq_zero_of_vecMul_eq_zero hd hkernel
        have hs0 := congrFun hs 0
        cases hp0 : p 0 <;> simp [s, hp0] at hs0
      exact ⟨0, by simp [hz]⟩

end IncidenceTU

open MatousekLP.Integrality in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : IsBipartite G) :
    (incidenceMatrix G).IsTotallyUnimodular := by
  classical
  obtain ⟨X, Y, hdisj, huniv, hadj⟩ := hG
  intro k f g hf hg
  refine IncidenceTU.det_two_colors k _ (fun i => decide (f i ∈ X))
    (fun i j => by
      change (if f i ∈ (g j : Sym2 V) then (1 : ℝ) else 0) = 0 ∨
        (if f i ∈ (g j : Sym2 V) then (1 : ℝ) else 0) = 1
      split <;> simp) ?_
  intro j i l hcolor hi hl
  have hfi : f i ∈ (g j : Sym2 V) := by
    by_contra h
    simp [incidenceMatrix, h] at hi
  have hfl : f l ∈ (g j : Sym2 V) := by
    by_contra h
    simp [incidenceMatrix, h] at hl
  generalize heq : (g j : Sym2 V) = e at hfi hfl
  have he : e ∈ G.edgeSet := heq ▸ (g j).property
  induction e using Sym2.ind with
  | h u v =>
    have huv : G.Adj u v := he
    have hdiff : decide (u ∈ X) ≠ decide (v ∈ X) := by
      rcases hadj u v huv with ⟨hu, hv⟩ | ⟨hu, hv⟩
      · have hvX : v ∉ X := fun h => Finset.disjoint_left.mp hdisj h hv
        simp [hu, hvX]
      · have huX : u ∉ X := fun h => Finset.disjoint_left.mp hdisj h hu
        simp [huX, hv]
    rcases Sym2.mem_iff.mp hfi with hfi | hfi <;>
      rcases Sym2.mem_iff.mp hfl with hfl | hfl
    · exact hf (hfi.trans hfl.symm)
    · exact False.elim (hdiff (by simpa [hfi, hfl] using hcolor))
    · exact False.elim (hdiff (by simpa [hfi, hfl] using hcolor.symm))
    · exact hf (hfi.trans hfl.symm)
