-- Prove2me | solution 1 for GlobalTheory.ValIwasawa.exists_clear_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:21:09.192699+00:00
-- url     : https://prove2.me/submissions/997cf8fe-26b6-4373-93f9-a2e2097ee07f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOfValILeOne
import Theorems.Thm_GlobalTheory_ValIwasawa_exists_of_valI_le_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ValIwasawa
open Matrix
variable {V F : Type} [CommRing V] [IsDomain V] [ValuationRing V] [Field F] [Algebra V F]
  [IsFractionRing V F]
namespace GlobalTheory.ValIwasawa
theorem _root_.solution {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (hA : A.det ≠ 0) :
    ∃ Q : Matrix (Fin (n + 1)) (Fin (n + 1)) V, IsUnit Q.det ∧
      ∀ i : Fin n, (Q.map (algebraMap V F) * A) i.succ 0 = 0 := by
  obtain ⟨p, -, hp⟩ := Finset.exists_max_image Finset.univ (fun r => valI V (A r 0)) Finset.univ_nonempty
  have hcol : ∃ r, A r 0 ≠ 0 := by
    by_contra h
    push Not at h
    exact hA (Matrix.det_eq_zero_of_column_eq_zero 0 h)
  have hp0 : A p 0 ≠ 0 := by
    obtain ⟨r, hr⟩ := hcol
    intro h0
    have := hp r (Finset.mem_univ _)
    rw [h0, map_zero] at this
    exact hr ((valI V).zero_iff.1 (le_antisymm this zero_le))
  let σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 p
  let P : Matrix (Fin (n + 1)) (Fin (n + 1)) V := σ.toPEquiv.toMatrix
  have hc : ∀ i, ∃ a : V, algebraMap V F a = A (σ i) 0 / A p 0 := by
    intro i
    apply exists_of_valI_le_one
    rw [map_div₀]
    have hpos : valI V (A p 0) ≠ 0 := by simpa using hp0
    rw [div_le_one₀ (zero_lt_iff.2 hpos)]
    exact hp _ (Finset.mem_univ _)
  choose c hc using hc
  let E : Matrix (Fin (n + 1)) (Fin (n + 1)) V := Matrix.of fun i j =>
    if i = j then 1 else if j = 0 then -c i else 0
  refine ⟨E * P, ?_, ?_⟩
  · rw [Matrix.det_mul]
    refine IsUnit.mul ?_ ?_
    · have hE : E.det = 1 := by
        rw [Matrix.det_of_lowerTriangular E]
        · simp [E]
        · intro i j hij
          have hij' : i < j := hij
          have hj : j ≠ 0 := fun h => by subst h; exact Fin.not_lt_zero _ hij'
          simp only [E, Matrix.of_apply, if_neg (ne_of_lt hij'), if_neg hj]
      rw [hE]; exact isUnit_one
    · simp only [P, Matrix.det_permutation]
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  · intro i
    rw [Matrix.map_mul, Matrix.mul_assoc, Matrix.mul_apply, Fin.sum_univ_succ]
    have hPA : ∀ r, (P.map (algebraMap V F) * A) r 0 = A (σ r) 0 := by
      intro r
      simp [P, Matrix.mul_apply, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
    simp only [hPA, Matrix.map_apply, E, Matrix.of_apply]
    rw [if_neg (Fin.succ_ne_zero i)]
    simp only [if_true, Fin.succ_ne_zero, map_neg, map_one, map_zero, zero_mul]
    rw [Finset.sum_eq_single i]
    · simp only [if_true, map_one, one_mul]
      rw [hc]
      have : σ 0 = p := by simp [σ]
      rw [this]
      field_simp
      ring
    · intro j _ hji
      rw [if_neg (fun h => hji (Fin.succ_injective _ h).symm)]
      simp
    · intro h; exact absurd (Finset.mem_univ i) h
end GlobalTheory.ValIwasawa
