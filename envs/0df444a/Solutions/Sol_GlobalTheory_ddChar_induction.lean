-- Prove2me | solution 1 for GlobalTheory.ddChar_induction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:51:33.624415+00:00
-- url     : https://prove2.me/submissions/0e945c52-981f-4aa5-9b97-43bfb6d38f43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GeneralLinearGroupCharEqOneOfDetEqOne
import Theorems.Thm_GlobalTheory_ddChar_stable
import Theorems.Thm_GlobalTheory_ddChar_diag
import Theorems.Thm_GlobalTheory_ddChar_det_unip
import Theorems.Thm_GlobalTheory_ddChar_row
import Theorems.Thm_GlobalTheory_ddChar_col
import Theorems.Thm_GlobalTheory_ddChar_unip_mul_apply
import Theorems.Thm_GlobalTheory_ddChar_mul_unip_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Matrix
variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
  {A : Type} [CommGroup A]
namespace GlobalTheory
theorem _root_.solution [Finite R] (ψ : GL n R →* A) (u : Rˣ) (hu : IsUnit ((u : R) - 1))
    (s : Finset n) : ∀ g : GL n R,
      (∀ i j, i ≠ j → (i ∉ s ∨ j ∉ s) → (g : Matrix n n R) i j = 0) →
      (g : Matrix n n R).det = 1 → ψ g = 1 := by
  induction s using Finset.induction_on with
  | empty =>
    intro g hg hdet
    exact ddChar_diag ψ g (fun i j hij => hg i j hij (Or.inl (Finset.notMem_empty i))) hdet
  | insert a s ha ih =>
    intro g hg hdet
    have hinv : ∑ k, ((g⁻¹ : GL n R) : Matrix n n R) a k * (g : Matrix n n R) k a = 1 := by
      have := congrArg (fun M : GL n R => (M : Matrix n n R) a a) (inv_mul_cancel g)
      simp only [Units.val_mul, Units.val_one, Matrix.mul_apply, Matrix.one_apply_eq] at this
      exact this
    have hz : ∀ k ∈ (Finset.univ : Finset n), k ∉ insert a s →
        ((g⁻¹ : GL n R) : Matrix n n R) a k * (g : Matrix n n R) k a = 0 := by
      intro k _ hk
      have hka : k ≠ a := fun e => hk (e ▸ Finset.mem_insert_self a s)
      rw [hg k a hka (Or.inl hk), mul_zero]
    have hwvb : ((g⁻¹ : GL n R) : Matrix n n R) a a * (g : Matrix n n R) a a +
        ∑ k ∈ s, ((g⁻¹ : GL n R) : Matrix n n R) a k * (g : Matrix n n R) k a = 1 := by
      rw [← Finset.sum_insert ha (f := fun k => ((g⁻¹ : GL n R) : Matrix n n R) a k * (g : Matrix n n R) k a),
        Finset.sum_subset (Finset.subset_univ _) hz]
      exact hinv
    obtain ⟨t, ht⟩ := ddChar_stable hwvb
    let y1 : n → R := fun k => if k ∈ s then t * ((g⁻¹ : GL n R) : Matrix n n R) a k else 0
    have hy1a : y1 a = 0 := by simp [y1, ha]
    have h1 : y1 ⬝ᵥ Pi.single a 1 = 0 := by rw [dotProduct_single, hy1a, zero_mul]
    let g1 : GL n R := ddCharUnip _ (ddChar_vecMulVec_sq h1) * g
    have e1 : ∀ i j, (g1 : Matrix n n R) i j =
        (g : Matrix n n R) i j + (Pi.single a (1 : R) : n → R) i * ∑ k, y1 k * (g : Matrix n n R) k j :=
      fun i j => ddChar_unip_mul_apply h1 g i j
    have hsum1 : ∀ j, ∑ k, y1 k * (g : Matrix n n R) k j =
        ∑ k ∈ s, t * ((g⁻¹ : GL n R) : Matrix n n R) a k * (g : Matrix n n R) k j := by
      intro j
      simp only [y1, ite_mul, zero_mul]
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    have hg1aa : IsUnit ((g1 : Matrix n n R) a a) := by
      rw [e1, hsum1, Pi.single_eq_same, one_mul]
      convert ht using 2
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    have hs1 : ∀ i j, i ≠ j → (i ∉ insert a s ∨ j ∉ insert a s) → (g1 : Matrix n n R) i j = 0 := by
      intro i j hij hout
      rw [e1]
      by_cases hia : i = a
      · subst hia
        have hj : j ∉ insert i s := by
          rcases hout with h | h
          · exact absurd (Finset.mem_insert_self i s) h
          · exact h
        rw [hg i j hij (Or.inr hj), zero_add, hsum1]
        refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun k hk => ?_)
        have hkj : k ≠ j := fun e => hj (e ▸ Finset.mem_insert_of_mem hk)
        rw [hg k j hkj (Or.inr hj), mul_zero]
      · rw [Pi.single_eq_of_ne hia, zero_mul, add_zero]
        exact hg i j hij hout
    have hdet1 : (g1 : Matrix n n R).det = 1 := by
      rw [Units.val_mul, det_mul, ddChar_det_unip h1, hdet, one_mul]
    have hψ1 : ψ g1 = ψ g := by rw [map_mul, ddChar_row ψ u hu a y1 hy1a h1, one_mul]
    let C : R := (g1 : Matrix n n R) a a
    let ci : R := ((hg1aa.unit⁻¹ : Rˣ) : R)
    have hCci : C * ci = 1 := hg1aa.mul_val_inv
    have hciC : ci * C = 1 := by rw [mul_comm]; exact hCci
    let x2 : n → R := fun i => if i = a then 0 else -((g1 : Matrix n n R) i a * ci)
    have hx2a : x2 a = 0 := by simp [x2]
    have h2 : Pi.single a 1 ⬝ᵥ x2 = 0 := by rw [single_dotProduct, hx2a, mul_zero]
    let g2 : GL n R := ddCharUnip _ (ddChar_vecMulVec_sq h2) * g1
    have e2 : ∀ i j, (g2 : Matrix n n R) i j = (g1 : Matrix n n R) i j + x2 i * (g1 : Matrix n n R) a j := by
      intro i j
      rw [ddChar_unip_mul_apply h2 g1 i j]
      congr 2
      simp [Pi.single_apply, ite_mul]
    have hg2a : ∀ i, i ≠ a → (g2 : Matrix n n R) i a = 0 := by
      intro i hia
      rw [e2]
      simp only [x2, if_neg hia]
      change (g1 : Matrix n n R) i a + -((g1 : Matrix n n R) i a * ci) * C = 0
      rw [neg_mul, mul_assoc, hciC, mul_one, add_neg_cancel]
    have hg2aj : ∀ j, (g2 : Matrix n n R) a j = (g1 : Matrix n n R) a j := by
      intro j
      rw [e2, hx2a, zero_mul, add_zero]
    have hs2 : ∀ i j, i ≠ j → (i ∉ insert a s ∨ j ∉ insert a s) → (g2 : Matrix n n R) i j = 0 := by
      intro i j hij hout
      by_cases hia : i = a
      · subst hia
        rw [hg2aj]
        exact hs1 i j hij hout
      · rw [e2, hs1 i j hij hout, zero_add]
        simp only [x2, if_neg hia]
        rcases hout with h | h
        · rw [hs1 i a hia (Or.inl h), zero_mul, neg_zero, zero_mul]
        · have haj : a ≠ j := fun e => h (e ▸ Finset.mem_insert_self a s)
          rw [hs1 a j haj (Or.inr h), mul_zero]
    have hdet2 : (g2 : Matrix n n R).det = 1 := by
      rw [Units.val_mul, det_mul, ddChar_det_unip h2, hdet1, one_mul]
    have hψ2 : ψ g2 = ψ g1 := by rw [map_mul, ddChar_col ψ u hu a x2 hx2a h2, one_mul]
    let y3 : n → R := fun j => if j = a then 0 else -(ci * (g2 : Matrix n n R) a j)
    have hy3a : y3 a = 0 := by simp [y3]
    have h3 : y3 ⬝ᵥ Pi.single a 1 = 0 := by rw [dotProduct_single, hy3a, zero_mul]
    let g3 : GL n R := g2 * ddCharUnip _ (ddChar_vecMulVec_sq h3)
    have e3 : ∀ i j, (g3 : Matrix n n R) i j = (g2 : Matrix n n R) i j + (g2 : Matrix n n R) i a * y3 j := by
      intro i j
      rw [ddChar_mul_unip_apply h3 g2 i j]
      congr 2
      simp [Pi.single_apply]
    have hg2aa : (g2 : Matrix n n R) a a = C := by rw [hg2aj]
    have hs3 : ∀ i j, i ≠ j → (i ∉ s ∨ j ∉ s) → (g3 : Matrix n n R) i j = 0 := by
      intro i j hij hout
      rw [e3]
      by_cases hia : i = a
      · subst hia
        have hja : j ≠ i := fun e => hij e.symm
        simp only [y3, if_neg hja]
        rw [hg2aa, mul_neg, ← mul_assoc, hCci, one_mul, add_neg_cancel]
      · rw [hg2a i hia, zero_mul, add_zero]
        by_cases hja : j = a
        · subst hja
          exact hg2a i hia
        · have hout' : i ∉ insert a s ∨ j ∉ insert a s := by
            rcases hout with h | h
            · exact Or.inl (by simp [hia, h])
            · exact Or.inr (by simp [hja, h])
          exact hs2 i j hij hout'
    have hdet3 : (g3 : Matrix n n R).det = 1 := by
      rw [Units.val_mul, det_mul, ddChar_det_unip h3, hdet2, mul_one]
    have hψ3 : ψ g3 = ψ g2 := by rw [map_mul, ddChar_row ψ u hu a y3 hy3a h3, mul_one]
    rw [← hψ1, ← hψ2, ← hψ3]
    exact ih g3 hs3 hdet3
end GlobalTheory
