-- Prove2me | solution 1 for GlobalTheory.MinorNorm.capelli_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:57:39.193103+00:00
-- url     : https://prove2.me/submissions/e32a30d9-9801-46f7-a38f-d55dddb301cb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_BottomMinor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PolarisationOperatorApplyVariable
import Theorems.Thm_GlobalTheory_MinorNorm_deriv_det
import Theorems.Thm_GlobalTheory_MinorNorm_det_cons
import Theorems.Thm_GlobalTheory_MinorNorm_det_cons_self
import Theorems.Thm_GlobalTheory_MinorNorm_pol_apply
import Theorems.Thm_GlobalTheory_MinorNorm_iterD_zero
import Theorems.Thm_GlobalTheory_MinorNorm_sum_pol_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix Finset
noncomputable section
open GlobalTheory GlobalTheory.MinorNorm
variable {R : Type} [CommRing R] [Algebra ℂ R]
variable {k : ℕ} (x : Fin k → Fin k → R) (d : Fin k → Fin k → Derivation ℂ R R)
variable {x d}
namespace GlobalTheory.MinorNorm
theorem _root_.solution (hd : ∀ r j s c, d r j (x s c) = if r = s ∧ j = c then 1 else 0)
    (a : Fin k → ℕ) (P : R) (hup : ∀ i j, i < j → pol x d i j P = 0)
    (hwt : ∀ j, pol x d j j P = a j * P) :
    ∀ (m : ℕ) (J I : Fin m → Fin k), (∀ t, (J t : ℕ) + m = k + t) →
      ∑ ρ : Fin m → Fin k, (Matrix.of fun t s => x (ρ t) (I s)).det * iterD d m ρ J P =
        ((∏ t, (a (J t) + (k - (J t + 1))) : ℕ) : R) *
          (Matrix.of fun t s => if I s = J t then (1 : R) else 0).det * P := by
  intro m
  induction m with
  | zero => intro J I _; simp [iterD_zero]
  | succ m ih =>
    intro J I hJ
    have hJ' : ∀ t, (Fin.tail J t : ℕ) + m = k + t := by
      intro t
      have := hJ t.succ
      simp only [Fin.val_succ] at this
      simp only [Fin.tail]
      omega
    have h0 : k - (J 0 + 1) = m := by
      have := hJ 0
      simp only [Fin.val_zero] at this
      omega
    set j := J 0 with hj
    set c : R := ((∏ t, (a (Fin.tail J t) + (k - (Fin.tail J t + 1))) : ℕ) : R) with hc
    set δ : Fin m → Fin (m + 1) → R := fun t s => if I s = Fin.tail J t then (1 : R) else 0 with hδ
    have ih' : ∀ s : Fin (m + 1), ∑ ρ : Fin m → Fin k,
        (Matrix.of fun t u => x (ρ t) (I (s.succAbove u))).det * iterD d m ρ (Fin.tail J) P =
        c * (Matrix.of fun t u => δ t (s.succAbove u)).det * P :=
      fun s => ih (Fin.tail J) (fun u => I (s.succAbove u)) hJ'

    have e1 : ∑ ρ : Fin (m + 1) → Fin k,
        (Matrix.of fun t s => x (ρ t) (I s)).det * iterD d (m + 1) ρ J P =
        ∑ ρ : Fin m → Fin k, ∑ s : Fin (m + 1), (-1) ^ (s : ℕ) *
          ((Matrix.of fun t u => x (ρ t) (I (s.succAbove u))).det *
            pol x d (I s) j (iterD d m ρ (Fin.tail J) P)) := by
      rw [← (Fin.consEquiv fun _ : Fin (m + 1) => Fin k).sum_comp, Fintype.sum_prod_type,
        Finset.sum_comm]
      refine Finset.sum_congr rfl fun ρ _ => ?_
      simp only [pol_apply, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [det_succ_row_zero, Finset.sum_mul]
      refine Finset.sum_congr rfl fun s _ => ?_
      have e : ((Matrix.of fun t s => x ((Fin.consEquiv fun _ : Fin (m + 1) => Fin k) (r, ρ) t)
          (I s)).submatrix Fin.succ s.succAbove) =
          Matrix.of fun t u => x (ρ t) (I (s.succAbove u)) := rfl
      rw [e]
      change (-1) ^ (s : ℕ) * x r (I s) * _ * d r j (iterD d m ρ (Fin.tail J) P) = _
      ring
    have e2 : ∀ ρ : Fin m → Fin k, ∑ s : Fin (m + 1), (-1) ^ (s : ℕ) *
          ((Matrix.of fun t u => x (ρ t) (I (s.succAbove u))).det *
            pol x d (I s) j (iterD d m ρ (Fin.tail J) P)) =
        ∑ s : Fin (m + 1), ((-1) ^ (s : ℕ) * pol x d (I s) j
          ((Matrix.of fun t u => x (ρ t) (I (s.succAbove u))).det * iterD d m ρ (Fin.tail J) P) +
          m * ((-1) ^ (s : ℕ) * (if I s = j then 1 else 0)) *
          ((Matrix.of fun t u => x (ρ t) (I (s.succAbove u))).det * iterD d m ρ (Fin.tail J) P)) := by
      intro ρ
      have h := congrArg (· * iterD d m ρ (Fin.tail J) P) (sum_pol_det hd ρ I j)
      simp only [Finset.sum_mul, Finset.mul_sum, neg_mul] at h
      simp only [Derivation.leibniz, smul_eq_mul, mul_add, Finset.sum_add_distrib]
      rw [add_assoc, left_eq_add]
      rw [eq_neg_iff_add_eq_zero] at h
      refine Eq.trans ?_ h
      congr 1
      · refine Finset.sum_congr rfl fun s _ => ?_
        ring
      · refine Finset.sum_congr rfl fun s _ => ?_
        ring
    have hcst : ∀ (D : Derivation ℂ R R) (s : Fin (m + 1)),
        D (c * (Matrix.of fun t u => δ t (s.succAbove u)).det * P) =
          c * (Matrix.of fun t u => δ t (s.succAbove u)).det * D P := by
      intro D s
      have : D (Matrix.of fun t u => δ t (s.succAbove u)).det = 0 := by
        rw [deriv_det]
        refine Finset.sum_eq_zero fun t _ => det_eq_zero_of_row_eq_zero t fun u => ?_
        simp only [updateRow_self, of_apply, hδ]
        split_ifs <;> simp
      simp only [Derivation.leibniz, this, hc, Derivation.map_natCast, smul_eq_mul]
      ring
    have hv : ∀ s : Fin (m + 1), pol x d (I s) j P =
        (if I s = j then 1 else 0) * (a j * P) + ∑ t, δ t s * pol x d (Fin.tail J t) j P := by
      intro s
      have hgt : ∀ t, j < Fin.tail J t := by
        intro t
        have := hJ' t
        have := j.2
        rw [Fin.lt_def]; omega
      rcases lt_trichotomy (I s) j with h | h | h
      · rw [hup _ _ h, if_neg h.ne, Finset.sum_eq_zero]
        · simp
        · intro t _
          simp only [hδ]
          rw [if_neg (h.trans (hgt t)).ne, zero_mul]
      · rw [h, hwt, if_pos rfl, Finset.sum_eq_zero]
        · simp
        · intro t _
          simp only [hδ]
          rw [if_neg (h.trans_lt (hgt t)).ne, zero_mul]
      · have h1 := (I s).2
        have h2 : (j : ℕ) < I s := h
        have h3 := j.2
        rw [if_neg h.ne', zero_mul, zero_add,
          Finset.sum_eq_single (⟨(I s : ℕ) - (j + 1), by omega⟩ : Fin m)]
        · have : I s = Fin.tail J ⟨(I s : ℕ) - (j + 1), by omega⟩ := by
            have := hJ' ⟨(I s : ℕ) - (j + 1), by omega⟩
            apply Fin.ext
            simp only at this
            omega
          simp only [hδ]
          rw [if_pos this, one_mul, ← this]
        · intro t _ ht
          simp only [hδ]
          rw [if_neg, zero_mul]
          intro h'
          apply ht
          have := hJ' t
          rw [← h'] at this
          apply Fin.ext
          simp only
          omega
        · simp
    have hz : ∀ t, ∑ s : Fin (m + 1), (-1) ^ (s : ℕ) * δ t s *
        (Matrix.of fun t u => δ t (s.succAbove u)).det = 0 := by
      intro t
      rw [← det_cons, det_cons_self]
    have e3 : (Matrix.of fun t s => if I s = J t then (1 : R) else 0).det =
        ∑ s : Fin (m + 1), (-1) ^ (s : ℕ) * (if I s = j then 1 else 0) *
          (Matrix.of fun t u => δ t (s.succAbove u)).det := by
      rw [det_succ_row_zero]; rfl
    rw [e1]
    simp only [e2]
    rw [Finset.sum_comm]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← map_sum, ih', hcst, hv]
    rw [Fin.prod_univ_succ, Nat.cast_mul, ← hj, h0, e3]
    change _ = _ * c * _ * _
    have hz' : ∑ s : Fin (m + 1), (-1) ^ (s : ℕ) *
        (c * (Matrix.of fun t u => δ t (s.succAbove u)).det *
          ∑ t, δ t s * pol x d (Fin.tail J t) j P) = 0 := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun t _ => ?_
      have := congrArg (· * (c * pol x d (Fin.tail J t) j P)) (hz t)
      simp only [Finset.sum_mul, zero_mul] at this
      rw [← this]
      refine Finset.sum_congr rfl fun s _ => ?_
      ring
    simp only [mul_add, Finset.sum_add_distrib, hz', add_zero]
    rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    push_cast
    ring
end GlobalTheory.MinorNorm
