-- Prove2me | solution 1 for KhintchineTwoRegime.corollary_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-21T03:10:08.870259+00:00
-- url     : https://prove2.me/submissions/e3790269-6810-4b39-8c95-196c276022b7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_KhintchineTwoRegime_K
import Definitions.Def_HighDimProb_SparseRecovery_L2Norm
import Theorems.Thm_KhintchineTwoRegime_haagerupF_increasing
import Theorems.Thm_KhintchineTwoRegime_haagerup_inequality
import Theorems.Thm_KhintchineTwoRegime_lemma_2
import Theorems.Thm_KhintchineTwoRegime_lemma_3

open HighDimProb.SparseRecovery (l2Norm)

namespace KhintchineTwoRegime

theorem _root_.solution (n : ℕ) (v : Fin n → ℝ) (hv : l2Norm v = 1)
    (htop : ∀ i j : Fin n, i ≠ j → |v i| + |v j| ≤ 1) :
    (7423 : ℝ) / 10000 ≤ K n v := by
  classical

  have K_perm (u : Fin n → ℝ) (σ : Fin n ≃ Fin n) :
      K n (fun i => u (σ i)) = K n u := by
    let e : (Fin n → Bool) ≃ (Fin n → Bool) :=
      { toFun := fun ε j => ε (σ.symm j)
        invFun := fun ε j => ε (σ j)
        left_inv := by
          intro ε
          funext j
          simp
        right_inv := by
          intro ε
          funext j
          simp }
    unfold K
    congr 1
    calc
      (∑ ε : Fin n → Bool,
          abs (∑ i : Fin n, (if ε i then (1 : ℝ) else -1) * u (σ i)))
          = ∑ ε : Fin n → Bool,
              abs (∑ i : Fin n, (if e ε i then (1 : ℝ) else -1) * u i) := by
            apply Finset.sum_congr rfl
            intro ε hε
            congr 1
            have h := Equiv.sum_comp σ
              (fun j : Fin n => (if e ε j then (1 : ℝ) else -1) * u j)
            simpa [e] using h
      _ = ∑ ε : Fin n → Bool,
              abs (∑ i : Fin n, (if ε i then (1 : ℝ) else -1) * u i) := by
            exact Equiv.sum_comp e
              (fun ε : Fin n → Bool =>
                abs (∑ i : Fin n, (if ε i then (1 : ℝ) else -1) * u i))

  have K_abs (u : Fin n → ℝ) :
      K n u = K n (fun i => abs (u i)) := by
    let e : (Fin n → Bool) ≃ (Fin n → Bool) :=
      { toFun := fun ε i => if u i < 0 then !(ε i) else ε i
        invFun := fun ε i => if u i < 0 then !(ε i) else ε i
        left_inv := by
          intro ε
          funext i
          by_cases hi : u i < 0 <;> simp [hi]
        right_inv := by
          intro ε
          funext i
          by_cases hi : u i < 0 <;> simp [hi] }
    have hterm (ε : Fin n → Bool) (i : Fin n) :
        (if e ε i then (1 : ℝ) else -1) * abs (u i)
          = (if ε i then (1 : ℝ) else -1) * u i := by
      by_cases hi : u i < 0
      · cases hε : ε i <;> simp [e, hi, hε, abs_of_neg hi]
      · have hu : 0 ≤ u i := le_of_not_gt hi
        simp [e, hi, abs_of_nonneg hu]
    unfold K
    congr 1
    calc
      (∑ ε : Fin n → Bool,
          abs (∑ i : Fin n, (if ε i then (1 : ℝ) else -1) * u i))
          = ∑ ε : Fin n → Bool,
              abs (∑ i : Fin n,
                (if e ε i then (1 : ℝ) else -1) * abs (u i)) := by
            apply Finset.sum_congr rfl
            intro ε hε
            congr 1
            symm
            apply Finset.sum_congr rfl
            intro i hi
            exact hterm ε i
      _ = ∑ ε : Fin n → Bool,
              abs (∑ i : Fin n,
                (if ε i then (1 : ℝ) else -1) * abs (u i)) := by
            exact Equiv.sum_comp e
              (fun ε : Fin n → Bool =>
                abs (∑ i : Fin n,
                  (if ε i then (1 : ℝ) else -1) * abs (u i)))

  by_cases hn0 : n = 0
  · subst n
    simp [l2Norm] at hv

  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0

  let uDual : Fin n → OrderDual ℝ := fun i => OrderDual.toDual (abs (v i))
  let σ : Fin n ≃ Fin n := Tuple.sort uDual
  let ω : Fin n → ℝ := fun i => abs (v (σ i))

  have hanti : Antitone ω := by
    intro i j hij
    have h := (Tuple.monotone_sort uDual) hij
    simpa [ω, σ, uDual] using h

  have hnonneg : ∀ i, 0 ≤ ω i := by
    intro i
    exact abs_nonneg _

  have hsumsq : (∑ i, ω i ^ 2) = ∑ i, v i ^ 2 := by
    calc
      (∑ i, ω i ^ 2) = ∑ i, v (σ i) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [ω, sq_abs]
      _ = ∑ i, v i ^ 2 := Equiv.sum_comp σ (fun i : Fin n => v i ^ 2)

  have hnorm : l2Norm ω = 1 := by
    change Real.sqrt (∑ i, ω i ^ 2) = 1
    rw [hsumsq]
    simpa [l2Norm] using hv

  have hproper : IsProper ω := ⟨hanti, hnonneg, hnorm⟩

  have hKω : K n ω = K n v := by
    calc
      K n ω = K n (fun i => abs (v i)) := by
        simpa [ω] using (K_perm (fun i => abs (v i)) σ)
      _ = K n v := (K_abs v).symm

  by_cases hn1 : n = 1
  · subst n
    have hω0nonneg : 0 ≤ ω (0 : Fin 1) := hnonneg 0
    have hω0 : ω (0 : Fin 1) = 1 := by
      have hnorm0 := hnorm
      unfold l2Norm at hnorm0
      simp only [Fin.sum_univ_one] at hnorm0
      rw [Real.sqrt_sq hω0nonneg] at hnorm0
      exact hnorm0
    have hpad : pad ω 0 = 1 := by
      have hp : pad ω 0 = ω (0 : Fin 1) := by
        simp [pad]
      rw [hp, hω0]
    have hle : (1 : ℝ) ≤ K 1 ω := by
      have h := (lemma_2 1 ω hproper).1
      rwa [hpad] at h
    calc
      (7423 : ℝ) / 10000 ≤ 1 := by norm_num
      _ ≤ K 1 ω := hle
      _ = K 1 v := hKω

  have hn2 : 2 ≤ n := by omega
  have hn1lt : 1 < n := by omega

  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩

  have hpad0 : pad ω 0 = ω i0 := by
    simp [pad, hnpos, i0]
  have hpad1 : pad ω 1 = ω i1 := by
    simp [pad, hn1lt, i1]

  have hba : pad ω 1 ≤ pad ω 0 := by
    rw [hpad0, hpad1]
    apply hanti
    simp [i0, i1, Fin.le_def]

  have hb0 : 0 ≤ pad ω 1 := by
    rw [hpad1]
    exact hnonneg _

  have hi01 : i0 ≠ i1 := by
    intro h
    have hval := congrArg Fin.val h
    simp [i0, i1] at hval

  have hσne : σ i0 ≠ σ i1 := by
    intro h
    exact hi01 (σ.injective h)

  have hab : pad ω 0 + pad ω 1 ≤ 1 := by
    rw [hpad0, hpad1]
    change abs (v (σ i0)) + abs (v (σ i1)) ≤ 1
    exact htop _ _ hσne

  have hwi_le (i : Fin n) : ω i ≤ pad ω 0 := by
    rw [hpad0]
    apply hanti
    simp [i0, Fin.le_def]

  have hlemma2 := lemma_2 n ω hproper

  by_cases hlarge : (7423 : ℝ) / 10000 ≤ pad ω 0
  · calc
      (7423 : ℝ) / 10000 ≤ pad ω 0 := hlarge
      _ ≤ K n ω := hlemma2.1
      _ = K n v := hKω

  by_cases hsmall : pad ω 0 ≤ (1 / 2 : ℝ)
  · have hnorm' : Real.sqrt (∑ i, ω i ^ 2) = 1 := by
      simpa [l2Norm] using hnorm
    have hsum_nonneg : 0 ≤ ∑ i, ω i ^ 2 := by
      exact Finset.sum_nonneg (fun i _ => sq_nonneg (ω i))
    have hsquares : (∑ i, ω i ^ 2) = 1 := by
      calc
        (∑ i, ω i ^ 2) = (Real.sqrt (∑ i, ω i ^ 2)) ^ 2 :=
          (Real.sq_sqrt hsum_nonneg).symm
        _ = 1 ^ 2 := by rw [hnorm']
        _ = 1 := by norm_num

    have hFmono : MonotoneOn haagerupF (Set.Ioi 0) := by
      intro x hx y hy hxy
      rcases eq_or_lt_of_le hxy with rfl | hxy'
      · exact le_rfl
      · exact (haagerupF_increasing.1 hx hy hxy').le

    have hFbound : ∀ i, ω i ≠ 0 →
        (3 / 4 : ℝ) ≤ haagerupF ((ω i ^ 2)⁻¹) := by
      intro i hi
      have hsq_pos : 0 < ω i ^ 2 := by positivity
      have hi_half : ω i ≤ (1 / 2 : ℝ) := (hwi_le i).trans hsmall
      have hi_nonneg : 0 ≤ ω i := hnonneg i
      have hfactor :
          0 ≤ ((1 / 2 : ℝ) - ω i) * ((1 / 2 : ℝ) + ω i) :=
        mul_nonneg (sub_nonneg.mpr hi_half) (by linarith)
      have hsq_bound : 4 * (ω i ^ 2) ≤ 1 := by
        nlinarith
      have h4s : (4 : ℝ) ≤ (ω i ^ 2)⁻¹ := by
        by_contra hn
        have hmul := mul_lt_mul_of_pos_right (not_le.mp hn) hsq_pos
        rw [inv_mul_cancel₀ (ne_of_gt hsq_pos)] at hmul
        linarith
      have hmono := hFmono
        (show (4 : ℝ) ∈ Set.Ioi 0 by norm_num)
        (show (ω i ^ 2)⁻¹ ∈ Set.Ioi 0 by exact inv_pos.mpr hsq_pos)
        h4s
      rw [haagerupF_increasing.2] at hmono
      exact hmono

    have hterm (i : Fin n) :
        (3 / 4 : ℝ) * ω i ^ 2 ≤
          (if ω i = 0 then 0
            else ω i ^ 2 * haagerupF ((ω i ^ 2)⁻¹)) := by
      by_cases hi : ω i = 0
      · simp [hi]
      · rw [if_neg hi]
        calc
          (3 / 4 : ℝ) * ω i ^ 2 = ω i ^ 2 * (3 / 4 : ℝ) := by ring
          _ ≤ ω i ^ 2 * haagerupF ((ω i ^ 2)⁻¹) :=
            mul_le_mul_of_nonneg_left (hFbound i hi) (sq_nonneg (ω i))

    have hsum :
        (∑ i, (3 / 4 : ℝ) * ω i ^ 2) ≤
          ∑ i, (if ω i = 0 then 0
            else ω i ^ 2 * haagerupF ((ω i ^ 2)⁻¹)) := by
      exact Finset.sum_le_sum (fun i _ => hterm i)

    have heq : (∑ i, (3 / 4 : ℝ) * ω i ^ 2) = 3 / 4 := by
      rw [← Finset.mul_sum, hsquares]
      norm_num

    calc
      (7423 : ℝ) / 10000 ≤ 3 / 4 := by norm_num
      _ = ∑ i, (3 / 4 : ℝ) * ω i ^ 2 := heq.symm
      _ ≤ ∑ i, (if ω i = 0 then 0
            else ω i ^ 2 * haagerupF ((ω i ^ 2)⁻¹)) := hsum
      _ ≤ K n ω := haagerup_inequality n ω hnorm
      _ = K n v := hKω

  · have ha1 : (1 / 2 : ℝ) ≤ pad ω 0 := (not_le.mp hsmall).le
    have ha2 : pad ω 0 ≤ (7423 : ℝ) / 10000 := (not_le.mp hlarge).le
    have hthree := lemma_3 (pad ω 0) (pad ω 1) ha1 ha2 hb0 hba hab
    have hmax :
        max (J (pad ω 0) (pad ω 1)) (H (pad ω 0) (pad ω 1)) ≤ K n ω :=
      max_le hlemma2.2.1 hlemma2.2.2
    have hfinal : (7423 : ℝ) / 10000 < K n v :=
      hthree.trans_le (hmax.trans_eq hKω)
    exact hfinal.le

end KhintchineTwoRegime
