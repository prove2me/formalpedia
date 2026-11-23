-- Prove2me | solution 1 for MinVolEllipsoid.eq_7
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:36:22.178588+00:00
-- url     : https://prove2.me/submissions/27e9684f-96f8-4005-b8d1-bf4879977cd0

import Mathlib
import Definitions.Def_MinVolEllipsoid_Zval
import Definitions.Def_MinVolEllipsoid_liftCone
import Definitions.Def_MinVolEllipsoid_GenCompletelyPositive
import Definitions.Def_MinVolEllipsoid_borderedMatrix

set_option autoImplicit false

open Matrix MinVolEllipsoid

namespace MinVolEllipsoid.Eq7Proof

theorem rank1_obj {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hAsymm : A.IsSymm)
    (b q : Fin n → ℝ) :
    trace (A * A * vecMulVec q q) + 2 * (b ⬝ᵥ (A *ᵥ q)) + b ⬝ᵥ b =
      (A *ᵥ q + b) ⬝ᵥ (A *ᵥ q + b) := by
  have hAt : ∀ i j, A i j = A j i := fun i j => by
    have := congr_fun (congr_fun hAsymm.eq i) j
    exact (by simpa [Matrix.transpose_apply] using this : A j i = A i j).symm
  have htr : trace (A * A * vecMulVec q q) = (A *ᵥ q) ⬝ᵥ (A *ᵥ q) := by
    have h1 : trace (A * A * vecMulVec q q) = q ⬝ᵥ ((A * A) *ᵥ q) := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, vecMulVec_apply, dotProduct, mulVec]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have h2 : q ⬝ᵥ (Aᵀ *ᵥ (A *ᵥ q)) = (A *ᵥ q) ⬝ᵥ (A *ᵥ q) := by
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    rw [hAsymm.eq, Matrix.mulVec_mulVec] at h2
    exact h1.trans h2
  rw [htr]
  simp only [add_dotProduct, dotProduct_add, dotProduct_comm (A *ᵥ q) b]
  ring

theorem cone_decomp {n : ℕ} {P : Set (Fin n → ℝ)} (hPcv : Convex ℝ P) (p₀ : Fin n → ℝ)
    (hp₀ : p₀ ∈ P) {v : Fin n ⊕ Unit → ℝ} (hv : v ∈ liftCone P) :
    ∃ (t : ℝ) (q : Fin n → ℝ), 0 ≤ t ∧ q ∈ P ∧
      v (Sum.inr ()) = t ∧ (fun i => v (Sum.inl i)) = t • q := by
  obtain ⟨k, c, p, hc, hp, rfl⟩ := hv
  set t : ℝ := ∑ s, c s
  have ht0 : 0 ≤ t := Finset.sum_nonneg fun s _ => hc s
  have hinr : (∑ s, c s • lift (p s)) (Sum.inr ()) = t := by
    simp [Finset.sum_apply, lift, t]
  have hinl : (fun i => (∑ s, c s • lift (p s)) (Sum.inl i)) = ∑ s, c s • p s := by
    ext i; simp [Finset.sum_apply, lift]
  by_cases ht : t = 0
  · have hc0 : ∀ s ∈ Finset.univ, c s = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun s _ => hc s).mp ht
    refine ⟨0, p₀, le_rfl, hp₀, by rw [hinr, ht], ?_⟩
    rw [hinl, zero_smul]
    exact Finset.sum_eq_zero fun s hs => by rw [hc0 s hs, zero_smul]
  · have ht_pos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
    let q : Fin n → ℝ := ∑ s, (t⁻¹ * c s) • p s
    have hqP : q ∈ P := by
      apply hPcv.sum_mem
      · intro s _
        exact mul_nonneg (inv_nonneg.mpr ht0) (hc s)
      · rw [← Finset.mul_sum]
        exact inv_mul_cancel₀ ht
      · intro s _
        exact hp s
    have htq : t • q = ∑ s, c s • p s := by
      simp only [q, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro s _
      rw [smul_smul, mul_inv_cancel_left₀ ht]
    exact ⟨t, q, ht0, hqP, hinr, by rw [hinl, htq]⟩

end MinVolEllipsoid.Eq7Proof

open MinVolEllipsoid.Eq7Proof in
theorem solution {n : ℕ} (P : Set (Fin n → ℝ)) (hPc : IsCompact P) (hPcv : Convex ℝ P)
    (hPi : (interior P).Nonempty) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (b : Fin n → ℝ) :
    IsLUB {z : ℝ | ∃ (x : Fin n → ℝ) (X : Matrix (Fin n) (Fin n) ℝ), X.IsSymm ∧
        GenCompletelyPositive (liftCone P) (borderedMatrix X x x 1) ∧
        z = trace (A * A * X) + 2 * (b ⬝ᵥ (A *ᵥ x)) + b ⬝ᵥ b}
      (Zval P A b) := by
  have hAsymm : A.IsSymm := by
    simpa [Matrix.IsHermitian, Matrix.IsSymm] using hA.1
  have hcont : Continuous (fun x : Fin n → ℝ => (A *ᵥ x + b) ⬝ᵥ (A *ᵥ x + b)) := by
    have h1 : Continuous (fun x : Fin n → ℝ => A *ᵥ x + b) :=
      (continuous_const.matrix_mulVec continuous_id).add continuous_const
    show Continuous (fun x => ∑ i, (A *ᵥ x + b) i * (A *ᵥ x + b) i)
    exact continuous_finsetSum _ (fun i _ =>
      ((continuous_apply i).comp h1).mul ((continuous_apply i).comp h1))
  have hbdd : BddAbove ((fun x => (A *ᵥ x + b) ⬝ᵥ (A *ᵥ x + b)) '' P) :=
    (hPc.image hcont).bddAbove
  obtain ⟨p₀, hp₀⟩ : P.Nonempty := hPi.mono interior_subset
  constructor
  · -- Upper bound: every feasible (x, X) has objective ≤ Zval P A b
    rintro _ ⟨x, X, -, ⟨m, v, hv, hBM⟩, rfl⟩
    have hex : ∀ r : Fin m, ∃ (t : ℝ) (q : Fin n → ℝ), 0 ≤ t ∧ q ∈ P ∧
        v r (Sum.inr ()) = t ∧ (fun i => v r (Sum.inl i)) = t • q :=
      fun r => cone_decomp hPcv p₀ hp₀ (hv r)
    choose t q ht0 hqP hvinr hvinl using hex
    have h1 : (1 : ℝ) = ∑ r : Fin m, (t r) ^ 2 := by
      have := congr_fun (congr_fun hBM (Sum.inr ())) (Sum.inr ())
      simp only [borderedMatrix, fromBlocks_apply₂₂, of_apply, Matrix.sum_apply,
        vecMulVec_apply, hvinr] at this
      simpa only [sq] using this
    have hx_eq : x = ∑ r : Fin m, (t r) ^ 2 • q r := by
      ext i
      have := congr_fun (congr_fun hBM (Sum.inl i)) (Sum.inr ())
      simp only [borderedMatrix, fromBlocks_apply₁₂, replicateCol, of_apply, Matrix.sum_apply,
        vecMulVec_apply, hvinr, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
      rw [this]
      apply Finset.sum_congr rfl
      intro r _
      have hi := congr_fun (hvinl r) i
      simp only [Pi.smul_apply, smul_eq_mul] at hi
      rw [hi]
      ring
    have hX_eq : X = ∑ r : Fin m, (t r) ^ 2 • vecMulVec (q r) (q r) := by
      ext i j
      have := congr_fun (congr_fun hBM (Sum.inl i)) (Sum.inl j)
      simp only [borderedMatrix, fromBlocks_apply₁₁, Matrix.sum_apply, Matrix.smul_apply,
        vecMulVec_apply, smul_eq_mul] at this ⊢
      rw [this]
      apply Finset.sum_congr rfl
      intro r _
      have hi := congr_fun (hvinl r) i
      have hj := congr_fun (hvinl r) j
      simp only [Pi.smul_apply, smul_eq_mul] at hi hj
      rw [hi, hj]
      ring
    have hobj : trace (A * A * X) + 2 * (b ⬝ᵥ (A *ᵥ x)) + b ⬝ᵥ b =
        ∑ r : Fin m, (t r) ^ 2 * ((A *ᵥ q r + b) ⬝ᵥ (A *ᵥ q r + b)) := by
      rw [hX_eq, hx_eq, Matrix.mul_sum, Matrix.trace_sum]
      rw [Matrix.mulVec_sum, dotProduct_sum, Finset.mul_sum]
      have hb1 : b ⬝ᵥ b = ∑ r : Fin m, (t r) ^ 2 * (b ⬝ᵥ b) := by
        rw [← Finset.sum_mul, ← h1, one_mul]
      rw [hb1, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro r _
      rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
      rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
      rw [← rank1_obj A hAsymm b (q r)]
      ring
    rw [hobj]
    calc ∑ r : Fin m, (t r) ^ 2 * ((A *ᵥ q r + b) ⬝ᵥ (A *ᵥ q r + b))
        ≤ ∑ r : Fin m, (t r) ^ 2 * Zval P A b := by
          apply Finset.sum_le_sum
          intro r _
          exact mul_le_mul_of_nonneg_left (le_csSup hbdd ⟨q r, hqP r, rfl⟩) (sq_nonneg _)
      _ = (∑ r : Fin m, (t r) ^ 2) * Zval P A b := (Finset.sum_mul _ _ _).symm
      _ = Zval P A b := by rw [← h1, one_mul]
  · -- Least upper bound: Zval P A b ≤ B for every upper bound B
    intro B hB
    unfold Zval
    have hne_img : ((fun x => (A *ᵥ x + b) ⬝ᵥ (A *ᵥ x + b)) '' P).Nonempty :=
      ⟨_, p₀, hp₀, rfl⟩
    apply csSup_le hne_img
    rintro _ ⟨p, hp, rfl⟩
    apply hB
    refine ⟨p, vecMulVec p p, ?_, ?_, (rank1_obj A hAsymm b p).symm⟩
    · ext i j; simp [vecMulVec_apply, mul_comm]
    · refine ⟨1, fun _ => lift p, ?_, ?_⟩
      · intro _
        exact ⟨1, fun _ => 1, fun _ => p, fun _ => zero_le_one, fun _ => hp, by simp⟩
      · ext i j
        rcases i with i | ⟨⟩ <;> rcases j with j | ⟨⟩ <;>
          simp [borderedMatrix, lift, vecMulVec_apply]
