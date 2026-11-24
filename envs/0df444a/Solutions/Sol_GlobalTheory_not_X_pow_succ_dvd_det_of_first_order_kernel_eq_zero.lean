-- Prove2me | solution 1 for GlobalTheory.not_X_pow_succ_dvd_det_of_first_order_kernel_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:28:17.266242+00:00
-- url     : https://prove2.me/submissions/2b95d343-5e9d-4a27-a504-bbd0c7b3ccef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NotXPowSuccDvdDetOfFirstOrderKernelEqZero
import Theorems.Thm_GlobalTheory_exists_det_one_mul_mul_eq_diagonal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (K : Type) [Field K] (a m : ℕ) (Ψ : Matrix (Fin a) (Fin a) (Polynomial K)), (∀ x0 x1 : Fin (0 + 1) → Fin a → K, (∀ j, (Ψ.map fun p => p.coeff 0).mulVec (x0 j) = 0 ∧ (Ψ.map fun p => p.coeff 1).mulVec (x0 j) + (Ψ.map fun p => p.coeff 0).mulVec (x1 j) = 0) → ¬ LinearIndependent K x0) → Module.finrank K (LinearMap.ker (Ψ.map fun p => p.coeff 0).mulVecLin) ≤ m → ¬ (Polynomial.X : Polynomial K) ^ (m + 1) ∣ Ψ.det := by
  classical
  intro K _ a m Ψ hker hm hdvd
  set A := Ψ.map fun p => p.coeff 0 with hA
  set B := Ψ.map fun p => p.coeff 1 with hB
  have hker' : ∀ x0 x1 : Fin a → K, A.mulVec x0 = 0 → B.mulVec x0 + A.mulVec x1 = 0 → x0 = 0 := by
    intro x0 x1 h0 h1
    by_contra hne
    refine hker (fun _ => x0) (fun _ => x1) (fun _ => ⟨h0, h1⟩) ?_
    exact (linearIndependent_unique_iff (v := fun _ : Fin 1 => x0)).2 hne
  obtain ⟨P, Q, D, hP, hQ, hD⟩ := exists_det_one_mul_mul_eq_diagonal A
  have hPu : IsUnit P.det := hP ▸ isUnit_one
  have hQu : IsUnit Q.det := hQ ▸ isUnit_one
  have hPinj : ∀ v : Fin a → K, P.mulVec v = 0 → v = 0 := fun v hv =>
    Matrix.eq_zero_of_mulVec_eq_zero hPu.ne_zero hv
  have hQinj : ∀ v : Fin a → K, Q.mulVec v = 0 → v = 0 := fun v hv =>
    Matrix.eq_zero_of_mulVec_eq_zero hQu.ne_zero hv

  have hcard : (Finset.univ.filter fun i => D i = 0).card ≤ m := by
    have h1 : A.rank = Fintype.card {i // D i ≠ 0} := by
      rw [← Matrix.rank_diagonal, ← hD, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hQu,
        Matrix.rank_mul_eq_right_of_isUnit_det _ _ hPu]
    have h2 := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
    have h3 : Fintype.card {i // D i ≠ 0} = a - Fintype.card {i // D i = 0} := by
      rw [Fintype.card_subtype_compl]; simp
    have h4 : Fintype.card {i // D i = 0} = (Finset.univ.filter fun i => D i = 0).card :=
      Fintype.card_subtype _
    have h5 : Fintype.card {i // D i = 0} ≤ a := by
      simpa using Fintype.card_subtype_le (fun i => D i = 0)
    rw [Matrix.rank] at h1
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h2
    omega
  have hAQ : ∀ v : Fin a → K, P.mulVec (A.mulVec (Q.mulVec v)) = fun i => D i * v i := by
    intro v
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hD]
    ext i
    rw [Matrix.mulVec_diagonal]
  have hcol : ∀ i j, D j = 0 → (A * Q) i j = 0 := by
    intro i j hj
    have h1 : A.mulVec (Q.mulVec (Pi.single j 1)) = 0 := by
      apply hPinj
      rw [hAQ]
      ext k
      by_cases hk : k = j
      · subst hk; simp [hj]
      · simp [hk]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at h1
    exact congrFun h1 i
  set Θ : Matrix (Fin a) (Fin a) K[X] := Ψ * Q.map C with hΘ
  have hΘ0 : ∀ i j, (Θ i j).coeff 0 = (A * Q) i j := by
    intro i j
    simp [hΘ, hA, Matrix.mul_apply, Polynomial.finset_sum_coeff]
  have hΘ1 : ∀ i j, (Θ i j).coeff 1 = (B * Q) i j := by
    intro i j
    simp [hΘ, hB, Matrix.mul_apply, Polynomial.finset_sum_coeff]
  set Θ' : Matrix (Fin a) (Fin a) K[X] :=
    Matrix.of fun i j => if D j = 0 then (Θ i j).divX else Θ i j with hΘ'
  have hfac : Θ = Θ' * Matrix.diagonal fun j => if D j = 0 then (X : K[X]) else 1 := by
    ext1 i j
    rw [Matrix.mul_diagonal]
    by_cases hj : D j = 0
    · have := Polynomial.divX_mul_X_add (Θ i j)
      rw [hΘ0, hcol i j hj] at this
      simpa [hΘ', hj] using this.symm
    · simp [hΘ', hj]
  have hdetΘ : Θ.det = Ψ.det := by
    have : (Q.map C).det = (1 : K[X]) := by
      have := RingHom.map_det (C : K →+* K[X]) Q
      rw [hQ, map_one] at this
      exact this.symm
    rw [hΘ, Matrix.det_mul, this, mul_one]
  have hdet : Ψ.det = Θ'.det * X ^ (Finset.univ.filter fun i => D i = 0).card := by
    rw [← hdetΘ]
    conv_lhs => rw [hfac]
    rw [Matrix.det_mul, Matrix.det_diagonal, Finset.prod_ite]
    simp
  set T : Matrix (Fin a) (Fin a) K := Θ'.map fun p => p.coeff 0 with hT
  have hTinj : ∀ y : Fin a → K, T.mulVec y = 0 → y = 0 := by
    intro y hy
    set y0 : Fin a → K := fun j => if D j = 0 then y j else 0 with hy0
    set y1 : Fin a → K := fun j => if D j = 0 then 0 else y j with hy1
    have e0 : A.mulVec (Q.mulVec y0) = 0 := by
      apply hPinj
      rw [hAQ]
      ext k
      by_cases hk : D k = 0 <;> simp [hy0, hk]
    have e1 : B.mulVec (Q.mulVec y0) + A.mulVec (Q.mulVec y1) = 0 := by
      rw [← hy, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      ext i
      simp only [Pi.add_apply, Matrix.mulVec, dotProduct, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : D j = 0
      · simp [hT, hΘ', hy0, hy1, hj, Polynomial.coeff_divX, hΘ1]
      · simp [hT, hΘ', hy0, hy1, hj, hΘ0]
    have z0 : y0 = 0 := hQinj _ (hker' _ _ e0 e1)
    rw [z0, Matrix.mulVec_zero, Matrix.mulVec_zero, zero_add] at e1
    have z1 := hAQ y1
    rw [e1, Matrix.mulVec_zero] at z1
    ext k
    by_cases hk : D k = 0
    · simpa [hy0, hk] using congrFun z0 k
    · simpa [hy1, hk] using (congrFun z1 k).symm
  have hTdet : T.det ≠ 0 := by
    intro h
    obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
    exact hv (hTinj v hv0)
  apply hTdet
  have hc : T.det = Θ'.det.coeff 0 := by
    have := RingHom.map_det (Polynomial.constantCoeff : K[X] →+* K) Θ'
    exact this.symm
  rw [hc, ← Polynomial.X_dvd_iff]
  set ν := (Finset.univ.filter fun i => D i = 0).card
  have h1 : (X : K[X]) * X ^ ν ∣ Θ'.det * X ^ ν := by
    rw [← hdet, ← pow_succ']
    exact (pow_dvd_pow _ (by omega)).trans hdvd
  exact (mul_dvd_mul_iff_right (pow_ne_zero _ Polynomial.X_ne_zero)).1 h1
end GlobalTheory
