-- Prove2me | solution 1 for GlobalTheory.Nef.hankel_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:21:35.982378+00:00
-- url     : https://prove2.me/submissions/90c68a61-083b-46a6-9aa5-15c9fec004c7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HankelDeterminantIntegralOfQuotient
import Theorems.Thm_GlobalTheory_Nef_hankelInt_sumLemma
import Theorems.Thm_GroundTheory_FunctionField_Place_ordHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.FunctionField.Place.ordHom_apply



set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
open GlobalTheory GlobalTheory.Nef
open PowerSeries Finset
namespace GlobalTheory.Nef
theorem _root_.solution : ∀ (O F : Type) [CommRing O] [Field F] (ι : O →+* F) (e ψ : PowerSeries O) (φ : PowerSeries F) (n : ℕ), PowerSeries.map ι e * φ = PowerSeries.map ι ψ → ∃ z : O, ι z = ι (PowerSeries.constantCoeff e) ^ (2 * (n + 1)) * hankel (fun i => PowerSeries.coeff i φ) n := by
  intro O F _ _ ι e ψ φ n h
  set E := PowerSeries.map ι e with hE
  set P : ℕ → PowerSeries F := fun i => (trunc (i + 1) E : PowerSeries F) with hP
  let N : Matrix (Fin (n + 1)) (Fin (n + 1)) O := Matrix.of fun i j =>
    coeff ((i : ℕ) + j) ((trunc ((i : ℕ) + 1) e : PowerSeries O) * ψ - (e - (trunc ((j : ℕ) + 1) e : PowerSeries O)) * ψ)
  let T : Matrix (Fin (n + 1)) (Fin (n + 1)) F := Matrix.of fun i l =>
    if (l : ℕ) ≤ i then coeff ((i : ℕ) - l) E else 0
  let H : Matrix (Fin (n + 1)) (Fin (n + 1)) F := Matrix.of fun i j => coeff ((i : ℕ) + j) φ
  have hmapP : ∀ k, PowerSeries.map ι (trunc k e : PowerSeries O) = (trunc k E : PowerSeries F) := by
    intro k; ext m; simp only [hE, coeff_map, Polynomial.coeff_coe, coeff_trunc]; split_ifs <;> simp
  have hX : ∀ i : ℕ, X ^ (i + 1) ∣ E - P i := by
    intro i; rw [X_pow_dvd_iff]; intro m hm
    simp [hP, Polynomial.coeff_coe, coeff_trunc, hm]
  have hdiv : ∀ i j : ℕ, coeff (i + j) ((E - P i) * (E - P j) * φ) = 0 := by
    intro i j
    have h3 : X ^ (i + 1 + (j + 1)) ∣ (E - P i) * (E - P j) * φ := by
      rw [pow_add]; exact Dvd.dvd.mul_right (mul_dvd_mul (hX i) (hX j)) φ
    exact X_pow_dvd_iff.mp h3 _ (by omega)
  have hent : N.map ι = T * H * T.transpose := by
    ext i j
    have inner : ∀ l : Fin (n + 1), ∑ m, H l m * T.transpose m j = coeff ((l : ℕ) + j) (P j * φ) := by
      intro l
      rw [Nat.add_comm (l : ℕ) (j : ℕ)]
      refine Eq.trans ?_ (hankelInt_sumLemma E φ n j l)
      refine sum_congr rfl fun m _ => ?_
      simp only [H, T, Matrix.of_apply, Matrix.transpose_apply]; rw [mul_comm, add_comm (l : ℕ)]
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    simp only [Matrix.mul_apply, inner]
    rw [show (∑ x, T i x * coeff ((x : ℕ) + j) (P j * φ)) = coeff ((i : ℕ) + j) (P i * (P j * φ)) from hankelInt_sumLemma E (P j * φ) n i j]
    simp only [Matrix.map_apply, N, Matrix.of_apply]
    have key : PowerSeries.map ι ((trunc ((i : ℕ) + 1) e : PowerSeries O) * ψ - (e - (trunc ((j : ℕ) + 1) e : PowerSeries O)) * ψ)
        = P i * (P j * φ) - (E - P i) * (E - P j) * φ := by
      rw [map_sub, map_mul, map_mul, map_sub, hmapP, hmapP, ← h, ← hE]
      simp only [hP]; ring
    rw [← coeff_map, key, map_sub, hdiv, sub_zero]
  have hT : T.det = ι (constantCoeff e) ^ (n + 1) := by
    rw [Matrix.det_of_lowerTriangular T ?_]
    · simp [T, E, Finset.prod_const]
    · intro i j hij
      have hij' : i < j := hij
      have h1 : ¬ j ≤ i := not_le.mpr hij'
      have h2 : ¬ ((j : ℕ) ≤ i) := h1
      simp [T, h1, h2]
  refine ⟨N.det, ?_⟩
  rw [RingHom.map_det, RingHom.mapMatrix_apply, hent, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hT]
  show _ = _ * H.det
  ring
end GlobalTheory.Nef
