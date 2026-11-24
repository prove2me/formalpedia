-- Prove2me | solution 1 for GlobalTheory.SimAlg.exists_ann
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:48:08.180064+00:00
-- url     : https://prove2.me/submissions/69b414e9-d54e-4209-b141-05523f97e987

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SimilitudeDefiniteFormIsAlgebraicOnVector
import Theorems.Thm_GlobalTheory_SimAlg_det_ne_zero
import Theorems.Thm_GlobalTheory_SimAlg_gram_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix
open GlobalTheory GlobalTheory.SimAlg
namespace GlobalTheory.SimAlg
theorem _root_.solution {Λ : Type} [AddCommGroup Λ] (b : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ)
    (hb : ∀ x, x ≠ 0 → 0 < b x x) (φ : Module.End ℤ Λ) (e : Λ) (l r : ℕ) (hl : 2 ≤ l)
    (h : ∀ n : ℕ, ∃ (χ : ℤ[X]) (y : Λ), χ.Monic ∧ χ.natDegree = r ∧ aeval φ χ e = l ^ n • y) :
    ∃ P : ℤ[X], P ≠ 0 ∧ aeval φ P e = 0 := by
  by_contra hne
  push Not at hne
  set G : Matrix (Fin (r + 1)) (Fin (r + 1)) ℤ :=
    Matrix.of fun i j => b ((φ ^ (i : ℕ)) e) ((φ ^ (j : ℕ)) e) with hG
  have hD : G.det ≠ 0 := det_ne_zero G (gram_pos b hb φ e (r + 1) fun P hP _ => hne P hP)
  obtain ⟨χ, y, hm, hr, hy⟩ := h G.det.natAbs
  set n := G.det.natAbs with hn
  have h1 : aeval φ χ e = ∑ i : Fin (r + 1), χ.coeff i • (φ ^ (i : ℕ)) e := by
    rw [aeval_eq_sum_range, hr, Finset.sum_range]
    simp [LinearMap.sum_apply]
  have h2 : G *ᵥ (fun i => χ.coeff i) = ((l : ℤ) ^ n) • fun i : Fin (r + 1) => b ((φ ^ (i : ℕ)) e) y := by
    ext i
    have : b ((φ ^ (i : ℕ)) e) (aeval φ χ e) = (l : ℤ) ^ n * b ((φ ^ (i : ℕ)) e) y := by
      rw [hy, map_nsmul]; simp
    rw [Pi.smul_apply, smul_eq_mul, ← this, h1]
    simp [mulVec, dotProduct, hG, mul_comm]
  have h3 := congrArg (fun v => (G.adjugate *ᵥ v) (Fin.last r)) h2
  simp only [mulVec_mulVec, adjugate_mul, smul_mulVec, one_mulVec, mulVec_smul, Pi.smul_apply,
    smul_eq_mul, Fin.val_last] at h3
  have hc : χ.coeff r = 1 := by rw [← hr]; exact hm
  rw [hc, mul_one] at h3
  have h4 : l ^ n ∣ n := by
    have : ((l ^ n : ℕ) : ℤ) ∣ G.det := ⟨_, by push_cast; exact h3⟩
    exact Int.natCast_dvd.1 this
  have h5 := Nat.le_of_dvd (Int.natAbs_pos.2 hD) h4
  exact absurd (Nat.lt_pow_self (n := n) (by omega : 1 < l)) (not_lt.2 h5)
end GlobalTheory.SimAlg
