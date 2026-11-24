-- Prove2me | solution 1 for GlobalTheory.SimAlg.real_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:48:11.635208+00:00
-- url     : https://prove2.me/submissions/563d5c42-a46b-458e-95a2-9516cc770ccf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SimilitudeDefiniteFormIsAlgebraicOnVector
import Theorems.Thm_GlobalTheory_SimAlg_det_ne_zero
import Theorems.Thm_GlobalTheory_SimAlg_real_nonneg

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
theorem _root_.solution {d : ℕ} (G : Matrix (Fin d) (Fin d) ℤ) (hs : ∀ i j, G i j = G j i)
    (hG : ∀ c : Fin d → ℤ, c ≠ 0 → 0 < c ⬝ᵥ G *ᵥ c) (x : Fin d → ℝ)
    (hx : ∑ i, ∑ j, x i * x j * (G i j : ℝ) = 0) : x = 0 := by
  set M : Matrix (Fin d) (Fin d) ℝ := G.map (Int.castRingHom ℝ) with hM
  have key : ∀ y : Fin d → ℝ, star y ⬝ᵥ M *ᵥ y = ∑ i, ∑ j, y i * y j * (G i j : ℝ) := by
    intro y
    simp only [dotProduct, mulVec, Finset.mul_sum, hM]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp; ring
  have hp : M.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun y => ?_
    · ext i j; simp [hM, hs i j]
    · rw [key]; exact real_nonneg G hG y
  have h0 : M *ᵥ x = 0 := (hp.dotProduct_mulVec_zero_iff x).1 (by rw [key, hx])
  by_contra hne
  have : M.det = 0 := Matrix.exists_mulVec_eq_zero_iff.1 ⟨x, hne, h0⟩
  rw [hM, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at this
  exact det_ne_zero G hG (by simpa using this)
end GlobalTheory.SimAlg
