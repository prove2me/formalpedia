-- Prove2me | solution 1 for GlobalTheory.MulSubOneValuation.mul_sub_one_le_of_valuation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:39:26.060418+00:00
-- url     : https://prove2.me/submissions/a587d63e-aed2-4063-894d-c9255879edb0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_MulSubOneLeOfValuation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.MulSubOneValuation
namespace GlobalTheory.MulSubOneValuation
theorem _root_.solution {K Γ : Type*} [CommRing K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) {n : ℕ} {γ : Γ} (hγ : γ ≤ 1) {A B : Matrix (Fin n) (Fin n) K}
    (hA : ∀ r s, v (A r s - (1 : Matrix (Fin n) (Fin n) K) r s) ≤ γ)
    (hB : ∀ r s, v (B r s - (1 : Matrix (Fin n) (Fin n) K) r s) ≤ γ) (r s : Fin n) :
    v ((A * B) r s - (1 : Matrix (Fin n) (Fin n) K) r s) ≤ γ := by

  have hM : A * B - 1 = (A - 1) + (B - 1) + (A - 1) * (B - 1) := by noncomm_ring
  have he : (A * B) r s - (1 : Matrix (Fin n) (Fin n) K) r s =
      (A - 1) r s + (B - 1) r s + ((A - 1) * (B - 1)) r s := by
    simpa [Matrix.sub_apply, Matrix.add_apply] using congrArg (fun M : Matrix (Fin n) (Fin n) K => M r s) hM
  rw [he, Matrix.mul_apply]
  refine v.map_add_le (v.map_add_le (hA r s) (hB r s)) (v.map_sum_le fun k _ => ?_)
  calc v ((A - 1) r k * (B - 1) k s) = v ((A - 1) r k) * v ((B - 1) k s) := map_mul v _ _
    _ ≤ γ * γ := mul_le_mul' (hA r k) (hB k s)
    _ ≤ γ := mul_le_of_le_one_right' hγ
end GlobalTheory.MulSubOneValuation
