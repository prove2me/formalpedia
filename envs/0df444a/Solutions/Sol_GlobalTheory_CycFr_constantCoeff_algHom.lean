-- Prove2me | solution 1 for GlobalTheory.CycFr.constantCoeff_algHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:15:20.084574+00:00
-- url     : https://prove2.me/submissions/7204bbfa-e74b-4eab-88c3-2be1d1cb08c2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OneAddXMulDerivativeBin
import Theorems.Thm_GlobalTheory_CycFr_algHom_C

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open GlobalTheory GlobalTheory.CycFr
open PowerSeries
namespace GlobalTheory.CycFr
namespace _root_.GlobalTheory.CycFr
theorem _root_.solution {O : Type} [CommRing O] (f : O⟦X⟧ →ₐ[O] O⟦X⟧)
    (hf : (X : O⟦X⟧) ∣ f X) (a : O⟦X⟧) : constantCoeff (f a) = constantCoeff a := by
  obtain ⟨s, hs⟩ : ∃ s, a = s * X + C (constantCoeff a) := ⟨_, eq_shift_mul_X_add_const a⟩
  have h0 : constantCoeff (f X) = 0 := X_dvd_iff.mp hf
  calc constantCoeff (f a) = constantCoeff (f (s * X + C (constantCoeff a))) := by rw [← hs]
    _ = constantCoeff a := by
      rw [map_add, map_mul, _root_.GlobalTheory.CycFr.algHom_C, map_add, map_mul, h0, mul_zero,
        zero_add]
      simp
end _root_.GlobalTheory.CycFr
end GlobalTheory.CycFr
