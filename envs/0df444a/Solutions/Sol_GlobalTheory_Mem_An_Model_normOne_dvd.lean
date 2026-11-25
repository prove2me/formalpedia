-- Prove2me | solution 1 for GlobalTheory.Mem.An.Model.normOne_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:02:25.023788+00:00
-- url     : https://prove2.me/submissions/4c8b4dc8-ba5b-4718-b0a7-938bae83d4f3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RayPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_NormOneSevenOneTwo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset ArithmeticFunction NumberField IsDedekindDomain
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.An GlobalTheory.Mem.An.Model
namespace GlobalTheory.Mem.An.Model
theorem _root_.solution {d M p : ℕ} (hd : d % 4 = 3) (h : NormOne d M p) : (M : ℤ) ∣ (p : ℤ) - 1 := by
  obtain ⟨A, B, hN, ⟨b, rfl⟩, ⟨c, hc⟩⟩ := h
  obtain rfl : A = 2 + M * b + 2 * M * c := by linear_combination hc
  obtain ⟨e, he⟩ : ∃ e : ℤ, (d : ℤ) = 4 * e - 1 := ⟨((d : ℤ) + 1) / 4, by omega⟩
  refine ⟨b + 2 * c + M * (c * (b + c) + e * b ^ 2), ?_⟩
  have h4 : 4 * ((p : ℤ) - 1) = 4 * ((M : ℤ) * (b + 2 * c + M * (c * (b + c) + e * b ^ 2))) := by
    linear_combination (-1 : ℤ) * hN + ((M : ℤ) ^ 2 * b ^ 2) * he
  linarith
end GlobalTheory.Mem.An.Model
