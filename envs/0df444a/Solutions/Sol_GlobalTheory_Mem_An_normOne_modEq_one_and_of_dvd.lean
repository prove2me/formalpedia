-- Prove2me | solution 1 for GlobalTheory.Mem.An.normOne_modEq_one_and_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:08:45.214854+00:00
-- url     : https://prove2.me/submissions/7de87280-b3ea-4934-a5d1-2bd9c187fc9b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RayPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NormOneModEqOneAndOfDvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.An
namespace GlobalTheory.Mem.An
namespace _root_.GlobalTheory.Mem.An
theorem _root_.solution :
    ∀ d M p : ℕ, d % 4 = 3 → _root_.GlobalTheory.Mem.An.NormOne d M p →
      p ≡ 1 [MOD M] ∧ ∀ M' : ℕ, M' ∣ M → _root_.GlobalTheory.Mem.An.NormOne d M' p := by
  intro d M p hd h
  obtain ⟨A, B, hAB, hB, hA⟩ := h
  refine ⟨?_, fun M' hM' => ⟨A, B, hAB, (Int.natCast_dvd_natCast.mpr hM').trans hB,
    (mul_dvd_mul_left 2 (Int.natCast_dvd_natCast.mpr hM')).trans hA⟩⟩
  obtain ⟨b, rfl⟩ := hB
  obtain ⟨k, hk⟩ := hA
  have hdq : (d : ℤ) = 4 * (d / 4 : ℕ) + 3 := by omega
  have hA' : A = 2 + M * b + 2 * M * k := by linear_combination hk
  have key : (4 : ℤ) * (p - 1) =
      4 * (M * (b + 2 * k + M * (((d / 4 : ℕ) + 1) * b ^ 2 + b * k + k ^ 2))) := by
    rw [hA', hdq] at hAB
    linear_combination -hAB
  have key' : (p : ℤ) - 1 = M * (b + 2 * k + M * (((d / 4 : ℕ) + 1) * b ^ 2 + b * k + k ^ 2)) := by
    linarith
  exact (Nat.modEq_iff_dvd.mpr ⟨_, key'⟩).symm
end _root_.GlobalTheory.Mem.An
end GlobalTheory.Mem.An
