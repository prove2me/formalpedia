-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Bernstein.arith_nil
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:20:30.812411+00:00
-- url     : https://prove2.me/submissions/58363531-adad-4400-8ff3-99e872568b1e

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_FinrankRangePowConvex
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CommuteOfMemAdjoin
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_FinrankAdjoinLeAdd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_StatementCommutative

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.Fl
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Bernstein
namespace GlobalTheory.CompanionTheory.Bernstein
theorem _root_.solution (N D D' E m K : ℕ) (hN : 0 < N)
    (h1 : D ≤ (2 * N - 1) * D' + E) (h2 : (2 * N - 1 + 1) * E ≤ m ^ 2)
    (h3 : 4 * N ^ 2 * D' ≤ m ^ 2 + K * m) : N * D ≤ m ^ 2 + K * m := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
  have e1 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  have e2 : 2 * (k + 1) - 1 + 1 = 2 * (k + 1) := by omega
  rw [e1] at h1
  rw [e2] at h2
  have h4 : (2 * (k + 1)) * D ≤ (2 * (k + 1)) * ((2 * k + 1) * D') + m ^ 2 := by
    calc (2 * (k + 1)) * D ≤ (2 * (k + 1)) * ((2 * k + 1) * D' + E) :=
          Nat.mul_le_mul_left _ h1
      _ = (2 * (k + 1)) * ((2 * k + 1) * D') + (2 * (k + 1)) * E := by ring
      _ ≤ _ := Nat.add_le_add_left h2 _
  have h5 : (2 * (k + 1)) * ((2 * k + 1) * D') ≤ 4 * (k + 1) ^ 2 * D' := by
    have : (2 * (k + 1)) * ((2 * k + 1) * D') + 2 * (k + 1) * D' = 4 * (k + 1) ^ 2 * D' := by ring
    omega
  have h6 : (2 * (k + 1)) * D ≤ 2 * m ^ 2 + K * m := by omega
  have h7 : 2 * ((k + 1) * D) ≤ 2 * (m ^ 2 + K * m) := by
    have : (2 * (k + 1)) * D = 2 * ((k + 1) * D) := by ring
    have h8 : 2 * (m ^ 2 + K * m) = 2 * m ^ 2 + K * m + K * m := by ring
    omega
  omega
end GlobalTheory.CompanionTheory.Bernstein
