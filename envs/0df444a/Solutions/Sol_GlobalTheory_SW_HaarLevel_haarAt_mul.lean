-- Prove2me | solution 1 for GlobalTheory.SW.HaarLevel.haarAt_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:57:11.434854+00:00
-- url     : https://prove2.me/submissions/99f1c2df-e5a8-4a0a-8e17-660a56539dcd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe
import Theorems.Thm_GlobalTheory_SW_HaarLevel_finsum_quotient_of_le
import Theorems.Thm_GlobalTheory_SW_HaarLevel_relIndex_perSub
import Theorems.Thm_GlobalTheory_SW_HaarLevel_perSub_le
import Theorems.Thm_GlobalTheory_SW_HaarLevel_periodic
import Theorems.Thm_GlobalTheory_SW_HaarLevel_finite_support

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HaarLevel
noncomputable section
open NumberField
variable {K : Type} [Field K] [NumberField K] {κ ι : Type} [Fintype κ] [Fintype ι]
namespace GlobalTheory.SW.HaarLevel
theorem _root_.solution {R : ℕ} {φ : Matrix κ ι K → ℂ} (hR : 0 < R) (h : HasLevel R φ) {S : ℕ}
    (hS : 0 < S) : haarAt (R * S) φ = haarAt R φ := by
  have hS' : (S : ℂ) ≠ 0 := by exact_mod_cast hS.ne'
  have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  rw [haarAt, haarAt, finsum_quotient_of_le (perSub_le R S)
    (by rw [relIndex_perSub R S hR]; positivity) φ (periodic h) (finite_support hR h),
    relIndex_perSub R S hR]
  push_cast
  rw [mul_pow]
  field_simp
end GlobalTheory.SW.HaarLevel
