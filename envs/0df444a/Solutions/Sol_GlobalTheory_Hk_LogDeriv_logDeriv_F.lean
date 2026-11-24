-- Prove2me | solution 1 for GlobalTheory.Hk.LogDeriv.logDeriv_F
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:29:33.790629+00:00
-- url     : https://prove2.me/submissions/bf9858ce-eca4-43c3-9fb1-d36f6e1bd595

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyContinuationGrowth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TsumOneDivRpowLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassFamilyLogDerivReGtOne
import Theorems.Thm_GlobalTheory_Hk_LogDeriv_hasDerivAt_of_conv
import Theorems.Thm_GlobalTheory_Hk_LogDeriv_summable_of_le
import Theorems.Thm_GlobalTheory_Hk_LogDeriv_norm_ge_of_conv
import Theorems.Thm_GlobalTheory_Hk_LogDeriv_norm_lamChi_le
import Theorems.Thm_GlobalTheory_Hk_LogDeriv_aChi_one
import Theorems.Thm_GlobalTheory_Hk_LogDeriv_conv_chi
import Theorems.Thm_GlobalTheory_Hk_RayCont_continuation_growth


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.LogDeriv
open LSeries
open scoped LSeries.notation
variable (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ)
namespace GlobalTheory.Hk.LogDeriv
theorem _root_.solution : ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (s : ℂ), 1 < s.re → LSeriesSummable (𝓕.lamChi χ) s ∧ ((s.re - 1) / s.re) ^ 2 ≤ ‖LSeries (𝓕.aChi χ) s‖ ∧ 𝓕.F χ s ≠ 0 ∧ -(deriv (𝓕.F χ) s / 𝓕.F χ s) + (if χ = 1 then 1 / (s - 1) else 0) = LSeries (𝓕.lamChi χ) s := by
  intro 𝓕 χ s hs
  obtain ⟨-, hLS, -, -⟩ := GlobalTheory.Hk.RayCont.continuation_growth 𝓕 χ
  have ha : ∀ z : ℂ, 1 < z.re → LSeriesSummable (𝓕.aChi χ) z := fun z hz => (hLS z hz).1
  have hl : ∀ z : ℂ, 1 < z.re → LSeriesSummable (𝓕.lamChi χ) z := fun z hz =>
    summable_of_le (norm_lamChi_le 𝓕 χ) z hz
  have hlb := norm_ge_of_conv ha (norm_lamChi_le 𝓕 χ) (aChi_one 𝓕 χ)
    (fun n _ => conv_chi 𝓕 χ n) hs
  have hσ : 0 < (s.re - 1) / s.re := div_pos (by linarith) (by linarith)
  have hL0 : LSeries (𝓕.aChi χ) s ≠ 0 := by
    intro h
    rw [h, norm_zero] at hlb
    linarith [pow_pos hσ 2]
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hder := hasDerivAt_of_conv ha hl (fun n _ => conv_chi 𝓕 χ n) hs
  have hU : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  refine ⟨hl s hs, hlb, ?_, ?_⟩
  · rw [(hLS s hs).2]
    split_ifs <;> simp [hs1, hL0]
  · by_cases h : χ = 1
    · have hev : 𝓕.F χ =ᶠ[𝓝 s] fun z => (z - 1) * LSeries (𝓕.aChi χ) z :=
        Filter.eventually_of_mem (hU.mem_nhds hs) fun z hz => by
          rw [(hLS z hz).2, if_pos h]
      have hd : HasDerivAt (fun z => (z - 1) * LSeries (𝓕.aChi χ) z)
          (1 * LSeries (𝓕.aChi χ) s +
            (s - 1) * (-(LSeries (𝓕.lamChi χ) s * LSeries (𝓕.aChi χ) s))) s :=
        ((hasDerivAt_id s).sub_const (1 : ℂ)).mul hder
      rw [hev.deriv_eq, hd.deriv, (hLS s hs).2, if_pos h, if_pos h]
      field_simp
      ring
    · have hev : 𝓕.F χ =ᶠ[𝓝 s] LSeries (𝓕.aChi χ) :=
        Filter.eventually_of_mem (hU.mem_nhds hs) fun z hz => by
          rw [(hLS z hz).2, if_neg h, one_mul]
      rw [hev.deriv_eq, hder.deriv, (hLS s hs).2, if_neg h, if_neg h, one_mul]
      field_simp
      ring
end GlobalTheory.Hk.LogDeriv
