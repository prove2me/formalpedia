-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.LatSum.norm_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:30:37.489744+00:00
-- url     : https://prove2.me/submissions/720683cd-4748-475d-8218-176b6f7dad54

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_EisensteinLatticeSumBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LatSum
namespace GlobalTheory.CompanionTheory.SW.LatSum
theorem _root_.solution {t : ℝ} (ht : 0 < t) (z : ℂ) (hz : t ≤ z.im) (s : ℝ) :
    (2 + 1 / t)⁻¹ * (|((⌊z.re + s⌋ : ℤ) : ℝ)| + z.im) ≤ ‖z + (s : ℂ)‖ := by
  have hc : 0 < 2 + 1 / t := by positivity
  rw [inv_mul_le_iff₀ hc]
  obtain ⟨v, hv⟩ : ∃ v, v = z + (s : ℂ) := ⟨_, rfl⟩
  rw [← hv]
  have hre : v.re = z.re + s := by rw [hv]; simp
  have him : v.im = z.im := by rw [hv]; simp
  have h1 : |v.re| ≤ ‖v‖ := Complex.abs_re_le_norm v
  have h2 : |v.im| ≤ ‖v‖ := Complex.abs_im_le_norm v
  have h3 : z.im ≤ ‖v‖ := by rw [← him]; exact (le_abs_self _).trans h2
  rw [← hre]
  have h4 : |((⌊v.re⌋ : ℤ) : ℝ)| ≤ |v.re| + 1 := by
    have a1 := Int.floor_le v.re
    have a2 := Int.lt_floor_add_one v.re
    rw [abs_le]
    constructor
    · have := neg_abs_le v.re
      linarith
    · have := le_abs_self v.re
      linarith
  have h5 : 1 ≤ ‖v‖ * (1 / t) := by
    have : t ≤ ‖v‖ := hz.trans h3
    rw [mul_one_div, le_div_iff₀ ht]
    linarith
  nlinarith
end GlobalTheory.CompanionTheory.SW.LatSum
