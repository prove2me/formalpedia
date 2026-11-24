-- Prove2me | solution 1 for GlobalTheory.exists_int_im_latticeForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:10:06.780332+00:00
-- url     : https://prove2.me/submissions/37ff566e-cdd8-4747-b621-8ebb1cdc4ed1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept
import Theorems.Thm_GlobalTheory_im_latticeForm_int
import Theorems.Thm_GlobalTheory_abs_im_latticeForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Complex PeriodPair
open scoped Topology ComplexConjugate Real
open GlobalTheory
variable (L : PeriodPair)
namespace GlobalTheory
theorem _root_.solution {a b : ℂ} (ha : a ∈ L.lattice) (hb : b ∈ L.lattice) :
    ∃ k : ℤ, (latticeForm L a b).im = k := by
  obtain ⟨m, n, rfl⟩ := mem_lattice.1 ha
  obtain ⟨m', n', rfl⟩ := mem_lattice.1 hb
  rw [im_latticeForm_int]
  rcases (abs_eq zero_le_one).1 (abs_im_latticeForm L) with h | h
  · exact ⟨n * m' - m * n', by rw [h, mul_one]⟩
  · exact ⟨-(n * m' - m * n'), by rw [h]; push_cast; ring⟩
end GlobalTheory
