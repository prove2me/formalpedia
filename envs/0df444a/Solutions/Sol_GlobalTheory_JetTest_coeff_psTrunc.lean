-- Prove2me | solution 1 for GlobalTheory.JetTest.coeff_psTrunc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:41:37.435934+00:00
-- url     : https://prove2.me/submissions/4b09dcf0-3012-43ed-9d13-70291afa0a4e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SubConstMemOrig
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_JetTruncNotInjective
import Theorems.Thm_GlobalTheory_JetTest_mem_degLE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.JetTest
open MvPolynomial Formalism.L2.Pj
variable {R : Type} [CommRing R] {ι : Type} {m : ℕ}
namespace GlobalTheory.JetTest
theorem _root_.solution [Fintype ι] [DecidableEq ι] (f : MvPowerSeries ι R) (e : ι →₀ ℕ) :
    (psTrunc m f).coeff e = if e.degree ≤ m then MvPowerSeries.coeff e f else 0 := by
  unfold psTrunc
  rw [MvPolynomial.coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  simp [mem_degLE]
end GlobalTheory.JetTest
