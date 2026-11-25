-- Prove2me | solution 1 for GlobalTheory.JetTest.jetSubstPS_add_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:56:22.597485+00:00
-- url     : https://prove2.me/submissions/3f3c85f7-3ff6-4d02-bb9d-898890694d63

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SubConstMemOrig
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_JetTruncNotInjective
import Theorems.Thm_GlobalTheory_JetTest_coeff_psTrunc

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
theorem _root_.solution {κ : Type} [Fintype κ] [DecidableEq κ] (φ : ι → MvPowerSeries κ R) (c : ι → R) :
    (jetSubstPS (m := m) fun i => φ i + MvPowerSeries.C (c i)) = jetSubstPS (m := m) φ := by
  unfold jetSubstPS
  congr 1
  funext i
  ext e
  simp only [coeff_sub, coeff_psTrunc, constantCoeff_eq, coeff_C, map_add, MvPowerSeries.coeff_C]
  by_cases h : e = 0
  · subst h; simp
  · simp [h, Ne.symm h]
end GlobalTheory.JetTest
