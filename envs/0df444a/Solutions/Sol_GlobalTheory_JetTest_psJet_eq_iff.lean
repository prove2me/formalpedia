-- Prove2me | solution 1 for GlobalTheory.JetTest.psJet_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:54:48.379998+00:00
-- url     : https://prove2.me/submissions/ee4a318d-e455-45b4-8af2-20d21c41957b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SubConstMemOrig
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_JetTruncNotInjective
import Theorems.Thm_GlobalTheory_JetTest_mk_eq_zero_iff
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
theorem _root_.solution [Fintype ι] [DecidableEq ι] (f g : MvPowerSeries ι R) :
    psJet m f = psJet m g ↔
      ∀ e : ι →₀ ℕ, e.degree ≤ m → MvPowerSeries.coeff e f = MvPowerSeries.coeff e g := by
  rw [← sub_eq_zero, psJet, psJet, ← map_sub, mk_eq_zero_iff]
  refine forall_congr' fun e => forall_congr' fun he => ?_
  rw [coeff_sub, coeff_psTrunc, coeff_psTrunc, if_pos he, if_pos he, sub_eq_zero]
end GlobalTheory.JetTest
