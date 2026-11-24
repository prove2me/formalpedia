-- Prove2me | solution 1 for GlobalTheory.AnArc.summable_add_Pw_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:29:54.603437+00:00
-- url     : https://prove2.me/submissions/bce96cda-13c7-4457-bcec-c09c66d42539

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_CoeffFSumDerivEqFderiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FormalThetaSumShiftPeriodDiv
import Theorems.Thm_GlobalTheory_AnArc_perFactor_ne_zero
import Theorems.Thm_GlobalTheory_AnArc_term_add_period


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
namespace GlobalTheory.AnArc
theorem _root_.solution {j : ℕ} {α : A.X} {th : (Fin A.gB → ℂ) → ℂ} (h : th ∈ A.Theta j α) (w : ℂ)
    (la : A.La) (v : A.V) :
    (Summable fun μ => A.term j α th μ (v + A.Pw w la) * eTwoPi (w * A.exponent j α μ)) ↔
      Summable fun μ => A.term j α th μ v * eTwoPi (w * A.exponent j α μ) := by
  simp only [A.term_add_period h]
  rw [summable_mul_left_iff (pow_ne_zero _ (A.perFactor_ne_zero w la v))]
  exact (Equiv.addRight la.y).summable_iff
    (f := fun μ => A.term j α th μ v * eTwoPi (w * A.exponent j α μ))
end GlobalTheory.AnArc
