-- Prove2me | solution 1 for GlobalTheory.AnArc.hasSum_add_Pw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:46:33.361457+00:00
-- url     : https://prove2.me/submissions/55bcfebf-6e85-4507-a0a1-6a71a84bdf73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_CoeffFSumDerivEqFderiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FormalThetaSumShiftPeriodDiv
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
    (la : A.La) (v : A.V) {s : ℂ} (hs : HasSum (fun μ => A.term j α th μ v * eTwoPi (w * A.exponent j α μ)) s) :
    HasSum (fun μ => A.term j α th μ (v + A.Pw w la) * eTwoPi (w * A.exponent j α μ)) (A.perFactor w la v ^ j * s) := by
  simp only [A.term_add_period h]
  exact ((Equiv.addRight la.y).hasSum_iff.2 hs).mul_left _
end GlobalTheory.AnArc
