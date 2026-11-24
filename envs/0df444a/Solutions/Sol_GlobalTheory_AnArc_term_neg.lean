-- Prove2me | solution 1 for GlobalTheory.AnArc.term_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:57:45.59205+00:00
-- url     : https://prove2.me/submissions/db19b5d7-c4f1-437f-aadd-945c83dcf817

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_CoeffFSumDerivEqFderiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FormalThetaSumShiftPeriodDiv

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
theorem _root_.solution (j : ℕ) (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (μ : A.X) (v : A.V) :
    A.term j α th μ (-v) = A.term j (-α) (fun z => th (-z)) (-μ) v := by
  have h1 : -α + j • -μ = -(α + j • μ) := by rw [smul_neg]; abel
  have h2 : -(v.2 + A.ct (-μ)) = -v.2 + A.ct μ := by rw [map_neg]; abel
  rw [term, term, h1, h2, A.psi_neg]
  simp only [map_neg, AddMonoidHom.neg_apply, neg_neg, Prod.fst_neg, Prod.snd_neg]
end GlobalTheory.AnArc
