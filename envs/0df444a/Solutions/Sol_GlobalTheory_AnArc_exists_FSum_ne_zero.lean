-- Prove2me | solution 1 for GlobalTheory.AnArc.exists_FSum_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:57:43.652813+00:00
-- url     : https://prove2.me/submissions/35aa0488-9075-40a1-9c83-f3ded6f5e1a0

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
theorem _root_.solution (j : ℕ) [NeZero j] (α : A.X) {th : (Fin A.gB → ℂ) → ℂ} (h : th ≠ 0) :
    ∃ v, A.FSum j α th v ≠ 0 :=
  Function.ne_iff.1 ((A.linearIndependent_FSum j (fun _ : Unit => α) (fun _ _ _ _ => rfl) (fun _ => th)
    (fun _ => (linearIndependent_unique_iff.2 h).linearIndepOn _)).ne_zero ())
end GlobalTheory.AnArc
