-- Prove2me | solution 1 for GlobalTheory.AnArc.be_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:57:43.447073+00:00
-- url     : https://prove2.me/submissions/ca74cdc9-a060-4180-9393-a76729b72247

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SummableExpNegSumAbs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HasSumLocallyUniformlyOnTerm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
namespace GlobalTheory.AnArc
theorem _root_.solution (x y : A.X) : A.be x y ^ 2 ≤ A.be x x * A.be y y :=
  A.be.apply_sq_le_of_symm A.be_self_nonneg ⟨A.be_symm⟩ x y
end GlobalTheory.AnArc
