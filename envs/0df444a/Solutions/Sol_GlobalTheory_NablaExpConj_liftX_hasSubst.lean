-- Prove2me | solution 1 for GlobalTheory.NablaExpConj.liftX_hasSubst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:39:06.89845+00:00
-- url     : https://prove2.me/submissions/7079c8c9-e281-442b-b432-0d4f8e0413c6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpSNegMulExpS

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.NablaExpConj
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable (k : Type) [CommRing k]
namespace GlobalTheory.NablaExpConj
theorem _root_.solution : HasSubst (fun p : Fin 1 × Fin d => (X (Sum.inl p.2) : AA k d)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
end GlobalTheory.NablaExpConj
