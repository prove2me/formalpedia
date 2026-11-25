-- Prove2me | solution 1 for GlobalTheory.IntegralFrameAllCompare.intAll_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:54:10.834865+00:00
-- url     : https://prove2.me/submissions/59c9984f-5744-45c0-a823-0aecfefa27a3

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllFree
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_IntegralFrameAcquisition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_VVNonnegIffLeOne
import Theorems.Thm_GlobalTheory_IntegralFrameAllCompare_conclusion_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open GlobalTheory GlobalTheory.IntegralFrameAllCompare
open NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.IntegralFrameAcquisition
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)
namespace GlobalTheory.IntegralFrameAllCompare
theorem _root_.solution : Formalism.L2.PjFree.IntAll Xo c ↔ AllAcquireIntegralFrame Xo c :=
  forall_congr' fun la => forall_congr' fun T => forall_congr' fun io => forall_congr' fun e =>
    forall_congr' fun ho => forall_congr' fun _ => forall_congr' fun y => conclusion_iff Xo c la T io e ho y
end GlobalTheory.IntegralFrameAllCompare
