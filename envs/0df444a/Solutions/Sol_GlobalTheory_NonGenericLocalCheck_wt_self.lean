-- Prove2me | solution 1 for GlobalTheory.NonGenericLocalCheck.wt_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:08:02.993795+00:00
-- url     : https://prove2.me/submissions/25b13975-a145-4535-bc6d-26c618175195

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_TransversalityLocal_FramePairFixatorUnitaryAndFixesFrame

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG
open GlobalTheory GlobalTheory.NonGenericLocalCheck
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E}
variable {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}
namespace GlobalTheory.NonGenericLocalCheck
theorem _root_.solution {P : FPair H r} (d : Datum P) : Datum.wt d d = 1 := by
  unfold Datum.wt volRel
  rw [Subgroup.relIndex_self]
  norm_num
end GlobalTheory.NonGenericLocalCheck
