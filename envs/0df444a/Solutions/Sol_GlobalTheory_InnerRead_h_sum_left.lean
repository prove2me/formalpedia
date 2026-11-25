-- Prove2me | solution 1 for GlobalTheory.InnerRead.h_sum_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:32:03.070888+00:00
-- url     : https://prove2.me/submissions/b8da4ef7-7354-484e-8d6b-a154cc3e7b12

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NonGenericDatumLatticeEqPerpQuotientImageTerm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG
noncomputable section
open GlobalTheory GlobalTheory.InnerRead
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
namespace GlobalTheory.InnerRead
theorem _root_.solution {ι : Type} (s : Finset ι) (u : ι → V) (y : V) :
    H.h (∑ i ∈ s, u i) y = ∑ i ∈ s, H.h (u i) y := map_sum (hL H y) u s
end GlobalTheory.InnerRead
