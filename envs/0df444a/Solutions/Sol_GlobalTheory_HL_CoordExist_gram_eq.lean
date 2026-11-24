-- Prove2me | solution 1 for GlobalTheory.HL.CoordExist.gram_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:06:32.37114+00:00
-- url     : https://prove2.me/submissions/d0c321fb-f508-45bc-856e-bcd408391c2b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NotField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.CoordExist
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]
namespace GlobalTheory.HL.CoordExist
theorem _root_.solution {H : HermSp M V} {r : ℕ} (A : LocNG.FrameD H r) (a b : Fin (r + 1)) :
    H.h (A.f a) (A.f b) = if a = Fin.last r ∧ b = Fin.last r then -algebraMap F E A.T else 0 := by
  split_ifs with hab
  · rw [hab.1, hab.2]
    exact A.h_zz
  · exact A.h_iso a b (not_and_or.mp hab)
end GlobalTheory.HL.CoordExist
