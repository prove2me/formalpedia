-- Prove2me | solution 1 for GlobalTheory.InnerRead.good_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:45:29.239223+00:00
-- url     : https://prove2.me/submissions/50551788-45db-496c-a8c5-cdbf662968ae

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NonGenericDatumLatticeEqPerpQuotientImageTerm
import Theorems.Thm_GlobalTheory_InnerRead_good_perp

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
theorem _root_.solution {X : Submodule E V} {u w : V ≃ₗ[E] V} (hX : X ≤ H.perp X) (hu : Good H X u)
    (hw : Good H X w) : Good H X (u * w) := by
  refine ⟨fun x y => ?_, fun v hv => ?_⟩
  · change H.h (u (w x)) (u (w y)) = _
    rw [hu.1, hw.1]
  · change u (w v) - v ∈ X
    have e : u (w v) - v = (u (w v) - w v) + (w v - v) := by abel
    rw [e]
    exact X.add_mem (hu.2 _ (good_perp H hX hw v hv)) (hw.2 v hv)
end GlobalTheory.InnerRead
