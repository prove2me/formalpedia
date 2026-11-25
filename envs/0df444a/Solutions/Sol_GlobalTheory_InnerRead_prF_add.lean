-- Prove2me | solution 1 for GlobalTheory.InnerRead.prF_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:41:07.861959+00:00
-- url     : https://prove2.me/submissions/7c1737e5-6e61-445c-8cbc-cf64c0af5e03

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NonGenericDatumLatticeEqPerpQuotientImageTerm
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG
noncomputable section
open GlobalTheory GlobalTheory.InnerRead
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
variable {H} {r : ℕ} (Fr : FrameD H r)
namespace GlobalTheory.InnerRead
theorem _root_.solution (x y : V) : Fr.prF (x + y) = Fr.prF x + Fr.prF y := by
  unfold FrameD.prF
  simp only [H.h_add_left, add_smul, Finset.sum_add_distrib]
  abel
end GlobalTheory.InnerRead
