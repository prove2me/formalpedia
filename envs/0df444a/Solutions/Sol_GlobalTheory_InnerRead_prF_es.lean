-- Prove2me | solution 1 for GlobalTheory.InnerRead.prF_es
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:45:36.620804+00:00
-- url     : https://prove2.me/submissions/effd4a48-6cb7-4899-a8df-01ae1dd6d1b5

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NonGenericDatumLatticeEqPerpQuotientImageTerm
import Theorems.Thm_GlobalTheory_InnerRead_h_sub_left
import Theorems.Thm_GlobalTheory_InnerRead_h_sum_left
import Theorems.Thm_GlobalTheory_InnerRead_h_e_es
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
theorem _root_.solution (v : V) (b : Fin r) : H.h (Fr.prF v) (Fr.es b) = 0 := by
  unfold FrameD.prF
  rw [h_sub_left, h_sub_left, h_sum_left, h_sum_left]
  simp only [H.h_smul_left, h_e_es, Fr.h_ss, mul_zero, Finset.sum_const_zero, mul_ite, mul_one,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring
end GlobalTheory.InnerRead
