-- Prove2me | solution 1 for GlobalTheory.Reg.TrivBound.chval_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:55:10.541843+00:00
-- url     : https://prove2.me/submissions/bd8c1868-f3f3-4098-af94-d02dd806aff8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegModelC
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_SCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegQFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FnTrdegOf
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RealPtGeo
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllProofFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_CombinedBoundAtTrivialValuationsOfCharts
import Theorems.Thm_GlobalTheory_Reg_TrivBound_nval_eq_vr
import Theorems.Thm_Formalism_L2_Pj_nval_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Reg GlobalTheory.Reg.TrivBound
open IsLocalRing Formalism.L2.Pj GlobalTheory.Reg
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
variable {A : Type} [CommRing A] [IsDomain A]
namespace GlobalTheory.Reg.TrivBound
theorem _root_.solution {φ : A →+* V} {e : ℕ} {r : EReal} (h : ChV φ e (0 : FractionRing A) r) : r = ⊤ := by
  obtain ⟨x, s, hs, hfs, rfl⟩ := h
  have hx : x = 0 := by
    rw [zero_mul] at hfs
    exact IsFractionRing.injective A (FractionRing A) (by rw [← hfs, map_zero])
  rw [hx, map_zero, map_zero, nval_zero, nval_eq_vr e hs, EReal.top_sub_coe]
end GlobalTheory.Reg.TrivBound
