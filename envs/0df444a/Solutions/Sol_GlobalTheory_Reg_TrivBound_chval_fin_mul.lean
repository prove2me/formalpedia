-- Prove2me | solution 1 for GlobalTheory.Reg.TrivBound.chval_fin_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:15:38.470204+00:00
-- url     : https://prove2.me/submissions/a7298ace-286f-404a-abc5-12ec8afc03a2

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
import Theorems.Thm_GlobalTheory_Reg_TrivBound_vr_mul
import Theorems.Thm_GlobalTheory_Reg_TrivBound_chval_fin_iff

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
theorem _root_.solution (φ : A →+* V) (e : ℕ) {f1 f2 : FractionRing A} {u1 u2 : ℝ}
    (h1 : ChV φ e f1 (u1 : EReal)) (h2 : ChV φ e f2 (u2 : EReal)) :
    ChV φ e (f1 * f2) ((u1 + u2 : ℝ) : EReal) := by
  obtain ⟨x1, s1, hs1, hx1, hf1, hu1⟩ := (chval_fin_iff φ e f1 u1).1 h1
  obtain ⟨x2, s2, hs2, hx2, hf2, hu2⟩ := (chval_fin_iff φ e f2 u2).1 h2
  refine (chval_fin_iff φ e _ _).2 ⟨x1 * x2, s1 * s2, ?_, ?_, ?_, ?_⟩
  · rw [map_mul]; exact mul_ne_zero hs1 hs2
  · rw [map_mul]; exact mul_ne_zero hx1 hx2
  · rw [map_mul, map_mul, ← hf1, ← hf2]; ring
  · rw [map_mul, map_mul, vr_mul e hx1 hx2, vr_mul e hs1 hs2, hu1, hu2]; ring
end GlobalTheory.Reg.TrivBound
