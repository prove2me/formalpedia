-- Prove2me | solution 1 for GlobalTheory.Reg.TrivBound.chval_fin_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:08:25.160207+00:00
-- url     : https://prove2.me/submissions/7a453172-35c2-42d0-bf1e-88057888f020

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
theorem _root_.solution (φ : A →+* V) (e : ℕ) {f : FractionRing A} {u : ℝ} (h : ChV φ e f (u : EReal)) :
    ChV φ e f⁻¹ ((-u : ℝ) : EReal) := by
  obtain ⟨x, s, hs, hx, hfs, hu⟩ := (chval_fin_iff φ e f u).1 h
  have hx0 : x ≠ 0 := fun h0 => hx (by rw [h0, map_zero])
  have hxK : algebraMap A (FractionRing A) x ≠ 0 := fun h0 => hx0 (IsFractionRing.injective A _ (by rw [h0, map_zero]))
  have hf0 : f ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hfs
    exact hxK hfs.symm
  refine (chval_fin_iff φ e _ _).2 ⟨s, x, hx, hs, ?_, ?_⟩
  · rw [← hfs]
    field_simp
  · rw [hu]; ring
end GlobalTheory.Reg.TrivBound
