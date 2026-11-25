-- Prove2me | solution 1 for GlobalTheory.HL.PrimTerm.Mof_le_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:03:04.770787+00:00
-- url     : https://prove2.me/submissions/0b3d6678-f631-432e-8237-b2a052cb21a4

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermInvariantsIndependentOfWitnesses
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFrameClassProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SelfDualLatticeUnipotentTranslateStandard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemSpanOfMemMof
import Theorems.Thm_GlobalTheory_HL_PrimTerm_left_mem
import Theorems.Thm_GlobalTheory_HL_PrimTerm_diff_mem
import Theorems.Thm_GlobalTheory_HL_PrimTerm_th_smul
import Theorems.Thm_GlobalTheory_HL_FrameClass_smul_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.PrimTerm
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.PrimTerm
theorem _root_.solution (h0 : S.th ≠ 0) (hO : algebraMap F E S.th ∈ L.O) (g g' : Fin (r + 1) → S.V) :
    S.Mof g' g ≤ S.Mof g g' := by
  refine Submodule.span_le.2 ?_
  rintro x (⟨b, rfl⟩ | ⟨b, rfl⟩)
  · have h1 := (S.Mof g g').smul_mem ⟨_, hO⟩ (diff_mem S g g' b)
    have h2 : (⟨_, hO⟩ : L.O) • algebraMap F E S.th⁻¹ • (g' b - g b) = g' b - g b :=
      th_smul S h0 _
    rw [h2] at h1
    have h3 := (S.Mof g g').add_mem h1 (left_mem S g g' b)
    rwa [sub_add_cancel] at h3
  · have h1 := (S.Mof g g').neg_mem (diff_mem S g g' b)
    rw [← smul_neg, neg_sub] at h1
    exact h1
end GlobalTheory.HL.PrimTerm
