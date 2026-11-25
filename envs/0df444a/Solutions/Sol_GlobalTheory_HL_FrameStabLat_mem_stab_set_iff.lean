-- Prove2me | solution 1 for GlobalTheory.HL.FrameStabLat.mem_stab_set_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:33:55.492934+00:00
-- url     : https://prove2.me/submissions/d581712f-710d-4f74-ae64-a87531e13696

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsLatticeStabilizerNormalisingSubgroup
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
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameStabLat
variable {E : Type} [CommRing E] {V : Type} [AddCommGroup V] [Module E V] (O : Subring E)
namespace GlobalTheory.HL.FrameStabLat
theorem _root_.solution {G X : Type} [Group G] [MulAction G X] (C : Set X) (h : G) :
    h ∈ MulAction.stabilizer G C ↔ (∀ v ∈ C, h • v ∈ C) ∧ ∀ v ∈ C, h⁻¹ • v ∈ C := by
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro H
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · rw [← H]
      exact Set.smul_mem_smul_set hv
    · rw [← H] at hv
      exact Set.mem_smul_set_iff_inv_smul_mem.1 hv
  · rintro ⟨H1, H2⟩
    ext v
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    constructor
    · intro hv
      simpa using H1 _ hv
    · exact H2 v
end GlobalTheory.HL.FrameStabLat
