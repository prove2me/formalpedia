-- Prove2me | solution 1 for GlobalTheory.HL.BlockStab.cj_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:29:06.162381+00:00
-- url     : https://prove2.me/submissions/374ca386-c129-43ad-a295-883f1d8c4047

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesPairingStabilizerBlockDiagonal
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
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.BlockStab
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {n : ℕ}
namespace GlobalTheory.HL.BlockStab
theorem _root_.solution (L : LocE F E) {x : E} : L.cj x ∈ L.O ↔ x ∈ L.O := by
  have h : ∀ x, x ∈ L.O → L.cj x ∈ L.O := fun x hx => by
    rw [L.O_def] at hx ⊢
    exact hx.map (L.cj.toAlgHom.restrictScalars 𝒪[F])
  exact ⟨fun hx => by simpa [L.cj_cj] using h _ hx, h x⟩
end GlobalTheory.HL.BlockStab
