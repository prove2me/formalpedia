-- Prove2me | solution 1 for GlobalTheory.HL.MoveSame.iso_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:01:22.446412+00:00
-- url     : https://prove2.me/submissions/5ed23622-57c2-430a-b4e2-d0d343990668

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermInvariantsIndependentOfWitnesses
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFramesDatumMovePropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MoveLatticeIsTermSameDatumWithWitnessesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianMovePreservesFrameLatticeLevels
import Theorems.Thm_GlobalTheory_FrameBasic_mem_perp_span
import Theorems.Thm_GlobalTheory_HL_StdLat_image_lt
import Theorems.Thm_GlobalTheory_HL_StdLat_mem_perp_span


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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.MoveSame
open GlobalTheory.HL.Eichler
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.MoveSame
theorem _root_.solution {g : Fin (r + 1) → S.V}
    (hg : ∀ a (j : Fin r), hf L S.Hm (g a) (g j.castSucc) = 0) {J : ℕ} {v : S.V}
    (hv : v ∈ S.spanTo g J) : v ∈ perp L S.Hm (S.spanTo g r) := by
  refine (Submodule.span_le.2 ?_ : S.spanTo g J ≤ _) hv
  rintro _ ⟨i, -, rfl⟩
  rw [SetLike.mem_coe, Frames.spanTo, StdLat.image_lt, StdLat.mem_perp_span]
  exact hg _
end GlobalTheory.HL.MoveSame
