-- Prove2me | solution 1 for GlobalTheory.MoveFine.noLeak_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:14:04.681718+00:00
-- url     : https://prove2.me/submissions/ee8571d0-82a2-4f04-8e86-687babaf293c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NoLeak
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermExponentsNonnegAndDefectGroupBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerLatticeLocallyConstantDataStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsFineSubgroupMovesAtLattice
import Theorems.Thm_GlobalTheory_MoveFine_h_add_l
import Theorems.Thm_GlobalTheory_MoveFine_h_smul_l
import Theorems.Thm_GlobalTheory_MoveFine_h_smul_r
import Theorems.Thm_GlobalTheory_MoveFine_smul_memO
import Theorems.Thm_GlobalTheory_MoveFine_cjO
import Theorems.Thm_GlobalTheory_MoveFine_one_add_unit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.MoveFine
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
variable [IsNonarchimedeanLocalField F] [CharZero F]
namespace GlobalTheory.MoveFine
theorem _root_.solution (Λ : Submodule L.O S.V) (hΛ : IsSD L S.Hm Λ) (u b : S.V) (hb : b ∈ Λ)
    (h : S.NoLeak Λ u) : S.NoLeak Λ (u + algebraMap F E S.ϖ • b) := by
  obtain ⟨y, hy, hy', e⟩ := h
  obtain ⟨c, hc, e'⟩ := one_add_unit S ((hΛ.2 y).2 hy b hb)
  refine ⟨L.cj c • y, smul_memO S (cjO S hc) hy, S.W0.smul_mem _ hy', ?_⟩
  rw [h_smul_r, L.cj_cj, h_add_l, h_smul_l, e]
  exact e'
end GlobalTheory.MoveFine
