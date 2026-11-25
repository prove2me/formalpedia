-- Prove2me | solution 1 for GlobalTheory.MoveFine.relIndex_inf_scl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:03:43.805679+00:00
-- url     : https://prove2.me/submissions/705b141e-3d86-49a4-8893-493b1bea8a92

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
import Theorems.Thm_GlobalTheory_MoveFine_mem_scl

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
namespace GlobalTheory.MoveFine
theorem _root_.solution {E W : Type} [CommRing E] [AddCommGroup W] [Module E W] (P Z : AddSubgroup W)
    (c e : E) (he : IsUnit e) (h : (scl P (e * c)).relIndex P ≠ 0) (G : AddSubgroup W) (hG : G ≤ Z)
    (hGP : ∀ w ∈ G, e • w ∈ P) : (Z ⊓ scl P c).relIndex G ≠ 0 := by
  let φ : W →+ W := (e • (LinearMap.id : W →ₗ[E] W)).toAddMonoidHom
  have h1 : ((scl P (e * c)).comap φ).relIndex G ≠ 0 := by
    rw [AddSubgroup.relIndex_comap]
    refine fun h0 => h (AddSubgroup.relIndex_eq_zero_of_le_right ?_ h0)
    rintro _ ⟨w, hw, rfl⟩
    exact hGP w hw
  rw [← AddSubgroup.inf_relIndex_right] at h1
  refine fun h0 => h1 (AddSubgroup.relIndex_eq_zero_of_le_left ?_ h0)
  rintro w ⟨hw, hwG⟩
  refine ⟨hG hwG, ?_⟩
  obtain ⟨y, hy, e1⟩ := mem_scl.1 (show φ w ∈ scl P (e * c) from hw)
  refine mem_scl.2 ⟨y, hy, he.smul_left_cancel.1 ?_⟩
  rw [← mul_smul, ← e1]; rfl
end GlobalTheory.MoveFine
