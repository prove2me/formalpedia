-- Prove2me | solution 1 for GlobalTheory.T.latticeStabilizer_inf_le_conj_normalisingSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:57:54.116695+00:00
-- url     : https://prove2.me/submissions/1245a081-01b9-4f28-b29a-fc868cf8fae6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeStabilizerInfLeConjNormalisingSubgroup
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeStabilizerInfLeConjNormalisingSubgroupStatement
import Theorems.Thm_GlobalTheory_FrameBasic_main
import Theorems.Thm_GlobalTheory_HL_FrameStabLat_main
import Theorems.Thm_GlobalTheory_HL_StabConj_main


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ n ∈ S.N, ∃ h ∈ S.St, S.St ⊓ stabL L (Submodule.span L.O (Set.range fun b => n (S.f b))) ≤ MulAut.conj h • S.K0 ∧ ∃ u : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUni u ∧ (∀ i j : Fin (r + 1), sameBlock S.w.blocks i j = true → u i j ∈ L.O) ∧ ∀ j, h⁻¹ (n (S.f j)) = ∑ i, u i j • S.f i := by
  first | exact @GlobalTheory.HL.StabConj.main | exact GlobalTheory.HL.StabConj.main | (intros; apply GlobalTheory.HL.StabConj.main <;> assumption)
end _root_.GlobalTheory.T
