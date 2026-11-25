-- Prove2me | solution 1 for GlobalTheory.ThickLevel.finite_pieces
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:36:52.646388+00:00
-- url     : https://prove2.me/submissions/0fcfa69e-b38d-4423-a1a4-aec460e1366c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommensurableCosetUnionContentBiUnionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TupleJacobianRightMulIsometryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianMatrixCongruenceContentJacobianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MatrixCongruentOneModUniformizerPowGroupAndOrbitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalisedContentThickenedSetIndependentOfLevel
import Theorems.Thm_GlobalTheory_ThickLevel_cont_mono
import Theorems.Thm_GlobalTheory_T_commensurableCosetUnionContent_biUnion


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
open GlobalTheory GlobalTheory.ThickLevel
namespace GlobalTheory.ThickLevel
theorem _root_.solution {W : Type} [AddCommGroup W] (W0 : AddSubgroup W) {T : Set W} (hT : IsCO W0 T)
    (P : Set (Set W)) (c : ℝ) (hc : 0 < c) (h1 : ∀ p ∈ P, IsCO W0 p ∧ cont W0 p = c ∧ p ⊆ T)
    (h2 : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → Disjoint p q) : P.Finite := by
  by_contra hinf
  obtain ⟨N, hN⟩ := exists_nat_gt (cont W0 T / c)
  obtain ⟨s, hs, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf N
  obtain ⟨h3, h4⟩ := GlobalTheory.T.commensurableCosetUnionContent_biUnion W0 s (fun p => p) (fun p hp => (h1 p (hs hp)).1)
  have h5 := h4 (fun p hp q hq => h2 p (hs hp) q (hs hq))
  rw [Finset.sum_congr rfl (fun p hp => (h1 p (hs hp)).2.1), Finset.sum_const, hcard, nsmul_eq_mul] at h5
  have h6 := cont_mono W0 h3 hT (Set.iUnion₂_subset fun p hp => (h1 p (hs hp)).2.2)
  rw [div_lt_iff₀ hc] at hN
  linarith
end GlobalTheory.ThickLevel
