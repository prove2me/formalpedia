-- Prove2me | solution 1 for GlobalTheory.T.continuous_slice_section_measure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:05:28.413124+00:00
-- url     : https://prove2.me/submissions/213a46b5-1a96-4f04-ba87-57a748688529

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousSliceSectionMeasure
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OmAOneApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousSliceSectionMeasureStatement
import Theorems.Thm_GlobalTheory_RankFibreKer_exists_isCompact_of_slice


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (Φ : Matrix (Fin a) (Fin d) k → ℂ), Φ ∈ fullRankSB k a d →
    ∀ (s : Matrix (Fin a) (Fin d) k → GL (Fin a) k), ContinuousOn s {Y | Y.rank = a} →
    (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank = a → ((s Y)⁻¹).val * Y ∈ slice k a d) →
    (∀ (Z : Matrix (Fin a) (Fin d) k) (g : GL (Fin a) k), Z ∈ slice k a d → g.val * Z ∈ slice k a d → g = 1) →
    ∃ C : Set (GL (Fin a) k), IsCompact C ∧ ∀ (g : GL (Fin a) k) (Z : Matrix (Fin a) (Fin d) k), Z ∈ slice k a d →
      Φ (g.val * Z) ≠ 0 → g ∈ C := by
  first | exact @GlobalTheory.RankFibreKer.exists_isCompact_of_slice | exact GlobalTheory.RankFibreKer.exists_isCompact_of_slice | (intros; apply GlobalTheory.RankFibreKer.exists_isCompact_of_slice <;> assumption)
end _root_.GlobalTheory.T
