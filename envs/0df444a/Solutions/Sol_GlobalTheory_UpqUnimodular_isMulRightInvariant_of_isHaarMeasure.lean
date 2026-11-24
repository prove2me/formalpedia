-- Prove2me | solution 1 for GlobalTheory.UpqUnimodular.isMulRightInvariant_of_isHaarMeasure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:19:15.487521+00:00
-- url     : https://prove2.me/submissions/d1a7385b-ef4f-4875-b9fb-61ff60d09ddd

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ModularCharacterEqOneOnExpHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_HaarUpqIsMulRightInvariant
import Theorems.Thm_GlobalTheory_UpqUnimodular_isMulRightInvariant_of_continuousMulEquiv
import Theorems.Thm_Formalism_REAL_indefinite_unitary_unimodular


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Formalism.BasicNotions
noncomputable section
open GlobalTheory GlobalTheory.UpqUnimodular
namespace GlobalTheory.UpqUnimodular
theorem _root_.solution (P Q : ℕ) (μ : Measure (UpqT P Q))
    (hμ : μ.IsHaarMeasure) : μ.IsMulRightInvariant := by
  haveI : IsTopologicalGroup (UpqT P Q) := inferInstanceAs (IsTopologicalGroup (Formalism.UG.Upq P Q))
  haveI : BorelSpace (UpqT P Q) := ⟨rfl⟩
  refine isMulRightInvariant_of_continuousMulEquiv (modelEquiv P Q) μ ?_
  haveI : (μ.map (modelEquiv P Q)).IsHaarMeasure := (modelEquiv P Q).isHaarMeasure_map μ
  haveI : (Formalism.REAL.muG (signs P Q)).IsMulRightInvariant :=
    ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular _ _ g⟩
  rw [Measure.isMulLeftInvariant_eq_smul (μ.map (modelEquiv P Q)) (Formalism.REAL.muG (signs P Q))]
  infer_instance
end GlobalTheory.UpqUnimodular
