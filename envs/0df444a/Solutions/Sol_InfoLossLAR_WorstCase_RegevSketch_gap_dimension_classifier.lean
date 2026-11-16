-- Prove2me | solution 1 for InfoLossLAR.WorstCase.RegevSketch.gap_dimension_classifier
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T09:02:12.04737+00:00
-- url     : https://prove2.me/submissions/a19214f3-7580-4e4e-a6a2-206d48475c03

import Definitions.Def_InfoLossLAR_FirstBridgeBundle_02
import Definitions.Def_InfoLossLAR_WorstCase_LatticeProblems
import Definitions.Def_InfoLossLAR_WorstCase_Family

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
open QAlgorithms.Complexity InfoLossLAR.WorstCase
open Integration9_9.LARPlatformEncoding Integration9_9.TM2PlatformSerialization
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open QMCNumericRuntime

namespace GapClassifierProof

def classifier (cutoff : ℕ) (word : Str) : Str :=
  [decide ((readB (readS word).2).2 < cutoff)]

theorem classifier_poly (cutoff : ℕ) : Poly (classifier cutoff) := by
  unfold classifier
  fun_prop

theorem classifier_correct (cutoff n : ℕ)
    (B : Matrix (Fin (famN n)) (Fin (famN n)) ℤ) (δ : ℚ) :
    classifier cutoff (encGapInstance B δ) = [decide (n < cutoff)] := by
  simp only [classifier, encGapInstance, encPair, readS_append, encMat, encL, readB_append]
  rw [List.length_ofFn]
  rfl

end GapClassifierProof
open GapClassifierProof

theorem solution (cutoff : ℕ) :
    ∃ f : Str → Str, PolyTimeComputable f ∧
      ∀ n : ℕ, ∀ B : Matrix (Fin (famN n)) (Fin (famN n)) ℤ,
        ∀ δ : ℚ, f (encGapInstance B δ) = [decide (n < cutoff)] := by
  have h : PolyTimeComputable (classifier cutoff) := by
    let P := (BooleanLists.packProgram.comp (classifier_poly cutoff).program).comp BooleanLists.unpackProgram
    exact ⟨(P.congr (classifier cutoff) (fun _ => rfl)).stock⟩
  exact ⟨classifier cutoff, h, classifier_correct cutoff⟩
