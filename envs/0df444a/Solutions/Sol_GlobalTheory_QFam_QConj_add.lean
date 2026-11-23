-- Prove2me | solution 1 for GlobalTheory.QFam.QConj.add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:17:04.000933+00:00
-- url     : https://prove2.me/submissions/5b454110-b53d-41da-bdbe-e6dbe704482e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionOfLevelLinearOperations
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionOfLevelMulOfPosLevel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QExpansionsCoeffwiseConjugateRingClosure
import Theorems.Thm_GlobalTheory_QFam_HasQ_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory GlobalTheory.QFam
variable {g : ℂ ≃+* ℂ} {N : ℕ}
namespace GlobalTheory.QFam
namespace QConj
theorem _root_.solution {f f' h h' : ℍ → ℂ} (hf : QConj g N f f') (hh : QConj g N h h') :
    QConj g N (fun τ => f τ + h τ) fun τ => f' τ + h' τ := by
  obtain ⟨a, ha, ha'⟩ := hf
  obtain ⟨b, hb, hb'⟩ := hh
  refine ⟨fun n => a n + b n, ha.add hb, ?_⟩
  simpa only [map_add] using ha'.add hb'
end QConj
end GlobalTheory.QFam
