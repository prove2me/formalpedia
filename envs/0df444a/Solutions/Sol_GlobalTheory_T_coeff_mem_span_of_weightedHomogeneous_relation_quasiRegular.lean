-- Prove2me | solution 1 for GlobalTheory.T.coeff_mem_span_of_weightedHomogeneous_relation_quasiRegular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:14:19.656586+00:00
-- url     : https://prove2.me/submissions/2a96a37f-c1d3-4a53-a6bc-f0afe3ec9b20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoeffMemSpanOfWeightedHomogeneousRelationQuasiRe
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoeffMemSpanOfWeightedHomogeneousRelationQuasiReStatement
import Theorems.Thm_GlobalTheory_weightedRelation_coeff_mem_span


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {R : Type} [CommRing R] {n : ℕ} (z : Fin n → R) (w : Fin n → ℕ), (∀ i, 1 ≤ w i) →
    IsQuasiRegularSeq R z → ∀ (D : ℕ) (F : MvPolynomial (Fin n) R),
    F.IsWeightedHomogeneous w D → MvPolynomial.eval z F = 0 →
    ∀ α : Fin n →₀ ℕ, F.coeff α ∈ Ideal.span (Set.range z) := by
  first | exact @GlobalTheory.weightedRelation_coeff_mem_span | exact GlobalTheory.weightedRelation_coeff_mem_span | (intros; apply GlobalTheory.weightedRelation_coeff_mem_span <;> assumption)
end _root_.GlobalTheory.T
