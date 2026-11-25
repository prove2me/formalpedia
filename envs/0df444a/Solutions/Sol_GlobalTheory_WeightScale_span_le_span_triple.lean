-- Prove2me | solution 1 for GlobalTheory.WeightScale.span_le_span_triple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:28:27.838109+00:00
-- url     : https://prove2.me/submissions/62d6d8b0-2f0c-4faa-b89d-05f20e14dd4a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsLiftAddOfIsReducedEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsUnimodularSolTriple

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw
open GlobalTheory GlobalTheory.WeightScale
variable {A B : Type*} [CommRing A] [CommRing B]
namespace GlobalTheory.WeightScale
theorem _root_.solution {u : A} (hu : IsUnit u) (P : Fin 3 → A) :
    Ideal.span (Set.range P) ≤ Ideal.span (Set.range (triple u P)) := by
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact (Ideal.unit_mul_mem_iff_mem _ (hu.pow 2)).mp (Ideal.subset_span ⟨0, rfl⟩)
  · exact (Ideal.unit_mul_mem_iff_mem _ (hu.pow 3)).mp (Ideal.subset_span ⟨1, rfl⟩)
  · exact Ideal.subset_span ⟨2, rfl⟩
end GlobalTheory.WeightScale
