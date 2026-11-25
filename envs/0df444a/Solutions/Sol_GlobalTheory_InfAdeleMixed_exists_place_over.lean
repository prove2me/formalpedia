-- Prove2me | solution 1 for GlobalTheory.InfAdeleMixed.exists_place_over
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:33:55.268017+00:00
-- url     : https://prove2.me/submissions/726f8098-8cd3-42eb-bf12-ce69e55cda41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_InfAdeleTensorBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsInfiniteAdeleTensorEquivMixedSpace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical
open scoped TensorProduct ContDiff nonZeroDivisors
open GlobalTheory GlobalTheory.InfAdeleMixed
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace GlobalTheory.InfAdeleMixed
theorem _root_.solution [IsTotallyComplex E] [IsTotallyReal F] (v : InfinitePlace F) :
    ∃ w : {w : InfinitePlace E // w.IsComplex}, InfinitePlace.mk (w.1.embedding.comp (algebraMap F E)) = v := by
  obtain ⟨w, hw⟩ := InfinitePlace.comap_surjective (k := F) (K := E) v
  refine ⟨⟨w, IsTotallyComplex.isComplex w⟩, ?_⟩
  rw [← InfinitePlace.comap_mk, InfinitePlace.mk_embedding]
  exact hw
end GlobalTheory.InfAdeleMixed
