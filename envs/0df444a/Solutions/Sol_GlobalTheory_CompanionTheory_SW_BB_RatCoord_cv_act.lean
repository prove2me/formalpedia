-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.BB.RatCoord.cv_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:26:47.332559+00:00
-- url     : https://prove2.me/submissions/45c6ad3f-fb7b-4eab-aa7a-737be7c63940

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussQ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsTraceFormGramMatrixInBasis
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteComponentCoordinatesAction
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BB_RatCoord_cv_ratTup
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_TraceCoord_coord_mulVec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB GlobalTheory.CompanionTheory.SW.BB.RatCoord
variable {F E : Type} [Field F] [Field E] [Algebra F E]
namespace GlobalTheory.CompanionTheory.SW.BB.RatCoord
theorem _root_.solution (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {d M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin d) F E) (h : HA R σ J)
    (x : Fin M × Fin d → F) :
    cv R b (actW R σ J h (ratTup R (ofF b x)) 0) =
      gmat R σ J b h *ᵥ fun j => algebraMap F R (x j) := by
  rw [← cv_ratTup R b x]
  refine TraceCoord.coord_mulVec (Algebra.TensorProduct.basis R b)
    (HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) (gmat R σ J b h) (fun p q => ?_) _
  rw [Algebra.TensorProduct.basis_apply]
  rfl
end GlobalTheory.CompanionTheory.SW.BB.RatCoord
