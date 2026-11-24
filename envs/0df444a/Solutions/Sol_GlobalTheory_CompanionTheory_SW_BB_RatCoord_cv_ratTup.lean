-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.BB.RatCoord.cv_ratTup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:10:42.703269+00:00
-- url     : https://prove2.me/submissions/094a646b-8b23-4996-9f4a-7e61db50f37e

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussQ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsTraceFormGramMatrixInBasis
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteComponentCoordinatesAction

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
theorem _root_.solution (R : Type) [CommRing R] [Algebra F R] {d M : ℕ}
    (b : Module.Basis (Fin d) F E) (x : Fin M × Fin d → F) :
    cv R b (ratTup R (ofF b x) 0) = fun j => algebraMap F R (x j) := by
  funext p
  have h : b.repr (∑ k, x (p.1, k) • b k) p.2 = x p := by
    rw [Module.Basis.repr_sum_self]
  simp only [cv, ratTup, ofF, inclR]
  change (Algebra.TensorProduct.basis R b).repr ((1 : R) ⊗ₜ[F] (∑ k, x (p.1, k) • b k)) p.2 = _
  rw [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, h, one_smul]
end GlobalTheory.CompanionTheory.SW.BB.RatCoord
