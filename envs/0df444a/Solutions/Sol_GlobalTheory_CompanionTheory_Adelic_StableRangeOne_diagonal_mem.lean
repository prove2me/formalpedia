-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Adelic.StableRangeOne.diagonal_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:59.160148+00:00
-- url     : https://prove2.me/submissions/72397bcc-3dc7-4c5d-ac09-3742f8c02243

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MatrixInductionTransvectionDiagonal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Adelic GlobalTheory.CompanionTheory.Adelic.StableRangeOne
variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.Adelic.StableRangeOne
theorem _root_.solution {D : ι → R} (h : ∀ i, IsUnit (D i)) : Matrix.diagonal D ∈ elem R ι :=
  Submonoid.subset_closure (Or.inr ⟨D, h, rfl⟩)
end GlobalTheory.CompanionTheory.Adelic.StableRangeOne
