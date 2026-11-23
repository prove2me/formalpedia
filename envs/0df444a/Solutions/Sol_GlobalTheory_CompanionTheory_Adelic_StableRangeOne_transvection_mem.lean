-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Adelic.StableRangeOne.transvection_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:01:57.345461+00:00
-- url     : https://prove2.me/submissions/2c58c19e-9a11-4e46-bec7-9a263ddd077c

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
theorem _root_.solution {i j : ι} (h : i ≠ j) (c : R) :
    Matrix.transvection i j c ∈ elem R ι :=
  Submonoid.subset_closure (Or.inl ⟨i, j, c, h, rfl⟩)
end GlobalTheory.CompanionTheory.Adelic.StableRangeOne
