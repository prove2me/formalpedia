-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.ThW.ZM_eq_blockDiagonal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:53.489109+00:00
-- url     : https://prove2.me/submissions/93abe5a1-8c4b-40bf-8d92-6f47a916152f

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SumRhoEqTrace
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SiegelMatrixSymmetricPosdefImag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.ThW
namespace GlobalTheory.CompanionTheory.SW.ThW
theorem _root_.solution {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]
    [DecidableEq ι] [DecidableEq (InfinitePlace F)] (B : Matrix ι ι F)
    (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ)
    (τ : InfinitePlace F → ℂ) : ZM B ρ P τ = blockDiagonal (ZB B ρ P τ) := rfl
end GlobalTheory.CompanionTheory.SW.ThW
