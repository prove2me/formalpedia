-- Prove2me | solution 1 for GlobalTheory.RankStrata.sub_mem_Nsp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:33:13.66121+00:00
-- url     : https://prove2.me/submissions/a17396ee-f3e2-483d-a992-8d79a7d496c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubMemNsp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.WeilM Matrix
noncomputable section
open GlobalTheory GlobalTheory.RankStrata
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {k}
namespace GlobalTheory.RankStrata
theorem _root_.solution {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ν : kˣ →* ℂˣ)
    (g : GL A k) {Ψ : Matrix A D k → ℂ} (hΨ : Ψ ∈ SB (Matrix A D k)) :
    GlobalTheory.SplitFlip.omB ν ν g 1 Ψ - Ψ ∈ Nsp k A D ν :=
  Submodule.subset_span ⟨g, Ψ, hΨ, rfl⟩
end GlobalTheory.RankStrata
