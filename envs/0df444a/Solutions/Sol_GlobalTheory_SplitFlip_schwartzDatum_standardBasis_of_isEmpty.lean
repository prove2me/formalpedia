-- Prove2me | solution 1 for GlobalTheory.SplitFlip.schwartzDatum_standardBasis_of_isEmpty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:13:23.335625+00:00
-- url     : https://prove2.me/submissions/931d8bdd-8f2a-4aea-a979-221d8cdef449

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Theorems.Thm_GlobalTheory_SplitFlip_isPrimitiveFrame_standardBasis
import Theorems.Thm_GlobalTheory_SplitFlip_blockLat_empty
import Theorems.Thm_GlobalTheory_SplitFlip_latA_blockLat
import Theorems.Thm_GlobalTheory_SplitFlip_splitTheta_fFun_frameFirstBlock_mul
import Theorems.Thm_GlobalTheory_SplitFlip_smallF_of_isEmpty

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.SplitFlip
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A A' D : Type*} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
variable [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.SplitFlip
theorem _root_.solution [IsEmpty A'] (σ : A ⊕ A' ≃ D) (ν : kˣ →* ℂˣ) (ϖ : kˣ) (e : ℕ) (Ψ : Matrix A' D k → ℂ) :
    phiA (haarVol (KO k A')) σ ν ϖ e (blockLat ϖ e Finset.univ) Ψ (X0 k σ) = Ψ 0 := by
  have := splitTheta_fFun_frameFirstBlock_mul (haarVol (KO k A')) σ ν Ψ 1
  rw [phiA, latA_blockLat, Finset.compl_univ, blockLat_empty, if_pos (isPrimitiveFrame_standardBasis σ)]
  simpa [smallF_of_isEmpty] using this
end GlobalTheory.SplitFlip
