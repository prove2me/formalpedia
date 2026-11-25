-- Prove2me | solution 1 for GlobalTheory.KSp.OpenCrit.tendsto_vOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:41:21.729287+00:00
-- url     : https://prove2.me/submissions/0888d58b-978b-4c43-8057-315edb3ad0e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QuadExtTopologyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenSubgroupOfSiegelAndOppositeNhds
import Theorems.Thm_P2M_GlobalTheory_KSp_OpenCrit_continuous_blk___234ddeb328d5
import Theorems.Thm_P2M_GlobalTheory_KSp_OpenCrit_continuous_blk___0416e917ecc0
import Theorems.Thm_P2M_GlobalTheory_KSp_OpenCrit_blk___one_6219ba4e2bbf
import Theorems.Thm_P2M_GlobalTheory_KSp_OpenCrit_blk___one_f3d920fac981

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary Filter Topology
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
noncomputable section
open GlobalTheory GlobalTheory.KSp GlobalTheory.KSp.OpenCrit
variable {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
  {ν : Type} [Fintype ν] [DecidableEq ν]
variable [TopologicalSpace E] [IsTopologicalRing E] [ContinuousInv₀ E] [T2Space E]
namespace GlobalTheory.KSp.OpenCrit
theorem _root_.solution : Tendsto (vOf c) (𝓝 (1 : UG c (stdJ ν E))) (𝓝 0) := by
  have hinv : ContinuousAt (fun g : UG c (stdJ ν E) => (mat c g).toBlocks₂₂⁻¹) 1 := by
    refine ContinuousAt.comp (g := Inv.inv) ?_ (continuous_blk₂₂ c).continuousAt
    apply continuousAt_matrix_inv
    rw [Ring.inverse_eq_inv', blk₂₂_one, det_one]
    exact continuousAt_inv₀ one_ne_zero
  have h2 : Tendsto (vOf c) (𝓝 1) (𝓝 (vOf c 1)) := (hinv.mul (continuous_blk₂₁ c).continuousAt).tendsto
  have h0 : vOf c (1 : UG c (stdJ ν E)) = 0 := by rw [vOf, blk₂₁_one, Matrix.mul_zero]
  rwa [h0] at h2
end GlobalTheory.KSp.OpenCrit
