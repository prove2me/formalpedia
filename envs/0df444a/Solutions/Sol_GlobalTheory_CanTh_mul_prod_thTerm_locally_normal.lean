-- Prove2me | solution 1 for GlobalTheory.CanTh.mul_prod_thTerm_locally_normal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:44:45.911677+00:00
-- url     : https://prove2.me/submissions/02434655-b593-4a4d-9668-d278a4bf403c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SetIntegralPowEqZeroOfPosFreqEuclidean
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MemThetaDomainIffIsSiegelAddTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsMulDotProductLeOfIsCompactThetaDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_DifferentiableOnThetaProdOfNormal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_HasSumPolyDerivMulProdAddMatrix
import Theorems.Thm_GlobalTheory_CanTh_thTerm_locally_normal
import Theorems.Thm_GlobalTheory_summable_prod_tuples


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix Filter Topology ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Real
open GlobalTheory GlobalTheory.CanTh
variable {g : ℕ}
variable {W : Type*} [TopologicalSpace W] [LocallyCompactSpace W]
namespace GlobalTheory.CanTh
theorem _root_.solution {κ : Type*} [Fintype κ] {U : Set W} (hU : IsOpen U)
    {G : W → ℂ} {T : κ → W → Matrix (Fin g) (Fin g) ℂ} {Z : κ → W → Fin g → ℂ}
    (hG : ContinuousOn G U) (hT : ∀ k i j, ContinuousOn (fun w => T k w i j) U)
    (hZ : ∀ k, ContinuousOn (Z k) U) (hdom : ∀ k, ∀ w ∈ U, T k w ∈ ThetaDomain (Fin g))
    (a b : κ → Fin g → ℝ) {x : W} (hx : x ∈ U) :
    ∃ t ∈ 𝓝 x, ∃ v : (κ → Fin g → ℤ) → ℝ, Summable v ∧
      ∀ m, ∀ w ∈ t, ‖G w * ∏ k, thTerm (T k w) (a k) (b k) (Z k w) (m k)‖ ≤ v m := by
  choose t ht v hv h using fun k =>
    thTerm_locally_normal hU (hT k) (hZ k) (hdom k) (a k) (b k) hx
  have h0 : ∀ k m, 0 ≤ v k m := fun k m =>
    (norm_nonneg _).trans (h k m x (mem_of_mem_nhds (ht k)))
  have hG' : ∀ᶠ w in 𝓝 x, ‖G w‖ < ‖G x‖ + 1 :=
    (hG.continuousAt (hU.mem_nhds hx)).norm.eventually (gt_mem_nhds (lt_add_one _))
  refine ⟨{w | ‖G w‖ < ‖G x‖ + 1} ∩ ⋂ k, t k, inter_mem hG' (iInter_mem.2 ht),
    fun m => (‖G x‖ + 1) * ∏ k, v k (m k),
    (summable_prod_tuples (J := fun _ : κ => Fin g → ℤ) h0 hv).mul_left _, fun m w hw => ?_⟩
  rw [norm_mul, norm_prod]
  exact mul_le_mul (le_of_lt hw.1) (Finset.prod_le_prod (fun k _ => norm_nonneg _)
    fun k _ => h k _ w (Set.mem_iInter.1 hw.2 k))
    (Finset.prod_nonneg fun k _ => norm_nonneg _) (by positivity)
end GlobalTheory.CanTh
