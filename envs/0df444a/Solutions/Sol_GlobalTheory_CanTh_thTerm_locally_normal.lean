-- Prove2me | solution 1 for GlobalTheory.CanTh.thTerm_locally_normal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:31:43.065127+00:00
-- url     : https://prove2.me/submissions/893beb30-9079-4258-a9d1-328e11db3616

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
import Theorems.Thm_GlobalTheory_CanTh_thTerm_eq_thetaTerm
import Theorems.Thm_GlobalTheory_thetaMTest_holds


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
theorem _root_.solution {U : Set W} (hU : IsOpen U) {T : W → Matrix (Fin g) (Fin g) ℂ}
    {Z : W → Fin g → ℂ} (hT : ∀ i j, ContinuousOn (fun w => T w i j) U) (hZ : ContinuousOn Z U)
    (hdom : ∀ w ∈ U, T w ∈ ThetaDomain (Fin g)) (a b : Fin g → ℝ) {x : W} (hx : x ∈ U) :
    ∃ t ∈ 𝓝 x, ∃ v : (Fin g → ℤ) → ℝ, Summable v ∧
      ∀ m, ∀ w ∈ t, ‖thTerm (T w) a b (Z w) m‖ ≤ v m := by
  obtain ⟨K, ⟨hKx, hK⟩, hKU⟩ := (compact_basis_nhds x).mem_iff.mp (hU.mem_nhds hx)
  have hc : ContinuousOn (fun w => ((Z w, fun i j => T w i j) :
      (Fin g → ℂ) × (Fin g → Fin g → ℂ))) K :=
    (hZ.prodMk (continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => hT i j)).mono hKU
  obtain ⟨v, hv, h⟩ := thetaMTest_holds (Fin g) a _ (hK.image_of_continuousOn hc) (by
    rintro _ ⟨w, hw, rfl⟩
    exact hdom w (hKU hw))
  refine ⟨K, hKx, v, hv, fun m w hw => ?_⟩
  rw [thTerm_eq_thetaTerm]
  exact h b _ ⟨w, hw, rfl⟩ m
end GlobalTheory.CanTh
