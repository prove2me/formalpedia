-- Prove2me | solution 1 for GlobalTheory.ThetaHalf.exists_real_of_half
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:47:14.573013+00:00
-- url     : https://prove2.me/submissions/66cef4c6-2252-4bf6-8b09-ac5c3170aa9a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_NormConst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Statements_HyperbolicHypotheses_HypothesesInhabitedHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_HasSumPolyDerivMulProdAddMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ThetaCharHalfDifferentiableNeZeroFamilies

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.ThetaHalf
namespace GlobalTheory.ThetaHalf
theorem _root_.solution {g : ℕ} {c : Fin g → ℂ} (hc : ∀ i, c i = 0 ∨ c i = 1 / 2) :
    ∃ a : Fin g → ℝ, c = fun i => (a i : ℂ) := by
  refine ⟨fun i => if c i = 0 then 0 else 1 / 2, funext fun i => ?_⟩
  rcases hc i with h | h
  · show c i = ((if c i = 0 then (0 : ℝ) else 1 / 2 : ℝ) : ℂ)
    rw [if_pos h, h, Complex.ofReal_zero]
  · have h0 : c i ≠ 0 := by rw [h]; norm_num
    show c i = ((if c i = 0 then (0 : ℝ) else 1 / 2 : ℝ) : ℂ)
    rw [if_neg h0, h]
    norm_num
end GlobalTheory.ThetaHalf
