-- Prove2me | solution 1 for GlobalTheory.exists_mulPull_sec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:37:43.075917+00:00
-- url     : https://prove2.me/submissions/2162efea-9faf-4217-926d-f686656b1b59

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsMulPullSec
import Theorems.Thm_GlobalTheory_MulPullSec_exists_pull_sec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (H : Out.MulPullSt) :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N k : ℕ) (h : (lbPow P.L N).Sec),
      ∃ h' : (lbPow P.L (N * k ^ 2)).Sec, Out.nonzeroLocus h' = (Out.mulA P.A k).left ⁻¹ᵁ Out.nonzeroLocus h := by
  intro K _ _ P N k h
  obtain ⟨α, hα⟩ := H (Sp K) P k
  exact MulPullSec.exists_pull_sec P.isLB _ ((k : ℤ) ^ 2) N _ (by push_cast; ring) α hα h
end GlobalTheory
