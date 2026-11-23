-- Prove2me | solution 1 for GlobalTheory.ThetaRational.growth_finite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:08:33.333668+00:00
-- url     : https://prove2.me/submissions/0aa81299-d85e-4843-ac16-1de3199e6ea7

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsIntegralAndRationalTheta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real ContDiff
open GlobalTheory GlobalTheory.ThetaRational
variable {E : Type*} {n : ℕ}
namespace GlobalTheory.ThetaRational
theorem _root_.solution {ι : Type*} [Fintype ι] (x : E → ℝ) (hx : ∀ e, 1 ≤ x e) (u : ι → E → ℂ)
    (hu : ∀ c, ∃ (C : ℝ) (m : ℕ), 0 ≤ C ∧ ∀ e, ‖u c e‖ ≤ C * x e ^ m) :
    ∃ (C : ℝ) (m : ℕ), 0 ≤ C ∧ ∀ e c, ‖u c e‖ ≤ C * x e ^ m := by
  choose C m hC h using hu
  refine ⟨∑ c, C c, ∑ c, m c, Finset.sum_nonneg fun c _ => hC c, fun e c => (h c e).trans ?_⟩
  have h1 : C c ≤ ∑ c, C c := Finset.single_le_sum (fun c _ => hC c) (Finset.mem_univ c)
  have h2 : m c ≤ ∑ c, m c := Finset.single_le_sum (fun c _ => Nat.zero_le _) (Finset.mem_univ c)
  have := hx e
  have := hC c
  have := this.trans h1
  gcongr
end GlobalTheory.ThetaRational
