-- Prove2me | solution 1 for GroundTheory.Automorphic.contDiff_prodExpVal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:46:13.256259+00:00
-- url     : https://prove2.me/submissions/e58a49e9-3689-4352-b653-074ad2af90f5

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinBasic
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinHaarCoord
import Theorems.Thm_GroundTheory_Automorphic_prodExpVal_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped Manifold ContDiff Topology
open NormedSpace Set Filter
set_option linter.unusedSectionVars false
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
namespace GroundTheory.Automorphic
theorem _root_.solution {d : ℕ} (X : Fin d → 𝔸) : ContDiff ℝ ∞ (prodExpVal X) := by
  induction d with
  | zero =>
    have e : prodExpVal X = fun _ => 1 := funext fun t => by simp [prodExpVal]
    rw [e]; exact contDiff_const
  | succ d ih =>
    have e : prodExpVal X = fun t => exp (t 0 • X 0) *
        prodExpVal (fun i => X i.succ) (fun i => t i.succ) := funext (prodExpVal_succ X)
    rw [e]
    exact ((contDiff_exp ℝ 𝔸).comp ((contDiff_apply ℝ ℝ 0).smul contDiff_const)).mul
      ((ih _).comp (contDiff_pi.2 fun i => contDiff_apply ℝ ℝ i.succ))
end GroundTheory.Automorphic
