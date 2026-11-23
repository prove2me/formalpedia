-- Prove2me | solution 1 for GlobalTheory.PolyOfDeriv.hasDerivAt_iter
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:55:27.880819+00:00
-- url     : https://prove2.me/submissions/211a410b-d3b1-4c22-b442-57f7967b9c02

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_EqEvalOfDirDerivVanish

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open GlobalTheory GlobalTheory.PolyOfDeriv
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace GlobalTheory.PolyOfDeriv
theorem _root_.solution {u : E → ℂ} (hu : ContDiff ℝ ∞ u) (k : ℕ) (y x : E) (t : ℝ) :
    HasDerivAt (fun t : ℝ => iteratedFDeriv ℝ k u (y + t • x) (fun _ => x))
      (iteratedFDeriv ℝ (k+1) u (y + t • x) (fun _ => x)) t := by
  have hk : (k : WithTop ℕ∞) < ∞ := by exact_mod_cast ENat.coe_lt_top k
  have hd := ((hu.differentiable_iteratedFDeriv hk) (y + t • x)).hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ => y + t • x) x t := by
    simpa using ((hasDerivAt_id t).smul_const x).const_add y
  have h1 := hd.comp_hasDerivAt t hl
  have h2 := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => E) ℂ
    (fun _ => x)).hasFDerivAt.comp_hasDerivAt t h1
  rw [iteratedFDeriv_succ_apply_left]
  exact h2
end GlobalTheory.PolyOfDeriv
