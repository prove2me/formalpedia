-- Prove2me | solution 1 for GlobalTheory.SchwartzTranslate.hasDerivAt_iteratedFDeriv_line
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:38:42.871121+00:00
-- url     : https://prove2.me/submissions/27310a02-58f9-4725-95af-11c78d789311

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSeminormTranslateSubLineDerivLe
import Theorems.Thm_GlobalTheory_SchwartzTranslate_fderiv_iteratedFDeriv_apply_comm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped SchwartzMap ContDiff
open GlobalTheory GlobalTheory.SchwartzTranslate
namespace GlobalTheory.SchwartzTranslate
theorem _root_.solution {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (a : V) (n : ℕ) (g : V → F) (hg : ContDiff ℝ ∞ g)
    (x : V) (s : ℝ) :
    HasDerivAt (fun s : ℝ => iteratedFDeriv ℝ n g (x + s • a))
      (iteratedFDeriv ℝ n (fun y => fderiv ℝ g y a) (x + s • a)) s := by
  have hline : HasDerivAt (fun s : ℝ => x + s • a) a s := by
    simpa using ((hasDerivAt_id s).smul_const a).const_add x
  have hd : Differentiable ℝ (iteratedFDeriv ℝ n g) :=
    hg.differentiable_iteratedFDeriv (mod_cast ENat.natCast_lt_top n)
  have key : fderiv ℝ (iteratedFDeriv ℝ n g) (x + s • a) a
      = iteratedFDeriv ℝ n (fun y => fderiv ℝ g y a) (x + s • a) := by
    ext m
    rw [← fderiv_continuousMultilinear_apply_const_apply (hd _)]
    exact fderiv_iteratedFDeriv_apply_comm a n g hg _ m
  rw [← key]
  exact (hd _).hasFDerivAt.comp_hasDerivAt s hline
end GlobalTheory.SchwartzTranslate
