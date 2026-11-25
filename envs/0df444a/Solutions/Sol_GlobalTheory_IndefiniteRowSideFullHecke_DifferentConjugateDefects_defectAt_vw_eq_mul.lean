-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.defectAt_vw_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:55:42.54518+00:00
-- url     : https://prove2.me/submissions/908d2f82-c838-4263-97bf-9a760877425c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_HeightDefect_SchurLatticeConjugates

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects
namespace GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects
theorem _root_.solution {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (σ : E →+* K) (n' : ℕ+) (a : ℕ) (la : HeightOneSpectrum (𝓞 K)) (e : ℝ) (he : 0 < e) :
    (defectAt_vw σ n' a la : ℝ) = e * a * max ((ord_vw la (conjDifferent σ) : ℝ) / e)
      ((ord_vw la (Ideal.span {((n' : ℕ) : 𝓞 K)}) : ℝ) / e) := by
  rw [max_div_div_right he.le, defectAt_vw]
  push_cast
  field_simp
end GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects
