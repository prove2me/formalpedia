-- Prove2me | solution 1 for GroundTheory.Global.dedekindZeta_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:54:43.018458+00:00
-- url     : https://prove2.me/submissions/cda50b42-2acd-45d1-bd16-3470668fa61b

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_PrimeZetaPole

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain Filter Topology Set Ideal
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution {s : ℝ} (hs : s ≠ 0) :
    dedekindZeta K s = (dedekindZetaReal K s : ℂ) := by
  rw [dedekindZeta, LSeries, dedekindZetaReal, Complex.ofReal_tsum]
  congr 1
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [dedekindZetaTerm, Real.zero_rpow (neg_ne_zero.mpr hs)]
  · rw [LSeries.term_of_ne_zero hn, dedekindZetaTerm, Complex.ofReal_mul,
      Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_neg, Complex.cpow_neg,
      div_eq_mul_inv]
    simp
end GroundTheory.Global
