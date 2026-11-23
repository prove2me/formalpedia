-- Prove2me | solution 1 for GlobalTheory.LaurentConst.scaleP_C
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:28:45.773974+00:00
-- url     : https://prove2.me/submissions/6f6ca95e-7564-43c5-9cd7-283940d3a881

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExtOfForallQuotient
import Theorems.Thm_GlobalTheory_restrictPoints_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open GlobalTheory GlobalTheory.LaurentConst
open AddMonoidAlgebra
attribute [-simp] LaurentPolynomial.single_eq_C_mul_T
variable {L R : Type} [CommRing L] [CommRing R]
variable (r : L →+* R) (t : Rˣ)
namespace GlobalTheory.LaurentConst
theorem _root_.solution (c : L) : scaleP r t (PowerSeries.C c) = PowerSeries.C (r c) := by
  ext n
  simp [scaleP, PowerSeries.coeff_C]
  aesop
end GlobalTheory.LaurentConst
