-- Prove2me | solution 1 for NewtonianLipschitz.tangential_denominator_fifth_power_ge_twelve
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:57:57.680929+00:00
-- url     : https://prove2.me/submissions/c66b975f-7d5c-48e0-bf9c-5c1ac2b32fec

module
public import Definitions.Def_NewtonianLipschitz_CrossFaceTwoHop
public import Definitions.Def_NewtonianLipschitz_TangentialAlgebra

set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution
    (t : ℝ) (ht : 0 ≤ t) :
    12 * t ≤ (1 + t) ^ 5 := by
  have hidentity :
      (1 + t) ^ 5 - 12 * t =
        (1 - 4 * t) ^ 2 +
          t * (1 - 3 * t) ^ 2 +
          t ^ 3 + 5 * t ^ 4 + t ^ 5 := by
    ring
  have hnonneg :
      0 ≤ (1 - 4 * t) ^ 2 +
        t * (1 - 3 * t) ^ 2 +
        t ^ 3 + 5 * t ^ 4 + t ^ 5 := by
    positivity
  linarith
end NewtonianLipschitz
