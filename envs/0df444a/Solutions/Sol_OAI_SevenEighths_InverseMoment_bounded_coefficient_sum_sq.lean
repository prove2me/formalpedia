-- Prove2me | solution 1 for OAI.SevenEighths.InverseMoment.bounded_coefficient_sum_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:00:57.38873+00:00
-- url     : https://prove2.me/submissions/d41d5e31-bfc0-433c-9047-c4101ded06d6

import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_Fibers
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_SieveComposition
import Theorems.Thm_OAI_SevenEighths_InverseMoment_bounded_finset_coefficient_sum_sq

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
open scoped BigOperators
noncomputable section
namespace OAI.SevenEighths.InverseMoment
theorem _root_.solution {C : Type*} [Fintype C]
    (b f : C → ℂ) (hb : ∀ c, ‖b c‖ ≤ 1) :
    ‖∑ c, b c * f c‖ ^ 2 ≤ (Fintype.card C : ℝ) * ∑ c, ‖f c‖ ^ 2 := by
  classical
  simpa using bounded_finset_coefficient_sum_sq Finset.univ b f (by simpa using hb)
end OAI.SevenEighths.InverseMoment
