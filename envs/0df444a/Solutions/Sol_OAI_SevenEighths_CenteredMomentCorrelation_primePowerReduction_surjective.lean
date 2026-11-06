-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentCorrelation.primePowerReduction_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:42:01.09535+00:00
-- url     : https://prove2.me/submissions/12680694-f206-4cc2-81b1-f6af92a37683

import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_Correlation
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_PrimePower

set_option autoImplicit false
open OAI
open scoped BigOperators Classical
open NumberField
open OAI.SevenEighths OAI.SevenEighths.CenteredMomentCorrelation
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
attribute [local instance] OAI.SevenEighths.CenteredMomentCorrelation._p2m_local_instance_3727eb8614_14
omit [NumberField K]
namespace OAI.SevenEighths.CenteredMomentCorrelation
theorem _root_.solution (P : Ideal (𝓞 K)) {c : ℕ} (hc : 1 ≤ c) :
    Function.Surjective (primePowerReduction P hc) :=
  Ideal.Quotient.factor_surjective _
end OAI.SevenEighths.CenteredMomentCorrelation
