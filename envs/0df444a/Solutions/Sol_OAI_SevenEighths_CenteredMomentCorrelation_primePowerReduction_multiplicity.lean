-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentCorrelation.primePowerReduction_multiplicity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:29:27.960231+00:00
-- url     : https://prove2.me/submissions/baf00ab2-e68a-4d21-9ed9-e1c9f27fac26

import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_Correlation
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_PrimePower
import Theorems.Thm_OAI_SevenEighths_CenteredMomentCorrelation_primePowerReduction_surjective
import Theorems.Thm_OAI_SevenEighths_CenteredMomentCorrelation_reductionMultiplicity_eq_pow


set_option autoImplicit false
open OAI
open scoped BigOperators Classical
open NumberField
open OAI.SevenEighths OAI.SevenEighths.CenteredMomentCorrelation
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
attribute [local instance] OAI.SevenEighths.CenteredMomentCorrelation._p2m_local_instance_3727eb8614_14
namespace OAI.SevenEighths.CenteredMomentCorrelation
theorem _root_.solution (P : Ideal (𝓞 K)) {c : ℕ} (hc : 1 ≤ c)
    [Fintype (𝓞 K ⧸ P ^ c)] [Fintype (𝓞 K ⧸ P)] :
    reductionMultiplicity (primePowerReduction P hc) = Ideal.absNorm P ^ (c - 1) := by
  have hcard (I : Ideal (𝓞 K)) [Fintype (𝓞 K ⧸ I)] :
      Fintype.card (𝓞 K ⧸ I) = Ideal.absNorm I := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  refine reductionMultiplicity_eq_pow _ (primePowerReduction_surjective P hc)
      (P := Ideal.absNorm P) ?_ hc ?_ ?_
  · rw [← hcard P]
    exact Fintype.card_pos
  · rw [hcard, map_pow]
  · exact hcard P
end OAI.SevenEighths.CenteredMomentCorrelation
