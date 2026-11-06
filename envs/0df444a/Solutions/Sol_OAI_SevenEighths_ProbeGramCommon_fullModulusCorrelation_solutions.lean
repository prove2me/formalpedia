-- Prove2me | solution 1 for OAI.SevenEighths.ProbeGramCommon.fullModulusCorrelation_solutions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:01:34.254443+00:00
-- url     : https://prove2.me/submissions/d34db1a5-132d-4de5-995f-5b4d685cbba7

import Definitions.Def_OAI_NumberTheory_DirichletL_Detector_GramCommonParam
import Definitions.Def_OAI_NumberTheory_DirichletL_Detector_GramCommonSum
import Theorems.Thm_OAI_SevenEighths_CenteredMomentCorrelation_scaledResidue_mk
import Theorems.Thm_OAI_SevenEighths_ProbeGramCommon_solutionEquiv_val
attribute [local simp] OAI.SevenEighths.CenteredMomentCorrelation.scaledResidue_mk
attribute [local simp] OAI.SevenEighths.ProbeGramCommon.solutionEquiv_val



set_option autoImplicit false
open OAI
noncomputable section
open scoped Classical
open OAI.SevenEighths OAI.SevenEighths.ProbeGramCommon
open CenteredMomentCorrelation
variable {A : Type*} [CommRing A] [IsDomain A]
omit [IsDomain A]
namespace OAI.SevenEighths.ProbeGramCommon
theorem _root_.solution (C n₁ n₂ k : A)
    [Fintype (ResidueQ (C*n₁))] [Fintype (ResidueQ (C*n₂))]
    (χ : MulChar (ResidueQ (C*n₁)) ℂ) (ψ : MulChar (ResidueQ (C*n₂)) ℂ) :
    fullModulusCorrelation (C*n₁) (C*n₂) χ ψ (C*k)=
      ∑p : Solutions C n₁ n₂ k,χ p.val.1*star (ψ p.val.2) := by
  unfold fullModulusCorrelation fullCorrelation
  change (∑x : ResidueQ (C*n₁),∑y : ResidueQ (C*n₂),
    if condition C n₁ n₂ k (x,y) then χ x*star (ψ y) else 0)=_
  rw [←Fintype.sum_prod_type (fun p : ResidueQ (C*n₁)×ResidueQ (C*n₂)=>
    if condition C n₁ n₂ k p then χ p.1*star (ψ p.2) else 0)]
  change (∑p : ResidueQ (C*n₁)×ResidueQ (C*n₂),
    if condition C n₁ n₂ k p then χ p.1*star (ψ p.2) else 0)=_
  rw [←Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _
end OAI.SevenEighths.ProbeGramCommon
