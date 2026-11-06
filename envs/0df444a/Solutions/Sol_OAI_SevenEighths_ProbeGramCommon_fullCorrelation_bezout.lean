-- Prove2me | solution 1 for OAI.SevenEighths.ProbeGramCommon.fullCorrelation_bezout
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:01:29.310227+00:00
-- url     : https://prove2.me/submissions/8c2b8702-f9f7-4955-9785-3be2d1e75bc9

import Definitions.Def_OAI_NumberTheory_DirichletL_Detector_GramCommonParam
import Definitions.Def_OAI_NumberTheory_DirichletL_Detector_GramCommonLinear
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
variable {R : Type*} [CommRing R]
namespace OAI.SevenEighths.ProbeGramCommon
theorem _root_.solution [Fintype R] (n₁ n₂ a b k : R) (hab : a*n₁+b*n₂=1)
    (f g : R→ℂ) :
    fullCorrelation (fun x=>n₂*x) (fun y=>n₁*y) f g k=
      ∑t : R,f (b*k+n₁*t)*star (g (-a*k+n₂*t)) := by
  unfold fullCorrelation
  rw [←Fintype.sum_prod_type (fun p : R×R=>if n₂*p.1-n₁*p.2=k then f p.1*star (g p.2) else 0)]
  have he := (Fintype.sum_equiv (bezoutPairEquiv n₁ n₂ a b hab)
    (fun p : R×R=>if p.2=k then f (b*p.2+n₁*p.1)*star (g (-a*p.2+n₂*p.1)) else 0)
    (fun p : R×R=>if n₂*p.1-n₁*p.2=k then f p.1*star (g p.2) else 0) (by
      intro p
      have hh : n₂*(b*p.2+n₁*p.1)-n₁*(-a*p.2+n₂*p.1)=p.2 := by
        linear_combination p.2*hab
      change (if p.2=k then _ else 0)=(if n₂*(b*p.2+n₁*p.1)-n₁*(-a*p.2+n₂*p.1)=k then _ else 0)
      rw [hh]
      rfl)).symm
  rw [he,Fintype.sum_prod_type]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
end OAI.SevenEighths.ProbeGramCommon
