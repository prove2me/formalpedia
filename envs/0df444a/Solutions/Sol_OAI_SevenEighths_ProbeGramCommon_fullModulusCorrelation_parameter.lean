-- Prove2me | solution 1 for OAI.SevenEighths.ProbeGramCommon.fullModulusCorrelation_parameter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:19:41.451916+00:00
-- url     : https://prove2.me/submissions/56ed15b2-5c41-431d-acc6-68b657bd6bc1

import Definitions.Def_OAI_NumberTheory_DirichletL_Detector_GramCommonParam
import Definitions.Def_OAI_NumberTheory_DirichletL_Detector_GramCommonSum
import Theorems.Thm_OAI_SevenEighths_ProbeGramCommon_fullModulusCorrelation_solutions

set_option autoImplicit false
open OAI
noncomputable section
open scoped Classical
open OAI.SevenEighths OAI.SevenEighths.ProbeGramCommon
open CenteredMomentCorrelation
variable {A : Type*} [CommRing A] [IsDomain A]
namespace OAI.SevenEighths.ProbeGramCommon
theorem _root_.solution (C n₁ n₂ a b k : A) (hC : C≠0) (hn₁ : n₁≠0)
    (hab : a*n₁+b*n₂=1)
    [Fintype (ResidueQ C)] [Fintype (ResidueQ (C*n₁))] [Fintype (ResidueQ (C*n₂))]
    (χ : MulChar (ResidueQ (C*n₁)) ℂ) (ψ : MulChar (ResidueQ (C*n₂)) ℂ) :
    fullModulusCorrelation (C*n₁) (C*n₂) χ ψ (C*k)=
      ∑t : ResidueQ C,χ (leftParam C n₁ b k t)*star (ψ (rightParam C n₂ a k t)) := by
  rw [fullModulusCorrelation_solutions]
  symm
  exact Fintype.sum_equiv (solutionEquiv C n₁ n₂ a b k hC hn₁ hab) _ _ (fun _=>rfl)
end OAI.SevenEighths.ProbeGramCommon
