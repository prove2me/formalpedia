-- Prove2me | solution 1 for OAI.SevenEighths.ProbeGramCommon.solutionEquiv_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:50:58.493517+00:00
-- url     : https://prove2.me/submissions/be5ba7ce-9482-47bc-841b-000a4396eea4

import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_FullCorrelation
import Definitions.Def_OAI_NumberTheory_DirichletL_Detector_GramCommonParam

set_option autoImplicit false
open OAI
noncomputable section
open scoped Classical
open OAI.SevenEighths OAI.SevenEighths.ProbeGramCommon
open CenteredMomentCorrelation
variable {A : Type*} [CommRing A] [IsDomain A]
namespace OAI.SevenEighths.ProbeGramCommon
theorem _root_.solution (C n₁ n₂ a b k : A) (hC : C≠0) (hn₁ : n₁≠0)
    (hab : a*n₁+b*n₂=1) (t : ResidueQ C) :
    (solutionEquiv C n₁ n₂ a b k hC hn₁ hab t).val=(leftParam C n₁ b k t,rightParam C n₂ a k t) := rfl
end OAI.SevenEighths.ProbeGramCommon
