-- Prove2me | solution 1 for OAI.SevenEighths.ProbePrimePower.actualSextic_neg_one_sq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T00:24:06.845741+00:00
-- url     : https://prove2.me/submissions/2dab717d-a3ec-4fe6-af72-aa2ade9248aa

import Mathlib
import Definitions.Def_OAIHecke78B008

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.PrimeConstants
namespace OAI

noncomputable section
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

lemma actualSextic_neg_one_sq_oai (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) : actualSextic P hg (-1)^2 = 1 := by
  rw [← map_pow]
  norm_num

end SevenEighths.ProbePrimePower
end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.ProbePrimePower.actualSextic_neg_one_sq_oai := @OAI.SevenEighths.ProbePrimePower.actualSextic_neg_one_sq_oai
