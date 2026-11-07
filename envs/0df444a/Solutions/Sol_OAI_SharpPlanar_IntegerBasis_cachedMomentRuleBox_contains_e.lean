-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerBasis.cachedMomentRuleBox_contains_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T17:01:58.950342+00:00
-- url     : https://prove2.me/submissions/e6b187c8-ef33-4e30-b111-69ad3fbe176b

import Mathlib
import Definitions.Def_OAIQ098E031
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_sum_fin_square_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_mul_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_scale_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_finSum_contains_e

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma cachedMomentRuleBox_contains_e_oai
    {c k : Fin 6 → Fin 16 → Fin 16 → CBox} {t : ℕ → ℕ → ℝ} {w : ℕ → ℝ}
    {n m : ℕ} {d e : Bool}
    (hc : ∀ j i v, (c j i v).Contains ((w (16*i.val+v.val):ℂ)*
      basisFunction d n j.val (t j.val (16*i.val+v.val))))
    (hk : ∀ j i v, (k j i v).Contains
      (lambda (t j.val (16*i.val+v.val))*Complex.exp (Complex.I*Real.pi*z (t j.val (16*i.val+v.val))*m)*
      (if e then Complex.I*Real.pi*z (t j.val (16*i.val+v.val)) else 1))) :
    (cachedMomentRuleBox c k).Contains (momentRuleValue t w n m d e) := by
  unfold cachedMomentRuleBox momentRuleValue
  apply finSum_contains_e
  intro j
  rw [← sum_fin_square_e 16 (fun v => (w v:ℂ)*basisMoment d e n j.val m (t j.val v))]
  have hh := finSum_contains_e (fun i => finSum_contains_e (fun v => CBox.contains_mul_e (hc j i v) (hk j i v)))
  have hs := CBox.contains_scale_e hh 1 6 (by norm_num)
  simpa only [Int.cast_one,Int.cast_ofNat,basisMoment,mul_assoc] using hs

end SharpPlanar.IntegerBasis

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerBasis.cachedMomentRuleBox_contains_e_oai := @OAI.SharpPlanar.IntegerBasis.cachedMomentRuleBox_contains_e_oai
