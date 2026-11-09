-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerBasis.cachedMomentRuleBox_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:05:17.726568+00:00
-- url     : https://prove2.me/submissions/577fec92-0a50-452e-9a75-0016cad8bb82

import Mathlib
import Definitions.Def_OAIQ098G072
import Definitions.Def_OAIQ098G079
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_sum_fin_square_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_add_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_mul_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_scale_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerIntervals

lemma zeroBox_contains : zeroBox.Contains 0 := by simp [zeroBox,CBox.Contains,RBox.Contains]
end SharpPlanar.IntegerIntervals

namespace SharpPlanar.IntegerIntervals

lemma finSum_contains {N : ℕ} {f : Fin N → CBox} {g : Fin N → ℂ}
    (h : ∀ i, (f i).Contains (g i)) : (finSum f).Contains (∑ i, g i) := by
  induction N with
  | zero => simpa [finSum] using zeroBox_contains
  | succ N ih =>
    rw [Fin.sum_univ_succ]
    exact CBox.contains_add_g (h 0) (ih (fun i => h i.succ))

end SharpPlanar.IntegerIntervals

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma cachedMomentRuleBox_contains_g_oai
    {c k : Fin 6 → Fin 16 → Fin 16 → CBox} {t : ℕ → ℕ → ℝ} {w : ℕ → ℝ}
    {n m : ℕ} {d e : Bool}
    (hc : ∀ j i v, (c j i v).Contains ((w (16*i.val+v.val):ℂ)*
      basisFunction d n j.val (t j.val (16*i.val+v.val))))
    (hk : ∀ j i v, (k j i v).Contains
      (lambda (t j.val (16*i.val+v.val))*Complex.exp (Complex.I*Real.pi*z (t j.val (16*i.val+v.val))*m)*
      (if e then Complex.I*Real.pi*z (t j.val (16*i.val+v.val)) else 1))) :
    (cachedMomentRuleBox c k).Contains (momentRuleValue t w n m d e) := by
  unfold cachedMomentRuleBox momentRuleValue
  apply finSum_contains
  intro j
  rw [← sum_fin_square_g 16 (fun v => (w v:ℂ)*basisMoment d e n j.val m (t j.val v))]
  have hh := finSum_contains (fun i => finSum_contains (fun v => CBox.contains_mul_g (hc j i v) (hk j i v)))
  have hs := CBox.contains_scale_g hh 1 6 (by norm_num)
  simpa only [Int.cast_one,Int.cast_ofNat,basisMoment,mul_assoc] using hs

end SharpPlanar.IntegerBasis

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerBasis.cachedMomentRuleBox_contains_g_oai := @OAI.SharpPlanar.IntegerBasis.cachedMomentRuleBox_contains_g_oai
