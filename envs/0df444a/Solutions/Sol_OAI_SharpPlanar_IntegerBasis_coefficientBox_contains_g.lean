-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerBasis.coefficientBox_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:05:46.530979+00:00
-- url     : https://prove2.me/submissions/980ac2ec-bd2f-4267-ae9c-c0a921c6bae7

import Mathlib
import Definitions.Def_OAIQ098G001
import Definitions.Def_OAIQ098G071
import Definitions.Def_OAIQ098G083
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_rat_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_rat_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_scale_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_bBounds_contains_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma coefficientBox_contains_g_oai (n : ℕ) : (coefficientBox n).Contains (Pcoeff n) := by
  have hb : bBounds.Contains b := bBounds_contains_g
  have hp := RBox.contains_scale_g hb 2 1 (by norm_num)
  have hm := RBox.contains_scale_g hb (-2) 1 (by norm_num)
  have h0 (m k : ℤ) (hk : 0 < k) := CBox.contains_rat_g m k 0 1 hk (by norm_num)
  have hr (m k : ℤ) (hk : 0 < k) := RBox.contains_rat_g m k hk
  rcases n with _|_|_|_|_|_|_|n
  · simpa [coefficientBox,Pcoeff] using h0 5 1 (by norm_num)
  · constructor
    · simpa [coefficientBox,Pcoeff] using hr (-1) 1 (by norm_num)
    · simpa [coefficientBox,Pcoeff] using hp
  · constructor
    · simpa [coefficientBox,Pcoeff] using hr 1 1 (by norm_num)
    · simpa [coefficientBox,Pcoeff] using hp
  · simpa [coefficientBox,Pcoeff] using h0 (-2) 1 (by norm_num)
  · constructor
    · convert hr (-1) 2 (by norm_num) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num [coefficientBox,Pcoeff])
    · simpa [coefficientBox,Pcoeff] using hb
  · constructor
    · simpa [coefficientBox,Pcoeff] using hr (-1) 1 (by norm_num)
    · simpa [coefficientBox,Pcoeff] using hm
  · simpa [coefficientBox,Pcoeff] using h0 1 1 (by norm_num)
  · simpa [coefficientBox,Pcoeff] using h0 0 1 (by norm_num)

end SharpPlanar.IntegerBasis

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerBasis.coefficientBox_contains_g_oai := @OAI.SharpPlanar.IntegerBasis.coefficientBox_contains_g_oai
