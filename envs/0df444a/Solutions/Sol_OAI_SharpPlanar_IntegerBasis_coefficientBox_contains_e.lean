-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerBasis.coefficientBox_contains_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T02:47:19.879823+00:00
-- url     : https://prove2.me/submissions/ce9cb468-a383-4959-9446-50d01d0b49e4

import Mathlib
import Definitions.Def_OAIQ098E031
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_rat_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_rat_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_scale_e
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_bBounds_contains_e

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma coefficientBox_contains_e_oai (n : ℕ) : (coefficientBox n).Contains (Pcoeff n) := by
  have hb : bBounds.Contains b := bBounds_contains_e
  have hp := RBox.contains_scale_e hb 2 1 (by norm_num)
  have hm := RBox.contains_scale_e hb (-2) 1 (by norm_num)
  have h0 (m k : ℤ) (hk : 0 < k) := CBox.contains_rat_e m k 0 1 hk (by norm_num)
  have hr (m k : ℤ) (hk : 0 < k) := RBox.contains_rat_e m k hk
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

theorem solution : type_of% @OAI.SharpPlanar.IntegerBasis.coefficientBox_contains_e_oai := @OAI.SharpPlanar.IntegerBasis.coefficientBox_contains_e_oai
