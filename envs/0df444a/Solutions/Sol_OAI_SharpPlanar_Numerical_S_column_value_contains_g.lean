-- Prove2me | solution 1 for OAI.SharpPlanar.Numerical.S_column_value_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T09:09:54.353324+00:00
-- url     : https://prove2.me/submissions/415bcdf0-b1c5-4e5d-9712-f158f267b8fe

import Mathlib
import Definitions.Def_OAIQ098G004
import Definitions.Def_OAIQ098G099
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_contains_mul_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_RBox_neg_contains_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_qiBox_contains_g
import Theorems.Thm_OAI_SharpPlanar_S_apply_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Entries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Entries of the cardinal interpolation operator

The columns of the interpolation operator are cardinal basis functions, and
certified quadrature controls their value and derivative entries.
-/

namespace SharpPlanar
open IntegerBasis IntegerIntervals IntegerGrid


lemma S_column_value (n m : Node) (d : Bool) :
    S (columnVector n d) (m,false) = -K (positiveData (columnVector n d)) 0 m.val / Q m.val := by
  simp [S_apply_g,Scoords]

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_NodeIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open IntegerIntervals IntegerBasis IntegerGrid
namespace Numerical

lemma S_column_value_contains_g_oai {n m : Node} {d : Bool} {a : RBox}
    (ha : a.Contains (K (positiveData (columnVector n d)) 0 m.val)) :
    (a.neg.mul (qiBox m.val)).Contains (S (columnVector n d) (m,false)) := by
  rw [S_column_value,div_eq_mul_inv]
  exact RBox.contains_mul_g (RBox.neg_contains_g ha) (qiBox_contains_g m.val m.property.2)
end Numerical
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Numerical.S_column_value_contains_g_oai := @OAI.SharpPlanar.Numerical.S_column_value_contains_g_oai
