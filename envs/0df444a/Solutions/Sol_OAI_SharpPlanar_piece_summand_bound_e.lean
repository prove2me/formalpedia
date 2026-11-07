-- Prove2me | solution 1 for OAI.SharpPlanar.piece_summand_bound_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T04:06:34.653369+00:00
-- url     : https://prove2.me/submissions/34b426e2-74ac-4cd4-81c8-ca613002545c

import Mathlib
import Definitions.Def_OAIQ098E126
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_basis_density_bounds_e

section
-- module Solutions.OAIQ098_PP.PlanarPacking_CanonicalRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar
open IntegerBasis

lemma piece_summand_bound_e_oai (x : X) (n : Node) (j : Fin 6) {t : ℝ}
    (ht : (j.val:ℝ)/6 ≤ t ∧ t ≤ ((j.val:ℝ)+1)/6) :
    ‖(x (n,false):ℂ)*u n.val j.val t+(x (n,true):ℂ)*v n.val j.val t‖ ≤
      densityCap j*(|x (n,false)|+|x (n,true)|) := by
  obtain ⟨hu,hv⟩ := basis_density_bounds_e n.val n.prop.2 j ht
  calc
    _ ≤ ‖(x (n,false):ℂ)*u n.val j.val t‖+‖(x (n,true):ℂ)*v n.val j.val t‖ := norm_add_le _ _
    _ = |x (n,false)| *‖u n.val j.val t‖+|x (n,true)| *‖v n.val j.val t‖ := by simp
    _ ≤ |x (n,false)| *densityCap j+|x (n,true)| *densityCap j := by gcongr
    _ = _ := by ring

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.piece_summand_bound_e_oai := @OAI.SharpPlanar.piece_summand_bound_e_oai
