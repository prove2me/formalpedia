-- Prove2me | solution 1 for ModularCurve.modularRing_eq_range_modularEval
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/5b5ae8fb-663d-595c-857f-aa59f027d74d

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_modularRing_eq_range_modularEval

set_option autoImplicit false

open ModularCurve ModularCurve.NodeLocalized

theorem solution (N : ℕ) [NeZero N] {L : Type*} [CommRing L] (A : Subring L) :
    CharPReduction.modularRing N A = (NodeLocalized.modularEval N A).range := by
  apply le_antisymm
  · rw [CharPReduction.modularRing, Subring.closure_le]
    rintro x (⟨c, rfl⟩ | rfl | rfl)
    · exact ⟨MvPolynomial.C c, by simp [NodeLocalized.modularEval]⟩
    · exact ⟨MvPolynomial.X 0, by simp [NodeLocalized.modularEval]⟩
    · exact ⟨MvPolynomial.X 1, by simp [NodeLocalized.modularEval]⟩
  · rintro x ⟨p, rfl⟩
    induction p using MvPolynomial.induction_on with
    | C c =>
      rw [NodeLocalized.modularEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
      exact CharPReduction.constSeries_mem_modularRing N A c
    | add p r hp hr => rw [map_add]; exact add_mem hp hr
    | mul_X p i hp =>
      rw [map_mul]
      refine mul_mem hp ?_
      rw [NodeLocalized.modularEval, MvPolynomial.eval₂Hom_X']
      fin_cases i
      · exact CharPReduction.jqModC_mem_modularRing N A
      · exact CharPReduction.jqNModC_mem_modularRing N A

end S_ModularCurve_modularRing_eq_range_modularEval
end P2MW
export P2MW.S_ModularCurve_modularRing_eq_range_modularEval (solution)
