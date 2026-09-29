-- Prove2me | solution 1 for ModularCurve.JZero.isPrincipal_sub_of_isRepOf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/fca50f0f-f98a-5993-8ed8-2717366b7a88

import Definitions.Def_ModularCurve_JZeroHeightForm
import Mathlib.Algebra.Ring.Action.Submonoid
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZero_isPrincipal_sub_of_isRepOf

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open AlgebraicCurve ModularCurve

open ModularCurve.JZero in
theorem solution (N : ℕ) [NeZero N]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K] {n : ℕ}
    {c : ↥(JZero N ^+ ↥K.fixingSubgroup)}
    {D D' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)}
    (h : JZero.IsRepOf N K n c D) (h' : JZero.IsRepOf N K n c D') :
    Divisor.IsPrincipal (D' - D) := by
  obtain ⟨E, -, hshape, -, hcE⟩ := h
  obtain ⟨E', -, hshape', -, hcE'⟩ := h'
  have hsub : D' - D = ((E' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
      - (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))) := by
    rw [← hshape, ← hshape']; abel
  have hq : Pic0.mk E = Pic0.mk E' := hcE.trans hcE'.symm
  have hmem : -E + E' ∈ (Divisor.principal (K := AlgebraicClosure ℚ)
      (F := ↥(modularFunctionFieldBar N))).addSubgroupOf Divisor.degZero := QuotientAddGroup.eq.mp hq
  rw [AddSubgroup.mem_addSubgroupOf] at hmem
  rw [hsub, sub_eq_neg_add]
  exact hmem

end S_ModularCurve_JZero_isPrincipal_sub_of_isRepOf
end P2MW
export P2MW.S_ModularCurve_JZero_isPrincipal_sub_of_isRepOf (solution)
