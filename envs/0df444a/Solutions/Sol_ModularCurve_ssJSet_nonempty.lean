-- Prove2me | solution 1 for ModularCurve.ssJSet_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/01849533-c7cb-5096-96f7-a97c882ea53a

import Mathlib
import Definitions.Def_ModularCurve_SupersingularModuli
import Theorems.Thm_ModularCurve_zero_mem_ssJSet_of_lt_five
import Theorems.Thm_ModularCurve_ssJSet_finite
import Theorems.Thm_ModularCurve_card_eq_of_ssJSet
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ssJSet_nonempty
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

open ModularCurve

theorem solution {q : ℕ} [Fact q.Prime] {k : Type*} [Field k] [DecidableEq k]
    [IsAlgClosed k] [CharP k q] : (ssJSet q k).Nonempty := by
  by_cases hq : q < 5
  · exact ⟨0, ModularCurve.zero_mem_ssJSet_of_lt_five hq⟩
  have hq5 : 5 ≤ q := not_lt.mp hq
  have hfin := ModularCurve.ssJSet_finite q k
  have hS : ∀ j, j ∈ hfin.toFinset ↔ j ∈ ssJSet q k := fun j => hfin.mem_toFinset
  have hcard := ModularCurve.card_eq_of_ssJSet q hq5 k hfin.toFinset hS

  have hpos : 0 < hfin.toFinset.card := by
    have hp : q.Prime := Fact.out
    rw [hcard]
    by_cases h12 : 12 ≤ q
    · exact Nat.add_pos_left (Nat.add_pos_left (Nat.div_pos h12 (by norm_num)) _) _
    · have h12' : q < 12 := not_le.mp h12
      interval_cases q <;> first | decide | exact absurd hp (by decide)
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hpos
  exact ⟨j, (hS j).mp hj⟩

end S_ModularCurve_ssJSet_nonempty
end P2MW
export P2MW.S_ModularCurve_ssJSet_nonempty (solution)
