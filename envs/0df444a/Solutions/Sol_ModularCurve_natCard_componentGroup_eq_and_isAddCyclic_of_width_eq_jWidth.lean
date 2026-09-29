-- Prove2me | solution 1 for ModularCurve.natCard_componentGroup_eq_and_isAddCyclic_of_width_eq_jWidth
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/7d76d2b4-5785-5a3b-9258-9d415726266a

import Mathlib
import Definitions.Def_ModularCurve_ComponentGroupKirchhoff
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_JWidth

import Theorems.Thm_ModularCurve_natCard_componentGroup_eq_eisensteinNumerator
import Theorems.Thm_ModularCurve_isAddCyclic_componentGroup_of_widths
import Theorems.Thm_ModularCurve_eisensteinNumerator_coprime
import Theorems.Thm_ModularCurve_sum_inv_jWidth_eq_of_ssJSet
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_natCard_componentGroup_eq_and_isAddCyclic_of_width_eq_jWidth
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

open ModularCurve Finset

theorem solution (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K q] [DecidableEq K]
    (S : Finset K) (hS : ∀ j, j ∈ S ↔ j ∈ ssJSet q K)
    {ι : Type*} [Fintype ι] (e : ι → ℕ) (σ : ι ≃ ↥S)
    (he : ∀ x, e x = jWidth ((σ x : ↥S) : K)) :
    Nat.card (componentGroup e) = eisensteinNumerator q ∧
      IsAddCyclic (componentGroup e) ∧ (eisensteinNumerator q).Coprime q := by
  classical

  have he' : ∀ x, e x = 1 ∨ e x = 2 ∨ e x = 3 := fun x => by
    rw [he x]; exact jWidth_eq_one_or _

  have h2j : ∀ j : K, jWidth j = 2 → j = 1728 := fun j hj => by
    unfold jWidth at hj; split_ifs at hj with h0 h1 <;> first | exact h1 | omega
  have h3j : ∀ j : K, jWidth j = 3 → j = 0 := fun j hj => by
    unfold jWidth at hj; split_ifs at hj with h0 h1 <;> first | exact h0 | omega
  have h2 : ({x | e x = 2} : Set ι).Subsingleton := fun x hx y hy => by
    have hx' : ((σ x : ↥S) : K) = 1728 := h2j _ ((he x).symm.trans hx)
    have hy' : ((σ y : ↥S) : K) = 1728 := h2j _ ((he y).symm.trans hy)
    exact σ.injective (Subtype.ext (hx'.trans hy'.symm))
  have h3 : ({x | e x = 3} : Set ι).Subsingleton := fun x hx y hy => by
    have hx' : ((σ x : ↥S) : K) = 0 := h3j _ ((he x).symm.trans hx)
    have hy' : ((σ y : ↥S) : K) = 0 := h3j _ ((he y).symm.trans hy)
    exact σ.injective (Subtype.ext (hx'.trans hy'.symm))

  have hmass : ∑ x, ((e x : ℚ))⁻¹ = ((q : ℚ) - 1) / 12 := by
    have h1 : ∑ x, ((e x : ℚ))⁻¹ = ∑ s : ↥S, ((jWidth (s : K) : ℚ))⁻¹ :=
      Fintype.sum_equiv σ _ _ (fun x => by rw [he x])
    rw [h1, ← sum_inv_jWidth_eq_of_ssJSet q hq K S hS]
    exact Finset.sum_coe_sort S (fun j => ((jWidth j : ℚ))⁻¹)
  have hq1 : 1 < q := by omega
  exact ⟨natCard_componentGroup_eq_eisensteinNumerator e q hq1 he' h2 h3 hmass,
    isAddCyclic_componentGroup_of_widths e he' h2 h3,
    eisensteinNumerator_coprime q (by omega)⟩

end S_ModularCurve_natCard_componentGroup_eq_and_isAddCyclic_of_width_eq_jWidth
end P2MW
export P2MW.S_ModularCurve_natCard_componentGroup_eq_and_isAddCyclic_of_width_eq_jWidth (solution)
