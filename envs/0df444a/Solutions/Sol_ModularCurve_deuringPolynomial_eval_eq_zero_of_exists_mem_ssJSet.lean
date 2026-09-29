-- Prove2me | solution 1 for ModularCurve.deuringPolynomial_eval_eq_zero_of_exists_mem_ssJSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/750ba9f4-4a6e-57ec-b2c4-5b9ce9cbba35

import Mathlib
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Definitions.Def_Polynomial_DeuringPolynomial
import Definitions.Def_ModularCurve_LegendreJ
import Theorems.Thm_ModularCurve_ssJSet_eq_ssJSetHasse
import Theorems.Thm_WeierstrassCurve_hasseInvariant_legendreCurve
import Theorems.Thm_WeierstrassCurve_isElliptic_legendreCurve_iff
import Theorems.Thm_WeierstrassCurve_j_legendreCurve
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_deuringPolynomial_eval_eq_zero_of_exists_mem_ssJSet
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

p2m_open "Polynomial ModularCurve P2MW.S_ModularCurve_deuringPolynomial_eval_eq_zero_of_exists_mem_ssJSet.ModularCurve WeierstrassCurve"

namespace ModularCurve
p2m_export "ModularCurve" "ssJSet legendreJ ssJSet_eq_ssJSetHasse"
namespace L11
p2m_open "ModularCurve"

theorem char_facts {q : ℕ} [Fact q.Prime] (hq : 5 ≤ q) (k : Type*) [Field k] [CharP k q] :
    (2 : k) ≠ 0 ∧ (4 : k) ≠ 0 ∧ (16 : k) ≠ 0 := by
  have hp : q.Prime := Fact.out
  have hcast : ∀ a : ℕ, 0 < a → a < q → (a : k) ≠ 0 := fun a ha haq h =>
    absurd (Nat.le_of_dvd ha ((CharP.cast_eq_zero_iff k q a).mp h)) (not_le.mpr haq)
  have h2 : (2 : k) ≠ 0 := by exact_mod_cast hcast 2 (by norm_num) (by omega)
  refine ⟨h2, ?_, ?_⟩
  · rw [show (4 : k) = 2 ^ 2 by norm_num]; exact pow_ne_zero _ h2
  · rw [show (16 : k) = 2 ^ 4 by norm_num]; exact pow_ne_zero _ h2

theorem main_a {q : ℕ} [Fact q.Prime] (hq : 5 ≤ q)
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    (l : k) (hl0 : l ≠ 0) (hl1 : 16 * l ≠ 1)
    (hss : ∃ a ∈ ssJSet q k, a * ((16 * l) ^ 2 * (16 * l - 1) ^ 2) = 256 * ((16 * l) ^ 2 - 16 * l + 1) ^ 3) :
    ((Polynomial.deuringPolynomial q).map (Int.castRingHom k)).eval (16 * l) = 0 := by
  have hp : q.Prime := Fact.out
  obtain ⟨h2, h4, h16⟩ := char_facts hq k
  obtain ⟨a, ha, hrel⟩ := hss
  set t : k := 16 * l with ht
  have ht0 : t ≠ 0 := mul_ne_zero h16 hl0
  have ht1 : t ≠ 1 := hl1
  have hden : t ^ 2 * (t - 1) ^ 2 ≠ 0 := mul_ne_zero (pow_ne_zero _ ht0) (pow_ne_zero _ (sub_ne_zero.mpr ht1))
  have haJ : a = legendreJ t := by
    rw [legendreJ, eq_div_iff hden]
    linear_combination hrel
  haveI hE : (legendreCurve t).IsElliptic := (isElliptic_legendreCurve_iff t h2).mpr ⟨ht0, ht1⟩
  rw [ssJSet_eq_ssJSetHasse q (by omega) k] at ha
  have hH : (legendreCurve t).hasseInvariant q = 0 := ha (legendreCurve t) (by rw [j_legendreCurve t, haJ])
  rw [hasseInvariant_legendreCurve (hp.odd_of_ne_two (by omega)) t] at hH
  rcases mul_eq_zero.mp hH with h | h
  · exact absurd h (pow_ne_zero _ (neg_ne_zero.mpr h4))
  · exact h

end ModularCurve.L11

theorem solution
    {q : ℕ} [Fact q.Prime] (hq : 5 ≤ q)
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    (l : k) (hl0 : l ≠ 0) (hl1 : 16 * l ≠ 1)
    (hss : ∃ a ∈ ModularCurve.ssJSet q k, a * ((16 * l) ^ 2 * (16 * l - 1) ^ 2) = 256 * ((16 * l) ^ 2 - 16 * l + 1) ^ 3) :
    ((Polynomial.deuringPolynomial q).map (Int.castRingHom k)).eval (16 * l) = 0 :=
  ModularCurve.L11.main_a hq l hl0 hl1 hss

end S_ModularCurve_deuringPolynomial_eval_eq_zero_of_exists_mem_ssJSet
end P2MW
export P2MW.S_ModularCurve_deuringPolynomial_eval_eq_zero_of_exists_mem_ssJSet (solution)
