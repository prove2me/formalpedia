-- Prove2me | solution 1 for ModularCurve.ModularPolynomialData.separable_map_eval2_of_not_isIntegral_of_isAlgClosed_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/e20f213c-9439-5eaf-a5d0-f8c1c49db1fe

import Mathlib
import Definitions.Def_ModularCurve_X0
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Definitions.Def_ModularCurve_FibrePoly
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_VeluOrderTwo
import Theorems.Thm_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_veluQuotient2_j
import Theorems.Thm_WeierstrassCurve_eq_of_veluQuotient2_j_eq_of_not_isIntegral_j
import Theorems.Thm_WeierstrassCurve_veluQuotient2_Delta_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ModularPolynomialData_separable_map_eval2_of_not_isIntegral_of_isAlgClosed_two
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.jqNModC_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.veluX_empty"

open Polynomial ModularCurve

section Main
set_option autoImplicit false
open Polynomial ModularCurve WeierstrassCurve WeierstrassCurve.Affine

theorem solution
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F]
    (data : ModularPolynomialData 2) (jv : F) (hjv : ¬ _root_.IsIntegral ℤ jv) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom F) jv)).Separable := by
  classical

  let W : WeierstrassCurve F := WeierstrassCurve.ofJ jv
  have hjW : W.j = jv := WeierstrassCurve.ofJ_j jv
  have hjW' : ¬ _root_.IsIntegral ℤ W.j := by rw [hjW]; exact hjv
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have hΔW : W.Δ ≠ 0 := W.isUnit_Δ.ne_zero

  have ha : W.twoTorsionPolynomial.a ≠ 0 := by
    show (4 : F) ≠ 0
    norm_num
  have hsplit : (Polynomial.map (RingHom.id F) W.twoTorsionPolynomial.toPoly).Splits :=
    IsAlgClosed.splits _
  obtain ⟨e₀, e₁, e₂, h3⟩ := (Cubic.splits_iff_roots_eq_three ha).mp hsplit
  have hdiscr : W.twoTorsionPolynomial.discr ≠ 0 :=
    W.twoTorsionPolynomial_discr_ne_zero (isUnit_iff_ne_zero.mpr h2) W.isUnit_Δ
  have hnodup : ({e₀, e₁, e₂} : Multiset F).Nodup := by
    rw [← h3]
    exact (Cubic.discr_ne_zero_iff_roots_nodup ha hsplit).mp hdiscr
  have h01 : e₀ ≠ e₁ := by
    intro h; subst h; simp at hnodup
  have h02 : e₀ ≠ e₂ := by
    intro h; subst h; simp at hnodup
  have h12 : e₁ ≠ e₂ := by
    intro h; subst h; simp at hnodup

  have hne0 : W.twoTorsionPolynomial.toPoly ≠ 0 := Cubic.ne_zero_of_a_ne_zero ha
  have hroot : ∀ e ∈ ({e₀, e₁, e₂} : Multiset F),
      4 * e ^ 3 + W.b₂ * e ^ 2 + 2 * W.b₄ * e + W.b₆ = 0 := by
    intro e he
    have he' : e ∈ W.twoTorsionPolynomial.roots := by
      have : (Cubic.map (RingHom.id F) W.twoTorsionPolynomial).roots = W.twoTorsionPolynomial.roots := by
        rw [Cubic.map_roots, Polynomial.map_id]; rfl
      rw [← this, h3]; exact he
    have := (Cubic.mem_roots_iff hne0 e).mp he'
    simpa [WeierstrassCurve.twoTorsionPolynomial] using this
  let yof : F → F := fun e => -(W.a₁ * e + W.a₃) / 2
  have heq : ∀ e ∈ ({e₀, e₁, e₂} : Multiset F), W.toAffine.Equation e (yof e) := by
    intro e he
    have hr := hroot e he
    rw [WeierstrassCurve.Affine.equation_iff]
    simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆] at hr
    show (-(W.a₁ * e + W.a₃) / 2) ^ 2 + W.a₁ * e * (-(W.a₁ * e + W.a₃) / 2) + W.a₃ * (-(W.a₁ * e + W.a₃) / 2) =
      e ^ 3 + W.a₂ * e ^ 2 + W.a₄ * e + W.a₆
    field_simp
    linear_combination (-1 : F) * hr
  have hgy : ∀ e : F, W.veluGy e (yof e) = 0 := by
    intro e
    show -(2 * (-(W.a₁ * e + W.a₃) / 2) + W.a₁ * e + W.a₃) = 0
    field_simp
    ring

  let P : Fin 3 → F × F := ![(e₀, yof e₀), (e₁, yof e₁), (e₂, yof e₂)]
  have hPinj1 : ∀ i k, (P i).1 = (P k).1 → i = k := by
    intro i k h
    fin_cases i <;> fin_cases k <;> simp [P] at h ⊢ <;>
      first | exact absurd h h01 | exact absurd h h02 | exact absurd h h12 |
        exact absurd h.symm h01 | exact absurd h.symm h02 | exact absurd h.symm h12
  have hPinj : Function.Injective P := fun i k h => hPinj1 i k (congrArg Prod.fst h)
  have hPeq : ∀ i, W.toAffine.Equation (P i).1 (P i).2 := by
    intro i; fin_cases i <;> exact heq _ (by simp [P])
  have hPgy : ∀ i, W.veluGy (P i).1 (P i).2 = 0 := by
    intro i; fin_cases i <;> exact hgy _
  have hΔ' : ∀ i, (W.veluQuotient2 (P i).1 (P i).2).Δ ≠ 0 := fun i =>
    WeierstrassCurve.veluQuotient2_Delta_ne_zero hΔW (hPeq i) (hPgy i)

  show (fibrePoly data.Φ jv).Separable
  rw [← hjW, ModularCurve.ModularPolynomialData.fibrePoly_j_eq_prod_veluQuotient2_j h2 data W
    (by simp) P hPinj hPeq hPgy hΔ']

  rw [Polynomial.separable_prod_X_sub_C_iff']
  intro i _ k _ hik
  exact hPinj1 i k (WeierstrassCurve.eq_of_veluQuotient2_j_eq_of_not_isIntegral_j W hjW'
    (hPeq i) (hPgy i) (hPeq k) (hPgy k) (hΔ' i) (hΔ' k) hik)

end Main

end S_ModularCurve_ModularPolynomialData_separable_map_eval2_of_not_isIntegral_of_isAlgClosed_two
end P2MW
export P2MW.S_ModularCurve_ModularPolynomialData_separable_map_eval2_of_not_isIntegral_of_isAlgClosed_two (solution)
