-- Prove2me | solution 1 for ModularCurve.IsLevelPStructure.relabel_variableChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/88e74c1b-e295-5c7a-9815-1939b2a423ae

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelRelabelling
import Theorems.Thm_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi
import Theorems.Thm_ModularCurve_indepElt_eq_zero_iff_mem_zmultiples
import Theorems.Thm_WeierstrassCurve_exists_addEquiv_point_variableChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IsLevelPStructure_relabel_variableChange
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero"

set_option autoImplicit false

universe u

open scoped Classical

namespace KatzRelabelFieldVC

open ModularCurve ModularCurve.LevelRelabelling WeierstrassCurve WeierstrassCurve.Affine

variable {F : Type u} [Field F]

theorem toPoint_of_nonsingular (W : WeierstrassCurve F) {x y : F} (h : W.toAffine.Nonsingular x y) :
    toPoint W x y = Point.some x y h := by
  unfold toPoint
  rw [dif_pos h]

theorem relabel_eq (W : WeierstrassCurve F) (g : Matrix (Fin 2) (Fin 2) ℤ) (D : LevelPData F) :
    LevelPData.relabel W g D =
      ⟨(ofPoint W (g 0 0 • toPoint W D.xP D.yP + g 1 0 • toPoint W D.xQ D.yQ)).1,
       (ofPoint W (g 0 0 • toPoint W D.xP D.yP + g 1 0 • toPoint W D.xQ D.yQ)).2,
       (ofPoint W (g 0 1 • toPoint W D.xP D.yP + g 1 1 • toPoint W D.xQ D.yQ)).1,
       (ofPoint W (g 0 1 • toPoint W D.xP D.yP + g 1 1 • toPoint W D.xQ D.yQ)).2⟩ := rfl

section Dict

set_option linter.unusedSectionVars false

variable (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ)
  (W : WeierstrassCurve F) (hΔ : IsUnit W.Δ) (D : LevelPData F) (hD : IsLevelPStructure W ℓ D)

include hΔ hD in
theorem nonsingular_P : W.toAffine.Nonsingular D.xP D.yP :=
  (equation_iff_nonsingular_of_Δ_ne_zero hΔ.ne_zero).1 hD.equation_P

include hΔ hD in
theorem nonsingular_Q : W.toAffine.Nonsingular D.xQ D.yQ :=
  (equation_iff_nonsingular_of_Δ_ne_zero hΔ.ne_zero).1 hD.equation_Q

include hℓ3 in
theorem ell_ne_two : ℓ ≠ 2 := by omega

include hℓ3 in
theorem odd_ell : Odd ℓ := (Fact.out : ℓ.Prime).odd_of_ne_two (ell_ne_two ℓ hℓ3)

include hℓ3 hΔ in
theorem ell_smul_eq_zero {x y : F} (h : W.toAffine.Nonsingular x y) (hx : (W.preΨ ℓ).eval x = 0) :
    (ℓ : ℤ) • Point.some x y h = 0 := by
  haveI : W.IsElliptic := ⟨hΔ⟩
  rw [natCast_zsmul]
  rw [WeierstrassCurve.preΨ_ofNat] at hx
  exact (Point.nsmul_some_eq_zero_iff_eval_prePsi W (odd_ell ℓ hℓ3) h).2 hx

include hℓ3 hΔ in
theorem exists_smul_smul_eq {x y : F} (h : W.toAffine.Nonsingular x y) (hx : (W.preΨ ℓ).eval x = 0)
    {c : ℤ} (hc : ¬ (ℓ : ℤ) ∣ c) : ∃ v : ℤ, v • (c • Point.some x y h) = Point.some x y h := by
  have hcop : IsCoprime (ℓ : ℤ) c := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have h1 : Nat.Coprime ℓ c.natAbs := by
      rw [Nat.Prime.coprime_iff_not_dvd (Fact.out : ℓ.Prime)]
      intro hd
      exact hc (Int.natCast_dvd.2 hd)
    simpa [Int.gcd] using h1
  obtain ⟨a, b, hab⟩ := hcop
  refine ⟨b, ?_⟩
  have h0 := ell_smul_eq_zero ℓ hℓ3 W hΔ h hx
  calc b • (c • Point.some x y h)
      = (a * (ℓ : ℤ) + b * c) • Point.some x y h - a • ((ℓ : ℤ) • Point.some x y h) := by
        rw [add_smul, mul_smul, mul_smul]; abel
    _ = Point.some x y h := by rw [hab, h0, smul_zero, sub_zero, one_smul]

include hℓ3 hΔ hD in
theorem dvd_and_dvd_of_smul_add_smul_eq_zero (a c : ℤ)
    (h : a • Point.some D.xP D.yP (nonsingular_P ℓ W hΔ D hD) +
        c • Point.some D.xQ D.yQ (nonsingular_Q ℓ W hΔ D hD) = 0) :
    (ℓ : ℤ) ∣ a ∧ (ℓ : ℤ) ∣ c := by
  set P := Point.some D.xP D.yP (nonsingular_P ℓ W hΔ D hD) with hP
  set Q := Point.some D.xQ D.yQ (nonsingular_Q ℓ W hΔ D hD) with hQ
  have hℓ2 := ell_ne_two ℓ hℓ3
  have hPℓ : (ℓ : ℤ) • P = 0 := ell_smul_eq_zero ℓ hℓ3 W hΔ _ hD.preΨ_P
  have hQℓ : (ℓ : ℤ) • Q = 0 := ell_smul_eq_zero ℓ hℓ3 W hΔ _ hD.preΨ_Q
  have hQP : Q ∉ AddSubgroup.zmultiples P := by
    intro hmem
    have hz : ModularCurve.indepElt W ℓ D.xP D.xQ = 0 :=
      (ModularCurve.indepElt_eq_zero_iff_mem_zmultiples hℓ2 (nonsingular_P ℓ W hΔ D hD)
        (nonsingular_Q ℓ W hΔ D hD) (by
          have := hPℓ; rwa [natCast_zsmul] at this)).2 hmem
    exact hD.isUnit_indepElt_PQ.ne_zero hz
  have hcQ : c • Q = (-a) • P := by
    rw [neg_smul, eq_neg_iff_add_eq_zero, add_comm, h]
  have hc : (ℓ : ℤ) ∣ c := by
    by_contra hc
    obtain ⟨v, hv⟩ := exists_smul_smul_eq ℓ hℓ3 W hΔ (nonsingular_Q ℓ W hΔ D hD) hD.preΨ_Q hc
    apply hQP
    rw [← hQ] at hv
    rw [← hv, hcQ, smul_smul]
    exact ⟨v * -a, rfl⟩
  refine ⟨?_, hc⟩
  obtain ⟨k, rfl⟩ := hc
  have haP : a • P = 0 := by
    have : ((ℓ : ℤ) * k) • Q = 0 := by rw [mul_comm, mul_smul, hQℓ, smul_zero]
    rwa [this, add_zero] at h
  by_contra ha
  obtain ⟨v, hv⟩ := exists_smul_smul_eq ℓ hℓ3 W hΔ (nonsingular_P ℓ W hΔ D hD) hD.preΨ_P ha
  rw [← hP, haP, smul_zero] at hv
  exact Point.some_ne_zero _ hv.symm

theorem not_dvd_col (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : IsUnit (g.map (Int.castRingHom (ZMod ℓ))).det)
    (j : Fin 2) : ¬ ((ℓ : ℤ) ∣ g 0 j ∧ (ℓ : ℤ) ∣ g 1 j) := by
  rintro ⟨h0, h1⟩
  have e0 : (g.map (Int.castRingHom (ZMod ℓ))) 0 j = 0 := by
    simpa [Matrix.map_apply] using (ZMod.intCast_zmod_eq_zero_iff_dvd (g 0 j) ℓ).2 h0
  have e1 : (g.map (Int.castRingHom (ZMod ℓ))) 1 j = 0 := by
    simpa [Matrix.map_apply] using (ZMod.intCast_zmod_eq_zero_iff_dvd (g 1 j) ℓ).2 h1
  have hdet : (g.map (Int.castRingHom (ZMod ℓ))).det = 0 := by
    rw [Matrix.det_fin_two]
    fin_cases j
    · simp only [Fin.zero_eta] at e0 e1
      rw [e0, e1]; ring
    · simp only [Fin.mk_one] at e0 e1
      rw [e0, e1]; ring
  rw [hdet] at hg
  exact not_isUnit_zero hg

include hℓ3 hΔ hD in
theorem col_ne_zero (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : IsUnit (g.map (Int.castRingHom (ZMod ℓ))).det)
    (j : Fin 2) :
    g 0 j • Point.some D.xP D.yP (nonsingular_P ℓ W hΔ D hD) +
        g 1 j • Point.some D.xQ D.yQ (nonsingular_Q ℓ W hΔ D hD) ≠ 0 :=
  fun h => not_dvd_col ℓ g hg j (dvd_and_dvd_of_smul_add_smul_eq_zero ℓ hℓ3 W hΔ D hD _ _ h)

end Dict

theorem relabel_variableChange (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ)
    (W : WeierstrassCurve F) (hΔ : IsUnit W.Δ) (D : LevelPData F) (hD : IsLevelPStructure W ℓ D)
    (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : IsUnit (g.map (Int.castRingHom (ZMod ℓ))).det)
    (C : VariableChange F) :
    LevelPData.relabel (C • W) g (D.variableChange C) = (LevelPData.relabel W g D).variableChange C := by
  obtain ⟨e, he⟩ := WeierstrassCurve.exists_addEquiv_point_variableChange W C
  have hP := nonsingular_P ℓ W hΔ D hD
  have hQ := nonsingular_Q ℓ W hΔ D hD
  set P := Point.some D.xP D.yP hP with hPdef
  set Q := Point.some D.xQ D.yQ hQ with hQdef

  have key : ∀ (x y : F) (h : W.toAffine.Nonsingular x y),
      toPoint (C • W) (((C.u⁻¹ : Fˣ) : F) ^ 2 * (x - C.r))
        (((C.u⁻¹ : Fˣ) : F) ^ 3 * (y - C.s * (x - C.r) - C.t)) = e (Point.some x y h) := by
    intro x y h
    obtain ⟨h', he'⟩ := he x y h
    have hy : ((C.u⁻¹ : Fˣ) : F) ^ 3 * (y - C.s * (x - C.r) - C.t) =
        ((C.u⁻¹ : Fˣ) : F) ^ 3 * (y - C.s * x + (C.s * C.r - C.t)) := by ring
    rw [hy, he', toPoint_of_nonsingular]

  have keyOf : ∀ (S : W.toAffine.Point), S ≠ 0 →
      ofPoint (C • W) (e S) = (((C.u⁻¹ : Fˣ) : F) ^ 2 * ((ofPoint W S).1 - C.r),
        ((C.u⁻¹ : Fˣ) : F) ^ 3 * ((ofPoint W S).2 - C.s * ((ofPoint W S).1 - C.r) - C.t)) := by
    intro S hS
    rcases S with _ | ⟨x, y, h⟩
    · exact (hS rfl).elim
    · obtain ⟨h', he'⟩ := he x y h
      rw [he']
      show ((((C.u⁻¹ : Fˣ) : F) ^ 2 * (x - C.r)), (((C.u⁻¹ : Fˣ) : F) ^ 3 * (y - C.s * x + (C.s * C.r - C.t)))) =
        (((C.u⁻¹ : Fˣ) : F) ^ 2 * (x - C.r), ((C.u⁻¹ : Fˣ) : F) ^ 3 * (y - C.s * (x - C.r) - C.t))
      ext
      · rfl
      · show ((C.u⁻¹ : Fˣ) : F) ^ 3 * (y - C.s * x + (C.s * C.r - C.t)) =
          ((C.u⁻¹ : Fˣ) : F) ^ 3 * (y - C.s * (x - C.r) - C.t)
        ring
  have h1 : g 0 0 • P + g 1 0 • Q ≠ 0 := col_ne_zero ℓ hℓ3 W hΔ D hD g hg 0
  have h2 : g 0 1 • P + g 1 1 • Q ≠ 0 := col_ne_zero ℓ hℓ3 W hΔ D hD g hg 1
  rw [relabel_eq (C • W) g, LevelPData.variableChange_xP, LevelPData.variableChange_yP,
    LevelPData.variableChange_xQ, LevelPData.variableChange_yQ, key D.xP D.yP hP, key D.xQ D.yQ hQ,
    ← hPdef, ← hQdef, ← map_zsmul, ← map_zsmul, ← map_zsmul, ← map_zsmul, ← map_add, ← map_add,
    keyOf _ h1, keyOf _ h2, relabel_eq W g D, toPoint_of_nonsingular W hP, toPoint_of_nonsingular W hQ,
    ← hPdef, ← hQdef]
  rfl

end KatzRelabelFieldVC

open KatzRelabelFieldVC in
theorem solution
    {F : Type u} [Field F] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ)
    (W : WeierstrassCurve F) (hΔ : IsUnit W.Δ) (D : ModularCurve.LevelPData F)
    (hD : ModularCurve.IsLevelPStructure W ℓ D)
    (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : IsUnit (g.map (Int.castRingHom (ZMod ℓ))).det)
    (C : WeierstrassCurve.VariableChange F) :
    ModularCurve.LevelRelabelling.LevelPData.relabel (C • W) g (D.variableChange C) =
      (ModularCurve.LevelRelabelling.LevelPData.relabel W g D).variableChange C :=
  relabel_variableChange ℓ hℓ3 W hΔ D hD g hg C

end S_ModularCurve_IsLevelPStructure_relabel_variableChange
end P2MW
export P2MW.S_ModularCurve_IsLevelPStructure_relabel_variableChange (solution)
