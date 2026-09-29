-- Prove2me | solution 1 for ModularCurve.torsion_basis_of_map_eq_variableChange_tateBase_cuspData_of_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/c96c07d3-69af-5960-8260-ca72615f965c

import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow

import Theorems.Thm_ModularCurve_isLevelPStructure_tateBase_cuspData_neg_of_dvd
import Theorems.Thm_ModularCurve_IsLevelPStructure_variableChange
import Theorems.Thm_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi
import Theorems.Thm_ModularCurve_indepElt_eq_zero_iff_mem_zmultiples
import Theorems.Thm_ModularCurve_nonToricPoint_inv_tsub
import Theorems.Thm_ModularCurve_toricPoint_add_nonToricPoint_of_charZero
import Theorems.Thm_ModularCurve_toricPoint_add_toricPoint_tateBase_of_charZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_torsion_basis_of_map_eq_variableChange_tateBase_cuspData_of_mul_eq
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero TateCurve.tateTorsionPoint_zero_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups

namespace DTTAux

p2m_open "ModularCurve WeierstrassCurve~cusp"
open scoped Classical

theorem isLevelPStructure_of_map {K F : Type*} [Field K] [Field F] (φ : K →+* F)
    {W : WeierstrassCurve K} {p : ℕ} {D : ModularCurve.LevelPData K}
    (h : ModularCurve.IsLevelPStructure (W.map φ) p (D.map φ)) : ModularCurve.IsLevelPStructure W p D := by
  have hinj : Function.Injective φ := φ.injective
  have heq : ∀ {x y : K}, (W.map φ).toAffine.Equation (φ x) (φ y) → W.toAffine.Equation x y := by
    intro x y hxy
    rw [WeierstrassCurve.Affine.equation_iff] at hxy ⊢
    apply hinj
    simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄,
      WeierstrassCurve.map_a₆] at hxy
    simpa only [map_add, map_mul, map_pow] using hxy
  have hpsi : ∀ {x : K}, ((W.map φ).preΨ p).eval (φ x) = 0 → (W.preΨ p).eval x = 0 := by
    intro x hx
    rw [WeierstrassCurve.map_preΨ, Polynomial.eval_map, Polynomial.eval₂_at_apply] at hx
    exact hinj (by rw [hx, map_zero])
  have hind : ∀ {x y : K}, IsUnit (ModularCurve.indepElt (W.map φ) p (φ x) (φ y)) → IsUnit (ModularCurve.indepElt W p x y) := by
    intro x y hu
    rw [ModularCurve.indepElt_map] at hu
    rw [isUnit_iff_ne_zero] at hu ⊢
    intro h0; exact hu (by rw [h0, map_zero])
  exact ⟨heq h.equation_P, heq h.equation_Q, hpsi h.preΨ_P, hpsi h.preΨ_Q, hind h.isUnit_indepElt_PQ,
    hind h.isUnit_indepElt_QP⟩

theorem dvd_of_comb_eq_zero {F : Type*} [Field F] {W : WeierstrassCurve F} {ℓ : ℕ} [Fact ℓ.Prime]
    {P Q : W.toAffine.Point}
    (hP : ℓ • P = 0) (hQ : ℓ • Q = 0) (hP0 : P ≠ 0) (hQP : Q ∉ AddSubgroup.zmultiples P)
    (a b : ℤ) (h : a • P + b • Q = 0) : (ℓ : ℤ) ∣ a ∧ (ℓ : ℤ) ∣ b := by
  have hp : ℓ.Prime := Fact.out
  haveI : NeZero ℓ := ⟨hp.ne_zero⟩
  have hordP : addOrderOf P = ℓ := addOrderOf_eq_prime_iff.mpr ⟨hP, hP0⟩
  have hkill : ∀ (R : W.toAffine.Point) (m : ℤ), ℓ • R = 0 → (ℓ : ℤ) ∣ m → m • R = 0 := by
    intro R m hR ⟨k, hk⟩
    rw [hk, mul_comm, ← smul_smul, natCast_zsmul, hR, smul_zero]
  have hb : (ℓ : ℤ) ∣ b := by
    by_contra hb
    have hb0 : ((b : ℤ) : ZMod ℓ) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    set c : ℤ := (((((b : ℤ) : ZMod ℓ)⁻¹).val : ℕ) : ℤ) with hc
    have hcb : (ℓ : ℤ) ∣ c * b - 1 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hc, Int.cast_natCast, ZMod.natCast_zmod_val, inv_mul_cancel₀ hb0, sub_self]
    apply hQP
    have e1 : Q = c • (b • Q) := by
      have := hkill Q (c * b - 1) hQ hcb
      rw [sub_smul, one_smul, sub_eq_zero] at this
      rw [smul_smul]; exact this.symm
    have e2 : b • Q = -(a • P) := eq_neg_of_add_eq_zero_right h
    rw [e1, e2, smul_neg, smul_smul, ← neg_smul]
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨-(c * a), rfl⟩
  have hbQ : b • Q = 0 := hkill Q b hQ hb
  have haP : a • P = 0 := by rwa [hbQ, add_zero] at h
  refine ⟨?_, hb⟩
  have := addOrderOf_dvd_iff_zsmul_eq_zero.mpr haP
  rwa [hordP] at this

theorem torsion_basis_of_isLevelPStructure {F : Type*} [Field F] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2)
    (W : WeierstrassCurve F) (hΔ : IsUnit W.Δ) (D : ModularCurve.LevelPData F) (hD : ModularCurve.IsLevelPStructure W ℓ D) :
    (ℓ : ℤ) • ModularCurve.LevelRelabelling.toPoint W D.xP D.yP = 0 ∧
    (ℓ : ℤ) • ModularCurve.LevelRelabelling.toPoint W D.xQ D.yQ = 0 ∧
    (∀ a b : ℕ, a < ℓ → b < ℓ →
      (a : ℤ) • ModularCurve.LevelRelabelling.toPoint W D.xP D.yP + (b : ℤ) • ModularCurve.LevelRelabelling.toPoint W D.xQ D.yQ = 0 →
      a = 0 ∧ b = 0) := by
  classical
  have hp : ℓ.Prime := Fact.out
  haveI : NeZero ℓ := ⟨hp.ne_zero⟩
  have hodd : Odd ℓ := hp.odd_of_ne_two hℓ2
  haveI : W.IsElliptic := ⟨hΔ⟩
  have nP := W.toAffine.equation_iff_nonsingular.mp hD.equation_P
  have nQ := W.toAffine.equation_iff_nonsingular.mp hD.equation_Q
  have tors : ∀ {x y : F} (nxy : W.toAffine.Nonsingular x y),
      (W.preΨ ℓ).eval x = 0 → ℓ • WeierstrassCurve.Affine.Point.some _ _ nxy = 0 := by
    intro x y nxy hx
    rw [WeierstrassCurve.preΨ_ofNat] at hx
    exact (WeierstrassCurve.Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi W hodd nxy).mpr hx
  have tP : ℓ • WeierstrassCurve.Affine.Point.some _ _ nP = 0 := tors nP hD.preΨ_P
  have tQ : ℓ • WeierstrassCurve.Affine.Point.some _ _ nQ = 0 := tors nQ hD.preΨ_Q
  have hP0 : WeierstrassCurve.Affine.Point.some _ _ nP ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero _
  have hQP : WeierstrassCurve.Affine.Point.some _ _ nQ ∉ AddSubgroup.zmultiples (WeierstrassCurve.Affine.Point.some _ _ nP) :=
    fun hmem => hD.isUnit_indepElt_PQ.ne_zero ((ModularCurve.indepElt_eq_zero_iff_mem_zmultiples hℓ2 nP nQ tP).mpr hmem)
  have htoP : ModularCurve.LevelRelabelling.toPoint W D.xP D.yP = WeierstrassCurve.Affine.Point.some _ _ nP := dif_pos nP
  have htoQ : ModularCurve.LevelRelabelling.toPoint W D.xQ D.yQ = WeierstrassCurve.Affine.Point.some _ _ nQ := dif_pos nQ
  rw [htoP, htoQ]
  refine ⟨by rw [natCast_zsmul]; exact tP, by rw [natCast_zsmul]; exact tQ, ?_⟩
  intro a b ha hb hab
  obtain ⟨h1, h2⟩ := dvd_of_comb_eq_zero tP tQ hP0 hQP a b hab
  exact ⟨Nat.eq_zero_of_dvd_of_lt (Int.natCast_dvd_natCast.mp h1) ha,
    Nat.eq_zero_of_dvd_of_lt (Int.natCast_dvd_natCast.mp h2) hb⟩

theorem equation_variableChange {R : Type*} [CommRing R] (W : WeierstrassCurve R) (C : WeierstrassCurve.VariableChange R)
    {x y : R} (h : W.toAffine.Equation x y) :
    (C • W).toAffine.Equation (((C.u⁻¹ : Rˣ) : R) ^ 2 * (x - C.r)) (((C.u⁻¹ : Rˣ) : R) ^ 3 * (y - C.s * (x - C.r) - C.t)) := by
  rw [WeierstrassCurve.Affine.equation_iff] at h ⊢
  simp only [WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂, WeierstrassCurve.variableChange_a₃,
    WeierstrassCurve.variableChange_a₄, WeierstrassCurve.variableChange_a₆]
  linear_combination (((C.u⁻¹ : Rˣ) : R)) ^ 6 * h

theorem negY_variableChange {R : Type*} [CommRing R] (W : WeierstrassCurve R) (C : WeierstrassCurve.VariableChange R) (x y : R) :
    (C • W).toAffine.negY (((C.u⁻¹ : Rˣ) : R) ^ 2 * (x - C.r)) (((C.u⁻¹ : Rˣ) : R) ^ 3 * (y - C.s * (x - C.r) - C.t))
        - ((C.u⁻¹ : Rˣ) : R) ^ 3 * (y - C.s * (x - C.r) - C.t)
      = ((C.u⁻¹ : Rˣ) : R) ^ 3 * (W.toAffine.negY x y - y) := by
  simp only [WeierstrassCurve.Affine.negY, WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₃]
  ring

theorem map_negY' {K F : Type*} [CommRing K] [CommRing F] (φ : K →+* F) (W : WeierstrassCurve K) (x y : K) :
    φ (W.toAffine.negY x y) = (W.map φ).toAffine.negY (φ x) (φ y) := by
  simp only [WeierstrassCurve.Affine.negY, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃, map_sub, map_neg, map_mul]

end DTTAux

open scoped Classical in
theorem solution
    (F : Type) [Field F] [CharZero F] (q : ℕ) [Fact q.Prime] (N : ℕ) [NeZero N] (m : ℕ) (hm : q * m = N)
    (ζ : Fˣ) (hζ : IsPrimitiveRoot (ζ : F) N)
    (C : WeierstrassCurve.VariableChange (LaurentSeries F))
    (T : Type) [Field T] (φ : T →+* LaurentSeries F)
    (W : WeierstrassCurve T) (D : ModularCurve.LevelPData T)
    (hW : W.map φ = C • ModularCurve.tateBase F N)
    (hD : D.map φ = (ModularCurve.cuspData F N ζ ![(m : ZMod N), 0] ![0, -(m : ZMod N)]).variableChange C) :
    W.toAffine.Equation D.xP D.yP ∧ W.toAffine.Equation D.xQ D.yQ ∧
    (q : ℤ) • ModularCurve.LevelRelabelling.toPoint W D.xP D.yP = 0 ∧
    (q : ℤ) • ModularCurve.LevelRelabelling.toPoint W D.xQ D.yQ = 0 ∧
    (∀ a b : ℕ, a < q → b < q →
      (a : ℤ) • ModularCurve.LevelRelabelling.toPoint W D.xP D.yP +
        (b : ℤ) • ModularCurve.LevelRelabelling.toPoint W D.xQ D.yQ = 0 → a = 0 ∧ b = 0) := by
  classical
  have hq : q.Prime := Fact.out
  haveI hNq : NeZero q := ⟨hq.ne_zero⟩
  have hinj : Function.Injective φ := φ.injective
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hmN : N / q = m := by rw [← hm, Nat.mul_div_cancel_left m hq.pos]
  have hmpos : 0 < m := Nat.pos_of_ne_zero (fun h0 => by rw [h0, mul_zero] at hm; exact (NeZero.ne N) hm.symm)

  have hΔ : IsUnit W.Δ := by
    rw [isUnit_iff_ne_zero]
    intro h0
    have hu' : IsUnit (C • ModularCurve.tateBase F N).Δ :=
      (ModularCurve.tateBase F N).isUnit_Δ_variableChange C (ModularCurve.isUnit_Δ_tateBase F N)
    rw [← hW, WeierstrassCurve.map_Δ, h0, map_zero] at hu'
    exact not_isUnit_zero hu'
  haveI : W.IsElliptic := ⟨hΔ⟩
  by_cases hq2 : q ≠ 2
  ·
    have hqF : IsUnit ((q : ℕ) : F) := isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hq.ne_zero)
    have hζm : IsPrimitiveRoot (((ζ : Fˣ) : F) ^ m) q := hζ.pow hNpos (by rw [mul_comm]; exact hm.symm)
    have hsum : ∑ i ∈ Finset.range q, (((ζ : Fˣ) : F) ^ (N / q)) ^ i = 0 := by
      rw [hmN]
      exact hζm.geom_sum_eq_zero hq.one_lt
    have hT := ModularCurve.isLevelPStructure_tateBase_cuspData_neg_of_dvd (R := F) (p := q) hq2 hqF N ⟨m, hm.symm⟩ ζ hsum
    rw [hmN] at hT
    have hDT : ModularCurve.IsLevelPStructure W q D :=
      DTTAux.isLevelPStructure_of_map φ (by rw [hW, hD]; exact hT.variableChange C)
    obtain ⟨tP, tQ, hind⟩ := DTTAux.torsion_basis_of_isLevelPStructure q hq2 W hΔ D hDT
    exact ⟨hDT.equation_P, hDT.equation_Q, tP, tQ, hind⟩
  ·
    push Not at hq2
    subst hq2
    have h2m : 2 * m = N := hm
    have hmltN : m < N := by omega
    have hNm : N - m = m := by omega
    have hζm2 : IsPrimitiveRoot (((ζ : Fˣ) : F) ^ m) 2 := hζ.pow hNpos (by rw [mul_comm]; exact h2m.symm)
    have hζ1 : ((ζ ^ m : Fˣ) : F) = -1 := by rw [Units.val_pow_eq_pow_val]; exact hζm2.eq_neg_one_of_two_right
    haveI : Fact (1 < N) := ⟨by omega⟩

    have hmval : ((m : ℕ) : ZMod N).val = m := ZMod.val_natCast_of_lt hmltN
    have hm0 : ((m : ℕ) : ZMod N) ≠ 0 := by
      intro h; have := congrArg ZMod.val h; rw [hmval, ZMod.val_zero] at this; omega
    have hcP : ModularCurve.cuspPoint F N ζ ![(m : ZMod N), 0] = ModularCurve.toricPoint F N ((ζ ^ m : Fˣ) : F) := by
      rw [ModularCurve.cuspPoint_of_eq_zero _ (by simp)]
      simp only [Matrix.cons_val_zero]
      rw [hmval, ModularCurve.tateToricPoint_eq_toricPoint]
    have hv1 : (![0, -(m : ZMod N)] : Fin 2 → ZMod N) 1 ≠ 0 := by simpa using hm0
    have hcQ : ModularCurve.cuspPoint F N ζ ![0, -(m : ZMod N)] = ModularCurve.nonToricPoint F N (1 : Fˣ) m := by
      rw [ModularCurve.cuspPoint_of_ne_zero _ hv1]
      have h0 : ((![0, -(m : ZMod N)] : Fin 2 → ZMod N) 0).val = 0 := by simp
      have h1 : ((![0, -(m : ZMod N)] : Fin 2 → ZMod N) 1).val = m := by
        rw [show (![0, -(m : ZMod N)] : Fin 2 → ZMod N) 1 = -(m : ZMod N) from rfl, ZMod.neg_val, if_neg hm0, hmval, hNm]
      rw [h0, h1, pow_zero]

    have hζne1 : ((ζ ^ m : Fˣ) : F) ≠ 1 := by rw [hζ1]; norm_num
    have hζne0 : ((ζ ^ m : Fˣ) : F) ≠ 0 := by rw [hζ1]; norm_num
    obtain ⟨nP, nQ, nR, hPQ⟩ :=
      (ModularCurve.toricPoint_add_nonToricPoint_of_charZero F N).1 (ζ ^ m) 1 m hζne1 hmpos hmltN
    obtain ⟨nP', nP'', hPP, hPP'⟩ :=
      ModularCurve.toricPoint_add_toricPoint_tateBase_of_charZero F N ((ζ ^ m : Fˣ) : F) ((ζ ^ m : Fˣ) : F) hζne0 hζne0 hζne1 hζne1
    have hPP0 := hPP (by rw [hζ1]; norm_num)

    have hPneg : (ModularCurve.toricPoint F N ((ζ ^ m : Fˣ) : F)).2 = (ModularCurve.tateBase F N).toAffine.negY (ModularCurve.toricPoint F N ((ζ ^ m : Fˣ) : F)).1 (ModularCurve.toricPoint F N ((ζ ^ m : Fˣ) : F)).2 := by
      by_contra hne
      rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hne] at hPP0
      exact WeierstrassCurve.Affine.Point.some_ne_zero _ hPP0

    have ha1 : (ModularCurve.tateBase F N).a₁ = 1 := by
      simp [ModularCurve.tateBase, ModularCurve.tateLaurent]
    have ha3 : (ModularCurve.tateBase F N).a₃ = 0 := by
      simp [ModularCurve.tateBase, ModularCurve.tateLaurent]
    have hQneg : (ModularCurve.nonToricPoint F N (1 : Fˣ) m).2 = (ModularCurve.tateBase F N).toAffine.negY (ModularCurve.nonToricPoint F N (1 : Fˣ) m).1 (ModularCurve.nonToricPoint F N (1 : Fˣ) m).2 := by
      have h49 := ModularCurve.nonToricPoint_inv_tsub (K := F) N (1 : Fˣ) m hmpos hmltN
      rw [inv_one, hNm] at h49
      have h2 := congrArg Prod.snd h49
      simp only at h2
      rw [WeierstrassCurve.Affine.negY, ha1, ha3]
      linear_combination h2

    have hPQne : ¬ ((ModularCurve.toricPoint F N ((ζ ^ m : Fˣ) : F)).1 = (ModularCurve.nonToricPoint F N (1 : Fˣ) m).1 ∧ (ModularCurve.toricPoint F N ((ζ ^ m : Fˣ) : F)).2 = (ModularCurve.nonToricPoint F N (1 : Fˣ) m).2) := by
      rintro ⟨hx, hy⟩
      have h0 : (WeierstrassCurve.Affine.Point.some _ _ nP : (ModularCurve.tateBase F N).toAffine.Point) + WeierstrassCurve.Affine.Point.some _ _ nQ = 0 :=
        WeierstrassCurve.Affine.Point.add_of_Y_eq hx (hy.trans hQneg)
      exact WeierstrassCurve.Affine.Point.some_ne_zero _ (hPQ.symm.trans h0)

    have hxP : φ D.xP = ((C.u⁻¹ : (LaurentSeries F)ˣ) : LaurentSeries F) ^ 2 * ((ModularCurve.toricPoint F N ((ζ ^ m : Fˣ) : F)).1 - C.r) := by
      have := congrArg ModularCurve.LevelPData.xP hD
      rw [ModularCurve.LevelPData.map_xP, ModularCurve.LevelPData.variableChange_xP, ModularCurve.cuspData_xP, hcP] at this
      exact this
    have hyP : φ D.yP = ((C.u⁻¹ : (LaurentSeries F)ˣ) : LaurentSeries F) ^ 3 * ((ModularCurve.toricPoint F N ((ζ ^ m : Fˣ) : F)).2 - C.s * ((ModularCurve.toricPoint F N ((ζ ^ m : Fˣ) : F)).1 - C.r) - C.t) := by
      have := congrArg ModularCurve.LevelPData.yP hD
      rw [ModularCurve.LevelPData.map_yP, ModularCurve.LevelPData.variableChange_yP, ModularCurve.cuspData_yP,
        ModularCurve.cuspData_xP, hcP] at this
      exact this
    have hxQ : φ D.xQ = ((C.u⁻¹ : (LaurentSeries F)ˣ) : LaurentSeries F) ^ 2 * ((ModularCurve.nonToricPoint F N (1 : Fˣ) m).1 - C.r) := by
      have := congrArg ModularCurve.LevelPData.xQ hD
      rw [ModularCurve.LevelPData.map_xQ, ModularCurve.LevelPData.variableChange_xQ, ModularCurve.cuspData_xQ, hcQ] at this
      exact this
    have hyQ : φ D.yQ = ((C.u⁻¹ : (LaurentSeries F)ˣ) : LaurentSeries F) ^ 3 * ((ModularCurve.nonToricPoint F N (1 : Fˣ) m).2 - C.s * ((ModularCurve.nonToricPoint F N (1 : Fˣ) m).1 - C.r) - C.t) := by
      have := congrArg ModularCurve.LevelPData.yQ hD
      rw [ModularCurve.LevelPData.map_yQ, ModularCurve.LevelPData.variableChange_yQ, ModularCurve.cuspData_yQ,
        ModularCurve.cuspData_xQ, hcQ] at this
      exact this

    have heq : ∀ {x y : T}, (W.map φ).toAffine.Equation (φ x) (φ y) → W.toAffine.Equation x y := by
      intro x y hxy
      rw [WeierstrassCurve.Affine.equation_iff] at hxy ⊢
      apply hinj
      simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄,
        WeierstrassCurve.map_a₆] at hxy
      simpa only [map_add, map_mul, map_pow] using hxy
    have hnegdesc : ∀ {x y : T}, (W.map φ).toAffine.negY (φ x) (φ y) = φ y → W.toAffine.negY x y = y := by
      intro x y h
      apply hinj
      rw [DTTAux.map_negY']; exact h

    have heqP : W.toAffine.Equation D.xP D.yP := by
      apply heq; rw [hW, hxP, hyP]; exact DTTAux.equation_variableChange (ModularCurve.tateBase F N) C nP.left
    have heqQ : W.toAffine.Equation D.xQ D.yQ := by
      apply heq; rw [hW, hxQ, hyQ]; exact DTTAux.equation_variableChange (ModularCurve.tateBase F N) C nQ.left

    have h2P : W.toAffine.negY D.xP D.yP = D.yP := by
      apply hnegdesc
      rw [hW, hxP, hyP]
      have key := DTTAux.negY_variableChange (ModularCurve.tateBase F N) C (ModularCurve.toricPoint F N ((ζ ^ m : Fˣ) : F)).1 (ModularCurve.toricPoint F N ((ζ ^ m : Fˣ) : F)).2
      rw [← hPneg, sub_self, mul_zero, sub_eq_zero] at key
      exact key
    have h2Q : W.toAffine.negY D.xQ D.yQ = D.yQ := by
      apply hnegdesc
      rw [hW, hxQ, hyQ]
      have key := DTTAux.negY_variableChange (ModularCurve.tateBase F N) C (ModularCurve.nonToricPoint F N (1 : Fˣ) m).1 (ModularCurve.nonToricPoint F N (1 : Fˣ) m).2
      rw [← hQneg, sub_self, mul_zero, sub_eq_zero] at key
      exact key

    have hu0 : ((C.u⁻¹ : (LaurentSeries F)ˣ) : LaurentSeries F) ≠ 0 := Units.ne_zero _
    have hPQT : ¬ (D.xP = D.xQ ∧ D.yP = D.yQ) := by
      rintro ⟨hx, hy⟩
      apply hPQne
      have hx' : (ModularCurve.toricPoint F N ((ζ ^ m : Fˣ) : F)).1 = (ModularCurve.nonToricPoint F N (1 : Fˣ) m).1 := by
        have := congrArg φ hx
        rw [hxP, hxQ] at this
        have := mul_left_cancel₀ (pow_ne_zero 2 hu0) this
        linear_combination this
      refine ⟨hx', ?_⟩
      have := congrArg φ hy
      rw [hyP, hyQ, hx'] at this
      have := mul_left_cancel₀ (pow_ne_zero 3 hu0) this
      linear_combination this

    have nPT : W.toAffine.Nonsingular D.xP D.yP := W.toAffine.equation_iff_nonsingular.mp heqP
    have nQT : W.toAffine.Nonsingular D.xQ D.yQ := W.toAffine.equation_iff_nonsingular.mp heqQ
    have htoP : ModularCurve.LevelRelabelling.toPoint W D.xP D.yP = WeierstrassCurve.Affine.Point.some _ _ nPT := dif_pos nPT
    have htoQ : ModularCurve.LevelRelabelling.toPoint W D.xQ D.yQ = WeierstrassCurve.Affine.Point.some _ _ nQT := dif_pos nQT
    rw [htoP, htoQ]
    have tP : (WeierstrassCurve.Affine.Point.some _ _ nPT : W.toAffine.Point) + WeierstrassCurve.Affine.Point.some _ _ nPT = 0 :=
      WeierstrassCurve.Affine.Point.add_self_of_Y_eq h2P.symm
    have tQ : (WeierstrassCurve.Affine.Point.some _ _ nQT : W.toAffine.Point) + WeierstrassCurve.Affine.Point.some _ _ nQT = 0 :=
      WeierstrassCurve.Affine.Point.add_self_of_Y_eq h2Q.symm
    refine ⟨heqP, heqQ, by rw [show ((2 : ℕ) : ℤ) = 2 from rfl, two_zsmul]; exact tP,
      by rw [show ((2 : ℕ) : ℤ) = 2 from rfl, two_zsmul]; exact tQ, ?_⟩
    intro a b ha hb hab
    interval_cases a <;> interval_cases b
    · exact ⟨rfl, rfl⟩
    · exfalso
      simp only [Nat.cast_zero, zero_smul, Nat.cast_one, one_smul, zero_add] at hab
      exact WeierstrassCurve.Affine.Point.some_ne_zero _ hab
    · exfalso
      simp only [Nat.cast_zero, zero_smul, Nat.cast_one, one_smul, add_zero] at hab
      exact WeierstrassCurve.Affine.Point.some_ne_zero _ hab
    · exfalso
      simp only [Nat.cast_one, one_smul] at hab
      rw [add_eq_zero_iff_eq_neg, WeierstrassCurve.Affine.Point.neg_some] at hab
      simp only [WeierstrassCurve.Affine.Point.some.injEq] at hab
      exact hPQT ⟨hab.1, by rw [hab.2, h2Q]⟩

#print axioms solution

end S_ModularCurve_torsion_basis_of_map_eq_variableChange_tateBase_cuspData_of_mul_eq
end P2MW
export P2MW.S_ModularCurve_torsion_basis_of_map_eq_variableChange_tateBase_cuspData_of_mul_eq (solution)
