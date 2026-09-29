-- Prove2me | solution 1 for ModularCurve.natCard_levelPData_isGamma1Point_and_isGamma1Link_eq_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/db010b3a-b7de-52ce-9a75-946a4247db94

import Mathlib
import Definitions.Def_ModularCurve_WeierstrassH1Pow
import Definitions.Def_ModularCurve_LevelRelabelling
import Theorems.Thm_ModularCurve_IsGamma1Link_exists_root_toPoint_eq_pow_smul_toPoint_of_isAlgClosed
import Theorems.Thm_ModularCurve_isGamma1Point_and_dvd_inLineMulPoly_of_toPoint_eq_mul_pow_smul_of_isRoot
import Theorems.Thm_WeierstrassCurve_IsCyclicGenKernel_exists_addOrderOf_eq_and_isRoot
import Theorems.Thm_WeierstrassCurve_IsCyclicGenKernel_eq_prod_X_sub_C_coordsOrZero_nsmul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_natCard_levelPData_isGamma1Point_and_isGamma1Link_eq_of_isAlgClosed
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂"
p2m_attr_erase "simp" "Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

open ModularCurve

namespace LPC

theorem baseChange_self {F : Type} [Field F] (W : WeierstrassCurve F) : W.baseChange F = W := by
  show W.map (algebraMap F F) = W
  rw [Algebra.algebraMap_self, WeierstrassCurve.map_id]

theorem toPoint_some {F : Type} [Field F] [DecidableEq F] (W : WeierstrassCurve F) {x y : F} (h : W.toAffine.Nonsingular x y) :
    ModularCurve.LevelRelabelling.toPoint W x y = WeierstrassCurve.Affine.Point.some x y h := by
  rw [ModularCurve.LevelRelabelling.toPoint, dif_pos h]

end LPC

theorem solution
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [DecidableEq Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (M' : ℕ) [NeZero M'] (hℓM' : ℓ ∣ M')
    (W₀ : WeierstrassCurve Ω) (hΔ : IsUnit W₀.Δ)
    (h : ↥M'.primeFactors → Polynomial Ω)
    (hh : ∀ p : ↥M'.primeFactors, ModularCurve.IsGamma0PowAt W₀ (p : ℕ) (M'.factorization (p : ℕ)) (h p)) :
    Nat.card {D : ModularCurve.LevelPData Ω //
        ModularCurve.IsGamma1Point W₀ ℓ D ∧ ModularCurve.IsGamma1Link W₀ ℓ M' h D} = ℓ - 1 := by
  classical
  haveI hE : W₀.IsElliptic := ⟨hΔ⟩
  have hℓp : ℓ.Prime := Fact.out
  have hℓΩ : (ℓ : Ω) ≠ 0 := Nat.cast_ne_zero.mpr hℓp.ne_zero
  have hmem : ℓ ∈ M'.primeFactors := Nat.mem_primeFactors.mpr ⟨hℓp, hℓM', NeZero.ne M'⟩
  set k : ℕ := M'.factorization ℓ with hk
  have hk1 : 1 ≤ k := by rw [hk]; exact hℓp.factorization_pos_of_dvd (NeZero.ne M') hℓM'
  have hℓk3 : 3 ≤ ℓ ^ k := le_trans hℓ3 (Nat.le_self_pow (by omega) ℓ)
  have hℓk2 : ℓ ^ k ≠ 2 := by omega
  set n : ℕ := ℓ ^ (k - 1) with hn
  have hnk : n * ℓ = ℓ ^ k := by rw [hn, ← pow_succ, Nat.sub_add_cancel hk1]
  have hnpos : 0 < n := by rw [hn]; positivity

  have hGK : W₀.IsCyclicGenKernel ℓ k (h ⟨ℓ, hmem⟩) := by
    have := hh ⟨ℓ, hmem⟩
    rw [ModularCurve.isGamma0PowAt_of_pow_ne_two W₀ hℓk2] at this
    exact this
  obtain ⟨xG, yG, hGns, hordG, hrootG⟩ :=
    WeierstrassCurve.IsCyclicGenKernel.exists_addOrderOf_eq_and_isRoot W₀ ℓ k hℓΩ hℓk3 (h ⟨ℓ, hmem⟩) hGK
  set G : W₀.toAffine.Point := WeierstrassCurve.Affine.Point.some xG yG hGns with hGdef
  have hprodG := WeierstrassCurve.IsCyclicGenKernel.eq_prod_X_sub_C_coordsOrZero_nsmul W₀ ℓ k hℓΩ hℓk3 (h ⟨ℓ, hmem⟩) hGK G hordG
    ⟨xG, yG, hGns, hGdef, hrootG⟩

  set G₁ : W₀.toAffine.Point := n • G with hG₁def
  have hordG₁ : addOrderOf G₁ = ℓ := by
    rw [hG₁def, addOrderOf_nsmul' G hnpos.ne', hordG, ← hnk, Nat.gcd_eq_right (dvd_mul_right n ℓ), Nat.mul_div_cancel_left ℓ hnpos]
  have hℓG₁ : (ℓ : ℤ) • G₁ = 0 := by
    rw [natCast_zsmul, ← hordG₁]; exact addOrderOf_nsmul_eq_zero G₁

  have hsome : ∀ (Q : W₀.toAffine.Point), Q ≠ 0 → ∃ (x y : Ω) (hxy : W₀.toAffine.Nonsingular x y),
      Q = WeierstrassCurve.Affine.Point.some x y hxy := by
    intro Q hQ
    cases hQ' : Q with
    | zero => exact absurd hQ' hQ
    | some x y hxy => exact ⟨x, y, hxy, rfl⟩

  set S₁ : Set W₀.toAffine.Point := ((AddSubgroup.zmultiples G₁ : Set W₀.toAffine.Point) \ {0}) with hS₁

  have hPns : ∀ D : {D : ModularCurve.LevelPData Ω // ModularCurve.IsGamma1Point W₀ ℓ D ∧ ModularCurve.IsGamma1Link W₀ ℓ M' h D},
      W₀.toAffine.Nonsingular D.1.xP D.1.yP := fun D =>
    (WeierstrassCurve.Affine.equation_iff_nonsingular).mp D.2.1.equation_P

  have hmemS : ∀ D : {D : ModularCurve.LevelPData Ω // ModularCurve.IsGamma1Point W₀ ℓ D ∧ ModularCurve.IsGamma1Link W₀ ℓ M' h D},
      WeierstrassCurve.Affine.Point.some D.1.xP D.1.yP (hPns D) ∈ S₁ := by
    intro D
    obtain ⟨xG', yG', hG'eq, hroot', hP⟩ :=
      ModularCurve.IsGamma1Link.exists_root_toPoint_eq_pow_smul_toPoint_of_isAlgClosed ℓ M' hℓ3 hℓΩ hmem W₀ hΔ h hh
        D.1 D.2.1 D.2.2
    rw [LPC.baseChange_self] at hP
    have hG'ns : W₀.toAffine.Nonsingular xG' yG' := (WeierstrassCurve.Affine.equation_iff_nonsingular).mp hG'eq
    rw [LPC.toPoint_some W₀ (hPns D), LPC.toPoint_some W₀ hG'ns, ← hk, ← hn] at hP

    have hev : (h ⟨ℓ, hmem⟩).eval xG' = 0 := hroot'
    rw [hprodG, Polynomial.eval_prod, Finset.prod_eq_zero_iff] at hev
    obtain ⟨a, hamem, ha⟩ := hev
    rw [Finset.mem_filter, Finset.mem_Icc] at hamem
    have haG_ne : a • G ≠ 0 := by
      intro h0
      have hdvd := addOrderOf_dvd_of_nsmul_eq_zero h0
      rw [hordG] at hdvd
      have := Nat.le_of_dvd (by omega) hdvd
      omega
    obtain ⟨xa, ya, hans, haG⟩ := hsome _ haG_ne
    rw [haG, WeierstrassCurve.Affine.Point.coordsOrZero_some] at ha
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at ha

    have hpm : WeierstrassCurve.Affine.Point.some xG' yG' hG'ns = a • G ∨
        WeierstrassCurve.Affine.Point.some xG' yG' hG'ns = -(a • G) := by
      rw [haG]; exact (WeierstrassCurve.Affine.Point.X_eq_iff).mp ha
    refine ⟨?_, WeierstrassCurve.Affine.Point.some_ne_zero _⟩
    show WeierstrassCurve.Affine.Point.some D.1.xP D.1.yP (hPns D) ∈ AddSubgroup.zmultiples G₁
    rw [hP]
    rcases hpm with h0 | h0
    · rw [h0, smul_smul, mul_comm, ← smul_smul]
      exact AddSubgroup.nsmul_mem_zmultiples G₁ a
    · rw [h0, smul_neg, smul_smul, mul_comm, ← smul_smul]
      exact AddSubgroup.neg_mem _ (AddSubgroup.nsmul_mem_zmultiples G₁ a)
  let f : {D : ModularCurve.LevelPData Ω // ModularCurve.IsGamma1Point W₀ ℓ D ∧ ModularCurve.IsGamma1Link W₀ ℓ M' h D} → ↥S₁ :=
    fun D => ⟨WeierstrassCurve.Affine.Point.some D.1.xP D.1.yP (hPns D), hmemS D⟩

  have hinj : Function.Injective f := by
    intro D D' hDD'
    have h1 : WeierstrassCurve.Affine.Point.some D.1.xP D.1.yP (hPns D) =
        WeierstrassCurve.Affine.Point.some D'.1.xP D'.1.yP (hPns D') := congrArg Subtype.val hDD'
    simp only [WeierstrassCurve.Affine.Point.some.injEq] at h1
    obtain ⟨hx, hy⟩ := h1
    apply Subtype.ext
    obtain ⟨⟨xP, yP, xQ, yQ⟩, ⟨hD1, hD2⟩⟩ := D
    obtain ⟨⟨xP', yP', xQ', yQ'⟩, ⟨hD1', hD2'⟩⟩ := D'
    simp only at hx hy
    have e1 := hD1.xQ_eq; have e2 := hD1.yQ_eq; have e3 := hD1'.xQ_eq; have e4 := hD1'.yQ_eq
    simp only at e1 e2 e3 e4
    show ModularCurve.LevelPData.mk xP yP xQ yQ = ModularCurve.LevelPData.mk xP' yP' xQ' yQ'
    rw [e1, e2, e3, e4, hx, hy]

  have hsurj : Function.Surjective f := by
    rintro ⟨P, hPmem, hP0⟩
    rw [Set.mem_singleton_iff] at hP0
    obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp hPmem
    obtain ⟨x, y, hxy, hPeq⟩ := hsome P hP0

    set b : ℕ := ((m : ℤ) : ZMod ℓ).val with hb
    have hbm : ((b : ℕ) : ZMod ℓ) = ((m : ℤ) : ZMod ℓ) := by rw [hb, ZMod.natCast_zmod_val]
    have hPb : P = (b * n) • G := by
      rw [mul_smul, ← hG₁def, ← hm, ← natCast_zsmul]
      obtain ⟨d, hd⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ ℓ).mp (by exact_mod_cast hbm.symm : ((m : ℤ) : ZMod ℓ) = ((b : ℕ) : ℤ))
      have e : ((b : ℕ) : ℤ) = m + (ℓ : ℤ) * d := by linarith
      rw [e, add_zsmul, mul_comm, ← smul_smul, hℓG₁, zsmul_zero, add_zero]
    have hbℓ : ¬ ℓ ∣ b := by
      intro hdvd
      have hb0 : ((b : ℕ) : ZMod ℓ) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
      have hm0 : ((m : ℤ) : ZMod ℓ) = 0 := by rw [← hbm, hb0]
      obtain ⟨d, hd⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd m ℓ).mp hm0
      apply hP0
      rw [← hm, hd, mul_comm, ← smul_smul, hℓG₁, zsmul_zero]
    let D : ModularCurve.LevelPData Ω := ⟨x, y, x, y⟩
    have hPG : ModularCurve.LevelRelabelling.toPoint (W₀.baseChange Ω) D.xP D.yP =
        (b * ℓ ^ (M'.factorization ℓ - 1)) • ModularCurve.LevelRelabelling.toPoint (W₀.baseChange Ω) xG yG := by
      rw [LPC.baseChange_self]
      rw [LPC.toPoint_some W₀ hxy, LPC.toPoint_some W₀ hGns, ← hGdef, ← hk, ← hn, ← hPb, hPeq]
    obtain ⟨hΓ1, hdvd⟩ := ModularCurve.isGamma1Point_and_dvd_inLineMulPoly_of_toPoint_eq_mul_pow_smul_of_isRoot
      ℓ M' hℓ3 hℓΩ hmem W₀ hΔ h hh xG yG hGns.left hrootG b hbℓ D hxy.left ⟨rfl, rfl⟩ hPG
    have hlink : ModularCurve.IsGamma1Link W₀ ℓ M' h D := fun _ => hdvd
    refine ⟨⟨D, hΓ1, hlink⟩, ?_⟩
    apply Subtype.ext
    show WeierstrassCurve.Affine.Point.some x y _ = P
    rw [hPeq]

  rw [Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩), Nat.card_coe_set_eq]
  have hcard : Nat.card (AddSubgroup.zmultiples G₁) = ℓ := by rw [Nat.card_zmultiples, hordG₁]
  haveI : Finite (AddSubgroup.zmultiples G₁) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hℓp.ne_zero)
  have hfin : (AddSubgroup.zmultiples G₁ : Set W₀.toAffine.Point).Finite := Set.toFinite _
  rw [hS₁, Set.ncard_diff_singleton_of_mem (AddSubgroup.zero_mem (AddSubgroup.zmultiples G₁)), ← Nat.card_coe_set_eq]
  show Nat.card (AddSubgroup.zmultiples G₁) - 1 = ℓ - 1
  rw [hcard]

end S_ModularCurve_natCard_levelPData_isGamma1Point_and_isGamma1Link_eq_of_isAlgClosed
end P2MW
export P2MW.S_ModularCurve_natCard_levelPData_isGamma1Point_and_isGamma1Link_eq_of_isAlgClosed (solution)
