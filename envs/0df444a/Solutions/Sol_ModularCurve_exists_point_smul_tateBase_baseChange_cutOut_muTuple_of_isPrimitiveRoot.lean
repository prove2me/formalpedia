-- Prove2me | solution 1 for ModularCurve.exists_point_smul_tateBase_baseChange_cutOut_muTuple_of_isPrimitiveRoot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/2fc081c4-2916-595d-9612-f12980aca2fd

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_WeierstrassCurve_CyclicQuotientJ
import Theorems.Thm_ModularCurve_exists_point_tateLaurent_nsmul_eq_toricPoint_of_isPrimitiveRoot
import Theorems.Thm_ModularCurve_toricPoint_level_mul
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_point_smul_tateBase_baseChange_cutOut_muTuple_of_isPrimitiveRoot
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero"
p2m_attr_erase "simp" "TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

open ModularCurve

set_option maxHeartbeats 3200000 in

theorem solution
    (F : Type) [Field F] [DecidableEq F] (Λ : Type) [Field Λ] [DecidableEq Λ] [Algebra (LaurentSeries F) Λ]
    (q ℓ M' : ℕ) [Fact q.Prime] [Fact ℓ.Prime] [NeZero M']
    (hqM' : ¬ q ∣ M') (hℓM' : ¬ ℓ ∣ M') (hM'F : ((M' : ℕ) : F) ≠ 0)
    (ζ : F) (hζ : IsPrimitiveRoot ζ M')
    (C : WeierstrassCurve.VariableChange Λ) :
    ∃ g : (C • (ModularCurve.tateBase F (q * ℓ)).baseChange Λ).toAffine.Point,
      (∀ n : ℕ, n • g = 0 ↔ M' ∣ n) ∧
      (∀ n : ℕ, ¬ M' ∣ n →
        ∃ h₁ : ((ModularCurve.tateBase F (q * ℓ)).baseChange Λ).toAffine.Nonsingular
            (algebraMap (LaurentSeries F) Λ (ModularCurve.toricPoint F (q * ℓ) (ζ ^ n)).1)
            (algebraMap (LaurentSeries F) Λ (ModularCurve.toricPoint F (q * ℓ) (ζ ^ n)).2),
          WeierstrassCurve.Affine.Point.vcFun C ((ModularCurve.tateBase F (q * ℓ)).baseChange Λ) (n • g) =
            WeierstrassCurve.Affine.Point.some _ _ h₁) ∧
      (addOrderOf g = M' ∧
        ∀ (p : ↥M'.primeFactors) (n : ℕ) (x₁ y₁ : Λ)
          (h₁ : (C • (ModularCurve.tateBase F (q * ℓ)).baseChange Λ).toAffine.Nonsingular x₁ y₁),
          n • g = WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ → addOrderOf (n • g) = (p : ℕ) ^ M'.factorization (p : ℕ) →
          ((fun p : ↥M'.primeFactors =>
        ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ)))
          (∏ a ∈ (Finset.Icc 1 ((p : ℕ) ^ M'.factorization (p : ℕ) / 2)).filter (fun a => ¬ (p : ℕ) ∣ a),
            (Polynomial.X - Polynomial.C (algebraMap (LaurentSeries F) Λ
              (ModularCurve.toricPoint F (q * ℓ) ((ζ ^ (M' / (p : ℕ) ^ M'.factorization (p : ℕ))) ^ a)).1)))) p).IsRoot x₁) ∧
      (∀ (p : ↥M'.primeFactors) (x₁ : Λ),
        ((fun p : ↥M'.primeFactors =>
        ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ)))
          (∏ a ∈ (Finset.Icc 1 ((p : ℕ) ^ M'.factorization (p : ℕ) / 2)).filter (fun a => ¬ (p : ℕ) ∣ a),
            (Polynomial.X - Polynomial.C (algebraMap (LaurentSeries F) Λ
              (ModularCurve.toricPoint F (q * ℓ) ((ζ ^ (M' / (p : ℕ) ^ M'.factorization (p : ℕ))) ^ a)).1)))) p).IsRoot x₁ ↔
          ∃ (P : (C • (ModularCurve.tateBase F (q * ℓ)).baseChange Λ).toAffine.Point) (y₁ : Λ)
            (h₁ : (C • (ModularCurve.tateBase F (q * ℓ)).baseChange Λ).toAffine.Nonsingular x₁ y₁),
            P ∈ AddSubgroup.zmultiples g ∧ addOrderOf P = (p : ℕ) ^ M'.factorization (p : ℕ) ∧
            P = WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) := by
  classical
  haveI : NeZero (q * ℓ) := ⟨Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero⟩
  have hM0 : M' ≠ 0 := NeZero.ne M'
  set a : LaurentSeries F →+* Λ := algebraMap (LaurentSeries F) Λ with ha

  have toric_inv : ∀ (N : ℕ) (c : F), (ModularCurve.toricPoint F N c⁻¹).1 = (ModularCurve.toricPoint F N c).1 := by
    intro N c
    simp only [ModularCurve.toricPoint_fst]
    congr 1
    ext m
    simp only [PowerSeries.coeff_mk, inv_inv]
    by_cases hm : m = 0
    · simp only [hm, if_true]
      by_cases hc : c = 0
      · simp [hc]
      by_cases hc1 : c = 1
      · simp [hc1]
      have h1c : (1 - c) ≠ 0 := sub_ne_zero.mpr (Ne.symm hc1)
      have h1c' : (1 - c⁻¹) ≠ 0 := by
        rw [sub_ne_zero]; intro h; exact hc1 (inv_eq_one.mp h.symm)
      rw [div_eq_div_iff (pow_ne_zero 2 h1c') (pow_ne_zero 2 h1c)]
      field_simp
      ring
    · simp only [hm, if_false]
      congr 1
      refine Finset.sum_congr rfl fun e _ => ?_
      split_ifs
      · rw [add_comm]
      · rfl

  have kvcd_root_iff : ∀ (dg : ℕ) (h : Polynomial Λ) (x' : Λ),
      (ModularCurve.kernelVariableChangeDeg C dg h).IsRoot x' ↔ h.IsRoot (WeierstrassCurve.Affine.vcX C x') := by
    intro dg h x'
    simp only [Polynomial.IsRoot, ModularCurve.kernelVariableChangeDeg, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X]
    rw [show (↑C.u : Λ) ^ 2 * x' + C.r = WeierstrassCurve.Affine.vcX C x' from rfl, mul_eq_zero,
      or_iff_right (pow_ne_zero _ (Units.ne_zero _))]

  by_cases hM1 : M' = 1
  · subst hM1
    refine ⟨0, fun n => by simp, fun n hn => absurd (one_dvd n) hn, ⟨by simp, ?_⟩, ?_⟩
    · rintro ⟨p, hp⟩; exact absurd hp (by simp)
    · rintro ⟨p, hp⟩; exact absurd hp (by simp)
  have hM2 : 2 ≤ M' := by omega

  obtain ⟨P, hP0, hP⟩ := @ModularCurve.exists_point_tateLaurent_nsmul_eq_toricPoint_of_isPrimitiveRoot
    F _ M' hM2 ζ hζ Λ _ _ ((a.comp (ModularCurve.qExpand F (q * ℓ))).toAlgebra)
  have h1 : ∀ c : F, @algebraMap (LaurentSeries F) Λ _ _ ((a.comp (ModularCurve.qExpand F (q * ℓ))).toAlgebra) (ModularCurve.toricPoint F 1 c).1 =
      a (ModularCurve.toricPoint F (q * ℓ) c).1 := by
    intro c
    have hlev := ModularCurve.toricPoint_level_mul F 1 (q * ℓ) c
    rw [mul_one] at hlev
    rw [hlev]; rfl
  have h2 : ∀ c : F, @algebraMap (LaurentSeries F) Λ _ _ ((a.comp (ModularCurve.qExpand F (q * ℓ))).toAlgebra) (ModularCurve.toricPoint F 1 c).2 =
      a (ModularCurve.toricPoint F (q * ℓ) c).2 := by
    intro c
    have hlev := ModularCurve.toricPoint_level_mul F 1 (q * ℓ) c
    rw [mul_one] at hlev
    rw [hlev]; rfl
  have hP0' : ∀ n : ℕ, (n • (P : ((ModularCurve.tateBase F (q * ℓ)).baseChange Λ).toAffine.Point)) = 0 ↔ M' ∣ n := hP0
  have hP' : ∀ n : ℕ, ¬ M' ∣ n →
      ∃ h₁ : ((ModularCurve.tateBase F (q * ℓ)).baseChange Λ).toAffine.Nonsingular (a (ModularCurve.toricPoint F (q * ℓ) (ζ ^ n)).1)
          (a (ModularCurve.toricPoint F (q * ℓ) (ζ ^ n)).2),
        (n • P : ((ModularCurve.tateBase F (q * ℓ)).baseChange Λ).toAffine.Point) = WeierstrassCurve.Affine.Point.some _ _ h₁ := by
    intro n hn
    have := hP n hn
    rw [h1, h2] at this
    exact this

  let ψ : ((ModularCurve.tateBase F (q * ℓ)).baseChange Λ).toAffine.Point →+ (C • ((ModularCurve.tateBase F (q * ℓ)).baseChange Λ)).toAffine.Point :=
    { toFun := WeierstrassCurve.Affine.Point.vcInvFun C ((ModularCurve.tateBase F (q * ℓ)).baseChange Λ)
      map_zero' := WeierstrassCurve.Affine.Point.vcInvFun_zero
      map_add' := WeierstrassCurve.Affine.Point.vcInvFun_add C ((ModularCurve.tateBase F (q * ℓ)).baseChange Λ).toAffine }
  have hψinj : Function.Injective ψ :=
    (WeierstrassCurve.Affine.Point.vcFun_rightInverse (C := C) (W := ((ModularCurve.tateBase F (q * ℓ)).baseChange Λ).toAffine)).injective
  have hvcψ : ∀ Q, WeierstrassCurve.Affine.Point.vcFun C ((ModularCurve.tateBase F (q * ℓ)).baseChange Λ) (ψ Q) = Q := fun Q =>
    WeierstrassCurve.Affine.Point.vcFun_rightInverse (C := C) (W := ((ModularCurve.tateBase F (q * ℓ)).baseChange Λ).toAffine) Q
  have hψvc : ∀ Q, ψ (WeierstrassCurve.Affine.Point.vcFun C ((ModularCurve.tateBase F (q * ℓ)).baseChange Λ) Q) = Q := fun Q =>
    WeierstrassCurve.Affine.Point.vcFun_leftInverse (C := C) (W := ((ModularCurve.tateBase F (q * ℓ)).baseChange Λ).toAffine) Q
  have hg0 : ∀ n : ℕ, n • ψ P = 0 ↔ M' ∣ n := by
    intro n
    rw [← map_nsmul ψ, ← hP0' n]
    constructor
    · intro h; exact hψinj (h.trans ψ.map_zero.symm)
    · intro h; exact (congrArg ψ h).trans ψ.map_zero
  have hgb : ∀ n : ℕ, ¬ M' ∣ n →
      ∃ h₁ : ((ModularCurve.tateBase F (q * ℓ)).baseChange Λ).toAffine.Nonsingular (a (ModularCurve.toricPoint F (q * ℓ) (ζ ^ n)).1)
          (a (ModularCurve.toricPoint F (q * ℓ) (ζ ^ n)).2),
        WeierstrassCurve.Affine.Point.vcFun C ((ModularCurve.tateBase F (q * ℓ)).baseChange Λ) (n • ψ P) = WeierstrassCurve.Affine.Point.some _ _ h₁ := by
    intro n hn
    obtain ⟨h₁, hsome⟩ := hP' n hn
    exact ⟨h₁, by rw [← map_nsmul ψ, hvcψ]; exact hsome⟩
  have hord : addOrderOf (ψ P) = M' := by
    apply Nat.dvd_antisymm
    · exact addOrderOf_dvd_of_nsmul_eq_zero ((hg0 M').mpr dvd_rfl)
    · exact (hg0 _).mp (addOrderOf_nsmul_eq_zero _)
  have hordζ : orderOf ζ = M' := hζ.eq_orderOf.symm

  have prim : ∀ (p : ↥M'.primeFactors), (p : ℕ).Prime ∧ (p : ℕ) ^ M'.factorization (p : ℕ) ∣ M' ∧
      0 < M'.factorization (p : ℕ) ∧ IsPrimitiveRoot (ζ ^ (M' / (p : ℕ) ^ M'.factorization (p : ℕ)))
        ((p : ℕ) ^ M'.factorization (p : ℕ)) := by
    intro p
    have hp : (p : ℕ).Prime := Nat.prime_of_mem_primeFactors p.2
    have hpk : (p : ℕ) ^ M'.factorization (p : ℕ) ∣ M' := Nat.ordProj_dvd M' p
    exact ⟨hp, hpk, hp.factorization_pos_of_dvd hM0 (Nat.dvd_of_mem_primeFactors p.2),
      hζ.pow (Nat.pos_of_ne_zero hM0) (Nat.div_mul_cancel hpk).symm⟩

  have cut : ∀ (p : ↥M'.primeFactors) (n : ℕ) (x₁ y₁ : Λ) (h₁ : (C • ((ModularCurve.tateBase F (q * ℓ)).baseChange Λ)).toAffine.Nonsingular x₁ y₁),
      n • ψ P = WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ → addOrderOf (n • ψ P) = (p : ℕ) ^ M'.factorization (p : ℕ) →
      (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ)))
          (∏ a₁ ∈ (Finset.Icc 1 ((p : ℕ) ^ M'.factorization (p : ℕ) / 2)).filter (fun a₁ => ¬ (p : ℕ) ∣ a₁),
            (Polynomial.X - Polynomial.C (a
              (ModularCurve.toricPoint F (q * ℓ) ((ζ ^ (M' / (p : ℕ) ^ M'.factorization (p : ℕ))) ^ a₁)).1)))).IsRoot x₁ := by
    intro p n x₁ y₁ h₁ hng hordn
    obtain ⟨hp, hpk, hkpos, hζ'prim⟩ := prim p
    haveI : NeZero ((p : ℕ) ^ M'.factorization (p : ℕ)) := ⟨(pow_pos hp.pos _).ne'⟩
    have hn : ¬ M' ∣ n := by
      intro hdv
      have := (hg0 n).mpr hdv
      rw [hng] at this
      exact WeierstrassCurve.Affine.Point.some_ne_zero h₁ this
    have hn0 : n ≠ 0 := by rintro rfl; exact hn (dvd_zero _)
    have hx₁ : WeierstrassCurve.Affine.vcX C x₁ = a (ModularCurve.toricPoint F (q * ℓ) (ζ ^ n)).1 := by
      obtain ⟨h₂, hsome⟩ := hgb n hn
      rw [hng] at hsome
      simp only [WeierstrassCurve.Affine.Point.vcFun] at hsome
      injection hsome
    have hζn : IsPrimitiveRoot (ζ ^ n) ((p : ℕ) ^ M'.factorization (p : ℕ)) := by
      have h := IsPrimitiveRoot.orderOf (ζ ^ n)
      have e1 : orderOf (ζ ^ n) = M' / Nat.gcd M' n := by rw [orderOf_pow' ζ hn0, hordζ]
      have e2 : addOrderOf (n • ψ P) = M' / Nat.gcd M' n := by rw [addOrderOf_nsmul' (ψ P) hn0, hord]
      rwa [e1, ← e2, hordn] at h
    set ζ' : F := ζ ^ (M' / (p : ℕ) ^ M'.factorization (p : ℕ)) with hζ'
    obtain ⟨i, hi, hiζ⟩ := hζ'prim.eq_pow_of_pow_eq_one hζn.pow_eq_one
    have hicop : i.Coprime ((p : ℕ) ^ M'.factorization (p : ℕ)) := by
      rw [← hζ'prim.pow_iff_coprime (pow_pos hp.pos _) i, hiζ]; exact hζn
    have hpi : ¬ (p : ℕ) ∣ i := by
      intro hdiv
      have := Nat.Coprime.coprime_dvd_left hdiv hicop
      rw [Nat.coprime_pow_right_iff hkpos, Nat.coprime_self] at this
      exact hp.one_lt.ne' this
    have hi0 : i ≠ 0 := by rintro rfl; exact hpi (dvd_zero _)
    have key : ∃ a₀ ∈ (Finset.Icc 1 ((p : ℕ) ^ M'.factorization (p : ℕ) / 2)).filter (fun a => ¬ (p : ℕ) ∣ a),
        (ModularCurve.toricPoint F (q * ℓ) (ζ' ^ a₀)).1 = (ModularCurve.toricPoint F (q * ℓ) (ζ ^ n)).1 := by
      by_cases hle : i ≤ (p : ℕ) ^ M'.factorization (p : ℕ) / 2
      · refine ⟨i, ?_, by rw [hiζ]⟩
        simp only [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨Nat.one_le_iff_ne_zero.mpr hi0, hle⟩, hpi⟩
      · refine ⟨(p : ℕ) ^ M'.factorization (p : ℕ) - i, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_Icc]
          refine ⟨⟨by omega, by omega⟩, fun hdiv => hpi ?_⟩
          exact (Nat.dvd_sub_iff_right (Nat.le_of_lt hi) (dvd_pow_self _ hkpos.ne')).mp hdiv
        · have hinv : ζ' ^ ((p : ℕ) ^ M'.factorization (p : ℕ) - i) = (ζ ^ n)⁻¹ := by
            rw [← hiζ]
            exact eq_inv_of_mul_eq_one_left (by rw [← pow_add, Nat.sub_add_cancel (Nat.le_of_lt hi), hζ'prim.pow_eq_one])
          rw [hinv, toric_inv]
    obtain ⟨a₀, ha₀, hxa⟩ := key
    rw [kvcd_root_iff, Polynomial.isRoot_prod]
    exact ⟨a₀, ha₀, by rw [Polynomial.root_X_sub_C, hxa, hx₁]⟩
  refine ⟨ψ P, hg0, hgb, ⟨hord, cut⟩, ?_⟩

  intro p x₁
  obtain ⟨hp, hpk, hkpos, hζ'prim⟩ := prim p
  haveI : NeZero ((p : ℕ) ^ M'.factorization (p : ℕ)) := ⟨(pow_pos hp.pos _).ne'⟩
  constructor
  · intro hroot
    rw [kvcd_root_iff, Polynomial.isRoot_prod] at hroot
    obtain ⟨a₀, ha₀, hxa⟩ := hroot
    rw [Polynomial.root_X_sub_C] at hxa
    simp only [Finset.mem_filter, Finset.mem_Icc] at ha₀
    obtain ⟨⟨ha1, -⟩, hpa⟩ := ha₀

    set n : ℕ := a₀ * (M' / (p : ℕ) ^ M'.factorization (p : ℕ)) with hn
    have hn' : ¬ M' ∣ n := by
      intro hdv
      apply hpa
      have hq0 : 0 < M' / (p : ℕ) ^ M'.factorization (p : ℕ) :=
        Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hM0) hpk) (pow_pos hp.pos _)
      have : (p : ℕ) ^ M'.factorization (p : ℕ) * (M' / (p : ℕ) ^ M'.factorization (p : ℕ)) ∣
          a₀ * (M' / (p : ℕ) ^ M'.factorization (p : ℕ)) := by
        rwa [Nat.mul_div_cancel' hpk]
      exact (dvd_pow_self _ hkpos.ne').trans ((Nat.dvd_of_mul_dvd_mul_right hq0) this)
    obtain ⟨h₂, hsome⟩ := hgb n hn'
    have hζpow : ζ ^ n = (ζ ^ (M' / (p : ℕ) ^ M'.factorization (p : ℕ))) ^ a₀ := by
      rw [← pow_mul, mul_comm, hn]
    have hx' : x₁ = WeierstrassCurve.Affine.vcXInv C (a (ModularCurve.toricPoint F (q * ℓ) (ζ ^ n)).1) := by
      rw [hζpow, hxa, WeierstrassCurve.Affine.vcXInv_vcX]
    refine ⟨n • ψ P, WeierstrassCurve.Affine.vcYInv C (a (ModularCurve.toricPoint F (q * ℓ) (ζ ^ n)).1)
      (a (ModularCurve.toricPoint F (q * ℓ) (ζ ^ n)).2), ?_, AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples _) _, ?_, ?_⟩
    ·
      rw [hx']
      exact (WeierstrassCurve.Affine.nonsingular_variableChange_iff _ _).mpr
        (by rw [WeierstrassCurve.Affine.vcX_vcXInv, WeierstrassCurve.Affine.vcY_vcYInv]; exact h₂)
    ·
      have ha0' : a₀ ≠ 0 := Nat.one_le_iff_ne_zero.mp ha1
      have hq0 : 0 < M' / (p : ℕ) ^ M'.factorization (p : ℕ) :=
        Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hM0) hpk) (pow_pos hp.pos _)
      have hn0 : n ≠ 0 := Nat.mul_ne_zero ha0' hq0.ne'
      rw [addOrderOf_nsmul' (ψ P) hn0, hord]
      have hcop : Nat.Coprime ((p : ℕ) ^ M'.factorization (p : ℕ)) a₀ :=
        Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpa)
      have hgcd : Nat.gcd M' n = M' / (p : ℕ) ^ M'.factorization (p : ℕ) := by
        conv_lhs => rw [← Nat.div_mul_cancel hpk, hn, mul_comm (M' / (p : ℕ) ^ M'.factorization (p : ℕ)),
          Nat.gcd_mul_right, hcop, one_mul]
      rw [hgcd, Nat.div_div_self hpk hM0]
    ·
      have hval : n • ψ P = ψ (WeierstrassCurve.Affine.Point.some _ _ h₂) := by
        rw [← hψvc (n • ψ P), hsome]
      have gen : ∀ (x : Λ) (hx : x = WeierstrassCurve.Affine.vcXInv C (a (ModularCurve.toricPoint F (q * ℓ) (ζ ^ n)).1))
          (h : (C • ((ModularCurve.tateBase F (q * ℓ)).baseChange Λ)).toAffine.Nonsingular x (WeierstrassCurve.Affine.vcYInv C
            (a (ModularCurve.toricPoint F (q * ℓ) (ζ ^ n)).1) (a (ModularCurve.toricPoint F (q * ℓ) (ζ ^ n)).2))),
          n • ψ P = WeierstrassCurve.Affine.Point.some _ _ h := by
        intro x hx h
        subst hx
        rw [hval]
        rfl
      exact gen x₁ hx' _
  · rintro ⟨Q, y₁, h₁, hQ, hordQ, rfl⟩
    obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp hQ

    have hM'g : ((M' : ℕ) : ℤ) • ψ P = 0 := by rw [natCast_zsmul]; exact (hg0 M').mpr dvd_rfl
    have h0 : 0 ≤ m % (M' : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hM0)
    set n : ℕ := (m % (M' : ℤ)).toNat with hn
    have hmn : m • ψ P = n • ψ P := by
      have hkill : ((M' : ℤ) * (m / (M' : ℤ))) • ψ P = 0 :=
        addOrderOf_dvd_iff_zsmul_eq_zero.mp (by rw [hord]; exact dvd_mul_right _ _)
      calc m • ψ P = (m % (M' : ℤ) + (M' : ℤ) * (m / (M' : ℤ))) • ψ P := by rw [Int.emod_add_mul_ediv]
        _ = (m % (M' : ℤ)) • ψ P + ((M' : ℤ) * (m / (M' : ℤ))) • ψ P := add_zsmul _ _ _
        _ = (m % (M' : ℤ)) • ψ P := by rw [hkill, add_zero]
        _ = n • ψ P := by rw [← natCast_zsmul, hn, Int.toNat_of_nonneg h0]
    rw [hmn] at hm
    exact cut p n x₁ y₁ h₁ hm (by rw [hm]; exact hordQ)

end S_ModularCurve_exists_point_smul_tateBase_baseChange_cutOut_muTuple_of_isPrimitiveRoot
end P2MW
export P2MW.S_ModularCurve_exists_point_smul_tateBase_baseChange_cutOut_muTuple_of_isPrimitiveRoot (solution)
