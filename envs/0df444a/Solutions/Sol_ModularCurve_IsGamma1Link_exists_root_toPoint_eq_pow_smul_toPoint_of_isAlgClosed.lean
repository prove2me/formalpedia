-- Prove2me | solution 1 for ModularCurve.IsGamma1Link.exists_root_toPoint_eq_pow_smul_toPoint_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/5ee097e9-f2d5-589e-b8d7-f2991585664f

import Mathlib
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import Definitions.Def_ModularCurve_WeierstrassGamma0Sqf
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Definitions.Def_EllipticCurve_DivisionPolynomialOmega
import Theorems.Thm_WeierstrassCurve_IsCyclicGenKernel_exists_addOrderOf_eq_and_isRoot
import Theorems.Thm_WeierstrassCurve_IsCyclicGenKernel_eq_prod_X_sub_C_coordsOrZero_nsmul
import Theorems.Thm_WeierstrassCurve_prod_X_sub_C_coordsOrZero_nsmul_eq_of_zmultiples_eq
import Theorems.Thm_WeierstrassCurve_Affine_Point_zsmul_x_mul_psi_sq
import Theorems.Thm_WeierstrassCurve_Affine_evalEval_phi
import Theorems.Thm_WeierstrassCurve_Affine_evalEval_psi_sq
import Theorems.Thm_WeierstrassCurve_isCoprime_Phi_PsiSq
import Theorems.Thm_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IsGamma1Link_exists_root_toPoint_eq_pow_smul_toPoint_of_isAlgClosed
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

open ModularCurve

namespace LinkRead

theorem baseChange_self {F : Type} [Field F] (W : WeierstrassCurve F) : W.baseChange F = W := by
  show W.map (algebraMap F F) = W
  rw [Algebra.algebraMap_self, WeierstrassCurve.map_id]

end LinkRead

theorem solution
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (ℓ M' : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓκ : (ℓ : κ) ≠ 0) (hmem : ℓ ∈ M'.primeFactors)
    (W : WeierstrassCurve κ) (hΔ : IsUnit W.Δ)
    (h : ↥M'.primeFactors → Polynomial κ) (hh : ∀ p : ↥M'.primeFactors, ModularCurve.IsGamma0PowAt W (p : ℕ) (M'.factorization (p : ℕ)) (h p))
    (D : ModularCurve.LevelPData κ) (hD : ModularCurve.IsGamma1Point W ℓ D)
    (hlink : ModularCurve.IsGamma1Link W ℓ M' h D) :
    ∃ (xG yG : κ),
      W.toAffine.Equation xG yG ∧ (h ⟨ℓ, hmem⟩).eval xG = 0 ∧
      ModularCurve.LevelRelabelling.toPoint (W.baseChange κ) D.xP D.yP =
        (ℓ ^ (M'.factorization ℓ - 1)) • ModularCurve.LevelRelabelling.toPoint (W.baseChange κ) xG yG := by
  classical
  haveI hE : W.IsElliptic := ⟨hΔ⟩
  set k : ℕ := M'.factorization ℓ with hk
  have hℓp : ℓ.Prime := Fact.out
  have hM'0 : M' ≠ 0 := (Nat.mem_primeFactors.mp hmem).2.2
  have hℓM' : ℓ ∣ M' := (Nat.mem_primeFactors.mp hmem).2.1
  have hk1 : 1 ≤ k := by rw [hk]; exact hℓp.factorization_pos_of_dvd hM'0 hℓM'
  have hℓk3 : 3 ≤ ℓ ^ k := le_trans hℓ3 (Nat.le_self_pow (by omega) ℓ)
  have hℓk2 : ℓ ^ k ≠ 2 := by omega
  have hℓodd : Odd ℓ := hℓp.odd_of_ne_two (by omega)
  set n : ℕ := ℓ ^ (k - 1) with hn
  have hnk : n * ℓ = ℓ ^ k := by rw [hn, ← pow_succ, Nat.sub_add_cancel hk1]

  have hGK : W.IsCyclicGenKernel ℓ k (h ⟨ℓ, hmem⟩) := by
    have := hh ⟨ℓ, hmem⟩
    rw [ModularCurve.isGamma0PowAt_of_pow_ne_two W hℓk2] at this
    exact this

  obtain ⟨xG, yG, hGns, hordG, hrootG⟩ :=
    WeierstrassCurve.IsCyclicGenKernel.exists_addOrderOf_eq_and_isRoot W ℓ k hℓκ hℓk3 (h ⟨ℓ, hmem⟩) hGK
  set G : W.toAffine.Point := WeierstrassCurve.Affine.Point.some xG yG hGns with hGdef

  have hPns : W.toAffine.Nonsingular D.xP D.yP := (WeierstrassCurve.Affine.equation_iff_nonsingular).mp hD.equation_P
  set P : W.toAffine.Point := WeierstrassCurve.Affine.Point.some D.xP D.yP hPns with hPdef
  have hordP : addOrderOf P = ℓ := by
    refine (addOrderOf_eq_prime_iff).mpr ⟨?_, WeierstrassCurve.Affine.Point.some_ne_zero hPns⟩
    rw [hPdef, WeierstrassCurve.Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi _ hℓodd hPns, ← WeierstrassCurve.preΨ_ofNat]
    exact hD.preΨ_P

  have tool : ∀ (x y : κ) (hns : W.toAffine.Nonsingular x y) (m : ℤ) (x' y' : κ) (hns' : W.toAffine.Nonsingular x' y'),
      m • WeierstrassCurve.Affine.Point.some x y hns = WeierstrassCurve.Affine.Point.some x' y' hns' →
      (W.ΨSq m).eval x ≠ 0 ∧ x' * (W.ΨSq m).eval x = (W.Φ m).eval x := by
    intro x y hns m x' y' hns' hm
    have e := WeierstrassCurve.Affine.Point.zsmul_x_mul_psi_sq W m hns hns' hm
    rw [WeierstrassCurve.Affine.evalEval_psi_sq W hns.left, WeierstrassCurve.Affine.evalEval_phi W hns.left] at e
    refine ⟨?_, e⟩
    intro h0
    have hΦ0 : (W.Φ m).eval x = 0 := by rw [← e, h0, mul_zero]
    obtain ⟨a, b, hab⟩ := WeierstrassCurve.isCoprime_Phi_PsiSq W m
    have := congrArg (Polynomial.eval x) hab
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul, hΦ0, h0, mul_zero, mul_zero, zero_add,
      Polynomial.eval_one] at this
    exact zero_ne_one this

  have hnG_ne : (n : ℤ) • G ≠ 0 := by
    intro h0
    rw [natCast_zsmul] at h0
    have hdvd := addOrderOf_dvd_of_nsmul_eq_zero h0
    rw [hordG] at hdvd
    have : ℓ ^ k ≤ n := Nat.le_of_dvd (by rw [hn]; positivity) hdvd
    rw [← hnk] at this
    have hnpos : 0 < n := by rw [hn]; positivity
    have h' : n * ℓ ≤ n * 1 := by simpa using this
    have := Nat.le_of_mul_le_mul_left h' hnpos
    omega
  obtain ⟨x1, y1, h1, hnG⟩ : ∃ (x1 y1 : κ) (h1 : W.toAffine.Nonsingular x1 y1),
      (n : ℤ) • G = WeierstrassCurve.Affine.Point.some x1 y1 h1 := by
    cases hQ : (n : ℤ) • G with
    | zero => exact absurd hQ hnG_ne
    | some x1 y1 h1 => exact ⟨x1, y1, h1, rfl⟩
  obtain ⟨hΨnG, hxnG⟩ := tool xG yG hGns n x1 y1 h1 (by rw [← hGdef]; exact hnG)

  have hev : (ModularCurve.inLineMulPoly W ℓ n D.xP).eval xG = 0 := by
    obtain ⟨c, hc⟩ := hlink hmem
    rw [← hk, ← hn] at hc
    rw [hc, Polynomial.eval_mul, show (h ⟨ℓ, hmem⟩).eval xG = 0 from hrootG, zero_mul]

  obtain ⟨b, hbmem, hbzero⟩ : ∃ b ∈ Finset.Icc 1 ((ℓ - 1) / 2),
      ((W.Φ n * Polynomial.C ((W.ΨSq b).eval D.xP) - Polynomial.C ((W.Φ b).eval D.xP) * W.ΨSq n).eval xG : κ) = 0 := by
    have : (ModularCurve.inLineMulPoly W ℓ n D.xP).eval xG =
        ∏ a ∈ Finset.Icc 1 ((ℓ - 1) / 2), (W.Φ n * Polynomial.C ((W.ΨSq a).eval D.xP) - Polynomial.C ((W.Φ a).eval D.xP) * W.ΨSq n).eval xG := by
      unfold ModularCurve.inLineMulPoly
      rw [Polynomial.eval_prod]
    rw [this] at hev
    exact Finset.prod_eq_zero_iff.mp hev
  rw [Finset.mem_Icc] at hbmem
  have hbℓ : b < ℓ := by omega

  have hbP_ne : (b : ℤ) • P ≠ 0 := by
    intro h0
    rw [natCast_zsmul] at h0
    have hdvd := addOrderOf_dvd_of_nsmul_eq_zero h0
    rw [hordP] at hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  obtain ⟨x2, y2, h2, hbP⟩ : ∃ (x2 y2 : κ) (h2 : W.toAffine.Nonsingular x2 y2),
      (b : ℤ) • P = WeierstrassCurve.Affine.Point.some x2 y2 h2 := by
    cases hQ : (b : ℤ) • P with
    | zero => exact absurd hQ hbP_ne
    | some x2 y2 h2 => exact ⟨x2, y2, h2, rfl⟩
  obtain ⟨hΨbP, hxbP⟩ := tool D.xP D.yP hPns b x2 y2 h2 (by rw [← hPdef]; exact hbP)

  have hx12 : x1 = x2 := by
    have e : (W.Φ (n : ℤ)).eval xG * (W.ΨSq (b : ℤ)).eval D.xP = (W.Φ (b : ℤ)).eval D.xP * (W.ΨSq (n : ℤ)).eval xG := by
      have := hbzero
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C] at this
      exact_mod_cast sub_eq_zero.mp this
    rw [← hxnG, ← hxbP] at e

    have : (x1 - x2) * ((W.ΨSq (n : ℤ)).eval xG * (W.ΨSq (b : ℤ)).eval D.xP) = 0 := by ring_nf; linear_combination e
    rcases mul_eq_zero.mp this with h0 | h0
    · exact sub_eq_zero.mp h0
    · rcases mul_eq_zero.mp h0 with h0 | h0
      · exact absurd h0 hΨnG
      · exact absurd h0 hΨbP

  have hpm : (n : ℤ) • G = (b : ℤ) • P ∨ (n : ℤ) • G = -((b : ℤ) • P) := by
    rw [hnG, hbP]; exact (WeierstrassCurve.Affine.Point.X_eq_iff).mp hx12
  obtain ⟨s, hs1, hsG⟩ : ∃ s : ℤ, s * s = 1 ∧ (n : ℤ) • G = (s * b) • P := by
    rcases hpm with h0 | h0
    · exact ⟨1, by norm_num, by rw [one_mul]; exact h0⟩
    · exact ⟨-1, by norm_num, by rw [neg_one_mul, neg_zsmul]; exact h0⟩

  have hb0 : ((b : ℕ) : ZMod ℓ) ≠ 0 := by
    intro h0
    rw [ZMod.natCast_eq_zero_iff] at h0
    have := Nat.le_of_dvd (by omega) h0
    omega
  set c : ℕ := (((b : ℕ) : ZMod ℓ)⁻¹).val with hc
  have hcb : ((c : ℕ) : ZMod ℓ) * ((b : ℕ) : ZMod ℓ) = 1 := by
    rw [hc, ZMod.natCast_zmod_val, inv_mul_cancel₀ hb0]
  have hℓc : ¬ ℓ ∣ c := by
    intro hdvd
    have : ((c : ℕ) : ZMod ℓ) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    rw [this, zero_mul] at hcb
    exact zero_ne_one hcb

  have hzsmulP : ∀ a a' : ℤ, ((a : ℤ) : ZMod ℓ) = (a' : ZMod ℓ) → a • P = a' • P := by
    intro a a' haa'
    obtain ⟨d, hd⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ ℓ).mp haa'
    have e : a' = a + (ℓ : ℤ) * d := by linarith
    have hℓP : ((ℓ : ℕ) : ℤ) • P = 0 := by rw [natCast_zsmul, ← hordP]; exact addOrderOf_nsmul_eq_zero P
    rw [e, add_zsmul, mul_comm, ← smul_smul, hℓP, zsmul_zero, add_zero]

  set G' : W.toAffine.Point := s • ((c : ℤ) • G) with hG'def
  have hPG' : (n : ℤ) • G' = P := by
    rw [hG'def, smul_smul, smul_smul, show ((n : ℤ) * s * (c : ℤ)) = (s * (c : ℤ)) * (n : ℤ) by ring, ← smul_smul, hsG, smul_smul]
    conv_rhs => rw [← one_zsmul P]
    apply hzsmulP
    have hss : ((s : ℤ) : ZMod ℓ) * (s : ZMod ℓ) = 1 := by exact_mod_cast congrArg (fun z : ℤ => (z : ZMod ℓ)) hs1
    push_cast
    linear_combination (((c : ℕ) : ZMod ℓ) * ((b : ℕ) : ZMod ℓ)) * hss + hcb

  have hs : s = 1 ∨ s = -1 := Int.isUnit_iff.mp (IsUnit.of_mul_eq_one s hs1)
  have hcop : (addOrderOf G).Coprime c := by
    rw [hordG]; exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hℓp).mpr hℓc)
  have hordcG : addOrderOf ((c : ℤ) • G) = ℓ ^ k := by
    rw [natCast_zsmul, hcop.addOrderOf_nsmul, hordG]
  have hordG' : addOrderOf G' = ℓ ^ k := by
    rcases hs with rfl | rfl
    · rw [hG'def, one_zsmul]; exact hordcG
    · rw [hG'def, neg_one_zsmul, addOrderOf_neg]; exact hordcG

  have hzm : AddSubgroup.zmultiples G = AddSubgroup.zmultiples G' := by
    have hle : AddSubgroup.zmultiples G' ≤ AddSubgroup.zmultiples G := by
      apply AddSubgroup.zmultiples_le_of_mem
      rw [hG'def, smul_smul]
      exact AddSubgroup.zsmul_mem_zmultiples G (s * (c : ℤ))
    have hcardG : Nat.card (AddSubgroup.zmultiples G) = ℓ ^ k := by rw [Nat.card_zmultiples, hordG]
    have hcardG' : Nat.card (AddSubgroup.zmultiples G') = ℓ ^ k := by rw [Nat.card_zmultiples, hordG']
    haveI : Finite (AddSubgroup.zmultiples G) := Nat.finite_of_card_ne_zero (by rw [hcardG]; positivity)
    exact (AddSubgroup.eq_of_le_of_card_ge hle (by rw [hcardG, hcardG'])).symm

  have hprodG := WeierstrassCurve.IsCyclicGenKernel.eq_prod_X_sub_C_coordsOrZero_nsmul W ℓ k hℓκ hℓk3 (h ⟨ℓ, hmem⟩) hGK G hordG
    ⟨xG, yG, hGns, hGdef, hrootG⟩
  rw [WeierstrassCurve.prod_X_sub_C_coordsOrZero_nsmul_eq_of_zmultiples_eq W ℓ k hℓk2 G G' hordG hordG' hzm] at hprodG
  have hG'ne : G' ≠ 0 := by
    intro h0; rw [h0, addOrderOf_zero] at hordG'; omega
  obtain ⟨xG', yG', hG'ns, hG'eq⟩ : ∃ (x' y' : κ) (h' : W.toAffine.Nonsingular x' y'), G' = WeierstrassCurve.Affine.Point.some x' y' h' := by
    cases hQ : G' with
    | zero => exact absurd hQ hG'ne
    | some x' y' h' => exact ⟨x', y', h', rfl⟩
  have hroot' : (h ⟨ℓ, hmem⟩).eval xG' = 0 := by
    have h1mem : (1 : ℕ) ∈ (Finset.Icc 1 (ℓ ^ k / 2)).filter (fun a => ¬ ℓ ∣ a) := by
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨le_rfl, ?_⟩, ?_⟩
      · omega
      · intro hd; have := Nat.le_of_dvd one_pos hd; omega
    rw [hprodG, Polynomial.eval_prod]
    apply Finset.prod_eq_zero h1mem
    rw [one_smul, hG'eq, WeierstrassCurve.Affine.Point.coordsOrZero_some]
    simp
  refine ⟨xG', yG', hG'ns.left, hroot', ?_⟩
  rw [LinkRead.baseChange_self]
  rw [ModularCurve.LevelRelabelling.toPoint, dif_pos hPns, ModularCurve.LevelRelabelling.toPoint, dif_pos hG'ns, ← hG'eq,
    ← hPdef, ← hPG', ← natCast_zsmul]

end S_ModularCurve_IsGamma1Link_exists_root_toPoint_eq_pow_smul_toPoint_of_isAlgClosed
end P2MW
export P2MW.S_ModularCurve_IsGamma1Link_exists_root_toPoint_eq_pow_smul_toPoint_of_isAlgClosed (solution)
