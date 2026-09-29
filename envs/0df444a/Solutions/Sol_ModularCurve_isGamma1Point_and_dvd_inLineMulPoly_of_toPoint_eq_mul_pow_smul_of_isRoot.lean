-- Prove2me | solution 1 for ModularCurve.isGamma1Point_and_dvd_inLineMulPoly_of_toPoint_eq_mul_pow_smul_of_isRoot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/a777d85b-1ea3-541e-87b3-6bc18571dea1

import Mathlib
import Definitions.Def_ModularCurve_WeierstrassH1Pow
import Definitions.Def_ModularCurve_LevelRelabelling
import Theorems.Thm_WeierstrassCurve_IsCyclicGenKernel_exists_addOrderOf_eq_and_isRoot
import Theorems.Thm_WeierstrassCurve_IsCyclicGenKernel_eq_prod_X_sub_C_coordsOrZero_nsmul
import Theorems.Thm_WeierstrassCurve_Affine_Point_zsmul_x_mul_psi_sq
import Theorems.Thm_WeierstrassCurve_Affine_evalEval_phi
import Theorems.Thm_WeierstrassCurve_Affine_evalEval_psi_sq
import Theorems.Thm_WeierstrassCurve_isCoprime_Phi_PsiSq
import Theorems.Thm_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isGamma1Point_and_dvd_inLineMulPoly_of_toPoint_eq_mul_pow_smul_of_isRoot
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

open ModularCurve

namespace LW

theorem baseChange_self {F : Type} [Field F] (W : WeierstrassCurve F) : W.baseChange F = W := by
  show W.map (algebraMap F F) = W
  rw [Algebra.algebraMap_self, WeierstrassCurve.map_id]

theorem toPoint_some {F : Type} [Field F] [DecidableEq F] (W : WeierstrassCurve F) {x y : F} (h : W.toAffine.Nonsingular x y) :
    ModularCurve.LevelRelabelling.toPoint W x y = WeierstrassCurve.Affine.Point.some x y h := by
  rw [ModularCurve.LevelRelabelling.toPoint, dif_pos h]

theorem exists_half_rep (ℓ : ℕ) (hℓ3 : 3 ≤ ℓ) (hodd : Odd ℓ) (r : ZMod ℓ) (hr : r ≠ 0) :
    ∃ (c : ℕ) (s : ℤ), 1 ≤ c ∧ c ≤ (ℓ - 1) / 2 ∧ (s = 1 ∨ s = -1) ∧ ((s * c : ℤ) : ZMod ℓ) = r := by
  haveI : NeZero ℓ := ⟨by omega⟩
  have hval : r.val < ℓ := ZMod.val_lt r
  have hval0 : r.val ≠ 0 := fun h0 => hr ((ZMod.val_eq_zero r).mp h0)
  obtain ⟨t, ht⟩ := hodd
  by_cases hle : r.val ≤ (ℓ - 1) / 2
  · refine ⟨r.val, 1, by omega, hle, Or.inl rfl, ?_⟩
    push_cast
    rw [one_mul, ZMod.natCast_zmod_val]
  · refine ⟨ℓ - r.val, -1, by omega, by omega, Or.inr rfl, ?_⟩
    have key : ((ℓ : ℕ) : ZMod ℓ) - ((r.val : ℕ) : ZMod ℓ) = - r := by
      rw [ZMod.natCast_self, ZMod.natCast_zmod_val, zero_sub]
    push_cast
    rw [Nat.cast_sub hval.le, neg_one_mul, key, neg_neg]

end LW

set_option maxHeartbeats 3200000 in
theorem solution
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (ℓ M' : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓκ : (ℓ : κ) ≠ 0) (hmem : ℓ ∈ M'.primeFactors)
    (W : WeierstrassCurve κ) (hΔ : IsUnit W.Δ)
    (h : ↥M'.primeFactors → Polynomial κ) (hh : ∀ p : ↥M'.primeFactors, ModularCurve.IsGamma0PowAt W (p : ℕ) (M'.factorization (p : ℕ)) (h p))
    (xG yG : κ) (hG : W.toAffine.Equation xG yG) (hroot : (h ⟨ℓ, hmem⟩).eval xG = 0)
    (b : ℕ) (hb : ¬ ℓ ∣ b)
    (D : ModularCurve.LevelPData κ) (hDP : W.toAffine.Equation D.xP D.yP)
    (hDQ : D.xQ = D.xP ∧ D.yQ = D.yP)
    (hPG : ModularCurve.LevelRelabelling.toPoint (W.baseChange κ) D.xP D.yP =
      (b * ℓ ^ (M'.factorization ℓ - 1)) • ModularCurve.LevelRelabelling.toPoint (W.baseChange κ) xG yG) :
    ModularCurve.IsGamma1Point W ℓ D ∧
      h ⟨ℓ, hmem⟩ ∣ ModularCurve.inLineMulPoly W ℓ (ℓ ^ (M'.factorization ℓ - 1)) D.xP := by
  classical
  haveI hE : W.IsElliptic := ⟨hΔ⟩
  have hℓp : ℓ.Prime := Fact.out
  haveI : NeZero ℓ := ⟨hℓp.ne_zero⟩
  set k : ℕ := M'.factorization ℓ with hk
  have hM'0 : M' ≠ 0 := (Nat.mem_primeFactors.mp hmem).2.2
  have hℓM' : ℓ ∣ M' := (Nat.mem_primeFactors.mp hmem).2.1
  have hk1 : 1 ≤ k := by rw [hk]; exact hℓp.factorization_pos_of_dvd hM'0 hℓM'
  have hℓk3 : 3 ≤ ℓ ^ k := le_trans hℓ3 (Nat.le_self_pow (by omega) ℓ)
  have hℓk2 : ℓ ^ k ≠ 2 := by omega
  have hℓodd : Odd ℓ := hℓp.odd_of_ne_two (by omega)
  have hℓkodd : Odd (ℓ ^ k) := hℓodd.pow
  set n : ℕ := ℓ ^ (k - 1) with hn
  have hnk : n * ℓ = ℓ ^ k := by rw [hn, ← pow_succ, Nat.sub_add_cancel hk1]
  have hnpos : 0 < n := by rw [hn]; positivity

  have hGK : W.IsCyclicGenKernel ℓ k (h ⟨ℓ, hmem⟩) := by
    have := hh ⟨ℓ, hmem⟩
    rw [ModularCurve.isGamma0PowAt_of_pow_ne_two W hℓk2] at this
    exact this
  obtain ⟨x₀, y₀, h₀ns, hordG₀, hroot₀⟩ :=
    WeierstrassCurve.IsCyclicGenKernel.exists_addOrderOf_eq_and_isRoot W ℓ k hℓκ hℓk3 (h ⟨ℓ, hmem⟩) hGK
  set G₀ : W.toAffine.Point := WeierstrassCurve.Affine.Point.some x₀ y₀ h₀ns with hG₀def
  have hprod := WeierstrassCurve.IsCyclicGenKernel.eq_prod_X_sub_C_coordsOrZero_nsmul W ℓ k hℓκ hℓk3 (h ⟨ℓ, hmem⟩) hGK G₀ hordG₀
    ⟨x₀, y₀, h₀ns, hG₀def, hroot₀⟩
  set G₁ : W.toAffine.Point := n • G₀ with hG₁def
  have hordG₁ : addOrderOf G₁ = ℓ := by
    rw [hG₁def, addOrderOf_nsmul' G₀ hnpos.ne', hordG₀, ← hnk, Nat.gcd_eq_right (dvd_mul_right n ℓ), Nat.mul_div_cancel_left ℓ hnpos]
  have hℓG₁ : (ℓ : ℤ) • G₁ = 0 := by
    rw [natCast_zsmul, ← hordG₁]; exact addOrderOf_nsmul_eq_zero G₁

  have hzsmul : ∀ z z' : ℤ, ((z : ℤ) : ZMod ℓ) = (z' : ZMod ℓ) → z • G₁ = z' • G₁ := by
    intro z z' hzz'
    obtain ⟨d, hd⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ ℓ).mp hzz'
    have e : z' = z + (ℓ : ℤ) * d := by linarith
    rw [e, add_zsmul, mul_comm, ← smul_smul, hℓG₁, zsmul_zero, add_zero]
  have hsome : ∀ (Q : W.toAffine.Point), Q ≠ 0 → ∃ (x y : κ) (hxy : W.toAffine.Nonsingular x y),
      Q = WeierstrassCurve.Affine.Point.some x y hxy := by
    intro Q hQ
    cases hQ' : Q with
    | zero => exact absurd hQ' hQ
    | some x y hxy => exact ⟨x, y, hxy, rfl⟩

  have tool : ∀ (x y : κ) (hns : W.toAffine.Nonsingular x y) (m : ℤ) (x' y' : κ) (hns' : W.toAffine.Nonsingular x' y'),
      m • WeierstrassCurve.Affine.Point.some x y hns = WeierstrassCurve.Affine.Point.some x' y' hns' →
      (W.ΨSq m).eval x ≠ 0 ∧ x' * (W.ΨSq m).eval x = (W.Φ m).eval x := by
    intro x y hns m x' y' hns' hm
    have e := WeierstrassCurve.Affine.Point.zsmul_x_mul_psi_sq W m hns hns' hm
    rw [WeierstrassCurve.Affine.evalEval_psi_sq W hns.left, WeierstrassCurve.Affine.evalEval_phi W hns.left] at e
    refine ⟨?_, e⟩
    intro h0
    have hΦ0 : (W.Φ m).eval x = 0 := by rw [← e, h0, mul_zero]
    obtain ⟨u, v, huv⟩ := WeierstrassCurve.isCoprime_Phi_PsiSq W m
    have := congrArg (Polynomial.eval x) huv
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul, hΦ0, h0, mul_zero, mul_zero, zero_add,
      Polynomial.eval_one] at this
    exact zero_ne_one this

  have hSne : ∀ a : ℕ, 1 ≤ a → a ≤ ℓ ^ k / 2 → a • G₀ ≠ 0 := by
    intro a ha1 ha2 h0
    have hdvd := addOrderOf_dvd_of_nsmul_eq_zero h0
    rw [hordG₀] at hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega

  have hGns : W.toAffine.Nonsingular xG yG := (WeierstrassCurve.Affine.equation_iff_nonsingular).mp hG
  set G : W.toAffine.Point := WeierstrassCurve.Affine.Point.some xG yG hGns with hGdef
  have hev : (h ⟨ℓ, hmem⟩).eval xG = 0 := hroot
  rw [hprod, Polynomial.eval_prod, Finset.prod_eq_zero_iff] at hev
  obtain ⟨aG, haGmem, haG⟩ := hev
  rw [Finset.mem_filter, Finset.mem_Icc] at haGmem
  obtain ⟨xa, ya, hans, haG₀⟩ := hsome _ (hSne aG haGmem.1.1 haGmem.1.2)
  rw [haG₀, WeierstrassCurve.Affine.Point.coordsOrZero_some] at haG
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at haG
  have hpmG : G = aG • G₀ ∨ G = -(aG • G₀) := by
    rw [hGdef, haG₀]; exact (WeierstrassCurve.Affine.Point.X_eq_iff).mp haG
  obtain ⟨ε, hε, hGε⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ G = (ε * aG) • G₀ := by
    rcases hpmG with h0 | h0
    · exact ⟨1, Or.inl rfl, by rw [one_mul, natCast_zsmul]; exact h0⟩
    · exact ⟨-1, Or.inr rfl, by rw [neg_one_mul, neg_zsmul, natCast_zsmul]; exact h0⟩

  have hPns : W.toAffine.Nonsingular D.xP D.yP := (WeierstrassCurve.Affine.equation_iff_nonsingular).mp hDP
  set P : W.toAffine.Point := WeierstrassCurve.Affine.Point.some D.xP D.yP hPns with hPdef
  have hP : P = (b * n) • G := by
    have e := hPG
    rw [LW.baseChange_self] at e
    rw [LW.toPoint_some W hPns, LW.toPoint_some W hGns] at e
    rw [hPdef, hGdef]; exact e
  set m : ℤ := ε * aG * b with hm
  have hPm : P = m • G₁ := by
    rw [hP, hGε, hG₁def, hm, ← natCast_zsmul _ (b * n), smul_smul, ← natCast_zsmul G₀ n, smul_smul]
    congr 1
    push_cast
    ring
  have hm0 : ((m : ℤ) : ZMod ℓ) ≠ 0 := by
    haveI : Fact ℓ.Prime := inferInstance
    have hb0 : ((b : ℕ) : ZMod ℓ) ≠ 0 := fun h0 => hb ((ZMod.natCast_eq_zero_iff _ _).mp h0)
    have ha0 : ((aG : ℕ) : ZMod ℓ) ≠ 0 := fun h0 => haGmem.2 ((ZMod.natCast_eq_zero_iff _ _).mp h0)
    have hε0 : ((ε : ℤ) : ZMod ℓ) ≠ 0 := by
      rcases hε with rfl | rfl
      · simp
      · simp
    rw [hm]; push_cast
    exact mul_ne_zero (mul_ne_zero hε0 ha0) hb0

  have hℓP : ℓ • P = 0 := by
    rw [hPm, ← natCast_zsmul, smul_smul, mul_comm, ← smul_smul, hℓG₁, zsmul_zero]
  have hpre : (W.preΨ' ℓ).eval D.xP = 0 :=
    (WeierstrassCurve.Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi W hℓodd hPns).mp (by rw [← hPdef]; exact hℓP)
  refine ⟨⟨hDP, by rw [WeierstrassCurve.preΨ_ofNat]; exact hpre, hDQ.1, hDQ.2⟩, ?_⟩

  rw [hprod]
  apply Finset.prod_dvd_of_coprime
  ·
    intro a ha a' ha' hne
    rw [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Icc] at ha ha'
    apply Polynomial.isCoprime_X_sub_C_of_isUnit_sub
    rw [isUnit_iff_ne_zero, sub_ne_zero]
    intro hxx
    obtain ⟨xa, ya, hans, haQ⟩ := hsome _ (hSne a ha.1.1 ha.1.2)
    obtain ⟨xa', ya', hans', haQ'⟩ := hsome _ (hSne a' ha'.1.1 ha'.1.2)
    rw [haQ, haQ', WeierstrassCurve.Affine.Point.coordsOrZero_some, WeierstrassCurve.Affine.Point.coordsOrZero_some] at hxx
    simp only at hxx
    have hpm : a • G₀ = a' • G₀ ∨ a • G₀ = -(a' • G₀) := by
      rw [haQ, haQ']; exact (WeierstrassCurve.Affine.Point.X_eq_iff).mp hxx
    have hordZ : ∀ z : ℤ, z • G₀ = 0 → (ℓ ^ k : ℤ) ∣ z := by
      intro z hz
      have := (addOrderOf_dvd_iff_zsmul_eq_zero).mpr hz
      rw [hordG₀] at this
      exact_mod_cast this
    have haltN : a < ℓ ^ k := lt_of_le_of_lt ha.1.2 (Nat.div_lt_self (by positivity) one_lt_two)
    have ha'ltN : a' < ℓ ^ k := lt_of_le_of_lt ha'.1.2 (Nat.div_lt_self (by positivity) one_lt_two)
    have halt : (a : ℤ) < (ℓ : ℤ) ^ k := by exact_mod_cast haltN
    have ha'lt : (a' : ℤ) < (ℓ : ℤ) ^ k := by exact_mod_cast ha'ltN
    have hsumN : a + a' < ℓ ^ k := by obtain ⟨t, ht⟩ := hℓkodd; omega
    have hsum : (a : ℤ) + (a' : ℤ) < (ℓ : ℤ) ^ k := by exact_mod_cast hsumN
    apply hne
    rcases hpm with h0 | h0
    ·
      have hz : ((a : ℤ) - (a' : ℤ)) • G₀ = 0 := by
        rw [sub_zsmul, natCast_zsmul, natCast_zsmul, h0]; abel
      have hd := hordZ _ hz
      have := Int.eq_zero_of_abs_lt_dvd hd (abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩)
      omega
    ·
      have hz : ((a : ℤ) + (a' : ℤ)) • G₀ = 0 := by
        rw [add_zsmul, natCast_zsmul, natCast_zsmul, h0]; abel
      have hd := hordZ _ hz
      have := Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_of_nonneg (by positivity)]; exact hsum)
      omega
  ·
    intro a ha
    rw [Finset.mem_filter, Finset.mem_Icc] at ha
    rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot]
    obtain ⟨xa, ya, hans, haQ⟩ := hsome _ (hSne a ha.1.1 ha.1.2)
    rw [haQ, WeierstrassCurve.Affine.Point.coordsOrZero_some]
    simp only

    have haG₁ : (n : ℤ) • WeierstrassCurve.Affine.Point.some xa ya hans = (a : ℤ) • G₁ := by
      rw [← haQ, hG₁def, natCast_zsmul, natCast_zsmul, smul_smul, smul_smul, mul_comm]
    have haG₁ne : (a : ℤ) • G₁ ≠ 0 := by
      intro h0
      have := (addOrderOf_dvd_iff_zsmul_eq_zero).mpr h0
      rw [hordG₁] at this
      exact ha.2 (by exact_mod_cast this)
    obtain ⟨x1, y1, h1ns, h1⟩ := hsome _ haG₁ne
    obtain ⟨hΨn, hxn⟩ := tool xa ya hans n x1 y1 h1ns (by rw [haG₁]; exact h1)

    haveI : Fact ℓ.Prime := inferInstance
    set r : ZMod ℓ := ((a : ℕ) : ZMod ℓ) * (((m : ℤ) : ZMod ℓ))⁻¹ with hr
    have ha0 : ((a : ℕ) : ZMod ℓ) ≠ 0 := fun h0 => ha.2 ((ZMod.natCast_eq_zero_iff _ _).mp h0)
    have hr0 : r ≠ 0 := mul_ne_zero ha0 (inv_ne_zero hm0)
    obtain ⟨c, s, hc1, hc2, hs, hsc⟩ := LW.exists_half_rep ℓ hℓ3 hℓodd r hr0
    have hscm : (((s * c * m : ℤ)) : ZMod ℓ) = ((a : ℕ) : ℤ) := by
      push_cast
      rw [show ((s : ℤ) : ZMod ℓ) * ((c : ℕ) : ZMod ℓ) = r by exact_mod_cast hsc, hr, mul_assoc, inv_mul_cancel₀ hm0, mul_one]
    have hcP : (s * c : ℤ) • P = (a : ℤ) • G₁ := by
      rw [hPm, smul_smul]
      exact hzsmul _ _ (by exact_mod_cast hscm)

    have hcPne : (c : ℤ) • P ≠ 0 := by
      intro h0
      apply haG₁ne
      rw [← hcP, ← smul_smul, h0, zsmul_zero]
    obtain ⟨x2, y2, h2ns, h2⟩ := hsome _ hcPne
    obtain ⟨hΨc, hxc⟩ := tool D.xP D.yP hPns c x2 y2 h2ns (by rw [← hPdef]; exact h2)
    have hx12 : x2 = x1 := by
      rcases hs with rfl | rfl
      · rw [one_mul, h2] at hcP
        rw [h1] at hcP
        simp only [WeierstrassCurve.Affine.Point.some.injEq] at hcP
        exact hcP.1
      · rw [neg_one_mul, neg_zsmul, h2, h1, WeierstrassCurve.Affine.Point.neg_some] at hcP
        simp only [WeierstrassCurve.Affine.Point.some.injEq] at hcP
        exact hcP.1

    have hcmem : c ∈ Finset.Icc 1 ((ℓ - 1) / 2) := Finset.mem_Icc.mpr ⟨hc1, hc2⟩
    unfold ModularCurve.inLineMulPoly
    rw [Polynomial.eval_prod]
    apply Finset.prod_eq_zero hcmem
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
    have e1 : (W.Φ (n : ℤ)).eval xa = x1 * (W.ΨSq (n : ℤ)).eval xa := hxn.symm
    have e2 : (W.Φ (c : ℤ)).eval D.xP = x2 * (W.ΨSq (c : ℤ)).eval D.xP := hxc.symm
    push_cast
    rw [e1, e2, hx12]
    ring

end S_ModularCurve_isGamma1Point_and_dvd_inLineMulPoly_of_toPoint_eq_mul_pow_smul_of_isRoot
end P2MW
export P2MW.S_ModularCurve_isGamma1Point_and_dvd_inLineMulPoly_of_toPoint_eq_mul_pow_smul_of_isRoot (solution)
