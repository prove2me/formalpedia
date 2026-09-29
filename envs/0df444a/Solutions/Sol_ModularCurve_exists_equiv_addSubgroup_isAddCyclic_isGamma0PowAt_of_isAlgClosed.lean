-- Prove2me | solution 1 for ModularCurve.exists_equiv_addSubgroup_isAddCyclic_isGamma0PowAt_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/b38d9c52-6c62-5b35-81e6-06b72147b567

import Mathlib
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
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import Definitions.Def_ModularCurve_WeierstrassGamma0Sqf
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Theorems.Thm_WeierstrassCurve_IsCyclicGenKernel_exists_addOrderOf_eq_and_isRoot
import Theorems.Thm_WeierstrassCurve_IsCyclicGenKernel_eq_prod_X_sub_C_coordsOrZero_nsmul
import Theorems.Thm_WeierstrassCurve_IsTwoKernel_exists_addOrderOf_eq_two_and_eq_X_sub_C
import Theorems.Thm_WeierstrassCurve_isCyclicGenKernel_prod_X_sub_C_coordsOrZero_nsmul_of_addOrderOf_eq_pow
import Theorems.Thm_WeierstrassCurve_isTwoKernel_X_sub_C_coordsOrZero_of_addOrderOf_eq_two
import Theorems.Thm_ModularCurve_IsGamma0PowAt_zmultiples_eq_zmultiples_of_isRoot_of_addOrderOf_eq
import Theorems.Thm_WeierstrassCurve_prod_X_sub_C_coordsOrZero_nsmul_eq_of_zmultiples_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_equiv_addSubgroup_isAddCyclic_isGamma0PowAt_of_isAlgClosed
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂"
p2m_attr_erase "simp" "Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups

theorem solution
    (F : Type) [Field F] [IsAlgClosed F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]
    (p k : ℕ) [Fact p.Prime] (hk : 1 ≤ k) (hpF : ((p : ℕ) : F) ≠ 0) :
    ∃ e : {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = p ^ k} ≃
        {h : Polynomial F // ModularCurve.IsGamma0PowAt W p k h},
      ∀ (H : {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = p ^ k})
        (Q : W.toAffine.Point), AddSubgroup.zmultiples Q = H.1 → p ^ k ≠ 2 →
        ((e H : {h : Polynomial F // ModularCurve.IsGamma0PowAt W p k h}) : Polynomial F) =
          ∏ a ∈ (Finset.Icc 1 (p ^ k / 2)).filter (fun a => ¬ p ∣ a),
            (Polynomial.X - Polynomial.C ((a • Q).coordsOrZero).1) := by
  classical
  let S : Finset ℕ := (Finset.Icc 1 (p ^ k / 2)).filter (fun a => ¬ p ∣ a)
  let prodQ : W.toAffine.Point → Polynomial F := fun Q =>
    ∏ a ∈ S, (Polynomial.X - Polynomial.C ((a • Q).coordsOrZero).1)
  have hpp : p.Prime := Fact.out

  have hgen : ∀ H : {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = p ^ k},
      ∃ Q : W.toAffine.Point, AddSubgroup.zmultiples Q = H.1 ∧ addOrderOf Q = p ^ k := by
    rintro ⟨H, hcyc, hcard⟩
    obtain ⟨Q, hQ⟩ := (AddSubgroup.isAddCyclic_iff_exists_zmultiples_eq_top H).mp hcyc
    refine ⟨Q, hQ, ?_⟩
    rw [← Nat.card_zmultiples, hQ]; exact hcard
  have hmk : ∀ Q : W.toAffine.Point, addOrderOf Q = p ^ k →
      IsAddCyclic (AddSubgroup.zmultiples Q) ∧ Nat.card (AddSubgroup.zmultiples Q) = p ^ k := fun Q hQ =>
    ⟨(AddSubgroup.isAddCyclic_iff_exists_zmultiples_eq_top _).mpr ⟨Q, rfl⟩, by rw [Nat.card_zmultiples, hQ]⟩

  have hsome : ∀ Q : W.toAffine.Point, addOrderOf Q = p ^ k →
      ∃ (x y : F) (hxy : W.toAffine.Nonsingular x y), Q = WeierstrassCurve.Affine.Point.some x y hxy := by
    intro Q hQ
    cases Q with
    | zero =>
      exfalso
      change addOrderOf (0 : W.toAffine.Point) = p ^ k at hQ
      rw [addOrderOf_zero] at hQ
      have : 1 < p ^ k := Nat.one_lt_pow (by omega) hpp.one_lt
      omega
    | some x y hxy => exact ⟨x, y, hxy, rfl⟩
  by_cases h2 : p ^ k = 2
  ·
    have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp (h2 ▸ dvd_pow_self p (by omega))
    have h2F : (2 : F) ≠ 0 := by have := hpF; rw [hp2] at this; exact_mod_cast this
    have hIff2 : ∀ h : Polynomial F, ModularCurve.IsGamma0PowAt W p k h ↔ W.IsTwoKernel h :=
      fun h => ModularCurve.isGamma0PowAt_of_pow_eq_two W h2 h
    let tw : W.toAffine.Point → Polynomial F := fun T => Polynomial.X - Polynomial.C (T.coordsOrZero).1

    have hmem2 : ∀ (T T' : W.toAffine.Point), addOrderOf T = 2 → T' ∈ AddSubgroup.zmultiples T → T' ≠ 0 → T' = T := by
      intro T T' hT hT' hT'0
      obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hT'
      have h2T : (2 : ℤ) • T = 0 := by
        rw [show (2 : ℤ) • T = (2 : ℕ) • T by norm_cast, ← hT]; exact addOrderOf_nsmul_eq_zero T
      obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' n
      · exfalso; apply hT'0
        rw [mul_comm, ← smul_smul, h2T, smul_zero]
      · rw [add_smul, mul_comm, ← smul_smul, h2T, smul_zero, zero_add, one_smul]

    have hx2 : ∀ (T T' : W.toAffine.Point), addOrderOf T = 2 → addOrderOf T' = 2 →
        (T.coordsOrZero).1 = (T'.coordsOrZero).1 → T = T' := by
      intro T T' hT hT' hx
      obtain ⟨x, y, hxy, rfl⟩ := hsome T (h2.symm ▸ hT)
      obtain ⟨x', y', hxy', rfl⟩ := hsome T' (h2.symm ▸ hT')
      simp only [WeierstrassCurve.Affine.Point.coordsOrZero_some] at hx
      subst hx
      rcases WeierstrassCurve.Affine.Y_eq_of_X_eq hxy'.1 hxy.1 rfl with hy | hy
      · subst hy; rfl
      ·
        have hneg : WeierstrassCurve.Affine.Point.some x y' hxy' = -WeierstrassCurve.Affine.Point.some x y hxy := by
          rw [WeierstrassCurve.Affine.Point.neg_some]; congr
        have hTT : -WeierstrassCurve.Affine.Point.some x y hxy = WeierstrassCurve.Affine.Point.some x y hxy := by
          have h0 : (2 : ℕ) • WeierstrassCurve.Affine.Point.some x y hxy = 0 := by rw [← hT]; exact addOrderOf_nsmul_eq_zero _
          rw [two_nsmul] at h0
          exact (neg_eq_of_add_eq_zero_left h0).symm ▸ rfl
        rw [hneg, hTT]
    have hγ : ∀ h : {h : Polynomial F // ModularCurve.IsGamma0PowAt W p k h},
        ∃ T : W.toAffine.Point, addOrderOf T = 2 ∧ h.1 = tw T := fun h =>
      WeierstrassCurve.IsTwoKernel.exists_addOrderOf_eq_two_and_eq_X_sub_C W h2F h.1 ((hIff2 _).mp h.2)
    let g : {h : Polynomial F // ModularCurve.IsGamma0PowAt W p k h} →
        {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = p ^ k} := fun h =>
      ⟨AddSubgroup.zmultiples (hγ h).choose, hmk _ (h2.symm ▸ (hγ h).choose_spec.1)⟩
    have hg_surj : Function.Surjective g := by
      intro H
      obtain ⟨Q, hQH, hQ⟩ := hgen H
      have hQ2 : addOrderOf Q = 2 := h2 ▸ hQ
      have htwQ : ModularCurve.IsGamma0PowAt W p k (tw Q) :=
        (hIff2 _).mpr (WeierstrassCurve.isTwoKernel_X_sub_C_coordsOrZero_of_addOrderOf_eq_two W Q hQ2)
      refine ⟨⟨tw Q, htwQ⟩, Subtype.ext ?_⟩
      show AddSubgroup.zmultiples (hγ ⟨tw Q, htwQ⟩).choose = H.1
      have spec := (hγ ⟨tw Q, htwQ⟩).choose_spec
      have hx : ((hγ ⟨tw Q, htwQ⟩).choose.coordsOrZero).1 = (Q.coordsOrZero).1 := by
        have h' : Polynomial.C (Q.coordsOrZero).1 = Polynomial.C ((hγ ⟨tw Q, htwQ⟩).choose.coordsOrZero).1 :=
          sub_right_inj.mp spec.2
        exact (Polynomial.C_inj.mp h').symm
      rw [hx2 _ _ spec.1 hQ2 hx, hQH]
    have hg_inj : Function.Injective g := by
      intro h₁ h₂ heq
      have s₁ := (hγ h₁).choose_spec
      have s₂ := (hγ h₂).choose_spec
      have hz : AddSubgroup.zmultiples (hγ h₁).choose = AddSubgroup.zmultiples (hγ h₂).choose := congrArg Subtype.val heq
      have hne : (hγ h₂).choose ≠ 0 := by
        intro h0; have := s₂.1; rw [h0] at this
        change addOrderOf (0 : W.toAffine.Point) = 2 at this
        rw [addOrderOf_zero] at this; omega
      have : (hγ h₂).choose = (hγ h₁).choose :=
        hmem2 _ _ s₁.1 (hz ▸ AddSubgroup.mem_zmultiples _) hne
      apply Subtype.ext
      rw [s₁.2, s₂.2, this]
    refine ⟨(Equiv.ofBijective g ⟨hg_inj, hg_surj⟩).symm, ?_⟩
    intro H Q hQH hne2
    exact absurd h2 hne2
  ·
    have hpk3 : 3 ≤ p ^ k := by
      have h1 : 2 ≤ p ^ k := le_trans hpp.two_le (Nat.le_self_pow (by omega) p)
      omega
    have hIff : ∀ h : Polynomial F, ModularCurve.IsGamma0PowAt W p k h ↔ W.IsCyclicGenKernel p k h :=
      fun h => ModularCurve.isGamma0PowAt_of_pow_ne_two W h2 h
    have hfwd : ∀ Q : W.toAffine.Point, addOrderOf Q = p ^ k → ModularCurve.IsGamma0PowAt W p k (prodQ Q) := fun Q hQ =>
      (hIff _).mpr (WeierstrassCurve.isCyclicGenKernel_prod_X_sub_C_coordsOrZero_nsmul_of_addOrderOf_eq_pow W p k h2 Q hQ)
    have h1S : 1 ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨le_rfl, by omega⟩, hpp.not_dvd_one⟩
    have hroot : ∀ (x y : F) (hxy : W.toAffine.Nonsingular x y),
        (prodQ (WeierstrassCurve.Affine.Point.some x y hxy)).IsRoot x := by
      intro x y hxy
      simp only [prodQ]
      rw [Polynomial.isRoot_prod]
      exact ⟨1, h1S, by simp [WeierstrassCurve.Affine.Point.coordsOrZero_some]⟩
    have hα : ∀ h : {h : Polynomial F // ModularCurve.IsGamma0PowAt W p k h},
        ∃ (x y : F) (hxy : W.toAffine.Nonsingular x y),
          addOrderOf (WeierstrassCurve.Affine.Point.some x y hxy) = p ^ k ∧ h.1.IsRoot x := fun h =>
      WeierstrassCurve.IsCyclicGenKernel.exists_addOrderOf_eq_and_isRoot W p k hpF hpk3 h.1 ((hIff _).mp h.2)
    let pt : {h : Polynomial F // ModularCurve.IsGamma0PowAt W p k h} → W.toAffine.Point := fun h =>
      WeierstrassCurve.Affine.Point.some (hα h).choose (hα h).choose_spec.choose (hα h).choose_spec.choose_spec.choose
    have hpt : ∀ h, addOrderOf (pt h) = p ^ k ∧ h.1.IsRoot (hα h).choose := fun h =>
      (hα h).choose_spec.choose_spec.choose_spec
    let g : {h : Polynomial F // ModularCurve.IsGamma0PowAt W p k h} →
        {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = p ^ k} := fun h =>
      ⟨AddSubgroup.zmultiples (pt h), hmk _ (hpt h).1⟩

    have hg : ∀ (Q : W.toAffine.Point) (hQ : addOrderOf Q = p ^ k),
        (g ⟨prodQ Q, hfwd Q hQ⟩).1 = AddSubgroup.zmultiples Q := by
      intro Q hQ
      obtain ⟨xQ, yQ, hxyQ, rfl⟩ := hsome Q hQ
      show AddSubgroup.zmultiples (pt _) = _
      have spec := hpt ⟨prodQ _, hfwd _ hQ⟩
      exact ModularCurve.IsGamma0PowAt.zmultiples_eq_zmultiples_of_isRoot_of_addOrderOf_eq W p k hpF _ (hfwd _ hQ)
        _ _ _ _ _ hxyQ spec.1 hQ spec.2 (hroot xQ yQ hxyQ)
    have hg_surj : Function.Surjective g := by
      intro H
      obtain ⟨Q, hQH, hQ⟩ := hgen H
      exact ⟨⟨prodQ Q, hfwd Q hQ⟩, Subtype.ext (by rw [hg Q hQ, hQH])⟩
    have hg_inj : Function.Injective g := by
      intro h₁ h₂ heq
      have s₁ := hpt h₁
      have s₂ := hpt h₂
      have e₁ := WeierstrassCurve.IsCyclicGenKernel.eq_prod_X_sub_C_coordsOrZero_nsmul W p k hpF hpk3 h₁.1 ((hIff _).mp h₁.2)
        (pt h₁) s₁.1 ⟨_, _, _, rfl, s₁.2⟩
      have e₂ := WeierstrassCurve.IsCyclicGenKernel.eq_prod_X_sub_C_coordsOrZero_nsmul W p k hpF hpk3 h₂.1 ((hIff _).mp h₂.2)
        (pt h₂) s₂.1 ⟨_, _, _, rfl, s₂.2⟩
      apply Subtype.ext
      rw [e₁, e₂]
      exact WeierstrassCurve.prod_X_sub_C_coordsOrZero_nsmul_eq_of_zmultiples_eq W p k h2 _ _ s₁.1 s₂.1
        (congrArg Subtype.val heq)
    refine ⟨(Equiv.ofBijective g ⟨hg_inj, hg_surj⟩).symm, ?_⟩
    intro H Q hQH _
    have hQ : addOrderOf Q = p ^ k := by rw [← Nat.card_zmultiples, hQH]; exact H.2.2
    have hgH : g ⟨prodQ Q, hfwd Q hQ⟩ = H := Subtype.ext (by rw [hg Q hQ, hQH])
    have : (Equiv.ofBijective g ⟨hg_inj, hg_surj⟩).symm H = ⟨prodQ Q, hfwd Q hQ⟩ := by
      rw [Equiv.symm_apply_eq]; exact hgH.symm
    rw [this]

end S_ModularCurve_exists_equiv_addSubgroup_isAddCyclic_isGamma0PowAt_of_isAlgClosed
end P2MW
export P2MW.S_ModularCurve_exists_equiv_addSubgroup_isAddCyclic_isGamma0PowAt_of_isAlgClosed (solution)
