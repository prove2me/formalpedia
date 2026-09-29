-- Prove2me | solution 1 for ModularCurve.IsLevelPStructure.relabel_of_isUnit_det
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/170d9e45-c9a7-5e2a-ba19-a162e283b3fb

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelRelabelling
import Theorems.Thm_ModularCurve_indepElt_eq_zero_iff_mem_zmultiples
import Theorems.Thm_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IsLevelPStructure_relabel_of_isUnit_det
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two"
p2m_attr_erase "simp" "compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

universe u

p2m_open "ModularCurve P2MW.S_ModularCurve_IsLevelPStructure_relabel_of_isUnit_det.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "LevelPData IsLevelPStructure LevelRelabelling.toPoint LevelRelabelling.LevelPData.relabel indepElt_eq_zero_iff_mem_zmultiples"
namespace KatzRelabel
p2m_open "ModularCurve"

open scoped Classical

variable {F : Type u} [Field F]

theorem some_eq_some {W : WeierstrassCurve F} {x y x' y' : F} (h : W.toAffine.Nonsingular x y)
    (h' : W.toAffine.Nonsingular x' y') (hx : x = x') (hy : y = y') :
    WeierstrassCurve.Affine.Point.some x y h = WeierstrassCurve.Affine.Point.some x' y' h' := by
  subst hx hy; rfl

theorem comb_sub_comb {W : WeierstrassCurve F} (P Q : W.toAffine.Point) (a b c d : ℤ)
    (h : a • P + b • Q = c • P + d • Q) : (a - c) • P + (b - d) • Q = 0 := by
  have : (a - c) • P + (b - d) • Q = (a • P + b • Q) - (c • P + d • Q) := by
    simp only [sub_smul]; abel
  rw [this, h, sub_self]

theorem dvd_of_comb_eq_zero {W : WeierstrassCurve F} {ℓ : ℕ} [Fact ℓ.Prime] {P Q : W.toAffine.Point}
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

end ModularCurve.KatzRelabel

open scoped Classical in
open ModularCurve.KatzRelabel in

theorem solution
    {F : Type u} [Field F] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓF : (ℓ : F) ≠ 0)
    (W : WeierstrassCurve F) (hΔ : IsUnit W.Δ) (D : LevelPData F) (hD : IsLevelPStructure W ℓ D)
    (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : IsUnit ((g.det : ℤ) : ZMod ℓ)) :
    IsLevelPStructure W ℓ (LevelRelabelling.LevelPData.relabel W g D) := by
  have hp : ℓ.Prime := Fact.out
  haveI : NeZero ℓ := ⟨hp.ne_zero⟩
  have hℓ2 : ℓ ≠ 2 := by omega
  have hodd : Odd ℓ := hp.odd_of_ne_two hℓ2
  haveI : W.IsElliptic := ⟨hΔ⟩

  have nP := W.toAffine.equation_iff_nonsingular.mp hD.equation_P
  have nQ := W.toAffine.equation_iff_nonsingular.mp hD.equation_Q
  have tors : ∀ {x y : F} (nxy : W.toAffine.Nonsingular x y),
      (W.preΨ ℓ).eval x = 0 → ℓ • WeierstrassCurve.Affine.Point.some _ _ nxy = 0 := by
    intro x y nxy hx
    rw [WeierstrassCurve.preΨ_ofNat] at hx
    exact (WeierstrassCurve.Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi W hodd nxy).mpr hx
  set P₁ := WeierstrassCurve.Affine.Point.some _ _ nP with hP₁
  set Q₁ := WeierstrassCurve.Affine.Point.some _ _ nQ with hQ₁
  have tP : ℓ • P₁ = 0 := tors nP hD.preΨ_P
  have tQ : ℓ • Q₁ = 0 := tors nQ hD.preΨ_Q
  have hP0 : P₁ ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero _
  have hQ0 : Q₁ ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero _
  have hQP : Q₁ ∉ AddSubgroup.zmultiples P₁ := fun hmem =>
    hD.isUnit_indepElt_PQ.ne_zero ((ModularCurve.indepElt_eq_zero_iff_mem_zmultiples hℓ2 nP nQ tP).mpr hmem)
  have hPQ : P₁ ∉ AddSubgroup.zmultiples Q₁ := fun hmem =>
    hD.isUnit_indepElt_QP.ne_zero ((ModularCurve.indepElt_eq_zero_iff_mem_zmultiples hℓ2 nQ nP tQ).mpr hmem)
  have indep := dvd_of_comb_eq_zero (W := W) (ℓ := ℓ) tP tQ hP0 hQP

  have hdet : ¬ (ℓ : ℤ) ∣ g.det := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hg.ne_zero
  have hdet2 : g.det = g 0 0 * g 1 1 - g 0 1 * g 1 0 := Matrix.det_fin_two g

  have htoP : ModularCurve.LevelRelabelling.toPoint W D.xP D.yP = P₁ := dif_pos nP
  have htoQ : ModularCurve.LevelRelabelling.toPoint W D.xQ D.yQ = Q₁ := dif_pos nQ
  set P' : W.toAffine.Point := g 0 0 • P₁ + g 1 0 • Q₁ with hP'def
  set Q' : W.toAffine.Point := g 0 1 • P₁ + g 1 1 • Q₁ with hQ'def
  have hP'0 : P' ≠ 0 := by
    intro h0
    obtain ⟨h1, h2⟩ := indep _ _ h0
    apply hdet; rw [hdet2]
    exact dvd_sub (dvd_mul_of_dvd_left h1 _) (dvd_mul_of_dvd_right h2 _)
  have hQ'0 : Q' ≠ 0 := by
    intro h0
    obtain ⟨h1, h2⟩ := indep _ _ h0
    apply hdet; rw [hdet2]
    exact dvd_sub (dvd_mul_of_dvd_right h2 _) (dvd_mul_of_dvd_left h1 _)
  obtain ⟨xP', yP', nP', hP'eq⟩ : ∃ (x y : F) (h : W.toAffine.Nonsingular x y),
      P' = WeierstrassCurve.Affine.Point.some _ _ h := by
    rcases hh : P' with _ | ⟨x, y, h⟩
    · exact absurd (hh ▸ WeierstrassCurve.Affine.Point.zero_def.symm) hP'0
    · exact ⟨x, y, h, rfl⟩
  obtain ⟨xQ', yQ', nQ', hQ'eq⟩ : ∃ (x y : F) (h : W.toAffine.Nonsingular x y),
      Q' = WeierstrassCurve.Affine.Point.some _ _ h := by
    rcases hh : Q' with _ | ⟨x, y, h⟩
    · exact absurd (hh ▸ WeierstrassCurve.Affine.Point.zero_def.symm) hQ'0
    · exact ⟨x, y, h, rfl⟩
  have hrel : ModularCurve.LevelRelabelling.LevelPData.relabel W g D = ⟨xP', yP', xQ', yQ'⟩ := by
    unfold ModularCurve.LevelRelabelling.LevelPData.relabel
    simp only [htoP, htoQ]
    rw [← hP'def, ← hQ'def, hP'eq, hQ'eq]
    rfl
  rw [hrel]

  have tcomb : ∀ a b : ℤ, ℓ • (a • P₁ + b • Q₁) = 0 := by
    intro a b
    rw [nsmul_add, smul_comm ℓ a P₁, smul_comm ℓ b Q₁, tP, tQ, smul_zero, smul_zero, add_zero]
  have tP' : ℓ • WeierstrassCurve.Affine.Point.some _ _ nP' = 0 := by rw [← hP'eq, hP'def]; exact tcomb _ _
  have tQ' : ℓ • WeierstrassCurve.Affine.Point.some _ _ nQ' = 0 := by rw [← hQ'eq, hQ'def]; exact tcomb _ _

  have hQ'P' : WeierstrassCurve.Affine.Point.some _ _ nQ' ∉ AddSubgroup.zmultiples (WeierstrassCurve.Affine.Point.some _ _ nP') := by
    rw [← hP'eq, ← hQ'eq]
    rintro ⟨m, hm⟩

    have e : (m * g 0 0) • P₁ + (m * g 1 0) • Q₁ = g 0 1 • P₁ + g 1 1 • Q₁ := by
      rw [← smul_smul, ← smul_smul, ← smul_add]; exact hm
    obtain ⟨h1, h2⟩ := indep _ _ (comb_sub_comb P₁ Q₁ _ _ _ _ e)
    apply hdet; rw [hdet2]
    have : g 0 0 * g 1 1 - g 0 1 * g 1 0 = -(g 0 0 * (m * g 1 0 - g 1 1)) + g 1 0 * (m * g 0 0 - g 0 1) := by ring
    rw [this]
    exact dvd_add (dvd_neg.mpr (dvd_mul_of_dvd_right h2 _)) (dvd_mul_of_dvd_right h1 _)
  have hP'Q' : WeierstrassCurve.Affine.Point.some _ _ nP' ∉ AddSubgroup.zmultiples (WeierstrassCurve.Affine.Point.some _ _ nQ') := by
    rw [← hP'eq, ← hQ'eq]
    rintro ⟨m, hm⟩
    have e : (m * g 0 1) • P₁ + (m * g 1 1) • Q₁ = g 0 0 • P₁ + g 1 0 • Q₁ := by
      rw [← smul_smul, ← smul_smul, ← smul_add]; exact hm
    obtain ⟨h1, h2⟩ := indep _ _ (comb_sub_comb P₁ Q₁ _ _ _ _ e)
    apply hdet; rw [hdet2]
    have : g 0 0 * g 1 1 - g 0 1 * g 1 0 = -((m * g 0 1 - g 0 0) * g 1 1) + g 0 1 * (m * g 1 1 - g 1 0) := by ring
    rw [this]
    exact dvd_add (dvd_neg.mpr (dvd_mul_of_dvd_left h1 _)) (dvd_mul_of_dvd_right h2 _)
  refine ⟨nP'.1, nQ'.1, ?_, ?_, ?_, ?_⟩
  · rw [WeierstrassCurve.preΨ_ofNat]
    exact (WeierstrassCurve.Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi W hodd nP').mp tP'
  · rw [WeierstrassCurve.preΨ_ofNat]
    exact (WeierstrassCurve.Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi W hodd nQ').mp tQ'
  · exact isUnit_iff_ne_zero.mpr fun h0 =>
      hQ'P' ((ModularCurve.indepElt_eq_zero_iff_mem_zmultiples hℓ2 nP' nQ' tP').mp h0)
  · exact isUnit_iff_ne_zero.mpr fun h0 =>
      hP'Q' ((ModularCurve.indepElt_eq_zero_iff_mem_zmultiples hℓ2 nQ' nP' tQ').mp h0)

end S_ModularCurve_IsLevelPStructure_relabel_of_isUnit_det
end P2MW
export P2MW.S_ModularCurve_IsLevelPStructure_relabel_of_isUnit_det (solution)
