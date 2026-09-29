-- Prove2me | solution 1 for ModularCurve.Gamma0Pair.cyclicQuotientJ_zmultiples_smul_gen_eq_of_mk_eq_mk
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/030af9b6-17ef-57fa-ad9e-13d03cee9d2d

import Mathlib
import Definitions.Def_ModularCurve_ModuliPoint
import Definitions.Def_WeierstrassCurve_CyclicQuotientJ
import Theorems.Thm_ModularCurve_ModuliPoint_mk_eq_mk_iff_step
import Theorems.Thm_WeierstrassCurve_cyclicQuotientJ_variableChange_eq
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_Gamma0Pair_cyclicQuotientJ_zmultiples_smul_gen_eq_of_mk_eq_mk

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine ModularCurve

universe u

namespace ClassJ

variable {L : Type u} [Field L] [DecidableEq L]

noncomputable def vcAddEquiv (γ : VariableChange L) (E : WeierstrassCurve L) :
    E.toAffine.Point ≃+ (γ • E).toAffine.Point where
  toFun := Point.vcInvFun γ E.toAffine
  invFun := Point.vcFun γ E.toAffine
  left_inv := Point.vcFun_rightInverse
  right_inv := Point.vcFun_leftInverse
  map_add' := Point.vcInvFun_add γ E.toAffine

@[scoped simp] theorem vcAddEquiv_apply (γ : VariableChange L) (E : WeierstrassCurve L) (R : E.toAffine.Point) :
    vcAddEquiv γ E R = Point.vcInvFun γ E.toAffine R := rfl

@[scoped simp] theorem vcAddEquiv_symm_apply (γ : VariableChange L) (E : WeierstrassCurve L) (R : (γ • E).toAffine.Point) :
    (vcAddEquiv γ E).symm R = Point.vcFun γ E.toAffine R := rfl

theorem zmultiples_nsmul_eq_of_coprime {A : Type*} [AddGroup A] (a : A) {k : ℕ} (hk : k.Coprime (addOrderOf a)) :
    AddSubgroup.zmultiples (k • a) = AddSubgroup.zmultiples a := by
  apply le_antisymm
  · exact AddSubgroup.zmultiples_le_of_mem (AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples a) k)
  · obtain ⟨m, hm⟩ := exists_nsmul_eq_self_of_coprime hk
    apply AddSubgroup.zmultiples_le_of_mem
    have h3 : m • (k • a) ∈ AddSubgroup.zmultiples (k • a) := AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples (k • a)) m
    rwa [hm] at h3

end ClassJ
p2m_reactivate "P2MW.S_ModularCurve_Gamma0Pair_cyclicQuotientJ_zmultiples_smul_gen_eq_of_mk_eq_mk.ClassJ"

open ClassJ in
theorem solution
    {L : Type u} [Field L] [DecidableEq L] {N : ℕ} [NeZero N] (hN : (N : L) ≠ 0)
    (P Q : ModularCurve.Gamma0Pair N L)
    (h : (Quot.mk _ P : ModularCurve.ModuliPoint N L) = Quot.mk _ Q)
    (d : ℕ) (hd : d ∣ N) :
    P.toCurve.cyclicQuotientJ (AddSubgroup.zmultiples ((N / d) • P.gen)) d =
      Q.toCurve.cyclicQuotientJ (AddSubgroup.zmultiples ((N / d) • Q.gen)) d := by
  classical
  rw [ModuliPoint.mk_eq_mk_iff_step] at h
  obtain ⟨γ, hγ, k, hk, hgen⟩ := h
  obtain ⟨cQ, eQ, gQ, oQ⟩ := Q
  simp only at hγ hgen ⊢
  subst hγ
  have hgQ : gQ = k • Point.vcInvFun γ P.toCurve.toAffine P.gen := eq_of_heq hgen
  subst hgQ
  have hdL : (d : L) ≠ 0 := by
    intro h0
    apply hN
    obtain ⟨m, rfl⟩ := hd
    rw [Nat.cast_mul, h0, zero_mul]
  symm
  apply cyclicQuotientJ_variableChange_eq γ P.toCurve (AddSubgroup.zmultiples ((N / d) • P.gen)) _ ?_ d hdL

  intro R
  set e := vcAddEquiv γ P.toCurve with he
  have h1 : (N / d) • (k • Point.vcInvFun γ P.toCurve.toAffine P.gen) = e (k • ((N / d) • P.gen)) := by
    rw [smul_comm k (N / d) P.gen, map_nsmul, map_nsmul]
    rfl
  have hcop : k.Coprime (addOrderOf ((N / d) • P.gen)) :=
    Nat.Coprime.coprime_dvd_right ((addOrderOf_smul_dvd (N / d)).trans (dvd_of_eq P.addOrderOf_gen)) hk
  have h2 : R ∈ AddSubgroup.zmultiples (e (k • ((N / d) • P.gen))) ↔
      e.symm R ∈ AddSubgroup.zmultiples (k • ((N / d) • P.gen)) := by
    simp only [AddSubgroup.mem_zmultiples_iff]
    constructor
    · rintro ⟨z, hz⟩
      exact ⟨z, by rw [← hz, map_zsmul, AddEquiv.symm_apply_apply]⟩
    · rintro ⟨z, hz⟩
      exact ⟨z, by rw [← map_zsmul, hz, AddEquiv.apply_symm_apply]⟩
  rw [h1, h2, zmultiples_nsmul_eq_of_coprime _ hcop, he, vcAddEquiv_symm_apply]

end S_ModularCurve_Gamma0Pair_cyclicQuotientJ_zmultiples_smul_gen_eq_of_mk_eq_mk
end P2MW
export P2MW.S_ModularCurve_Gamma0Pair_cyclicQuotientJ_zmultiples_smul_gen_eq_of_mk_eq_mk (solution)
