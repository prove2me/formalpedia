-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.algEquiv_eq_of_forall_pointEquivPlace_eq_ofAlgAut_smul_of_comp_w_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/76dcbc7e-0ff5-57b0-ba17-532057a22888

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_AlgebraicCurve_IsCurveOver

import Theorems.Thm_AlgebraicCurve_SemilinearAut_eq_of_baseAut_eq_of_forall_smul_place_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_algEquiv_eq_of_forall_pointEquivPlace_eq_ofAlgAut_smul_of_comp_w_eq
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    [Algebra.EssFiniteType (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)] [IsCurveOver (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)]
    (θ θ' : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (hwgen' : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ' • 𝔛.Meta.pointEquivPlace y) :
    θ = θ' := by

  set X := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) with hX
  have hwinv : 𝔛.w.inv ≫ toBase p (ΓM M H) hj = toBase p (ΓM M H) hj := by
    rw [Iso.inv_comp_eq, 𝔛.w_over]
  let winv : X ⟶ X := pullback.lift (pullback.fst _ _ ≫ 𝔛.w.inv) (pullback.snd _ _)
    (by rw [Category.assoc, hwinv, pullback.condition])
  have hwinv_fst : winv ≫ pullback.fst _ _ = pullback.fst _ _ ≫ 𝔛.w.inv := pullback.lift_fst _ _ _
  have hwinv_snd : winv ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  have hinv_base : inv 𝔛.eeta ≫ 𝔛.Meta.toBase = pullback.snd _ _ := by
    rw [IsIso.inv_comp_eq, 𝔛.heeta]

  have key : ∀ v : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      SemilinearAut.ofAlgAut θ • v = SemilinearAut.ofAlgAut θ' • v := by
    intro v
    set y := 𝔛.Meta.pointEquivPlace.symm v with hy
    have hv : v = 𝔛.Meta.pointEquivPlace y := (Equiv.apply_symm_apply _ v).symm
    let q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C := y.1 ≫ 𝔛.eeta ≫ winv ≫ inv 𝔛.eeta
    have hq : q ≫ 𝔛.Meta.toBase = 𝟙 _ := by
      simp only [q, Category.assoc, hinv_base, hwinv_snd]
      rw [𝔛.heeta]
      exact y.2
    have hq' : q ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ := by
      simp only [q, Category.assoc, IsIso.inv_hom_id_assoc]
      rw [← Category.assoc winv, hwinv_fst, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hv, ← hwgen y ⟨q, hq⟩ hq', ← hwgen' y ⟨q, hq⟩ hq']
  have h : SemilinearAut.ofAlgAut θ = SemilinearAut.ofAlgAut θ' :=
    SemilinearAut.eq_of_baseAut_eq_of_forall_smul_place_eq _ _
      (by rw [SemilinearAut.baseAut_ofAlgAut, SemilinearAut.baseAut_ofAlgAut]) key
  apply AlgEquiv.ext
  intro x
  have hx := congrArg (fun g : SemilinearAut (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) => g • x) h
  simpa only [SemilinearAut.ofAlgAut_smul] using hx

#print axioms solution

end S_ModularCurve_XHDRModelAtP_algEquiv_eq_of_forall_pointEquivPlace_eq_ofAlgAut_smul_of_comp_w_eq
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_algEquiv_eq_of_forall_pointEquivPlace_eq_ofAlgAut_smul_of_comp_w_eq (solution)
