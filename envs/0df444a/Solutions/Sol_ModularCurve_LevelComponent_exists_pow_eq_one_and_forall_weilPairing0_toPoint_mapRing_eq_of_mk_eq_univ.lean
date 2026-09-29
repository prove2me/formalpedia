-- Prove2me | solution 1 for ModularCurve.LevelComponent.exists_pow_eq_one_and_forall_weilPairing0_toPoint_mapRing_eq_of_mk_eq_univ
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/f596b251-aad6-50d3-92e6-d3a8683e7469

import Mathlib
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_EllipticCurve_WeilPairingFun
import Definitions.Def_ModularCurve_KatzLevelP
import Theorems.Thm_ModularCurve_LevelComponent_exists_not_mem_and_exists_pow_eq_one_forall_weilPairing0_toPoint_mapRing_localizationAway_eq
import Theorems.Thm_Algebra_exists_pow_eq_one_and_forall_algHom_apply_eq_of_locally_of_isUnit_natCast
import Theorems.Thm_WeierstrassCurve_Affine_weilPairing0_toPoint_variableChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LevelComponent_exists_pow_eq_one_and_forall_weilPairing0_toPoint_mapRing_eq_of_mk_eq_univ
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂"
p2m_attr_erase "simp" "Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero"

set_option autoImplicit false

universe u

open ModularCurve

namespace P2M
namespace WeilUniv

theorem exists_eq_act {A : Type u} [CommRing A] (R : ModularCurve.RigidWeierstrassData.{u} A)
    {B : Type u} [CommRing B] [Algebra A B] (u₀ u : R.Raw B) (h : (Quot.mk _ u : R.Pt B) = Quot.mk _ u₀) :
    ∃ C : WeierstrassCurve.VariableChange B, u = R.act C u₀ := by
  have hequiv : Equivalence (R.Rel (T := B)) := by
    refine ⟨ModularCurve.RigidWeierstrassData.Rel.refl R, ?_, ModularCurve.RigidWeierstrassData.Rel.trans R⟩
    rintro a b ⟨C, rfl⟩
    refine ⟨C⁻¹, ?_⟩
    rw [← R.act_mul, inv_mul_cancel, R.act_one]
  exact hequiv.eqvGen_iff.mp (Quot.eq.mp h.symm)

end P2M.WeilUniv

open P2M.WeilUniv in
theorem solution
    (A₀ : Type u) [CommRing A₀] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓA : IsUnit ((ℓ : ℕ) : A₀))
    (hℓ : ∀ (T : Type u) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (L₁ L₃ : ModularCurve.LevelComponent.{u} A₀)
    (P₀ : LevelModuliPackageAbs A₀ (L₁.prod ((levelPComponent A₀ ℓ hℓ).prod L₃)).toRigid.toLevelModuliDatum) :
    ∃ ε : P₀.B₀, ε ^ ℓ = 1 ∧
      ∀ (u : (L₁.prod ((levelPComponent A₀ ℓ hℓ).prod L₃)).Raw P₀.B₀),
        (Quot.mk _ u : (L₁.prod ((levelPComponent A₀ ℓ hℓ).prod L₃)).toRigid.Pt P₀.B₀) = P₀.univ →
        ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω] [Algebra A₀ Ω] (φ : P₀.B₀ →ₐ[A₀] Ω),
          (letI x := (L₁.prod ((levelPComponent A₀ ℓ hℓ).prod L₃)).toRigid.mapRing φ u;
           letI _ : (x.curve).IsElliptic := ⟨x.isUnit_Δ⟩;
            ((WeierstrassCurve.Affine.weilPairing0 (x.curve) Ω (ℓ : ℤ)
                (ModularCurve.LevelRelabelling.toPoint ((x.curve).baseChange Ω) (x.level.2.1).xP (x.level.2.1).yP)
                (ModularCurve.LevelRelabelling.toPoint ((x.curve).baseChange Ω) (x.level.2.1).xQ (x.level.2.1).yQ) : Ωˣ) :
              Ω)) = φ ε := by

  let R : ModularCurve.RigidWeierstrassData.{u} A₀ := (L₁.prod ((levelPComponent A₀ ℓ hℓ).prod L₃)).toRigid
  let V : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω] [Algebra A₀ Ω],
      (L₁.prod ((levelPComponent A₀ ℓ hℓ).prod L₃)).Raw Ω → Ω :=
    fun Ω _ _ _ _ x =>
      letI _ : (x.curve).IsElliptic := ⟨x.isUnit_Δ⟩
      ((WeierstrassCurve.Affine.weilPairing0 (x.curve) Ω (ℓ : ℤ)
          (ModularCurve.LevelRelabelling.toPoint ((x.curve).baseChange Ω) (x.level.2.1).xP (x.level.2.1).yP)
          (ModularCurve.LevelRelabelling.toPoint ((x.curve).baseChange Ω) (x.level.2.1).xQ (x.level.2.1).yQ) : Ωˣ) : Ω)

  obtain ⟨u₀, hu₀⟩ := Quot.exists_rep P₀.univ

  have hℓB : IsUnit ((ℓ : ℕ) : P₀.B₀) := by
    have h := hℓA.map (algebraMap A₀ P₀.B₀)
    rwa [map_natCast] at h
  obtain ⟨ε, hεℓ, hε⟩ :=
    Algebra.exists_pow_eq_one_and_forall_algHom_apply_eq_of_locally_of_isUnit_natCast A₀ P₀.B₀ ℓ hℓB
      (fun Ω _ _ _ _ φ => V Ω (R.mapRing φ u₀))
      (fun 𝔭 _ =>
        ModularCurve.LevelComponent.exists_not_mem_and_exists_pow_eq_one_forall_weilPairing0_toPoint_mapRing_localizationAway_eq
          A₀ ℓ hℓ3 hℓA hℓ L₁ L₃ P₀.B₀ u₀ 𝔭)
  refine ⟨ε, hεℓ, ?_⟩
  intro u hu Ω _ _ _ _ φ

  obtain ⟨C, rfl⟩ := exists_eq_act R u₀ u (hu.trans hu₀.symm)

  show V Ω (R.mapRing φ (R.act C u₀)) = φ ε
  rw [R.mapRing_act φ C u₀, ← hε Ω φ]

  have hℓΩ : ((ℓ : ℕ) : Ω) ≠ 0 := by
    have h := hℓA.map (algebraMap A₀ Ω)
    rw [map_natCast] at h
    exact h.ne_zero
  haveI hwE : ((R.mapRing φ u₀).curve).IsElliptic := ⟨(R.mapRing φ u₀).isUnit_Δ⟩
  haveI hCwE : ((C.map φ.toRingHom) • (R.mapRing φ u₀).curve).IsElliptic :=
    ⟨(R.act (C.map φ.toRingHom) (R.mapRing φ u₀)).isUnit_Δ⟩
  have iso := WeierstrassCurve.Affine.weilPairing0_toPoint_variableChange (K := Ω)
    ((R.mapRing φ u₀).curve) (C.map φ.toRingHom) ℓ hℓ3 hℓΩ
    ((R.mapRing φ u₀).level.2.1) ((R.mapRing φ u₀).isLevel.2.1)
  exact congrArg (fun z : Ωˣ => (z : Ω)) iso

end S_ModularCurve_LevelComponent_exists_pow_eq_one_and_forall_weilPairing0_toPoint_mapRing_eq_of_mk_eq_univ
end P2MW
export P2MW.S_ModularCurve_LevelComponent_exists_pow_eq_one_and_forall_weilPairing0_toPoint_mapRing_eq_of_mk_eq_univ (solution)
