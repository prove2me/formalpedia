-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_forall_eq_map_dualNumber_smul_of_trivial_gamma0Pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/a33cea7f-ecc2-50ab-b1db-6837f83212e5

import Mathlib
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Theorems.Thm_ModularCurve_IsGamma0PowAt_existsUnique_tuple_map_eq_of_surjective_of_ker_pow_eq_bot
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Theorems.Thm_ModularCurve_IsLevelPStructure_existsUnique_map_eq_of_surjective_of_ker_pow_eq_bot
import Theorems.Thm_WeierstrassCurve_exists_map_eq_and_forall_variableChange_smul_map_ne
import Theorems.Thm_WeierstrassCurve_exists_variableChange_smul_map_eq_of_forall_variableChange_smul_ne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_forall_eq_map_dualNumber_smul_of_trivial_gamma0Pow
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Generic.isElliptic_curve ModularCurve.LevelP.instCommRingUnivBase ModularCurve.LevelP.instAwayMvPolynomialFinOfNatNatIntPDeltaUnivBase ModularCurve.LevelP.instCommRingTorsionPointRing ModularCurve.LevelP.instCommRingPsiRoot ModularCurve.LevelP.instIsScalarTowerTwoPointRingBasisRing ModularCurve.LevelP.instAlgebraPsiRoot ModularCurve.LevelP.instIsScalarTowerPsiRootTorsionPointRing ModularCurve.LevelP.instAlgebraMvPolynomialFinOfNatNatIntUnivBase ModularCurve.LevelP.instAlgebraTwoPointRing ModularCurve.LevelP.instIsScalarTowerTorsionPointRingTwoPointRing ModularCurve.LevelP.instAwayTwoPointRingIndepDenomBasisRing ModularCurve.LevelP.instCommRingBasisRing ModularCurve.LevelP.instAlgebraTorsionPointRing ModularCurve.LevelP.instAlgebraPsiRootTorsionPointRing ModularCurve.LevelP.instAlgebraBasisRing ModularCurve.LevelP.instAlgebraTwoPointRingBasisRing"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Generic.poly_map_classify WeierstrassCurve.Generic.poly_a₆ WeierstrassCurve.Generic.poly_a₁ WeierstrassCurve.Generic.classify_X WeierstrassCurve.Generic.coeffs_two WeierstrassCurve.Generic.coeffs_one WeierstrassCurve.Generic.curve_a₄"
p2m_attr_erase "simp" "WeierstrassCurve.Generic.coeffs_three WeierstrassCurve.Generic.poly_a₄ WeierstrassCurve.Generic.poly_a₃ WeierstrassCurve.Generic.poly_a₂ WeierstrassCurve.Generic.coeffs_zero WeierstrassCurve.Generic.curve_a₂ WeierstrassCurve.Generic.coeffs_four WeierstrassCurve.Generic.curve_a₆ WeierstrassCurve.Generic.curve_a₁ WeierstrassCurve.Generic.curve_a₃ ModularCurve.KatzLevelPForm.evalUniv_neg ModularCurve.KatzLevelPForm.evalUniv_mul ModularCurve.KatzLevelPForm.evalUniv_zero ModularCurve.KatzLevelPForm.evalUniv_sub ModularCurve.KatzLevelPForm.evalUniv_add"

set_option autoImplicit false

open ModularCurve

theorem solution
    (ℓ M' : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) [NeZero M']
    (A₀ : Type) [CommRing A₀]
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (k : Type) [Field k] [Algebra A₀ k] (hℓk : ((ℓ : ℕ) : k) ≠ 0) (hM'k : ((M' : ℕ) : k) ≠ 0)
    (x₀ : (((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).toLevelModuliDatum.Pt k) :
    ∃ y₁ : (((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).toLevelModuliDatum.Pt (DualNumber k),
      (((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).toLevelModuliDatum.map
          ((TrivSqZeroExt.fstHom k k k).restrictScalars A₀) y₁ = x₀ ∧
      y₁ ≠ (((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).toLevelModuliDatum.map
          ((TrivSqZeroExt.inlAlgHom k k k).restrictScalars A₀) x₀ ∧
      ∀ y : (((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).toLevelModuliDatum.Pt (DualNumber k),
        (((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).toLevelModuliDatum.map
            ((TrivSqZeroExt.fstHom k k k).restrictScalars A₀) y = x₀ →
        ∃ c : k, y = (((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).toLevelModuliDatum.map
            ((TrivSqZeroExt.map (c • (LinearMap.id : k →ₗ[k] k))).restrictScalars A₀) y₁ := by
  classical
  obtain ⟨X₀, rfl⟩ := Quot.exists_rep x₀
  set fstA : DualNumber k →ₐ[A₀] k := (TrivSqZeroExt.fstHom k k k).restrictScalars A₀ with hfstA
  set inlA : k →ₐ[A₀] DualNumber k := (TrivSqZeroExt.inlAlgHom k k k).restrictScalars A₀ with hinlA
  have hfst_toRingHom : fstA.toRingHom = (TrivSqZeroExt.fstHom k k k).toRingHom := rfl
  have hinl_toRingHom : inlA.toRingHom = algebraMap k (DualNumber k) := RingHom.ext fun a => rfl
  have hsc_toRingHom : ∀ c : k, ((TrivSqZeroExt.map (c • (LinearMap.id : k →ₗ[k] k))).restrictScalars A₀ :
      DualNumber k →ₐ[A₀] DualNumber k).toRingHom = (TrivSqZeroExt.map (c • (LinearMap.id : k →ₗ[k] k))).toRingHom :=
    fun c => rfl
  have hℓ2 : ℓ ≠ 2 := by omega

  have hsurj : Function.Surjective (TrivSqZeroExt.fstHom k k k).toRingHom :=
    fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  have hnil : ∃ n : ℕ, RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom ^ n = ⊥ := by
    refine ⟨2, ?_⟩
    rw [show RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom ^ 2 =
        RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom * RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom
        from pow_two _, eq_bot_iff, Ideal.mul_le]
    intro x hx y hy
    rw [RingHom.mem_ker] at hx hy
    change x.fst = 0 at hx
    change y.fst = 0 at hy
    rw [Ideal.mem_bot]
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [TrivSqZeroExt.fst_mul, hx, zero_mul, TrivSqZeroExt.fst_zero]
    · rw [DualNumber.snd_mul, hx, hy, zero_mul, mul_zero, add_zero, TrivSqZeroExt.snd_zero]
  have hunitε : ∀ n : ℕ, ((n : ℕ) : k) ≠ 0 → IsUnit ((n : ℕ) : DualNumber k) := fun n hn => by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_natCast]; exact isUnit_iff_ne_zero.mpr hn
  have hM'ε := hunitε M' hM'k
  have hℓε := hunitε ℓ hℓk

  have relSymm : ∀ {T : Type} [CommRing T] [Algebra A₀ T] (x y : (((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).Raw T), (((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).Rel x y → (((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).Rel y x := by
    intro T _ _ x y ⟨C, hC⟩
    refine ⟨C⁻¹, ?_⟩
    rw [hC, ← (((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).act_mul, inv_mul_cancel, (((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).act_one]
  have relOfEq : ∀ {T : Type} [CommRing T] [Algebra A₀ T] (x y : (((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).Raw T),
      (Quot.mk _ x : (((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).Pt T) = Quot.mk _ y → (((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).Rel x y := by
    intro T _ _ x y h
    have hE : Equivalence ((((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).Rel (T := T)) :=
      ⟨ModularCurve.RigidWeierstrassData.Rel.refl _, fun hxy => relSymm _ _ hxy,
        fun hxy hyz => ModularCurve.RigidWeierstrassData.Rel.trans _ hxy hyz⟩
    exact hE.eqvGen_iff.mp (Quot.eqvGen_exact h)

  set E₀ : WeierstrassCurve k := X₀.curve with hE₀
  have hΔ₀ : IsUnit E₀.Δ := X₀.isUnit_Δ
  haveI : E₀.IsElliptic := ⟨hΔ₀⟩
  set h₀ : ↥M'.primeFactors → Polynomial k := X₀.level.1 with hh₀def
  set D₀ : ModularCurve.LevelPData k := X₀.level.2.1 with hD₀def
  have hh₀ : ∀ p : ↥M'.primeFactors, ModularCurve.IsGamma0PowAt E₀ (p : ℕ) (M'.factorization (p : ℕ)) (h₀ p) := X₀.isLevel.1
  have hD₀ : ModularCurve.IsLevelPStructure E₀ ℓ D₀ := X₀.isLevel.2.1

  obtain ⟨E₁, hE₁, hE₁'⟩ := WeierstrassCurve.exists_map_eq_and_forall_variableChange_smul_map_ne k E₀
  have hΔ₁ : IsUnit E₁.Δ := by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
    change IsUnit ((TrivSqZeroExt.fstHom k k k).toRingHom E₁.Δ)
    rw [← WeierstrassCurve.map_Δ, hE₁]; exact hΔ₀
  obtain ⟨h₁, ⟨hh₁m, hh₁⟩, -⟩ :=
    ModularCurve.IsGamma0PowAt.existsUnique_tuple_map_eq_of_surjective_of_ker_pow_eq_bot
      (TrivSqZeroExt.fstHom k k k).toRingHom hsurj hnil E₁ hΔ₁ M' hM'ε h₀ (by rw [hE₁]; exact hh₀)
  obtain ⟨D₁, ⟨hD₁m, hD₁⟩, -⟩ :=
    ModularCurve.IsLevelPStructure.existsUnique_map_eq_of_surjective_of_ker_pow_eq_bot
      (TrivSqZeroExt.fstHom k k k).toRingHom hsurj hnil E₁ hΔ₁ ℓ hℓ2 hℓε D₀ (by rw [hE₁]; exact hD₀)
  let X₁ : (((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).Raw (DualNumber k) :=
    (⟨E₁, hΔ₁, ⟨h₁, D₁, X₀.level.2.2⟩, ⟨hh₁, hD₁, trivial⟩⟩ :
      ((ModularCurve.gamma0PowComponent A₀ M' hM).prod ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod
        (ModularCurve.LevelComponent.trivial (A := A₀)))).Raw (DualNumber k))

  have hX₁fst : (((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).mapRing fstA X₁ = X₀ := by
    apply ModularCurve.LevelComponent.Raw.ext'
    · exact hE₁
    · show ((fun p => (h₁ p).map fstA.toRingHom), (D₁.map fstA.toRingHom, X₀.level.2.2)) = X₀.level
      rw [hfst_toRingHom, hh₁m, hD₁m, hh₀def, hD₀def]
      exact Prod.ext rfl (Prod.ext rfl rfl)
  refine ⟨Quot.mk _ X₁, ?_, ?_, ?_⟩
  ·
    show (((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).map fstA (Quot.mk _ X₁) = Quot.mk _ X₀
    rw [ModularCurve.RigidWeierstrassData.map_mk, hX₁fst]
  ·
    intro heq
    have heq' : (Quot.mk _ X₁ : (((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).Pt (DualNumber k)) = Quot.mk _ ((((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).mapRing inlA X₀) := by
      rw [heq]; exact ModularCurve.RigidWeierstrassData.map_mk _ inlA X₀
    obtain ⟨C, hC⟩ := relSymm _ _ (relOfEq _ _ heq')

    have hcurve : E₁ = C • (E₀.map (algebraMap k (DualNumber k))) := by
      have := congrArg (((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).curve hC
      rw [(((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).curve_act, (((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).curve_mapRing, hinl_toRingHom] at this
      exact this
    have hred : X₀ = (((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).act (C.map fstA.toRingHom) X₀ := by
      have := congrArg ((((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).mapRing fstA) hC
      rw [hX₁fst, (((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).mapRing_act, ← (((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).mapRing_comp] at this
      have hid : fstA.comp inlA = AlgHom.id A₀ k := AlgHom.ext fun a => rfl
      rw [hid, (((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).mapRing_id] at this
      exact this
    have hcurve₀ : (C.map (TrivSqZeroExt.fstHom k k k).toRingHom) • E₀ = E₀ := by
      have := congrArg (((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).curve hred
      rw [(((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).curve_act] at this
      exact this.symm
    set Cbar := C.map (TrivSqZeroExt.fstHom k k k).toRingHom with hCbar
    have hcurve₀' : Cbar⁻¹ • E₀ = E₀ := by
      conv_lhs => rw [← hcurve₀]
      rw [smul_smul, inv_mul_cancel, one_smul]
    set C' : WeierstrassCurve.VariableChange (DualNumber k) :=
      C * (Cbar⁻¹).map (algebraMap k (DualNumber k)) with hC'
    have hmap_mul : ∀ (C₁ C₂ : WeierstrassCurve.VariableChange (DualNumber k)),
        (C₁ * C₂).map (TrivSqZeroExt.fstHom k k k).toRingHom =
          C₁.map (TrivSqZeroExt.fstHom k k k).toRingHom * C₂.map (TrivSqZeroExt.fstHom k k k).toRingHom :=
      fun C₁ C₂ => by
        show WeierstrassCurve.VariableChange.mapHom _ (C₁ * C₂) =
          WeierstrassCurve.VariableChange.mapHom _ C₁ * WeierstrassCurve.VariableChange.mapHom _ C₂
        exact map_mul _ _ _
    have hC'1 : C'.map (TrivSqZeroExt.fstHom k k k).toRingHom = 1 := by
      have hcomp : ((TrivSqZeroExt.fstHom k k k).toRingHom.comp (algebraMap k (DualNumber k))) = RingHom.id k :=
        RingHom.ext fun a => rfl
      rw [hC', hmap_mul, WeierstrassCurve.VariableChange.map_map, hcomp, WeierstrassCurve.VariableChange.map_id, ← hCbar,
        mul_inv_cancel]
    have hC'E : C' • (E₀.map (algebraMap k (DualNumber k))) = E₁ := by
      rw [hC', ← smul_smul, WeierstrassCurve.map_variableChange, hcurve₀', ← hcurve]
    exact hE₁' C' hC'1 hC'E
  ·

    have main : ∀ Y' : (((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).Raw (DualNumber k), (((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).mapRing fstA Y' = X₀ →
        ∃ c : k, (Quot.mk _ Y' : (((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).Pt (DualNumber k)) =
          (((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).map ((TrivSqZeroExt.map (c • (LinearMap.id : k →ₗ[k] k))).restrictScalars A₀) (Quot.mk _ X₁) := by
      intro Y' hY'fst
      have hEfst : ((((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).curve Y').map (TrivSqZeroExt.fstHom k k k).toRingHom = E₀ := by
        have := congrArg (((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).curve hY'fst
        rw [(((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).curve_mapRing] at this
        exact this
      obtain ⟨c, C, hC1, hCE⟩ :=
        WeierstrassCurve.exists_variableChange_smul_map_eq_of_forall_variableChange_smul_ne k E₀ E₁ hE₁ hE₁'
          ((((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).curve Y') hEfst
      refine ⟨c, ?_⟩
      symm
      show (((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).map ((TrivSqZeroExt.map (c • (LinearMap.id : k →ₗ[k] k))).restrictScalars A₀) (Quot.mk _ X₁) = Quot.mk _ Y'
      rw [ModularCurve.RigidWeierstrassData.map_mk]
      apply Quot.sound
      refine ⟨C, ?_⟩
      set scA : DualNumber k →ₐ[A₀] DualNumber k :=
        (TrivSqZeroExt.map (c • (LinearMap.id : k →ₗ[k] k))).restrictScalars A₀ with hscA
      have hfst_sc : (TrivSqZeroExt.fstHom k k k).toRingHom.comp scA.toRingHom = (TrivSqZeroExt.fstHom k k k).toRingHom :=
        RingHom.ext fun z => TrivSqZeroExt.fst_map _ z
      have hcurveY : (((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).curve Y' = C • (E₁.map scA.toRingHom) := hCE.symm
      have hΔY : IsUnit ((((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).curve Y').Δ := (((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).isUnit_Δ Y'

      have huh := ModularCurve.IsGamma0PowAt.existsUnique_tuple_map_eq_of_surjective_of_ker_pow_eq_bot
        (TrivSqZeroExt.fstHom k k k).toRingHom hsurj hnil ((((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).curve Y') hΔY M' hM'ε h₀ (by rw [hEfst]; exact hh₀)
      have hlevY : (fun p => (Y'.level.1 p).map (TrivSqZeroExt.fstHom k k k).toRingHom) = h₀ ∧
          ∀ p : ↥M'.primeFactors, ModularCurve.IsGamma0PowAt ((((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).curve Y') (p : ℕ) (M'.factorization (p : ℕ)) (Y'.level.1 p) :=
        ⟨congrArg (fun Z => Z.level.1) hY'fst, Y'.isLevel.1⟩
      have hlev1 : (fun p : ↥M'.primeFactors => (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ))) ((h₁ p).map scA.toRingHom)).map
            (TrivSqZeroExt.fstHom k k k).toRingHom) = h₀ ∧
          ∀ p : ↥M'.primeFactors, ModularCurve.IsGamma0PowAt ((((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).curve Y') (p : ℕ) (M'.factorization (p : ℕ))
            (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ))) ((h₁ p).map scA.toRingHom)) := by
        refine ⟨?_, ?_⟩
        · funext p
          rw [ModularCurve.kernelVariableChangeDeg_map, hC1, ModularCurve.kernelVariableChangeDeg_one,
            Polynomial.map_map, hfst_sc]
          exact congrFun hh₁m p
        · intro p
          rw [hcurveY]
          exact hM _ _ C _ _ _ (ModularCurve.IsGamma0PowAt.map scA.toRingHom E₁ _ _ (hh₁ p))
      have e1 := huh.unique hlevY hlev1

      have huD := ModularCurve.IsLevelPStructure.existsUnique_map_eq_of_surjective_of_ker_pow_eq_bot
        (TrivSqZeroExt.fstHom k k k).toRingHom hsurj hnil ((((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).curve Y') hΔY ℓ hℓ2 hℓε D₀ (by rw [hEfst]; exact hD₀)
      have hlevYD : Y'.level.2.1.map (TrivSqZeroExt.fstHom k k k).toRingHom = D₀ ∧
          ModularCurve.IsLevelPStructure ((((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).curve Y') ℓ Y'.level.2.1 :=
        ⟨congrArg (fun Z => Z.level.2.1) hY'fst, Y'.isLevel.2.1⟩
      have hlev2 : ((D₁.map scA.toRingHom).variableChange C).map (TrivSqZeroExt.fstHom k k k).toRingHom = D₀ ∧
          ModularCurve.IsLevelPStructure ((((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).curve Y') ℓ ((D₁.map scA.toRingHom).variableChange C) := by
        refine ⟨?_, ?_⟩
        · rw [ModularCurve.LevelPData.map_variableChange, hC1, ModularCurve.LevelPData.variableChange_one]
          show D₁.map ((TrivSqZeroExt.fstHom k k k).toRingHom.comp scA.toRingHom) = D₀
          rw [hfst_sc, hD₁m]
        · rw [hcurveY]
          exact hℓ _ _ C _ (hD₁.map scA.toRingHom)
      have e2 := huD.unique hlevYD hlev2
      apply ModularCurve.LevelComponent.Raw.ext'
      · show (((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).curve Y' = (((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).curve ((((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).act C ((((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).mapRing scA X₁))
        conv_rhs => rw [(((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).curve_act, (((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).curve_mapRing]
        exact hcurveY
      · show Y'.level = ((fun p : ↥M'.primeFactors => ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ))) ((h₁ p).map scA.toRingHom)),
          ((D₁.map scA.toRingHom).variableChange C, X₀.level.2.2))
        exact Prod.ext e1 (Prod.ext e2 rfl)
    intro y hy
    obtain ⟨Y, rfl⟩ := Quot.exists_rep y
    obtain ⟨C₀, hC₀⟩ := relOfEq _ _ (Eq.trans (ModularCurve.RigidWeierstrassData.map_mk _ fstA Y).symm hy)

    have hYY' : (Quot.mk _ Y : (((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).Pt (DualNumber k)) =
        Quot.mk _ ((((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).act (C₀.map (algebraMap k (DualNumber k))) Y) := Quot.sound ⟨_, rfl⟩
    have hY'fst : (((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).mapRing fstA ((((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).act (C₀.map (algebraMap k (DualNumber k))) Y) = X₀ := by
      rw [(((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).mapRing_act, WeierstrassCurve.VariableChange.map_map]
      have hcomp : (fstA.toRingHom.comp (algebraMap k (DualNumber k))) = RingHom.id k := RingHom.ext fun a => rfl
      rw [hcomp, WeierstrassCurve.VariableChange.map_id]
      exact hC₀.symm
    obtain ⟨c, hc⟩ := main _ hY'fst
    exact ⟨c, hYY'.trans hc⟩

end S_ModularCurve_FullLevel_exists_forall_eq_map_dualNumber_smul_of_trivial_gamma0Pow
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_forall_eq_map_dualNumber_smul_of_trivial_gamma0Pow (solution)
