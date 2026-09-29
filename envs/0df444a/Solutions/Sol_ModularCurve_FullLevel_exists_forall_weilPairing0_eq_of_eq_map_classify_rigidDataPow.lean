-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_forall_weilPairing0_eq_of_eq_map_classify_rigidDataPow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/cf57f22a-0f07-509f-9c5f-8313bac83f9d

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_EllipticCurve_WeilPairingFun
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_LevelComponent_exists_pow_eq_one_and_forall_weilPairing0_toPoint_mapRing_eq_of_mk_eq_univ
import Theorems.Thm_WeierstrassCurve_Affine_weilPairing0_toPoint_variableChange
import Theorems.Thm_LaurentSeries_exists_valuationSubring_pow_eq_one_algebraMap_eq_of_pow_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_forall_weilPairing0_eq_of_eq_map_classify_rigidDataPow
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂"
p2m_attr_erase "simp" "Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups Classical

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

namespace P2M
namespace WeilConst

theorem exists_eq_act_mapRing {A : Type} [CommRing A] (R : ModularCurve.RigidWeierstrassData.{0} A)
    {B T : Type} [CommRing B] [Algebra A B] [CommRing T] [Algebra A T] (f : B →ₐ[A] T)
    (pt : R.Pt B) (u : R.Raw B) (hu : (Quot.mk _ u : R.Pt B) = pt)
    (x : R.Raw T) (hx : (Quot.mk _ x : R.Pt T) = R.toLevelModuliDatum.map f pt) :
    ∃ C : WeierstrassCurve.VariableChange T, x = R.act C (R.mapRing f u) := by
  have hequiv : Equivalence (R.Rel (T := T)) := by
    refine ⟨ModularCurve.RigidWeierstrassData.Rel.refl R, ?_, ModularCurve.RigidWeierstrassData.Rel.trans R⟩
    rintro a b ⟨C, rfl⟩
    refine ⟨C⁻¹, ?_⟩
    rw [← R.act_mul, inv_mul_cancel, R.act_one]
  have hxw : (Quot.mk _ x : R.Pt T) = Quot.mk _ (R.mapRing f u) := by
    rw [hx, ← hu]
    rfl
  exact hequiv.eqvGen_iff.mp (Quot.eq.mp hxw.symm)

end P2M.WeilConst

set_option maxHeartbeats 16000000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (s : ↥W)

    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
      Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A)

    (ℓ' : ℕ) [Fact ℓ'.Prime] (hℓ'q : ℓ' ≠ q) (hℓ'3 : 3 ≤ ℓ') (hℓ'M' : ¬ ℓ' ∣ M')
    (ξ : ↥k₀) (hξ : IsPrimitiveRoot ξ (q * ℓ'))
    (hιξ : ∃ ι : ↥k₀ →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ')))
    (K : IntermediateField ↥k₀ (LaurentSeries ↥k₀))
    (hK : K = ModularCurve.laurentBaseChange ↥k₀
      (ModularCurve.xHFunctionField ((q * ℓ') ^ 2 * M') (ModularCurve.FullLevel.levelH (q * ℓ') M')))
    [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥K] [IsScalarTower ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀ ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries ↥k₀)) = ModularCurve.coeffEmb ↥k₀ ModularCurve.jq) [Fact (j ≠ 0)]

    (hℓ : ∀ (T : Type) [CommRing T] [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ' D →
        ModularCurve.IsLevelPStructure (C • W) ℓ' (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (𝒢 : GroupLaws ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    (hVC : ∀ (T : Type) [CommRing T] [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (hCO : ∀ (T T' : Type) [CommRing T] [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) T] [CommRing T'] [Algebra ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) T'] (f : T →ₐ[↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ)

    (P₀ : LevelModuliPackageAbs ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (WeierstrassCurve.DrinfeldGlobal.rigidDataPow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓ' M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum)
    (x₀ : (WeierstrassCurve.DrinfeldGlobal.rigidDataPow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓ' M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt ↥K)
    (hx₀ : (((WeierstrassCurve.DrinfeldGlobal.rigidDataPow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓ' M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.jOf x₀ : ↥K) : LaurentSeries ↥k₀) = ModularCurve.jqNModC ↥k₀ (q * ℓ'))
    (clC : P₀.B₀ →ₐ[↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))] ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j))
    (hclC : ∀ b : P₀.B₀, ((clC b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j)) : ↥K) = P₀.classify x₀ b) :
    ∃ c : ((ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))ˣ,
      ∀ (y : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j)) (_ : y.IsMaximal)
        (ψ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j) →ₐ[↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))] (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))) (_ : ∀ c' : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (↥K) j), ψ c' = 0 ↔ c' ∈ y),
        ∀ x : (WeierstrassCurve.DrinfeldGlobal.rigidDataPow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓ' M' q hℓ hM 𝒢 𝒯).Raw (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))), (Quot.mk _ x : (WeierstrassCurve.DrinfeldGlobal.rigidDataPow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓ' M' q hℓ hM 𝒢 𝒯).Pt (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))) = (WeierstrassCurve.DrinfeldGlobal.rigidDataPow ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ℓ' M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.map ((ψ).comp clC) P₀.univ →
          (letI _ : (x.curve).IsElliptic := ⟨x.isUnit_Δ⟩;
            WeierstrassCurve.Affine.weilPairing0 (x.curve) (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) (ℓ' : ℤ)
              (ModularCurve.LevelRelabelling.toPoint ((x.curve).baseChange (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))) (x.level.2.1).xP (x.level.2.1).yP)
              (ModularCurve.LevelRelabelling.toPoint ((x.curve).baseChange (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))) (x.level.2.1).xQ (x.level.2.1).yQ)) = c  := by
  classical

  let A₀ : ValuationSubring ↥k₀ := A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))

  have hℓ'A : IsUnit ((ℓ' : ℕ) : ↥A₀) := by
    have hqp : q.Prime := Fact.out
    have hℓp : ℓ'.Prime := Fact.out
    have hcop : Nat.Coprime ℓ' q := (Nat.coprime_primes hℓp hqp).mpr hℓ'q

    have hℓA : IsUnit ((ℓ' : ℕ) : ↥A) := by
      by_contra hnu
      have hmemℓ : ((ℓ' : ℕ) : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := hnu
      have hmemq : ((q : ℕ) : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
        have hq' : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits := hA
        rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal] at hq'
        obtain ⟨hqA, hqmax⟩ := hq'
        have : (⟨((q : ℕ) : AlgebraicClosure ℚ), hqA⟩ : ↥A) = ((q : ℕ) : ↥A) := Subtype.ext (by simp)
        rw [← this]; exact hqmax
      obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, u * ℓ' + v * q = 1 := by
        have := Nat.Coprime.isCoprime hcop
        obtain ⟨u, v, h⟩ := this
        exact ⟨u, v, by linarith [h]⟩
      have h1 : (1 : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
        have : (1 : ↥A) = (u : ↥A) * ((ℓ' : ℕ) : ↥A) + (v : ↥A) * ((q : ℕ) : ↥A) := by
          have := congrArg (fun z : ℤ => (z : ↥A)) huv
          push_cast at this ⊢
          exact this.symm
        rw [this]
        exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hmemℓ) (Ideal.mul_mem_left _ _ hmemq)
      exact (Ideal.ne_top_iff_one _).mp (Ideal.IsMaximal.ne_top inferInstance) h1
    obtain ⟨w, hw⟩ := hℓA.exists_right_inv

    have hℓ0 : ((ℓ' : ℕ) : ↥k₀) ≠ 0 := by exact_mod_cast hℓp.ne_zero
    have hwval : (w : AlgebraicClosure ℚ) = ((ℓ' : ℕ) : AlgebraicClosure ℚ)⁻¹ := by
      have hw' : ((ℓ' : ℕ) : AlgebraicClosure ℚ) * (w : AlgebraicClosure ℚ) = 1 := by
        have := congrArg (fun z : ↥A => (z : AlgebraicClosure ℚ)) hw
        simpa using this
      have hℓ0' : ((ℓ' : ℕ) : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast hℓp.ne_zero
      exact (eq_inv_of_mul_eq_one_right hw')
    have hinvmem : ((ℓ' : ℕ) : ↥k₀)⁻¹ ∈ A₀ := by
      show algebraMap ↥k₀ (AlgebraicClosure ℚ) (((ℓ' : ℕ) : ↥k₀)⁻¹) ∈ A
      rw [map_inv₀, map_natCast, ← hwval]
      exact w.2
    refine IsUnit.of_mul_eq_one ⟨_, hinvmem⟩ ?_
    apply Subtype.ext
    show ((ℓ' : ℕ) : ↥k₀) * ((ℓ' : ℕ) : ↥k₀)⁻¹ = 1
    exact mul_inv_cancel₀ hℓ0

  obtain ⟨ε, hεpow, hε⟩ :=
    ModularCurve.LevelComponent.exists_pow_eq_one_and_forall_weilPairing0_toPoint_mapRing_eq_of_mk_eq_univ
      (↥A₀) ℓ' hℓ'3 hℓ'A hℓ (ModularCurve.gamma0PowComponent (↥A₀) M' hM)
      (WeierstrassCurve.DrinfeldGlobal.levelComponent (↥A₀) 𝒢 q 𝒯) P₀

  have hℓ'0 : ℓ' ≠ 0 := (Fact.out : ℓ'.Prime).ne_zero
  have hCpow : ((clC ε : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₀ (↥K) j)) : ↥K) ^ ℓ' = 1 := by
    rw [← Subalgebra.coe_pow, ← map_pow, hεpow, map_one, Subalgebra.coe_one]
  obtain ⟨a, hapow, haK⟩ :=
    LaurentSeries.exists_valuationSubring_pow_eq_one_algebraMap_eq_of_pow_eq_one K A₀ hℓ'0 _ hCpow
  have haC : algebraMap (↥A₀) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥A₀ (↥K) j) a = clC ε := by
    apply Subtype.ext
    rw [Subalgebra.coe_algebraMap]
    exact haK

  have haunit : IsUnit a := IsUnit.of_pow_eq_one hapow hℓ'0
  have hcunit : IsUnit (IsLocalRing.residue (↥A₀) a) := haunit.map _
  refine ⟨hcunit.unit, ?_⟩

  have hex : ∃ u : (WeierstrassCurve.DrinfeldGlobal.rigidDataPow (↥A₀) ℓ' M' q hℓ hM 𝒢 𝒯).Raw P₀.B₀,
      (Quot.mk _ u : (WeierstrassCurve.DrinfeldGlobal.rigidDataPow (↥A₀) ℓ' M' q hℓ hM 𝒢 𝒯).Pt P₀.B₀) = P₀.univ :=
    Quot.exists_rep _
  obtain ⟨u, hu⟩ := hex
  intro y _ ψ _ x hx

  obtain ⟨C, hC⟩ := P2M.WeilConst.exists_eq_act_mapRing _ (ψ.comp clC) P₀.univ u hu x hx
  subst hC

  have key := hε u hu (ResidueField ↥A₀) (ψ.comp clC)
  have hℓ'κ : ((ℓ' : ℕ) : ResidueField ↥A₀) ≠ 0 := by
    have h := hℓ'A.map (IsLocalRing.residue ↥A₀)
    rw [map_natCast] at h
    exact h.ne_zero
  haveI hwE : (((WeierstrassCurve.DrinfeldGlobal.rigidDataPow (↥A₀) ℓ' M' q hℓ hM 𝒢 𝒯).mapRing (ψ.comp clC) u).curve).IsElliptic :=
    ⟨((WeierstrassCurve.DrinfeldGlobal.rigidDataPow (↥A₀) ℓ' M' q hℓ hM 𝒢 𝒯).mapRing (ψ.comp clC) u).isUnit_Δ⟩
  haveI hCwE : (C • ((WeierstrassCurve.DrinfeldGlobal.rigidDataPow (↥A₀) ℓ' M' q hℓ hM 𝒢 𝒯).mapRing (ψ.comp clC) u).curve).IsElliptic :=
    ⟨((WeierstrassCurve.DrinfeldGlobal.rigidDataPow (↥A₀) ℓ' M' q hℓ hM 𝒢 𝒯).act C
      ((WeierstrassCurve.DrinfeldGlobal.rigidDataPow (↥A₀) ℓ' M' q hℓ hM 𝒢 𝒯).mapRing (ψ.comp clC) u)).isUnit_Δ⟩
  have iso := WeierstrassCurve.Affine.weilPairing0_toPoint_variableChange (K := ResidueField ↥A₀)
    (((WeierstrassCurve.DrinfeldGlobal.rigidDataPow (↥A₀) ℓ' M' q hℓ hM 𝒢 𝒯).mapRing (ψ.comp clC) u).curve) C ℓ' hℓ'3 hℓ'κ
    (((WeierstrassCurve.DrinfeldGlobal.rigidDataPow (↥A₀) ℓ' M' q hℓ hM 𝒢 𝒯).mapRing (ψ.comp clC) u).level.2.1)
    (((WeierstrassCurve.DrinfeldGlobal.rigidDataPow (↥A₀) ℓ' M' q hℓ hM 𝒢 𝒯).mapRing (ψ.comp clC) u).isLevel.2.1)
  apply Units.ext
  rw [IsUnit.unit_spec]
  refine (?_ : _ = (ψ.comp clC) ε).trans ?_
  · rw [← key]
    exact congrArg Units.val iso
  · rw [AlgHom.comp_apply, ← haC, AlgHom.commutes]
    rw [IsLocalRing.ResidueField.algebraMap_eq]

end S_ModularCurve_FullLevel_exists_forall_weilPairing0_eq_of_eq_map_classify_rigidDataPow
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_forall_weilPairing0_eq_of_eq_map_classify_rigidDataPow (solution)
