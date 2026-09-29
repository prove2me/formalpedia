-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevelOne.formallySmooth_fiber_bot_blowupChart_of_drinfeldChartWitness_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/035880c7-ed0f-5046-9173-fe28681c84da

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_CoordRing
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_Subalgebra_le_and_exists_pow_mul_mem_and_finiteType_of_eq_restrictScalars_adjoin_div
import Theorems.Thm_Algebra_Smooth_of_isIntegrallyClosed_of_krullDimLE_one_of_perfectField
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isLocalization_chartAlg
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegrallyClosed_chartAlg
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finiteType_chartAlgFin_and_chartAlgInf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevelOne_formallySmooth_fiber_bot_blowupChart_of_drinfeldChartWitness_of_dvd
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg"

set_option autoImplicit false
set_option maxHeartbeats 12800000
set_option synthInstance.maxHeartbeats 1600000

namespace GenericFibre

open TensorProduct

theorem formallySmooth_fiber_bot
    {A B L D : Type*} [CommRing A] [IsDomain A] [CommRing B] [Algebra A B]
    [Field L] [Algebra A L] [IsFractionRing A L]
    [CommRing D] [Algebra A D] [Algebra L D] [IsScalarTower A L D] [Algebra B D] [IsScalarTower A B D]
    [Algebra.IsPushout A L B D] [Algebra.FormallySmooth L D] :
    Algebra.FormallySmooth (⊥ : Ideal A).ResidueField ((⊥ : Ideal A).Fiber B) := by
  set κ := (⊥ : Ideal A).ResidueField with hκ
  have hunits : ∀ y : nonZeroDivisors A, IsUnit (algebraMap A κ y) := by
    intro y
    apply isUnit_iff_ne_zero.mpr
    intro h
    have hy : (y : A) ∈ (⊥ : Ideal A) := Ideal.algebraMap_residueField_eq_zero.mp h
    rw [Ideal.mem_bot] at hy
    exact nonZeroDivisors.ne_zero y.2 hy
  letI algLκ : Algebra L κ := (IsLocalization.lift (M := nonZeroDivisors A) hunits : L →+* κ).toAlgebra
  have hLκ : ∀ a, algebraMap L κ (algebraMap A L a) = algebraMap A κ a := fun a =>
    IsLocalization.lift_eq hunits a
  haveI : IsScalarTower A L κ := IsScalarTower.of_algebraMap_eq (fun a => (hLκ a).symm)
  let e : L ⊗[A] B ≃ₐ[L] D := Algebra.IsPushout.equiv A L B D
  haveI : Algebra.FormallySmooth L (L ⊗[A] B) := .of_equiv e.symm
  haveI : Algebra.FormallySmooth κ (κ ⊗[L] (L ⊗[A] B)) := inferInstance
  exact .of_equiv (Algebra.TensorProduct.cancelBaseChange A L κ κ B)

end GenericFibre

open CategoryTheory AlgebraicGeometry IsLocalRing AlgebraicCurve.TwoChartIntegralModel

open scoped MatrixGroups

namespace GenericFibreAssembly

theorem gamma_le_gammaH (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) :
    CongruenceSubgroup.Gamma N ≤ CohCarrier.GammaH N H := by
  intro γ hγ
  rw [CohCarrier.mem_GammaH_iff]
  rw [CongruenceSubgroup.Gamma_mem] at hγ
  have h0 : γ ∈ CongruenceSubgroup.Gamma0 N := by
    rw [CongruenceSubgroup.Gamma0_mem]; exact hγ.2.2.1
  refine ⟨h0, ?_⟩
  have : CohCarrier.gamma0Units N ⟨γ, h0⟩ = 1 := by
    ext
    rw [CohCarrier.val_gamma0Units, Units.val_one]
    exact hγ.2.2.2
  rw [this]; exact one_mem H

scoped instance finiteIndex_gammaH (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) :
    (CohCarrier.GammaH N H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (gamma_le_gammaH N H)

end GenericFibreAssembly
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_AuxLevelOne_formallySmooth_fiber_bot_blowupChart_of_drinfeldChartWitness_of_dvd.GenericFibreAssembly"

open GenericFibreAssembly in

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')

    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)

    (hι : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / q))
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [HenselianLocalRing A] [IsAlgClosed (ResidueField A)]
    (hAq : (q : A) ∈ maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ})

    (ϖt : A) (hϖt : ∃ u : A, IsUnit u ∧ ϖt ^ (q ^ 2 - 1) = (q : A) * u)

    (y : Ideal ↥(chartAlgFin A (↥K) j)) (hy : y.IsMaximal) (hϖy : algebraMap A ↥(chartAlgFin A (↥K) j) ϖ ∈ y)
    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(chartAlgFin A (↥K) j) →+* Ω), RingHom.ker φ = y → φ (jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω)

    (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j))
        (ϖz : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
        (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
          (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
        (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        (y' : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j))
        (hy' : (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y' = z)
        (hss' : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
          (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω),
          RingHom.ker φ = y'.asIdeal →
            φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω)
    (hy'y : y'.asIdeal = y)
      (W₁ : Type) [CommRing W₁] [IsDomain W₁] [IsDiscreteValuationRing W₁]
        [IsAdicComplete (IsLocalRing.maximalIdeal W₁) W₁] (σ₁ : A →+* W₁)
        (hσ₁ : IsLocalRing.maximalIdeal W₁ = Ideal.span {σ₁ ϖ})
        (f₁ u₁ v₁ : MvPowerSeries (Fin 2) W₁) (hu₁ : IsUnit u₁) (hv₁ : IsUnit v₁)
        (hf₁ : f₁ - DrinfeldCurve.LocalChart.drinfeldForm q W₁ ∈
          (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ (q + 2))
        (e₁ : AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ≃+*
          MvPowerSeries (Fin 2) W₁ ⧸ Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})

    (hW₁ :
        let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
        let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        let toC : STK →+* CMP := algebraMap STK CMP
        let S := (MvPowerSeries (Fin 2) W₁ ⧸ Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
        let mkS : MvPowerSeries (Fin 2) W₁ →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
        let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
          ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
              ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y', trivial, hy'⟩).hom.comp
            ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
              (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)

        (∀ a : A, e₁ (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
              (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
            (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
              (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
                ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)))) =
          Ideal.Quotient.mk _ (MvPowerSeries.C (σ₁ a))) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
            ∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
              τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' → ((γ 1 1 : ℤ) : ZMod ℓ) = 1 →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
            ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
                τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
              ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y'.asIdeal) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
            ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
                τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
              (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y'.asIdeal) →
                ∃ (θ : S ≃+* S) (c : W₁) (M : Matrix (Fin 2) (Fin 2) W₁),

                  (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                    θ (e₁ (toC (germY a))) = e₁ (toC (germY (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a)))) ∧

                  (∀ w : W₁, θ (mkS (MvPowerSeries.C w)) = mkS (MvPowerSeries.C w)) ∧

                  (∀ jj : Fin 2, θ (mkS (MvPowerSeries.X jj)) -
                      mkS (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) ∈
                    (Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2) ∧
                  (c ^ (q + 1) - 1 ∈ IsLocalRing.maximalIdeal W₁) ∧
                  (∀ ii jj : Fin 2, M ii jj - c * ((γ ii jj : ℤ) : W₁) ∈ IsLocalRing.maximalIdeal W₁) ∧
                  (((γ 1 1 : ℤ) : ZMod ℓ) = 1 → c - 1 ∈ IsLocalRing.maximalIdeal W₁) ∧

                  (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥K, τ k = k) → c - 1 ∉ IsLocalRing.maximalIdeal W₁)) ∧

        (∀ (a₁ b₁ a₂ b₂ : ℤ) (P₁ P₂ : Ideal S), P₁.IsPrime → P₂.IsPrime →

          (mkS (MvPowerSeries.X 0) ∉ P₁ ∨ mkS (MvPowerSeries.X 1) ∉ P₁) →
          (mkS (MvPowerSeries.X 0) ∉ P₂ ∨ mkS (MvPowerSeries.X 1) ∉ P₂) →
          mkS (MvPowerSeries.C (σ₁ ϖ)) ∈ P₁ → mkS (MvPowerSeries.C (σ₁ ϖ)) ∈ P₂ →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C ((a₁ : ℤ) : W₁) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₁ : ℤ) : W₁) * MvPowerSeries.X 1 + h)
                ∈ P₁) →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C ((a₂ : ℤ) : W₁) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₂ : ℤ) : W₁) * MvPowerSeries.X 1 + h)
                ∈ P₂) →
          ¬ ((q : ℤ) ∣ a₁ * b₂ - a₂ * b₁) →
            Ideal.comap ((e₁ : CMP →+* S).comp toC) P₁ ≠ Ideal.comap ((e₁ : CMP →+* S).comp toC) P₂) ∧

        (∀ P : Ideal S, P.IsPrime → (mkS (MvPowerSeries.X 0) ∉ P ∨ mkS (MvPowerSeries.X 1) ∉ P) →
          mkS (MvPowerSeries.C (σ₁ ϖ)) ∈ P →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C (1 : W₁) * MvPowerSeries.X 0 + MvPowerSeries.C (0 : W₁) * MvPowerSeries.X 1 + h) ∈ P) →
          ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
            toC (germY a) ∈ Ideal.comap (e₁ : CMP →+* S) P ↔
              ∀ n : ℤ, ∃ m ∈ IsLocalRing.maximalIdeal A,
                (((a : ↥K) : LaurentSeries L).coeff n) = algebraMap A L m) ∧

        (∃ (hjK : ModularCurve.jqNModC L q ∈ K)
           (hjC : (⟨ModularCurve.jqNModC L q, hjK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
           (a₀ : A) (_ : (⟨(⟨ModularCurve.jqNModC L q, hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) -
              algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a₀ ∈ y'.asIdeal)
           (e₀ : ℕ) (_ : 1 ≤ e₀) (h : MvPowerSeries (Fin 2) W₁)
           (_ : h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ e₀),
           (∀ a b : W₁, (a ∉ IsLocalRing.maximalIdeal W₁ ∨ b ∉ IsLocalRing.maximalIdeal W₁) →
              a ^ q * b - a * b ^ q ∈ IsLocalRing.maximalIdeal W₁ →
              IsUnit (∑ i ∈ Finset.range (e₀ + 1),
                MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (e₀ - i)) h * a ^ i * b ^ (e₀ - i))) ∧
           (e₁ : CMP →+* S) (toC (germY ((⟨(⟨ModularCurve.jqNModC L q, hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) -
              algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a₀))) = mkS h))

    (J : Ideal ↥(chartAlgFin A (↥K) j))
    (hJ :
        let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
        let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        let toC : STK →+* CMP := algebraMap STK CMP
        let S := (MvPowerSeries (Fin 2) W₁ ⧸ Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
        let mkS : MvPowerSeries (Fin 2) W₁ →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
        let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
          ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
              ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y', trivial, hy'⟩).hom.comp
            ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
              (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)
        J = sInf {J' : Ideal ↥(chartAlgFin A (↥K) j) | ∃ (γ : SL(2, ℤ)) (_ : γ ∈ CongruenceSubgroup.Gamma q)
          (_ : γ ∈ CongruenceSubgroup.Gamma0 M') (τ : ↥K ≃ₐ[L] ↥K)
          (_ : ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ)
          (hpres : ∀ a : ↥K, a ∈ chartAlgFin A (↥K) j → τ a ∈ chartAlgFin A (↥K) j),
          J' = Ideal.comap ((τ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpres)
            (Ideal.comap ((e₁ : CMP →+* S).comp (toC.comp germY))
              (Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖt)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}))})

    (B : Subalgebra A ↥K)
    (hB : B = (Algebra.adjoin ↥(chartAlgFin A (↥K) j)
        {x : ↥K | ∃ i ∈ J, x * algebraMap A ↥K ϖt = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}).restrictScalars A) :

        Algebra.FormallySmooth (⊥ : Ideal A).ResidueField ((⊥ : Ideal A).Fiber ↥B) := by
  classical
  have hqp : q.Prime := Fact.out

  have hinjAL : Function.Injective (algebraMap A L) := IsFractionRing.injective A L
  have hinjAK : Function.Injective (algebraMap A ↥K) := by
    rw [IsScalarTower.algebraMap_eq A L ↥K, RingHom.coe_comp]
    exact (algebraMap L ↥K).injective.comp hinjAL
  have hϖt0 : ϖt ≠ 0 := by
    intro h0
    obtain ⟨u, hu, hpow⟩ := hϖt
    have hexp : q ^ 2 - 1 ≠ 0 := by
      have h2 : 2 ≤ q := hqp.two_le
      have h4 : 4 ≤ q ^ 2 := by nlinarith
      omega
    rw [h0, zero_pow hexp] at hpow
    have hqA : (q : A) = 0 := by
      have := congrArg (· * (↑hu.unit⁻¹ : A)) hpow
      simpa [mul_assoc, IsUnit.mul_val_inv] using this.symm
    have hqL : (q : L) = 0 := by
      have := congrArg (algebraMap A L) hqA
      simpa using this
    exact hqp.ne_zero (by exact_mod_cast hqL)
  have hLt0 : algebraMap A L ϖt ≠ 0 := fun h => hϖt0 (hinjAL (by rw [h, map_zero]))
  have ht0 : algebraMap A ↥K ϖt ≠ 0 := fun h => hϖt0 (hinjAK (by rw [h, map_zero]))
  have hK' : K = ModularCurve.laurentBaseChange L
      (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') H₁)) := by
    rw [hK]; rfl
  have hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K :=
    ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
      (CohCarrier.GammaH (q ^ 2 * M') H₁)
      (ModularCurve.translation_mem_GammaH _ _) L K hK' j hj
  haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K := Algebra.IsAlgebraic.of_finite _ _
  have hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  have htj : Transcendental A j := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K A j hj
  have htjL : Transcendental L j := fun halg => htj ((IsFractionRing.isAlgebraic_iff A L ↥K).mpr halg)

  obtain ⟨h1, h2, -, -, -, -⟩ :=
    Subalgebra.le_and_exists_pow_mul_mem_and_finiteType_of_eq_restrictScalars_adjoin_div
      (chartAlgFin A (↥K) j) J ϖt ht0 B hB

  set CL : Subalgebra L ↥K := chartAlgFin L (↥K) j with hCLdef
  have hftCL : Algebra.FiniteType L ↥CL :=
    (AlgebraicCurve.TwoChartIntegralModel.finiteType_chartAlgFin_and_chartAlgInf L L (↥K) j htjL hFD hsep).1
  haveI : IsIntegrallyClosed ↥CL := AlgebraicCurve.TwoChartIntegralModel.isIntegrallyClosed_chartAlg L (↥K) {j}
  haveI : IsDomain ↥CL := inferInstance

  set R₀ : Subalgebra L ↥K := Algebra.adjoin L ({j} : Set ↥K) with hR₀def
  haveI : IsDomain ↥R₀ := inferInstance
  have ePol : Polynomial L ≃ₐ[L] ↥R₀ := Polynomial.algEquivOfTranscendental L j htjL
  haveI : IsPrincipalIdealRing ↥R₀ := IsPrincipalIdealRing.of_surjective ePol.toRingHom ePol.surjective
  haveI : Ring.DimensionLEOne ↥R₀ := inferInstance
  have hR₀CL : R₀ ≤ CL := adjoin_le_chartAlg L (↥K) {j}
  letI algR₀ : Algebra ↥R₀ ↥CL := (Subalgebra.inclusion hR₀CL).toRingHom.toAlgebra
  have halgR₀ : ∀ r : ↥R₀, ((algebraMap ↥R₀ ↥CL r : ↥CL) : ↥K) = (r : ↥K) := fun r => rfl
  let fval : ↥CL →ₐ[↥R₀] ↥K :=
    { (CL.val : ↥CL →+* ↥K) with commutes' := fun r => rfl }
  haveI : Algebra.IsIntegral ↥R₀ ↥CL := by
    refine ⟨fun x => ?_⟩
    have hx : IsIntegral ↥R₀ (x : ↥K) := x.2
    exact (isIntegral_algHom_iff fval Subtype.val_injective).mp hx
  haveI : Ring.DimensionLEOne ↥CL := Ring.DimensionLEOne.of_isIntegral ↥R₀ ↥CL
  haveI : Ring.KrullDimLE 1 ↥CL := inferInstance
  haveI := hftCL
  have hSm : Algebra.Smooth L ↥CL := Algebra.Smooth.of_isIntegrallyClosed_of_krullDimLE_one_of_perfectField L ↥CL
  haveI : Algebra.FormallySmooth L ↥CL := hSm.formallySmooth

  have hCCL : ∀ x : ↥K, x ∈ chartAlgFin A (↥K) j → x ∈ CL := fun x hx =>
    chartAlg_le_restrictScalars A (↥K) L {j} hx
  have htL : algebraMap A ↥K ϖt = algebraMap L ↥K (algebraMap A L ϖt) := IsScalarTower.algebraMap_apply A L ↥K ϖt
  have hBCL : ∀ x : ↥K, x ∈ B → x ∈ CL := by
    intro x hx
    obtain ⟨n, hn⟩ := h2 x hx
    have hunit : x = algebraMap L ↥K ((algebraMap A L ϖt)⁻¹ ^ n) * (algebraMap A ↥K ϖt ^ n * x) := by
      rw [htL, map_pow, ← mul_assoc, ← mul_pow, ← map_mul, inv_mul_cancel₀ hLt0, map_one, one_pow, one_mul]
    rw [hunit]
    exact CL.mul_mem (CL.algebraMap_mem _) (hCCL _ hn)
  let ιBL : ↥B →+* ↥CL :=
    { toFun := fun b => ⟨(b : ↥K), hBCL _ b.2⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun a b => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun a b => Subtype.ext rfl }
  letI algBCL : Algebra ↥B ↥CL := ιBL.toAlgebra
  have hιBL : ∀ b : ↥B, ((algebraMap ↥B ↥CL b : ↥CL) : ↥K) = (b : ↥K) := fun b => rfl
  have hACL : ∀ a : A, ((algebraMap A ↥CL a : ↥CL) : ↥K) = algebraMap A ↥K a := fun a =>
    Subalgebra.coe_algebraMap CL a
  haveI : IsScalarTower A ↥B ↥CL := by
    refine IsScalarTower.of_algebraMap_eq (fun a => Subtype.ext ?_)
    rw [hACL, hιBL, Subalgebra.coe_algebraMap]
  haveI : IsScalarTower A L ↥CL := inferInstance

  letI algCCL : Algebra ↥(chartAlgFin A (↥K) j) ↥CL := (chartBaseChange A (↥K) L {j}).toAlgebra
  have hlocC : IsLocalization ((nonZeroDivisors A).map (algebraMap A ↥(chartAlgFin A (↥K) j))) ↥CL :=
    AlgebraicCurve.TwoChartIntegralModel.isLocalization_chartAlg A (↥K) L (nonZeroDivisors A) {j}
  have hCCLcoe : ∀ c : ↥(chartAlgFin A (↥K) j), ((algebraMap ↥(chartAlgFin A (↥K) j) ↥CL c : ↥CL) : ↥K) = (c : ↥K) :=
    fun c => coe_chartBaseChange A (↥K) L {j} c
  haveI hlocB : IsLocalization (Algebra.algebraMapSubmonoid ↥B (nonZeroDivisors A)) ↥CL := by
    rw [isLocalization_iff]
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨_, a, ha, rfl⟩
      have ha0 : (a : A) ≠ 0 := nonZeroDivisors.ne_zero ha
      have hL0 : algebraMap A L a ≠ 0 := fun h => ha0 (hinjAL (by rw [h, map_zero]))
      refine IsUnit.of_mul_eq_one (algebraMap L ↥CL (algebraMap A L a)⁻¹) (Subtype.ext ?_)
      rw [Subalgebra.coe_mul, Subalgebra.coe_one]
      change ((algebraMap ↥B ↥CL (algebraMap A ↥B a) : ↥CL) : ↥K) * _ = 1
      rw [hιBL, Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply A L ↥K,
        ← map_mul, mul_inv_cancel₀ hL0, map_one]
    · intro zz
      obtain ⟨⟨c, s⟩, hcs⟩ := IsLocalization.surj ((nonZeroDivisors A).map (algebraMap A ↥(chartAlgFin A (↥K) j))) zz
      obtain ⟨a, ha, hs⟩ := s.2
      refine ⟨⟨⟨(c : ↥K), h1 c.2⟩, ⟨algebraMap A ↥B a, a, ha, rfl⟩⟩, Subtype.ext ?_⟩
      have hcs' := congrArg (fun w : ↥CL => (w : ↥K)) hcs
      simp only [Subalgebra.coe_mul, hCCLcoe] at hcs'
      change (zz : ↥K) * ((algebraMap ↥B ↥CL (algebraMap A ↥B a) : ↥CL) : ↥K) =
        ((algebraMap ↥B ↥CL ⟨(c : ↥K), h1 c.2⟩ : ↥CL) : ↥K)
      rw [hιBL, hιBL, Subalgebra.coe_algebraMap]
      rw [← hs, Subalgebra.coe_algebraMap] at hcs'
      exact hcs'
    · intro x₁ x₂ hx
      refine ⟨1, ?_⟩
      have : (x₁ : ↥K) = (x₂ : ↥K) := by
        have := congrArg (fun w : ↥CL => (w : ↥K)) hx
        simpa [hιBL] using this
      rw [Subtype.ext this]
  haveI : Algebra.IsPushout A ↥B L ↥CL := Algebra.isPushout_of_isLocalization (nonZeroDivisors A) L ↥B ↥CL
  haveI : Algebra.IsPushout A L ↥B ↥CL := Algebra.IsPushout.symm inferInstance
  exact GenericFibre.formallySmooth_fiber_bot (A := A) (B := ↥B) (L := L) (D := ↥CL)

end S_ModularCurve_FullLevel_AuxLevelOne_formallySmooth_fiber_bot_blowupChart_of_drinfeldChartWitness_of_dvd
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevelOne_formallySmooth_fiber_bot_blowupChart_of_drinfeldChartWitness_of_dvd (solution)
