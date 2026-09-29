-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevel.exists_blowupChart_ringHom_localBlowupChart_surjective_ker_eq_span_of_dense_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/bdb0258d-fd86-5a98-a5e2-3ad4a6dd06fc

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
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_blowupChart_ringHom_away_extends_chartMap_of_eq_adjoin
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_localBlowupChart_ringHom_coordRing_of_chartPresentation_of_mem_nonZeroDivisors
import Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_blowupChart_ringHom_coordRing_surjective_ker_eq_span_of_chartMap_of_localFibreMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_blowupChart_ringHom_localBlowupChart_surjective_ker_eq_span_of_dense_of_flat

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry IsLocalRing AlgebraicCurve.TwoChartIntegralModel

open scoped MatrixGroups

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))

    (hι : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [HenselianLocalRing A] [IsAlgClosed (ResidueField A)]
    (hAq : (q : A) ∈ maximalIdeal A) (hξA : ∃ x : A, algebraMap A L x = ξ)
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
    (J : Ideal ↥(chartAlgFin A (↥K) j))
    (B : Subalgebra A ↥K)
    (hB : B = (Algebra.adjoin ↥(chartAlgFin A (↥K) j)
        {x : ↥K | ∃ i ∈ J, x * algebraMap A ↥K ϖt = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}).restrictScalars A)
    (hCB : chartAlgFin A (↥K) j ≤ B)

    (hbridge :
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

        Ideal.comap ((e₁ : CMP →+* S).comp (toC.comp germY)) (Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖ)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) = y ∧

        (∀ (n : ℕ) (s : S), ∃ a : ↥(chartAlgFin A (↥K) j), ((e₁ : CMP →+* S).comp (toC.comp germY)) a - s ∈ (Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖ)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ n) ∧

        (∀ a : A, ((e₁ : CMP →+* S).comp (toC.comp germY)) (algebraMap A ↥(chartAlgFin A (↥K) j) a) = mkS (MvPowerSeries.C (σ₁ a))) ∧

        (∀ c : ↥(chartAlgFin A (↥K) j), ∃ a : A, c - algebraMap A ↥(chartAlgFin A (↥K) j) a ∈ y) ∧
        (∀ w : W₁, ∃ a : A, w - σ₁ a ∈ IsLocalRing.maximalIdeal W₁) ∧
        Ideal.comap σ₁ (IsLocalRing.maximalIdeal W₁) = IsLocalRing.maximalIdeal A ∧

        (Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖ)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}).IsMaximal ∧ (∀ I : Ideal S, I.IsMaximal → I = Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖ)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ∧

        (letI : Algebra ↥(chartAlgFin A (↥K) j) S := (((e₁ : CMP →+* S).comp (toC.comp germY))).toAlgebra
         Module.Flat ↥(chartAlgFin A (↥K) j) S))

    (hcentre :
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

        Ideal.map ((e₁ : CMP →+* S).comp (toC.comp germY)) J = Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖt)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)} ∧

        (∃ I : Ideal ↥(chartAlgFin A (↥K) j),
            J = Ideal.comap ((e₁ : CMP →+* S).comp (toC.comp germY)) (Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖt)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ⊓ I ∧ I ⊔ y = ⊤) ∧
        J ≤ y ∧ algebraMap A ↥(chartAlgFin A (↥K) j) ϖt ∈ J)
    (inst : Algebra (GaloisField q 2) (ResidueField A)) :
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
        let Lloc := Localization.Away (mkS (MvPowerSeries.C (σ₁ ϖt)))
        let ιS : S →+* Lloc := algebraMap S Lloc
        let x₀ : Lloc := ιS (mkS (MvPowerSeries.X 0)) * IsLocalization.Away.invSelf (S := Lloc) (mkS (MvPowerSeries.C (σ₁ ϖt)))
        let x₁ : Lloc := ιS (mkS (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf (S := Lloc) (mkS (MvPowerSeries.C (σ₁ ϖt)))
        let Rloc : Subring Lloc := Subring.closure (Set.range ιS ∪ {x₀, x₁})
        ∃ (Φ : ↥B →+* Lloc) (hιR : ∀ s : S, ιS s ∈ Rloc) (hx₀ : x₀ ∈ Rloc) (hx₁ : x₁ ∈ Rloc) (hΦR : ∀ b : ↥B, Φ b ∈ Rloc)
          (tW : W₁ →+* ResidueField A) (cR : ResidueField A)
          (ρR : ↥Rloc →+* DrinfeldCurve.CoordRing q (ResidueField A))
          (ρ : ↥B →+* DrinfeldCurve.CoordRing q (ResidueField A)),

          (∀ a : ↥(chartAlgFin A (↥K) j), Φ ⟨(a : ↥K), hCB a.2⟩ = ιS (((e₁ : CMP →+* S).comp (toC.comp germY)) a)) ∧
          (∀ (x : ↥B) (i : ↥(chartAlgFin A (↥K) j)), i ∈ J → (x : ↥K) * algebraMap A ↥K ϖt = (i : ↥K) →
              Φ x * ιS (mkS (MvPowerSeries.C (σ₁ ϖt))) = ιS (((e₁ : CMP →+* S).comp (toC.comp germY)) i)) ∧

          (∀ a : A, tW (σ₁ a) = residue A a) ∧ (∀ w : W₁, w ∈ IsLocalRing.maximalIdeal W₁ → tW w = 0) ∧

          cR ≠ 0 ∧
          (∀ F : MvPowerSeries (Fin 2) W₁, ρR ⟨ιS (mkS F), hιR (mkS F)⟩ =
              algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) (tW (MvPowerSeries.constantCoeff F))) ∧
          ρR ⟨x₀, hx₀⟩ = algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) cR * DrinfeldCurve.x q (ResidueField A) ∧
          ρR ⟨x₁, hx₁⟩ = algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) cR * DrinfeldCurve.y q (ResidueField A) ∧

          (∀ b : ↥B, ρ b = ρR ⟨Φ b, hΦR b⟩) ∧
          Function.Surjective ρ ∧
          (∀ b : ↥B, ρ b = 0 ↔ b ∈ Ideal.span ((fun c : ↥(chartAlgFin A (↥K) j) => (⟨(c : ↥K), hCB c.2⟩ : ↥B)) '' (y : Set ↥(chartAlgFin A (↥K) j)))) ∧
          (∀ a : A, ρ (algebraMap A ↥B a) = algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) (residue A a)) := by
  intro STK CMP toC S mkS germY Lloc ιS x₀ x₁ Rloc
  have hΦpkg := ModularCurve.FullLevel.AuxLevel.exists_blowupChart_ringHom_away_extends_chartMap_of_eq_adjoin
    q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ hξ hι K hK A hAq hξA j hj ϖ hϖ ϖt hϖt y hy hϖy hss z ϖz hϖz hz y' hy' hss' hy'y W₁ σ₁ hσ₁ f₁ u₁ v₁ hu₁ hv₁ hf₁ e₁ J B hB hCB hbridge hcentre inst
  obtain ⟨Φ, hιR, hx₀, hx₁, hΦR, hΦ1, hΦ2, hnz, hnzd⟩ := hΦpkg
  have hb := hbridge
  obtain ⟨-, -, -, -, hσsurj, hσcomap, -⟩ := hb
  have hLpkg := ModularCurve.FullLevel.AuxLevel.exists_localBlowupChart_ringHom_coordRing_of_chartPresentation_of_mem_nonZeroDivisors
    q A hAq ϖ ϖt hϖt W₁ σ₁ hσ₁ f₁ u₁ v₁ hu₁ hv₁ hf₁ hσsurj hσcomap hnz hnzd inst
  obtain ⟨hιR', hx₀', hx₁', tW, cR, ρR, htW1, htW2, hcR, hρF, hρx₀, hρx₁, hρsurj, hρker⟩ := hLpkg
  have hK := ModularCurve.FullLevel.AuxLevel.exists_blowupChart_ringHom_coordRing_surjective_ker_eq_span_of_chartMap_of_localFibreMap
    q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ξ hξ hι K hK A hAq hξA j hj ϖ hϖ ϖt hϖt y hy hϖy hss z ϖz hϖz hz y' hy' hss' hy'y W₁ σ₁ hσ₁ f₁ u₁ v₁ hu₁ hv₁ hf₁ e₁ J B hB hCB hbridge hcentre inst Φ hιR' hx₀' hx₁' hΦR tW cR ρR hΦ1 hΦ2 htW1 htW2 hcR hρF hρx₀ hρx₁ hρsurj hρker
  obtain ⟨ρ, h9, h10, h11, h12⟩ := hK
  exact ⟨Φ, hιR', hx₀', hx₁', hΦR, tW, cR, ρR, ρ, hΦ1, hΦ2, htW1, htW2, hcR, hρF, hρx₀, hρx₁, h9, h10, h11, h12⟩

end S_ModularCurve_FullLevel_AuxLevel_exists_blowupChart_ringHom_localBlowupChart_surjective_ker_eq_span_of_dense_of_flat
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_blowupChart_ringHom_localBlowupChart_surjective_ker_eq_span_of_dense_of_flat (solution)
