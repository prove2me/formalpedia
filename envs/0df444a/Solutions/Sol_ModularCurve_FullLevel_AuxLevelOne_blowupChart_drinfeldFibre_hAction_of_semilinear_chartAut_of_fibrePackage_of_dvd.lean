-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevelOne.blowupChart_drinfeldFibre_hAction_of_semilinear_chartAut_of_fibrePackage_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/aeea4449-1ef6-56c4-9bf0-f2fc8e84171e

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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevelOne_blowupChart_drinfeldFibre_hAction_of_semilinear_chartAut_of_fibrePackage_of_dvd

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry IsLocalRing AlgebraicCurve.TwoChartIntegralModel

open scoped MatrixGroups

namespace BlowupEqILaw

theorem exists_of_mem_span_pair_sq {S : Type} [CommRing S] (a b r : S)
    (hr : r ∈ (Ideal.span {a, b}) ^ 2) :
    ∃ z₁ ∈ Ideal.span {a, b}, ∃ z₂ ∈ Ideal.span {a, b}, r = a * z₁ + b * z₂ := by
  rw [pow_two, Ideal.span_insert, Ideal.sup_mul, Submodule.mem_sup] at hr
  obtain ⟨r₁, hr₁, r₂, hr₂, rfl⟩ := hr
  rw [Ideal.mem_span_singleton_mul] at hr₁ hr₂
  obtain ⟨z₁, hz₁, rfl⟩ := hr₁
  obtain ⟨z₂, hz₂, rfl⟩ := hr₂
  refine ⟨z₁, ?_, z₂, ?_, rfl⟩
  · simpa [Ideal.span_insert] using hz₁
  · simpa [Ideal.span_insert] using hz₂

open MvPolynomial in
theorem hAction_mk_X (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [Algebra (GaloisField q 2) k]
    (p : ↥(DrinfeldCurve.hSubgroup q)) (jj : Fin 2) :
    DrinfeldCurve.hAction q k p (DrinfeldCurve.mk q k (X jj)) =
      ∑ ii : Fin 2, algebraMap k (DrinfeldCurve.CoordRing q k)
        (DrinfeldCurve.ofZMod q k (((p : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ).1 : Matrix (Fin 2) (Fin 2) (ZMod q)) ii jj) *
          DrinfeldCurve.scalarOf q k (p : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) × (GaloisField q 2)ˣ).2) *
        DrinfeldCurve.mk q k (X ii) := by
  have hC : ∀ a : k, DrinfeldCurve.mk q k (C a) = algebraMap k (DrinfeldCurve.CoordRing q k) a := by
    intro a; rw [← MvPolynomial.algebraMap_eq]; exact AlgHom.commutes _ a
  rw [DrinfeldCurve.hAction_mk, DrinfeldCurve.substPoly_X, map_sum, map_sum]
  refine Finset.sum_congr rfl (fun ii _ => ?_)
  rw [map_mul, DrinfeldCurve.scalePoly_X, ← MvPolynomial.algebraMap_eq, AlgHom.commutes, MvPolynomial.algebraMap_eq,
    map_mul, map_mul, hC, hC, map_mul, mul_assoc]

theorem ringHom_eq_of_eqOn_gens {R T : Type} [Ring R] [Ring T] {s : Set R}
    {f g : ↥(Subring.closure s) →+* T}
    (h : ∀ (x : R) (hx : x ∈ s), f ⟨x, Subring.subset_closure hx⟩ = g ⟨x, Subring.subset_closure hx⟩) : f = g := by
  apply RingHom.ext
  rintro ⟨x, hx⟩
  induction hx using Subring.closure_induction with
  | mem x hx => exact h x hx
  | zero => change f 0 = g 0; rw [map_zero, map_zero]
  | one => change f 1 = g 1; rw [map_one, map_one]
  | add x y hx hy ihx ihy =>
      change f (⟨x, hx⟩ + ⟨y, hy⟩) = g (⟨x, hx⟩ + ⟨y, hy⟩)
      rw [map_add, map_add, ihx, ihy]
  | neg x hx ihx =>
      change f (-⟨x, hx⟩) = g (-⟨x, hx⟩)
      rw [map_neg, map_neg, ihx]
  | mul x y hx hy ihx ihy =>
      change f (⟨x, hx⟩ * ⟨y, hy⟩) = g (⟨x, hx⟩ * ⟨y, hy⟩)
      rw [map_mul, map_mul, ihx, ihy]

end BlowupEqILaw

set_option maxHeartbeats 32000000 in

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
        ∀ (Φ : ↥B →+* Lloc) (hιR : ∀ s : S, ιS s ∈ Rloc) (hx₀ : x₀ ∈ Rloc) (hx₁ : x₁ ∈ Rloc) (hΦR : ∀ b : ↥B, Φ b ∈ Rloc)
          (tW : W₁ →+* ResidueField A) (cR : ResidueField A)
          (ρR : ↥Rloc →+* DrinfeldCurve.CoordRing q (ResidueField A))
          (ρ : ↥B →+* DrinfeldCurve.CoordRing q (ResidueField A)),

          (∀ a : ↥(chartAlgFin A (↥K) j), Φ ⟨(a : ↥K), hCB a.2⟩ = ιS (((e₁ : CMP →+* S).comp (toC.comp germY)) a)) →
          (∀ (x : ↥B) (i : ↥(chartAlgFin A (↥K) j)), i ∈ J → (x : ↥K) * algebraMap A ↥K ϖt = (i : ↥K) →
              Φ x * ιS (mkS (MvPowerSeries.C (σ₁ ϖt))) = ιS (((e₁ : CMP →+* S).comp (toC.comp germY)) i)) →
          (∀ a : A, tW (σ₁ a) = residue A a) → (∀ w : W₁, w ∈ IsLocalRing.maximalIdeal W₁ → tW w = 0) →
          cR ≠ 0 →
          (∀ F : MvPowerSeries (Fin 2) W₁, ρR ⟨ιS (mkS F), hιR (mkS F)⟩ =
              algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) (tW (MvPowerSeries.constantCoeff F))) →
          ρR ⟨x₀, hx₀⟩ = algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) cR * DrinfeldCurve.x q (ResidueField A) →
          ρR ⟨x₁, hx₁⟩ = algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) cR * DrinfeldCurve.y q (ResidueField A) →
          (∀ b : ↥B, ρ b = ρR ⟨Φ b, hΦR b⟩) →

          ∀ (τ : ↥K ≃+* ↥K)
            (hτC : ∀ a : ↥K, a ∈ chartAlgFin A (↥K) j → τ a ∈ chartAlgFin A (↥K) j)
            (hτB : ∀ f : ↥K, f ∈ B → τ f ∈ B)
            (θ : S ≃+* S) (σW : W₁ ≃+* W₁) (ta tm : W₁) (M : Matrix (Fin 2) (Fin 2) W₁)
            (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)) (c : (GaloisField q 2)ˣ)
            (hmem : (g, c) ∈ DrinfeldCurve.hSubgroup q),

            (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
              θ (e₁ (toC (germY a))) = e₁ (toC (germY ((τ.toRingHom.restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
              (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hτC) a)))) →

            (∀ w : W₁, θ (mkS (MvPowerSeries.C w)) = mkS (MvPowerSeries.C (σW w))) →
            (∀ w : W₁, σW w - w ∈ IsLocalRing.maximalIdeal W₁) →

            IsUnit ta → tm ∈ IsLocalRing.maximalIdeal W₁ → σW (σ₁ ϖt) = ta * σ₁ ϖt * (1 + tm) →

            (∀ jj : Fin 2, θ (mkS (MvPowerSeries.X jj)) -
                mkS (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) ∈
              (Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2) →

            (∀ ii jj : Fin 2, tW (M ii jj) =
                tW ta * algebraMap (GaloisField q 2) (ResidueField A) ((c : (GaloisField q 2)ˣ) : GaloisField q 2) *
                  ((((g : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q)) ii jj).val : ResidueField A)) →

            ∀ (b : ↥B) (hb : τ (b : ↥K) ∈ B),
              ρ ⟨τ (b : ↥K), hb⟩ = DrinfeldCurve.hAction q (ResidueField A) ⟨(g, c), hmem⟩ (ρ b) := by
  intro STK CMP toC S mkS germY Lloc ιS x₀ x₁ Rloc
  intro Φ hιR hx₀ hx₁ hΦR tW cR ρR ρ hΦC hΦJ htW1 htW2 hcR hρRS hρRx0 hρRx1 hρΦ
  intro τ hτC hτB θ σW ta tm M g c hmem hθΨ hθW hσW hta htm hσWt hθlin hMres
  classical
  have hcenΨ := hbridge.1
  have hdense := hbridge.2.1
  have hconstΨ := hbridge.2.2.1
  have hres := hbridge.2.2.2.1
  have hmaxu := hbridge.2.2.2.2.2.2.2.1

  let ιR : S →+* ↥Rloc := ιS.codRestrict Rloc hιR
  let χS : S →+* DrinfeldCurve.CoordRing q (ResidueField A) := ρR.comp ιR
  have hχS_mk : ∀ F : MvPowerSeries (Fin 2) W₁,
      χS (mkS F) = algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) (tW (MvPowerSeries.constantCoeff F)) :=
    fun F => hρRS F
  have hχS_M : ∀ s : S, s ∈ Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖ)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)} → χS s = 0 := by
    have hle : Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖ)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)} ≤ RingHom.ker χS := by
      rw [Ideal.span_le]
      intro s hs
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      rw [SetLike.mem_coe, RingHom.mem_ker]
      rcases hs with rfl | rfl | rfl
      · rw [hχS_mk, MvPowerSeries.constantCoeff_C, htW1]
        have : residue A ϖ = 0 := by
          rw [IsLocalRing.residue_eq_zero_iff, hϖ]; exact Ideal.mem_span_singleton_self ϖ
        rw [this, map_zero]
      · rw [hχS_mk, MvPowerSeries.constantCoeff_X, map_zero, map_zero]
      · rw [hχS_mk, MvPowerSeries.constantCoeff_X, map_zero, map_zero]
    intro s hs; exact hle hs

  haveI hMmax : (Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖ)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}).IsMaximal := hbridge.2.2.2.2.2.2.1
  have hθM : ∀ s : S, s ∈ Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖ)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)} → θ s ∈ Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖ)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)} := by
    have hc : Ideal.comap (θ : S →+* S) (Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖ)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) = Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖ)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)} := by
      haveI := Ideal.comap_isMaximal_of_surjective (θ : S →+* S) θ.surjective (K := Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖ)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)})
      exact hmaxu _ this
    intro s hs
    have : s ∈ Ideal.comap (θ : S →+* S) (Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖ)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) := by rw [hc]; exact hs
    exact Ideal.mem_comap.mp this

  have htWσ : ∀ w : W₁, tW (σW w) = tW w := by
    intro w
    have := htW2 _ (hσW w)
    rwa [map_sub, sub_eq_zero] at this
  have hχθ : ∀ s : S, χS (θ s) = χS s := by
    intro s
    have hda := hdense 1 s
    obtain ⟨a, ha⟩ := hda
    have hra := hres a
    obtain ⟨a₀, ha₀⟩ := hra
    replace ha := Ideal.pow_le_self one_ne_zero ha
    have h1 : s - mkS (MvPowerSeries.C (σ₁ a₀)) ∈ Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖ)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)} := by
      have h2 : ((e₁ : CMP →+* S).comp (toC.comp germY)) (a - algebraMap A ↥(chartAlgFin A (↥K) j) a₀) ∈ Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖ)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)} := by
        have : a - algebraMap A ↥(chartAlgFin A (↥K) j) a₀ ∈ Ideal.comap ((e₁ : CMP →+* S).comp (toC.comp germY)) (Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖ)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) := by
          rw [hcenΨ]; exact ha₀
        exact Ideal.mem_comap.mp this
      rw [map_sub, hconstΨ] at h2
      have : s - mkS (MvPowerSeries.C (σ₁ a₀)) =
          (((e₁ : CMP →+* S).comp (toC.comp germY)) a - mkS (MvPowerSeries.C (σ₁ a₀))) - (((e₁ : CMP →+* S).comp (toC.comp germY)) a - s) := by ring
      rw [this]; exact Ideal.sub_mem _ h2 ha
    have e1 : χS s = χS (mkS (MvPowerSeries.C (σ₁ a₀))) := by
      rw [← sub_eq_zero, ← map_sub]; exact hχS_M _ h1
    have e2 : χS (θ s) = χS (θ (mkS (MvPowerSeries.C (σ₁ a₀)))) := by
      rw [← sub_eq_zero, ← map_sub, ← map_sub]; exact hχS_M _ (hθM _ h1)
    rw [e1, e2, hθW, hχS_mk, hχS_mk, MvPowerSeries.constantCoeff_C, MvPowerSeries.constantCoeff_C, htWσ]

  have h1tm : IsUnit (1 + tm) := by
    by_contra hnu
    have hmem1 : (1 + tm) ∈ IsLocalRing.maximalIdeal W₁ := (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu)
    have : (1 : W₁) ∈ IsLocalRing.maximalIdeal W₁ := by
      have := Ideal.sub_mem _ hmem1 htm
      rwa [add_sub_cancel_right] at this
    exact (IsLocalRing.maximalIdeal.isMaximal W₁).ne_top ((Ideal.eq_top_iff_one _).mpr this)
  obtain ⟨wU, hwU⟩ : ∃ wU : W₁ˣ, (wU : W₁) = ta * (1 + tm) := ⟨(hta.mul h1tm).unit, by simp⟩
  let u : S := mkS (MvPowerSeries.C (wU : W₁))
  let uinv : S := mkS (MvPowerSeries.C ((wU⁻¹ : W₁ˣ) : W₁))
  have huu : u * uinv = 1 := by
    show mkS (MvPowerSeries.C (wU : W₁)) * mkS (MvPowerSeries.C ((wU⁻¹ : W₁ˣ) : W₁)) = 1
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  have hθt : θ (mkS (MvPowerSeries.C (σ₁ ϖt))) = u * mkS (MvPowerSeries.C (σ₁ ϖt)) := by
    rw [hθW, hσWt]
    show mkS (MvPowerSeries.C (ta * σ₁ ϖt * (1 + tm))) = mkS (MvPowerSeries.C (wU : W₁)) * mkS (MvPowerSeries.C (σ₁ ϖt))
    rw [← map_mul, ← map_mul, hwU]
    congr 2; ring
  have htWu : tW (wU : W₁) = tW ta := by
    rw [hwU, map_mul, map_add, map_one, htW2 _ htm, add_zero, mul_one]
  have htWta : tW ta ≠ 0 := (hta.map tW).ne_zero
  have hχuinv : χS uinv = algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) ((tW ta)⁻¹) := by
    show χS (mkS (MvPowerSeries.C ((wU⁻¹ : W₁ˣ) : W₁))) = _
    rw [hχS_mk, MvPowerSeries.constantCoeff_C]
    congr 1
    rw [← htWu]
    have hm : tW ((wU⁻¹ : W₁ˣ) : W₁) * tW (wU : W₁) = 1 := by rw [← map_mul, Units.inv_mul, map_one]
    have hne : tW (wU : W₁) ≠ 0 := by rw [htWu]; exact htWta
    exact (eq_inv_of_mul_eq_one_left hm)

  have hu : IsUnit (ιS (mkS (MvPowerSeries.C (σ₁ ϖt)))) := IsLocalization.Away.algebraMap_isUnit _
  have hιu : IsUnit (ιS u) := by
    exact IsUnit.of_mul_eq_one (ιS uinv) (by rw [← map_mul, huu, map_one])
  have hunit : IsUnit ((ιS.comp (θ : S →+* S)) (mkS (MvPowerSeries.C (σ₁ ϖt)))) := by
    rw [RingHom.comp_apply]
    show IsUnit (ιS (θ (mkS (MvPowerSeries.C (σ₁ ϖt)))))
    rw [hθt, map_mul]
    exact hιu.mul hu
  let θL : Lloc →+* Lloc := IsLocalization.Away.lift (mkS (MvPowerSeries.C (σ₁ ϖt))) hunit
  have hθLι : ∀ s : S, θL (ιS s) = ιS (θ s) := fun s => IsLocalization.Away.lift_eq _ hunit s
  have hinv1 : ιS (mkS (MvPowerSeries.C (σ₁ ϖt))) * IsLocalization.Away.invSelf (S := Lloc) (mkS (MvPowerSeries.C (σ₁ ϖt))) = 1 := IsLocalization.Away.mul_invSelf _
  have hθLinv : θL (IsLocalization.Away.invSelf (S := Lloc) (mkS (MvPowerSeries.C (σ₁ ϖt)))) = IsLocalization.Away.invSelf (S := Lloc) (mkS (MvPowerSeries.C (σ₁ ϖt))) * ιS uinv := by
    have hU : IsUnit (ιS (θ (mkS (MvPowerSeries.C (σ₁ ϖt))))) := by rw [hθt, map_mul]; exact hιu.mul hu
    have h2 : ιS (θ (mkS (MvPowerSeries.C (σ₁ ϖt)))) * θL (IsLocalization.Away.invSelf (S := Lloc) (mkS (MvPowerSeries.C (σ₁ ϖt)))) = 1 := by
      rw [← hθLι, ← map_mul, hinv1, map_one]
    have h3 : ιS (θ (mkS (MvPowerSeries.C (σ₁ ϖt)))) * (IsLocalization.Away.invSelf (S := Lloc) (mkS (MvPowerSeries.C (σ₁ ϖt))) * ιS uinv) = 1 := by
      rw [hθt, map_mul]
      calc ιS u * ιS (mkS (MvPowerSeries.C (σ₁ ϖt))) * (IsLocalization.Away.invSelf (S := Lloc) (mkS (MvPowerSeries.C (σ₁ ϖt))) * ιS uinv)
          = (ιS (mkS (MvPowerSeries.C (σ₁ ϖt))) * IsLocalization.Away.invSelf (S := Lloc) (mkS (MvPowerSeries.C (σ₁ ϖt)))) * (ιS u * ιS uinv) := by ring
        _ = 1 := by rw [hinv1, ← map_mul, huu, map_one, one_mul]
    exact hU.mul_right_injective (h2.trans h3.symm)

  let τC : ↥(chartAlgFin A (↥K) j) →+* ↥(chartAlgFin A (↥K) j) := τ.toRingHom.restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hτC
  let τB : ↥B →+* ↥B := τ.toRingHom.restrict B B hτB
  have hτBv : ∀ b : ↥B, ((τB b : ↥B) : ↥K) = τ (b : ↥K) := fun b => rfl
  have hBmem : ∀ x : ↥K, x ∈ Algebra.adjoin ↥(chartAlgFin A (↥K) j) {x : ↥K | ∃ i ∈ J, x * algebraMap A ↥K ϖt = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)} ↔ x ∈ B := by
    intro x; rw [hB, Subalgebra.mem_restrictScalars]
  have hPSI : ∀ a : ↥(chartAlgFin A (↥K) j), ((e₁ : CMP →+* S).comp (toC.comp germY)) a = e₁ (toC (germY a)) := fun a => rfl

  have hΦτC : ∀ (cc : ↥(chartAlgFin A (↥K) j)) (h : τ ((cc : ↥(chartAlgFin A (↥K) j)) : ↥K) ∈ B),
      Φ ⟨τ ((cc : ↥(chartAlgFin A (↥K) j)) : ↥K), h⟩ = θL (Φ ⟨(cc : ↥K), hCB cc.2⟩) := by
    intro cc h
    have e0 : (⟨τ ((cc : ↥(chartAlgFin A (↥K) j)) : ↥K), h⟩ : ↥B) = ⟨((τC cc : ↥(chartAlgFin A (↥K) j)) : ↥K), hCB (τC cc).2⟩ := Subtype.ext rfl
    rw [e0, hΦC, hΦC, hθLι, hPSI, hPSI, hθΨ cc]
  have hΦτ : ∀ b : ↥B, Φ (τB b) = θL (Φ b) := by
    suffices h : ∀ x : ↥K, x ∈ Algebra.adjoin ↥(chartAlgFin A (↥K) j) {x : ↥K | ∃ i ∈ J, x * algebraMap A ↥K ϖt = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)} →
        ∀ hx : x ∈ B, Φ (τB ⟨x, hx⟩) = θL (Φ ⟨x, hx⟩) by
      intro b; exact h b.1 ((hBmem _).mpr b.2) b.2
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hxS =>
        intro hxB
        obtain ⟨i, hiJ, hxi⟩ := hxS

        have hϖtB : algebraMap A ↥K ϖt ∈ B := by
          have : algebraMap A ↥K ϖt = ((algebraMap A ↥(chartAlgFin A (↥K) j) ϖt : ↥(chartAlgFin A (↥K) j)) : ↥K) := (Subalgebra.coe_algebraMap _ _).symm
          rw [this]; exact hCB (algebraMap A ↥(chartAlgFin A (↥K) j) ϖt).2
        have hprodB : (⟨x, hxB⟩ : ↥B) * ⟨algebraMap A ↥K ϖt, hϖtB⟩ = ⟨((i : ↥(chartAlgFin A (↥K) j)) : ↥K), hCB i.2⟩ := Subtype.ext hxi

        have e1 := congrArg (fun bb : ↥B => Φ (τB bb)) hprodB
        simp only [map_mul] at e1

        have e2 : Φ (τB ⟨algebraMap A ↥K ϖt, hϖtB⟩) = θL (ιS (mkS (MvPowerSeries.C (σ₁ ϖt)))) := by
          have h0 : (⟨algebraMap A ↥K ϖt, hϖtB⟩ : ↥B) = ⟨((algebraMap A ↥(chartAlgFin A (↥K) j) ϖt : ↥(chartAlgFin A (↥K) j)) : ↥K), hCB (algebraMap A ↥(chartAlgFin A (↥K) j) ϖt).2⟩ :=
            Subtype.ext (Subalgebra.coe_algebraMap _ _).symm
          have h0' : τB ⟨algebraMap A ↥K ϖt, hϖtB⟩ = ⟨τ (((algebraMap A ↥(chartAlgFin A (↥K) j) ϖt : ↥(chartAlgFin A (↥K) j)) : ↥K)), hτB _ (hCB (algebraMap A ↥(chartAlgFin A (↥K) j) ϖt).2)⟩ := by
            apply Subtype.ext; rw [hτBv, h0]
          rw [h0', hΦτC, hΦC, hPSI, ← hPSI, hconstΨ]
        have e3 : Φ (τB ⟨((i : ↥(chartAlgFin A (↥K) j)) : ↥K), hCB i.2⟩) = θL (Φ ⟨x, hxB⟩ * ιS (mkS (MvPowerSeries.C (σ₁ ϖt)))) := by
          have h0' : τB ⟨((i : ↥(chartAlgFin A (↥K) j)) : ↥K), hCB i.2⟩ = ⟨τ ((i : ↥(chartAlgFin A (↥K) j)) : ↥K), hτB _ (hCB i.2)⟩ := Subtype.ext rfl
          rw [h0', hΦτC, hΦJ ⟨x, hxB⟩ i hiJ hxi, hΦC]
        rw [e2, e3, map_mul] at e1
        have hU : IsUnit (θL (ιS (mkS (MvPowerSeries.C (σ₁ ϖt))))) := by rw [hθLι, hθt, map_mul]; exact hιu.mul hu
        exact (hU.mul_left_inj).mp e1
    | algebraMap cc =>
        intro hxB
        have h0 : (⟨algebraMap ↥(chartAlgFin A (↥K) j) ↥K cc, hxB⟩ : ↥B) = ⟨(cc : ↥K), hCB cc.2⟩ := rfl
        have h0' : τB ⟨algebraMap ↥(chartAlgFin A (↥K) j) ↥K cc, hxB⟩ = ⟨τ ((cc : ↥(chartAlgFin A (↥K) j)) : ↥K), hτB _ (hCB cc.2)⟩ := Subtype.ext rfl
        rw [h0', hΦτC, h0]
    | add x y hx hy ihx ihy =>
        intro hxyB
        have hxB : x ∈ B := (hBmem _).mp hx
        have hyB : y ∈ B := (hBmem _).mp hy
        have : (⟨x + y, hxyB⟩ : ↥B) = ⟨x, hxB⟩ + ⟨y, hyB⟩ := rfl
        rw [this]; simp only [map_add]; rw [ihx hxB, ihy hyB]
    | mul x y hx hy ihx ihy =>
        intro hxyB
        have hxB : x ∈ B := (hBmem _).mp hx
        have hyB : y ∈ B := (hBmem _).mp hy
        have : (⟨x * y, hxyB⟩ : ↥B) = ⟨x, hxB⟩ * ⟨y, hyB⟩ := rfl
        rw [this]; simp only [map_mul]; rw [ihx hxB, ihy hyB]

  have hXle : Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)} ≤ Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖ)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)} :=
    Ideal.span_mono (by intro s hs; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ⊢; tauto)
  have hcoef : ∀ jj : Fin 2, ∃ t₀ t₁ : S, θ (mkS (MvPowerSeries.X jj)) = mkS (MvPowerSeries.X 0) * t₀ + mkS (MvPowerSeries.X 1) * t₁ ∧
      χS t₀ = algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) (tW (M 0 jj)) ∧ χS t₁ = algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) (tW (M 1 jj)) := by
    intro jj
    have hsq := BlowupEqILaw.exists_of_mem_span_pair_sq (mkS (MvPowerSeries.X 0)) (mkS (MvPowerSeries.X 1)) _ (hθlin jj)
    obtain ⟨z₁, hz₁, z₂, hz₂, hr⟩ := hsq
    refine ⟨mkS (MvPowerSeries.C (M 0 jj)) + z₁, mkS (MvPowerSeries.C (M 1 jj)) + z₂, ?_, ?_, ?_⟩
    · have h2 : θ (mkS (MvPowerSeries.X jj)) = mkS (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) +
          (mkS (MvPowerSeries.X 0) * z₁ + mkS (MvPowerSeries.X 1) * z₂) := by
        rw [← hr]; abel
      rw [h2, map_sum, Fin.sum_univ_two, map_mul, map_mul]
      ring
    · rw [map_add, hχS_mk, MvPowerSeries.constantCoeff_C, hχS_M _ (hXle hz₁), add_zero]
    · rw [map_add, hχS_mk, MvPowerSeries.constantCoeff_C, hχS_M _ (hXle hz₂), add_zero]
  have hcoef0 := hcoef 0
  have hcoef1 := hcoef 1
  obtain ⟨t₀₀, t₁₀, hθX0, hχt₀₀, hχt₁₀⟩ := hcoef0
  obtain ⟨t₀₁, t₁₁, hθX1, hχt₀₁, hχt₁₁⟩ := hcoef1
  have hθLx : ∀ (jj : Fin 2) (t₀ t₁ : S), θ (mkS (MvPowerSeries.X jj)) = mkS (MvPowerSeries.X 0) * t₀ + mkS (MvPowerSeries.X 1) * t₁ →
      θL (ιS (mkS (MvPowerSeries.X jj)) * IsLocalization.Away.invSelf (S := Lloc) (mkS (MvPowerSeries.C (σ₁ ϖt)))) = (ιS t₀ * x₀ + ιS t₁ * x₁) * ιS uinv := by
    intro jj t₀ t₁ h
    rw [map_mul, hθLι, hθLinv, h, map_add, map_mul, map_mul]
    show (ιS (mkS (MvPowerSeries.X 0)) * ιS t₀ + ιS (mkS (MvPowerSeries.X 1)) * ιS t₁) * (IsLocalization.Away.invSelf (S := Lloc) (mkS (MvPowerSeries.C (σ₁ ϖt))) * ιS uinv) =
      (ιS t₀ * (ιS (mkS (MvPowerSeries.X 0)) * IsLocalization.Away.invSelf (S := Lloc) (mkS (MvPowerSeries.C (σ₁ ϖt)))) + ιS t₁ * (ιS (mkS (MvPowerSeries.X 1)) * IsLocalization.Away.invSelf (S := Lloc) (mkS (MvPowerSeries.C (σ₁ ϖt))))) * ιS uinv
    ring
  have hθLx0 : θL x₀ = (ιS t₀₀ * x₀ + ιS t₁₀ * x₁) * ιS uinv := hθLx 0 t₀₀ t₁₀ hθX0
  have hθLx1 : θL x₁ = (ιS t₀₁ * x₀ + ιS t₁₁ * x₁) * ιS uinv := hθLx 1 t₀₁ t₁₁ hθX1

  have hθLR : ∀ r : Lloc, r ∈ Rloc → θL r ∈ Rloc := by
    have hle : Rloc ≤ Subring.comap θL Rloc := by
      show Subring.closure (Set.range ιS ∪ {x₀, x₁}) ≤ _
      rw [Subring.closure_le]
      rintro r (⟨s, rfl⟩ | hr01)
      · show θL (ιS s) ∈ Rloc
        rw [hθLι]; exact hιR _
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr01
        rcases hr01 with rfl | rfl
        · show θL x₀ ∈ Rloc
          rw [hθLx0]
          exact Subring.mul_mem _ (Subring.add_mem _ (Subring.mul_mem _ (hιR _) hx₀) (Subring.mul_mem _ (hιR _) hx₁)) (hιR _)
        · show θL x₁ ∈ Rloc
          rw [hθLx1]
          exact Subring.mul_mem _ (Subring.add_mem _ (Subring.mul_mem _ (hιR _) hx₀) (Subring.mul_mem _ (hιR _) hx₁)) (hιR _)
    intro r hr; exact hle hr

  have hρRι : ∀ (s : S) (h : ιS s ∈ Rloc), ρR ⟨ιS s, h⟩ = χS s := fun s h => rfl
  have hactC : ∀ t : ResidueField A, DrinfeldCurve.hAction q (ResidueField A) ⟨(g, c), hmem⟩ (algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) t) = algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) t :=
    fun t => AlgEquiv.commutes _ t

  have hofZMod : ∀ ii jj : Fin 2, DrinfeldCurve.ofZMod q (ResidueField A) (((g : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q)) ii jj) =
      (((((g : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q)) ii jj).val : ℕ) : ResidueField A) := by
    intro ii jj
    conv_lhs => rw [← ZMod.natCast_zmod_val ((((g : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q)) ii jj))]
    rw [map_natCast]
  have hMres' : ∀ ii jj : Fin 2, tW (M ii jj) * (tW ta)⁻¹ =
      DrinfeldCurve.ofZMod q (ResidueField A) (((g : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q)) ii jj) *
        algebraMap (GaloisField q 2) (ResidueField A) ((c : (GaloisField q 2)ˣ) : GaloisField q 2) := by
    intro ii jj
    rw [hMres, hofZMod]
    field_simp
  have hactx : ∀ jj : Fin 2, DrinfeldCurve.hAction q (ResidueField A) ⟨(g, c), hmem⟩ (DrinfeldCurve.mk q (ResidueField A) (MvPolynomial.X jj)) =
      ∑ ii : Fin 2, algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) (tW (M ii jj) * (tW ta)⁻¹) * DrinfeldCurve.mk q (ResidueField A) (MvPolynomial.X ii) := by
    intro jj
    rw [BlowupEqILaw.hAction_mk_X]
    refine Finset.sum_congr rfl (fun ii _ => ?_)
    rw [hMres']
    rfl

  have hρx0 : DrinfeldCurve.hAction q (ResidueField A) ⟨(g, c), hmem⟩ (algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) cR * DrinfeldCurve.x q (ResidueField A)) =
      (algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) (tW (M 0 0)) * (algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) cR * DrinfeldCurve.x q (ResidueField A)) + algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) (tW (M 1 0)) * (algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) cR * DrinfeldCurve.y q (ResidueField A))) * algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) ((tW ta)⁻¹) := by
    show DrinfeldCurve.hAction q (ResidueField A) ⟨(g, c), hmem⟩ (algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) cR * DrinfeldCurve.mk q (ResidueField A) (MvPolynomial.X 0)) =
      (algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) (tW (M 0 0)) * (algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) cR * DrinfeldCurve.mk q (ResidueField A) (MvPolynomial.X 0)) + algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) (tW (M 1 0)) * (algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) cR * DrinfeldCurve.mk q (ResidueField A) (MvPolynomial.X 1))) * algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) ((tW ta)⁻¹)
    rw [map_mul, hactC, hactx, Fin.sum_univ_two, map_mul, map_mul]; ring
  have hρx1 : DrinfeldCurve.hAction q (ResidueField A) ⟨(g, c), hmem⟩ (algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) cR * DrinfeldCurve.y q (ResidueField A)) =
      (algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) (tW (M 0 1)) * (algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) cR * DrinfeldCurve.x q (ResidueField A)) + algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) (tW (M 1 1)) * (algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) cR * DrinfeldCurve.y q (ResidueField A))) * algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) ((tW ta)⁻¹) := by
    show DrinfeldCurve.hAction q (ResidueField A) ⟨(g, c), hmem⟩ (algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) cR * DrinfeldCurve.mk q (ResidueField A) (MvPolynomial.X 1)) =
      (algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) (tW (M 0 1)) * (algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) cR * DrinfeldCurve.mk q (ResidueField A) (MvPolynomial.X 0)) + algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) (tW (M 1 1)) * (algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) cR * DrinfeldCurve.mk q (ResidueField A) (MvPolynomial.X 1))) * algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) ((tW ta)⁻¹)
    rw [map_mul, hactC, hactx, Fin.sum_univ_two, map_mul, map_mul]; ring

  let θR : ↥Rloc →+* ↥Rloc := θL.restrict Rloc Rloc hθLR
  let G₁ : ↥Rloc →+* DrinfeldCurve.CoordRing q (ResidueField A) := ρR.comp θR
  let G₂ : ↥Rloc →+* DrinfeldCurve.CoordRing q (ResidueField A) :=
    (DrinfeldCurve.hAction q (ResidueField A) ⟨(g, c), hmem⟩).toAlgHom.toRingHom.comp ρR
  have hG₁ : ∀ (r : Lloc) (hr : r ∈ Rloc), G₁ ⟨r, hr⟩ = ρR ⟨θL r, hθLR r hr⟩ := fun r hr => rfl
  have hG₂ : ∀ (r : Lloc) (hr : r ∈ Rloc), G₂ ⟨r, hr⟩ = DrinfeldCurve.hAction q (ResidueField A) ⟨(g, c), hmem⟩ (ρR ⟨r, hr⟩) := fun r hr => rfl
  have hG : G₁ = G₂ := by
    apply BlowupEqILaw.ringHom_eq_of_eqOn_gens
    intro r hr
    rw [hG₁, hG₂]
    rcases hr with ⟨s, rfl⟩ | hr01
    · have e1 : (⟨θL (ιS s), hθLR _ (Subring.subset_closure (Or.inl ⟨s, rfl⟩))⟩ : ↥Rloc) = ⟨ιS (θ s), hιR _⟩ :=
        Subtype.ext (hθLι s)
      rw [e1, hρRι, hρRι, hχθ]
      have hF := Ideal.Quotient.mk_surjective s
      obtain ⟨F, rfl⟩ := hF
      have e5 : χS (Ideal.Quotient.mk _ F) = algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) (tW (MvPowerSeries.constantCoeff F)) := hχS_mk F
      rw [e5, hactC]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr01
      rcases hr01 with rfl | rfl
      · have e1 : (⟨θL x₀, hθLR _ (Subring.subset_closure (Or.inr (by simp)))⟩ : ↥Rloc) =
            (ιR t₀₀ * ⟨x₀, hx₀⟩ + ιR t₁₀ * ⟨x₁, hx₁⟩) * ιR uinv := Subtype.ext hθLx0
        have e2 : (⟨x₀, Subring.subset_closure (Or.inr (by simp))⟩ : ↥Rloc) = ⟨x₀, hx₀⟩ := rfl
        rw [e1, e2, map_mul, map_add, map_mul, map_mul]
        show (χS t₀₀ * ρR ⟨x₀, hx₀⟩ + χS t₁₀ * ρR ⟨x₁, hx₁⟩) * χS uinv = DrinfeldCurve.hAction q (ResidueField A) ⟨(g, c), hmem⟩ (ρR ⟨x₀, hx₀⟩)
        rw [hρRx0, hρRx1, hρx0, hχt₀₀, hχt₁₀, hχuinv]
      · have e1 : (⟨θL x₁, hθLR _ (Subring.subset_closure (Or.inr (by simp)))⟩ : ↥Rloc) =
            (ιR t₀₁ * ⟨x₀, hx₀⟩ + ιR t₁₁ * ⟨x₁, hx₁⟩) * ιR uinv := Subtype.ext hθLx1
        have e2 : (⟨x₁, Subring.subset_closure (Or.inr (by simp))⟩ : ↥Rloc) = ⟨x₁, hx₁⟩ := rfl
        rw [e1, e2, map_mul, map_add, map_mul, map_mul]
        show (χS t₀₁ * ρR ⟨x₀, hx₀⟩ + χS t₁₁ * ρR ⟨x₁, hx₁⟩) * χS uinv = DrinfeldCurve.hAction q (ResidueField A) ⟨(g, c), hmem⟩ (ρR ⟨x₁, hx₁⟩)
        rw [hρRx0, hρRx1, hρx1, hχt₀₁, hχt₁₁, hχuinv]

  intro b hb
  have e2 : (⟨Φ (τB b), hΦR (τB b)⟩ : ↥Rloc) = ⟨θL (Φ b), hθLR _ (hΦR b)⟩ := Subtype.ext (hΦτ b)
  calc ρ ⟨τ (b : ↥K), hb⟩ = ρ (τB b) := rfl
    _ = ρR ⟨Φ (τB b), hΦR (τB b)⟩ := hρΦ _
    _ = ρR ⟨θL (Φ b), hθLR _ (hΦR b)⟩ := by rw [e2]
    _ = G₁ ⟨Φ b, hΦR b⟩ := (hG₁ _ _).symm
    _ = G₂ ⟨Φ b, hΦR b⟩ := by rw [hG]
    _ = DrinfeldCurve.hAction q (ResidueField A) ⟨(g, c), hmem⟩ (ρR ⟨Φ b, hΦR b⟩) := hG₂ _ _
    _ = DrinfeldCurve.hAction q (ResidueField A) ⟨(g, c), hmem⟩ (ρ b) := by rw [hρΦ]

end S_ModularCurve_FullLevel_AuxLevelOne_blowupChart_drinfeldFibre_hAction_of_semilinear_chartAut_of_fibrePackage_of_dvd
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevelOne_blowupChart_drinfeldFibre_hAction_of_semilinear_chartAut_of_fibrePackage_of_dvd (solution)
