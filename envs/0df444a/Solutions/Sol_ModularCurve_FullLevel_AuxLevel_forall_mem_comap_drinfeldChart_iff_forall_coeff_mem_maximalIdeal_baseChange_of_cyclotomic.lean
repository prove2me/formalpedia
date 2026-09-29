-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevel.forall_mem_comap_drinfeldChart_iff_forall_coeff_mem_maximalIdeal_baseChange_of_cyclotomic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/7ae494a9-8609-5c12-81e0-e3da8572e90b

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AdicCompletionLocalRing
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_stalk_iso_localization_atPrime_of_iotaFin_apply_eq
import Theorems.Thm_ModularCurve_linearIndependent_coeffMap_of_linearIndependent
import Theorems.Thm_AdicCompletion_eq_maximalIdeal_of_comap_algebraMap_eq_maximalIdeal
import Theorems.Thm_Ideal_IsMaximal_of_isPrime_of_ne_bot_of_isIntegral_adjoin_singleton
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevel_forall_mem_comap_drinfeldChart_iff_forall_coeff_mem_maximalIdeal_baseChange_of_cyclotomic

set_option autoImplicit false
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry

open scoped MatrixGroups TensorProduct

namespace WAnchor

open ModularCurve

theorem coeffMap_injective {R L : Type} [CommRing R] [CommRing L] (ι : R →+* L)
    (hι : Function.Injective ι) : Function.Injective (coeffMap ι) := by
  intro x y h
  ext n
  apply hι
  have := congrArg (fun s => HahnSeries.coeff s n) h
  simpa [coeffMap_coeff] using this

theorem exists_ringHom_coeffMap_comp_eq {R L B : Type} [CommRing R] [CommRing L] [CommRing B]
    (ι : R →+* L) (hι : Function.Injective ι) (v : B →+* LaurentSeries L)
    (hv : ∀ (b : B) (n : ℤ), ∃ m : R, (v b).coeff n = ι m) :
    ∃ τ : B →+* LaurentSeries R, ∀ b, coeffMap ι (τ b) = v b := by
  classical

  have key : ∀ s : LaurentSeries L, (∀ n : ℤ, ∃ m : R, s.coeff n = ι m) →
      ∃ t : LaurentSeries R, coeffMap ι t = s := by
    intro s hs
    choose f hf using hs
    refine ⟨⟨f, s.isPWO_support'.mono ?_⟩, ?_⟩
    · intro n hn
      rw [Function.mem_support] at hn ⊢
      intro h0
      apply hn
      have h1 := hf n
      rw [h0] at h1
      have : ι (f n) = ι 0 := by rw [← h1, map_zero]
      exact hι this
    · ext n
      simp only [coeffMap_coeff]
      exact (hf n).symm
  choose pre hpre using key
  have hinj := coeffMap_injective ι hι
  refine ⟨{ toFun := fun b => pre (v b) (hv b)
            map_one' := hinj (by rw [hpre, map_one, map_one])
            map_mul' := fun a b => hinj (by rw [hpre, map_mul, map_mul, hpre, hpre])
            map_zero' := hinj (by rw [hpre, map_zero, map_zero])
            map_add' := fun a b => hinj (by rw [hpre, map_add, map_add, hpre, hpre]) }, fun b => ?_⟩
  exact hpre (v b) (hv b)

theorem baseChange_induction {A₀ A B₀ B : Type} [CommRing A₀] [CommRing A] [CommRing B₀] [CommRing B]
    [Algebra A₀ A] [Algebra A₀ B₀] [Algebra A B]
    (c : B₀ →+* B) (β : A ⊗[A₀] B₀ ≃+* B)
    (hβ : ∀ (a : A) (b : B₀), β (a ⊗ₜ[A₀] b) = algebraMap A B a * c b)
    {p : B → Prop} (h0 : p 0) (htmul : ∀ (a : A) (b : B₀), p (algebraMap A B a * c b))
    (hadd : ∀ x y, p x → p y → p (x + y)) (x : B) : p x := by
  obtain ⟨t, rfl⟩ := β.surjective x
  induction t using TensorProduct.induction_on with
  | zero => simpa using h0
  | tmul a b => rw [hβ]; exact htmul a b
  | add s t hs ht => rw [map_add]; exact hadd _ _ hs ht

theorem exists_finset_of_baseChange {A₀ A B₀ B : Type} [CommRing A₀] [CommRing A] [CommRing B₀] [CommRing B]
    [Algebra A₀ A] [Algebra A₀ B₀] [Algebra A B]
    (c : B₀ →+* B) (β : A ⊗[A₀] B₀ ≃+* B)
    (hβ : ∀ (a : A) (b : B₀), β (a ⊗ₜ[A₀] b) = algebraMap A B a * c b) (x : B) :
    ∃ s : Finset (A × B₀), x = ∑ ab ∈ s, algebraMap A B ab.1 * c ab.2 := by
  classical
  obtain ⟨t, rfl⟩ := β.surjective x
  obtain ⟨s, hs⟩ := TensorProduct.exists_finset t
  refine ⟨s, ?_⟩
  rw [hs, map_sum]
  exact Finset.sum_congr rfl fun ab _ => hβ ab.1 ab.2

end WAnchor

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (hι : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [IsAlgClosed (IsLocalRing.ResidueField A)]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})

    (t : A) (ht : ∃ w : A, IsUnit w ∧ t ^ (q - 1) = (q : A) * w)
    (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j))
    (ϖz : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
    (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
      (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
    (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
    (y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j))
    (hy : (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y = z)
    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω),
      RingHom.ker φ = y.asIdeal →
        φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω)

    (L₀ : Type) [Field L₀] [CharZero L₀] [IsCyclotomicExtension {q * ℓ} ℚ L₀]
    (ζ₀ : L₀) (hζ₀ : IsPrimitiveRoot ζ₀ q)
    (ξ₀ : L₀) (hξ₀ : IsPrimitiveRoot ξ₀ (q * ℓ))
    (K₀ : IntermediateField L₀ (LaurentSeries L₀))
    (hK₀ : K₀ = ModularCurve.laurentBaseChange L₀
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀] [Algebra A₀ L₀] [IsFractionRing A₀ L₀]
    (hA₀q : (q : A₀) ∈ IsLocalRing.maximalIdeal A₀) (hζ₀A : ∃ x : A₀, algebraMap A₀ L₀ x = ζ₀)
    [Algebra A₀ ↥K₀] [IsScalarTower A₀ L₀ ↥K₀]
    (j₀ : ↥K₀) (hj₀ : ((j₀ : LaurentSeries L₀)) = ModularCurve.coeffEmb L₀ ModularCurve.jq) [Fact (j₀ ≠ 0)]
    (ϖ₀ : A₀) (hϖ₀ : IsLocalRing.maximalIdeal A₀ = Ideal.span {ϖ₀})
    (z₀ : ↥(AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀))
    (ϖz₀ : (AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀)
    (hϖz₀ : ϖz₀ = ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.germ ⊤ z₀ trivial).hom
      (((AlgebraicCurve.TwoChartIntegralModel.toBase A₀ (↥K₀) j₀).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom ϖ₀)))
    (hz₀ : ϖz₀ ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀))
    (y₀ : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A₀ (↥K₀) j₀))
    (hy₀ : (AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀).base y₀ = z₀)
    (hss₀ : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) →+* Ω),
      RingHom.ker φ = y₀.asIdeal →
        φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A₀ (↥K₀) j₀) ∈ ModularCurve.ssJSet q Ω)

    (i : L₀ →+* L) (hiζ : i ζ₀ = ζ) (hiξ : i ξ₀ = ξ)
    [Algebra A₀ A] [IsLocalHom (algebraMap A₀ A)] (hinj : Function.Injective (algebraMap A₀ A))
    (hA₀A : ∀ a : A₀, algebraMap A L (algebraMap A₀ A a) = i (algebraMap A₀ L₀ a))
    (hϖ₀t : ∃ w : A, IsUnit w ∧ algebraMap A₀ A ϖ₀ = t * w)
    (cK : ↥K₀ →+* ↥K)
    (hcK : ∀ x : ↥K₀, ((cK x : ↥K) : LaurentSeries L) = ModularCurve.coeffMap i ((x : ↥K₀) : LaurentSeries L₀))
    (hcKj : cK j₀ = j)
    (c : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) →+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))
    (hc : ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀),
      ((c a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) : ↥K) = cK (a : ↥K₀))
    (hcy : Ideal.comap c y.asIdeal = y₀.asIdeal)

    (β : (A ⊗[A₀] ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)) ≃+*
      ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))
    (hβ : ∀ (a : A) (b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)),
      β (a ⊗ₜ[A₀] b) = algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a * c b)

    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (IsLocalRing.maximalIdeal W₀) W₀] (σ₀ : A₀ →+* W₀)
    (hσ₀ϖ : IsLocalRing.maximalIdeal W₀ = Ideal.span {σ₀ ϖ₀})
    (f₀ u₀ v₀ : MvPowerSeries (Fin 2) W₀) (hu₀ : IsUnit u₀) (hv₀ : IsUnit v₀)
    (hf₀ : f₀ - DrinfeldCurve.LocalChart.drinfeldForm q W₀ ∈
      (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₀), MvPowerSeries.X 1}) ^ (q + 2))
    (e₀ : AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀)) ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀) ≃+*
      MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {MvPowerSeries.C (σ₀ ϖ₀) * v₀ - f₀ * u₀})

    (ψ : W₀ →+* (AdicCompletion (IsLocalRing.maximalIdeal A) A))
    (hψσ₀ : ∀ a : A₀, ψ (σ₀ a) = (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) (algebraMap A₀ A a))
    (f u v : MvPowerSeries (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A))
    (e : AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ≃+*
        MvPowerSeries (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A) ⧸ Ideal.span {MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) t) * v - f * u})

    (hrel : MvPowerSeries.map ψ (MvPowerSeries.C (σ₀ ϖ₀) * v₀ - f₀ * u₀) ∈
      Ideal.span {MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) t) * v - f * u})

    (hanchor₀ :
      let STK₀ := ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀)
      let CMP₀ := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀)) ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀))
      let toC₀ : STK₀ →+* CMP₀ := algebraMap STK₀ CMP₀
      let S₀ := (MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {MvPowerSeries.C (σ₀ ϖ₀) * v₀ - f₀ * u₀})
      let mkS₀ : MvPowerSeries (Fin 2) W₀ →+* S₀ := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ₀ ϖ₀) * v₀ - f₀ * u₀})
      let germY₀ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) →+* STK₀ :=
        ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.germ
            ((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀) ''ᵁ ⊤) z₀ ⟨y₀, trivial, hy₀⟩).hom.comp
          ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀).appIso ⊤).inv.hom).comp
            (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀))).inv.hom)

      (∀ P : Ideal S₀, P.IsPrime → (mkS₀ (MvPowerSeries.X 0) ∉ P ∨ mkS₀ (MvPowerSeries.X 1) ∉ P) →
        mkS₀ (MvPowerSeries.C (σ₀ ϖ₀)) ∈ P →
        (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₀), MvPowerSeries.X 1}) ^ 2,
            mkS₀ (MvPowerSeries.C (1 : W₀) * MvPowerSeries.X 0 + MvPowerSeries.C (0 : W₀) * MvPowerSeries.X 1 + h) ∈ P) →
        ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀),
          toC₀ (germY₀ a) ∈ Ideal.comap (e₀ : CMP₀ →+* S₀) P ↔
            ∀ n : ℤ, ∃ m ∈ IsLocalRing.maximalIdeal A₀,
              (((a : ↥K₀) : LaurentSeries L₀).coeff n) = algebraMap A₀ L₀ m))

    (hconst :
      let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
      let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
      let toC : STK →+* CMP := algebraMap STK CMP
      let S := (MvPowerSeries (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A) ⧸ Ideal.span {MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) t) * v - f * u})
      let mkS : MvPowerSeries (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A) →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) t) * v - f * u})
      let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
        ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
            ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y, trivial, hy⟩).hom.comp
          ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
            (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)

      (∀ a : A, e (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
            (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
          (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
            (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
              ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)))) =
        Ideal.Quotient.mk _ (MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) a))))

    (hcompat :
      let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
      let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
      let toC : STK →+* CMP := algebraMap STK CMP
      let S := (MvPowerSeries (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A) ⧸ Ideal.span {MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) t) * v - f * u})
      let mkS : MvPowerSeries (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A) →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) t) * v - f * u})
      let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
        ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
            ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y, trivial, hy⟩).hom.comp
          ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
            (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)

      (∀ (x : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)) (s : MvPowerSeries (Fin 2) W₀),
        e₀ (algebraMap _ (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀)) ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀))
          ((((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.germ
              ((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀) ''ᵁ ⊤) z₀ ⟨y₀, trivial, hy₀⟩).hom.comp
            ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀).appIso ⊤).inv.hom).comp
              (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀))).inv.hom)) x)) =
          Ideal.Quotient.mk _ s →
        e (toC (germY (c x))) = mkS (MvPowerSeries.map ψ s)))

    (hnoeth : IsNoetherianRing ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) :
      let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
      let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
      let toC : STK →+* CMP := algebraMap STK CMP
      let S := (MvPowerSeries (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A) ⧸ Ideal.span {MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) t) * v - f * u})
      let mkS : MvPowerSeries (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A) →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) t) * v - f * u})
      let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
        ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
            ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y, trivial, hy⟩).hom.comp
          ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
            (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)

      (∀ P : Ideal S, P.IsPrime → (mkS (MvPowerSeries.X 0) ∉ P ∨ mkS (MvPowerSeries.X 1) ∉ P) →
        mkS (MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) ϖ)) ∈ P →
        (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A)), MvPowerSeries.X 1}) ^ 2,
            mkS (MvPowerSeries.C (1 : (AdicCompletion (IsLocalRing.maximalIdeal A) A)) * MvPowerSeries.X 0 + MvPowerSeries.C (0 : (AdicCompletion (IsLocalRing.maximalIdeal A) A)) * MvPowerSeries.X 1 + h) ∈ P) →

        (∃ h₀ ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₀), MvPowerSeries.X 1}) ^ 2,
            mkS (MvPowerSeries.map ψ (MvPowerSeries.C (1 : W₀) * MvPowerSeries.X 0 + MvPowerSeries.C (0 : W₀) * MvPowerSeries.X 1 + h₀)) ∈ P) →
        ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
          toC (germY a) ∈ Ideal.comap (e : CMP →+* S) P ↔
            ∀ n : ℤ, ∃ m ∈ IsLocalRing.maximalIdeal A,
              (((a : ↥K) : LaurentSeries L).coeff n) = algebraMap A L m) := by
  intro STK CMP toC S mkS germY P hP hPX hPϖ htan hBR a
  classical
  haveI hPinst : P.IsPrime := hP

  let STK₀ := ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀)
  let CMP₀ := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀)) ((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.stalk z₀))
  let toC₀ : STK₀ →+* CMP₀ := algebraMap STK₀ CMP₀
  let I₀ : Ideal (MvPowerSeries (Fin 2) W₀) := Ideal.span {(MvPowerSeries.C (σ₀ ϖ₀) * v₀ - f₀ * u₀)}
  let S₀ := MvPowerSeries (Fin 2) W₀ ⧸ I₀
  let mkS₀ : MvPowerSeries (Fin 2) W₀ →+* S₀ := Ideal.Quotient.mk I₀
  let germY₀ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) →+* STK₀ :=
    (((AlgebraicCurve.TwoChartIntegralModel A₀ (↥K₀) j₀).presheaf.germ
            ((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀) ''ᵁ ⊤) z₀ ⟨y₀, trivial, hy₀⟩).hom.comp
          ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ (↥K₀) j₀).appIso ⊤).inv.hom).comp
            (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀))).inv.hom))
  let Γ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* S := (e : CMP →+* S).comp (toC.comp germY)
  let Γ₀ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) →+* S₀ := (e₀ : CMP₀ →+* S₀).comp (toC₀.comp germY₀)

  have hI₀ : ∀ x ∈ I₀, (mkS.comp (MvPowerSeries.map ψ)) x = 0 := by
    intro x hx
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    rw [RingHom.comp_apply, map_mul, map_mul]
    exact mul_eq_zero_of_right _ (Ideal.Quotient.eq_zero_iff_mem.mpr hrel)
  let lam : S₀ →+* S := Ideal.Quotient.lift I₀ (mkS.comp (MvPowerSeries.map ψ)) hI₀
  have hlam : ∀ s : MvPowerSeries (Fin 2) W₀, lam (mkS₀ s) = mkS (MvPowerSeries.map ψ s) := fun s =>
    Ideal.Quotient.lift_mk I₀ _ hI₀
  let P' : Ideal S₀ := P.comap lam
  haveI hP' : P'.IsPrime := Ideal.comap_isPrime lam P

  have hXlam : ∀ i : Fin 2, lam (mkS₀ (MvPowerSeries.X i)) = mkS (MvPowerSeries.X i) := fun i => by
    rw [hlam, MvPowerSeries.map_X]
  have hX' : mkS₀ (MvPowerSeries.X 0) ∉ P' ∨ mkS₀ (MvPowerSeries.X 1) ∉ P' := by
    rcases hPX with h | h
    · left
      intro h'
      apply h
      have h'' : lam (mkS₀ (MvPowerSeries.X 0)) ∈ P := h'
      rwa [hXlam] at h''
    · right
      intro h'
      apply h
      have h'' : lam (mkS₀ (MvPowerSeries.X 1)) ∈ P := h'
      rwa [hXlam] at h''
  have htmem : t ∈ IsLocalRing.maximalIdeal A := by
    obtain ⟨w, -, hw⟩ := ht
    apply (IsLocalRing.maximalIdeal.isMaximal A).isPrime.mem_of_pow_mem (q - 1)
    rw [hw]
    exact Ideal.mul_mem_right _ _ hAq
  have hϖ' : mkS₀ (MvPowerSeries.C (σ₀ ϖ₀)) ∈ P' := by
    show lam (mkS₀ (MvPowerSeries.C (σ₀ ϖ₀))) ∈ P
    rw [hlam, MvPowerSeries.map_C, hψσ₀]
    obtain ⟨w, -, hw⟩ := hϖ₀t
    have htϖ : t ∈ Ideal.span {ϖ} := hϖ ▸ htmem
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp htϖ
    have hfac : (MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) (algebraMap A₀ A ϖ₀)) :
        MvPowerSeries (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A)) =
        MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) ϖ) * MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) (r * w)) := by
      rw [← map_mul, ← map_mul, hw, ← hr]
      congr 1
      ring_nf
    rw [hfac, map_mul]
    exact Ideal.mul_mem_right _ _ hPϖ
  have htan' : ∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₀), MvPowerSeries.X 1}) ^ 2,
      mkS₀ (MvPowerSeries.C (1 : W₀) * MvPowerSeries.X 0 + MvPowerSeries.C (0 : W₀) * MvPowerSeries.X 1 + h) ∈ P' := by
    obtain ⟨h₀, hh₀, hmem⟩ := hBR
    refine ⟨h₀, hh₀, ?_⟩
    show lam (mkS₀ _) ∈ P
    rw [hlam]
    exact hmem
  have H₀ : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀), toC₀ (germY₀ b) ∈ Ideal.comap (e₀ : CMP₀ →+* S₀) P' ↔
      ∀ n : ℤ, ∃ m ∈ IsLocalRing.maximalIdeal A₀, (((b : ↥K₀) : LaurentSeries L₀).coeff n) = algebraMap A₀ L₀ m :=
    hanchor₀ P' hP' hX' hϖ' htan'

  have hsq : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀), Γ (c b) = lam (Γ₀ b) := by
    intro b
    obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (Γ₀ b)
    have h1 : e (toC (germY (c b))) = mkS (MvPowerSeries.map ψ s) := hcompat b s hs.symm
    calc Γ (c b) = e (toC (germY (c b))) := rfl
      _ = mkS (MvPowerSeries.map ψ s) := h1
      _ = lam (mkS₀ s) := (hlam s).symm
      _ = lam (Γ₀ b) := by rw [← hs]

  have hcoe_alg₀ : ∀ r : A₀, (((algebraMap A₀ ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) r) : ↥K₀) : LaurentSeries L₀) =
      HahnSeries.single 0 (algebraMap A₀ L₀ r) := fun r => by
    rw [Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply A₀ L₀ ↥K₀,
      ← ModularCurve.algebraMap_laurentSeries_eq_single]
    exact (IsScalarTower.algebraMap_apply L₀ ↥K₀ (LaurentSeries L₀) _).symm
  have hcoe_alg : ∀ r : A, (((algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) r) : ↥K) : LaurentSeries L) =
      HahnSeries.single 0 (algebraMap A L r) := fun r => by
    rw [Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply A L ↥K,
      ← ModularCurve.algebraMap_laurentSeries_eq_single]
    exact (IsScalarTower.algebraMap_apply L ↥K (LaurentSeries L) _).symm
  have hϖ₀ne : algebraMap A₀ L₀ ϖ₀ ≠ 0 := by
    intro h0
    have : ϖ₀ = 0 := (IsFractionRing.injective A₀ L₀) (by rw [h0, map_zero])
    apply IsDiscreteValuationRing.not_a_field A₀
    rw [hϖ₀, this, Ideal.span_singleton_eq_bot]
  have hcoefA₀ : ∀ (b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)) (n : ℤ), ∃ m : A₀, ((b : ↥K₀) : LaurentSeries L₀).coeff n = algebraMap A₀ L₀ m := by

    let J₀ : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) := Ideal.comap (toC₀.comp germY₀) (Ideal.comap (e₀ : CMP₀ →+* S₀) P')
    have hϖ₀mem : algebraMap A₀ ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) ϖ₀ ∈ J₀ := by
      refine (H₀ _).mpr ?_
      intro n
      by_cases hn : n = 0
      · refine ⟨ϖ₀, ?_, ?_⟩
        · rw [hϖ₀]; exact Ideal.mem_span_singleton_self ϖ₀
        · rw [hcoe_alg₀, hn, HahnSeries.coeff_single_same]
      · refine ⟨0, zero_mem _, ?_⟩
        rw [hcoe_alg₀, HahnSeries.coeff_single_of_ne hn, map_zero]
    intro b n
    have hmul : algebraMap A₀ ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) ϖ₀ * b ∈ J₀ := J₀.mul_mem_right _ hϖ₀mem
    obtain ⟨m, hm, hmn⟩ := (H₀ _).mp hmul n
    rw [hϖ₀] at hm
    obtain ⟨m', rfl⟩ := Ideal.mem_span_singleton'.mp hm
    refine ⟨m', ?_⟩
    have h2 : (((algebraMap A₀ ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) ϖ₀ * b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)) : ↥K₀) : LaurentSeries L₀).coeff n =
        algebraMap A₀ L₀ ϖ₀ * ((b : ↥K₀) : LaurentSeries L₀).coeff n := by
      rw [Subalgebra.coe_mul, IntermediateField.coe_mul, hcoe_alg₀, HahnSeries.single_zero_mul_eq_smul,
        HahnSeries.coeff_smul, smul_eq_mul]
    rw [h2, map_mul, mul_comm (algebraMap A₀ L₀ m')] at hmn
    exact mul_left_cancel₀ hϖ₀ne hmn
  have hcoef_c : ∀ (b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)) (n : ℤ),
      (((c b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) : ↥K) : LaurentSeries L).coeff n = i (((b : ↥K₀) : LaurentSeries L₀).coeff n) := fun b n => by
    rw [hc, hcK]
    rfl
  have hcoefA : ∀ (x : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) (n : ℤ), ∃ m : A, ((x : ↥K) : LaurentSeries L).coeff n = algebraMap A L m := by
    intro x
    refine WAnchor.baseChange_induction c β hβ
      (p := fun x => ∀ n : ℤ, ∃ m : A, ((x : ↥K) : LaurentSeries L).coeff n = algebraMap A L m) ?_ ?_ ?_ x
    · intro n; exact ⟨0, by simp⟩
    · intro a b n
      obtain ⟨m, hm⟩ := hcoefA₀ b n
      refine ⟨a * algebraMap A₀ A m, ?_⟩
      rw [Subalgebra.coe_mul, IntermediateField.coe_mul, hcoe_alg, HahnSeries.single_zero_mul_eq_smul,
        HahnSeries.coeff_smul, smul_eq_mul, hcoef_c, hm, ← hA₀A, map_mul]
    · intro s t hs ht n
      obtain ⟨m₁, h₁⟩ := hs n
      obtain ⟨m₂, h₂⟩ := ht n
      refine ⟨m₁ + m₂, ?_⟩
      rw [Subalgebra.coe_add, IntermediateField.coe_add, HahnSeries.coeff_add, h₁, h₂, map_add]
  obtain ⟨τ₀, hτ₀⟩ : ∃ τ₀ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) →+* LaurentSeries A₀,
      ∀ b, ModularCurve.coeffMap (algebraMap A₀ L₀) (τ₀ b) = ((b : ↥K₀) : LaurentSeries L₀) :=
    WAnchor.exists_ringHom_coeffMap_comp_eq (algebraMap A₀ L₀) (IsFractionRing.injective A₀ L₀)
      ((algebraMap ↥K₀ (LaurentSeries L₀)).comp (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) ↥K₀)) hcoefA₀
  obtain ⟨τ, hτ⟩ : ∃ τ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* LaurentSeries A,
      ∀ x, ModularCurve.coeffMap (algebraMap A L) (τ x) = ((x : ↥K) : LaurentSeries L) :=
    WAnchor.exists_ringHom_coeffMap_comp_eq (algebraMap A L) (IsFractionRing.injective A L)
      ((algebraMap ↥K (LaurentSeries L)).comp (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ↥K)) hcoefA
  let red₀ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) →+* LaurentSeries (IsLocalRing.ResidueField A₀) :=
    (ModularCurve.coeffMap (IsLocalRing.residue A₀)).comp τ₀
  let red : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* LaurentSeries (IsLocalRing.ResidueField A) :=
    (ModularCurve.coeffMap (IsLocalRing.residue A)).comp τ
  let G : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) := RingHom.ker red
  haveI hGprime : G.IsPrime := RingHom.ker_isPrime red
  have hG_iff : ∀ x : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j), x ∈ G ↔
      ∀ n : ℤ, ∃ m ∈ IsLocalRing.maximalIdeal A, (((x : ↥K) : LaurentSeries L).coeff n) = algebraMap A L m := by
    intro x
    have hcoefτ : ∀ n : ℤ, ((x : ↥K) : LaurentSeries L).coeff n = algebraMap A L ((τ x).coeff n) := fun n => by
      rw [← hτ x]; rfl
    rw [RingHom.mem_ker]
    constructor
    · intro h n
      refine ⟨(τ x).coeff n, ?_, hcoefτ n⟩
      have := congrArg (fun s => HahnSeries.coeff s n) h
      simp only [red, RingHom.coe_comp, Function.comp_apply, ModularCurve.coeffMap_coeff,
        HahnSeries.coeff_zero] at this
      exact (IsLocalRing.residue_eq_zero_iff _).mp this
    · intro h
      ext n
      obtain ⟨m, hm, hmn⟩ := h n
      simp only [red, RingHom.coe_comp, Function.comp_apply, ModularCurve.coeffMap_coeff, HahnSeries.coeff_zero]
      rw [IsLocalRing.residue_eq_zero_iff]
      have : (τ x).coeff n = m := IsFractionRing.injective A L (by rw [← hcoefτ n, hmn])
      rwa [this]
  have hG₀_iff : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀), red₀ b = 0 ↔
      ∀ n : ℤ, ∃ m ∈ IsLocalRing.maximalIdeal A₀, (((b : ↥K₀) : LaurentSeries L₀).coeff n) = algebraMap A₀ L₀ m := by
    intro b
    have hcoefτ : ∀ n : ℤ, ((b : ↥K₀) : LaurentSeries L₀).coeff n = algebraMap A₀ L₀ ((τ₀ b).coeff n) := fun n => by
      rw [← hτ₀ b]; rfl
    constructor
    · intro h n
      refine ⟨(τ₀ b).coeff n, ?_, hcoefτ n⟩
      have := congrArg (fun s => HahnSeries.coeff s n) h
      simp only [red₀, RingHom.coe_comp, Function.comp_apply, ModularCurve.coeffMap_coeff,
        HahnSeries.coeff_zero] at this
      exact (IsLocalRing.residue_eq_zero_iff _).mp this
    · intro h
      ext n
      obtain ⟨m, hm, hmn⟩ := h n
      simp only [red₀, RingHom.coe_comp, Function.comp_apply, ModularCurve.coeffMap_coeff, HahnSeries.coeff_zero]
      rw [IsLocalRing.residue_eq_zero_iff]
      have : (τ₀ b).coeff n = m := IsFractionRing.injective A₀ L₀ (by rw [← hcoefτ n, hmn])
      rwa [this]

  have hτA : ∀ r : A, τ (algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) r) = HahnSeries.single 0 r := fun r =>
    WAnchor.coeffMap_injective _ (IsFractionRing.injective A L) (by
      rw [hτ, hcoe_alg, ModularCurve.coeffMap_single])
  have hredA : ∀ r : A, red (algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) r) =
      HahnSeries.single 0 (IsLocalRing.residue A r) := fun r => by
    show ModularCurve.coeffMap (IsLocalRing.residue A) (τ (algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) r)) = _
    rw [hτA, ModularCurve.coeffMap_single]
  have hτc : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀), τ (c b) = ModularCurve.coeffMap (algebraMap A₀ A) (τ₀ b) := fun b =>
    WAnchor.coeffMap_injective _ (IsFractionRing.injective A L) (by
      have hcomp : (algebraMap A L).comp (algebraMap A₀ A) = i.comp (algebraMap A₀ L₀) := RingHom.ext hA₀A
      rw [hτ, ModularCurve.coeffMap_coeffMap, hcomp, ← ModularCurve.coeffMap_coeffMap, hτ₀, hc, hcK])
  have hredc : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀), red (c b) =
      ModularCurve.coeffMap (IsLocalRing.ResidueField.map (algebraMap A₀ A)) (red₀ b) := fun b => by
    show ModularCurve.coeffMap (IsLocalRing.residue A) (τ (c b)) =
      ModularCurve.coeffMap (IsLocalRing.ResidueField.map (algebraMap A₀ A))
        (ModularCurve.coeffMap (IsLocalRing.residue A₀) (τ₀ b))
    rw [hτc, ModularCurve.coeffMap_coeffMap, ModularCurve.coeffMap_coeffMap]
    exact ModularCurve.coeffMap_congr (RingHom.ext fun r =>
      (IsLocalRing.ResidueField.map_residue (algebraMap A₀ A) r).symm) _
  have hAG : ∀ r : A, algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) r ∈ G ↔ r ∈ IsLocalRing.maximalIdeal A := fun r => by
    show red (algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) r) = 0 ↔ _
    rw [hredA, HahnSeries.single_eq_zero_iff, IsLocalRing.residue_eq_zero_iff]
  let 𝔮 : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) := P.comap Γ
  haveI h𝔮prime : 𝔮.IsPrime := Ideal.comap_isPrime Γ P

  obtain ⟨ε, hε1, hε2⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_stalk_iso_localization_atPrime_of_iotaFin_apply_eq A (↥K) j z y hy
  let εe : STK ≃+* Localization.AtPrime y.asIdeal := ε.commRingCatIsoToRingEquiv
  have hεe : ∀ x : STK, εe x = ε.hom.hom x := fun _ => rfl
  have hεY : ∀ x : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j), εe (germY x) = algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) (Localization.AtPrime y.asIdeal) x :=
    fun x => by rw [hεe]; exact hε2 x
  have hunit : ∀ s : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j), s ∉ y.asIdeal → IsUnit (germY s) := fun s hs => by
    have h1 : IsUnit (εe (germY s)) := by
      rw [hεY]
      exact IsLocalization.map_units (Localization.AtPrime y.asIdeal) (⟨s, hs⟩ : y.asIdeal.primeCompl)
    simpa using h1.map εe.symm
  have hϖ𝔮 : algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ϖ ∈ 𝔮 := by
    have hgerm : germY (algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ϖ) =
        ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
          (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)) := by
      apply εe.injective
      rw [hεY, hεe, hε1, IsScalarTower.algebraMap_apply A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) (Localization.AtPrime y.asIdeal)]
    show e (toC (germY (algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ϖ))) ∈ P
    rw [hgerm]
    have hc' : e (toC (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
          (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))) =
        mkS (MvPowerSeries.C ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) ϖ)) := hconst ϖ
    rw [hc']
    exact hPϖ
  have hc𝔮 : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀), c b ∈ 𝔮 ↔ red₀ b = 0 := fun b => by
    rw [hG₀_iff, ← H₀]
    show Γ (c b) ∈ P ↔ lam (Γ₀ b) ∈ P
    rw [hsq]
  suffices hfinal : 𝔮 = G by
    have hiff : toC (germY a) ∈ Ideal.comap (e : CMP →+* S) P ↔ a ∈ 𝔮 := by
      simp only [𝔮, Γ, Ideal.mem_comap, RingHom.coe_comp, Function.comp_apply]
    rw [hiff, hfinal]
    exact hG_iff a

  have h3 : G ≤ 𝔮 := by

    let aC : A →+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) := algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
    let κmap := IsLocalRing.ResidueField.map (algebraMap A₀ A)
    have hκinj : Function.Injective (ModularCurve.coeffMap κmap) := by
      intro u v huv
      ext n
      have h := congrArg (fun z : LaurentSeries (IsLocalRing.ResidueField A) => z.coeff n) huv
      simp only [ModularCurve.coeffMap_coeff] at h
      exact κmap.injective h

    have hc1 : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀), c b = β (1 ⊗ₜ[A₀] b) := by
      intro b; rw [hβ, map_one, one_mul]
    have hcsmul : ∀ (l : A₀) (b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)), c (l • b) = aC (algebraMap A₀ A l) * c b := by
      intro l b
      have h1 : c (algebraMap A₀ ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) l) = aC (algebraMap A₀ A l) := by
        rw [hc1, ← Algebra.TensorProduct.algebraMap_apply', Algebra.TensorProduct.algebraMap_apply, hβ, map_one, mul_one]
      rw [Algebra.smul_def, map_mul, h1]

    have hredcomb : ∀ (r : A) (b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)),
        red (aC r * c b) = IsLocalRing.residue A r • ModularCurve.coeffMap κmap (red₀ b) := by
      intro r b
      rw [map_mul, hredA, hredc, HahnSeries.single_zero_mul_eq_smul]
    have hredsmul₀ : ∀ (μ : IsLocalRing.ResidueField A₀) (v : LaurentSeries (IsLocalRing.ResidueField A₀)),
        ModularCurve.coeffMap κmap (μ • v) = κmap μ • ModularCurve.coeffMap κmap v := by
      intro μ v
      rw [← HahnSeries.single_zero_mul_eq_smul, ← HahnSeries.single_zero_mul_eq_smul, map_mul,
        ModularCurve.coeffMap_single]
    have hϖmem : ∀ r : A, IsLocalRing.residue A r = 0 → ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j), aC r * b ∈ 𝔮 := by
      intro r hr b
      rw [IsLocalRing.residue_eq_zero_iff, hϖ] at hr
      obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.mp hr
      rw [← he, map_mul, mul_assoc]
      rw [mul_comm (aC e), mul_assoc]
      exact Ideal.mul_mem_right _ _ hϖ𝔮

    have hcG𝔮 : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀), red (c b) = 0 → c b ∈ 𝔮 := by
      intro b hb
      refine (hc𝔮 b).mpr (hκinj ?_)
      rw [← hredc, hb, map_zero]

    obtain ⟨x_dummy, -⟩ : ∃ n : ℕ, True := ⟨0, trivial⟩
    have key : ∀ (n : ℕ) (ι : Type) (b : ι → ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)) (s : Finset ι), s.card = n → ∀ (a : ι → A),
        red (∑ i ∈ s, aC (a i) * c (b i)) = 0 → (∑ i ∈ s, aC (a i) * c (b i)) ∈ 𝔮 := by
      intro n
      induction n with
      | zero =>
          intro ι b s hs a _
          rw [Finset.card_eq_zero.mp hs, Finset.sum_empty]
          exact Ideal.zero_mem _
      | succ n ih =>
          intro ι b s hs a hred
          classical

          have hrel : ∑ i : ↥s, IsLocalRing.residue A (a i) • ModularCurve.coeffMap κmap (red₀ (b i)) = 0 := by
            rw [Finset.sum_coe_sort s (fun i => IsLocalRing.residue A (a i) • ModularCurve.coeffMap κmap (red₀ (b i)))]
            rw [map_sum] at hred
            simpa only [hredcomb] using hred
          by_cases hli : LinearIndependent (IsLocalRing.ResidueField A₀) (fun i : ↥s => red₀ (b i))
          ·
            have hliK := ModularCurve.linearIndependent_coeffMap_of_linearIndependent
              (IsLocalRing.ResidueField A₀) (IsLocalRing.ResidueField A) κmap ↥s (fun i : ↥s => red₀ (b i)) hli
            have hzero : ∀ i : ↥s, IsLocalRing.residue A (a i) = 0 :=
              (Fintype.linearIndependent_iff.mp hliK) (fun i => IsLocalRing.residue A (a i)) hrel
            refine Ideal.sum_mem _ (fun i hi => ?_)
            exact hϖmem (a i) (hzero ⟨i, hi⟩) (c (b i))
          ·
            obtain ⟨g, hg, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.mp hli

            let μ : ↥s → IsLocalRing.ResidueField A₀ := fun i => (g i₀)⁻¹ * g i
            have hμ₀ : μ i₀ = 1 := inv_mul_cancel₀ hi₀
            have hμrel : ∑ i : ↥s, μ i • red₀ (b i) = 0 := by
              have : ∑ i : ↥s, μ i • red₀ (b i) = (g i₀)⁻¹ • ∑ i : ↥s, g i • red₀ (b i) := by
                rw [Finset.smul_sum]
                refine Finset.sum_congr rfl (fun i _ => ?_)
                rw [smul_smul]
              rw [this, hg, smul_zero]

            have hlift : ∀ i : ↥s, ∃ l : A₀, IsLocalRing.residue A₀ l = μ i := fun i =>
              IsLocalRing.residue_surjective (μ i)
            choose lam0 hlam0 using hlift
            let lam : ↥s → A₀ := Function.update lam0 i₀ 1
            have hlam : ∀ i : ↥s, IsLocalRing.residue A₀ (lam i) = μ i := by
              intro i
              by_cases h : i = i₀
              · rw [h, show lam i₀ = 1 from Function.update_self .., map_one, hμ₀]
              · rw [show lam i = lam0 i from Function.update_of_ne h .., hlam0]
            have hlam₀ : lam i₀ = 1 := Function.update_self ..

            let bstar : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀) := ∑ i : ↥s, lam i • b i
            have hcb : c bstar = ∑ i : ↥s, aC (algebraMap A₀ A (lam i)) * c (b i) := by
              simp only [bstar, map_sum, hcsmul]
            have hredb : red (c bstar) = 0 := by
              rw [hcb, map_sum]
              have : ∀ i : ↥s, red (aC (algebraMap A₀ A (lam i)) * c (b i)) =
                  ModularCurve.coeffMap κmap (μ i • red₀ (b i)) := by
                intro i
                rw [hredcomb, hredsmul₀, ← IsLocalRing.ResidueField.map_residue, hlam]
              simp only [this, ← map_sum, hμrel, map_zero]
            have hb𝔮 : c bstar ∈ 𝔮 := hcG𝔮 bstar hredb

            let lamι : ι → A := fun i => if h : i ∈ s then algebraMap A₀ A (lam ⟨i, h⟩) else 0
            let a' : ι → A := fun i => a i - lamι i * a i₀
            have hi₀s : (i₀ : ι) ∈ s := i₀.2
            have hsplit : ∑ i ∈ s, aC (a i) * c (b i) =
                aC (a i₀) * c bstar + ∑ i ∈ s.erase i₀, aC (a' i) * c (b i) := by
              have h1 : ∑ i ∈ s.erase i₀, aC (a' i) * c (b i) = ∑ i ∈ s, aC (a' i) * c (b i) := by
                apply Finset.sum_erase
                simp only [a', lamι, dif_pos hi₀s, Subtype.coe_eta, hlam₀, map_one, one_mul, sub_self, map_zero,
                  zero_mul]
              have h2 : aC (a i₀) * c bstar = ∑ i ∈ s, aC (lamι i * a i₀) * c (b i) := by
                rw [hcb, Finset.mul_sum, ← Finset.sum_coe_sort s (fun i => aC (lamι i * a i₀) * c (b i))]
                refine Finset.sum_congr rfl (fun i _ => ?_)
                simp only [lamι, dif_pos i.2, Subtype.coe_eta, map_mul]
                ring
              rw [h1, h2, ← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl (fun i _ => ?_)
              simp only [a', map_sub, map_mul]
              ring
            have hred' : red (∑ i ∈ s.erase i₀, aC (a' i) * c (b i)) = 0 := by
              have h := hred
              rw [hsplit, map_add, map_mul, hredb, mul_zero, zero_add] at h
              exact h
            have hcard : (s.erase i₀).card = n := by
              rw [Finset.card_erase_of_mem hi₀s, hs]; rfl
            have hIH := ih ι b (s.erase i₀) hcard a' hred'
            rw [hsplit]
            exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hb𝔮) hIH

    intro x hx
    have hx0 : red x = 0 := RingHom.mem_ker.mp hx
    obtain ⟨t, rfl⟩ : ∃ t, β t = x := β.surjective x
    obtain ⟨s, hs⟩ := TensorProduct.exists_finset t
    have hsum : β t = ∑ p ∈ s, aC p.1 * c p.2 := by
      rw [hs, map_sum]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      exact hβ p.1 p.2
    rw [hsum] at hx0 ⊢
    exact key s.card (A × ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ (↥K₀) j₀)) (fun p => p.2) s rfl (fun p => p.1) hx0

  have h4a : 𝔮 ≤ y.asIdeal := by
    intro x hx
    by_contra hxy
    have hu : IsUnit (Γ x) := ((hunit x hxy).map toC).map e
    exact hP.ne_top (Ideal.eq_top_of_isUnit_mem P hx hu)
  have h4b : 𝔮 ≠ y.asIdeal := by
    intro heq
    let Pc : Ideal CMP := P.comap (e : CMP →+* S)
    haveI hPc : Pc.IsPrime := Ideal.comap_isPrime _ P
    have hPstk : Pc.comap (algebraMap STK CMP) = IsLocalRing.maximalIdeal STK := by
      apply le_antisymm
      · exact IsLocalRing.le_maximalIdeal (Ideal.comap_isPrime (algebraMap STK CMP) Pc).ne_top
      · intro m hm
        obtain ⟨⟨a, s⟩, has⟩ := IsLocalization.mk'_surjective y.asIdeal.primeCompl (εe m)
        dsimp only at has
        have ha : a ∈ y.asIdeal := by
          by_contra ha
          apply (IsLocalRing.mem_maximalIdeal _).mp hm
          have hu : IsUnit (IsLocalization.mk' (Localization.AtPrime y.asIdeal) a s) :=
            IsLocalization.AtPrime.isUnit_mk'_iff (Localization.AtPrime y.asIdeal) y.asIdeal a s |>.mpr ha
          rw [has] at hu
          simpa using hu.map εe.symm
        have hms : m * germY (s : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) = germY a := by
          apply εe.injective
          rw [map_mul, ← has, hεY, hεY]
          exact IsLocalization.mk'_spec _ a s
        have haq : a ∈ 𝔮 := by rw [heq]; exact ha
        have hprod : e (toC m) * Γ (s : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) ∈ P := by
          have : e (toC m) * Γ (s : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) = Γ a := by
            show e (toC m) * e (toC (germY s)) = e (toC (germY a))
            rw [← map_mul, ← map_mul, hms]
          rw [this]
          exact haq
        rcases hP.mem_or_mem hprod with h | h
        · exact h
        · exact absurd (Ideal.eq_top_of_isUnit_mem P h (((hunit s s.2).map toC).map e)) hP.ne_top
    haveI : IsNoetherianRing ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) := hnoeth
    haveI : IsNoetherianRing STK := isNoetherianRing_of_ringEquiv (Localization.AtPrime y.asIdeal) εe.symm
    have hPcmax : Pc = IsLocalRing.maximalIdeal CMP :=
      AdicCompletion.eq_maximalIdeal_of_comap_algebraMap_eq_maximalIdeal STK Pc hPstk
    have hPmax : P.IsMaximal := by
      have hP' : P = (IsLocalRing.maximalIdeal CMP).comap (e.symm : S →+* CMP) := by
        ext s
        rw [← hPcmax]
        show s ∈ P ↔ e (e.symm s) ∈ P
        rw [e.apply_symm_apply]
      rw [hP']
      exact Ideal.comap_isMaximal_of_surjective _ e.symm.surjective
    have hXmem : ∀ ii : Fin 2, mkS (MvPowerSeries.X ii) ∈ P := by
      intro ii
      by_contra hni
      obtain ⟨w, p, hp, hwp⟩ := hPmax.exists_inv hni
      obtain ⟨w', rfl⟩ := Ideal.Quotient.mk_surjective w
      have hu : IsUnit (1 - w' * (MvPowerSeries.X ii : MvPowerSeries (Fin 2) (AdicCompletion (IsLocalRing.maximalIdeal A) A))) := by
        rw [MvPowerSeries.isUnit_iff_constantCoeff]
        simp
      have hpe : p = mkS (1 - w' * MvPowerSeries.X ii) := by
        rw [map_sub, map_one, map_mul]
        show p = 1 - Ideal.Quotient.mk _ w' * mkS (MvPowerSeries.X ii)
        linear_combination hwp
      exact hPmax.ne_top (Ideal.eq_top_of_isUnit_mem P hp (hpe ▸ hu.map mkS))
    rcases hPX with h | h
    · exact h (hXmem 0)
    · exact h (hXmem 1)

  have h56 : 𝔮 ≤ G := by
    haveI hGp : G.IsPrime := hGprime
    haveI : IsDomain (↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ⧸ G) := Ideal.Quotient.isDomain G

    have hR : ∀ r : A, algebraMap A (↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ⧸ G) r = 0 ∨ IsUnit (algebraMap A (↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ⧸ G) r) := by
      intro r
      by_cases hr : r ∈ IsLocalRing.maximalIdeal A
      · left
        show Ideal.Quotient.mk G (algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) r) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem]
        exact (hAG r).mpr hr
      · right
        have hu : IsUnit r := by
          by_contra hnu
          exact hr ((IsLocalRing.mem_maximalIdeal r).mpr (mem_nonunits_iff.mpr hnu))
        exact hu.map _

    let jC := AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j
    let TK : Subalgebra A ↥K := Algebra.adjoin A ({j} : Set ↥K)
    have hTK : TK ≤ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j :=
      AlgebraicCurve.TwoChartIntegralModel.adjoin_le_chartAlg A ↥K ({j} : Set ↥K)
    let incl : ↥TK →ₐ[A] ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) := Subalgebra.inclusion hTK
    let mkG : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →ₐ[A] (↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ⧸ G) := Ideal.Quotient.mkₐ A G
    let θD : ↥TK →ₐ[A] (↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ⧸ G) := mkG.comp incl
    let TD : Subalgebra A (↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ⧸ G) := Algebra.adjoin A ({Ideal.Quotient.mk G jC} : Set (↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ⧸ G))
    have hθD : ∀ t : ↥TK, θD t ∈ TD := by
      intro t
      obtain ⟨k, hk⟩ := t
      induction hk using Algebra.adjoin_induction with
      | mem z hz =>
          rw [Set.mem_singleton_iff] at hz
          have hz' := hz.symm
          subst hz'
          have : θD ⟨j, Algebra.subset_adjoin (Set.mem_singleton j)⟩ = Ideal.Quotient.mk G jC := rfl
          rw [this]
          exact Algebra.subset_adjoin (Set.mem_singleton _)
      | algebraMap r =>
          have : (⟨algebraMap A ↥K r, Subalgebra.algebraMap_mem _ r⟩ : ↥TK) = algebraMap A ↥TK r := rfl
          rw [this, AlgHom.commutes]
          exact Subalgebra.algebraMap_mem _ r
      | add k k' hk hk' ih ih' =>
          have : (⟨k + k', Subalgebra.add_mem _ hk hk'⟩ : ↥TK) = ⟨k, hk⟩ + ⟨k', hk'⟩ := rfl
          rw [this, map_add]
          exact Subalgebra.add_mem _ ih ih'
      | mul k k' hk hk' ih ih' =>
          have : (⟨k * k', Subalgebra.mul_mem _ hk hk'⟩ : ↥TK) = ⟨k, hk⟩ * ⟨k', hk'⟩ := rfl
          rw [this, map_mul]
          exact Subalgebra.mul_mem _ ih ih'
    let φD : ↥TK →+* ↥TD := (θD.codRestrict TD hθD).toRingHom
    let IC : Subalgebra ↥TK ↥K := integralClosure ↥TK ↥K
    have hICmem : ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j), (a : ↥K) ∈ IC := fun a =>
      (mem_integralClosure_iff _ _).mpr ((AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff A ↥K).mp a.2)
    let eIC : ↥IC →+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) :=
      { toFun := fun z => ⟨(z : ↥K), (AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff A ↥K).mpr
          ((mem_integralClosure_iff _ _).mp z.2)⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    have hint : ∀ d : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ⧸ G, IsIntegral ↥TD d := by
      intro d
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective d
      have ha : IsIntegral ↥TK (⟨(a : ↥K), hICmem a⟩ : ↥IC) := integralClosure.isIntegral _
      have h := ha.map_of_comp_eq φD ((Ideal.Quotient.mk G).comp eIC) (by
        refine RingHom.ext (fun t => ?_)
        rfl)
      exact h

    let P' : Ideal (↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ⧸ G) := 𝔮.map (Ideal.Quotient.mk G)
    have hkerG : RingHom.ker (Ideal.Quotient.mk G) = G := Ideal.mk_ker
    haveI hP' : P'.IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [hkerG]; exact h3)
    by_cases hbot : P' = ⊥
    · intro a ha
      have hmem : Ideal.Quotient.mk G a ∈ P' := Ideal.mem_map_of_mem _ ha
      rw [hbot, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hmem
      exact hmem
    · exfalso
      have hmax : P'.IsMaximal :=
        Ideal.IsMaximal.of_isPrime_of_ne_bot_of_isIntegral_adjoin_singleton A (↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ⧸ G) hR
          (Ideal.Quotient.mk G jC) hint P' hbot
      have hcomap : Ideal.comap (Ideal.Quotient.mk G) P' = 𝔮 := by
        rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, hkerG,
          sup_eq_left.mpr h3]
      have h𝔮max : 𝔮.IsMaximal := by
        rw [← hcomap]
        exact Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
      exact h4b (h𝔮max.eq_of_le y.isPrime.ne_top h4a)
  exact le_antisymm h56 h3

end S_ModularCurve_FullLevel_AuxLevel_forall_mem_comap_drinfeldChart_iff_forall_coeff_mem_maximalIdeal_baseChange_of_cyclotomic
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevel_forall_mem_comap_drinfeldChart_iff_forall_coeff_mem_maximalIdeal_baseChange_of_cyclotomic (solution)
