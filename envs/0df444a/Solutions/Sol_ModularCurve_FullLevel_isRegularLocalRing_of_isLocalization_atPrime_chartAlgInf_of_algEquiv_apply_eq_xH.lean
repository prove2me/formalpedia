-- Prove2me | solution 1 for ModularCurve.FullLevel.isRegularLocalRing_of_isLocalization_atPrime_chartAlgInf_of_algEquiv_apply_eq_xH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/3859ad07-8f56-5391-9133-704b9cf04293

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_isRegularLocalRing_of_isLocalization_atPrime_chartAlgInf_of_algEquiv_apply_eq_xH

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open scoped MatrixGroups

namespace RegTransport

open AlgebraicCurve.TwoChartIntegralModel

theorem exists_algHom_chartAlgInf {R F F' : Type} [CommRing R] [Field F] [Field F'] [Algebra R F] [Algebra R F']
    (φ : F →ₐ[R] F') (j : F) (j' : F') [Fact (j ≠ 0)] [Fact (j' ≠ 0)] (hj : φ j = j') :
    ∃ ι : ↥(chartAlgInf R F j) →ₐ[R] ↥(chartAlgInf R F' j'), ∀ x : ↥(chartAlgInf R F j), ((ι x : ↥(chartAlgInf R F' j')) : F') = φ (x : F) := by
  have hφj : φ j⁻¹ = j'⁻¹ := by rw [map_inv₀, hj]
  have hmapadj : (Algebra.adjoin R {j⁻¹}).map φ = Algebra.adjoin R {j'⁻¹} := by
    rw [AlgHom.map_adjoin, Set.image_singleton, hφj]
  let ψ : ↥(Algebra.adjoin R {j⁻¹}) →+* ↥(Algebra.adjoin R {j'⁻¹}) :=
    ((φ.comp (Algebra.adjoin R {j⁻¹}).val).codRestrict (Algebra.adjoin R {j'⁻¹})
      (fun x => hmapadj ▸ Subalgebra.mem_map.mpr ⟨x.1, x.2, rfl⟩)).toRingHom
  refine ⟨{ toFun := fun x => ⟨φ x, (x.2 : IsIntegral _ (x : F)).map_of_comp_eq ψ φ.toRingHom (by ext; rfl)⟩
            map_one' := Subtype.ext (map_one φ)
            map_mul' := fun x y => Subtype.ext (map_mul φ _ _)
            map_zero' := Subtype.ext (map_zero φ)
            map_add' := fun x y => Subtype.ext (map_add φ _ _)
            commutes' := fun a => Subtype.ext (φ.commutes a) }, fun x => rfl⟩

theorem transport {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (e : B ≃ₐ[A] B)
    (x : B) (hx : e x = x)
    (𝔫 P : Ideal B) [𝔫.IsPrime] [P.IsPrime] (hP : ∀ b, b ∈ 𝔫 ↔ e b ∈ P)
    (H : ∀ (Cm : Type) [CommRing Cm] [Algebra B Cm] [IsLocalization.AtPrime Cm 𝔫],
      IsRegularLocalRing Cm ∧ IsRegularLocalRing (Cm ⧸ Ideal.span {algebraMap B Cm x}))
    (Bm : Type) [CommRing Bm] [Algebra B Bm] [IsLocalization.AtPrime Bm P] :
    IsRegularLocalRing Bm ∧ IsRegularLocalRing (Bm ⧸ Ideal.span {algebraMap B Bm x}) := by
  classical
  let f : B →+* Bm := algebraMap B Bm
  have key := IsLocalization.isLocalization_of_base_ringEquiv P.primeCompl Bm (e.symm : B ≃ₐ[A] B).toRingEquiv
  have hmap : P.primeCompl.map (e.symm : B ≃ₐ[A] B).toRingEquiv = 𝔫.primeCompl := by
    ext b
    simp only [Submonoid.mem_map, Ideal.mem_primeCompl_iff]
    constructor
    · rintro ⟨c, hc, rfl⟩
      intro hb
      apply hc
      have := (hP _).mp hb
      simpa using this
    · intro hb
      refine ⟨e b, fun h => hb ((hP b).mpr h), ?_⟩
      simp
  rw [hmap] at key
  letI instT : Algebra B Bm := (f.comp (e.symm : B ≃ₐ[A] B).toRingEquiv.symm.toRingHom).toAlgebra
  obtain ⟨h1, h4⟩ := @H Bm _ instT key
  have halg : ∀ b : B, @algebraMap B Bm _ _ instT b = f (e b) := fun b => by
    show f ((e.symm : B ≃ₐ[A] B).toRingEquiv.symm.toRingHom b) = f (e b)
    congr 1
  rw [halg, hx] at h4
  exact ⟨h1, h4⟩

end RegTransport

open RegTransport AlgebraicCurve.TwoChartIntegralModel in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)

    (hι : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / q))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A)
    (σ : ↥K ≃ₐ[L] ↥K) (hσj : σ j = j)
    (Y : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j)) [Y.IsPrime]
    (hY : ∀ (Cm : Type) [CommRing Cm] [Algebra ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) Cm]
      [IsLocalization.AtPrime Cm Y],
      IsRegularLocalRing Cm ∧
        IsRegularLocalRing (Cm ⧸ Ideal.span {algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) Cm
          (algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) ϖ)}))
    (Y' : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j)) [Y'.IsPrime]
    (hY' : ∀ b' : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j), b' ∈ Y' ↔
      ∃ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j), b ∈ Y ∧ ((b' : ↥K)) = σ (b : ↥K))
    (Bm : Type) [CommRing Bm] [Algebra ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) Bm] [IsLocalization.AtPrime Bm Y'] :
    IsRegularLocalRing Bm ∧
      IsRegularLocalRing (Bm ⧸ Ideal.span {algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) Bm
        (algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) ϖ)}) := by
  classical
  let φ : ↥K →ₐ[A] ↥K := (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.restrictScalars A
  let ψ : ↥K →ₐ[A] ↥K := (σ.symm : ↥K ≃ₐ[L] ↥K).toAlgHom.restrictScalars A
  have hφ : ∀ x, φ x = σ x := fun x => rfl
  have hψ : ∀ x, ψ x = σ.symm x := fun x => rfl
  have hσj' : σ.symm j = j := by
    have h := congrArg σ.symm hσj
    rw [AlgEquiv.symm_apply_apply] at h
    exact h.symm
  obtain ⟨ιB, hιB⟩ := exists_algHom_chartAlgInf φ j j (hσj)
  obtain ⟨ιB', hιB'⟩ := exists_algHom_chartAlgInf ψ j j hσj'
  have h1 : ∀ x, ιB (ιB' x) = x := fun x => Subtype.ext (by rw [hιB, hιB', hφ, hψ, AlgEquiv.apply_symm_apply])
  have h2 : ∀ x, ιB' (ιB x) = x := fun x => Subtype.ext (by rw [hιB', hιB, hφ, hψ, AlgEquiv.symm_apply_apply])
  let e : ↥(chartAlgInf A (↥K) j) ≃ₐ[A] ↥(chartAlgInf A (↥K) j) :=
    AlgEquiv.ofAlgHom ιB ιB' (AlgHom.ext h1) (AlgHom.ext h2)
  have he : ∀ x, ((e x : ↥(chartAlgInf A (↥K) j)) : ↥K) = σ x := fun x => hιB x
  have hYY' : ∀ b, b ∈ Y ↔ e b ∈ Y' := by
    intro b
    rw [hY']
    constructor
    · intro hb
      exact ⟨b, hb, he b⟩
    · rintro ⟨b₀, hb₀, hbb₀⟩
      rw [he] at hbb₀
      have : (b : ↥K) = (b₀ : ↥K) := σ.injective hbb₀
      rw [Subtype.ext this]
      exact hb₀
  have hx : e (algebraMap A _ ϖ) = algebraMap A _ ϖ := e.commutes ϖ
  exact transport e _ hx Y Y' hYY' (fun Cm _ _ _ => hY Cm) Bm

end S_ModularCurve_FullLevel_isRegularLocalRing_of_isLocalization_atPrime_chartAlgInf_of_algEquiv_apply_eq_xH
end P2MW
export P2MW.S_ModularCurve_FullLevel_isRegularLocalRing_of_isLocalization_atPrime_chartAlgInf_of_algEquiv_apply_eq_xH (solution)
