-- Prove2me | solution 1 for ModularCurve.isMaximal_of_jInvChartInf_mem_of_forall_mem_nonunits_gauss_chartAlgInf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/6bfd005e-0767-56e6-ae73-cddbf3c93829

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isMaximal_of_jInvChartInf_mem_of_forall_mem_nonunits_gauss_chartAlgInf

set_option autoImplicit false

open IsLocalRing

namespace MaxAtCusp

open AlgebraicCurve.TwoChartIntegralModel

variable (R : Type) [CommRing R] (F : Type) [Field F] [Algebra R F] (s : F)

noncomputable def ψ : Polynomial R →ₐ[R] ↥(Algebra.adjoin R ({s} : Set F)) :=
  (Polynomial.aeval s).codRestrict (Algebra.adjoin R ({s} : Set F))
    (fun P => by
      rw [Algebra.adjoin_singleton_eq_range_aeval]
      exact ⟨P, rfl⟩)

theorem ψ_surjective : Function.Surjective (ψ R F s) := by
  rintro ⟨y, hy⟩
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hy
  obtain ⟨P, rfl⟩ := hy
  exact ⟨P, Subtype.ext rfl⟩

noncomputable def ι : ↥(Algebra.adjoin R ({s} : Set F)) →+* ↥(chartAlg R F {s}) :=
  (Subalgebra.inclusion (adjoin_le_chartAlg R F {s})).toRingHom

theorem ι_isIntegral : (ι R F s).IsIntegral := by
  intro x
  obtain ⟨P, hPm, hP⟩ := (mem_chartAlg_iff R F).mp x.2
  refine ⟨P, hPm, ?_⟩
  apply Subtype.ext
  have h1 := Polynomial.hom_eval₂ P (ι R F s) ((chartAlg R F {s}).val.toRingHom) x
  have h2 : ((chartAlg R F {s}).val.toRingHom).comp (ι R F s) = algebraMap ↥(Algebra.adjoin R ({s} : Set F)) F := rfl
  rw [h2] at h1
  exact h1.trans hP

theorem comp_isIntegral : ((ι R F s).comp (ψ R F s).toRingHom).IsIntegral :=
  RingHom.IsIntegral.trans _ _ (RingHom.isIntegral_of_surjective _ (ψ_surjective R F s)) (ι_isIntegral R F s)

theorem comp_X : (((ι R F s).comp (ψ R F s).toRingHom) Polynomial.X : F) = s := by
  show (Polynomial.aeval s (Polynomial.X : Polynomial R) : F) = s
  rw [Polynomial.aeval_X]

theorem comp_C (a : R) : (((ι R F s).comp (ψ R F s).toRingHom) (Polynomial.C a) : F) = algebraMap R F a := by
  show (Polynomial.aeval s (Polynomial.C a : Polynomial R) : F) = algebraMap R F a
  rw [Polynomial.aeval_C]

theorem isMaximal_of_X_mem_of_C_mem {A : Type} [CommRing A] [IsLocalRing A] (ϖ : A)
    (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ}) (P : Ideal (Polynomial A)) [P.IsPrime]
    (hX : (Polynomial.X : Polynomial A) ∈ P) (hC : Polynomial.C ϖ ∈ P) : P.IsMaximal := by
  let cc : Polynomial A →+* A := Polynomial.constantCoeff
  have hcc : Function.Surjective cc := fun a => ⟨Polynomial.C a, by simp [cc, Polynomial.constantCoeff_apply]⟩
  have hker : RingHom.ker cc ≤ P := by
    intro p hp
    rw [RingHom.mem_ker] at hp
    have : p = Polynomial.X * p.divX := by
      conv_lhs => rw [← Polynomial.X_mul_divX_add p]
      rw [show Polynomial.C (p.coeff 0) = 0 from by rw [← Polynomial.constantCoeff_apply, hp, map_zero], add_zero]
    rw [this]
    exact P.mul_mem_right _ hX
  have hP : P = (P.map cc).comap cc := by
    rw [Ideal.comap_map_of_surjective _ hcc, left_eq_sup]
    exact hker
  haveI : (P.map cc).IsPrime := Ideal.map_isPrime_of_surjective hcc hker
  have hmax : P.map cc = IsLocalRing.maximalIdeal A := by
    refine ((IsLocalRing.maximalIdeal.isMaximal A).eq_of_le Ideal.IsPrime.ne_top' ?_).symm
    rw [hϖ, Ideal.span_le, Set.singleton_subset_iff]
    have := Ideal.mem_map_of_mem cc hC
    simpa [cc, Polynomial.constantCoeff_apply] using this
  rw [hP, hmax]
  exact Ideal.comap_isMaximal_of_surjective cc hcc

end MaxAtCusp

theorem solution
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (y : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j)) [y.IsPrime]
    (hϖy : algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) ϖ ∈ y)
    (hcusp : AlgebraicCurve.TwoChartIntegralModel.jInvChartInf A (↥K) j ∈ y)
    (hz₀ : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j), (b : ↥K) ∈ W₀.nonunits → b ∈ y) :
    y.IsMaximal := by
  have hj0 : (j : ↥K) ≠ 0 := Fact.out

  let Ψ : Polynomial A →+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) :=
    (MaxAtCusp.ι A (↥K) (j : ↥K)⁻¹).comp (MaxAtCusp.ψ A (↥K) (j : ↥K)⁻¹).toRingHom
  have hΨ : Ψ.IsIntegral := MaxAtCusp.comp_isIntegral A (↥K) (j : ↥K)⁻¹
  have hX : Ψ Polynomial.X = AlgebraicCurve.TwoChartIntegralModel.jInvChartInf A (↥K) j :=
    Subtype.ext ((MaxAtCusp.comp_X A (↥K) (j : ↥K)⁻¹).trans (AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf (R := A) (F := ↥K) (j := j)).symm)
  have hC : Ψ (Polynomial.C ϖ) = algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) ϖ :=
    Subtype.ext (MaxAtCusp.comp_C A (↥K) (j : ↥K)⁻¹ ϖ)
  have hmax : (y.comap Ψ).IsMaximal :=
    MaxAtCusp.isMaximal_of_X_mem_of_C_mem ϖ hϖ (y.comap Ψ) (by rw [Ideal.mem_comap, hX]; exact hcusp)
      (by rw [Ideal.mem_comap, hC]; exact hϖy)
  exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap' Ψ hΨ y hmax

end S_ModularCurve_isMaximal_of_jInvChartInf_mem_of_forall_mem_nonunits_gauss_chartAlgInf
end P2MW
export P2MW.S_ModularCurve_isMaximal_of_jInvChartInf_mem_of_forall_mem_nonunits_gauss_chartAlgInf (solution)
