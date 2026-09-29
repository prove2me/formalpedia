-- Prove2me | solution 1 for ModularCurve.DRModelPackage.ringKrullDim_stalk_pullback_toBase_le_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/f90912bb-039b-5cc8-a73a-73190ae9739a

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Theorems.Thm_AlgebraicGeometry_IsOpenImmersion_ringKrullDim_stalk_eq
import Theorems.Thm_AlgebraicGeometry_IsAffineOpen_ringKrullDim_stalk_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackage_ringKrullDim_stalk_pullback_toBase_le_two

set_option autoImplicit false

p2m_open "Polynomial TensorProduct CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve P2MW.S_ModularCurve_DRModelPackage_ringKrullDim_stalk_pullback_toBase_le_two.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "DRModel DRModel.toBase DRModelPackage modularFunctionFieldFull IgusaScheme.jFull IgusaScheme"
namespace DRModelPackage
p2m_export "ModularCurve.DRModelPackage" "chartFin_finite chartInf_finite isIntegral w"
namespace Dim2
p2m_open "ModularCurve.DRModelPackage ModularCurve"

theorem ringKrullDim_le_of_isIntegral (A B : Type) [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.IsIntegral A B] : ringKrullDim B ≤ ringKrullDim A := by
  refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap A B)) ?_
  intro P Q hPQ
  have hPQ' : P.asIdeal < Q.asIdeal := hPQ
  obtain ⟨x, hxQ, hxP⟩ := Set.exists_of_ssubset hPQ'
  change Ideal.comap (algebraMap A B) P.asIdeal < Ideal.comap (algebraMap A B) Q.asIdeal
  exact Ideal.comap_lt_comap_of_integral_mem_sdiff hPQ'.le ⟨hxQ, hxP⟩ (Algebra.IsIntegral.isIntegral x)

theorem ringKrullDim_polynomial_eq_two (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] :
    ringKrullDim (Polynomial O) = 2 := by
  rw [Polynomial.ringKrullDim_of_isNoetherianRing, IsDiscreteValuationRing.ringKrullDim_eq_one]
  rfl

theorem ringKrullDim_tensorProduct_le_two (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A : Type) [CommRing A] (ψA : Polynomial ℤ →+* A) (hA : ψA.IsIntegral) :
    ringKrullDim (O ⊗[ℤ] A) ≤ 2 := by

  let φ : Polynomial O →ₐ[O] O ⊗[ℤ] A := Polynomial.aeval ((1 : O) ⊗ₜ[ℤ] ψA Polynomial.X)
  letI iA : Algebra (Polynomial ℤ) A := ψA.toAlgebra
  letI iT : Algebra (Polynomial O) (O ⊗[ℤ] A) := φ.toRingHom.toAlgebra
  letI iZT : Algebra (Polynomial ℤ) (O ⊗[ℤ] A) :=
    ((Algebra.TensorProduct.includeRight (R := ℤ) (A := O) (B := A)).toRingHom.comp ψA).toAlgebra
  letI iZO : Algebra (Polynomial ℤ) (Polynomial O) := (Polynomial.mapRingHom (algebraMap ℤ O)).toAlgebra
  have hcomp : φ.toRingHom.comp (Polynomial.mapRingHom (algebraMap ℤ O)) =
      (Algebra.TensorProduct.includeRight (R := ℤ) (A := O) (B := A)).toRingHom.comp ψA := by
    apply Polynomial.ringHom_ext
    · intro n
      have hC : (C n : ℤ[X]) = (n : ℤ[X]) := by rw [← Polynomial.C_eq_intCast, Int.cast_id]
      simp only [AlgHom.toRingHom_eq_coe, hC, map_intCast]
    · simp [φ]
  haveI : IsScalarTower (Polynomial ℤ) (Polynomial O) (O ⊗[ℤ] A) :=
    IsScalarTower.of_algebraMap_eq fun x => (RingHom.congr_fun hcomp x).symm

  let ι' : A →ₐ[Polynomial ℤ] O ⊗[ℤ] A :=
    { (Algebra.TensorProduct.includeRight (R := ℤ) (A := O) (B := A)).toRingHom with
      commutes' := fun _ => rfl }

  haveI : Algebra.IsIntegral (Polynomial O) (O ⊗[ℤ] A) := by
    refine ⟨fun t => ?_⟩
    induction t using TensorProduct.induction_on with
    | zero => exact isIntegral_zero
    | tmul o a =>
      have h1 : IsIntegral (Polynomial O) (o ⊗ₜ[ℤ] (1 : A)) := by
        have : o ⊗ₜ[ℤ] (1 : A) = algebraMap (Polynomial O) (O ⊗[ℤ] A) (Polynomial.C o) := by
          change _ = φ (Polynomial.C o)
          rw [Polynomial.aeval_C]
          rfl
        rw [this]
        exact isIntegral_algebraMap
      have h2 : IsIntegral (Polynomial O) ((1 : O) ⊗ₜ[ℤ] a) := by
        have ha : IsIntegral (Polynomial ℤ) a := hA a
        have := ha.map ι'
        exact this.tower_top
      have : o ⊗ₜ[ℤ] a = (o ⊗ₜ[ℤ] (1 : A)) * ((1 : O) ⊗ₜ[ℤ] a) := by
        simp [Algebra.TensorProduct.tmul_mul_tmul]
      rw [this]
      exact h1.mul h2
    | add x y hx hy => exact hx.add hy
  calc ringKrullDim (O ⊗[ℤ] A) ≤ ringKrullDim (Polynomial O) := ringKrullDim_le_of_isIntegral _ _
    _ = 2 := ringKrullDim_polynomial_eq_two O

section Geo
variable (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O]

theorem ringKrullDim_stalk_le_of_chart {A : Type} [CommRing A] (u : Spec (CommRingCat.of A) ⟶ DRModel p)
    [IsOpenImmersion u] (hu : u ≫ DRModel.toBase p = Spec.map (CommRingCat.ofHom (algebraMap ℤ A)))
    (z : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))
    (hz : (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).base z ∈
      Set.range ⇑u.base) :
    ringKrullDim ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk z) ≤
      ringKrullDim (A ⊗[ℤ] O) := by
  set v := pullback.snd u (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))
    with hv
  have hzv : z ∈ Set.range ⇑v.base := by
    rw [hv, Scheme.Pullback.range_snd]
    exact hz
  obtain ⟨w, rfl⟩ := hzv
  rw [← AlgebraicGeometry.IsOpenImmersion.ringKrullDim_stalk_eq v w]

  let e : pullback u (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ≅
      Spec (CommRingCat.of (A ⊗[ℤ] O)) :=
    pullbackRightPullbackFstIso (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) u ≪≫
      pullback.congrHom hu rfl ≪≫ pullbackSpecIso ℤ A O
  rw [AlgebraicGeometry.IsOpenImmersion.ringKrullDim_stalk_eq e.hom w]
  refine (AlgebraicGeometry.IsAffineOpen.ringKrullDim_stalk_le (isAffineOpen_top (Spec (CommRingCat.of (A ⊗[ℤ] O))))
    (e.hom.base w) trivial).trans (le_of_eq ?_)
  exact (ringKrullDim_eq_of_ringEquiv (Scheme.ΓSpecIso (CommRingCat.of (A ⊗[ℤ] O))).commRingCatIsoToRingEquiv)

end Geo

end ModularCurve.DRModelPackage.Dim2

open ModularCurve.DRModelPackage.Dim2 in

theorem solution
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (z : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))) :
    ringKrullDim ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk z) ≤ 2 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

  have hdim : ∀ {A : Type} [CommRing A] (ψ : Polynomial ℤ →+* A), ψ.IsIntegral →
      ringKrullDim (A ⊗[ℤ] O) ≤ 2 := fun {A} _ ψ hψ =>
    (ringKrullDim_eq_of_ringEquiv (Algebra.TensorProduct.comm ℤ A O).toRingEquiv).trans_le
      (ringKrullDim_tensorProduct_le_two O A ψ hψ)
  rcases AlgebraicCurve.TwoChartIntegralModel.mem_range_ιFin_or_mem_range_ιInf ℤ ↥(modularFunctionFieldFull p)
      (IgusaScheme.jFull p) ((pullback.fst (DRModel.toBase p) _).base z) with h | h
  · refine (ringKrullDim_stalk_le_of_chart p O _
      (AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase ℤ _ _) z h).trans
      (hdim (AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin ℤ ↥(modularFunctionFieldFull p)
        (IgusaScheme.jFull p)).toRingHom ?_)
    exact RingHom.Finite.to_isIntegral 𝔛.chartFin_finite
  · refine (ringKrullDim_stalk_le_of_chart p O _
      (AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase ℤ _ _) z h).trans
      (hdim (AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf ℤ ↥(modularFunctionFieldFull p)
        (IgusaScheme.jFull p)).toRingHom ?_)
    exact RingHom.Finite.to_isIntegral 𝔛.chartInf_finite

end S_ModularCurve_DRModelPackage_ringKrullDim_stalk_pullback_toBase_le_two
end P2MW
export P2MW.S_ModularCurve_DRModelPackage_ringKrullDim_stalk_pullback_toBase_le_two (solution)
