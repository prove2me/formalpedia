-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.isReduced_chartAlgFin_quotient_span_natCast
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/42fa1ed5-470b-538e-a10e-959ad1ee9250

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Theorems.Thm_GaloisRep_ratLocalizedAt_isLocalRing
import Theorems.Thm_GaloisRep_ratLocalizedAt_maximalIdeal_eq_span_natCast
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_isReduced_chartAlgFin_quotient_span_natCast
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard
open ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel
p2m_open_scoped "Polynomial AlgebraicGeometry.Polynomial"

open scoped TensorProduct

namespace C7Qred

private theorem mem_of_tmul_one_eq_zero (R : Type) [CommRing R] (I : Ideal R) (A : Type) [CommRing A] [Algebra R A]
    (κ : Type) [CommRing κ] [Algebra R κ] (lam : κ →ₗ[R] (R ⧸ I)) (hlam : lam 1 = 1)
    (a : A) (ha : a ⊗ₜ[R] (1 : κ) = 0) : a ∈ I.map (algebraMap R A) := by
  have h0 : (1 : κ) ⊗ₜ[R] a = 0 := by
    rw [← TensorProduct.comm_tmul R A κ a 1, ha, map_zero]
  have h1 : (LinearMap.rTensor A lam) ((1 : κ) ⊗ₜ[R] a) = (1 : R ⧸ I) ⊗ₜ[R] a := by
    rw [LinearMap.rTensor_tmul, hlam]
  rw [h0, map_zero] at h1
  have h2 := congrArg (TensorProduct.quotTensorEquivQuotSMul A I) h1.symm
  rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, map_zero, Submodule.Quotient.mk_eq_zero,
    Ideal.smul_top_eq_map] at h2
  exact h2

private theorem isReduced_tensor (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN)
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] [Algebra (R q) κ] :
    IsReduced (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⊗[R q] κ) := by
  haveI hred : IsReduced (DRLevel.fibre (N₀ := N₀) (algebraMap (R q) κ)) := 𝔓.fibre_reduced κ (algebraMap (R q) κ)

  haveI : IsReduced (pullback (IgusaScheme.ιFin (N₀ * q) q)
      (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (R q) κ))))) :=
    isReduced_of_isOpenImmersion (pullback.snd (IgusaScheme.ιFin (N₀ * q) q)
      (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (R q) κ)))))

  have hι : IgusaScheme.ιFin (N₀ * q) q ≫ DRLevel.toBase N₀ q =
      Spec.map (CommRingCat.ofHom (algebraMap (R q) ↥(IgusaScheme.chartAlgFin (N₀ * q) q))) := IgusaScheme.ιFin_igusaTo (N₀ * q) q
  let e : pullback (IgusaScheme.ιFin (N₀ * q) q)
        (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (R q) κ)))) ≅
      Spec (CommRingCat.of (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⊗[R q] κ)) :=
    pullbackRightPullbackFstIso (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (algebraMap (R q) κ)))
        (IgusaScheme.ιFin (N₀ * q) q) ≪≫
      pullback.congrHom hι rfl ≪≫ pullbackSpecIso (R q) ↥(IgusaScheme.chartAlgFin (N₀ * q) q) κ
  haveI : IsReduced (Spec (CommRingCat.of (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⊗[R q] κ))) := isReduced_of_isOpenImmersion e.inv
  exact (affine_isReduced_iff (CommRingCat.of (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⊗[R q] κ))).mp inferInstance

end C7Qred

theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN) :
    IsReduced (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ Ideal.span {((q : ℕ) : ↥(IgusaScheme.chartAlgFin (N₀ * q) q))}) := by
  classical
  haveI hqF : Fact q.Prime := inferInstance

  haveI : IsLocalRing (R q) := GaloisRep.ratLocalizedAt.isLocalRing hqF.out
  have hmax : IsLocalRing.maximalIdeal (R q) = Ideal.span {(q : R q)} :=
    GaloisRep.ratLocalizedAt.maximalIdeal_eq_span_natCast q hqF.out
  haveI hqmax : (Ideal.span {(q : R q)}).IsMaximal := hmax ▸ IsLocalRing.maximalIdeal.isMaximal (R q)
  letI : Field (R q ⧸ Ideal.span {(q : R q)}) := Ideal.Quotient.field _
  have hqnu : ((q : ℕ) : R q) ∈ nonunits (R q) := by
    rw [← IsLocalRing.mem_maximalIdeal, hmax]
    exact Ideal.mem_span_singleton_self _
  haveI : CharP (R q ⧸ Ideal.span {(q : R q)}) q := CharP.quotient (R q) q hqnu
  haveI : CharP (AlgebraicClosure (R q ⧸ Ideal.span {(q : R q)})) q := charP_of_injective_algebraMap (algebraMap (R q ⧸ Ideal.span {(q : R q)}) (AlgebraicClosure (R q ⧸ Ideal.span {(q : R q)}))).injective q

  haveI hT : IsReduced (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⊗[R q] (AlgebraicClosure (R q ⧸ Ideal.span {(q : R q)}))) := C7Qred.isReduced_tensor N₀ q hqN 𝔓 (AlgebraicClosure (R q ⧸ Ideal.span {(q : R q)}))

  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap (R q ⧸ Ideal.span {(q : R q)}) (AlgebraicClosure (R q ⧸ Ideal.span {(q : R q)})))
    (LinearMap.ker_eq_bot.mpr (algebraMap (R q ⧸ Ideal.span {(q : R q)}) (AlgebraicClosure (R q ⧸ Ideal.span {(q : R q)}))).injective)
  have hg1 : g 1 = 1 := by
    have := LinearMap.congr_fun hg (1 : (R q ⧸ Ideal.span {(q : R q)}))
    rw [LinearMap.comp_apply, Algebra.linearMap_apply, map_one, LinearMap.id_apply] at this
    exact this
  let lam : (AlgebraicClosure (R q ⧸ Ideal.span {(q : R q)})) →ₗ[R q] (R q ⧸ Ideal.span {(q : R q)}) := g.restrictScalars (R q)
  have hlam : lam 1 = 1 := hg1

  have hq0 : algebraMap (R q) (AlgebraicClosure (R q ⧸ Ideal.span {(q : R q)})) (q : R q) = 0 := by
    rw [IsScalarTower.algebraMap_apply (R q) (R q ⧸ Ideal.span {(q : R q)}) (AlgebraicClosure (R q ⧸ Ideal.span {(q : R q)}))]
    have hqk : algebraMap (R q) (R q ⧸ Ideal.span {(q : R q)}) (q : R q) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
    rw [hqk, map_zero]
  have hker : ∀ a ∈ Ideal.span {((q : ℕ) : ↥(IgusaScheme.chartAlgFin (N₀ * q) q))},
      (Algebra.TensorProduct.includeLeftRingHom : ↥(IgusaScheme.chartAlgFin (N₀ * q) q) →+* ↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⊗[R q] (AlgebraicClosure (R q ⧸ Ideal.span {(q : R q)}))) a = 0 := by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp ha
    rw [map_mul]
    have h1 : (Algebra.TensorProduct.includeLeftRingHom : ↥(IgusaScheme.chartAlgFin (N₀ * q) q) →+* ↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⊗[R q] (AlgebraicClosure (R q ⧸ Ideal.span {(q : R q)}))) ((q : ℕ) : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) = 0 := by
      change ((q : ℕ) : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) ⊗ₜ[R q] (1 : (AlgebraicClosure (R q ⧸ Ideal.span {(q : R q)}))) = 0
      have h2 : ((q : ℕ) : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) = (q : R q) • (1 : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) := by
        rw [Algebra.smul_def, mul_one, map_natCast]
      rw [h2, TensorProduct.smul_tmul, Algebra.smul_def, mul_one, hq0, TensorProduct.tmul_zero]
    rw [h1, zero_mul]
  let ψ : (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ Ideal.span {((q : ℕ) : ↥(IgusaScheme.chartAlgFin (N₀ * q) q))}) →+* ↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⊗[R q] (AlgebraicClosure (R q ⧸ Ideal.span {(q : R q)})) :=
    Ideal.Quotient.lift _ Algebra.TensorProduct.includeLeftRingHom hker
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.eq_zero_iff_mem]
    have ha : a ⊗ₜ[R q] (1 : (AlgebraicClosure (R q ⧸ Ideal.span {(q : R q)}))) = 0 := by
      have := hx
      rwa [Ideal.Quotient.lift_mk] at this
    have hmem := C7Qred.mem_of_tmul_one_eq_zero (R q) (Ideal.span {(q : R q)}) ↥(IgusaScheme.chartAlgFin (N₀ * q) q) (AlgebraicClosure (R q ⧸ Ideal.span {(q : R q)})) lam hlam a ha
    rwa [Ideal.map_span, Set.image_singleton, map_natCast] at hmem
  exact isReduced_of_injective ψ hψ

end S_ModularCurve_DRModelPackageLevel_isReduced_chartAlgFin_quotient_span_natCast
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_isReduced_chartAlgFin_quotient_span_natCast (solution)
