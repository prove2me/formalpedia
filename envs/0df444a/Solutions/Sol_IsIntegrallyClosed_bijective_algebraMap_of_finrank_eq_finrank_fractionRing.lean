-- Prove2me | solution 1 for IsIntegrallyClosed.bijective_algebraMap_of_finrank_eq_finrank_fractionRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/b7ebd016-4365-528b-90c9-7aff09265457

import Mathlib
import Theorems.Thm_Algebra_finrank_tensorProduct_eq_finrank_of_isFractionRing_of_finite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsIntegrallyClosed_bijective_algebraMap_of_finrank_eq_finrank_fractionRing

set_option autoImplicit false

theorem solution
    {O W C : Type*} [CommRing O] [IsDomain O] [CommRing W] [IsDomain W] [IsIntegrallyClosed W]
    [CommRing C] [IsDomain C]
    [Algebra O W] [Module.Finite O W] [Module.Free O W] [FaithfulSMul O W]
    [Algebra O C] [Algebra.IsIntegral O C] [Algebra W C] [IsScalarTower O W C] [FaithfulSMul W C]
    (K₁ K : Type*) [Field K₁] [Field K] [Algebra O K₁] [IsFractionRing O K₁]
    [Algebra C K] [IsFractionRing C K] [Algebra K₁ K] [Algebra O K]
    [IsScalarTower O C K] [IsScalarTower O K₁ K]
    (h : Module.finrank O W = Module.finrank K₁ K) :
    Function.Bijective (algebraMap W C) := by
  classical
  refine ⟨FaithfulSMul.algebraMap_injective W C, fun c => ?_⟩

  letI algWK : Algebra W K := ((algebraMap C K).comp (algebraMap W C)).toAlgebra
  haveI : IsScalarTower W C K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower O W K := IsScalarTower.of_algebraMap_eq fun o => by
    show algebraMap O K o = algebraMap C K (algebraMap W C (algebraMap O W o))
    rw [← IsScalarTower.algebraMap_apply O W C, ← IsScalarTower.algebraMap_apply O C K]
  have hinjWK : Function.Injective (algebraMap W K) :=
    (IsFractionRing.injective C K).comp (FaithfulSMul.algebraMap_injective W C)
  haveI : FaithfulSMul W K := (faithfulSMul_iff_algebraMap_injective W K).mpr hinjWK

  let F := FractionRing W
  letI : Algebra F K := FractionRing.liftAlgebra W K
  haveI : IsScalarTower W F K := FractionRing.isScalarTower_liftAlgebra W K

  have hinjOF : Function.Injective (algebraMap O F) := by
    rw [IsScalarTower.algebraMap_eq O W F]
    exact (IsFractionRing.injective W F).comp (FaithfulSMul.algebraMap_injective O W)
  letI algK₁F : Algebra K₁ F := (IsFractionRing.lift (K := K₁) hinjOF).toAlgebra
  haveI : IsScalarTower O K₁ F := IsScalarTower.of_algebraMap_eq fun o => (IsFractionRing.lift_algebraMap hinjOF o).symm
  haveI : IsScalarTower K₁ F K := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_

    have hext : (algebraMap K₁ K) = (algebraMap F K).comp (algebraMap K₁ F) := by
      refine IsLocalization.ringHom_ext (nonZeroDivisors O) (RingHom.ext fun o => ?_)
      show algebraMap K₁ K (algebraMap O K₁ o) = algebraMap F K (algebraMap K₁ F (algebraMap O K₁ o))
      rw [← IsScalarTower.algebraMap_apply O K₁ K, ← IsScalarTower.algebraMap_apply O K₁ F,
        ← IsScalarTower.algebraMap_apply O F K]
    exact RingHom.congr_fun hext x

  have hF : Module.finrank K₁ F = Module.finrank O W := by
    have h1 := Algebra.finrank_tensorProduct_eq_finrank_of_isFractionRing_of_finite
      (A := O) (B := W) K₁ (F := K₁) (F' := F) (algebraMap K₁ F)
      (fun a => ((IsScalarTower.algebraMap_apply O W F a).symm.trans (IsScalarTower.algebraMap_apply O K₁ F a)))
    have hA : (algebraMap K₁ F).toAlgebra = algK₁F := Algebra.algebra_ext _ _ fun _ => rfl
    rw [hA] at h1
    rw [← h1, Module.finrank_baseChange]
  have hpos : 0 < Module.finrank K₁ K := by
    rw [← h]; exact Module.finrank_pos
  haveI : FiniteDimensional K₁ K := Module.finite_of_finrank_pos hpos
  haveI : FiniteDimensional K₁ F := Module.finite_of_finrank_pos (by rw [hF, h]; exact hpos)
  haveI : FiniteDimensional F K := Module.Finite.of_restrictScalars_finite K₁ F K
  have hFK : Module.finrank F K = 1 := by
    have htower := Module.finrank_mul_finrank K₁ F K
    rw [hF, h] at htower
    exact Nat.eq_of_mul_eq_mul_left hpos (htower.trans (mul_one _).symm)

  have hsurjFK : Function.Surjective (algebraMap F K) := by
    intro k
    have hk : k ∈ (⊤ : Subalgebra F K) := Algebra.mem_top
    rw [← Subalgebra.bot_eq_top_of_finrank_eq_one hFK, Algebra.mem_bot] at hk
    exact hk
  let e : F ≃ₐ[W] K :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom W F K) ⟨(algebraMap F K).injective, hsurjFK⟩
  haveI : IsFractionRing W K := IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors W) e

  haveI : Algebra.IsIntegral W C := Algebra.IsIntegral.tower_top O
  have hc : IsIntegral W (algebraMap C K c) :=
    (Algebra.IsIntegral.isIntegral (R := W) c).map (IsScalarTower.toAlgHom W C K)
  obtain ⟨w, hw⟩ := IsIntegrallyClosed.isIntegral_iff.mp hc
  refine ⟨w, IsFractionRing.injective C K ?_⟩
  rw [← hw]
  rfl

end S_IsIntegrallyClosed_bijective_algebraMap_of_finrank_eq_finrank_fractionRing
end P2MW
export P2MW.S_IsIntegrallyClosed_bijective_algebraMap_of_finrank_eq_finrank_fractionRing (solution)
