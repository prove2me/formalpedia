-- Prove2me | solution 1 for GlobalTheory.isUnit_adjoinRoot_mk_of_aeval_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:35:50.871604+00:00
-- url     : https://prove2.me/submissions/efacea54-e246-40da-a218-9ccdd0b368e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Polynomial IsLocalRing
open scoped TensorProduct
universe u
variable {B W : Type u} {K : Type*} [CommRing B] [CommRing W] [Field K] [IsLocalRing B]
  [Algebra B W] [Algebra B K] [Algebra (ResidueField B) K] [IsScalarTower B (ResidueField B) K]
omit [Algebra B W] [CommRing W]
namespace GlobalTheory
theorem _root_.solution {θ : K} (hθ : IsIntegral (ResidueField B) θ)
    {μ : B[X]} (hμm : μ.Monic) (hμ : μ.map (residue B) = minpoly (ResidueField B) θ) {g : B[X]}
    (hg : aeval θ g ≠ 0) : IsUnit (AdjoinRoot.mk μ g) := by
  have : Module.Finite B (AdjoinRoot μ) := hμm.finite_adjoinRoot
  by_contra hn
  obtain ⟨M, hM, hgM⟩ := exists_max_ideal_of_mem_nonunits hn
  have hM' : M.comap (algebraMap B (AdjoinRoot μ)) = maximalIdeal B :=
    eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M)
  have hco : IsCoprime (minpoly (ResidueField B) θ) (g.map (residue B)) := by
    rw [(minpoly.irreducible hθ).coprime_iff_not_dvd, minpoly.dvd_iff]
    rwa [← aeval_map_algebraMap (ResidueField B)] at hg
  obtain ⟨a, b, hab⟩ := hco
  obtain ⟨a, rfl⟩ := map_surjective (residue B) residue_surjective a
  obtain ⟨b, rfl⟩ := map_surjective (residue B) residue_surjective b
  have h₀ : (a * μ + b * g - 1).map (residue B) = 0 := by
    rw [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, hμ, hab,
      Polynomial.map_one, sub_self]
  have h₁ : AdjoinRoot.mk μ (a * μ + b * g - 1) ∈ M := by
    rw [(a * μ + b * g - 1).as_sum_support_C_mul_X_pow, map_sum]
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [map_mul]
    refine Ideal.mul_mem_right _ _ ?_
    change algebraMap B (AdjoinRoot μ) _ ∈ M
    rw [← Ideal.mem_comap, hM', ← residue_eq_zero_iff, ← coeff_map, h₀, coeff_zero]
  rw [map_sub, map_add, map_mul, map_mul, AdjoinRoot.mk_self, mul_zero, zero_add, map_one] at h₁
  have h₂ := sub_mem (M.mul_mem_left (AdjoinRoot.mk μ b) hgM) h₁
  rw [sub_sub_cancel] at h₂
  exact hM.ne_top ((Ideal.eq_top_iff_one _).mpr h₂)
end GlobalTheory
