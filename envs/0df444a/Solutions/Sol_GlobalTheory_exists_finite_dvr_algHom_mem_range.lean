-- Prove2me | solution 1 for GlobalTheory.exists_finite_dvr_algHom_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:00:12.281386+00:00
-- url     : https://prove2.me/submissions/71eb3059-3b3a-41f5-8ea2-e0675d07b1c8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsFiniteDvrExtensionEmbeddingResidueField
import Theorems.Thm_GlobalTheory_algebraMap_eq_zero_iff_mem_maximalIdeal
import Theorems.Thm_GlobalTheory_exists_isDiscreteValuationRing_of_flat
import Theorems.Thm_GlobalTheory_isUnit_adjoinRoot_mk_of_aeval_ne_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_FiniteAlgebraLocalCompletion_isAdicComplete_finite_algebra


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
namespace GlobalTheory
theorem _root_.solution {B K : Type} [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B] [IsAdicComplete (maximalIdeal B) B] [Field K] [Algebra B K]
    [IsLocalHom (algebraMap B K)] [Module.Finite B K] (θ : K) :
    ∃ (B' : Type) (_ : CommRing B') (_ : IsDomain B') (_ : IsDiscreteValuationRing B')
      (_ : IsAdicComplete (maximalIdeal B') B') (_ : Algebra B B'), Module.Finite B B' ∧
      Function.Injective (algebraMap B B') ∧
      ∃ e : B' →ₐ[B] K, IsLocalHom (e : B' →+* K) ∧ θ ∈ Set.range e := by
  let k := ResidueField B
  letI : Algebra k K := (ResidueField.lift (algebraMap B K)).toAlgebra
  have : IsScalarTower B k K := .of_algebraMap_eq fun b =>
    (ResidueField.lift_residue_apply (algebraMap B K) b).symm
  have hθ : IsIntegral k θ := (Algebra.IsIntegral.isIntegral (R := B) θ).tower_top
  obtain ⟨μ, hμ, -, hμm⟩ := lifts_and_natDegree_eq_and_monic (f := algebraMap B k)
    (p := minpoly k θ) (map_surjective _ residue_surjective _) (minpoly.monic hθ)
  let B' := AdjoinRoot μ
  have hμθ : aeval θ μ = 0 := by
    rw [← aeval_map_algebraMap k]
    exact (congrArg (aeval θ) hμ).trans (minpoly.aeval k θ)
  let e : B' →ₐ[B] K := AdjoinRoot.liftAlgHom μ (Algebra.ofId B K) θ hμθ
  have he₀ : e (AdjoinRoot.root μ) = θ := AdjoinRoot.liftAlgHom_root ..
  have he : ∀ g : B[X], e (AdjoinRoot.mk μ g) = aeval θ g := fun g => by
    rw [← AdjoinRoot.aeval_eq, ← aeval_algHom_apply, he₀]
  have hu : ∀ y : B', e y ≠ 0 → IsUnit y := fun y hy => by
    obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective y
    exact isUnit_adjoinRoot_mk_of_aeval_ne_zero hθ hμm hμ (he g ▸ hy)
  have : Nontrivial B' := e.toRingHom.domain_nontrivial
  have : IsLocalRing B' := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun y => by
    by_cases hy : e y = 0
    · exact Or.inr (hu _ (by simp [hy]))
    · exact Or.inl (hu _ hy)
  have hm : ∀ y : B', y ∈ maximalIdeal B' ↔ e y = 0 := fun y =>
    ⟨fun hy => by_contra fun h => hy (hu y h), fun hy h => (h.map e).ne_zero hy⟩
  have hfin : Module.Finite B B' := hμm.finite_adjoinRoot
  have : Module.Free B B' := hμm.free_adjoinRoot
  have hmap : (maximalIdeal B).map (algebraMap B B') = maximalIdeal B' := by
    refine le_antisymm (Ideal.map_le_iff_le_comap.mpr fun b hb => ?_) fun y hy => ?_
    · rw [Ideal.mem_comap, hm, AlgHom.commutes, algebraMap_eq_zero_iff_mem_maximalIdeal (K := K)]
      exact hb
    · obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective y
      rw [hm, he, ← aeval_map_algebraMap k] at hy
      obtain ⟨c, hc⟩ := minpoly.dvd k θ hy
      obtain ⟨c, rfl⟩ := map_surjective (algebraMap B k) residue_surjective c
      have h₀ : (g - μ * c).map (algebraMap B k) = 0 := by
        rw [Polynomial.map_sub, Polynomial.map_mul, hμ, hc, sub_self]
      have h₁ : AdjoinRoot.mk μ (g - μ * c) ∈ (maximalIdeal B).map (algebraMap B B') := by
        rw [(g - μ * c).as_sum_support_C_mul_X_pow, map_sum]
        refine Ideal.sum_mem _ fun i _ => ?_
        rw [map_mul]
        refine Ideal.mul_mem_right _ _ ?_
        change algebraMap B B' _ ∈ _
        refine Ideal.mem_map_of_mem _ ?_
        rw [← residue_eq_zero_iff]
        change algebraMap B k _ = 0
        rw [← coeff_map, h₀, coeff_zero]
      rwa [map_sub, map_mul, AdjoinRoot.mk_self, zero_mul, sub_zero] at h₁
  have : IsNoetherianRing B' := IsNoetherianRing.of_finite B B'
  obtain ⟨_, _⟩ := exists_isDiscreteValuationRing_of_flat B B' hmap
    (Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal B').ne_top)
  have hc := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isAdicComplete_finite_algebra (R := B) B'
  rw [hmap] at hc
  exact ⟨B', inferInstance, inferInstance, inferInstance, hc, inferInstance, hfin,
    FaithfulSMul.algebraMap_injective B B', e, ⟨fun y hy => hu y hy.ne_zero⟩,
    AdjoinRoot.root μ, he₀⟩
end GlobalTheory
