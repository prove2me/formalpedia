-- Prove2me | solution 1 for GlobalTheory.trdeg_residueField_of_trdeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:16:26.677368+00:00
-- url     : https://prove2.me/submissions/fe86b26f-28ba-4319-a509-ae16340297c5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisKaehlerOfAlgebraicIndependent
import Theorems.Thm_GlobalTheory_rank_kaehler_eq_trdeg
import Theorems.Thm_GlobalTheory_one_tmul_D_ne_zero
import Theorems.Thm_GlobalTheory_exists_basis_kaehler_of_trdeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open scoped BigOperators TensorProduct nonZeroDivisors
open Module KaehlerDifferential IsLocalRing
variable (K : Type*) {V : Type*} [Field K] [PerfectField K] [CommRing V] [IsDomain V]
  [IsDiscreteValuationRing V] [Algebra K V] [Algebra.EssFiniteType K V]
  [Algebra.FormallySmooth K V]
variable (F : Type*) [Field F] [Algebra V F] [IsFractionRing V F] [Algebra K F]
  [IsScalarTower K V F]
variable (V)
namespace GlobalTheory
theorem _root_.solution {n : ℕ} (hn : Algebra.trdeg K F = n) :
    Algebra.trdeg K (ResidueField V) = (n - 1 : ℕ) := by
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨h, z, b, -, -⟩ := exists_basis_kaehler_of_trdeg K F hn ht
  let κ := ResidueField V
  have hs : Function.Surjective (algebraMap V κ) := residue_surjective
  have : Algebra.EssFiniteType K κ := .comp K V _
  have hker : RingHom.ker (algebraMap V κ) = Ideal.span {t} :=
    ker_residue.trans ht.maximalIdeal_eq
  have hk : LinearMap.ker (mapBaseChange K V κ) = Submodule.span κ {(1 : κ) ⊗ₜ[V] D K V t} := by
    apply le_antisymm
    · intro y hy
      obtain ⟨c, rfl⟩ := (exact_kerCotangentToTensor_mapBaseChange K V κ hs y).mp hy
      obtain ⟨⟨x, hx⟩, rfl⟩ := Ideal.toCotangent_surjective _ c
      rw [kerCotangentToTensor_toCotangent]
      rw [hker, Ideal.mem_span_singleton'] at hx
      obtain ⟨a, rfl⟩ := hx
      have ht₀ : algebraMap V κ t = 0 := by
        rw [← RingHom.mem_ker, hker]
        exact Ideal.mem_span_singleton_self t
      change (1 : κ) ⊗ₜ[V] D K V (a * t) ∈ _
      rw [Derivation.leibniz, TensorProduct.tmul_add, TensorProduct.tmul_smul,
        TensorProduct.tmul_smul, ← algebraMap_smul κ t, ht₀, zero_smul, add_zero,
        ← algebraMap_smul κ a]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker,
        mapBaseChange_tmul, map_D]
      have ht₀ : algebraMap V κ t = 0 := by
        rw [← RingHom.mem_ker, hker]
        exact Ideal.mem_span_singleton_self t
      rw [ht₀, map_zero, smul_zero]
  have h₂ := LinearMap.finrank_range_add_finrank_ker (mapBaseChange K V κ)
  rw [hk, finrank_span_singleton (one_tmul_D_ne_zero K ht),
    LinearMap.range_eq_top.mpr (mapBaseChange_surjective K V κ hs), finrank_top,
    finrank_eq_card_basis (b.baseChange κ), Fintype.card_fin] at h₂
  rw [← rank_kaehler_eq_trdeg, ← finrank_eq_rank, ← h₂, Nat.add_sub_cancel]
end GlobalTheory
