-- Prove2me | solution 1 for GlobalTheory.adicCompletion_ringHom_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:26:45.574814+00:00
-- url     : https://prove2.me/submissions/3ae41eac-5dab-425d-9761-3be67cffa0c4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Theorems.Thm_GlobalTheory_pow_mul_le_comap_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry IsLocalRing
universe u
open GlobalTheory
variable {A R : Type*} [CommRing A] [CommRing R]
namespace GlobalTheory
theorem _root_.solution {J : Ideal A} (hJ : J.FG) (I : Ideal R) [IsHausdorff I R]
    {ψ ψ' : AdicCompletion J A →+* R} {k : ℕ}
    (hk : J.map (ψ.comp (algebraMap A (AdicCompletion J A))) ^ k ≤ I)
    (h : ψ.comp (algebraMap A (AdicCompletion J A)) =
      ψ'.comp (algebraMap A (AdicCompletion J A))) : ψ = ψ' := by
  apply DFunLike.coe_injective
  apply IsHausdorff.funext' I
  intro n x
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval J A (k * n) x)
  have hx : x - algebraMap A _ a ∈ (J ^ (k * n)).map (algebraMap A (AdicCompletion J A)) := by
    rw [← Submodule.restrictScalars_mem A, ← Ideal.smul_top_eq_map,
      AdicCompletion.pow_smul_top_eq_ker_eval hJ, LinearMap.mem_ker, map_sub, ← ha, sub_eq_zero]
    exact (AdicCompletion.eval_of J A _ a).symm
  have hmem : ∀ χ : AdicCompletion J A →+* R,
      χ.comp (algebraMap A (AdicCompletion J A)) = ψ.comp (algebraMap A (AdicCompletion J A)) →
      χ x - ψ (algebraMap A _ a) ∈ I ^ n := by
    intro χ hχ
    have h1 : χ (algebraMap A _ a) = ψ (algebraMap A _ a) := congr($hχ a)
    rw [← h1, ← map_sub]
    have h2 := Ideal.mem_map_of_mem χ hx
    rw [Ideal.map_map, hχ] at h2
    exact Ideal.map_le_iff_le_comap.mpr (pow_mul_le_comap_pow _ hk n) h2
  rw [Ideal.Quotient.eq]
  have := sub_mem (hmem ψ rfl) (hmem ψ' h.symm)
  simpa using this
end GlobalTheory
