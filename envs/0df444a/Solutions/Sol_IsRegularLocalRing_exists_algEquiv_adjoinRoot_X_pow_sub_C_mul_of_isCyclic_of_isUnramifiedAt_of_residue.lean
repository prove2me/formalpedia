-- Prove2me | solution 1 for IsRegularLocalRing.exists_algEquiv_adjoinRoot_X_pow_sub_C_mul_of_isCyclic_of_isUnramifiedAt_of_residue
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/d3f7a107-3832-5be0-856f-96c24622da6b

import Mathlib
import Theorems.Thm_IsRegularLocalRing_exists_etale_isLocalRing_isPrimitiveRoot_of_isUnit
import Theorems.Thm_IsRegularLocalRing_exists_algEquiv_tensorProduct_isGalois_isCyclic_of_etale_of_isUnramifiedAt_of_forall_sub_mem
import Theorems.Thm_IsRegularLocalRing_exists_algEquiv_adjoinRoot_X_pow_sub_C_mul_of_baseChange_of_isIntegrallyClosed
import Theorems.Thm_IsRegularLocalRing_exists_algEquiv_adjoinRoot_X_pow_sub_C_mul_of_isCyclic_of_isUnramifiedAt_of_residue_of_isPrimitiveRoot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsRegularLocalRing_exists_algEquiv_adjoinRoot_X_pow_sub_C_mul_of_isCyclic_of_isUnramifiedAt_of_residue
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open IsLocalRing Polynomial
open scoped TensorProduct

universe u v w x

theorem solution
    {R : Type*} [CommRing R] [IsRegularLocalRing R] [IsDomain R] [IsAdicComplete (maximalIdeal R) R]
    (ϖ s : R) (hmax : maximalIdeal R = Ideal.span {ϖ, s}) (hdim : ringKrullDim R = 2)
    (e : ℕ) (he : 0 < e) (heR : IsUnit (e : R))
    (B : Type*) [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [IsLocalRing B] [IsNoetherianRing B]
    [Algebra R B] [Module.Finite R B] [FaithfulSMul R B]
    (K₀ : Type*) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type*) [Field F] [Algebra K₀ F] [Algebra R F] [IsScalarTower R K₀ F]
    [Algebra B F] [IsScalarTower R B F] [IsFractionRing B F]
    [FiniteDimensional K₀ F] [IsGalois K₀ F] (hcyc : IsCyclic (F ≃ₐ[K₀] F)) (hdeg : Module.finrank K₀ F = e)
    (hunr : ∀ (𝔭 : Ideal B) [𝔭.IsPrime], (𝔭.comap (algebraMap R B)).height = 1 →
      s ∉ 𝔭.comap (algebraMap R B) → Algebra.IsUnramifiedAt R 𝔭)
    (hres : ∀ b : B, ∃ r : R, b - algebraMap R B r ∈ maximalIdeal B) :
    ∃ u : Rˣ, Nonempty (B ≃ₐ[R] AdjoinRoot (X ^ e - C ((u : R) * s) : R[X])) := by
  classical

  obtain ⟨R', _, _, _, _, _, _, _, _, _, ζ, hζ, hdim', hmax'⟩ :=
    IsRegularLocalRing.exists_etale_isLocalRing_isPrimitiveRoot_of_isUnit ϖ s hmax hdim e he heR
  have heR' : IsUnit (e : R') := by simpa using heR.map (algebraMap R R')
  have hs' : algebraMap R R' s ∈ maximalIdeal R' := by
    rw [hmax']; exact Ideal.subset_span (by simp)

  obtain ⟨B', _, _, _, _, _, _, _, _, K₀', _, _, _, F', _, _, _, _, _, _, _, _, _, hcyc', hdeg', hunr', hres', ⟨eBC⟩⟩ :=
    IsRegularLocalRing.exists_algEquiv_tensorProduct_isGalois_isCyclic_of_etale_of_isUnramifiedAt_of_forall_sub_mem
      ϖ s hmax hdim e he heR B K₀ F hcyc hdeg hunr hres R'

  obtain ⟨u', ⟨e'⟩⟩ :=
    IsRegularLocalRing.exists_algEquiv_adjoinRoot_X_pow_sub_C_mul_of_isCyclic_of_isUnramifiedAt_of_residue_of_isPrimitiveRoot
      (algebraMap R R' ϖ) (algebraMap R R' s) hmax' hdim' e he heR' ζ hζ B' K₀' F' hcyc' hdeg' hunr' hres'

  have hs2 : s ∉ maximalIdeal R ^ 2 := by

    intro hs2
    have hle : maximalIdeal R ≤ Ideal.span {ϖ} := by
      refine Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
        (IsLocalRing.maximalIdeal_le_jacobson _) ?_
      rw [Ideal.smul_eq_mul, ← pow_two]
      conv_lhs => rw [hmax]
      rw [Ideal.span_insert]
      exact sup_le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr hs2) _
    have heq : maximalIdeal R = Ideal.span {ϖ} :=
      le_antisymm hle (by rw [hmax]; exact Ideal.span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _)))
    have h1 : (maximalIdeal R).spanFinrank ≤ 1 := by
      rw [heq]
      have := Submodule.spanFinrank_span_le_encard (R := R) ({ϖ} : Set R)
      rw [Set.encard_singleton] at this
      exact_mod_cast this
    have h2 := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
    rw [hdim] at h2
    have h3 : (maximalIdeal R).spanFinrank = 2 := by exact_mod_cast h2
    omega
  have hsm : s ∈ maximalIdeal R := by rw [hmax]; exact Ideal.subset_span (by simp)
  exact IsRegularLocalRing.exists_algEquiv_adjoinRoot_X_pow_sub_C_mul_of_baseChange_of_isIntegrallyClosed
    hdim.le s hsm hs2 e he heR R' B K₀ F hdeg hres u' (eBC.trans e')

end S_IsRegularLocalRing_exists_algEquiv_adjoinRoot_X_pow_sub_C_mul_of_isCyclic_of_isUnramifiedAt_of_residue
end P2MW
export P2MW.S_IsRegularLocalRing_exists_algEquiv_adjoinRoot_X_pow_sub_C_mul_of_isCyclic_of_isUnramifiedAt_of_residue (solution)
