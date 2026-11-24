-- Prove2me | solution 1 for GlobalTheory.MaxOrder.isIntegral_aeval_eq_aeval_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:13:26.459551+00:00
-- url     : https://prove2.me/submissions/557df21c-f0d5-4575-90db-601794dcd8e0

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CharpolyEqPowOfIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralAevalEqAevalMapOfCoprimeCharpoly
import Theorems.Thm_GlobalTheory_MaxOrder_exists_eq_uniformizer_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Matrix GlobalTheory.LatOrb IsLocalRing
open GlobalTheory GlobalTheory.MaxOrder
namespace GlobalTheory.MaxOrder
theorem _root_.solution : ∀ {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] (n : ℕ) (P₀ : O[X]), IsCoprime P₀ (derivative P₀) →
    ∀ γ : Matrix (Fin n) (Fin n) K, γ.charpoly = P₀.map (algebraMap O K) →
    ∀ p : K[X], IsIntegral O (aeval γ p) → ∃ r : O[X], aeval γ p = aeval γ (r.map (algebraMap O K)) := by
  intro O K _ _ _ _ _ _ n P₀ hP γ hγ p hp
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  simp only [aeval_map_algebraMap]
  have hπK : algebraMap O K π ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective O K)]; exact hπ.ne_zero
  have key : ∀ k : ℕ, ∀ f : O[X], aeval γ f = π ^ k • aeval γ p → ∃ r : O[X], aeval γ p = aeval γ r := by
    intro k
    induction k with
    | zero => intro f hf; exact ⟨f, by rw [hf, pow_zero, one_smul]⟩
    | succ k ih =>
      intro f hf
      obtain ⟨h, hh⟩ := exists_eq_uniformizer_smul P₀ hP γ hγ π hπ _ hp (k + 1) (by omega) f hf
      refine ih h ?_
      have h1 : π • (π ^ k • aeval γ p) = π • aeval γ h := by rw [smul_smul, ← pow_succ', ← hf, hh]
      rw [← algebraMap_smul K π (π ^ k • aeval γ p), ← algebraMap_smul K π (aeval γ h)] at h1
      exact (smul_right_injective _ hπK h1).symm
  obtain ⟨b, hb⟩ := IsLocalization.integerNormalization_map_to_map (nonZeroDivisors O) p
  obtain ⟨k, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero b.2) hπ
  refine key k (C (↑v⁻¹ : O) * IsLocalization.integerNormalization (nonZeroDivisors O) p) ?_
  rw [map_mul, aeval_C, ← aeval_map_algebraMap K γ (IsLocalization.integerNormalization _ p), hb,
    ← algebraMap_smul K (b : O) p, map_smul, algebraMap_smul, ← Algebra.smul_def, smul_smul, hv,
    ← mul_assoc, Units.inv_mul, one_mul]
end GlobalTheory.MaxOrder
