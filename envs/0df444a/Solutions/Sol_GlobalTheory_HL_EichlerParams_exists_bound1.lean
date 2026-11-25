-- Prove2me | solution 1 for GlobalTheory.HL.EichlerParams.exists_bound1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:50:35.350175+00:00
-- url     : https://prove2.me/submissions/dc4ce7e8-b03b-4e6f-b3b5-58bd53183236

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalExtend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StrongApproximationAdditiveQuadraticExtensionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemCoord
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsSmulIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianSymplecticBasisLocalExtension
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_PlacesInt_isIntegral_of_quad
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory.HL.SAN
noncomputable section
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.EichlerParams
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
variable {R : Type} [CommRing R] [Algebra K R] [TopologicalSpace R]
variable (L : LocE K R)
namespace GlobalTheory.HL.EichlerParams
theorem _root_.solution (x : R) : ∃ e ∈ 𝒪[K], e ≠ 0 ∧ Sm L e⁻¹ x := by
  obtain ⟨t, ht⟩ := (L.cj_fix (x + L.cj x)).1 (by rw [map_add, L.cj_cj, add_comm])
  obtain ⟨n, hn⟩ := (L.cj_fix (x * L.cj x)).1 (by rw [map_mul, L.cj_cj, mul_comm])
  have key : ∀ k : K, ∃ c ∈ 𝒪[K], c ≠ 0 ∧ c * k ∈ 𝒪[K] := by
    intro k
    rcases (ValuativeRel.valuation K).valuationSubring.mem_or_inv_mem k with h | h
    · exact ⟨1, (𝒪[K]).one_mem, one_ne_zero, by rw [one_mul]; exact h⟩
    · by_cases hk : k = 0
      · exact ⟨1, (𝒪[K]).one_mem, one_ne_zero, by simp [hk]⟩
      · exact ⟨k⁻¹, h, inv_ne_zero hk, by rw [inv_mul_cancel₀ hk]; exact (𝒪[K]).one_mem⟩
  obtain ⟨c1, hc1, hc10, ht1⟩ := key t
  obtain ⟨c2, hc2, hc20, hn2⟩ := key n
  refine ⟨c1 * c2, (𝒪[K]).mul_mem hc1 hc2, mul_ne_zero hc10 hc20, ?_⟩
  have hI : algebraMap K R (c1 * c2) * x ∈ L.O := by
    rw [L.O_def]
    have htr : algebraMap K R (c2 * (c1 * t)) = algebraMap K R (c1 * c2) * x +
        L.cj (algebraMap K R (c1 * c2) * x) := by
      rw [map_mul L.cj, AlgEquiv.commutes, ← mul_add, ← ht]; simp only [map_mul]; ring
    have hnr : algebraMap K R ((c1 * c1 * c2) * (c2 * n)) = algebraMap K R (c1 * c2) * x *
        L.cj (algebraMap K R (c1 * c2) * x) := by
      rw [map_mul L.cj, AlgEquiv.commutes]
      have : algebraMap K R (c1 * c2) * x * (algebraMap K R (c1 * c2) * L.cj x) =
        algebraMap K R (c1 * c2) * algebraMap K R (c1 * c2) * (x * L.cj x) := by ring
      rw [this, ← hn]; simp only [map_mul]; ring
    exact GlobalTheory.HL.PlacesInt.isIntegral_of_quad (R := 𝒪[K]) _ _
      ⟨_, (𝒪[K]).mul_mem hc2 ht1⟩ ⟨_, (𝒪[K]).mul_mem ((𝒪[K]).mul_mem ((𝒪[K]).mul_mem hc1 hc1) hc2) hn2⟩ htr hnr
  refine ⟨_, hI, ?_⟩
  rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ (mul_ne_zero hc10 hc20), map_one, one_mul]
end GlobalTheory.HL.EichlerParams
