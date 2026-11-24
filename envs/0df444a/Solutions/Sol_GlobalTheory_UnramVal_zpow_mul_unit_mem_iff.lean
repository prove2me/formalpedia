-- Prove2me | solution 1 for GlobalTheory.UnramVal.zpow_mul_unit_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:19:53.906256+00:00
-- url     : https://prove2.me/submissions/29b91822-cfb9-4c50-8a7e-a385e91b29e7

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.UnramVal
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.UnramVal
theorem _root_.solution {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (k : ℤ) (u : (𝒪[F])ˣ) :
    (ϖ : F) ^ k * ((u : 𝒪[F]) : F) ∈ 𝒪[F] ↔ 0 ≤ k := by
  have h0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  constructor
  · intro h
    by_contra hk
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = -((n : ℤ) + 1) := ⟨(-k - 1).toNat, by omega⟩
    refine hϖ.not_isUnit (IsUnit.of_mul_eq_one (ϖ ^ n * ⟨_, h⟩ * ((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F])) ?_)
    apply Subtype.ext
    have hu : ((u : 𝒪[F]) : F) * (((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F) = 1 := by
      rw [← Subring.coe_mul, Units.mul_inv]; rfl
    have h1 : (ϖ : F) * (ϖ : F) ^ n * (ϖ : F) ^ (-((n : ℤ) + 1)) = 1 := by
      rw [zpow_neg, zpow_add_one₀ h0, zpow_natCast]
      field_simp
    simp only [Subring.coe_mul, Subring.coe_pow, Subring.coe_one]
    linear_combination (((u : 𝒪[F]) : F) * (((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F)) * h1 + hu
  · intro hk
    lift k to ℕ using hk
    rw [zpow_natCast]
    exact Subring.mul_mem _ (Subring.pow_mem _ ϖ.2 k) (u : 𝒪[F]).2
end GlobalTheory.UnramVal
