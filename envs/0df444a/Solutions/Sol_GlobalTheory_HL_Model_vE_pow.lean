-- Prove2me | solution 1 for GlobalTheory.HL.Model.vE_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:59:11.248182+00:00
-- url     : https://prove2.me/submissions/99f01889-8b65-4485-9fb0-1255bc6921a4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_HermitianLattices
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIntegralIff
import Theorems.Thm_GlobalTheory_HL_Model_nontrivial
import Theorems.Thm_GlobalTheory_HL_Model_algebraMap_mem_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Model
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.Model
theorem _root_.solution (L : LocE F E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) (u : 𝒪[F]ˣ) (k : ℤ) :
    vE L ϖ (algebraMap F E ((ϖ : F) ^ k * ((u : 𝒪[F]) : F))) = k := by
  have hϖ0 : (ϖ : F) ≠ 0 := fun e => hϖ.ne_zero (Subtype.ext e)
  have := nontrivial L
  unfold vE
  apply IsGreatest.csSup_eq
  refine ⟨⟨algebraMap F E ((u : 𝒪[F]) : F), (algebraMap_mem_iff L _).mpr (u : 𝒪[F]).2, by
    rw [map_mul]⟩, ?_⟩
  rintro m ⟨y, hy, he⟩
  by_contra hlt
  obtain ⟨j, hj⟩ : ∃ j : ℕ, m = k + ((j + 1 : ℕ) : ℤ) := ⟨(m - k - 1).toNat, by omega⟩
  have h1 : algebraMap F E ((ϖ : F) ^ m)⁻¹ * algebraMap F E ((ϖ : F) ^ m) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ (zpow_ne_zero _ hϖ0), map_one]
  have hy' : y = algebraMap F E (((ϖ : F) ^ (j + 1))⁻¹ * ((u : 𝒪[F]) : F)) := by
    calc y = algebraMap F E ((ϖ : F) ^ m)⁻¹ * (algebraMap F E ((ϖ : F) ^ m) * y) := by
          rw [← mul_assoc, h1, one_mul]
      _ = _ := by
          rw [← he, ← map_mul]
          congr 1
          rw [hj, zpow_add₀ hϖ0, zpow_natCast]
          field_simp
  have hz : ((ϖ : F) ^ (j + 1))⁻¹ * ((u : 𝒪[F]) : F) ∈ 𝒪[F] :=
    (algebraMap_mem_iff L _).mp (hy' ▸ hy)
  have hu : ϖ ^ (j + 1) * (⟨_, hz⟩ : 𝒪[F]) = (u : 𝒪[F]) := by
    apply Subtype.ext
    push_cast
    field_simp
  have hunit : IsUnit (ϖ ^ (j + 1)) := isUnit_of_mul_isUnit_left (hu ▸ u.isUnit)
  exact hϖ.not_isUnit ((isUnit_pow_iff (Nat.succ_ne_zero j)).mp hunit)
end GlobalTheory.HL.Model
