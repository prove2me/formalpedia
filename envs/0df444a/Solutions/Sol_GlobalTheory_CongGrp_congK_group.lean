-- Prove2me | solution 1 for GlobalTheory.CongGrp.congK_group
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:55:21.20623+00:00
-- url     : https://prove2.me/submissions/8e0cbae2-33f3-4643-b1c2-8eaf2bd2ad6e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CongruentOneMatricesTransitiveNearHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MatrixCongruentOneModUniformizerPowGroupAndOrbit
import Theorems.Thm_GlobalTheory_CongGrp_cont_pos
import Theorems.Thm_GlobalTheory_CongGrp_intM_mul
import Theorems.Thm_GlobalTheory_CongGrp_intM_neg
import Theorems.Thm_GlobalTheory_CongGrp_intM_smul
import Theorems.Thm_GlobalTheory_CongGrp_mem_congK
import Theorems.Thm_P2M_GlobalTheory_CongGrp_pow_mem__de67754d33b0
import Theorems.Thm_GlobalTheory_CongGrp_congK_basic
import Theorems.Thm_GlobalTheory_CongGrp_congK_int
import Theorems.Thm_GlobalTheory_CongGrp_congK_mul
import Theorems.Thm_GlobalTheory_CongGrp_congK_one
import Theorems.Thm_GlobalTheory_CongGrp_horb_isCO

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.CongGrp
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable [IsNonarchimedeanLocalField F] [CharZero F]
omit [IsNonarchimedeanLocalField F] [CharZero F]
namespace GlobalTheory.CongGrp
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ (m i : ℕ), 1 ≤ i → (1 : Matrix (Fin m) (Fin m) E) ∈ congK L ϖ m i ∧ (∀ A ∈ congK L ϖ m i, IsIntM L A ∧ IsUnit A.det ∧ vE L ϖ (A.det * L.cj A.det) = 0 ∧ A⁻¹ ∈ congK L ϖ m i ∧ (∀ B ∈ congK L ϖ m i, A * B ∈ congK L ϖ m i) ∧ ∀ i' ≥ i, ∀ B ∈ congK L ϖ m i', A⁻¹ * B * A ∈ congK L ϖ m i' ∧ B ∈ congK L ϖ m i) ∧ ∀ Γ : Matrix (Fin m) (Fin m) E, IsHerm L Γ → IsUnit Γ.det → IsCO (hermLat L m) (horb L ϖ Γ i) ∧ 0 < cont (hermLat L m) (horb L ϖ Γ i) := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ m i hi
  refine ⟨congK_one L ϖ, fun A hA => ?_, fun Γ hΓ hdet => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := congK_basic L ϖ hϖ hi hA
    have hAi := congK_int L ϖ hA
    have hinv : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A h1
    refine ⟨hAi, h1, h2, ?_, fun B hB => congK_mul L ϖ hA hB, fun i' hi' B hB => ⟨?_, ?_⟩⟩
    · obtain ⟨C, hC, hAC⟩ := (mem_congK L ϖ).1 hA
      refine (mem_congK L ϖ).2 ⟨-(A⁻¹ * C), intM_neg L (intM_mul L h3 hC), ?_⟩
      have : A⁻¹ * (1 + algebraMap F E ((ϖ : F) ^ i) • C) = 1 := by rw [← hAC, hinv]
      rw [mul_add, mul_one, Matrix.mul_smul] at this
      rw [smul_neg, ← sub_eq_add_neg]
      exact eq_sub_of_add_eq this
    · obtain ⟨D, hD, rfl⟩ := (mem_congK L ϖ).1 hB
      refine (mem_congK L ϖ).2 ⟨A⁻¹ * D * A, intM_mul L (intM_mul L h3 hD) hAi, ?_⟩
      rw [mul_add, add_mul, mul_one, hinv, Matrix.mul_smul, Matrix.smul_mul]
    · obtain ⟨D, hD, rfl⟩ := (mem_congK L ϖ).1 hB
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hi'
      refine (mem_congK L ϖ).2 ⟨_, intM_smul L (pow_mem' L ϖ k) hD, ?_⟩
      rw [pow_add, map_mul, mul_smul]
  · have h := horb_isCO L ϖ hϖ hi Γ hΓ hdet
    exact ⟨h, cont_pos _ _ h ⟨_, 1, congK_one L ϖ, rfl⟩⟩
end GlobalTheory.CongGrp
