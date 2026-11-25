-- Prove2me | solution 1 for GlobalTheory.HL.congruence_subgroup_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:07:11.148205+00:00
-- url     : https://prove2.me/submissions/b4e1f880-b5b3-47cc-8493-efe2636948ee

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsPowSmulMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CongruenceSubgroupLatticeStabilizer
import Theorems.Thm_GlobalTheory_HL_CongFin_conj_smul_eq
import Theorems.Thm_GlobalTheory_HL_CongFin_relIndex_ne_zero
import Theorems.Thm_GlobalTheory_HL_CongFin_mem_stab_of_cong
import Theorems.Thm_GlobalTheory_HL_CongFin_exists_level
import Theorems.Thm_GlobalTheory_HL_CongFin_exists_pow_mul_mem
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_UnramOrder_order_facts
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
open GlobalTheory.HL.CongFin
namespace GlobalTheory.HL
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n : ℕ} (Λ : Submodule L.O (Fin n → E)), IsLat L Λ → ∀ N : ℕ, (∃ K : Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E)), (∀ g, g ∈ K ↔ g ∈ stabL L Λ ∧ CongId L ϖ Λ N g) ∧ K.relIndex (stabL L Λ) ≠ 0 ∧ ∀ a ∈ stabL L Λ, MulAut.conj a • K = K) ∧ (1 ≤ N → ∀ g, CongId L ϖ Λ N g → g ∈ stabL L Λ) ∧ ∀ Λ', IsLat L Λ' → ∃ N' : ℕ, ∀ g, CongId L ϖ Λ N' g → CongId L ϖ Λ' N g := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ n Λ hΛ N
  obtain ⟨-, -, -, -, hO, hcard, hq, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  have hp : algebraMap F E ϖ ∈ L.O := (hO _).2 ϖ.2
  have hu : IsUnit (algebraMap F E ϖ) :=
    (IsUnit.mk0 (ϖ : F) (fun h => hϖ.ne_zero (Subtype.ext h))).map _
  have hdiv := exists_pow_mul_mem L ϖ hϖ
  simp only [CongId, map_pow]
  refine ⟨⟨congSub Λ (algebraMap F E ϖ ^ N), fun g => Iff.rfl, ?_, fun a ha => conj_smul_eq Λ _ ha⟩,
    fun hN g hg => mem_stab_of_cong hp hdiv Λ hΛ.1 hΛ.2 hN g hg,
    fun Λ' hΛ' => exists_level hp hu hdiv Λ Λ' hΛ.1 hΛ.2 hΛ'.1 hΛ'.2 N⟩
  refine relIndex_ne_zero Λ hΛ.1 (L.O.pow_mem hp N) ?_
  have hs : {y : L.O | (y : E) = algebraMap F E ((ϖ : F) ^ N)}
      = {(⟨algebraMap F E ϖ ^ N, L.O.pow_mem hp N⟩ : L.O)} := by
    ext y; simp [Subtype.ext_iff]
  have h := hcard N
  rw [hs] at h
  refine Nat.finite_of_card_ne_zero ?_
  rw [h]
  exact pow_ne_zero _ (by omega)
end GlobalTheory.HL
