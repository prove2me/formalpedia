-- Prove2me | solution 1 for GlobalTheory.QRefl.of_involution
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:07:00.089079+00:00
-- url     : https://prove2.me/submissions/b2850604-299f-4db3-8d8e-21d76a5be8dd

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfPerpEqBot
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_QuasiReflectionStabilizesLattice
import Theorems.Thm_GlobalTheory_QRefl_hf_add_left
import Theorems.Thm_GlobalTheory_QRefl_hf_add_right
import Theorems.Thm_GlobalTheory_QRefl_hf_smul_left
import Theorems.Thm_GlobalTheory_QRefl_hf_smul_right
import Theorems.Thm_GlobalTheory_QRefl_cj_hf
import Theorems.Thm_GlobalTheory_QRefl_mem_stabL
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HermOrthBasis_cj_hf
import Theorems.Thm_GlobalTheory_HermOrthBasis_hf_add_left
import Theorems.Thm_GlobalTheory_HermOrthBasis_hf_add_right
import Theorems.Thm_GlobalTheory_HermOrthBasis_hf_smul_left
import Theorems.Thm_GlobalTheory_HermOrthBasis_hf_smul_right
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
open GlobalTheory GlobalTheory.QRefl
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
namespace GlobalTheory.QRefl
theorem _root_.solution (hH : IsHerm L Hm) (c : (Fin n → E) →+ (Fin n → E))
    (hs : ∀ t v, c (t • v) = L.cj t • c v) (hc : ∀ v, c (c v) = v)
    (hf' : ∀ v w, hf L Hm (c v) (c w) = L.cj (hf L Hm v w))
    (Y : Submodule E (Fin n → E)) (hY : ∀ v ∈ Y, c v ∈ Y)
    (Λ : Submodule L.O (Fin n → E)) (hΛ : ∀ v ∈ Λ, c v ∈ Λ)
    (a : Fin n → E) (ha : c a = a) (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) (hg : IsQRefl L Hm a g) :
    ∃ α : ((Fin n → E) ≃ₗ[E] (Fin n → E)) ≃* ((Fin n → E) ≃ₗ[E] (Fin n → E)),
      (fixG L Hm Y ⊓ stabL L Λ).map α.toMonoidHom = fixG L Hm Y ⊓ stabL L Λ ∧ α g = g⁻¹ := by
  have hY' : ∀ v, c v ∈ Y ↔ v ∈ Y := fun v => ⟨fun h => hc v ▸ hY _ h, hY v⟩
  have hΛ' : ∀ v, c v ∈ Λ ↔ v ∈ Λ := fun v => ⟨fun h => hc v ▸ hΛ _ h, hΛ v⟩
  have key : ∀ h ∈ fixG L Hm Y ⊓ stabL L Λ, conjAut L c hs hc h ∈ fixG L Hm Y ⊓ stabL L Λ := by
    rintro h ⟨⟨h1, h2, h3⟩, h4⟩
    refine ⟨⟨fun v w => ?_, fun v => ?_, fun v hv => ?_⟩, ?_⟩
    · show hf L Hm (c (h (c v))) (c (h (c w))) = _
      rw [hf', h1, hf', L.cj_cj]
    · show c (h (c v)) ∈ Y ↔ _
      rw [hY', h2, hY']
    · show c (h (c v)) - v ∈ (⊥ : Submodule E (Fin n → E))
      have := h3 _ (hY v hv)
      rw [Submodule.mem_bot, sub_eq_zero] at this ⊢
      rw [this, hc]
    · refine (mem_stabL L Λ _).2 fun v => ?_
      show c (h (c v)) ∈ Λ ↔ _
      rw [hΛ', (mem_stabL L Λ _).1 h4, hΛ']
  refine ⟨conjAut L c hs hc, le_antisymm ?_ fun h hh => ?_, ?_⟩
  · rintro _ ⟨h, hh, rfl⟩
    exact key h hh
  · exact ⟨_, key h hh, (conjAut L c hs hc).left_inv h⟩
  · obtain ⟨hN, hi, s, hsv⟩ := hg
    have hN' : L.cj (hf L Hm a a) = hf L Hm a a := cj_hf L Hm hH a a
    have e1 : hf L Hm (g a) (g a) = hf L Hm a a := hi a a
    rw [hsv a] at e1
    simp only [hf_add_left, hf_add_right, hf_smul_left, hf_smul_right, map_mul, hN'] at e1
    have e2 : L.cj s + s + s * L.cj s * hf L Hm a a = 0 := by
      refine (hN.mul hN).mul_left_cancel ?_
      linear_combination e1
    rw [eq_inv_iff_mul_eq_one]
    ext1 v
    show c (g (c (g v))) = v
    have e3 : ∀ w, c (g (c w)) = w + (L.cj s * hf L Hm w a) • a := fun w => by
      rw [hsv, map_add, hc, hs, ha, map_mul]
      congr 3
      rw [← hf', hc, ha]
    rw [e3, hsv v, hf_add_left, hf_smul_left, add_assoc, ← add_smul]
    have : s * hf L Hm v a + L.cj s * (hf L Hm v a + s * hf L Hm v a * hf L Hm a a) = 0 := by
      linear_combination hf L Hm v a * e2
    rw [this, zero_smul, add_zero]
end GlobalTheory.QRefl
