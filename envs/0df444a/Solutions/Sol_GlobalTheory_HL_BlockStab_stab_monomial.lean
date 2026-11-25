-- Prove2me | solution 1 for GlobalTheory.HL.BlockStab.stab_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:14:43.261184+00:00
-- url     : https://prove2.me/submissions/c14fb932-5bb0-4bec-b9a4-aa5de4bbf14b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesPairingStabilizerBlockDiagonal
import Theorems.Thm_GlobalTheory_HL_BlockStab_inv_facts
import Theorems.Thm_GlobalTheory_HL_BlockStab_mul_mono
import Theorems.Thm_GlobalTheory_HL_BlockStab_cj_mem_iff
import Theorems.Thm_GlobalTheory_HL_BlockStab_cT_mul_eq_one
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
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.BlockStab
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {n : ℕ}
namespace GlobalTheory.HL.BlockStab
theorem _root_.solution (L : LocE F E) (σ : Fin n → Fin n) (β : Fin n → ℕ) (c : Fin n → Eˣ)
    (Z : Matrix (Fin n) (Fin n) E) (hσ : ∀ a, σ (σ a) = a) (hβ : ∀ a, β (σ a) = β a)
    (hm : ∀ a b, a ≤ b → β a ≤ β b) (hr : ∀ a b, β a = β b → a < b → σ b < σ a)
    (hc : ∀ a b, β a = β b → c a = c b ∨ c a = - c b)
    (hZ : ∀ a b, Z a b = if b = σ a then (c a : E) else 0) :
    (∀ s s' : Matrix (Fin n) (Fin n) E, IsUni s → IsUni s' → cT L s * Z * s' = Z →
      (∀ i j, β i ≠ β j → s i j = 0 ∧ s' i j = 0) ∧ (IsIntM L s ↔ IsIntM L s')) ∧
    ∀ s : Matrix (Fin n) (Fin n) E, IsUni s → (∀ i j, β i ≠ β j → s i j = 0) →
      ∃ s', IsUni s' ∧ cT L s * Z * s' = Z := by
  have hlt : ∀ a b, β a < β b → a < b := fun a b h => by
    by_contra h'
    exact absurd (hm b a (not_lt.1 h')) (not_le.2 h)
  have key : ∀ X Y : Matrix (Fin n) (Fin n) E, IsUni X → IsUni Y → cT L X * Z = Z * Y →
      (∀ i j, β i ≠ β j → X i j = 0 ∧ Y i j = 0) ∧ (IsIntM L X ↔ IsIntM L Y) := by
    intro X Y hX hY h
    rw [mul_mono σ hσ (fun a => (c a : E)) Z hZ] at h
    simp only [cT] at h
    have hz : ∀ i j, β i ≠ β j → X i j = 0 ∧ Y i j = 0 := by
      intro i j hij
      rcases lt_or_gt_of_ne hij with h1 | h1
      · constructor
        · have h2 := h j i
          rw [hY.1 _ _ (hlt _ _ (by rwa [hβ, hβ])), mul_zero, Units.mul_left_eq_zero] at h2
          simpa using h2
        · have h2 := h (σ i) (σ j)
          rw [hX.1 _ _ (hlt _ _ (by rwa [hβ, hβ])), map_zero, zero_mul, hσ, hσ, eq_comm,
            Units.mul_right_eq_zero] at h2
          exact h2
      · exact ⟨hX.1 _ _ (hlt _ _ h1), hY.1 _ _ (hlt _ _ h1)⟩
    have he : ∀ i a, X a i ∈ L.O ↔ Y (σ i) (σ a) ∈ L.O := by
      intro i a
      by_cases hia : β a = β i
      · have h2 := h i a
        rw [← cj_mem_iff L]
        rcases hc a i hia with h3 | h3
        · rw [h3, mul_comm, Units.mul_right_inj] at h2
          rw [h2]
        · rw [h3, Units.val_neg, mul_neg, ← neg_mul, mul_comm, Units.mul_right_inj] at h2
          rw [← h2, neg_mem_iff]
      · rw [(hz a i hia).1, (hz (σ i) (σ a) (by rw [hβ, hβ]; exact Ne.symm hia)).2]
    refine ⟨hz, fun hi p q => ?_, fun hi p q => (he q p).2 (hi _ _)⟩
    have := (he (σ p) (σ q)).1 (hi _ _)
    rwa [hσ, hσ] at this
  refine ⟨fun s s' hs hs' h => ?_, fun s hs hb => ?_⟩
  · obtain ⟨B, b1, b2, b3, b4, -⟩ := inv_facts s hs
    obtain ⟨U, u1, u2, u3, u4, -⟩ := inv_facts s' hs'
    have e1 : cT L s * Z = Z * U := by
      conv_rhs => rw [← h, Matrix.mul_assoc, u1, Matrix.mul_one]
    have e2 : cT L B * Z = Z * s' := by
      conv_lhs => rw [← h, Matrix.mul_assoc, ← Matrix.mul_assoc, cT_mul_eq_one L _ _ b1, Matrix.one_mul]
    obtain ⟨k1, k2⟩ := key s U hs u3 e1
    obtain ⟨k3, k4⟩ := key B s' b3 hs' e2
    exact ⟨fun i j hij => ⟨(k1 i j hij).1, (k3 i j hij).2⟩,
      fun hi => k4.1 (b4 L.O hi), fun hi => k2.2 (u4 L.O hi)⟩
  · let U : Matrix (Fin n) (Fin n) E := fun p q =>
      ((c (σ p))⁻¹ : Eˣ) * (L.cj (s (σ q) (σ p)) * c (σ q))
    have hU : IsUni U := by
      refine ⟨fun p q hpq => ?_, fun p => ?_⟩
      · have : s (σ q) (σ p) = 0 := by
          by_cases h1 : β q = β p
          · exact hs.1 _ _ (hr _ _ h1 hpq)
          · exact hb _ _ (by rwa [hβ, hβ])
        simp [U, this]
      · simp [U, hs.2]
    have e1 : cT L s * Z = Z * U := by
      rw [mul_mono σ hσ (fun a => (c a : E)) Z hZ]
      intro i a
      simp [U, hσ, cT]
    obtain ⟨V, u1, u2, u3, -⟩ := inv_facts U hU
    exact ⟨V, u3, by rw [e1, Matrix.mul_assoc, u1, Matrix.mul_one]⟩
end GlobalTheory.HL.BlockStab
