-- Prove2me | solution 1 for GlobalTheory.HL.BlockStab.mul_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:29:07.895464+00:00
-- url     : https://prove2.me/submissions/62df9114-b50b-481c-b26e-3da41b012dff

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesPairingStabilizerBlockDiagonal
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
variable {E : Type} [CommRing E] {n : ℕ}
namespace GlobalTheory.HL.BlockStab
theorem _root_.solution (σ : Fin n → Fin n) (hσ : ∀ a, σ (σ a) = a) (c : Fin n → E)
    (Z : Matrix (Fin n) (Fin n) E) (hZ : ∀ a b, Z a b = if b = σ a then c a else 0)
    (X Y : Matrix (Fin n) (Fin n) E) :
    X * Z = Z * Y ↔ ∀ i a, X i a * c a = c i * Y (σ i) (σ a) := by
  have h1 : ∀ i a, (X * Z) i (σ a) = X i a * c a := by
    intro i a
    rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · simp [hZ]
    · intro k _ hk
      have : ¬ σ a = σ k := fun h => hk (by rw [← hσ k, ← h, hσ])
      simp [hZ, this]
    · simp
  have h2 : ∀ i j, (Z * Y) i j = c i * Y (σ i) j := by
    intro i j
    simp [Matrix.mul_apply, hZ]
  constructor
  · intro h i a; rw [← h1, h, h2]
  · intro h; ext i j; rw [← hσ j, h1, h2, h]
end GlobalTheory.HL.BlockStab
