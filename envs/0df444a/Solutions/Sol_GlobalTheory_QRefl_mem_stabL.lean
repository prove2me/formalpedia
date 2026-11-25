-- Prove2me | solution 1 for GlobalTheory.QRefl.mem_stabL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:49:04.019135+00:00
-- url     : https://prove2.me/submissions/a3c388e7-6e10-40e7-be73-38cac86ed706

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfPerpEqBot
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_QuasiReflectionStabilizesLattice
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
open GlobalTheory GlobalTheory.QRefl
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
namespace GlobalTheory.QRefl
theorem _root_.solution (Λ : Submodule L.O (Fin n → E)) (h : (Fin n → E) ≃ₗ[E] (Fin n → E)) :
    h ∈ stabL L Λ ↔ ∀ v, h v ∈ Λ ↔ v ∈ Λ := by
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro e v
    constructor
    · intro hv
      rw [← e, Submodule.mem_smul_pointwise_iff_exists] at hv
      obtain ⟨w, hw, hwv⟩ := hv
      have : w = v := h.injective hwv
      exact this ▸ hw
    · intro hv
      rw [← e, Submodule.mem_smul_pointwise_iff_exists]
      exact ⟨v, hv, rfl⟩
  · intro e
    ext v
    rw [Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (e w).2 hw
    · intro hv
      refine ⟨h.symm v, (e _).1 (by simpa using hv), ?_⟩
      show h (h.symm v) = v
      simp
end GlobalTheory.QRefl
