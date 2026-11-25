-- Prove2me | solution 1 for GlobalTheory.HL.DatumStab.stab_inner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:33:18.703676+00:00
-- url     : https://prove2.me/submissions/b373c550-efe8-4341-bed7-6b7a6b74dbe4

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemPerpSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DatumStabilizerBetweenLatticeStabilizers
import Theorems.Thm_GlobalTheory_HL_DatumStab_smul_eq_iff
import Theorems.Thm_GlobalTheory_HL_DatumStab_perp_iff
import Theorems.Thm_GlobalTheory_HL_DatumStab_sub_iff
import Theorems.Thm_GlobalTheory_HL_DatumStab_complementGroup_fixes_frameSpan

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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.DatumStab
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ}
namespace GlobalTheory.HL.DatumStab
theorem _root_.solution (S : Frames L r k) {A Λ : Submodule L.O S.V} {X : Submodule E S.V} (hX : X ≤ S.ME)
    (hA : ∀ x, x ∈ A ↔ ∃ y ∈ Λ, y ∈ perp L S.Hm X ∧ y - x ∈ X)
    {h : S.GLV} (hh : h ∈ S.H0) (hΛ : h • Λ = Λ) : h • A = A := by
  have hfix : ∀ y ∈ X, h y = y := fun y hy => complementGroup_fixes_frameSpan S hh y (hX hy)
  rw [smul_eq_iff] at hΛ ⊢
  intro x
  rw [hA, hA]
  constructor
  · rintro ⟨y, hy, hp, hx⟩
    obtain ⟨y, rfl⟩ := h.surjective y
    rw [← map_sub, sub_iff hfix] at hx
    exact ⟨y, (hΛ y).1 hy, (perp_iff hh.1 hfix y).1 hp, hx⟩
  · rintro ⟨y, hy, hp, hx⟩
    refine ⟨h y, (hΛ y).2 hy, (perp_iff hh.1 hfix y).2 hp, ?_⟩
    rwa [← map_sub, sub_iff hfix]
end GlobalTheory.HL.DatumStab
