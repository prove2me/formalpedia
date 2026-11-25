-- Prove2me | solution 1 for GlobalTheory.HL.DatumStab.stab_graph
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:33:13.050086+00:00
-- url     : https://prove2.me/submissions/646f5139-e7bd-48c7-89e2-ce58ccfb7abb

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
import Theorems.Thm_GlobalTheory_HL_DatumStab_X_le
import Theorems.Thm_P2M_GlobalTheory_HL_DatumStab_X__le_b88df43215a7
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.DatumStab
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ}
namespace GlobalTheory.HL.DatumStab
theorem _root_.solution (S : Frames L r k) {Λ : Submodule L.O S.V}
    {h : S.GLV} (hh : h ∈ S.H0) (hΛ : h • Λ = Λ) : h • S.graphOf Λ = S.graphOf Λ := by
  have hfix : ∀ y ∈ S.X, h y = y := fun y hy => complementGroup_fixes_frameSpan S hh y (X_le S hy)
  have hfix' : ∀ y ∈ S.X', h y = y := fun y hy => complementGroup_fixes_frameSpan S hh y (X'_le S hy)
  rw [smul_eq_iff] at hΛ
  have hth : ∀ x, S.InTh Λ (h x) ↔ S.InTh Λ x := fun x => by
    constructor
    · rintro ⟨y, hy, hx⟩
      obtain ⟨y, rfl⟩ := h.surjective y
      rw [← map_smul] at hx
      exact ⟨y, (hΛ y).1 hy, h.injective hx⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨h y, (hΛ y).2 hy, map_smul _ _ _⟩
  have key : ∀ p : S.V × S.V, h • p ∈ S.graphOf Λ ↔ p ∈ S.graphOf Λ := by
    rintro ⟨a, b⟩
    change (h a, h b) ∈ _ ↔ _
    constructor
    · rintro ⟨y', hy', y, hy, h1, h2, h3, h4, h5⟩
      obtain ⟨y, rfl⟩ := h.surjective y
      obtain ⟨y', rfl⟩ := h.surjective y'
      simp only [← map_sub, sub_iff hfix, sub_iff hfix', hth] at h3 h4 h5
      exact ⟨y', (hΛ _).1 hy', y, (hΛ _).1 hy, (perp_iff hh.1 hfix' _).1 h1,
        (perp_iff hh.1 hfix _).1 h2, h3, h4, h5⟩
    · rintro ⟨y', hy', y, hy, h1, h2, h3, h4, h5⟩
      refine ⟨h y', (hΛ _).2 hy', h y, (hΛ _).2 hy, (perp_iff hh.1 hfix' _).2 h1,
        (perp_iff hh.1 hfix _).2 h2, ?_, ?_, ?_⟩
      · simpa only [← map_sub, sub_iff hfix'] using h3
      · simpa only [← map_sub, sub_iff hfix] using h4
      · simpa only [← map_sub, hth] using h5
  ext p
  rw [Set.mem_smul_set_iff_inv_smul_mem, ← key, smul_inv_smul]
end GlobalTheory.HL.DatumStab
