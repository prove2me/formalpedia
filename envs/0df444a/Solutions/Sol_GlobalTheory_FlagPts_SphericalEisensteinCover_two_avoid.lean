-- Prove2me | solution 1 for GlobalTheory.FlagPts.SphericalEisensteinCover.two_avoid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:57:38.200803+00:00
-- url     : https://prove2.me/submissions/1aa7a2b5-8427-4350-803c-b4f8d81b1b84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DiagMatLower
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsAdaptedFrameBigCell
import Theorems.Thm_GlobalTheory_FullFlag_map_sub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FullFlag.map_sub



set_option autoImplicit false
open Module TopologicalSpace GlobalTheory.FlagPts
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.FlagPts GlobalTheory.FlagPts.SphericalEisensteinCover
variable {k W : Type} [Field k] [AddCommGroup W] [Module k W]
namespace GlobalTheory.FlagPts.SphericalEisensteinCover
theorem _root_.solution (S H₁ H₂ : Submodule k W) (h₁ : ¬ S ≤ H₁) (h₂ : ¬ S ≤ H₂) :
    ∃ v ∈ S, v ∉ H₁ ∧ v ∉ H₂ := by
  obtain ⟨x, hxS, hx1⟩ := SetLike.not_le_iff_exists.1 h₁
  obtain ⟨y, hyS, hy2⟩ := SetLike.not_le_iff_exists.1 h₂
  by_cases hx2 : x ∈ H₂
  · by_cases hy1 : y ∈ H₁
    · refine ⟨x + y, S.add_mem hxS hyS, fun h => hx1 ?_, fun h => hy2 ?_⟩
      · simpa using H₁.sub_mem h hy1
      · simpa using H₂.sub_mem h hx2
    · exact ⟨y, hyS, hy1, hy2⟩
  · exact ⟨x, hxS, hx1, hx2⟩
end GlobalTheory.FlagPts.SphericalEisensteinCover
