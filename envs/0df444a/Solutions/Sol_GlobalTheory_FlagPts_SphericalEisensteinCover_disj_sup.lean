-- Prove2me | solution 1 for GlobalTheory.FlagPts.SphericalEisensteinCover.disj_sup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:56:14.796411+00:00
-- url     : https://prove2.me/submissions/71be08ed-4536-48ef-a8b0-1237def808b1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DiagMatLower
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsAdaptedFrameBigCell

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module TopologicalSpace GlobalTheory.FlagPts
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.FlagPts GlobalTheory.FlagPts.SphericalEisensteinCover
variable {k W : Type} [Field k] [AddCommGroup W] [Module k W]
namespace GlobalTheory.FlagPts.SphericalEisensteinCover
theorem _root_.solution (P G : Submodule k W) (v : W) (hPG : Disjoint P G) (hv : v ∉ P ⊔ G) :
    Disjoint P (G ⊔ k ∙ v) := by
  rw [Submodule.disjoint_def]
  intro x hxP hx
  obtain ⟨g, hg, y, hy, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
  by_cases hc : c = 0
  · subst hc
    rw [zero_smul, add_zero] at hxP ⊢
    exact Submodule.disjoint_def.1 hPG _ hxP hg
  · exfalso
    apply hv
    have h1 : g + c • v ∈ P ⊔ G := Submodule.mem_sup_left hxP
    have h2 : g ∈ P ⊔ G := Submodule.mem_sup_right hg
    have h3 : v = c⁻¹ • ((g + c • v) - g) := by
      rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [h3]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ h1 h2)
end GlobalTheory.FlagPts.SphericalEisensteinCover
