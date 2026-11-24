-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEis.glue_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:03:26.524571+00:00
-- url     : https://prove2.me/submissions/e3dabbad-c750-4a7f-9262-524548fa5a19

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_StagedEstimateHolds
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_cls_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_cls_rep
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_rep_cls

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEis
open PositivityTheory.RgEis
variable {G : Type} [Group G] {P Δ Γ : Subgroup G}
namespace GlobalTheory.CompanionTheory.RgEis
theorem _root_.solution (hΔ : Δ ≤ Γ) (hP : ∀ γ ∈ Γ, γ ∈ P → γ ∈ Δ) :
    Function.Surjective (glue (P := P) hΔ) := by
  intro t
  obtain ⟨y, rfl⟩ : ∃ y : Γ, cls y = t := ⟨_, cls_rep t⟩
  obtain ⟨d, hdΔ, -, hd⟩ := rep_cls (P := Δ) y
  obtain ⟨p, hpP, hpΔ, hp⟩ := rep_cls (P := P) (⟨d⁻¹, Δ.inv_mem hdΔ⟩ : Δ)
  refine ⟨⟨cls y, cls ⟨d⁻¹, Δ.inv_mem hdΔ⟩⟩, ?_⟩
  apply cls_eq.2
  show (y : G) * (rep (cls ⟨d⁻¹, Δ.inv_mem hdΔ⟩ : Cos P Δ) * rep (cls y : Cos Δ Γ))⁻¹ ∈ P
  rw [hp, hd]
  have : (y : G) * (p * d⁻¹ * (d * y))⁻¹ = p⁻¹ := by group
  rw [this]
  exact P.inv_mem hpP
end GlobalTheory.CompanionTheory.RgEis
