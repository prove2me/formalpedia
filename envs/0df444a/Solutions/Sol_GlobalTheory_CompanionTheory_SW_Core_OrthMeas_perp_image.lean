-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Core.OrthMeas.perp_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:15:06.932389+00:00
-- url     : https://prove2.me/submissions/be680d8e-eece-40a9-b1be-bf0196ceadf0

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_WeilOrthogonalGroupInvariance

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.Core.OrthMeas
namespace GlobalTheory.CompanionTheory.SW.Core.OrthMeas
theorem _root_.solution {V : Type} (χ : V → V → ℂ) (e : V ≃ V)
    (hχ : ∀ x y, χ (e x) (e y) = χ x y) (L : Set V) :
    perp χ (e '' L) = e '' perp χ L := by
  ext y
  constructor
  · intro hy
    refine ⟨e.symm y, fun x hx => ?_, e.apply_symm_apply y⟩
    have := hy (e x) ⟨x, hx, rfl⟩
    rwa [← e.apply_symm_apply y, hχ] at this
  · rintro ⟨z, hz, rfl⟩ x ⟨w, hw, rfl⟩
    rw [hχ]
    exact hz w hw
end GlobalTheory.CompanionTheory.SW.Core.OrthMeas
