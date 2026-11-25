-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HodgeLow.lowSt_of_dictSt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:37:32.958245+00:00
-- url     : https://prove2.me/submissions/59a9f7bb-c987-4b30-afd9-a561be77ea71

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PullbackZeroCochainsAlgebraMap
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeLow_qIsoAt_transport
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeLow_cn_heq
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_HodgeLow_mk__comp_6b8f8d3f6a0d
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_HodgeLow_mk__comp_dd1199b7125f
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_HodgeLow_mk__comp_78527bb5975f
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeLow_pull1_bijective
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeLow_pull2_bijective
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeLow_stein_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HodgeLow
namespace GlobalTheory.CompanionTheory.HodgeLow
theorem _root_.solution : DictSt → LowSt := by
  intro hD R _ C C' _ _ F F' m hQ
  obtain ⟨e₀, e₁, e₂, e₃, v₀, v₁, v₂, v₃, c₀, c₁, c₂⟩ := hD R C F
  obtain ⟨e₀', e₁', e₂', e₃', v₀', v₁', v₂', v₃', c₀', c₁', c₂'⟩ := hD R C' F'
  have p0 : ∀ f, e₀' (pulln m 0 f) = pullbackZeroCochains m (e₀ f) := fun f ↦ by
    funext T
    rw [v₀']
    change m.α T (f (ComposableArrows.mk₀ T ⋙ m.G)) = m.α T (e₀ f (m.G.obj T))
    rw [v₀]
    exact congrArg (m.α T) (eq_of_heq (cn_heq f (mk₀_comp m.G T)))
  have p1 : ∀ f, e₁' (pulln m 1 f) = pullbackOneCochains m (e₁ f) := fun f ↦ by
    funext T T' φ
    rw [v₁']
    change m.α T' (f (ComposableArrows.mk₁ φ ⋙ m.G)) = m.α T' (e₁ f _ _ (m.G.map φ))
    rw [v₁]
    exact congrArg (m.α T') (eq_of_heq (cn_heq f (mk₁_comp m.G φ)))
  have p2 : ∀ f, e₂' (pulln m 2 f) = pullbackTwoCochains m (e₂ f) := fun f ↦ by
    funext T T' T'' φ ψ
    rw [v₂']
    change m.α T'' (f (ComposableArrows.mk₂ φ ψ ⋙ m.G)) = m.α T'' (e₂ f _ _ _ (m.G.map φ) (m.G.map ψ))
    rw [v₂]
    exact congrArg (m.α T'') (eq_of_heq (cn_heq f (mk₂_comp m.G φ ψ)))
  refine ⟨pull1_bijective m ?_, pull2_bijective m ?_, stein_iff m ?_⟩
  · exact qIsoAt_transport e₀ e₁ e₂ e₀' e₁' e₂' c₀ c₁ c₀' c₁' p1 (hQ.2 0)
  · exact qIsoAt_transport e₁ e₂ e₃ e₁' e₂' e₃' c₁ c₂ c₁' c₂' p2 (hQ.2 1)
  · exact qIsoAt_transport (LinearEquiv.refl R R) e₀ e₁ (LinearEquiv.refl R R) e₀' e₁'
      (fun _ ↦ map_zero _) c₀ (fun _ ↦ map_zero _) c₀' p0 hQ.1
end GlobalTheory.CompanionTheory.HodgeLow
