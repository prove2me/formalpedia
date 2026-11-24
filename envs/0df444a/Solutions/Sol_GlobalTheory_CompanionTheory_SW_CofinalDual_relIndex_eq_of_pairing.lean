-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.CofinalDual.relIndex_eq_of_pairing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:49:19.892366+00:00
-- url     : https://prove2.me/submissions/8818d0cf-b521-485f-8f6e-d53771b56aef

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AnnihilatorOfAnnihilatorLe
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_CofinalDual_index_eq_of_pairing

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.CofinalDual
namespace GlobalTheory.CompanionTheory.SW.CofinalDual
theorem _root_.solution {V : Type} [AddCommGroup V] (χ : V → V → ℂ)
    (hs : ∀ x y, χ x y = χ y x) (hn : ∀ x y, ‖χ x y‖ = 1)
    (ha : ∀ x x' y, χ (x + x') y = χ x y * χ x' y) (X₀ X Y₀ Y : AddSubgroup V)
    (hX : ∀ x ∈ X, (x ∈ X₀ ↔ ∀ y ∈ Y, χ x y = 1))
    (hY : ∀ y ∈ Y, (y ∈ Y₀ ↔ ∀ x ∈ X, χ x y = 1))
    (fX : X₀.relIndex X ≠ 0) (fY : Y₀.relIndex Y ≠ 0) : X₀.relIndex X = Y₀.relIndex Y := by
  haveI : (X₀.addSubgroupOf X).FiniteIndex := ⟨fX⟩
  haveI : (Y₀.addSubgroupOf Y).FiniteIndex := ⟨fY⟩
  refine index_eq_of_pairing (fun (x : X) (y : Y) => χ x y) (fun x y => hn _ _)
    (fun x x' y => ha _ _ _)
    (fun x y y' => by
      change χ x ((y : V) + y') = _
      rw [hs, ha, hs y, hs y']) _ _ ?_ ?_
  · intro x
    rw [AddSubgroup.mem_addSubgroupOf, hX x x.2]
    exact ⟨fun h y => h y y.2, fun h y hy => h ⟨y, hy⟩⟩
  · intro y
    rw [AddSubgroup.mem_addSubgroupOf, hY y y.2]
    exact ⟨fun h x => h x x.2, fun h x hx => h ⟨x, hx⟩⟩
end GlobalTheory.CompanionTheory.SW.CofinalDual
