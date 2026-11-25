-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.OpenModelSections.nonzeroOnFibre_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:57:40.934152+00:00
-- url     : https://prove2.me/submissions/e7535b40-93c4-462f-9e04-b59c3b393dd6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_CoefficientFieldBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_OpenModelSections

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.OpenModelSections
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.IndefiniteRowSideFullHecke.CoefficientFieldBaseChange
variable {X : Scheme.{0}} (G : Over X) (L : LB G.left)
namespace GlobalTheory.IndefiniteRowSideFullHecke.OpenModelSections
theorem _root_.solution {V : X.Opens} (θ : ∀ i, Γ(G.left, G.hom ⁻¹ᵁ V ⊓ L.U i)) (x : X)
    [IsReduced (Scheme.Hom.fiber G.hom x)] :
    NonzeroOnFibre G L θ x ↔ ∃ (i : L.ι) (g : G.left), G.hom g = x ∧ g ∈ G.left.basicOpen (θ i) := by
  refine exists_congr fun i => ?_
  rw [Ne, ← basicOpen_eq_bot_iff, ← Scheme.preimage_basicOpen]
  constructor
  · intro hne
    obtain ⟨y, hy⟩ : ∃ y, y ∈ Scheme.Hom.fiberι G.hom x ⁻¹ᵁ G.left.basicOpen (θ i) := by
      by_contra hh
      push_neg at hh
      exact hne (le_bot_iff.mp fun y hy => (hh y hy).elim)
    refine ⟨_, ?_, hy⟩
    have : Scheme.Hom.fiberι G.hom x y ∈ Set.range (Scheme.Hom.fiberι G.hom x) := ⟨y, rfl⟩
    rw [Scheme.Hom.range_fiberι] at this
    exact this
  · rintro ⟨g, hg, hb⟩ h0
    have : g ∈ Set.range (Scheme.Hom.fiberι G.hom x) := by
      rw [Scheme.Hom.range_fiberι]; exact hg
    obtain ⟨y, rfl⟩ := this
    have : y ∈ Scheme.Hom.fiberι G.hom x ⁻¹ᵁ G.left.basicOpen (θ i) := hb
    rw [h0] at this
    exact this
end GlobalTheory.IndefiniteRowSideFullHecke.OpenModelSections
