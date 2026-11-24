-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HodgeAlt.closed_of_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:28:16.679807+00:00
-- url     : https://prove2.me/submissions/82a5aac1-1606-44b2-81fd-c85d0877cc17

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsOfRTensor

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
open KaehlerDifferential
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HodgeAlt
variable {R : Type} [CommRing R] {C D : Type} [Category.{0} C] [Category.{0} D]
  {F : C ⥤ CommAlgCat.{0} R} {G : D ⥤ CommAlgCat.{0} R}
namespace GlobalTheory.CompanionTheory.HodgeAlt
theorem _root_.solution (p q : CoefMap (RingHom.id R) F G)
    (hb : Function.Surjective fun x : Glob1 F × Glob1 F ↦ pullGlob1 p x.1 + pullGlob1 q x.2)
    (hc : Closed1 F = ⊤) : Closed1 G = ⊤ := by
  refine eq_top_iff.2 fun ω _ ↦ ?_
  obtain ⟨⟨a, b⟩, rfl⟩ := hb ω
  have ha : a ∈ Closed1 F := hc ▸ Submodule.mem_top
  have hb' : b ∈ Closed1 F := hc ▸ Submodule.mem_top
  exact add_mem (pullClosed1 p ⟨a, ha⟩).2 (pullClosed1 q ⟨b, hb'⟩).2
end GlobalTheory.CompanionTheory.HodgeAlt
