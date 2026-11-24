-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HodgeAlt.surj_of_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:28:15.191962+00:00
-- url     : https://prove2.me/submissions/6a96f29b-92eb-4031-b5f1-868048562ad4

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsOfRTensor
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_toO
import Theorems.Thm_GlobalTheory_CechDR_toO_pullHyp1


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
    (hb : Function.Surjective fun x : H1 F × H1 F ↦ p.pull1 x.1 + q.pull1 x.2)
    (hs : Function.Surjective (toO F)) : Function.Surjective (toO G) := by
  intro c
  obtain ⟨⟨a, b⟩, rfl⟩ := hb c
  obtain ⟨a, rfl⟩ := hs a
  obtain ⟨b, rfl⟩ := hs b
  exact ⟨pullHyp1 p a + pullHyp1 q b, by rw [map_add, toO_pullHyp1, toO_pullHyp1]⟩
end GlobalTheory.CompanionTheory.HodgeAlt
