-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Hodge.LiftO.exists_prim_cochain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:23:22.128078+00:00
-- url     : https://prove2.me/submissions/7160b7b8-206d-4225-b7c5-b7383bd0985c

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExteriorPairingIotaTwo
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyOne_class
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_eq_mk
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_eq_mk
import Theorems.Thm_GlobalTheory_CechDR_Hyp1_mk_eq_mk
import Theorems.Thm_GlobalTheory_CechDR_Hyp2_mk_eq_mk


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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hodge GlobalTheory.CompanionTheory.Hodge.LiftO
variable {R : Type} [CommRing R] {C E : Type} [Category.{0} C] [Category.{0} E]
  {F : C ⥤ CommAlgCat.{0} R} {G : E ⥤ CommAlgCat.{0} R}
namespace GlobalTheory.CompanionTheory.Hodge.LiftO
theorem _root_.solution (m p q : CoefMap (RingHom.id R) F G)
    (hm1 : ∀ c, m.pull1 c = p.pull1 c + q.pull1 c) (f : Z1 F) :
    ∃ g : C0 G, ∀ ⦃T T' : E⦄ (φ : T ⟶ T'), g T' - mp G φ (g T) =
      (m.pullbackOneCocycle f).1 T T' φ - ((p.pullbackOneCocycle f).1 T T' φ + (q.pullbackOneCocycle f).1 T T' φ) := by
  obtain ⟨g, hg⟩ := (H1.mk_eq_mk (F := G) (f := m.pullbackOneCocycle f) (f' := p.pullbackOneCocycle f + q.pullbackOneCocycle f)).1 (by
    have := hm1 (H1.mk F f)
    rwa [CoefMap.pullCohomologyOne_class, CoefMap.pullCohomologyOne_class, CoefMap.pullCohomologyOne_class, ← map_add] at this)
  exact ⟨g, fun T T' φ ↦ congrFun (congrFun (congrFun hg T) T') φ⟩
end GlobalTheory.CompanionTheory.Hodge.LiftO
