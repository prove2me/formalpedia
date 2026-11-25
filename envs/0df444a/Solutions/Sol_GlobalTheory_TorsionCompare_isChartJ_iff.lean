-- Prove2me | solution 1 for GlobalTheory.TorsionCompare.isChartJ_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:12:33.679079+00:00
-- url     : https://prove2.me/submissions/8c9f563b-24d3-4240-a532-28367fe28c74

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_OriginChartMultiplication
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NotIsUnitNatCastOfIsLocalHom
import Theorems.Thm_GlobalTheory_TorsionCompare_UniversalJets_rename
import Theorems.Thm_GlobalTheory_TorsionCompare_law_iff

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
open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF GlobalTheory.IndefiniteRowSideFullHecke.OriginChartMultiplication
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TorsionCompare
variable {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G]
variable {d : ℕ}
namespace GlobalTheory.TorsionCompare
theorem _root_.solution (F : FGLaw R d) (x : ∀ m : ℕ, algOver R (JetR R (Fin 1 × Fin d) m) ⟶ G) :
    IsChartJ G F x ↔ IsOriginChart G (chartEquiv G d x) F := by
  constructor
  · intro h
    obtain ⟨h1, h2, h3⟩ := UniversalJets.rename G Prod.snd toOne toOne_snd (fun _ => rfl)
      (x := x) ⟨h.trunc, h.zero, h.univ⟩
    exact ⟨h1, h2, h3, fun m => (law_iff G F x m).mp (h.law m)⟩
  · rintro ⟨h1, h2, h3, h4⟩
    have hx := UniversalJets.rename G toOne Prod.snd (fun _ => rfl) toOne_snd
      (x := chartEquiv G d x) ⟨h1, h2, h3⟩
    have e : renameChart toOne (chartEquiv G d x) = x := (chartEquiv G d).left_inv x
    rw [e] at hx
    exact ⟨hx.1, hx.2.1, hx.2.2, fun m => (law_iff G F x m).mpr (h4 m)⟩
end GlobalTheory.TorsionCompare
