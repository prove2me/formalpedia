-- Prove2me | solution 1 for GlobalTheory.CubeFib.mapSer_iff_psJet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:43:00.966957+00:00
-- url     : https://prove2.me/submissions/cc869310-46c8-46c6-8d71-4247671f835b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubicalPullBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegUnif
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsFormalGroupLawOfChartOfJetChart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_PsJetEqToJetOfNonempty
import Theorems.Thm_GlobalTheory_ChartJLaw_psJet_eq_toJet


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
open GlobalTheory GlobalTheory.CubeFib
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open scoped BigOperators
attribute [local instance] Over.cartesianMonoidalCategory
variable {k : Type} [CommRing k] {d g : ℕ}
namespace GlobalTheory.CubeFib
theorem _root_.solution {G B : Over (Sp k)} (q : G ⟶ B) (x : ∀ m : ℕ, algOver k (JetR k (Fin 1 × Fin d) m) ⟶ G)
    (y : ∀ m : ℕ, algOver k (JetR k (Fin 1 × Fin g) m) ⟶ B) (ψ : Fin g → PS k 1 d) :
    MapSer q x y ψ ↔ (∀ j, MvPowerSeries.constantCoeff (ψ j) = 0) ∧
      ∀ m : ℕ, ∃ a : JetR k (Fin 1 × Fin g) m →ₐ[k] JetR k (Fin 1 × Fin d) m,
        (∀ j, a (zR m ((0 : Fin 1), j)) = psJet m (ψ j)) ∧ x m ≫ q = algOverHom a ≫ y m := by
  constructor
  · intro h
    refine ⟨h.constantCoeff_eq_zero, fun m => ?_⟩
    obtain ⟨a, ha, hq⟩ := h m
    exact ⟨a, fun j => (ha j).trans (GlobalTheory.ChartJLaw.psJet_eq_toJet m _ (h.constantCoeff_eq_zero j)).symm, hq⟩
  · rintro ⟨h0, h⟩ m
    obtain ⟨a, ha, hq⟩ := h m
    exact ⟨a, fun j => (ha j).trans (GlobalTheory.ChartJLaw.psJet_eq_toJet m _ (h0 j)), hq⟩
end GlobalTheory.CubeFib
