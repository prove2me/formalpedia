-- Prove2me | solution 1 for GlobalTheory.ChartBaseChange.rep_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:05:15.042285+00:00
-- url     : https://prove2.me/submissions/efec450a-acf7-48b8-b8f7-760e79d462e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_GermEvalOneStandardPointSelf
import Theorems.Thm_GlobalTheory_ChartBaseChange_push_injective
import Theorems.Thm_GlobalTheory_ChartBaseChange_push_spMap
import Theorems.Thm_GlobalTheory_ChartBaseChange_jetCoeff_zR
import Theorems.Thm_GlobalTheory_ChartBaseChange_const_map
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jet_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_const_ev


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (IsGrpPullback pushHom)
open GlobalTheory.JetSer ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ChartBaseChange
variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
variable {d n N : ℕ}
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G']
  {π : G'.left ⟶ G.left} (hπ : IsGrpPullback G' G (Spec.map (CommRingCat.ofHom (algebraMap R R'))) π)
namespace GlobalTheory.ChartBaseChange
theorem _root_.solution (hJ : JetAlgSt) {x : Fam G (Fin d)} {x' : Fam G' (Fin d)}
    (hx' : ∀ m, push hπ (x' m) = spMap (jetCoeff R R' (Fin d) m) ≫ x m)
    {a : Fin N → Pt R' n d} (ha : ∀ i, GP (a i))
    {Θ : ∀ m, JetR R (Fin N × Fin d) m →ₐ[R] JetR R' (Fin n × Fin d) m} (hΘ : IsMove a Θ)
    {b : Pt R N d} {t : Fam G (Fin N × Fin d)} (ht : Rep x b t) (y : Fam G' (Fin n × Fin d)) :
    Rep x' (fun j => ev a (MvPowerSeries.map (algebraMap R R') (b j))) y ↔
      ∀ m, push hπ (y m) = spMap (Θ m) ≫ t m := by
  have key : ∀ m (ψ : JetR R' (Fin d) m →ₐ[R'] JetR R' (Fin n × Fin d) m),
      (∀ j, ψ (zR m j) = toJet m (ev a (MvPowerSeries.map (algebraMap R R') (b j)))) →
      push hπ (spMap ψ ≫ x' m) = spMap (Θ m) ≫ t m := by
    intro m ψ hψ
    obtain ⟨φ, hφ, e⟩ := ht.2 m
    rw [push_spMap, hx', e, ← Category.assoc, ← Category.assoc, spMap_comp, spMap_comp]
    congr 2
    refine jet_ext fun j => ?_
    show ψ (jetCoeff R R' _ _ (zR _ j)) = Θ m (φ (zR m j))
    rw [jetCoeff_zR, hψ, hφ, hΘ]
  constructor
  · intro h m
    obtain ⟨ψ, hψ, e⟩ := h.2 m
    rw [e, key m ψ hψ]
  · intro h
    have hc : ∀ j, constantCoeff (ev a (MvPowerSeries.map (algebraMap R R') (b j))) = 0 :=
      fun j => gt_const_ev a ha _ (const_map (ht.1 j))
    refine ⟨hc, fun m => ?_⟩
    obtain ⟨ψ, hψ⟩ := ((hJ R' (Fin n × Fin d)).2.2.2.2 (Fin d) _ hc m).1
    exact ⟨ψ, hψ, push_injective hπ ((h m).trans (key m ψ hψ).symm)⟩
end GlobalTheory.ChartBaseChange
