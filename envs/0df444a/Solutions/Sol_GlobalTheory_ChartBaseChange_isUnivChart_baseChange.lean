-- Prove2me | solution 1 for GlobalTheory.ChartBaseChange.isUnivChart_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:26:32.873801+00:00
-- url     : https://prove2.me/submissions/624a6989-cc41-404d-9504-f5b3477c04cc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_GermEvalOneStandardPointSelf
import Theorems.Thm_GlobalTheory_ChartBaseChange_push_injective
import Theorems.Thm_GlobalTheory_ChartBaseChange_push_one
import Theorems.Thm_GlobalTheory_ChartBaseChange_push_spMap
import Theorems.Thm_GlobalTheory_ChartBaseChange_jetCoeff_zR
import Theorems.Thm_GlobalTheory_ChartBaseChange_pt_eps_self
import Theorems.Thm_GlobalTheory_ChartBaseChange_exists_pt_of_aug
import Theorems.Thm_GlobalTheory_ChartBaseChange_chart_aug
import Theorems.Thm_GlobalTheory_ChartBaseChange_fib_cond
import Theorems.Thm_GlobalTheory_ChartBaseChange_fib_ker
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetAug_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetLift_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jet_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ker_jetAug_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pt_injective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart


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
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
variable {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G']
  {π : G'.left ⟶ G.left} (hπ : IsGrpPullback G' G (Spec.map (CommRingCat.ofHom (algebraMap R R'))) π)
namespace GlobalTheory.ChartBaseChange
theorem _root_.solution [IsLocalRing R] {d : ℕ} {x : Fam G (Fin d)} (hx : IsUnivChart G d x)
    {x' : Fam G' (Fin d)} (hx' : ∀ m, push hπ (x' m) = spMap (jetCoeff R R' (Fin d) m) ≫ x m) :
    IsUnivChart G' d x' := by
  refine ⟨fun m => push_injective hπ ?_, fun m => push_injective hπ ?_, ?_⟩
  · rw [push_spMap, hx', hx', ← hx.1 m, ← Category.assoc, ← Category.assoc, spMap_comp, spMap_comp]
    congr 2
    refine jet_ext fun j => ?_
    show jetTruncR R' _ m (jetCoeff R R' _ _ (zR _ j)) = jetCoeff R R' _ _ (zR _ j)
    rw [jetCoeff_zR, jetCoeff_zR]
    rfl
  · rw [push_spMap, hx', push_one, ← Category.assoc, spMap_comp]
    have : ((jetZeroR R' (Fin d) m).restrictScalars R).comp (jetCoeff R R' (Fin d) m) =
        (jetCoeff R R' (Fin d) 0).comp (jetZeroR R (Fin d) m) := by
      refine jet_ext fun j => ?_
      show jetZeroR R' _ m (jetCoeff R R' _ _ (zR _ j)) = jetCoeff R R' _ _ (zR _ j)
      rw [jetCoeff_zR, jetCoeff_zR]
      rfl
    rw [this, ← spMap_comp, Category.assoc, hx.2.1, MonObj.comp_one]
  intro A _ _ aug m hJ y hy
  letI : Algebra R A := ((algebraMap R' A).comp (algebraMap R R')).toAlgebra
  haveI : IsScalarTower R R' A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨C⟩ := exists_chart G
  let q : A →ₐ[R] R' := aug.restrictScalars R
  have hq : Function.Surjective q := fun r => ⟨algebraMap R' A r, aug.commutes r⟩
  have hJq : (RingHom.ker q) ^ (m + 1) = ⊥ := hJ
  obtain ⟨h, hh, hqh⟩ := exists_pt_of_aug C q hq hJq (push hπ y) (by
    rw [← push_spMap, hy, push_one])
  obtain ⟨k, hk, hqk⟩ := exists_pt_of_aug C (jetAug R (Fin d) m) (fun r => ⟨algebraMap _ _ r, AlgHom.commutes _ r⟩)
    (ker_jetAug_pow _ m) (x m) (chart_aug hx m)
  let h₀ := fibLift q (eps C) h hqh
  obtain ⟨ψ₀, ⟨ha, hψ₀⟩, hu⟩ := hx.2.2 (fib q) (fibFst q) m (fib_ker q hJq) (ReciprocityTheory.ChartRestriction.G.Chart.pt C h₀) (by
    rw [spMap_pt]
    exact pt_eps_self C)
  have hb : ∀ j, fibSnd q (ψ₀ (zR m j)) ∈ RingHom.ker aug := fun j => by
    show q _ = 0
    rw [fib_cond, show fibFst q (ψ₀ (zR m j)) = 0 from (AlgHom.congr_fun ha _).trans (jetAug_zR m j), map_zero]
  refine ⟨jetLift R' (RingHom.ker aug) hJ _ hb, ⟨jet_ext fun j => ?_, push_injective hπ ?_⟩, ?_⟩
  · rw [AlgHom.comp_apply, jetLift_zR, jetAug_zR]
    exact hb j
  · have : ((jetLift R' (RingHom.ker aug) hJ _ hb).restrictScalars R).comp (jetCoeff R R' (Fin d) m) =
        (fibSnd q).comp ψ₀ := by
      refine jet_ext fun j => ?_
      show jetLift R' (RingHom.ker aug) hJ _ hb (jetCoeff R R' _ _ (zR _ j)) = _
      rw [jetCoeff_zR, jetLift_zR]
      rfl
    rw [push_spMap, hx', ← Category.assoc, spMap_comp, this, ← spMap_comp, Category.assoc, ← hψ₀, spMap_pt, hh]
    rfl
  · rintro ψ ⟨hψa, hψ⟩
    let v := (ψ.restrictScalars R).comp (jetCoeff R R' (Fin d) m)
    have hv : q.comp v = (Algebra.ofId R R').comp (jetAug R (Fin d) m) := by
      refine jet_ext fun j => ?_
      show aug.comp ψ (jetCoeff R R' _ _ (zR _ j)) = algebraMap R R' (jetAug R _ m (zR m j))
      rw [jetCoeff_zR, hψa, jetAug_zR, jetAug_zR, map_zero]
    have hvk : h = v.comp k := by
      apply pt_injective C
      rw [← hh, hψ, push_spMap, hx', ← Category.assoc, spMap_comp, hk, spMap_pt]
    have e := hu (fibLift q (jetAug R (Fin d) m) v hv) ⟨rfl, by
      rw [hk, spMap_pt]
      congr 1
      refine AlgHom.ext fun s => Subtype.ext (Prod.ext ?_ ?_)
      · exact (AlgHom.congr_fun hqk s).symm
      · exact AlgHom.congr_fun hvk s⟩
    refine jet_ext fun j => ?_
    rw [jetLift_zR, ← e]
    show _ = ψ (jetCoeff R R' _ _ (zR _ j))
    rw [jetCoeff_zR]
end GlobalTheory.ChartBaseChange
