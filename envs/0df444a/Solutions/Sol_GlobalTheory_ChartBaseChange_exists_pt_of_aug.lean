-- Prove2me | solution 1 for GlobalTheory.ChartBaseChange.exists_pt_of_aug
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:16:42.516605+00:00
-- url     : https://prove2.me/submissions/10702869-657d-4b89-8da5-07234a06ca52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_GermEvalOneStandardPointSelf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_exists_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_le_preimage_of_nil
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pt_eps
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pt_injective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
namespace GlobalTheory.ChartBaseChange
theorem _root_.solution (C : Chart G) {A B : Type} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    (q : A →ₐ[R] B) (hq : Function.Surjective q) {m : ℕ} (hJ : (RingHom.ker q) ^ (m + 1) = ⊥)
    (y : sp (R₀ := R) A ⟶ G) (hy : spMap q ≫ y = 1) :
    ∃ h : Γ(G.left, C.U) →ₐ[R] A, y = ReciprocityTheory.ChartRestriction.G.Chart.pt C h ∧ q.comp h = (Algebra.ofId R B).comp (eps C) := by
  have hn : ∀ a ∈ RingHom.ker q, IsNilpotent a := fun a ha =>
    ⟨m + 1, by
      have := Ideal.pow_mem_pow ha (m + 1)
      rwa [hJ, Ideal.mem_bot] at this⟩
  obtain ⟨h, rfl⟩ := exists_pt C y (le_preimage_of_nil C q hq hn y _ (hy.trans (pt_eps C B).symm))
  refine ⟨h, rfl, pt_injective C ?_⟩
  rw [← spMap_pt, hy, pt_eps]
end GlobalTheory.ChartBaseChange
