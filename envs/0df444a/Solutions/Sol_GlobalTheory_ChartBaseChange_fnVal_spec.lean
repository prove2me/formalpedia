-- Prove2me | solution 1 for GlobalTheory.ChartBaseChange.fnVal_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:10:50.938791+00:00
-- url     : https://prove2.me/submissions/3e4b1f9e-a8e5-4155-a0cc-2d82f52842c2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_GermEvalOneStandardPointSelf

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
variable {A B : Type} [CommRing A] [CommRing B] {X Y : Scheme.{0}}
namespace GlobalTheory.ChartBaseChange
theorem _root_.solution (θ : A →+* B) (p : Spec (CommRingCat.of A) ⟶ X) (U : X.Opens) (f : Γ(X, U))
    (h : ⊤ ≤ p ⁻¹ᵁ U) :
    ⊤ ≤ (Spec.map (CommRingCat.ofHom θ) ≫ p) ⁻¹ᵁ U ∧
      fnVal (Spec.map (CommRingCat.ofHom θ) ≫ p) U f = θ (fnVal p U f) := by
  have h' : ⊤ ≤ (Spec.map (CommRingCat.ofHom θ) ≫ p) ⁻¹ᵁ U := fun z _ => h (Set.mem_univ _)
  refine ⟨h', ?_⟩
  unfold fnVal
  rw [dif_pos h, dif_pos h']
  have e : (Spec.map (CommRingCat.ofHom θ) ≫ p).appLE U ⊤ h' =
      p.appLE U ⊤ h ≫ (Spec.map (CommRingCat.ofHom θ)).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  have e2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom θ)
  rw [e]
  exact congrArg (fun k => k.hom ((p.appLE U ⊤ h).hom f)) e2
end GlobalTheory.ChartBaseChange
