-- Prove2me | solution 1 for GlobalTheory.ChartJLaw.read_pt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:10:41.031805+00:00
-- url     : https://prove2.me/submissions/1b5b5ce9-7326-4b33-83cd-f68dc82c6bcb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsToJetEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsFormalGroupLawOfChartOfJetChart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ChartJLaw
variable {T : Type} [CommRing T] {d : ℕ}
namespace GlobalTheory.ChartJLaw
theorem _root_.solution {G : Over (Sp T)} {A B C D : Type} [CommRing A] [Algebra T A] [CommRing B] [Algebra T B]
    [CommRing C] [Algebra T C] [CommRing D] [Algebra T D] (x : algOver T A ⟶ G) (x0 : Chart.sp (R₀ := T) B ⟶ G)
    (ρ : A →ₐ[T] B) (h : x0.left = spMap (ρ : A →+* B) ≫ x.left) (S : A →ₐ[T] C) (Φ : C →ₐ[T] D) (ψ : B →ₐ[T] D)
    (hψ : ψ.comp ρ = Φ.comp S) :
    (Chart.spMap ψ ≫ x0 : Chart.sp (R₀ := T) D ⟶ G) = algOverHom Φ ≫ algOverHom S ≫ x := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, h, Chart.spMap_left, algOverHom, Over.homMk_left, ← Category.assoc]
  congr 1
  simp only [Geo.Tor.spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact congrArg (fun f : A →ₐ[T] D => (f : A →+* D)) hψ
end GlobalTheory.ChartJLaw
