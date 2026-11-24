-- Prove2me | solution 1 for GlobalTheory.LamBiext.nest_isGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:36:22.916525+00:00
-- url     : https://prove2.me/submissions/973be217-3464-4ac6-825e-918482896a05

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_AbelianLawCounterexamples_MulGenNegRight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsLaws
import Theorems.Thm_GlobalTheory_LamBiext_trF_flat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LamBiext
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
variable {X W Y Z : Scheme.{0}} (L : LB X) {I K : Type} [Fintype I] [Fintype K]
  (φ : I → (W ⟶ X)) (δ : I → ℤ) (ψ : K → (Y ⟶ W)) (ε : K → ℤ)
variable {L φ δ ψ ε}
namespace GlobalTheory.LamBiext
theorem _root_.solution {t : LB.Gen (LB.LinComb L (flatφ φ ψ) (flatε δ ε))} (ht : t.IsGen) :
    (nest L φ δ ψ ε t).IsGen := fun j j' => unit_ext fun y hy => by
  have hj : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart (LB.LinComb L φ δ) ψ j := hy.1
  have hj' : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart (LB.LinComb L φ δ) ψ j' := hy.2
  refine (gm_res _ y _ hy _).trans ((gm_res _ y _ hj _).trans ?_)
  refine (gen_trans ht (𝟙 Y) y (nest_le L φ δ ψ j hj) (nest_le L φ δ ψ j' hj')).trans ?_
  refine Eq.trans ?_ (map_mul _ _ _).symm
  refine congrArg₂ (· * ·) ?_ ((gm_res _ y _ hj' _).symm.trans (gm_res _ y _ hy _).symm)
  refine (trF_flat L φ δ ψ ε (𝟙 Y) y j j').trans (Eq.symm ?_)
  refine (gm_linComb _ ψ ε (𝟙 Y) y j j' hj hj').trans (Finset.prod_congr rfl fun k _ => ?_)
  exact congrArg (· ^ ε k) (gm_linComb L φ δ (𝟙 Y ≫ ψ k) y (j k) (j' k) (Set.mem_iInter.1 hj k)
    (Set.mem_iInter.1 hj' k))
end GlobalTheory.LamBiext
