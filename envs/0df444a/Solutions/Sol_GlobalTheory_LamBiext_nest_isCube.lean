-- Prove2me | solution 1 for GlobalTheory.LamBiext.nest_isCube
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:35:24.126461+00:00
-- url     : https://prove2.me/submissions/5eadf607-0c71-403e-8103-13ea41e3072c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_AbelianLawCounterexamples_MulGenNegRight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsLaws
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
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]
namespace GlobalTheory.LamBiext
theorem _root_.solution (L : RigLB G) (c : CubicalStr G L) (ψ : ULift.{0} (Fin 3) → ((G3 G).left ⟶ (G2 G).left))
    (t : LB.Gen (LB.LinComb L.L (flatφ (lamφ G) ψ) (flatε lamε lawε)))
    (v : LB.Gen.Corr L.L _ _ (thφ G (x3 G)) thε t c.t) :
    GlobalTheory.BiextSignTwist.LawIsCube G L c ψ (nest L.L (lamφ G) lamε ψ lawε t) := fun J j h₁ h₂ h₃ =>
  unit_ext fun y hy => by
    have e := v (fun p => J p.1 p.2) j (fun a b q => h₁ _ _ _ _ q) h₂ (fun a b q => h₃ _ _ _ q)
    have hm := nest_le L.L (lamφ G) lamε ψ J hy.1
    have hy' : (𝟙 _ : (G3 G).left ⟶ _) y ∈ LB.wchart L.L (flatφ (lamφ G) ψ) (fun p => J p.1 p.2) ⊓
        LB.wchart L.L (thφ G (x3 G)) j := ⟨hm, hy.2⟩
    refine (gm_res _ y _ hy _).trans ((gm_res _ y _ hy.1 _).trans ?_)
    refine Eq.trans ?_ (gm_res _ y _ hy _).symm
    exact (gm_res _ y _ hy' _).symm.trans ((congrArg (gm _ y _) e).trans (gm_res _ y _ hy' _))
end GlobalTheory.LamBiext
