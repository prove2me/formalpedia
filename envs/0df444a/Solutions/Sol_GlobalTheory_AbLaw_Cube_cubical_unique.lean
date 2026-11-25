-- Prove2me | solution 1 for GlobalTheory.AbLaw.Cube.cubical_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:41:25.047799+00:00
-- url     : https://prove2.me/submissions/2f2b696f-f9e5-409a-bd65-6993e3a058c8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubicalOfNormalised
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isCub_cubV


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.Cube
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}} {A : Over S} [GrpObj A]
variable [IsCommMonObj A] {L : LB A.left}
namespace GlobalTheory.AbLaw.Cube
theorem _root_.solution (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {M : RigLB A} (c c' : CubicalStr A M) :
    LB.Gen.Corr M.L _ _ _ _ c.t c'.t :=
  corr_of_val_section M.isLB (surj_tensor hG hA (surj_tensor hG hA (hG _ _ hA).2)) (lift 1 (lift 1 1))
    (φ := thφ A (x3 A)) (ε := thε) (φ' := thφ A (x3 A)) (ε' := thε) (fun _ _ _ => rfl) c.isGen c'.isGen
    fun _ _ hJ => ((isCub_cubV c hJ).face 1 1).trans ((isCub_cubV c' hJ).face 1 1).symm
end GlobalTheory.AbLaw.Cube
