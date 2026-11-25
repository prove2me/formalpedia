-- Prove2me | solution 1 for GlobalTheory.UU.pullIso_isGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:50:10.690825+00:00
-- url     : https://prove2.me/submissions/1805af4f-19c4-429a-997a-8d34878341e1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubicalSymmetryTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_WeilIsGrpPullbackIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_comm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_cocycle
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.UU
variable {S S' : Scheme.{0}}
attribute [instance] TQ.grp TQ.comm
variable {S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [IsCommMonObj G] [GrpObj G']
  [IsCommMonObj G'] [GrpObj G''] [IsCommMonObj G'']
  {f : S' ⟶ S} {F : G'.left ⟶ G.left} {hw : F ≫ G.hom = G'.hom ≫ f}
namespace GlobalTheory.UU
theorem _root_.solution {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (F : Y ⟶ X) : (pullIso L F).IsGen := by
  rw [isGen_iff]
  intro Y f y j j' k k' hj hj' hk hk'
  have hk1 : F (f y) ∈ L.U (k PUnit.unit) := mem_pull.1 hk
  have hk1' : F (f y) ∈ L.U (k' PUnit.unit) := mem_pull.1 hk'
  have key : ∀ (a b : PUnit → L.ι), f y ∈ (L.pull F).U a ⊓ (L.pull F).U b →
      gm f y _ ((L.pull F).g a b) =
        gm (f ≫ F) y (L.U (a PUnit.unit) ⊓ L.U (b PUnit.unit)) (L.g (a PUnit.unit) (b PUnit.unit)) := by
    intro a b hab
    have hF : F (f y) ∈ L.U (a PUnit.unit) ⊓ L.U (b PUnit.unit) :=
      TopologicalSpace.Opens.mem_inf.2 ⟨mem_pull.1 (TopologicalSpace.Opens.mem_inf.1 hab).1,
        mem_pull.1 (TopologicalSpace.Opens.mem_inf.1 hab).2⟩
    rw [← gm_pull f F y _ hF]
    unfold LB.pull LB.LinComb
    simp only [Fintype.prod_unique, zpow_one]
    exact gm_res f y _ hab _
  have g1 : gw (pullIso L F) f y j k = gm (f ≫ F) y _ (L.g j (k PUnit.unit)) :=
    key (fun _ => j) k (TopologicalSpace.Opens.mem_inf.2 ⟨mem_pull.2 hj, hk⟩)
  have g2 : gw (pullIso L F) f y j' k' = gm (f ≫ F) y _ (L.g j' (k' PUnit.unit)) :=
    key (fun _ => j') k' (TopologicalSpace.Opens.mem_inf.2 ⟨mem_pull.2 hj', hk'⟩)
  rw [g1, g2, key k k' (TopologicalSpace.Opens.mem_inf.2 ⟨hk, hk'⟩)]
  have c1 := congrArg Additive.ofMul (gm_cocycle hL (f ≫ F) y hj hj' hk1')
  have c2 := congrArg Additive.ofMul (gm_cocycle hL (f ≫ F) y hj hk1 hk1')
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv] at c1 c2 ⊢
  linear_combination (norm := abel) c2 - c1
end GlobalTheory.UU
