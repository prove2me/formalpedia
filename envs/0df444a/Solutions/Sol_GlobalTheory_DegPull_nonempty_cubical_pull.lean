-- Prove2me | solution 1 for GlobalTheory.DegPull.nonempty_cubical_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:30:27.098342+00:00
-- url     : https://prove2.me/submissions/d3e06994-fe14-40ae-8778-c6c41d80f3f3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_NonemptyCubicalPull
import Theorems.Thm_GlobalTheory_DegPull_exists_pmaps
import Theorems.Thm_GlobalTheory_DegPull_pmaps_val
import Theorems.Thm_P2M_GlobalTheory_DegPull_exists_good__8835be56d0ec
import Theorems.Thm_GlobalTheory_DegPull_isCub_of_rel
import Theorems.Thm_GlobalTheory_DegPull_nonempty_cubical
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_cubeMap_comp_proj_three
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_hom_ext_triple
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isCub_cubV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_cub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.DegPull
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]
variable {S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] [IsCommMonObj G'] {f : S' ⟶ S} {F : G'.left ⟶ G.left}
namespace GlobalTheory.DegPull
theorem _root_.solution (gp : IsGrpPullback G' G f F) {L : RigLB G} (c : CubicalStr G L) (L' : RigLB G')
    {w : LB.Iso L'.L (L.L.pull F)} (hw : PGen w) : Nonempty (CubicalStr G' L') := by
  have hψ : ∀ I : thK, thφ G' (x3 G') I ≫ F = (cubeMapOf gp).F3 ≫ thφ G (x3 G) I :=
    fun I => (cubeMapOf gp).psum_comm I.down
  obtain ⟨t, ht, H⟩ := exists_pmaps hw L.isLB L'.isLB (ε := thε) (cubeMapOf gp).F3 hψ c.t c.isGen
  refine nonempty_cubical L' t ht fun T z J' hJ' => ?_
  obtain ⟨J, hJ⟩ := exists_good' L.isLB z
  refine isCub_of_rel (isCub_cubV c (T := Over.mk (T.hom ≫ f)) hJ) (pushHom gp T)
    (fun x => gw w x.left z (J (x.left ≫ F)) (J' x.left)) _ fun a b c' => ?_
  have e := pmaps_val hψ H (lift a (lift b c')).left z hJ hJ'
  have q : (lift a (lift b c')).left ≫ (cubeMapOf gp).F3 =
      (lift (pushHom gp T a) (lift (pushHom gp T b) (pushHom gp T c'))).left := hom_ext_triple _ fun i => by
    rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
    fin_cases i <;> simp [x3] <;> rfl
  rw [q] at e
  exact e.trans (congrArg₂ (· * ·) (prod_cub a b c' (fun q => gw w q z (J (q ≫ F)) (J' q))) rfl)
end GlobalTheory.DegPull
