-- Prove2me | solution 1 for GlobalTheory.RatLift.exists_point_over
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:11:35.882918+00:00
-- url     : https://prove2.me/submissions/88b20db2-3626-40a7-8aa7-4e8c23f9ebfa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsLiftOfRetraction
import Theorems.Thm_GlobalTheory_RatLift_exists_lift_of_retraction
import Theorems.Thm_GlobalTheory_RatLift_exists_retraction
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.RatLift
attribute [local instance] SplitExt.free SplitExt.finite
namespace GlobalTheory.RatLift
theorem _root_.solution :
    ∀ (F : Type) [Field F] (E : SplitExt (Spec (CommRingCat.of F))) (G : Over (Spec (CommRingCat.of F))) [GrpObj G] (Dat : E.GtDatum G) (b : 𝟙_ (Over (Spec (CommRingCat.of F))) ⟶ E.B), ∃ x : 𝟙_ (Over (Spec (CommRingCat.of F))) ⟶ G, x ≫ Dat.q = b := by
  intro F _ E G _ Dat b
  let b' : Spec (CommRingCat.of F) ⟶ E.B.left := b.left
  let p : Spec (CommRingCat.of F) := default
  choose j hj using fun k => exists_chart (E.O (E.basis k)).isLB (b' p)
  have hp : b' p ∈ E.chart j := by
    have : ((E.chart j : E.B.left.Opens) : Set E.B.left) =
      ⋂ k, ((E.O (E.basis k)).L.U (j k) : Set E.B.left) := TopologicalSpace.Opens.coe_iInf _
    exact this.ge (Set.mem_iInter.2 hj)
  obtain ⟨_, ⟨V, hV, rfl⟩, hpV, hVj⟩ :=
    E.B.left.isBasis_affineOpens.exists_subset_of_mem_open hp (E.chart j).2
  obtain ⟨r, hr⟩ := exists_retraction _ _ (Dat.coord j V hV hVj)
  have := Dat.q_affine
  obtain ⟨x, hx⟩ := exists_lift_of_retraction Dat.q.left hV (CommRingCat.ofHom r) (CommRingCat.hom_ext hr) b'
    (fun y _ => by
      obtain rfl : y = p := Subsingleton.elim _ _
      exact hpV)
  refine ⟨Over.homMk x ?_, Over.OverMorphism.ext hx⟩
  rw [← Over.w Dat.q, ← Category.assoc, hx]
  exact Over.w b
end GlobalTheory.RatLift
