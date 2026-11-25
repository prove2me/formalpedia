-- Prove2me | solution 1 for GlobalTheory.TripleMap.pmaps_cubical
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:08:01.82552+00:00
-- url     : https://prove2.me/submissions/979a4821-4341-4c3f-8bb4-b7e04b5eb563

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOneOfAppLESectionEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothGeometricallyIntegralAbLocusTensorObj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIntegralOfSmoothFieldOfConnectedSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_NonemptyCubicalPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSabMapOfLbIso
import Theorems.Thm_GlobalTheory_TripleMap_exists_ratio
import Theorems.Thm_GlobalTheory_DegPull_exists_pmaps
import Theorems.Thm_GlobalTheory_DegPull_pmaps_val
import Theorems.Thm_GlobalTheory_restrictPoints_val
import Theorems.Thm_P2M_GlobalTheory_DegPull_exists_good__8835be56d0ec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
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
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory
open GlobalTheory.TripleMap
namespace GlobalTheory.TripleMap
theorem _root_.solution {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {f : S' ⟶ S} {F : G'.left ⟶ G.left} (gp : IsGrpPullback G' G f F) {L : RigLB G}
    {L' : RigLB G'} (c : CubicalStr G L) (c' : CubicalStr G' L') {w : LB.Iso L'.L (L.L.pull F)} (hw : PGen w)
    (rigid : ∀ a : Γ((G3 G').left, ⊤)ˣ,
      (∀ y, gm (lift (1 : 𝟙_ (Over S') ⟶ G') (lift (1 : 𝟙_ (Over S') ⟶ G') (1 : 𝟙_ (Over S') ⟶ G'))).left y ⊤ a = 1) →
        a = 1) :
    PMaps w (thφ G' (x3 G')) (thφ G (x3 G)) thε c'.t c.t (cubeMapOf gp).F3 := by
  have hψ : ∀ I : thK, thφ G' (x3 G') I ≫ F = (cubeMapOf gp).F3 ≫ thφ G (x3 G) I :=
    fun I => (cubeMapOf gp).psum_comm I.down
  obtain ⟨t, ht, H⟩ := DegPull.exists_pmaps hw L.isLB L'.isLB (ε := thε) (cubeMapOf gp).F3 hψ c.t c.isGen
  obtain ⟨a, ha⟩ := exists_ratio L'.isLB ht c'.isGen
  have a1 : a = 1 := rigid a fun y => by
    obtain ⟨J, hJ⟩ := DegPull.exists_good' L.isLB y
    obtain ⟨J', hJ'⟩ := DegPull.exists_good' L'.isLB y
    let o : 𝟙_ (Over S') ⟶ G' := 1
    have e := DegPull.pmaps_val hψ H (lift o (lift o o)).left y hJ hJ'
    have q : (lift o (lift o o)).left ≫ (cubeMapOf gp).F3 =
        (lift (pushHom gp _ o) (lift (pushHom gp _ o) (pushHom gp _ o))).left := hom_ext_triple _ fun i => by
      rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
      fin_cases i <;> simp [x3] <;> rfl
    rw [q] at e
    have e₁ : cubV c y J (pushHom gp _ o) (pushHom gp _ o) (pushHom gp _ o) = 1 := by
      rw [map_one]
      exact (isCub_cubV c (T := Over.mk ((𝟙_ (Over S')).hom ≫ f)) hJ).face _ _
    have e₂ := prod_cub o o o (fun q => gw w q y (J (q ≫ F)) (J' q))
    have e₃ : cubV c' y J' o o o = 1 := (isCub_cubV c' hJ').face _ _
    have e₄ := ha _ (lift o (lift o o)).left y _ (hJ'.mem (thφ G' (x3 G')) _)
    have e₅ := e₁.symm.trans (e.trans (congrArg₂ (· * ·) e₂ (e₄.trans (congrArg _ e₃))))
    simp only [o, _root_.mul_one, mul_inv_cancel, inv_mul_cancel_right, mul_inv_cancel_right, _root_.one_mul, inv_mul_cancel] at e₅
    exact e₅.symm
  intro Z r z p q hp hq
  rw [H Z r z p q hp hq, ha Z r z q (Set.mem_iInter.2 hq), a1, map_one, _root_.one_mul]
end GlobalTheory.TripleMap
