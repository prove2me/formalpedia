-- Prove2me | solution 1 for GlobalTheory.BiextSym.exists_gen_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:05:27.400894+00:00
-- url     : https://prove2.me/submissions/be6c74e1-ca96-4aff-a97d-a9ce7b88c529

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_GenericFiberCubeInclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_BiextensionSecondLawProduct
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.BiextSym
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.BiextSym
theorem _root_.solution {X : Scheme.{0}} {L : LB X} {F : X ⟶ X} (h : LBIso L (L.pull F)) :
    ∃ s : LB.Gen (LB.LinComb L (K := Fin 2) ![F, 𝟙 X] ![1, -1]), s.IsGen := by
  obtain ⟨w, hw⟩ := h
  have hp := (isGen_iff w).1 hw
  have le : ∀ j : Fin 2 → L.ι, LB.wchart L (K := Fin 2) ![F, 𝟙 X] j ≤ (L.pull F).U (fun _ => j 0) ⊓ L.U (j 1) :=
    fun j x hx => ⟨mem_pull.2 (Set.mem_iInter.1 hx 0), Set.mem_iInter.1 hx 1⟩
  refine ⟨⟨fun j => res (le j) (w.s (fun _ => j 0, j 1))⟩, fun j j' => unit_ext fun y hy => ?_⟩
  have a := hp _ (𝟙 X) y (j 0) (j' 0) (j 1) (j' 1) (mem_pull.1 (le j hy.1).1) (mem_pull.1 (le j' hy.2).1)
    (le j hy.1).2 (le j' hy.2).2
  refine ((gm_res _ y _ hy _).trans (gm_res (𝟙 X) y (le j) hy.1 _)).trans (a.trans (Eq.symm ?_))
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_linComb L _ _ (𝟙 X) y j j' hy.1 hy.2).trans ?_)
    ((gm_res _ y _ hy _).trans (gm_res (𝟙 X) y (le j') hy.2 _)))
  rw [Fin.prod_univ_two]
  show gm (𝟙 X ≫ F) y _ (L.g (j 0) (j' 0)) ^ (1 : ℤ) * gm (𝟙 X ≫ 𝟙 X) y _ (L.g (j 1) (j' 1)) ^ (-1 : ℤ) = _
  rw [_root_.zpow_neg, _root_.zpow_one, _root_.zpow_one, Category.id_comp (𝟙 X)]
end GlobalTheory.BiextSym
