-- Prove2me | solution 1 for GlobalTheory.RigidLinearisation.exists_gen_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:32:57.891866+00:00
-- url     : https://prove2.me/submissions/c89a4f39-9ff2-47d9-969b-866d95e34ce9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLinearisation
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_of_gm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory GlobalTheory.RigidLinearisation
namespace GlobalTheory.RigidLinearisation
theorem _root_.solution {Y : Scheme.{0}} (L : LB Y) (τ : Y ⟶ Y) (h : LBIso L (L.pull τ)) :
    ∃ t : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 Y, τ] ![1, -1]), t.IsGen := by
  obtain ⟨w, hw⟩ := h
  have hp := (isGen_iff w).1 hw
  have le : ∀ j : Fin 2 → L.ι, LB.wchart L (K := Fin 2) ![𝟙 Y, τ] j ≤ (L.pull τ).U (fun _ => j 1) ⊓ L.U (j 0) :=
    fun j y hy => ⟨mem_pull.2 (Set.mem_iInter.1 hy 1), Set.mem_iInter.1 hy 0⟩
  refine ⟨⟨fun j => (res (le j) (w.s (fun _ => j 1, j 0)))⁻¹⟩, isGen_of_gm _ fun y j j' hj hj' => ?_⟩
  have v : ∀ j : Fin 2 → L.ι, y ∈ LB.wchart L (K := Fin 2) ![𝟙 Y, τ] j →
      gm (𝟙 Y) y (LB.wchart L (K := Fin 2) ![𝟙 Y, τ] j) (res (le j) (w.s (fun _ => j 1, j 0)))⁻¹ =
        (gw w (𝟙 Y) y (j 1) (j 0))⁻¹ := fun j hj =>
    (map_inv _ _).trans (congrArg (·⁻¹) (gm_res (𝟙 Y) y (le j) hj _))
  refine (v j hj).trans (Eq.trans ?_ (congrArg (_ * ·) (v j' hj')).symm)
  rw [hp Y (𝟙 Y) y (j 1) (j' 1) (j 0) (j' 0) (Set.mem_iInter.1 hj 1) (Set.mem_iInter.1 hj' 1)
    (Set.mem_iInter.1 hj 0) (Set.mem_iInter.1 hj' 0), trF, Fin.prod_univ_two]
  show _ = gm (𝟙 Y ≫ 𝟙 Y) y _ (L.g (j 0) (j' 0)) ^ (1 : ℤ) * gm (𝟙 Y ≫ τ) y _ (L.g (j 1) (j' 1)) ^ (-1 : ℤ) * _
  rw [Category.id_comp (𝟙 Y), zpow_one, zpow_neg_one, mul_inv, mul_inv, inv_inv, mul_comm (_⁻¹) (gm (𝟙 Y) y _ _)]
end GlobalTheory.RigidLinearisation
