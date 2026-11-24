-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsPsiCoord.unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:57:23.427678+00:00
-- url     : https://prove2.me/submissions/db7c664c-3a2a-43b2-a13f-1579b83fb851

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_GeneratorValues
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_GeneratorValues_res_res
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_GeneratorValues_pull_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues
variable {R : Type} [CommRing R] [IsDomain R]
namespace GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues
namespace IsPsiCoord
theorem _root_.solution {D : DegPre R} {χ : D.X} {x x' : (FractionRing R)ˣ}
    (hx : IsPsiCoord D χ x) (hx' : IsPsiCoord D χ x') :
    ∃ u : Rˣ, x = Units.map (algebraMap R (FractionRing R)).toMonoidHom u * x' := by
  obtain ⟨j, h, hj, rfl⟩ := hx
  obtain ⟨j', h', hj', rfl⟩ := hx'
  have key := congrArg (res (le_inf h h')) (D.psi_gen χ j j')
  rw [map_mul, res_res, res_res] at key
  have hjj : ⊤ ≤ (D.c χ).left ⁻¹ᵁ (D.P.L.U (j PUnit.unit) ⊓ D.P.L.U (j' PUnit.unit)) :=
    le_inf hj hj'
  have hK : ⊤ ≤ (jK R ≫ (D.c χ).left) ⁻¹ᵁ (D.P.L.U (j PUnit.unit) ⊓ D.P.L.U (j' PUnit.unit)) :=
    fun y _ => hjj (Set.mem_univ (jK R y))
  refine ⟨(Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom
    (res hjj (pullU (D.c χ).left _ (D.P.L.g _ _))))⁻¹, ?_⟩
  have hg : res (le_inf h h') ((LB.LinComb D.P.L (K := PUnit) (fun _ => ptK (D.c χ))
      (fun _ => -1)).g j j') = (res hK (pullU (jK R ≫ (D.c χ).left) _ (D.P.L.g _ _)))⁻¹ := by
    simp only [LB.LinComb, Finset.univ_unique, Finset.prod_singleton, zpow_neg, zpow_one]
    refine (MonoidHom.map_inv _ _).trans (congrArg Inv.inv ?_)
    exact res_res _ _ _
  unfold genVal
  rw [key, map_mul, hg]
  congr 1
  refine (MonoidHom.map_inv _ _).trans (Eq.trans (congrArg Inv.inv ?_) (MonoidHom.map_inv _ _).symm)
  exact pull_val (CommRingCat.ofHom (algebraMap R (FractionRing R))) (D.c χ).left _ _ hjj hK
end IsPsiCoord
end GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues
