-- Prove2me | solution 1 for GlobalTheory.EvenPull.sym_pmaps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:59:58.874461+00:00
-- url     : https://prove2.me/submissions/fa446683-2b12-4aca-af61-f5ea0eac046c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PulledComparisonEven
import Theorems.Thm_GlobalTheory_EvenPull_pmaps_of_section
import Theorems.Thm_GlobalTheory_EvenPull_inv_hom_fst
import Theorems.Thm_GlobalTheory_EvenPull_eSec_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.EvenPull
namespace GlobalTheory.EvenPull
theorem _root_.solution (hG : GlobalFnsSt) {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
    {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D') :
    PMaps hD.w (K := Fin 2) ![(ι[D'.P.A]).left, 𝟙 D'.P.A.left] ![(ι[D.P.A]).left, 𝟙 D.P.A.left] ![1, -1]
      D'.sym D.sym (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) := by
  have := hD.e_hom
  refine pmaps_of_section ((isGen_iff _).1 hD.w_gen) D.P.isLB D'.P.isLB _ (fun k => ?_) _ D'.sym_gen _ D.sym_gen
    D'.P.A.hom (eSec D'.P.A) (Over.w η[D'.P.A]) (hG _ _ D'.P.isAb).2 (fun y J J' hJ hJ' => ?_)
  · fin_cases k
    · exact inv_hom_fst _ _ hD.e.hom
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
  · have a₁ := val_corr hJ D.sym_rig (specOf φ)
    have a₂ := val_corr hJ' D'.sym_rig (𝟙 _)
    rw [val_pull hJ, val_one] at a₁
    rw [val_pull hJ', val_one, Category.id_comp] at a₂
    rw [hD.he, a₂, Fin.prod_univ_two]
    refine a₁.trans ?_
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, eSec_inv, Category.comp_id]
    simp
end GlobalTheory.EvenPull
