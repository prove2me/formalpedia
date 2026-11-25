-- Prove2me | solution 1 for GlobalTheory.CoverO.restrict_pull1_bijective_of_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:26:38.912805+00:00
-- url     : https://prove2.me/submissions/ca1d4f4a-2ca6-4fa5-86bb-5d16ec4732ce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechPullOneBijectiveLatticeCover
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyOne_comp
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyOne_eq_of_natTrans
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyOne_id
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp
import Theorems.Thm_GlobalTheory_Cris_IsMor_pullCohomologyOne_id


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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CoverO
namespace GlobalTheory.CoverO
theorem _root_.solution {R : Type} [CommRing R] {C C' : Type} [Category.{0} C]
    [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) (H : C ⥤ C') (adj : G ⊣ H) :
    Function.Bijective (CoefMap.restrict F G).pull1 := by
  have hl : ∀ c, (counitCoef F adj).pull1 ((CoefMap.restrict F G).pull1 c) = c := by
    intro c
    rw [← CoefMap.pullCohomologyOne_comp]
    exact (CoefMap.pullCohomologyOne_eq_of_natTrans _ (CoefMap.id F) adj.counit (fun T b ↦ rfl) c).trans
      (CoefMap.pullCohomologyOne_id c)
  have hr : ∀ c, (CoefMap.restrict F G).pull1 ((counitCoef F adj).pull1 c) = c := by
    intro c
    rw [← CoefMap.pullCohomologyOne_comp]
    refine ((CoefMap.pullCohomologyOne_eq_of_natTrans (CoefMap.id (G ⋙ F))
      ((counitCoef F adj).comp (CoefMap.restrict F G)) adj.unit (fun T b ↦ ?_) c).symm.trans
      (CoefMap.pullCohomologyOne_id c))
    change mp F (adj.counit.app (G.obj T)) (mp F (G.map (adj.unit.app T)) b) = b
    exact (mp_comp F (G.map (adj.unit.app T)) (adj.counit.app (G.obj T)) b).symm.trans
      ((congrArg (fun ξ ↦ mp F ξ b) (adj.left_triangle_components T)).trans (mp_id F (G.obj T) b))
  exact ⟨Function.LeftInverse.injective hl, Function.RightInverse.surjective hr⟩
end GlobalTheory.CoverO
