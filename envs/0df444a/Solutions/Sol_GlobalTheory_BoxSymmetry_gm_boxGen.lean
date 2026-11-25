-- Prove2me | solution 1 for GlobalTheory.BoxSymmetry.gm_boxGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:35:01.513574+00:00
-- url     : https://prove2.me/submissions/2bbc154b-2616-4e25-bedf-d643b7947781

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_CubePullbacks_SubAddEqZeroOfEqAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_BoxSymIsSymmetry
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.BoxSymmetry
section Generators
variable {X X' Y Z : Scheme.{0}} (L : LB X) {J K : Type} [Fintype J] [Fintype K]
private theorem gm_res_eq_gm {X Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) {U V : X.Opens} (hUV : U ≤ V)
    (hz : r z ∈ U) (x : Γ(X, V)ˣ) : gm r z U (res hUV x) = gm r z V x := by
  have key : X.presheaf.map (homOfLE hUV).op ≫ r.app U ≫ Z.presheaf.germ (r ⁻¹ᵁ U) z hz =
      r.app V ≫ Z.presheaf.germ (r ⁻¹ᵁ V) z (hUV hz) := by
    rw [Scheme.Hom.naturality_assoc]
    congr 1
    exact TopCat.Presheaf.germ_res _ _ _ _
  unfold gm res
  rw [dif_pos hz, dif_pos (hUV hz)]
  unfold pullU
  ext
  simp only [MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe]
  have e := congrArg (fun f => CommRingCat.Hom.hom f (x : Γ(X, V))) key
  simpa using e
end Generators
variable {S : Scheme.{0}}
end GlobalTheory.BoxSymmetry
end
end

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.BoxSymmetry
variable {X X' Y Z : Scheme.{0}} (L : LB X) {J K : Type} [Fintype J] [Fintype K]
namespace GlobalTheory.BoxSymmetry
theorem _root_.solution (F : J → (X' ⟶ X)) (φ : K → (Y ⟶ X')) (ε : K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb (L.pull (F i)) φ ε)) (r : Z ⟶ Y) (z : Z)
    (jj : K → (LB.LinComb L F (fun _ => 1)).ι)
    (h : r z ∈ LB.wchart (LB.LinComb L F (fun _ => 1)) φ jj) :
    gm r z (LB.wchart (LB.LinComb L F (fun _ => 1)) φ jj) ((GeneratorPullback.boxGen L F φ ε t).s jj) =
      ∏ i, gm r z (LB.wchart (L.pull (F i)) φ (fun k _ => jj k i)) ((t i).s (fun k _ => jj k i)) := by
  unfold GeneratorPullback.boxGen
  dsimp only
  refine (map_prod (gm r z _) _ _).trans (Finset.prod_congr rfl fun i _ => ?_)
  exact gm_res_eq_gm r z _ h _
end GlobalTheory.BoxSymmetry
