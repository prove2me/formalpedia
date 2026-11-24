-- Prove2me | solution 1 for GlobalTheory.exists_sec_smul_sub_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:46:59.508238+00:00
-- url     : https://prove2.me/submissions/4dff103f-5021-4399-8553-ec90355fc125

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecRelationDefect

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s t : LB.Sec (LB.LinComb L φ ε)) (c' c : Γ(Y, ⊤)) : ∃ d : LB.Sec (LB.LinComb L φ ε),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
        sval d r z J = gs r z ⊤ c' * sval s r z J - gs r z ⊤ c * sval t r z J := by
  have gsub : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (_ : r z ∈ U) (a b : Γ(Y, U)),
      gs r z U (a - b) = gs r z U a - gs r z U b := fun Z r z U h a b => by
    simp only [gs_eq r z U h, map_sub]
  have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : K → L.ι), r z ∈ LB.wchart L φ j →
      gs r z (LB.wchart L φ j)
        ((Y.presheaf.map (homOfLE (le_top : LB.wchart L φ j ≤ ⊤)).op).hom c' * (show Γ(Y, LB.wchart L φ j) from s.f j) -
          (Y.presheaf.map (homOfLE (le_top : LB.wchart L φ j ≤ ⊤)).op).hom c * (show Γ(Y, LB.wchart L φ j) from t.f j)) =
      gs r z ⊤ c' * gs r z (LB.wchart L φ j) (s.f j) - gs r z ⊤ c * gs r z (LB.wchart L φ j) (t.f j) :=
    fun Z r z j hj => (gsub Z r z _ hj _ _).trans (congrArg₂ (· - ·)
      ((gs_mul r z _ hj _ _).trans (congrArg (· * _) (gs_res r z _ hj _)))
      ((gs_mul r z _ hj _ _).trans (congrArg (· * _) (gs_res r z _ hj _))))
  refine ⟨⟨fun j => (Y.presheaf.map (homOfLE (le_top : LB.wchart L φ j ≤ ⊤)).op).hom c' * (show Γ(Y, LB.wchart L φ j) from s.f j) -
          (Y.presheaf.map (homOfLE (le_top : LB.wchart L φ j ≤ ⊤)).op).hom c * (show Γ(Y, LB.wchart L φ j) from t.f j),
      fun (j j' : K → L.ι) => fn_ext fun y hy => ?_⟩, fun Z r z J hJ => v Z r z _ (hJ.mem φ r)⟩
  refine ((gs_res (𝟙 Y) y _ hy _).trans (v _ _ y j hy.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans
    (congrArg₂ (· * ·) ((gs_unit (𝟙 Y) y _ hy _).trans
      (congrArg Units.val (gm_linComb L _ _ (𝟙 Y) y j j' hy.1 hy.2)))
      ((gs_res (𝟙 Y) y _ hy _).trans (v _ _ y j' hy.2)))).symm)
  rw [sec_trans s (𝟙 Y) y hy.1 hy.2, sec_trans t (𝟙 Y) y hy.1 hy.2]
  simp only [trF]
  ring
end GlobalTheory
