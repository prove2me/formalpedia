-- Prove2me | solution 1 for GlobalTheory.CubeLift.eq_one_of_dif
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:28:20.892656+00:00
-- url     : https://prove2.me/submissions/7f1c5973-4133-43c0-bcd7-ffd20ad0eb9a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsNilpotentOfRd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_EvSurjective
import Theorems.Thm_GlobalTheory_CubeLift_ex_bijective
import Theorems.Thm_GlobalTheory_CubeLift_ex_dif
import Theorems.Thm_GlobalTheory_CubeLift_ex_mem_cong
import Theorems.Thm_GlobalTheory_CubeLift_eq_one_of_del


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.CubeLift
open SplitTorus (ev univPt ptOf pull bcMap ofVal valHom)
open ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht (chi torusFst)
variable {A : Type} [CommRing A] {X Y : Type} [AddCommGroup X] [AddCommGroup Y]
variable {J : Ideal A}
namespace GlobalTheory.CubeLift
theorem _root_.solution (hJ : IsNilpotent J) (g : Γ((splitTorus (Spec (CommRingCat.of A)) X).left, ⊤)ˣ)
    (h : app (bcMap (red J) X) g = 1)
    (hg : ∀ (Z : Over (Spec (CommRingCat.of A))) (x y u : Z ⟶ splitTorus _ X), dif g x y u = 1) : g = 1 := by
  have h1 : ex g ∈ cong J := (ex_mem_cong J g).2 h
  have h2 : del (ex g) p₁ p₂ p₃ = 1 := by
    rw [← ex_dif, hg, map_one]
  apply (ex_bijective (A := A) (X := X)).1
  rw [eq_one_of_del hJ h1 h2, map_one]
end GlobalTheory.CubeLift
