-- Prove2me | solution 1 for GlobalTheory.Cartier.SecMaps.ratSecs_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:16:43.976712+00:00
-- url     : https://prove2.me/submissions/986c51f8-0209-43a0-8d85-ea663dc599ae

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Theorems.Thm_GlobalTheory_Cartier_mem_ratSecs_iff_stalk
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_mem_of_cover


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
open GlobalTheory GlobalTheory.Cartier
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X Y Z : Scheme.{0}}
variable [IsIntegral X]
namespace GlobalTheory.Cartier
namespace SecMaps
theorem _root_.solution {A B : LB X} (hA : A.IsLB) (hB : B.IsLB) {w : LB.Iso A B} {a : A.Sec}
    {b : B.Sec} (hw : SecMaps w a b) (V : X.Opens) [Nonempty V] : ratSecs a V = ratSecs b V := by
  have key : ∀ (p : B.ι) (q : A.ι) (x : X) (hp : x ∈ B.U p) (hq : x ∈ A.U q),
      Associated ((X.presheaf.germ _ x hq).hom (a.f q)) ((X.presheaf.germ _ x hp).hom (b.f p)) := by
    intro p q x hp hq
    have hm : x ∈ B.U p ⊓ A.U q := ⟨hp, hq⟩
    have e := congrArg (X.presheaf.germ (B.U p ⊓ A.U q) x hm).hom (hw (p, q))
    rw [map_mul, germ_resG, germ_resG] at e
    exact (congrArg (Associated _) e).mpr
      (associated_unit_mul_right _ _ ((Units.isUnit _).map _))
  have mv : ∀ (x : X) (r r' : X.presheaf.stalk x) (h : X.functionField), r ∣ r' →
      algebraMap _ X.functionField r * h ∈ Set.range (algebraMap (X.presheaf.stalk x) _) →
      algebraMap _ X.functionField r' * h ∈ Set.range (algebraMap (X.presheaf.stalk x) _) := by
    rintro x r _ h ⟨c, rfl⟩ ⟨d, hd⟩
    exact ⟨c * d, by rw [map_mul, map_mul, hd]; ring⟩
  ext h
  rw [mem_ratSecs_iff_stalk, mem_ratSecs_iff_stalk]
  constructor
  · intro H p x hV hp
    obtain ⟨q, hq⟩ := LB.mem_of_cover hA x
    exact mv x _ _ h (key p q x hp hq).dvd (H q x hV hq)
  · intro H q x hV hq
    obtain ⟨p, hp⟩ := LB.mem_of_cover hB x
    exact mv x _ _ h (key p q x hp hq).symm.dvd (H p x hV hp)
end SecMaps
end GlobalTheory.Cartier
