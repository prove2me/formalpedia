-- Prove2me | solution 1 for GlobalTheory.LocTriv.comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:47:42.065417+00:00
-- url     : https://prove2.me/submissions/64a70e7e-73fe-462a-9964-899c2a7ed26d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorusStableAffineOpenFunctionsWeightGradedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_LocallyTrivialTorusQuotientFlatSurjectiveCosets
import Theorems.Thm_GlobalTheory_LocTriv_hom_ext_appLE
import Theorems.Thm_GlobalTheory_LocTriv_stable
import Theorems.Thm_GlobalTheory_LocTriv_appLE_app
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one


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
open GlobalTheory GlobalTheory.LocTriv
variable {S : Scheme.{0}}
variable {X : Type} [AddCommGroup X] {G B : Over S} [GrpObj G] {i : splitTorus S X ⟶ G} {q : G ⟶ B}
variable [IsMonHom i] [IsAffineHom q.left] {V : B.left.Opens} (hV : IsAffineOpen V)
  (h₀ : ∀ a : Γ(G.left, q.left ⁻¹ᵁ V), IsWt i _ a 0 ↔ ∃ c, (q.left.app V).hom c = a)
  (hU : (snd (splitTorus _ X) G).left ⁻¹ᵁ (q.left ⁻¹ᵁ V) ≤
    ((fst (splitTorus _ X) G ≫ i) * snd _ G).left ⁻¹ᵁ (q.left ⁻¹ᵁ V))
  (u : Multiplicative X →* Γ(G.left, q.left ⁻¹ᵁ V)ˣ) (hu : ∀ χ, IsWt i _ (u (Multiplicative.ofAdd χ)).val χ)
include hV h₀ hU
omit [IsMonHom i] [IsAffineHom q.left]
namespace GlobalTheory.LocTriv
theorem _root_.solution {Z : Over S} (t : Z ⟶ splitTorus S X) {g : Z ⟶ G} (hg : ⊤ ≤ g.left ⁻¹ᵁ (q.left ⁻¹ᵁ V)) :
    g ≫ q = ((t ≫ i) * g) ≫ q :=  by
  have h₁ := stable hU t hg
  apply Over.OverMorphism.ext
  refine hom_ext_appLE hV hg h₁ ?_
  have e1 := appLE_app (q := q) g hg
  have e2 := appLE_app (q := q) ((t ≫ i) * g) h₁
  rw [← e1, ← e2]
  apply CommRingCat.hom_ext
  ext c
  simp only [CommRingCat.hom_comp, RingHom.comp_apply]
  rw [(h₀ _).2 ⟨c, rfl⟩ Z t g h₁ hg, ← chV_val, chV_zero, Units.val_one, _root_.one_mul]
end GlobalTheory.LocTriv
