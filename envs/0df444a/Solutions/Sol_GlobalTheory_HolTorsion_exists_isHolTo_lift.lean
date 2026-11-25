-- Prove2me | solution 1 for GlobalTheory.HolTorsion.exists_isHolTo_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:14:03.940421+00:00
-- url     : https://prove2.me/submissions/6fcdddcb-4000-4fc8-826c-2f5e9db30b22

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TorsionEqAndWeilIsOfIsHolTo
import Theorems.Thm_GlobalTheory_HolTorsion_isHolTo_congr
import Theorems.Thm_GlobalTheory_HolTorsion_isHolTo_of_isPullback

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
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.HolTorsion
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {B : Set E}
namespace GlobalTheory.HolTorsion
theorem _root_.solution {S X Y Z : Scheme.{0}} {p : Z ⟶ X} {q : Z ⟶ Y} {s : X ⟶ S} {t : Y ⟶ S}
    (H : IsPullback p q s t) {a : E → (Sp ℂ ⟶ X)} {a' : E → (Sp ℂ ⟶ Y)} (ha : IsHolTo B a) (ha' : IsHolTo B a')
    (h : ∀ w ∈ B, a w ≫ s = a' w ≫ t) {b₀ : E} (hb₀ : b₀ ∈ B) :
    ∃ c : E → (Sp ℂ ⟶ Z), IsHolTo B c ∧ ∀ w ∈ B, c w ≫ p = a w ∧ c w ≫ q = a' w := by
  classical
  let c : E → (Sp ℂ ⟶ Z) := fun w =>
    if hw : w ∈ B then H.lift (a w) (a' w) (h w hw) else H.lift (a b₀) (a' b₀) (h b₀ hb₀)
  have hc : ∀ w ∈ B, c w ≫ p = a w ∧ c w ≫ q = a' w := fun w hw => by
    simp only [c, dif_pos hw, IsPullback.lift_fst, IsPullback.lift_snd, and_self]
  exact ⟨c, isHolTo_of_isPullback H (isHolTo_congr ha fun w hw => (hc w hw).1)
    (isHolTo_congr ha' fun w hw => (hc w hw).2), hc⟩
end GlobalTheory.HolTorsion
