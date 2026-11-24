-- Prove2me | solution 1 for GlobalTheory.existsUnique_character_of_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:36:56.010628+00:00
-- url     : https://prove2.me/submissions/810dfe46-dbc2-47c5-8dc3-474d2c72796f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_TorusInj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueCharacterOfMul
import Theorems.Thm_GlobalTheory_TorusUnit_eq_of_single_one_eq
import Theorems.Thm_GlobalTheory_TorusUnit_expand_char
import Theorems.Thm_GlobalTheory_TorusUnit_ext_of_expand
import Theorems.Thm_GlobalTheory_TorusUnit_IsCharNear_residueField
import Theorems.Thm_GlobalTheory_TorusUnit_IsCharNear_unique
import Theorems.Thm_GlobalTheory_TorusUnit_IsMulLeft_exists_isCharNear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj TensorProduct AlgebraMonoidAlgebra
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open TorusUnit
namespace GlobalTheory
theorem _root_.solution (S : Scheme.{0}) (X : Type) [AddCommGroup X] (Y : Over S)
    [ConnectedSpace Y.left] (ρ : Γ((splitTorus S X ⊗ Y).left, ⊤)ˣ)
    (hρ : ∀ (Z : Over S) (t t' : Z ⟶ splitTorus S X) (y : Z ⟶ Y),
      (lift (t * t') y).left.appTop.hom ρ.val =
        (lift t y).left.appTop.hom ρ.val * (lift t' y).left.appTop.hom ρ.val) :
    ∃! χ : X, ρ.val = (fst (splitTorus S X) Y).left.appTop.hom (charUnit S X χ).val := by
  choose c hc using IsMulLeft.exists_isCharNear (ρ := ρ.val) hρ ρ.isUnit
  have hlc : IsLocallyConstant c := by
    rw [IsLocallyConstant.iff_exists_open]
    intro p
    obtain ⟨R, y, hy, hp, he⟩ := hc p
    exact ⟨Set.range y, y.isOpenEmbedding.isOpen_range, hp,
      fun p' hp' => (hc p').unique ⟨R, y, hy, hp', he⟩⟩
  obtain ⟨p₀⟩ : Nonempty Y.left := inferInstance
  refine ⟨c p₀, ext_of_expand fun p => ?_, fun χ hχ => ?_⟩
  · obtain ⟨R, y, hy, hp, he⟩ := hc p
    refine ⟨R, y, hy, hp, ?_⟩
    rw [he, expand_char, hlc.apply_eq_of_preconnectedSpace p p₀]
  · have := (hc p₀).residueField
    rw [hχ, expand_char] at this
    exact eq_of_single_one_eq this
end GlobalTheory
