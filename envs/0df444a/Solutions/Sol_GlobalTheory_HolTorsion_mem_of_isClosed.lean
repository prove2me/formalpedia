-- Prove2me | solution 1 for GlobalTheory.HolTorsion.mem_of_isClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:37:21.030783+00:00
-- url     : https://prove2.me/submissions/049bccde-a6d1-417e-9019-9d68bb653c86

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TorsionEqAndWeilIsOfIsHolTo
import Theorems.Thm_GlobalTheory_top_le_preimage_iff_mem


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
theorem _root_.solution {Z : Scheme.{0}} {c : E → (Sp ℂ ⟶ Z)} (hc : IsHolTo B c) (hB : IsPreconnected B)
    (U : Z.Opens) (hU : IsClosed (U : Set Z)) {b₀ : E} (hb₀ : b₀ ∈ B) (h₀ : c b₀ (default : PrimeSpectrum ℂ) ∈ U)
    {b : E} (hb : b ∈ B) : c b (default : PrimeSpectrum ℂ) ∈ U := by
  let U' : Z.Opens := ⟨(U : Set Z)ᶜ, hU.isOpen_compl⟩
  have h := hB.subset_left_of_subset_union (hc U 0).1 (hc U' 0).1
    (Set.disjoint_left.2 fun w h₁ h₂ =>
      (top_le_preimage_iff_mem _ _).1 h₂.2 ((top_le_preimage_iff_mem _ _).1 h₁.2))
    (fun w hw => by
      by_cases hm : c w (default : PrimeSpectrum ℂ) ∈ U
      · exact Or.inl ⟨hw, (top_le_preimage_iff_mem _ _).2 hm⟩
      · exact Or.inr ⟨hw, (top_le_preimage_iff_mem _ _).2 hm⟩)
    ⟨b₀, hb₀, hb₀, (top_le_preimage_iff_mem _ _).2 h₀⟩
  exact (top_le_preimage_iff_mem _ _).1 (h hb).2
end GlobalTheory.HolTorsion
