-- Prove2me | solution 1 for GlobalTheory.HolTorsion.comp_eq_of_unramified
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:55:08.967856+00:00
-- url     : https://prove2.me/submissions/73ee297f-009a-49f4-8c00-fa5a44bb3c80

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TorsionEqAndWeilIsOfIsHolTo
import Theorems.Thm_GlobalTheory_HolTorsion_mem_of_isClosed

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
theorem _root_.solution {N X : Scheme.{0}} (q : N ⟶ X) [FormallyUnramified q] [LocallyOfFiniteType q]
    [IsSeparated q] {c : E → (Sp ℂ ⟶ pullback q q)} (hc : IsHolTo B c) (hB : IsPreconnected B) {b₀ b : E}
    (hb₀ : b₀ ∈ B) (hb : b ∈ B) (h₀ : c b₀ ≫ pullback.fst q q = c b₀ ≫ pullback.snd q q) :
    c b ≫ pullback.fst q q = c b ≫ pullback.snd q q := by
  have e₀ : c b₀ = (c b₀ ≫ pullback.fst q q) ≫ pullback.diagonal q := by
    apply pullback.hom_ext
    · simp
    · simp [h₀]
  have hm : c b (default : PrimeSpectrum ℂ) ∈ (pullback.diagonal q).opensRange := by
    refine mem_of_isClosed hc hB _ (pullback.diagonal q).isClosedEmbedding.isClosed_range hb₀ ?_ hb
    rw [e₀]
    exact ⟨_, rfl⟩
  have hr : Set.range (c b) ⊆ Set.range (pullback.diagonal q) := by
    rintro _ ⟨z, rfl⟩
    obtain rfl : z = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    exact hm
  rw [← IsOpenImmersion.lift_fac (pullback.diagonal q) (c b) hr, Category.assoc, Category.assoc,
    pullback.diagonal_fst, pullback.diagonal_snd]
end GlobalTheory.HolTorsion
