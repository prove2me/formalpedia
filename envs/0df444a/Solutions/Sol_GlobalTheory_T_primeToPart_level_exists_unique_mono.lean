-- Prove2me | solution 1 for GlobalTheory.T.primeToPart_level_exists_unique_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:24:41.32081+00:00
-- url     : https://prove2.me/submissions/7d0430e8-dbff-42e7-b213-114da450de80

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_PrimeToPartLevelExistsUniqueMono
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_AuxiliaryInertOddPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_PrimeToPartLevelExistsUniqueMonoStatement
import Theorems.Thm_GlobalTheory_Models_primeToPart_spec


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
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (p : ℕ), p.Prime → (∀ l : Level H, l.GoodAt p → ∃ l₀ : Level H, IsPrimeToPart l₀ l p) ∧ (∀ l l₀ : Level H, IsPrimeToPart l₀ l p → l₀.Dvd l ∧ l₀.M.Coprime p ∧ ∀ l₀' : Level H, IsPrimeToPart l₀' l p → l₀' = l₀) ∧ ∀ l l' l₀ l₀' : Level H, IsPrimeToPart l₀ l p → IsPrimeToPart l₀' l' p → l.Dvd l' → l₀.Dvd l₀' := by
  first | exact @GlobalTheory.Models.primeToPart_spec | exact GlobalTheory.Models.primeToPart_spec | (intros; apply GlobalTheory.Models.primeToPart_spec <;> assumption)
end _root_.GlobalTheory.T
