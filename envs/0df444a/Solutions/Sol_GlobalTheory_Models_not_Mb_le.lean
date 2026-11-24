-- Prove2me | solution 1 for GlobalTheory.Models.not_Mb_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:37:39.886433+00:00
-- url     : https://prove2.me/submissions/8767c104-f3b6-494c-a49b-369fc8dda5f8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_AuxiliaryInertOddPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CmGeneratorSqQuadraticEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CoprimeLevel
import Theorems.Thm_GlobalTheory_Models_bar_mem_of_mem

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
open GlobalTheory GlobalTheory.Models
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.Models
theorem _root_.solution (H : Host E) {n : ℕ} (hn : AuxiliaryInertOddPrime H n) (l : Level H) (P : Ideal (𝓞 E)) (hP : P.IsPrime)
    (hnP : (n : 𝓞 E) ∈ P) : ¬ l.Mb ≤ P := by
  intro h
  apply hP.ne_top
  rw [eq_top_iff, ← l.coprime]
  refine sup_le h ?_
  rw [Ideal.map_le_iff_le_comap, l.fromK, Ideal.span_le]
  rintro a ⟨haM, ha⟩
  exact bar_mem_of_mem H hn P hP hnP ha (h haM)
end GlobalTheory.Models
