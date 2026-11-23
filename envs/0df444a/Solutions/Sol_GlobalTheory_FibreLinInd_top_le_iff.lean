-- Prove2me | solution 1 for GlobalTheory.FibreLinInd.top_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:16:13.466717+00:00
-- url     : https://prove2.me/submissions/5b2220b9-77ce-4f74-86d7-38bc604a5704

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsOpenSetOfLinearIndependentOnFibres

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.FibreLinInd
variable {K : Type} [Field K] {P G : Scheme.{0}}
namespace GlobalTheory.FibreLinInd
theorem _root_.solution (x : Sp K ⟶ P) (U : P.Opens) (z : Sp K) : ⊤ ≤ x ⁻¹ᵁ U ↔ x z ∈ U := by
  have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  exact ⟨fun h => h (show z ∈ (⊤ : (Sp K).Opens) from trivial),
    fun h y _ => by rw [Subsingleton.elim y z]; exact h⟩
end GlobalTheory.FibreLinInd
