-- Prove2me | solution 1 for GlobalTheory.UnifParts.triv_iff_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:48:24.759397+00:00
-- url     : https://prove2.me/submissions/11082925-8596-4397-a9ab-05afa78887b4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FamilyUnifOfParts
import Theorems.Thm_GlobalTheory_UnifParts_triv_iff

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
noncomputable section
open GlobalTheory GlobalTheory.UnifParts
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
namespace GlobalTheory.UnifParts
theorem _root_.solution {D D' : Datum H} (l : Level H) (t : D.La →ₗ[𝓞 E] D'.La)
    (ht : ∀ b, ∃ a e, b = t a + l.M' • e) (gam : D'.La ≃ₗ[𝓞 E] D'.La) (n : ℕ) (hn : n ∣ l.M') :
    (∀ a, ∃ x, gam (t a) = t a + n • x) ↔ ∀ a, ∃ x, gam a = a + n • x := by
  simpa using triv_iff l t ht gam ⊤ n hn
end GlobalTheory.UnifParts
