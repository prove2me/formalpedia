-- Prove2me | solution 1 for GlobalTheory.KeyPow.NormalAt.mem_siegelH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:42:35.43779+00:00
-- url     : https://prove2.me/submissions/bb91996d-52aa-4c39-b503-f323b4596852

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRuleOneOfKeyFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.KeyPow
namespace GlobalTheory.KeyPow
namespace NormalAt
theorem _root_.solution {x : KeyIn ℂ} {τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ} {a b : Fin x.P.g → ℂ} {c : ℂ}
    (h : NormalAt x τ M a b c) : τ ∈ ReciprocityTheory.PTheta.SiegelH (Fin x.P.g) := by
  obtain ⟨_, hs, hp, -⟩ := h
  exact ⟨hs, hp⟩
end NormalAt
end GlobalTheory.KeyPow
