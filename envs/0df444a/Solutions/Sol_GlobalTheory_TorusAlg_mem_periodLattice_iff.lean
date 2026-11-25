-- Prove2me | solution 1 for GlobalTheory.TorusAlg.mem_periodLattice_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:19:57.363367+00:00
-- url     : https://prove2.me/submissions/9a75949a-b88e-41cb-b08e-6b56b06c7668

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Definitions.Def_Development_AbelianVarietyTheory_Statements_ThetaLevelCharacters_MemThetaLevelCharDimZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.TorusAlg
open ReciprocityTheory.PTheta
variable {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} {a b : Fin g → ℂ}
namespace GlobalTheory.TorusAlg
theorem _root_.solution (z : Fin g → ℂ) : z ∈ periodLattice τ ↔
    ∃ m n : Fin g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ)) :=
  ⟨fun ⟨n, m, h⟩ => ⟨m, n, h.trans (add_comm _ _)⟩, fun ⟨m, n, h⟩ => ⟨n, m, h.trans (add_comm _ _)⟩⟩
end GlobalTheory.TorusAlg
