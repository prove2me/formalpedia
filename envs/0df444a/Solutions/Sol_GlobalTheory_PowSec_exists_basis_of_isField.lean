-- Prove2me | solution 1 for GlobalTheory.PowSec.exists_basis_of_isField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:32:43.35041+00:00
-- url     : https://prove2.me/submissions/8c095485-a849-4d58-897d-01f340131200

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsIndepSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsBasisOfIsField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.PowSec
namespace GlobalTheory.PowSec
theorem _root_.solution {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (hR : IsField R)
    {m : ℕ} (hm : 0 < m) (h : Module.finrank R M = m) : Nonempty (Module.Basis (Fin m) R M) := by
  letI := hR.toField
  haveI : Module.Finite R M := Module.finite_of_finrank_pos (h ▸ hm)
  exact ⟨Module.finBasisOfFinrankEq R M h⟩
end GlobalTheory.PowSec
