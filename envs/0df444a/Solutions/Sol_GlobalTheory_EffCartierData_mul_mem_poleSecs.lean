-- Prove2me | solution 1 for GlobalTheory.EffCartierData.mul_mem_poleSecs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:45:49.44592+00:00
-- url     : https://prove2.me/submissions/c7979f73-6606-4533-bc03-173e280dded9

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheaf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_CoeNonzeroLocusCanonicalEqComplRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open Cartier
open GlobalTheory.EffCartierData
variable {X Y Z : Scheme.{0}}
variable (D D' : EffCartierData X)
variable [IsIntegral X]
namespace GlobalTheory.EffCartierData
theorem _root_.solution {m n : ℕ} {V : X.Opens} [Nonempty V] {h h' : X.functionField}
    (hh : h ∈ D.poleSecs m V) (hh' : h' ∈ D.poleSecs n V) : h * h' ∈ D.poleSecs (m + n) V := by
  rw [mem_poleSecs_iff_stalk] at hh hh' ⊢
  intro i x hx hi
  obtain ⟨r, hr⟩ := hh i x hx hi
  obtain ⟨r', hr'⟩ := hh' i x hx hi
  exact ⟨r * r', by rw [map_mul, hr, hr']; ring⟩
end GlobalTheory.EffCartierData
