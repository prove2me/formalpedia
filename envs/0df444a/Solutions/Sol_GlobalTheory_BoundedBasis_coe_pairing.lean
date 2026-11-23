-- Prove2me | solution 1 for GlobalTheory.BoundedBasis.coe_pairing
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:32:26.387514+00:00
-- url     : https://prove2.me/submissions/52409d43-64e3-4576-aa7f-2119c17052d8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegerApproximationCountHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsFinsetTypesOfBoundedBases
import Theorems.Thm_GlobalTheory_BoundedBasis_herm_vecMul_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory
open GlobalTheory.BoundedBasis
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : DataX E r)
namespace GlobalTheory.BoundedBasis
theorem _root_.solution (v : Fin r → Fin r → E) (hv : ∀ i, v i ∈ X.L') (x : X.Λ) (c : Fin r → E)
    (hc : (x : Fin r → E) = c ᵥ* Matrix.of v) (k : Fin r) :
    ((pairing X v hv x k : 𝓞 E) : E) = (((X.NA : E) • c) ᵥ* gramOf X.Gm v) k := by
  change herm X.Gm ((X.NA : E) • (x : Fin r → E)) (v k) = _
  rw [hc, ← smul_vecMul, herm_vecMul_left]
end GlobalTheory.BoundedBasis
