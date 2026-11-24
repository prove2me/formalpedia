-- Prove2me | solution 1 for GlobalTheory.BoundedBasis.smul_vecMul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:02:41.128986+00:00
-- url     : https://prove2.me/submissions/b0adb2d5-ebcc-4a8a-802c-5be0bbf02558

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegerApproximationCountHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsFinsetTypesOfBoundedBases
import Theorems.Thm_GlobalTheory_BoundedBasis_vecMul_of

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
theorem _root_.solution {v : Fin r → Fin r → E} (hv : ∀ i, v i ∈ X.L') (o : Fin r → 𝓞 E) :
    (X.NC : E) • ((fun i => (o i : E)) ᵥ* Matrix.of v) ∈ X.Λ := by
  refine X.NC_sub _ ?_
  rw [vecMul_of]
  exact Submodule.sum_mem _ fun i _ => X.L'.smul_mem (o i) (hv i)
end GlobalTheory.BoundedBasis
