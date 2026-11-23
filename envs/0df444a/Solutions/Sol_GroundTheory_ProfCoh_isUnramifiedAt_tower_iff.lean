-- Prove2me | solution 1 for GroundTheory.ProfCoh.isUnramifiedAt_tower_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:34.690654+00:00
-- url     : https://prove2.me/submissions/ba397dca-47e0-4e27-8959-abf61563cc94

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_Ramification

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.ProfCoh
open NumberField IsDedekindDomain
variable {F L M : Type*} [Field F] [Field L] [Field M] [NumberField F] [NumberField L]
  [NumberField M] [Algebra F L] [Algebra L M] [Algebra F M] [IsScalarTower F L M]
namespace GroundTheory.ProfCoh
theorem _root_.solution (Q : Ideal (𝓞 M)) [Q.IsPrime] :
    Algebra.IsUnramifiedAt (𝓞 F) Q ↔
      Algebra.IsUnramifiedAt (𝓞 F) (Q.under (𝓞 L)) ∧ Algebra.IsUnramifiedAt (𝓞 L) Q := by
  rw [← Ideal.ramificationIdx_eq_one_iff, ← Ideal.ramificationIdx_eq_one_iff,
    ← Ideal.ramificationIdx_eq_one_iff, Ideal.ramificationIdx_tower (q := Q.under (𝓞 L))]
  exact mul_eq_one
end GroundTheory.ProfCoh
