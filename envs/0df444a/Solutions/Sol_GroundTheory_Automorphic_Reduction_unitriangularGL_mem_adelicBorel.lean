-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.unitriangularGL_mem_adelicBorel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:05:53.355802+00:00
-- url     : https://prove2.me/submissions/09a47cd2-354c-408b-ab20-b73c822adc10

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionCore
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionSiegel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory.Global GroundTheory.Global.IdeleGroup
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Reduction
variable {K : Type*} [Field K] [NumberField K]
variable (n : ℕ)
namespace GroundTheory.Automorphic.Reduction
theorem _root_.solution (p : Fin n → Fin n → 𝔸[K]) :
    unitriangularGL n p ∈ adelicBorel :=
  (isUnitriangular_unitriangular p).1
end GroundTheory.Automorphic.Reduction
