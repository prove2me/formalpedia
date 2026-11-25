-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.coe_diagUnits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:28:38.665618+00:00
-- url     : https://prove2.me/submissions/6732530f-7fd0-4fe1-b06a-3be24e1ef6f3

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
theorem _root_.solution {R : Type*} [CommRing R] (d : Fin n → Rˣ) :
    ((diagUnits n d : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = diagonal fun i => (d i : R) := rfl
end GroundTheory.Automorphic.Reduction
