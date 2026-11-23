-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.finite_inter_singularSet
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:43:26.744207+00:00
-- url     : https://prove2.me/submissions/bd6f7f8d-3e4b-4a06-a850-474b5734d875

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable (L : PeriodPair)
variable {L}
variable (L)
variable {L}
namespace GroundTheory.Global.Elliptic
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {f : ℂ → E} (hf : Meromorphic f) {K : Set ℂ} (hK : IsCompact K) :
    (K ∩ singularSet f).Finite := by
  have h := hK.finite_sdiff_of_mem_codiscreteWithin
    ((hf.meromorphicOn (s := K)).analyticAt_mem_codiscreteWithin)
  exact h.subset fun z hz ↦ ⟨hz.1, hz.2⟩
end GroundTheory.Global.Elliptic
