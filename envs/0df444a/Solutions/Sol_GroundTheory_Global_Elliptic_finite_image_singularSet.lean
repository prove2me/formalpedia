-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.finite_image_singularSet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:13:34.626535+00:00
-- url     : https://prove2.me/submissions/30b5ad19-a740-4746-9518-a07b4eaf276a

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Theorems.Thm_GroundTheory_Global_Elliptic_Torus_mk_eq_mk_iff
import Theorems.Thm_GroundTheory_Global_Elliptic_isCompact_fundamentalCompact
import Theorems.Thm_GroundTheory_Global_Elliptic_exists_sub_mem_fundamentalCompact
import Theorems.Thm_GroundTheory_Global_Elliptic_IsPeriodic_analyticAt_add_iff
import Theorems.Thm_GroundTheory_Global_Elliptic_finite_inter_singularSet

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
variable (L)
namespace GroundTheory.Global.Elliptic
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {f : ℂ → E} (hf : Meromorphic f) (hp : IsPeriodic L f) :
    (Torus.mk L '' singularSet f).Finite := by
  refine ((finite_inter_singularSet hf (isCompact_fundamentalCompact L)).image
    (Torus.mk L)).subset ?_
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨l, hl, hzl⟩ := exists_sub_mem_fundamentalCompact L z
  refine ⟨z - l, ⟨hzl, fun h ↦ hz ?_⟩, ?_⟩
  · have := (hp.analyticAt_add_iff hl (z - l)).2 h
    simpa using this
  · exact (Torus.mk_eq_mk_iff L).2 (by simpa using L.lattice.neg_mem hl)
end GroundTheory.Global.Elliptic
