-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.IsPeriodic.analyticAt_add_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:43:25.496873+00:00
-- url     : https://prove2.me/submissions/0191f8b3-35dd-42bc-a206-acab47a116d5

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Theorems.Thm_GroundTheory_Global_Elliptic_IsPeriodic_sub
import Theorems.Thm_GroundTheory_Global_Elliptic_IsPeriodic_comp_add

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
namespace IsPeriodic
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} (hf : IsPeriodic L f) {l : ℂ} (hl : l ∈ L.lattice) (z : ℂ) :
    AnalyticAt ℂ f (z + l) ↔ AnalyticAt ℂ f z := by
  constructor
  · intro h
    have : AnalyticAt ℂ (f ∘ fun w ↦ w + l) z := AnalyticAt.comp (g := f) h (by fun_prop)
    rwa [Function.comp_def, hf.comp_add hl] at this
  · intro h
    have h' : AnalyticAt ℂ f ((z + l) - l) := by simpa using h
    have : AnalyticAt ℂ (f ∘ fun w ↦ w - l) (z + l) := AnalyticAt.comp (g := f) h' (by fun_prop)
    have e : (fun w ↦ f (w - l)) = f := funext fun w ↦ hf.sub w hl
    rwa [Function.comp_def, e] at this
end IsPeriodic
end GroundTheory.Global.Elliptic
