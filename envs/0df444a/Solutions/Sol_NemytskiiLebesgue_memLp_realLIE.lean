-- Prove2me | solution 1 for NemytskiiLebesgue.memLp_realLIE
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:39:25.338565+00:00
-- url     : https://prove2.me/submissions/deecb41d-9216-484b-86a6-f386be34564a

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Basic
public import Definitions.Def_LeanPool_NemytskiiLebesgue_RealIso

set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory
open scoped ENNReal
namespace NemytskiiLebesgue
theorem _root_.solution {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {p : ℝ≥0∞} {u : Ω → ℝ} (hu : MemLp u p μ) :
    MemLp (fun ω : Ω => realLIE (u ω)) p μ :=
  hu.continuousLinearMap_comp realLIE.toLinearEquiv.toContinuousLinearMap
end NemytskiiLebesgue
