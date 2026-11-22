-- Prove2me | solution 1 for NemytskiiLebesgue.eLpNorm_realLIE
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:37:03.621956+00:00
-- url     : https://prove2.me/submissions/85543b66-9f9b-4804-9232-27a1b134a470

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
    {p : ℝ≥0∞} (u : Ω → ℝ) :
    eLpNorm (fun ω : Ω => realLIE (u ω)) p μ = eLpNorm u p μ := by
  rw [←eLpNorm_norm (fun ω => realLIE (u ω)), ←eLpNorm_norm u]
  simp
end NemytskiiLebesgue
