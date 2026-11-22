-- Prove2me | solution 1 for NemytskiiLebesgue.IsCaratheodory.memLp_nemytskii_of_globally_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:39:36.621755+00:00
-- url     : https://prove2.me/submissions/43bf227e-ec36-41b2-818b-5a607eee069c

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Continuity
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Lipschitz
public import Theorems.Thm_NemytskiiLebesgue_memLp_nemytskii_of_globally_lipschitz_of_aestronglyMeas
public import Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_aestronglyMeas_nemytskii_of_aestronglyMeas


set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory
open scoped NNReal ENNReal
namespace NemytskiiLebesgue
namespace IsCaratheodory
theorem _root_.solution
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {m k : ℕ}
    {f : Ω → ℝ^m → ℝ^k} (hf : IsCaratheodory f μ)
    {p : ℝ≥0∞} (hf0p : MemLp (f · 0) p μ)
    {u : Ω → ℝ^m} (hup : MemLp u p μ)
    {L : Ω → ℝ} (hL : MemLp L ⊤ μ)
    (hfL : ∀ᵐ ω : Ω ∂μ, ∀ ξ η : ℝ^m, ‖f ω ξ - f ω η‖ ≤ L ω * ‖ξ - η‖) :
    MemLp (fun ω : Ω => f ω (u ω)) p μ :=
  memLp_nemytskii_of_globally_lipschitz_of_aestronglyMeas
    hf0p
    hup
    (hf.aestronglyMeas_nemytskii_of_aestronglyMeas hup.aestronglyMeasurable)
    hL.eLpNorm_lt_top
    hfL
end IsCaratheodory
end NemytskiiLebesgue
