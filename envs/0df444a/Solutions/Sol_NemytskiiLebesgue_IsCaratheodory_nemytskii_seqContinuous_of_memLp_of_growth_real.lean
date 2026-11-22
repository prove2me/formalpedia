-- Prove2me | solution 1 for NemytskiiLebesgue.IsCaratheodory.nemytskii_seqContinuous_of_memLp_of_growth_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:38:58.355772+00:00
-- url     : https://prove2.me/submissions/b5b84e6e-509a-4bd0-a172-93d8b2618b26

module
public import Mathlib.MeasureTheory.Function.UnifTight
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Caratheodory
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Continuity
public import Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_nemytskii_seqContinuous_of_aestronglyMeas_of_growth

set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter
open scoped NNReal ENNReal Topology
namespace NemytskiiLebesgue
namespace IsCaratheodory
theorem _root_.solution
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {m k : ℕ}
    {f : Ω → ℝ^m → ℝ^k} (hf : IsCaratheodory f μ)
    {p : ℝ≥0∞} (h1p : 1 ≤ p) (hp : p < ⊤)
    {q : ℝ≥0∞} (h1q : 1 ≤ q) (hq : q < ⊤)
    {a : Ω → ℝ} (haq : MemLp a q μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hfaCpq : ∀ᵐ ω : Ω ∂μ, ∀ ξ : ℝ^m, ‖f ω ξ‖ ≤ |a ω| + C * ‖ξ‖ ^ (p / q).toReal)
    {uₙ : ℕ → Ω → ℝ^m} (huₙ : ∀ n : ℕ, MemLp (uₙ n) p μ)
    {u : Ω → ℝ^m} (hup : MemLp u p μ)
    (huuₙ : uₙ.NemytskiiConvergesTo u p μ) :
    (fun n : ℕ => fun ω : Ω => f ω (uₙ n ω)).NemytskiiConvergesTo (fun ω : Ω => f ω (u ω)) q μ :=
  hf.nemytskii_seqContinuous_of_aestronglyMeas_of_growth h1p hp.ne_top h1q hq.ne_top haq hC hfaCpq
    (huₙ ·|>.aestronglyMeasurable) hup huuₙ
end IsCaratheodory
end NemytskiiLebesgue
