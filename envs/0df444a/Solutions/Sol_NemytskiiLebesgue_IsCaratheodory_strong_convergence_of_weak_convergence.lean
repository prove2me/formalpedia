-- Prove2me | solution 1 for NemytskiiLebesgue.IsCaratheodory.strong_convergence_of_weak_convergence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:39:33.49885+00:00
-- url     : https://prove2.me/submissions/30c4c848-bcc1-46bc-a608-8c7e58553425

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Vitali
public import Definitions.Def_LeanPool_NemytskiiLebesgue_WeakConvergence
public import Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_seqContinuous_nemytskii_of_aestronglyMeas_of_growth


set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter
open scoped ENNReal Topology
namespace NemytskiiLebesgue
namespace IsCaratheodory
theorem _root_.solution
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f : Ω → ℝ → ℝ} (hf : IsCaratheodory f μ)
    {p : ℝ≥0∞} (h1p : 1 ≤ p) (hp : p < ⊤)
    {q : ℝ≥0∞} (h1q : 1 ≤ q) (hq : q < ⊤)
    {ι : X →L[ℝ] (Ω → ℝ)} (hιp : ∀ x : X, MemLp (ι x) p μ)
    {a : Ω → ℝ} (haq : MemLp a q μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hfaCpq : ∀ᵐ ω ∂μ, ∀ ξ : ℝ, |f ω ξ| ≤ |a ω| + C * |ξ| ^ (p / q).toReal)
    {u : ℕ → X} (hup : UnifIntegrable (ι ∘ u) p μ)
    {v : X} (huv : u.NemytskiiWeaklyConvergesTo v) :
    (fun n : ℕ => fun ω : Ω => f ω (ι (u n) ω)).NemytskiiConvergesTo (fun ω : Ω => f ω (ι v ω)) q μ
      := by
  convert
    hf.seqContinuous_nemytskii_of_aestronglyMeas_of_growth h1p hp.ne_top h1q hq.ne_top haq hC hfaCpq
    .. using 1
  any_goals tauto
  · exact (MemLp.aestronglyMeasurable <| hιp <| u ·)
  · convert tendstoInMeasure_of_tendsto_ae (MemLp.aestronglyMeasurable <| hιp <| u ·) _
    apply Eventually.of_forall
    intro ω
    have := huv ((ContinuousLinearMap.proj ω).comp ι)
    aesop
end IsCaratheodory
end NemytskiiLebesgue
