-- Prove2me | solution 1 for GlobalTheory.AnArc.locally_normal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:42:29.513338+00:00
-- url     : https://prove2.me/submissions/46e0ee0e-0be6-4d8d-839f-691cc930fa57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SummableExpNegSumAbs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HasSumLocallyUniformlyOnTerm
import Theorems.Thm_GlobalTheory_AnArc_exists_summable_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
variable {A} {T₀ : ℝ} (hT : A.IsConvLine T₀) {j : ℕ} {α : A.X} {th : (Fin A.gB → ℂ) → ℂ}
include hT
namespace GlobalTheory.AnArc
theorem _root_.solution (hj : j ≠ 0) (h : th ∈ A.Theta j α) (p : ℂ × A.V) (hp : T₀ < p.1.im) :
    ∃ t ∈ 𝓝 p, ∃ u : A.X → ℝ, Summable u ∧ ∀ μ, ∀ q ∈ t,
      ‖A.term j α th μ q.2 * eTwoPi (q.1 * A.exponent j α μ)‖ ≤ u μ := by
  obtain ⟨u, hu, hb⟩ := exists_summable_bound hT hj h (T₁ := (T₀ + p.1.im) / 2) (by linarith) (p.1.im + 1) (‖p.2‖ + 1)
  have c1 : Continuous fun q : ℂ × A.V => q.1.im := by fun_prop
  have c2 : Continuous fun q : ℂ × A.V => ‖q.2‖ := by fun_prop
  refine ⟨{q | (T₀ + p.1.im) / 2 ≤ q.1.im} ∩ ({q | q.1.im ≤ p.1.im + 1} ∩ {q | ‖q.2‖ ≤ ‖p.2‖ + 1}), ?_, u, hu,
    fun μ q hq => hb μ q.1 q.2 hq.1 hq.2.1 hq.2.2⟩
  exact inter_mem (c1.continuousAt.eventually (eventually_ge_nhds (by simp only; linarith)))
    (inter_mem (c1.continuousAt.eventually (eventually_le_nhds (by simp)))
      (c2.continuousAt.eventually (eventually_le_nhds (by simp))))
end GlobalTheory.AnArc
