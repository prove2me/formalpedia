-- Prove2me | solution 1 for GlobalTheory.AnArc.exists_convergence
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:37:15.520719+00:00
-- url     : https://prove2.me/submissions/b4684eb0-9c15-49f8-a1fc-d4054059794d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SummableExpNegSumAbs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HasSumLocallyUniformlyOnTerm
import Theorems.Thm_GlobalTheory_AnArc_exists_isConvLine
import Theorems.Thm_GlobalTheory_AnArc_locally_normal
import Theorems.Thm_GlobalTheory_AnArc_summable_norm_term
import Theorems.Thm_GlobalTheory_AnArc_hasSumLocallyUniformlyOn_term
import Theorems.Thm_GlobalTheory_AnArc_differentiableOn_Sum
import Theorems.Thm_GlobalTheory_AnArc_differentiable_coeff_FSum
import Theorems.Thm_GlobalTheory_AnArc_hasSum_coeff_FSum
import Theorems.Thm_GlobalTheory_AnArc_hasSum_fderiv_coeff_FSum

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
namespace GlobalTheory.AnArc
theorem _root_.solution : ∃ T₀ : ℝ, ∀ (j : ℕ) [NeZero j] (α : A.X) (th : (Fin A.gB → ℂ) → ℂ), th ∈ A.Theta j α →
    (∀ p : ℂ × A.V, T₀ < p.1.im → ∃ t ∈ 𝓝 p, ∃ u : A.X → ℝ, Summable u ∧ ∀ μ, ∀ q ∈ t,
      ‖A.term j α th μ q.2 * eTwoPi (q.1 * A.exponent j α μ)‖ ≤ u μ) ∧
    (∀ w : ℂ, T₀ < w.im → ∀ v, Summable fun μ => ‖A.term j α th μ v * eTwoPi (w * A.exponent j α μ)‖) ∧
    HasSumLocallyUniformlyOn (fun μ (p : ℂ × A.V) => A.term j α th μ p.2 * eTwoPi (p.1 * A.exponent j α μ))
      (fun p => A.Sum j α th p.1 p.2) {p | T₀ < p.1.im} ∧
    DifferentiableOn ℂ (fun p : ℂ × A.V => A.Sum j α th p.1 p.2) {p | T₀ < p.1.im} ∧
    (∀ w : ℂ, T₀ < w.im → ∀ v,
      HasSum (fun n : ℤ => (A.FSum j α th v).coeff n * eTwoPi w ^ n) (A.Sum j α th w v)) ∧
    (∀ n : ℤ, Differentiable ℂ fun v => (A.FSum j α th v).coeff n) ∧
    (∀ w : ℂ, T₀ < w.im → ∀ v v₀,
      HasSum (fun n : ℤ => fderiv ℂ (fun v => (A.FSum j α th v).coeff n) v v₀ * eTwoPi w ^ n)
        (fderiv ℂ (A.Sum j α th w) v v₀)) := by
  obtain ⟨T₀, hT⟩ := A.exists_isConvLine
  exact ⟨T₀, fun j _ α th h => ⟨locally_normal hT (NeZero.ne j) h,
    fun _ hw => summable_norm_term hT (NeZero.ne j) h hw, hasSumLocallyUniformlyOn_term hT (NeZero.ne j) h,
    differentiableOn_Sum hT (NeZero.ne j) h, fun _ hw => hasSum_coeff_FSum hT h hw,
    differentiable_coeff_FSum h.1, fun _ hw => hasSum_fderiv_coeff_FSum hT h hw⟩⟩
end GlobalTheory.AnArc
