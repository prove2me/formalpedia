-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.TermDecay.hasDerivAt_qZ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:22:56.58044+00:00
-- url     : https://prove2.me/submissions/68aa1772-c7ff-473f-8e9f-2140b30fa8af

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContDiffOnHeckeEisensteinFourierTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntZEqFourier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasDerivAtHeckeTermDecayIntegrand
import Theorems.Thm_GlobalTheory_HeckeTwo_TermSmooth_u_ne


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.TermDecay
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.TermDecay
namespace GlobalTheory.HeckeTwo.TermDecay
theorem _root_.solution : ∀ (σ : ℂ) (a : ℤ) (b m : ℕ) (y : ℝ), y ≠ 0 → ∀ t : ℝ,
    HasDerivAt (qZ σ a b m y) (-(a : ℂ) * qZ σ (a + 1) b m y t
      + 2 * (-σ - (b : ℂ)) * (qZ σ (a - 1) (b + 1) m y t - I * qZ σ a (b + 1) (m + 1) y t)) t := by
  intro σ a b m y hy t
  have hu := GlobalTheory.HeckeTwo.TermSmooth.u_ne hy t
  have hQ : 0 < t ^ 2 + y ^ 2 := by positivity
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) + (y : ℂ) * I) 1 t := by
    simpa using (hasDerivAt_id t).ofReal_comp.add_const ((y : ℂ) * I)
  have h2 := (hasDerivAt_zpow (-a) ((t : ℂ) + (y : ℂ) * I) (Or.inl hu)).comp t h1
  have h3 : HasDerivAt (fun t : ℝ => (((t ^ 2 + y ^ 2 : ℝ) : ℂ))) ((2 * t : ℝ) : ℂ) t := by
    have : HasDerivAt (fun t : ℝ => t ^ 2 + y ^ 2) (2 * t) t := by
      simpa using ((hasDerivAt_pow 2 t).add_const (y ^ 2))
    exact this.ofReal_comp
  have h4 := (Complex.hasStrictDerivAt_cpow_const (c := -σ - (b : ℂ))
      (Complex.ofReal_mem_slitPlane.2 hQ)).hasDerivAt.comp t h3
  have h := (h2.mul h4).mul_const ((y : ℂ) ^ m)
  refine h.congr_deriv ?_
  simp only [qZ, Function.comp_def]
  rw [show -(a + 1) = -a - 1 by ring, show -(a - 1) = -a + 1 by ring, zpow_add_one₀ hu,
    show -σ - ((b + 1 : ℕ) : ℂ) = -σ - (b : ℂ) - 1 by push_cast; ring]
  push_cast
  ring
end GlobalTheory.HeckeTwo.TermDecay
