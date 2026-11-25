-- Prove2me | solution 1 for GlobalTheory.fj_eq_sum_of_eqOn_dom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:27:55.025466+00:00
-- url     : https://prove2.me/submissions/39b60f44-690a-4f88-83af-fc4c8da73742

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BoundedSectionAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FourierJacobiCoeffLinearBoundedSections
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_BoundedSectionAlgebra_integrableOn_fj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_TransvectionPeriodicity_flow_real_mem_dom


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD MeasureTheory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (m : ℕ) (a : Fin m → ℂ) (Q : Fin m → Frame X.Ψ r → ℂ) (f : Frame X.Ψ r → ℂ), (∀ i, X.IsBddSec la (Q i)) → (∀ x ∈ X.dom, f x = ∑ i, a i * Q i x) → ∀ ξ, X.IsIso ξ → ∀ ν : X.Ψ → ℝ, ∀ x ∈ X.dom, X.fj la ξ ν f x = ∑ i, a i * X.fj la ξ ν (Q i) x := by
  intro E _ _ _ r X la m a Q f hQ hf ξ hξ ν x hx
  unfold Data.fj
  split_ifs with h1 h2
  · have hint := fun i => (BoundedSectionAlgebra.integrableOn_fj X (hQ i) hξ.2.1 hx ν
      h2.choose_spec.2.2.2).const_mul (a i)
    have hs := integral_finsetSum (s := Finset.univ) (fun i _ => hint i)
    have hdom : ∀ s : X.Ψ → ℝ, X.flow ξ (fun τ => (s τ : ℂ)) x ∈ X.dom := fun s =>
      TransvectionPeriodicity.flow_real_mem_dom X hξ.2.1 s x hx
    simp only [integral_const_mul] at hs
    simp only [hf _ (hdom _), Finset.sum_mul, mul_assoc] at hs ⊢
    rw [hs, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => mul_left_comm _ _ _
  · simp
  · simp
end GlobalTheory
