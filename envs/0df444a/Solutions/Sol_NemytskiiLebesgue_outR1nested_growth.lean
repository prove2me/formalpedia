-- Prove2me | solution 1 for NemytskiiLebesgue.outR1nested_growth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:38:24.760425+00:00
-- url     : https://prove2.me/submissions/22bfdaa9-2e5d-4469-8221-4380c2a5cfbe

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Closure
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Frechet
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Nemytskii
public import Definitions.Def_LeanPool_NemytskiiLebesgue_RealIso
public import Definitions.Def_LeanPool_NemytskiiLebesgue_IntegralFunctional
public import Theorems.Thm_NemytskiiLebesgue_outR1nested_norm_eq

set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory
open scoped ENNReal
namespace NemytskiiLebesgue
theorem _root_.solution
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m : ℕ}
    (f' : Ω → ℝ^m → (ℝ^m →L[ℝ] ℝ))
    {b : Ω → ℝ} {C α : ℝ}
    (hf'bCα : ∀ᵐ ω ∂μ, ∀ ξ : ℝ^m, ‖f' ω ξ‖ ≤ b ω + C * ‖ξ‖ ^ α) :
    ∀ᵐ ω ∂μ, ∀ ξ : ℝ^m, ‖NemytskiiLebesgue.outR1nested f' ω ξ‖ ≤ b ω + C * ‖ξ‖ ^ α := by
  filter_upwards [hf'bCα] with ω hω ξ using le_trans (by rw [outR1nested_norm_eq]) (hω ξ)
end NemytskiiLebesgue
