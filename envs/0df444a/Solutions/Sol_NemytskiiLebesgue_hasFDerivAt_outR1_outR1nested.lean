-- Prove2me | solution 1 for NemytskiiLebesgue.hasFDerivAt_outR1_outR1nested
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:37:35.604727+00:00
-- url     : https://prove2.me/submissions/f525a0f4-114a-468c-9954-8c2db609fa02

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Closure
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Frechet
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Nemytskii
public import Definitions.Def_LeanPool_NemytskiiLebesgue_RealIso
public import Definitions.Def_LeanPool_NemytskiiLebesgue_IntegralFunctional

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
    {f : Ω → ℝ^m → ℝ} {f' : Ω → ℝ^m → (ℝ^m →L[ℝ] ℝ)}
    (hff' : ∀ᵐ ω ∂μ, ∀ ξ : ℝ^m, HasFDerivAt (f ω) (f' ω ξ) ξ) :
    ∀ᵐ ω ∂μ, ∀ ξ : ℝ^m, HasFDerivAt (NemytskiiLebesgue.outR1 f ω) (NemytskiiLebesgue.outR1nested f'
      ω ξ) ξ :=
  hff'.mono ↓(fun _ => realLIE.toContinuousLinearMap.hasFDerivAt.comp _ <| · _)
end NemytskiiLebesgue
