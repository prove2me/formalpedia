-- Prove2me | solution 1 for NemytskiiLebesgue.outR1nested_norm_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:37:37.520074+00:00
-- url     : https://prove2.me/submissions/cf8c3716-db4e-41bd-b328-8dd03a52f12d

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
    {Ω : Type*}
    {m : ℕ}
    (f' : Ω → ℝ^m → (ℝ^m →L[ℝ] ℝ)) (ω : Ω) (ξ : ℝ^m) :
    ‖NemytskiiLebesgue.outR1nested f' ω ξ‖ = ‖f' ω ξ‖ := by
  have f'_norm : ∀ v : ℝ^m, ‖realLIE.toContinuousLinearMap (f' ω ξ v)‖ = ‖f' ω ξ v‖ := by
    bound
  refine
    le_antisymm
      (ContinuousLinearMap.opNorm_le_bound _ (ContinuousLinearMap.opNorm_nonneg (f' ω ξ)) fun v :
        ℝ^m => ?_)
      (ContinuousLinearMap.opNorm_le_bound _ (ContinuousLinearMap.opNorm_nonneg
        (NemytskiiLebesgue.outR1nested f' ω ξ)) fun v : ℝ^m => ?_)
  · exact f'_norm v ▸ ContinuousLinearMap.le_opNorm ..
  · exact le_trans (f'_norm v).ge ((realLIE.toContinuousLinearMap.comp (f' ω ξ)).le_opNorm v)
end NemytskiiLebesgue
