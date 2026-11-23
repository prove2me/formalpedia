-- Prove2me | solution 1 for GlobalTheory.QuadFibre.fibOf_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:35:48.832077+00:00
-- url     : https://prove2.me/submissions/62c9fdfc-6477-4485-bdf6-ced80e7ec84d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FibOfZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.QuadFibre
open MeasureTheory
open scoped Pointwise
namespace GlobalTheory.QuadFibre
theorem _root_.solution {K V : Type} [NormedField K] [MeasurableSpace K] [AddCommGroup V] [Module K V]
    [MeasurableSpace V] (μ : Measure V) (ν : Measure K) (q : V → K) (U : Set K) (s : K → K)
    {t : K} (ht : t ≠ 0) : fibOf μ ν q U s t =
      (ν (t • U))⁻¹ • Measure.map (fun x => s (t / q x) • x) (μ.restrict (q ⁻¹' (t • U))) := by
  simp [fibOf, ht]
end GlobalTheory.QuadFibre
