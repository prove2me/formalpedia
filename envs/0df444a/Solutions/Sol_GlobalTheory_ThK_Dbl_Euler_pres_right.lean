-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.Euler.pres_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:28:43.742848+00:00
-- url     : https://prove2.me/submissions/33ae0766-378f-42c3-8450-324f747d67d1

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_EulerA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.Euler
open MeasureTheory Set
variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H]
  [LocallyCompactSpace H] [SecondCountableTopology H] {ν : Measure H} [ν.IsHaarMeasure] {K : Subgroup H}
namespace GlobalTheory.ThK.Dbl.Euler
theorem _root_.solution (hK : MeasurableSet (K : Set H)) (h1 : ν K = 1) {k : H} (hk : k ∈ K) :
    MeasurePreserving (· * k) ν ν := by
  have e := Measure.isMulLeftInvariant_eq_smul (ν.map (· * k)) ν
  have m : Measurable fun x : H => x * k := measurable_mul_const k
  have e2 := congrArg (· (K : Set H)) e
  have p : (fun x : H => x * k) ⁻¹' K = K := Set.ext fun x => K.mul_mem_cancel_right hk
  simp only [Measure.map_apply m hK, p, h1, Measure.coe_nnreal_smul_apply, mul_one] at e2
  refine ⟨m, ?_⟩
  rw [e, show Measure.haarScalarFactor (ν.map (· * k)) ν = 1 by exact_mod_cast e2.symm, one_smul]
end GlobalTheory.ThK.Dbl.Euler
