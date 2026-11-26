-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_cosine_jump_high_frequency
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:43:20.845344+00:00
-- url     : https://prove2.me/submissions/0356f281-8fc9-4494-9efd-3ed41696528e

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Theorems.Thm_Kyprianou_Ch04_ito43_cosine_jump_envelope_pathwise
import Theorems.Thm_Kyprianou_Ch04_ito43_cosine_jump_envelope_measurable
import Theorems.Thm_Kyprianou_Ch04_ito43_ucp_countable_envelope
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04
open scoped Topology
open Set
theorem solution {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hLevy : ProbabilityTheory.IsLevyProcess X P)
    (triplet : ProbabilityTheory.LevyKhintchineTriple)
    (hTriplet : forall (t : NNReal) (xi : Real),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : Real) : Complex) *
          Kyprianou.Ch01.levyTripleExponent triplet xi))
    (Xleft : NNReal -> Omega -> Real)
    (hLeft : ∀ᵐ omega : Omega ∂P,
      forall t : NNReal, 0 < t ->
        Tendsto (fun s : NNReal => X s omega)
          (nhdsWithin t (Set.Iio t))
          (nhds (Xleft t omega))) :
    ∀ T : NNReal,
    let q : ℕ → ℝ → ℝ := fun m z => (1-Real.cos (((m:ℝ)+1)*z))/((m:ℝ)+1)^2
    let J : ℕ → NNReal → Omega → ℝ := fun m t w =>
      ∫ z in Icc (0:ℝ) (t:ℝ) ×ˢ (univ : Set ℝ),
        q m z.2 ∂(pathJumpMeasure X Xleft w)
    ∀ e : ℝ, 0 < e → ∀ η : ℝ, 0 < η → ∀ᶠ m : ℕ in atTop,
      (P {w | ∃ t ≤ T, e ≤ |J m t w|}).toReal ≤ η := by 
  intro T q J e he η hη
  obtain ⟨hl,hb⟩ := ito43_cosine_jump_envelope_pathwise P X hLevy triplet hTriplet Xleft hLeft T
  have hm := ito43_cosine_jump_envelope_measurable P X hLevy triplet hTriplet Xleft hLeft T
  have h := ito43_ucp_countable_envelope P J (fun m => J m (T+1)) T hm hl hb e he
  filter_upwards [h.eventually (gt_mem_nhds hη)] with m hm
  exact le_of_lt hm
