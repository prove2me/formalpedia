-- Prove2me | solution 1 for Kyprianou.Ch02.levyItoTripleIndependentFromMarkRegionPathsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:45:41.179796+00:00
-- url     : https://prove2.me/submissions/a0cef843-057f-40b5-831a-3cda3e829939

import Theorems.Thm_Kyprianou_Ch02_threeSigmaIndepOfJoinAndPairCh02V1
import Theorems.Thm_Kyprianou_ch02PoissonDisjointRegionsIndependentSigma
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

open scoped Topology

theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    [SigmaFinite levyMeasure]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure)
    (a : ℝ) (σ : ℝ≥0)
    (B : LevyStochCalc.Brownian.BrownianMotion P)
    (hDrivers : ProbabilityTheory.IndepFun
      (fun ω => fun (t : ℝ) => B.W t ω)
      (fun ω => N.N ω) P)
    (L S : Ω → ℝ≥0 → ℝ)
    (hL : Measurable[(⨆ C ∈ {C : Set (ℝ × ℝ) |
        C ⊆ ((Set.univ : Set ℝ) ×ˢ {x : ℝ | 1 ≤ |x|}) ∧ MeasurableSet C},
        MeasurableSpace.comap (fun ω => N.N ω C) inferInstance)] L)
    (hS : Measurable[(⨆ C ∈ {C : Set (ℝ × ℝ) |
        C ⊆ ((Set.univ : Set ℝ) ×ˢ {x : ℝ | |x| < 1}) ∧ MeasurableSet C},
        MeasurableSpace.comap (fun ω => N.N ω C) inferInstance)] S) :
    Kyprianou.IndependentLevyItoComponents P
      (fun (t : ℝ≥0) (ω : Ω) => (σ : ℝ) * B.W (t : ℝ) ω - a * (t : ℝ))
      (fun t ω => L ω t) (fun t ω => S ω t) := by
  let A : Set (ℝ × ℝ) := (Set.univ : Set ℝ) ×ˢ {x : ℝ | 1 ≤ |x|}
  let C : Set (ℝ × ℝ) := (Set.univ : Set ℝ) ×ˢ {x : ℝ | |x| < 1}
  let mN := MeasurableSpace.comap (fun ω => N.N ω) inferInstance
  letI : MeasurableSpace Ω := mΩ
  let mB := MeasurableSpace.comap (fun ω => fun (t : ℝ) => B.W t ω) inferInstance
  letI : MeasurableSpace Ω := mΩ
  let mL : MeasurableSpace Ω := ⨆ D ∈ {D : Set (ℝ × ℝ) | D ⊆ A ∧ MeasurableSet D},
    MeasurableSpace.comap (fun ω => N.N ω D) inferInstance
  letI : MeasurableSpace Ω := mΩ
  let mS : MeasurableSpace Ω := ⨆ D ∈ {D : Set (ℝ × ℝ) | D ⊆ C ∧ MeasurableSet D},
    MeasurableSpace.comap (fun ω => N.N ω D) inferInstance
  letI : MeasurableSpace Ω := mΩ
  have hA : MeasurableSet A := MeasurableSet.univ.prod
    (measurableSet_le measurable_const continuous_abs.measurable)
  have hC : MeasurableSet C := MeasurableSet.univ.prod
    (measurableSet_lt continuous_abs.measurable measurable_const)
  have hAC : Disjoint A C := by
    rw [Set.disjoint_left]
    intro p hp hq
    have hp' : (1 : ℝ) ≤ |p.2| := hp.2
    have hq' : |p.2| < (1 : ℝ) := hq.2
    exact (not_lt_of_ge hp') hq'
  have hLS : Indep mL mS P :=
    Kyprianou.ch02PoissonDisjointRegionsIndependentSigma P levyMeasure N A C hA hC hAC
  have hsub (R : Set (ℝ × ℝ)) :
      (⨆ D ∈ {D : Set (ℝ × ℝ) | D ⊆ R ∧ MeasurableSet D},
        MeasurableSpace.comap (fun ω => N.N ω D) inferInstance) ≤ mN := by
    refine iSup_le (fun D => iSup_le (fun hD => ?_))
    exact MeasurableSpace.comap_le_comap_of_eq_comp
      (fun μ : Measure (ℝ × ℝ) => μ D) (Measure.measurable_coe hD.2) rfl
  have hB : Indep mB mN P := hDrivers
  have hBLS : Indep mB (mL ⊔ mS) P :=
    indep_of_indep_of_le_right hB (sup_le (hsub A) (hsub C))
  have hI := Kyprianou.Ch02.threeSigmaIndepOfJoinAndPairCh02V1
    P mB mL mS hBLS hLS
  let g : (ℝ → ℝ) → (ℝ≥0 → ℝ) := fun w t =>
    (σ : ℝ) * w (t : ℝ) - a * (t : ℝ)
  have hg : Measurable g := by
    apply measurable_pi_lambda
    intro t
    exact (measurable_const.mul (measurable_pi_apply (t : ℝ))).sub_const _
  have hG : Measurable[mB] (fun ω (t : ℝ≥0) =>
      (σ : ℝ) * B.W (t : ℝ) ω - a * (t : ℝ)) :=
    hg.comp (comap_measurable (fun ω => fun t : ℝ => B.W t ω))
  unfold Kyprianou.IndependentLevyItoComponents
  rw [iIndepFun_iff_iIndep]
  apply iIndep_of_iIndep_of_le hI
  intro i
  fin_cases i
  · simpa using hG.comap_le
  · simpa [mL, A] using hL.comap_le
  · simpa [mS, C] using hS.comap_le
