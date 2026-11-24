-- Prove2me | solution 1 for Kyprianou.Ch02.smallJumpUniformLimitMarkRegionVersionV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:41:12.474822+00:00
-- url     : https://prove2.me/submissions/0d0922b0-7ea8-4593-832d-e2d4793961e2

import Theorems.Thm_Kyprianou_Ch02_measurableRealSequenceLimitVersionCh02V1
import Theorems.Thm_Kyprianou_Ch02_prmMarkedIntegralMeasurableLocalEvalSigmaV1
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
    (M : ℝ≥0 → Ω → ℝ)
    (huniform :
      ∀ T : ℝ≥0, 0 < T →
        ∃ ε : ℕ → ℝ,
          StrictAnti ε ∧
          (∀ n, 0 < ε n ∧ ε n < 1) ∧
          Tendsto ε Filter.atTop (nhds 0) ∧
          (∀ᵐ ω ∂P, ∀ δ : ℝ, 0 < δ →
            ∃ n₀ : ℕ, ∀ n ≥ n₀,
              ∀ t : ℝ≥0, t ≤ T →
                |Kyprianou.compensatedSmallJumpBand P levyMeasure N (ε n) t ω -
                    M t ω| < δ)) :
    ∃ S : Ω → ℝ≥0 → ℝ,
      Measurable[(⨆ C ∈ {C : Set (ℝ × ℝ) |
        C ⊆ ((Set.univ : Set ℝ) ×ˢ {x : ℝ | |x| < 1}) ∧ MeasurableSet C},
        MeasurableSpace.comap (fun ω => N.N ω C) inferInstance)] S ∧
      S =ᵐ[P] (fun ω t => M t ω) := by
  classical
  let m : MeasurableSpace Ω :=
    ⨆ C ∈ {C : Set (ℝ × ℝ) | C ⊆ ((Set.univ : Set ℝ) ×ˢ
      {x : ℝ | |x| < 1}) ∧ MeasurableSet C},
        MeasurableSpace.comap (fun ω => N.N ω C) inferInstance
  letI : MeasurableSpace Ω := mΩ
  choose ε hanti hε hzero hlim using
    fun k : ℕ => huniform ((k : ℝ≥0) + 1) (by positivity)
  have H (k : ℕ) (t : ℝ≥0) : ∃ g : Ω → ℝ, Measurable[m] g ∧
      ∀ ω l, Tendsto (fun n =>
        Kyprianou.compensatedSmallJumpBand P levyMeasure N (ε k n) t ω)
        atTop (nhds l) → g ω = l := by
    let F : ℕ → Ω → ℝ := fun n =>
      Kyprianou.compensatedSmallJumpBand P levyMeasure N (ε k n) t
    have hF (n : ℕ) : Measurable[m] (F n) := by
      let R : Set (ℝ × ℝ) := Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ
        {x : ℝ | ε k n ≤ |x| ∧ |x| < 1}
      have hR : MeasurableSet R := measurableSet_Ioc.prod
        ((measurableSet_le measurable_const continuous_abs.measurable).inter
          (measurableSet_lt continuous_abs.measurable measurable_const))
      have hsub : R ⊆ ((Set.univ : Set ℝ) ×ˢ {x : ℝ | |x| < 1}) :=
        Set.prod_mono (Set.subset_univ _) (fun _ hx => hx.2)
      have hm := Kyprianou.Ch02.prmMarkedIntegralMeasurableLocalEvalSigmaV1
        P levyMeasure N R hR
      have hm' : Measurable[m] (fun ω => ∫ z in R, z.2 ∂(N.N ω)) := by
        refine hm.mono ?_ le_rfl
        refine iSup_le (fun C => iSup_le (fun hC => ?_))
        exact le_iSup_of_le C (le_iSup_of_le ⟨hC.1.trans hsub, hC.2⟩ le_rfl)
      exact hm'.sub_const _
    exact @Kyprianou.Ch02.measurableRealSequenceLimitVersionCh02V1 Ω m F hF
  choose g hg hversion using H
  let S : Ω → ℝ≥0 → ℝ := fun ω t => g ⌈(t : ℝ)⌉₊ t ω
  refine ⟨S, @measurable_pi_lambda Ω ℝ≥0 (fun _ => ℝ) m
    (fun _ => inferInstance) S (fun t => hg _ t), ?_⟩
  have hall := ae_all_iff.2 hlim
  filter_upwards [hall] with ω hw
  funext t
  let k : ℕ := ⌈(t : ℝ)⌉₊
  have ht0 : t ≤ (k : ℝ≥0) := by
    exact_mod_cast (Nat.le_ceil (t : ℝ))
  have ht : t ≤ (k : ℝ≥0) + 1 := le_trans ht0 (by simp)
  change g k t ω = M t ω
  apply hversion k t
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨n₀, hn₀⟩ := hw k δ hδ
  refine ⟨n₀, fun n hn => ?_⟩
  simpa only [Real.dist_eq] using hn₀ n hn t ht
