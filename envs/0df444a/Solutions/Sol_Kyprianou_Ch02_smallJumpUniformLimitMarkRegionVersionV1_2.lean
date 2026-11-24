-- Prove2me | solution 2 for Kyprianou.Ch02.smallJumpUniformLimitMarkRegionVersionV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:42:26.497835+00:00
-- url     : https://prove2.me/submissions/791aa8a4-1353-4dc5-9075-4f6f7e53f9c7

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

open Kyprianou Kyprianou.Ch02

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
  have hAll (k : ℕ) := huniform ((k : ℝ≥0) + 1) (by positivity)
  choose ε hanti hband hzero hu using hAll
  let k (t : ℝ≥0) : ℕ := ⌈(t : ℝ)⌉₊
  let F (n : ℕ) (t : ℝ≥0) (ω : Ω) :=
    Kyprianou.compensatedSmallJumpBand P levyMeasure N (ε (k t) n) t ω
  let Nfun : Ω → Measure (ℝ × ℝ) := N.N
  let S (ω : Ω) (t : ℝ≥0) := Filter.limsup (fun n => F n t ω) atTop
  refine ⟨S, ?_, ?_⟩
  · let mReg : MeasurableSpace Ω :=
      ⨆ C ∈ {C : Set (ℝ × ℝ) |
        C ⊆ ((Set.univ : Set ℝ) ×ˢ {x : ℝ | |x| < 1}) ∧ MeasurableSet C},
        MeasurableSpace.comap (fun ω => N.N ω C) inferInstance
    refine @measurable_pi_lambda Ω ℝ≥0 (fun _ => ℝ) mReg _ _ ?_
    intro t
    change Measurable[mReg] (fun ω => Filter.limsup (fun n => F n t ω) atTop)
    refine Measurable.limsup (mδ := mReg) ?_
    intro n
    let R : Set (ℝ × ℝ) :=
      Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | ε (k t) n ≤ |x| ∧ |x| < 1}
    have hR : MeasurableSet R := measurableSet_Ioc.prod
      ((measurableSet_le measurable_const continuous_abs.measurable).inter
       (measurableSet_lt continuous_abs.measurable measurable_const))
    have hm := @Kyprianou.Ch02.prmMarkedIntegralMeasurableLocalEvalSigmaV1 Ω mΩ
      P _ levyMeasure _ N R hR
    have hsub : R ⊆ (Set.univ : Set ℝ) ×ˢ {x : ℝ | |x| < 1} :=
      fun z hz => ⟨Set.mem_univ z.1, hz.2.2⟩
    have hm' : Measurable[mReg]
        (fun ω => ∫ z in R, z.2 ∂(Nfun ω)) := by
      apply hm.mono ?_ le_rfl
      dsimp [mReg]
      apply iSup_le
      intro C
      apply iSup_le
      intro hC
      exact le_iSup_of_le C (le_iSup_of_le ⟨hC.1.trans hsub, hC.2⟩ le_rfl)
    unfold F Kyprianou.compensatedSmallJumpBand
    exact hm'.sub measurable_const
  · have hAE := ae_all_iff.2 hu
    filter_upwards [hAE] with ω hω
    funext t
    have ht : t ≤ (k t : ℝ≥0) + 1 := by
      change (t : ℝ) ≤ (((k t : ℝ≥0) + 1 : ℝ≥0) : ℝ)
      push_cast
      have hh := Nat.le_ceil (t : ℝ)
      dsimp [k]
      linarith
    have hlim : Tendsto (fun n => F n t ω) atTop (nhds (M t ω)) := by
      apply Metric.tendsto_atTop.2
      intro δ hδ
      obtain ⟨n₀, hn₀⟩ := hω (k t) δ hδ
      exact ⟨n₀, fun n hn => by simpa [F, Real.dist_eq] using hn₀ n hn t ht⟩
    exact hlim.limsup_eq
