-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_upper_negative_start_payoff_zero_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T22:48:29.210661+00:00
-- url     : https://prove2.me/submissions/9e19978b-8344-48ef-9c44-66fa0f1fa2fb

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_positive_open_clock_eq_all_times
open MeasureTheory ProbabilityTheory Filter Set Topology
open AvramDividend.Classical Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (D : Kyprianou.Ch08.SpectrallyNegativeModel Ω P)
    {F : Filtration ℝ≥0 mΩ}
    (A : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hpaths : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, A.X t ω = D.X t ω)
    (q x a : ℝ) (hxneg : x < 0) :
    (fun ω => if Kyprianou.Ch08.tauPlus
          (Kyprianou.Ch08.StageB.shifted D.X x) a ω <
        Kyprianou.Ch08.tauMinus
          (Kyprianou.Ch08.StageB.shifted D.X x) 0 ω
      then Kyprianou.Ch08.discountedAt q
        (Kyprianou.Ch08.tauPlus
          (Kyprianou.Ch08.StageB.shifted D.X x) a ω)
      else 0) =ᵐ[P] 0 := by
  have key : ∀ m p : WithTop ℝ≥0,
      (∀ ε : ℝ≥0, 0 < ε → m ≤ (ε : WithTop ℝ≥0)) → p < m → False := by
    intro m p hub hlt
    revert hub hlt
    refine WithTop.recTopCoe ?_ ?_ m
    · intro hub hlt
      have hle := hub 1 one_pos
      have hcon : (⊤ : WithTop ℝ≥0) < ⊤ :=
        lt_of_le_of_lt hle (WithTop.coe_lt_top 1)
      exact absurd hcon (lt_irrefl _)
    · intro s hub hlt
      revert hlt
      refine WithTop.recTopCoe ?_ ?_ p
      · intro hlt
        have hcon : (⊤ : WithTop ℝ≥0) < ⊤ :=
          lt_trans hlt (WithTop.coe_lt_top s)
        exact absurd hcon (lt_irrefl _)
      · intro r hlt
        have hs : ∀ ε : ℝ≥0, 0 < ε → s ≤ ε :=
          fun ε hε => WithTop.coe_le_coe.mp (hub ε hε)
        have hs0 : s = 0 := by
          by_contra hne
          have hpos : 0 < s := pos_iff_ne_zero.mpr hne
          obtain ⟨ε, hε0, hεs⟩ := exists_between hpos
          exact (not_le_of_gt hεs) (hs ε hε0)
        rw [hs0] at hlt
        have hr : r < 0 := WithTop.coe_lt_coe.mp hlt
        exact (not_le_of_gt hr) (zero_le : (0 : ℝ≥0) ≤ r)
  filter_upwards [hpaths] with ω hω
  have hD0 : D.X 0 ω = 0 := by
    have h0 := hω 0
    rw [← h0]
    exact A.X_zero ω
  have hY0 : Kyprianou.Ch08.StageB.shifted D.X x 0 ω = x := by
    show x + D.X 0 ω = x
    rw [hD0, add_zero]
  have hY0lt : Kyprianou.Ch08.StageB.shifted D.X x 0 ω < 0 := by
    rw [hY0]
    exact hxneg
  have hcont : ContinuousWithinAt
      (fun s => Kyprianou.Ch08.StageB.shifted D.X x s ω) (Ici 0) 0 := by
    have hA := A.rightCont ω 0
    have heq : (fun s => Kyprianou.Ch08.StageB.shifted D.X x s ω)
        = fun s => x + A.X s ω := by
      funext s
      show x + D.X s ω = x + A.X s ω
      rw [← hω s]
    rw [heq]
    exact continuousWithinAt_const.add hA
  have hmem : Iio (0 : ℝ) ∈ 𝓝 (Kyprianou.Ch08.StageB.shifted D.X x 0 ω) :=
    isOpen_Iio.mem_nhds hY0lt
  have hev : ∀ᶠ u in 𝓝[Ici (0 : ℝ≥0)] 0,
      Kyprianou.Ch08.StageB.shifted D.X x u ω < 0 :=
    hcont.tendsto.eventually (p := fun y => y < 0)
      (eventually_of_mem hmem (fun y hy => hy))
  have hub : ∀ ε : ℝ≥0, 0 < ε →
      Kyprianou.Ch08.tauMinus (Kyprianou.Ch08.StageB.shifted D.X x) 0 ω ≤
        (ε : WithTop ℝ≥0) := by
    intro ε hε
    haveI := nhdsWithin_Ioi_neBot (show (0 : ℝ≥0) ≤ 0 from le_rfl)
    have hself : ∀ᶠ u in 𝓝[Ioi (0 : ℝ≥0)] 0, (0 : ℝ≥0) < u :=
      eventually_of_mem self_mem_nhdsWithin (fun u hu => hu)
    have hneg : ∀ᶠ u in 𝓝[Ioi (0 : ℝ≥0)] 0,
        Kyprianou.Ch08.StageB.shifted D.X x u ω < 0 :=
      hev.filter_mono (nhdsWithin_mono 0 Ioi_subset_Ici_self)
    have hsmall : ∀ᶠ u in 𝓝[Ioi (0 : ℝ≥0)] 0, u < ε :=
      eventually_nhdsWithin_of_eventually_nhds
        (eventually_of_mem (Iio_mem_nhds hε) (fun u hu => hu))
    obtain ⟨u, hu0, huε, huneg⟩ := (hself.and (hsmall.and hneg)).exists
    have hle : Kyprianou.Ch08.tauMinus (Kyprianou.Ch08.StageB.shifted D.X x) 0 ω ≤
        (u : WithTop ℝ≥0) :=
      sInf_le ⟨u, hu0, rfl, huneg⟩
    exact le_trans hle (WithTop.coe_le_coe.mpr (le_of_lt huε))
  have hcon : ¬ (Kyprianou.Ch08.tauPlus (Kyprianou.Ch08.StageB.shifted D.X x) a ω <
      Kyprianou.Ch08.tauMinus (Kyprianou.Ch08.StageB.shifted D.X x) 0 ω) :=
    fun hlt => key _ _ hub hlt
  exact if_neg hcon
