-- Prove2me | solution 1 for Kyprianou.Ch03.firstPassageTransform_zeroDiscount_strictBarrier
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T00:08:27.213877+00:00
-- url     : https://prove2.me/submissions/ae6a1712-011a-49e5-85a0-c943910ab524

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Theorems.Thm_Kyprianou_Ch03_firstPassageZero_consequence1

open MeasureTheory ProbabilityTheory AvramDividend.Classical Filter Set Topology
open scoped NNReal ENNReal

set_option autoImplicit false

namespace Kyprianou.Ch03

section ZeroDiscountStrictBarrier

/-! Measurability of upward first-passage times (spliced from the killed-subordinator proof). -/

private lemma firstHittingTime_Ioi_lt_coe_iff
    {Omega : Type} [MeasurableSpace Omega]
    {P : Measure Omega} {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (x a : NNReal) (ω : Omega) :
    firstHittingTime L.X (Set.Ioi (x : ℝ)) ω < (a : WithTop NNReal) ↔
      ∃ q : ℚ, 0 < q ∧ (q : ℝ) < (a : ℝ) ∧ (x : ℝ) < L.X (Real.toNNReal (q : ℝ)) ω := by
  constructor
  · intro hlt
    unfold firstHittingTime at hlt
    rcases sInf_lt_iff.mp hlt with ⟨_, ⟨t, ⟨htpos, htx⟩, rfl⟩, hta⟩
    have hta' : (t : ℝ) < (a : ℝ) := by exact_mod_cast (WithTop.coe_lt_coe.mp hta)
    have hrc := L.rightCont ω t
    have hmem : Set.Ioi (x : ℝ) ∈ 𝓝 (L.X t ω) := isOpen_Ioi.mem_nhds htx
    have hev : ∀ᶠ s in 𝓝[Set.Ici t] t, (x : ℝ) < L.X s ω := hrc.eventually hmem
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
    rcases hev with ⟨δ, hδpos, hδ⟩
    let u : ℝ := min (a : ℝ) ((t : ℝ) + δ)
    have htu : (t : ℝ) < u := lt_min hta' (by linarith)
    rcases exists_rat_btwn htu with ⟨q, htq, hqu⟩
    have hq_pos : (0 : ℚ) < q := by
      have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast htpos
      have : (0 : ℝ) < (q : ℝ) := lt_trans ht0 htq
      exact_mod_cast this
    have hq_lt_a : (q : ℝ) < (a : ℝ) := lt_of_lt_of_le hqu (min_le_left _ _)
    have hq_nn_ge : t ≤ Real.toNNReal (q : ℝ) := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (le_of_lt (by exact_mod_cast hq_pos))]
      exact le_of_lt htq
    have hq_dist : dist (Real.toNNReal (q : ℝ)) t < δ := by
      rw [NNReal.dist_eq, Real.coe_toNNReal _ (le_of_lt (by exact_mod_cast hq_pos)),
        abs_of_nonneg (by linarith)]
      have : (q : ℝ) < (t : ℝ) + δ := lt_of_lt_of_le hqu (min_le_right _ _)
      linarith
    exact ⟨q, hq_pos, hq_lt_a, hδ hq_dist hq_nn_ge⟩
  · rintro ⟨q, hqpos, hqa, hqx⟩
    unfold firstHittingTime
    have hqnn_pos : (0 : NNReal) < Real.toNNReal (q : ℝ) :=
      Real.toNNReal_pos.mpr (by exact_mod_cast hqpos)
    have hqnn_lt : Real.toNNReal (q : ℝ) < a := by
      rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ (le_of_lt (by exact_mod_cast hqpos))]
      exact hqa
    exact lt_of_le_of_lt
      (sInf_le ⟨Real.toNNReal (q : ℝ), ⟨hqnn_pos, hqx⟩, rfl⟩)
      (WithTop.coe_lt_coe.mpr hqnn_lt)

private lemma measurable_firstHittingTime_Ioi
    {Omega : Type} [MeasurableSpace Omega]
    {P : Measure Omega} {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F) (x : NNReal) :
    Measurable (fun ω : Omega => firstHittingTime L.X (Set.Ioi (x : ℝ)) ω) := by
  have hlt : ∀ a : NNReal,
      MeasurableSet {ω : Omega | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω < (a : WithTop NNReal)} := by
    intro a
    have hEq :
        {ω : Omega | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω < (a : WithTop NNReal)} =
          ⋃ q : {q : ℚ // 0 < q ∧ (q : ℝ) < (a : ℝ)},
            {ω : Omega | (x : ℝ) < L.X (Real.toNNReal (q.1 : ℝ)) ω} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Subtype.exists]
      simpa [and_assoc] using firstHittingTime_Ioi_lt_coe_iff L x a ω
    rw [hEq]
    refine MeasurableSet.iUnion fun q => ?_
    have hmeasX : Measurable (L.X (Real.toNNReal (q.1 : ℝ))) :=
      (L.adapted (Real.toNNReal (q.1 : ℝ))).mono (F.le _) le_rfl
    exact measurableSet_lt measurable_const hmeasX
  have hlt_top : ∀ b : WithTop NNReal,
      MeasurableSet {ω : Omega | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω < b} := by
    intro b
    cases b with
    | top =>
      have hEq :
          {ω : Omega | firstHittingTime L.X (Set.Ioi (x : ℝ)) ω < (⊤ : WithTop NNReal)} =
            ⋃ n : ℕ, {ω : Omega |
              firstHittingTime L.X (Set.Ioi (x : ℝ)) ω < ((n : NNReal) : WithTop NNReal)} := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
        constructor
        · intro h
          rcases WithTop.ne_top_iff_exists.mp (WithTop.lt_top_iff_ne_top.mp h) with ⟨t, ht⟩
          rw [← ht]
          rcases exists_nat_gt (t : ℝ) with ⟨n, hn⟩
          refine ⟨n, WithTop.coe_lt_coe.mpr ?_⟩
          exact_mod_cast hn
        · rintro ⟨n, hn⟩
          exact lt_trans hn (WithTop.coe_lt_top _)
      rw [hEq]
      exact MeasurableSet.iUnion fun n => hlt (n : NNReal)
    | coe a => exact hlt a
  exact measurable_of_Iio hlt_top

private lemma measurable_firstHittingTime_Ioi_real
    {Omega : Type} [MeasurableSpace Omega]
    {P : Measure Omega} {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    {x : ℝ} (hx : 0 ≤ x) :
    Measurable (fun ω : Omega => firstHittingTime L.X (Set.Ioi x) ω) := by
  have hx_coe : (Real.toNNReal x : ℝ) = x := Real.coe_toNNReal x hx
  simpa [hx_coe] using measurable_firstHittingTime_Ioi L (Real.toNNReal x)

end ZeroDiscountStrictBarrier

end Kyprianou.Ch03

open Kyprianou.Ch03 in
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotDecreasing : ¬ (∀ᵐ omega : Omega ∂ P,
      Antitone (fun t : NNReal => L.X t omega))) :
    forall (q : Real), q = 0 ->
          forall phi : Real,
      (0 <= phi ∧ L.ψ phi = q ∧ (forall theta : Real, 0 <= theta ->
          L.ψ theta = q -> theta <= phi)) ->
      (forall (x : Real), 0 < x ->
          forall (finiteTime : Omega -> NNReal),
            (forall omega,
              firstHittingTime L.X (Set.Ioi x) omega != ⊤ ->
                firstHittingTime L.X (Set.Ioi x) omega =
                  (finiteTime omega : WithTop NNReal)) ->
            (∫ omega,
              if firstHittingTime L.X (Set.Ioi x) omega = ⊤
              then (0 : Real)
              else Real.exp (-q * (finiteTime omega : Real)) ∂P) =
              Real.exp (-phi * x)) := by
  intro q hq phi hphi x hx finiteTime hfin
  subst hq
  have hx0 : 0 ≤ x := hx.le
  -- With q = 0 the integrand is the indicator of {τ_x⁺ < ∞}.
  let S : Set Omega := {ω : Omega | firstHittingTime L.X (Set.Ioi x) ω ≠ ⊤}
  have hSmeas : MeasurableSet S :=
    (measurable_firstHittingTime_Ioi_real L hx0) (MeasurableSet.singleton (⊤ : WithTop NNReal)).compl
  have hind :
      (fun ω : Omega =>
        if firstHittingTime L.X (Set.Ioi x) ω = ⊤
        then (0 : ℝ)
        else Real.exp (-(0 : ℝ) * (finiteTime ω : ℝ))) =
      S.indicator (fun _ => (1 : ℝ)) := by
    ext ω
    by_cases htop : firstHittingTime L.X (Set.Ioi x) ω = ⊤
    · simp [htop, S, Set.indicator_of_notMem]
    · simp [htop, S, Set.indicator_of_mem, Real.exp_zero]
  rw [hind, integral_indicator hSmeas]
  have hInt : ∫ _ω in S, (1 : ℝ) ∂P = (P S).toReal := by
    rw [integral_const, smul_eq_mul, Measure.real, Measure.restrict_apply_univ, mul_one]
  rw [hInt]
  -- Passage probability equals e^{-φ x} by the already-proved zero-discount consequence.
  have hphi0 : 0 ≤ phi ∧ L.ψ phi = 0 ∧
      (∀ theta : ℝ, 0 ≤ theta → L.ψ theta = 0 → theta ≤ phi) := hphi
  have hS_eq : S = {ω : Omega | (firstHittingTime L.X (Set.Ioi x) ω != ⊤) = true} := by
    ext ω
    simp only [S, mem_setOf_eq, bne_iff_ne, decide_eq_true_iff]
  rw [hS_eq]
  exact firstPassageZero_consequence1 P F L hNotDecreasing phi hphi0 x hx0 finiteTime hfin
