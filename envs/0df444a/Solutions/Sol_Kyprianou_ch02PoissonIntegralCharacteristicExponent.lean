-- Prove2me | solution 1 for Kyprianou.ch02PoissonIntegralCharacteristicExponent
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T07:36:30.831732+00:00
-- url     : https://prove2.me/submissions/119b03f2-7171-48f0-bc68-0d59591015c4

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

namespace AuxK2

variable {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] {P : Measure Ω} [IsProbabilityMeasure P]
    {m : Measure E} [SigmaFinite m]
    {K : ℕ → Ω → ℕ} {Y : ℕ → ℕ → Ω → E}

theorem hasSum_pieces {g : E → ℝ} (hi : Integrable g m) :
    HasSum (fun k => ∫ x in prmPiece m k, g x ∂m) (∫ x, g x ∂m) := by
  have h := hasSum_integral_iUnion (μ := m) (f := g) (s := prmPiece m)
    (fun k => measurableSet_prmPiece) pairwise_disjoint_prmPiece
    (by rw [iUnion_prmPiece]; exact hi.integrableOn)
  rwa [iUnion_prmPiece, Measure.restrict_univ] at h

theorem fin (hd : IsPoissonPointFamily K Y m P) {g : E → ℝ} (hg : Measurable g)
    (hi : ∀ k, Integrable g (m.restrict (prmPiece m k)))
    (hi2 : ∀ k, Integrable (fun x => g x ^ 2) (m.restrict (prmPiece m k))) (n : ℕ) :
    ∫ ω, (∑ k ∈ Finset.range n, pieceSum K Y g k ω) ^ 2 ∂P
      = (∑ k ∈ Finset.range n, ∫ x in prmPiece m k, g x ^ 2 ∂m)
        + (∑ k ∈ Finset.range n, ∫ x in prmPiece m k, g x ∂m) ^ 2 := by
  have hmeas : ∀ k, Measurable (pieceSum K Y g k) := fun k =>
    measurable_pieceSum (hd.measurable_count k) (hd.measurable_point k) hg
  have hL2 : ∀ k, MemLp (pieceSum K Y g k) 2 P := fun k =>
    (memLp_two_iff_integrable_sq (hmeas k).aestronglyMeasurable).2
      (integrable_sq_pieceSum hd hg (hi k) (hi2 k))
  simp_rw [sq, Finset.sum_mul_sum]
  rw [integral_finset_sum (Finset.range n)
    (f := fun i ω => ∑ j ∈ Finset.range n, pieceSum K Y g i ω * pieceSum K Y g j ω)
    (fun i _ => integrable_finset_sum _ fun j _ => (hL2 i).integrable_mul (hL2 j))]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finset_sum (Finset.range n)
    (f := fun j ω => pieceSum K Y g i ω * pieceSum K Y g j ω)
    (fun j _ => (hL2 i).integrable_mul (hL2 j))]
  have e : ∀ j ∈ Finset.range n, ∫ ω, pieceSum K Y g i ω * pieceSum K Y g j ω ∂P
      = (∫ x in prmPiece m i, g x ∂m) * (∫ x in prmPiece m j, g x ∂m)
        + if i = j then ∫ x in prmPiece m i, g x * g x ∂m else 0 := by
    intro j _
    by_cases h : i = j
    · subst h
      have := integral_sq_pieceSum (k := i) hd hg (hi _) (hi2 _)
      simp only [sq] at this
      rw [this, if_pos rfl]; ring
    · have hI := (indepFun_pieceSum_pieceSum hd hg hg h).integral_mul_eq_mul_integral
          (hmeas i).aestronglyMeasurable (hmeas j).aestronglyMeasurable
      simp only [Pi.mul_apply] at hI
      rw [if_neg h, add_zero, hI,
        integral_pieceSum hd hg (hi _), integral_pieceSum hd hg (hi _)]
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_ite_eq, if_pos ‹_›, add_comm]

/-- integral against the random measure, when the absolute piece sums are summable. -/
theorem pointwise {f : E → ℝ} (hf : Measurable f) (ω : Ω)
    (hW : ∑' k, ENNReal.ofReal (pieceSum K Y (fun x => |f x|) k ω) ≠ ∞) :
    Integrable f (poissonRandomMeasure K Y ω) ∧
    ∫ x, f x ∂(poissonRandomMeasure K Y ω) = ∑' k, pieceSum K Y f k ω := by
  classical
  have hdir : ∀ k n, ∫⁻ x, ‖f x‖ₑ ∂(if n < K k ω then Measure.dirac (Y k n ω) else 0)
      = if n < K k ω then ENNReal.ofReal (|f (Y k n ω)|) else 0 := by
    intro k n
    split_ifs
    · rw [lintegral_dirac' _ hf.enorm, Real.enorm_eq_ofReal_abs]
    · simp
  have hk : ∀ k, ∫⁻ x, ‖f x‖ₑ ∂(Measure.sum fun n =>
      if n < K k ω then Measure.dirac (Y k n ω) else (0 : Measure E))
      = ENNReal.ofReal (pieceSum K Y (fun x => |f x|) k ω) := by
    intro k
    rw [lintegral_sum_measure]
    simp_rw [hdir]
    rw [tsum_eq_sum (s := Finset.range (K k ω)) (fun n hn => by
      rw [if_neg (by simpa using hn)]), pieceSum,
      ENNReal.ofReal_sum_of_nonneg (fun n _ => abs_nonneg _)]
    exact Finset.sum_congr rfl fun n hn => if_pos (by simpa using hn)
  have hint : Integrable f (poissonRandomMeasure K Y ω) := by
    refine ⟨hf.aestronglyMeasurable, ?_⟩
    show ∫⁻ x, ‖f x‖ₑ ∂(poissonRandomMeasure K Y ω) < ∞
    rw [poissonRandomMeasure, lintegral_sum_measure]
    simp_rw [hk]
    exact lt_top_iff_ne_top.2 hW
  refine ⟨hint, ?_⟩
  rw [poissonRandomMeasure, integral_sum_measure hint]
  refine tsum_congr fun k => ?_
  have hik := hint.mono_measure (Measure.le_sum _ k)
  rw [integral_sum_measure hik]
  rw [tsum_eq_sum (s := Finset.range (K k ω)) (fun n hn => by
      rw [if_neg (by simpa using hn)]; simp), pieceSum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [if_pos (by simpa using hn), integral_dirac' _ _ hf.stronglyMeasurable]

end AuxK2


namespace AuxIC
variable {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] {P : Measure Ω} [IsProbabilityMeasure P]
    {m : Measure E} [SigmaFinite m]
    {K : ℕ → Ω → ℕ} {Y : ℕ → ℕ → Ω → E}

theorem lsum {h : E → ℝ≥0∞} (hh : Measurable h) (ω : Ω) :
    ∫⁻ x, h x ∂(poissonRandomMeasure K Y ω)
      = ∑' k, ∑ n ∈ Finset.range (K k ω), h (Y k n ω) := by
  classical
  rw [poissonRandomMeasure, lintegral_sum_measure]
  refine tsum_congr fun k => ?_
  rw [lintegral_sum_measure, tsum_eq_sum (s := Finset.range (K k ω)) (fun n hn => by
      rw [if_neg (by simpa using hn)]; simp)]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [if_pos (by simpa using hn), lintegral_dirac' _ hh]

theorem lsum_real {g : E → ℝ} (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x) (ω : Ω) :
    ∫⁻ x, ENNReal.ofReal (g x) ∂(poissonRandomMeasure K Y ω)
      = ∑' k, ENNReal.ofReal (pieceSum K Y g k ω) := by
  rw [lsum hg.ennreal_ofReal]
  refine tsum_congr fun k => ?_
  rw [pieceSum, ENNReal.ofReal_sum_of_nonneg fun n _ => hg0 _]

theorem piece_int {g : E → ℝ} (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1)
    (k : ℕ) : Integrable g (m.restrict (prmPiece m k)) := by
  haveI : IsFiniteMeasure (m.restrict (prmPiece m k)) :=
    isFiniteMeasure_restrict.2 measure_prmPiece_lt_top.ne
  exact Integrable.of_bound hg.aestronglyMeasurable 1 (Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 x)]; exact hg1 x)

theorem lint_pieces {g : E → ℝ} (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1) :
    ∫⁻ x, ENNReal.ofReal (g x) ∂m = ∑' k, ENNReal.ofReal (∫ x in prmPiece m k, g x ∂m) := by
  rw [← setLIntegral_univ, ← iUnion_prmPiece (m := m),
    lintegral_iUnion (fun k => measurableSet_prmPiece) pairwise_disjoint_prmPiece]
  refine tsum_congr fun k => ?_
  rw [ofReal_integral_eq_lintegral_ofReal (piece_int hg hg0 hg1 k)
    (Eventually.of_forall hg0)]

end AuxIC

namespace Kyprianou
theorem AuxIC.crit
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (f : E → ℝ) (hf : Measurable f) :
    ((∀ᵐ ω ∂P,
      Integrable f (ProbabilityTheory.poissonRandomMeasure K Y ω)) ↔
      Integrable (fun x => min (1 : ℝ) |f x|) m) := by
  classical
  set g : E → ℝ := fun x => min (1 : ℝ) |f x| with hgdef
  have hg : Measurable g := measurable_const.min (continuous_abs.measurable.comp hf)
  have hg0 : ∀ x, 0 ≤ g x := fun x => le_min zero_le_one (abs_nonneg _)
  have hg1 : ∀ x, g x ≤ 1 := fun x => min_le_left _ _
  have hSm : ∀ k, Measurable (pieceSum K Y g k) := fun k =>
    measurable_pieceSum (hd.measurable_count k) (hd.measurable_point k) hg
  have hS0 : ∀ k ω, 0 ≤ pieceSum K Y g k ω := fun k ω =>
    Finset.sum_nonneg fun _ _ => hg0 _
  have hint_iff : ∀ ω, Integrable f (poissonRandomMeasure K Y ω) ↔
      ∫⁻ x, ‖f x‖ₑ ∂(poissonRandomMeasure K Y ω) < ∞ :=
    fun ω => ⟨fun h => h.2, fun h => ⟨hf.aestronglyMeasurable, h⟩⟩
  have hgi_iff : Integrable g m ↔ ∫⁻ x, ENNReal.ofReal (g x) ∂m < ∞ := by
    constructor
    · intro h
      have := h.2
      unfold HasFiniteIntegral at this
      simpa [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hg0 _)] using this
    · intro h
      refine ⟨hg.aestronglyMeasurable, ?_⟩
      show ∫⁻ x, ‖g x‖ₑ ∂m < ∞
      simpa [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hg0 _)] using h
  have hpi : ∀ k, Integrable g (m.restrict (prmPiece m k)) := AuxIC.piece_int hg hg0 hg1
  have hpi2 : ∀ k, Integrable (fun x => g x ^ 2) (m.restrict (prmPiece m k)) :=
    AuxIC.piece_int (g := fun x => g x ^ 2) (hg.pow_const 2) (fun x => sq_nonneg _)
      (fun x => by nlinarith [hg0 x, hg1 x])
  have hL2 : ∀ k, MemLp (pieceSum K Y g k) 2 P := fun k =>
    (memLp_two_iff_integrable_sq (hSm k).aestronglyMeasurable).2
      (integrable_sq_pieceSum hd hg (hpi k) (hpi2 k))
  set W : Ω → ℝ≥0∞ := fun ω => ∫⁻ x, ENNReal.ofReal (g x) ∂(poissonRandomMeasure K Y ω) with hW
  have hWe : ∀ ω, W ω = ∑' k, ENNReal.ofReal (pieceSum K Y g k ω) := fun ω =>
    AuxIC.lsum_real hg hg0 ω
  have hWm : Measurable W := by
    have : W = fun ω => ∑' k, ENNReal.ofReal (pieceSum K Y g k ω) := funext hWe
    rw [this]; exact Measurable.ennreal_tsum fun k => (hSm k).ennreal_ofReal
  simp_rw [hint_iff, hgi_iff]
  constructor
  · -- necessity: Chebyshev on partial piece sums
    intro hae
    by_contra hinf
    rw [not_lt, top_le_iff, AuxIC.lint_pieces hg hg0 hg1, ENNReal.tsum_eq_iSup_nat] at hinf
    set a : ℕ → ℝ := fun k => ∫ x in prmPiece m k, g x ∂m with ha
    have ha0 : ∀ k, 0 ≤ a k := fun k => setIntegral_nonneg measurableSet_prmPiece
      fun x _ => hg0 x
    set A : ℕ → ℝ := fun M => ∑ k ∈ Finset.range M, a k with hA
    have hA0 : ∀ M, 0 ≤ A M := fun M => Finset.sum_nonneg fun k _ => ha0 k
    have hunb : ∀ c : ℝ, ∃ M, c < A M := by
      intro c
      have : ENNReal.ofReal c < ⨆ M, ∑ k ∈ Finset.range M, ENNReal.ofReal (a k) := by
        rw [hinf]; exact ENNReal.ofReal_lt_top
      obtain ⟨M, hM⟩ := lt_iSup_iff.1 this
      refine ⟨M, ?_⟩
      rw [← ENNReal.ofReal_sum_of_nonneg fun k _ => ha0 k] at hM
      exact (ENNReal.ofReal_lt_ofReal_iff'.1 hM).1
    set T : ℕ → Ω → ℝ := fun M ω => ∑ k ∈ Finset.range M, pieceSum K Y g k ω with hT
    have hTm : ∀ M, Measurable (T M) := fun M => Finset.measurable_sum _ fun k _ => hSm k
    have hTL2 : ∀ M, MemLp (T M) 2 P := fun M => memLp_finset_sum _ fun k _ => hL2 k
    have hET : ∀ M, ∫ ω, T M ω ∂P = A M := by
      intro M
      rw [integral_finset_sum _ fun k _ => (hL2 k).integrable one_le_two]
      exact Finset.sum_congr rfl fun k _ => integral_pieceSum hd hg (AuxIC.piece_int hg hg0 hg1 k)
    -- variance bound
    have hvar : ∀ M, ∫ ω, (T M ω - A M) ^ 2 ∂P ≤ A M := by
      intro M
      have hT2 : ∫ ω, T M ω ^ 2 ∂P = (∑ k ∈ Finset.range M, ∫ x in prmPiece m k, g x ^ 2 ∂m)
          + A M ^ 2 := AuxK2.fin hd hg hpi hpi2 M
      have e : (fun ω => (T M ω - A M) ^ 2) = fun ω => (T M ω ^ 2 - 2 * A M * T M ω) + A M ^ 2 := by
        funext ω; ring
      rw [e, integral_add (f := fun ω => T M ω ^ 2 - 2 * A M * T M ω) (g := fun _ => A M ^ 2) ((hTL2 M).integrable_sq.sub (((hTL2 M).integrable one_le_two).const_mul _))
        (integrable_const _), integral_sub (f := fun ω => T M ω ^ 2)
        (g := fun ω => 2 * A M * T M ω) (hTL2 M).integrable_sq
        (((hTL2 M).integrable one_le_two).const_mul _), integral_const_mul, hT2, hET,
        integral_const, smul_eq_mul, probReal_univ, one_mul]
      have hv : ∑ k ∈ Finset.range M, ∫ x in prmPiece m k, g x ^ 2 ∂m ≤ A M :=
        Finset.sum_le_sum fun k _ => setIntegral_mono (hpi2 k) (hpi k)
          fun x => by nlinarith [hg0 x, hg1 x]
      linarith
    have hcheb : ∀ M, 0 < A M → P.real {ω | T M ω ≤ A M / 2} ≤ 4 / A M := by
      intro M hAp
      have hsub : {ω | T M ω ≤ A M / 2} ⊆ {ω | (A M / 2) ^ 2 ≤ (T M ω - A M) ^ 2} := by
        intro ω hω
        simp only [Set.mem_setOf_eq] at hω ⊢
        nlinarith
      have hmk := mul_meas_ge_le_integral_of_nonneg (μ := P)
        (Eventually.of_forall fun ω => sq_nonneg (T M ω - A M))
        (((hTL2 M).sub (memLp_const (A M))).integrable_sq) ((A M / 2) ^ 2)
      have h1 := measureReal_mono (μ := P) hsub
      have h2 : (A M / 2) ^ 2 * P.real {ω | T M ω ≤ A M / 2} ≤ A M :=
        ((mul_le_mul_of_nonneg_left h1 (sq_nonneg _)).trans hmk).trans (by
          have := hvar M; simpa [Pi.sub_apply] using this)
      rw [le_div_iff₀ hAp]
      nlinarith [measureReal_nonneg (μ := P) (s := {ω | T M ω ≤ A M / 2})]
    have hWT : ∀ M ω, ENNReal.ofReal (T M ω) ≤ W ω := by
      intro M ω
      rw [hWe, hT, ENNReal.ofReal_sum_of_nonneg fun k _ => hS0 k ω]
      exact ENNReal.sum_le_tsum _
    have hnull : ∀ c : ℕ, P {ω | W ω ≤ c} = 0 := by
      intro c
      have hreal : P.real {ω | W ω ≤ c} = 0 := by
        refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) measureReal_nonneg
        obtain ⟨M, hM⟩ := hunb (max (2 * c) (4 / ε))
        have hAp : 0 < A M := lt_of_le_of_lt (le_max_of_le_right (by positivity)) hM
        have hsub : {ω | W ω ≤ c} ⊆ {ω | T M ω ≤ A M / 2} := by
          intro ω hω
          simp only [Set.mem_setOf_eq] at hω ⊢
          have h1 := (hWT M ω).trans hω
          have h2 : T M ω ≤ c := by
            rw [← ENNReal.ofReal_natCast] at h1
            exact (ENNReal.ofReal_le_ofReal_iff (Nat.cast_nonneg c)).1 h1
          have := le_max_left (2 * (c : ℝ)) (4 / ε)
          linarith
        have h3 := (measureReal_mono (μ := P) hsub).trans (hcheb M hAp)
        have h4 : 4 / A M < ε := by
          rw [div_lt_iff₀ hAp]
          have := le_max_right (2 * (c : ℝ)) (4 / ε)
          have h5 : 4 / ε < A M := lt_of_le_of_lt this hM
          rw [div_lt_iff₀ hε] at h5
          linarith
        linarith
      exact (measureReal_eq_zero_iff).1 hreal
    have hWfin : ∀ᵐ ω ∂P, W ω < ∞ := by
      filter_upwards [hae] with ω hω
      refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hω
      rw [Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_ofReal (min_le_right _ _)
    have hall : ∀ᵐ ω ∂P, ∀ c : ℕ, ¬ (W ω ≤ c) :=
      ae_all_iff.2 fun c => by
        rw [ae_iff]; simpa using hnull c
    have hfalse : ∀ᵐ ω ∂P, False := by
      filter_upwards [hall, hWfin] with ω h1 h2
      obtain ⟨c, hc⟩ := ENNReal.exists_nat_gt h2.ne
      exact h1 c hc.le
    have := (Filter.eventually_false_iff_eq_bot.1 hfalse)
    rw [ae_eq_bot] at this
    exact (IsProbabilityMeasure.ne_zero P) this
  · -- sufficiency
    intro hfin
    have hEW : ∫⁻ ω, W ω ∂P < ∞ := by
      simp_rw [hWe]
      rw [lintegral_tsum fun k => (hSm k).ennreal_ofReal.aemeasurable]
      have e : ∀ k, ∫⁻ ω, ENNReal.ofReal (pieceSum K Y g k ω) ∂P
          = ENNReal.ofReal (∫ x in prmPiece m k, g x ∂m) := by
        intro k
        rw [← ofReal_integral_eq_lintegral_ofReal ((hL2 k).integrable one_le_two)
          (Eventually.of_forall (hS0 k)), integral_pieceSum hd hg (hpi k)]
      simp_rw [e]
      rw [← AuxIC.lint_pieces hg hg0 hg1]
      exact hfin
    have hWae : ∀ᵐ ω ∂P, W ω < ∞ := ae_lt_top hWm hEW.ne
    set L : Set E := {x | 1 < |f x|} with hL
    have hLm : MeasurableSet L := measurableSet_lt measurable_const
      (continuous_abs.measurable.comp hf)
    have hmL : m L < ∞ := by
      refine lt_of_le_of_lt ?_ hfin
      rw [← lintegral_indicator_one hLm]
      refine lintegral_mono fun x => ?_
      by_cases hx : x ∈ L
      · rw [Set.indicator_of_mem hx, Pi.one_apply]
        have : g x = 1 := min_eq_left (le_of_lt hx)
        rw [this, ENNReal.ofReal_one]
      · rw [Set.indicator_of_notMem hx]; exact bot_le
    filter_upwards [hWae, ae_poissonRandomMeasure_apply_lt_top hd hLm hmL] with ω hω hNL
    have hb : ∀ x, ‖f x‖ₑ ≤ ENNReal.ofReal (g x) + L.indicator (fun x => ‖f x‖ₑ) x := by
      intro x
      by_cases hx : x ∈ L
      · rw [Set.indicator_of_mem hx]; exact le_add_self
      · rw [Set.indicator_of_notMem hx, add_zero, Real.enorm_eq_ofReal_abs]
        simp only [hL, Set.mem_setOf_eq, not_lt] at hx
        exact ENNReal.ofReal_le_ofReal (le_min hx le_rfl)
    refine lt_of_le_of_lt (lintegral_mono hb) ?_
    rw [lintegral_add_left hg.ennreal_ofReal]
    refine ENNReal.add_lt_top.2 ⟨hω, ?_⟩
    rw [AuxIC.lsum (hf.enorm.indicator hLm)]
    rw [← lintegral_indicator_one hLm, AuxIC.lsum (measurable_one.indicator hLm)] at hNL
    have hS := ENNReal.finite_const_le_of_tsum_ne_top hNL.ne one_ne_zero
    rw [tsum_eq_sum (s := hS.toFinset) (fun k hk => ?_)]
    · exact ENNReal.sum_lt_top.2 fun k _ => ENNReal.sum_lt_top.2 fun n _ => by
        by_cases hx : Y k n ω ∈ L
        · rw [Set.indicator_of_mem hx]; exact enorm_lt_top
        · rw [Set.indicator_of_notMem hx]; exact ENNReal.zero_lt_top
    · simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_le] at hk
      refine Finset.sum_eq_zero fun n hn => ?_
      have hx : Y k n ω ∉ L := by
        intro hx
        have := Finset.single_le_sum (f := fun n => L.indicator (1 : E → ℝ≥0∞) (Y k n ω))
          (fun _ _ => bot_le) hn
        rw [Set.indicator_of_mem hx, Pi.one_apply] at this
        exact absurd (lt_of_le_of_lt this hk) (lt_irrefl _)
      rw [Set.indicator_of_notMem hx]

end Kyprianou

namespace AuxCE
variable {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] {P : Measure Ω} [IsProbabilityMeasure P]
    {m : Measure E} [SigmaFinite m]
    {K : ℕ → Ω → ℕ} {Y : ℕ → ℕ → Ω → E}

theorem indep_prefix (hd : IsPoissonPointFamily K Y m P) (M : ℕ) :
    IndepFun (fun ω => (K M ω, fun n => Y M n ω))
      (fun ω (j : Fin M) => (K j ω, fun n => Y j n ω)) P := by
  set φ : Unit ⊕ ℕ → ℕ ⊕ ℕ × ℕ := Sum.elim (fun _ => Sum.inl M) (fun n => Sum.inr (M, n)) with hφ
  set ψ : Fin M × (Unit ⊕ ℕ) → ℕ ⊕ ℕ × ℕ := fun p =>
    Sum.elim (fun _ => Sum.inl (p.1 : ℕ)) (fun n => Sum.inr ((p.1 : ℕ), n)) p.2 with hψ
  have hφinj : Function.Injective φ := by
    rintro (a | a) (b | b) hab <;> simp_all [hφ]
  have hψinj : Function.Injective ψ := by
    rintro ⟨j, a | a⟩ ⟨j', b | b⟩ hab <;> simp_all [hψ, Fin.ext_iff]
  have hST : ∀ s t, φ s ≠ ψ t := by
    rintro (s | s) ⟨j, t | t⟩ <;> simp [hφ, hψ] <;> omega
  have h := hd.indepFun_pointFamily_split φ ψ hφinj hψinj hST
  have hextrL : Measurable
      (fun g : (i : Unit ⊕ ℕ) → pointFamilyIndexType E (φ i) =>
        ((g (Sum.inl ()) : ℕ), fun n => (g (Sum.inr n) : E))) :=
    (measurable_pi_apply (Sum.inl ())).prodMk
      (measurable_pi_lambda _ fun n => measurable_pi_apply (Sum.inr n))
  have hextrR : Measurable
      (fun g : (i : Fin M × (Unit ⊕ ℕ)) → pointFamilyIndexType E (ψ i) =>
        fun j : Fin M => ((g (j, Sum.inl ()) : ℕ), fun n => (g (j, Sum.inr n) : E))) :=
    measurable_pi_lambda _ fun j => (measurable_pi_apply (j, Sum.inl ())).prodMk
      (measurable_pi_lambda _ fun n => measurable_pi_apply (j, Sum.inr n))
  exact h.comp hextrL hextrR

noncomputable def phi (w : E → ℂ) (p : ℕ × (ℕ → E)) : ℂ := ∏ n ∈ Finset.range p.1, w (p.2 n)

theorem measurable_phi {w : E → ℂ} (hw : Measurable w) : Measurable (phi w) := by
  have h : Measurable fun p : (ℕ → E) × ℕ => ∏ n ∈ Finset.range p.2, w (p.1 n) :=
    measurable_from_prod_countable_left fun y =>
      Finset.measurable_prod (Finset.range y) fun n _ => hw.comp (measurable_pi_apply n)
  exact h.comp measurable_swap

theorem measurable_G (hd : IsPoissonPointFamily K Y m P) (k : ℕ) :
    Measurable (fun ω => (K k ω, fun n => Y k n ω)) :=
  (hd.measurable_count k).prodMk (measurable_pi_lambda _ fun n => hd.measurable_point k n)

theorem prod_int (hd : IsPoissonPointFamily K Y m P) {w : E → ℂ} (hw : Measurable w) (M : ℕ) :
    ∫ ω, ∏ k ∈ Finset.range M, phi w (K k ω, fun n => Y k n ω) ∂P
      = ∏ k ∈ Finset.range M, ∫ ω, phi w (K k ω, fun n => Y k n ω) ∂P := by
  induction M with
  | zero => simp
  | succ M ih =>
    have e : ∀ ω, ∏ k ∈ Finset.range (M + 1), phi w (K k ω, fun n => Y k n ω)
        = phi w (K M ω, fun n => Y M n ω) *
          (fun h : Fin M → ℕ × (ℕ → E) => ∏ j, phi w (h j))
            (fun j : Fin M => (K j ω, fun n => Y j n ω)) := by
      intro ω
      rw [Finset.prod_range_succ, mul_comm]
      congr 1
      exact (Fin.prod_univ_eq_prod_range (fun k => phi w (K k ω, fun n => Y k n ω)) M).symm
    simp_rw [e]
    have hY : Measurable (fun ω (j : Fin M) => (K j ω, fun n => Y j n ω)) :=
      measurable_pi_lambda _ fun j => measurable_G hd j
    have hI : ∫ ω, phi w (K M ω, fun n => Y M n ω) * ∏ j : Fin M, phi w (K j ω, fun n => Y j n ω) ∂P
        = (∫ ω, phi w (K M ω, fun n => Y M n ω) ∂P)
          * ∫ ω, ∏ j : Fin M, phi w (K j ω, fun n => Y j n ω) ∂P :=
      (indep_prefix hd M).integral_fun_comp_mul_comp (f := phi w)
        (g := fun h : Fin M → ℕ × (ℕ → E) => ∏ j, phi w (h j)) (measurable_G hd M).aemeasurable
        hY.aemeasurable (measurable_phi hw).aestronglyMeasurable
        (Finset.measurable_prod _ fun j _ => (measurable_phi hw).comp
          (measurable_pi_apply j)).aestronglyMeasurable
    rw [hI]
    rw [Finset.prod_range_succ, mul_comm]
    congr 1
    rw [← ih]
    congr 1
    funext ω
    exact Fin.prod_univ_eq_prod_range (fun k => phi w (K k ω, fun n => Y k n ω)) M

theorem piece_exp (hd : IsPoissonPointFamily K Y m P) {w : E → ℂ} (hw : Measurable w)
    (hb : ∀ x, ‖w x‖ ≤ 1) (k : ℕ) :
    ∫ ω, phi w (K k ω, fun n => Y k n ω) ∂P
      = Complex.exp (∫ x in prmPiece m k, (w x - 1) ∂m) := by
  have h := integral_pieceProd_eq_exp (k := k) hd hw hb
  simp only [phi]
  rw [h]
  congr 1
  haveI : IsFiniteMeasure (m.restrict (prmPiece m k)) :=
    isFiniteMeasure_restrict.2 measure_prmPiece_lt_top.ne
  have hwi : Integrable w (m.restrict (prmPiece m k)) :=
    Integrable.of_bound hw.aestronglyMeasurable 1 (Eventually.of_forall hb)
  by_cases h0 : m (prmPiece m k) = 0
  · rw [h0, Measure.restrict_eq_zero.2 h0]; simp
  · unfold prmPieceLaw
    rw [if_neg h0, integral_smul_measure, integral_sub hwi (integrable_const _),
      setIntegral_const, ENNReal.toReal_inv, measureReal_def]
    have ha : (m (prmPiece m k)).toReal ≠ 0 :=
      ENNReal.toReal_ne_zero.mpr ⟨h0, (measure_prmPiece_lt_top).ne⟩
    rw [Complex.real_smul, Complex.real_smul, Complex.ofReal_inv]
    have ha' : ((m (prmPiece m k)).toReal : ℂ) ≠ 0 := by exact_mod_cast ha
    field_simp

end AuxCE

namespace Kyprianou
theorem _root_.solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (f : E → ℝ) (hf : Measurable f) :
(Integrable (fun x => min (1 : ℝ) |f x|) m →
      ∀ ξ : ℝ,
        charFun (P.map (fun ω =>
          ∫ x, f x ∂(ProbabilityTheory.poissonRandomMeasure K Y ω))) ξ =
        Complex.exp
          (∫ x, (Complex.exp (Complex.I *
            (((ξ * f x : ℝ) : ℂ))) - 1) ∂m)) := by
  intro hgi ξ
  set w : E → ℂ := fun x => Complex.exp (Complex.I * (((ξ * f x : ℝ) : ℂ))) with hwdef
  have hw : Measurable w := Complex.measurable_exp.comp
    (measurable_const.mul (Complex.measurable_ofReal.comp (measurable_const.mul hf)))
  have hw1 : ∀ x, ‖w x‖ = 1 := fun x => by
    simp only [hwdef]; rw [Complex.norm_exp]; simp
  have hb : ∀ x, ‖w x - 1‖ ≤ (2 + |ξ|) * min (1 : ℝ) |f x| := by
    intro x
    by_cases hx : |f x| ≤ 1
    · rw [min_eq_right hx]
      have h1 : ‖w x - 1‖ ≤ ‖ξ * f x‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
      rw [Real.norm_eq_abs, abs_mul] at h1
      nlinarith [abs_nonneg (f x), abs_nonneg ξ]
    · rw [min_eq_left (le_of_lt (not_le.1 hx)), mul_one]
      have h1 : ‖w x - 1‖ ≤ ‖w x‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      rw [hw1, norm_one] at h1
      linarith [abs_nonneg ξ]
  have hwi : Integrable (fun x => w x - 1) m :=
    Integrable.mono' (hgi.const_mul (2 + |ξ|)) (hw.sub measurable_const).aestronglyMeasurable
      (Eventually.of_forall hb)
  -- the right-hand side as a limit
  have hsum : HasSum (fun k => ∫ x in prmPiece m k, (w x - 1) ∂m) (∫ x, (w x - 1) ∂m) := by
    have h := hasSum_integral_iUnion (μ := m) (f := fun x => w x - 1) (s := prmPiece m)
      (fun k => measurableSet_prmPiece) pairwise_disjoint_prmPiece
      (by rw [iUnion_prmPiece]; exact hwi.integrableOn)
    rwa [iUnion_prmPiece, Measure.restrict_univ] at h
  set T : ℕ → Ω → ℝ := fun M ω => ∑ k ∈ Finset.range M, pieceSum K Y f k ω with hT
  have hF : ∀ M ω, ∏ k ∈ Finset.range M, AuxCE.phi w (K k ω, fun n => Y k n ω)
      = Complex.exp (↑ξ * ↑(T M ω) * Complex.I) := by
    intro M ω
    simp only [AuxCE.phi, hwdef]
    rw [Finset.prod_congr rfl (fun k _ => (Complex.exp_sum _ _).symm), ← Complex.exp_sum]
    congr 1
    simp only [hT, pieceSum]
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun n _ => by ring
  have hR : Tendsto (fun M => ∫ ω, Complex.exp (↑ξ * ↑(T M ω) * Complex.I) ∂P) atTop
      (𝓝 (Complex.exp (∫ x, (w x - 1) ∂m))) := by
    have e : ∀ M, ∫ ω, Complex.exp (↑ξ * ↑(T M ω) * Complex.I) ∂P
        = Complex.exp (∑ k ∈ Finset.range M, ∫ x in prmPiece m k, (w x - 1) ∂m) := by
      intro M
      simp_rw [← hF]
      rw [AuxCE.prod_int hd hw M, Complex.exp_sum]
      exact Finset.prod_congr rfl fun k _ => AuxCE.piece_exp hd hw (fun x => (hw1 x).le) k
    simp_rw [e]
    exact (Complex.continuous_exp.tendsto _).comp hsum.tendsto_sum_nat
  -- the left-hand side
  have hint : ∀ᵐ ω ∂P, Integrable f (poissonRandomMeasure K Y ω) :=
    (AuxIC.crit P m K Y hd f hf).2 hgi
  have hfa : Measurable fun x => |f x| := continuous_abs.measurable.comp hf
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun M => T M ω) atTop
      (𝓝 (∫ x, f x ∂(poissonRandomMeasure K Y ω))) := by
    filter_upwards [hint] with ω hω
    have hW : ∑' k, ENNReal.ofReal (pieceSum K Y (fun x => |f x|) k ω) ≠ ∞ := by
      rw [← AuxIC.lsum_real hfa (fun x => abs_nonneg _) ω]
      have := hω.2
      unfold HasFiniteIntegral at this
      simp_rw [Real.enorm_eq_ofReal_abs] at this
      exact this.ne
    have hAnn : ∀ k, 0 ≤ pieceSum K Y (fun x => |f x|) k ω := fun k =>
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hsumA : Summable fun k => pieceSum K Y (fun x => |f x|) k ω := by
      have := ENNReal.summable_toReal hW
      simpa [ENNReal.toReal_ofReal (hAnn _)] using this
    have hsumS : Summable fun k => pieceSum K Y f k ω :=
      Summable.of_norm_bounded hsumA fun k => by
        rw [Real.norm_eq_abs]; exact Finset.abs_sum_le_sum_abs _ _
    rw [(AuxK2.pointwise hf ω hW).2]
    exact hsumS.hasSum.tendsto_sum_nat
  have hTm : ∀ M, Measurable (T M) := fun M => Finset.measurable_sum _ fun k _ =>
    measurable_pieceSum (hd.measurable_count k) (hd.measurable_point k) hf
  have hZ : AEMeasurable (fun ω => ∫ x, f x ∂(poissonRandomMeasure K Y ω)) P :=
    aemeasurable_of_tendsto_metrizable_ae' (fun M => (hTm M).aemeasurable) hlim
  have hcont : Continuous fun x : ℝ => Complex.exp (↑ξ * ↑x * Complex.I) := by fun_prop
  rw [charFun_apply_real, integral_map hZ hcont.aestronglyMeasurable]
  have hL : Tendsto (fun M => ∫ ω, Complex.exp (↑ξ * ↑(T M ω) * Complex.I) ∂P) atTop
      (𝓝 (∫ ω, Complex.exp (↑ξ * ↑(∫ x, f x ∂(poissonRandomMeasure K Y ω)) * Complex.I) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
      (fun M => (hcont.measurable.comp (hTm M)).aestronglyMeasurable) (integrable_const _)
      (fun M => Eventually.of_forall fun ω => ?_) ?_
    · rw [← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I]
    · filter_upwards [hlim] with ω hω
      exact (hcont.tendsto _).comp hω
  exact tendsto_nhds_unique hL hR

end Kyprianou
