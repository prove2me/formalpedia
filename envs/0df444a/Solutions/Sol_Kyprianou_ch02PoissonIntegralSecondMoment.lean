-- Prove2me | solution 1 for Kyprianou.ch02PoissonIntegralSecondMoment
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T07:20:31.232903+00:00
-- url     : https://prove2.me/submissions/505495c9-bd46-4eb8-a38a-a8c942d251dc

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
    (hi : Integrable g m) (hi2 : Integrable (fun x => g x ^ 2) m) (n : ℕ) :
    ∫ ω, (∑ k ∈ Finset.range n, pieceSum K Y g k ω) ^ 2 ∂P
      = (∑ k ∈ Finset.range n, ∫ x in prmPiece m k, g x ^ 2 ∂m)
        + (∑ k ∈ Finset.range n, ∫ x in prmPiece m k, g x ∂m) ^ 2 := by
  have hmeas : ∀ k, Measurable (pieceSum K Y g k) := fun k =>
    measurable_pieceSum (hd.measurable_count k) (hd.measurable_point k) hg
  have hL2 : ∀ k, MemLp (pieceSum K Y g k) 2 P := fun k =>
    (memLp_two_iff_integrable_sq (hmeas k).aestronglyMeasurable).2
      (integrable_sq_pieceSum hd hg hi.restrict hi2.restrict)
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
      have := integral_sq_pieceSum (k := i) hd hg hi.restrict hi2.restrict
      simp only [sq] at this
      rw [this, if_pos rfl]; ring
    · have hI := (indepFun_pieceSum_pieceSum hd hg hg h).integral_mul_eq_mul_integral
          (hmeas i).aestronglyMeasurable (hmeas j).aestronglyMeasurable
      simp only [Pi.mul_apply] at hI
      rw [if_neg h, add_zero, hI,
        integral_pieceSum hd hg hi.restrict, integral_pieceSum hd hg hi.restrict]
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

namespace Kyprianou
theorem _root_.solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (f : E → ℝ) (hf : Measurable f) :
((Integrable f m ∧ MemLp f 2 m) →
      (∫ ω, (∫ x, f x ∂
        (ProbabilityTheory.poissonRandomMeasure K Y ω)) ^ 2 ∂P) =
          (∫ x, f x ^ 2 ∂m) + (∫ x, f x ∂m) ^ 2) := by
  rintro ⟨hi, h2⟩
  have hi2 := h2.integrable_sq
  have hfa : Measurable fun x => |f x| := continuous_abs.measurable.comp hf
  have hia : Integrable (fun x => |f x|) m := hi.abs
  have hia2 : Integrable (fun x => |f x| ^ 2) m := by simpa only [sq_abs] using hi2
  set A : ℕ → Ω → ℝ := fun k ω => pieceSum K Y (fun x => |f x|) k ω with hA
  have hAnn : ∀ k ω, 0 ≤ A k ω := fun k ω => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hAm : ∀ k, Measurable (A k) := fun k =>
    measurable_pieceSum (hd.measurable_count k) (hd.measurable_point k) hfa
  have hSm : ∀ k, Measurable (pieceSum K Y f k) := fun k =>
    measurable_pieceSum (hd.measurable_count k) (hd.measurable_point k) hf
  set W : Ω → ℝ≥0∞ := fun ω => ∑' k, ENNReal.ofReal (A k ω) with hWdef
  have hWm : Measurable W := Measurable.ennreal_tsum fun k => (hAm k).ennreal_ofReal
  set C : ℝ := (∫ x, f x ^ 2 ∂m) + (∫ x, |f x| ∂m) ^ 2 with hC
  have hsq := AuxK2.hasSum_pieces (g := fun x => f x ^ 2) hi2
  have hab := AuxK2.hasSum_pieces (g := fun x => |f x|) hia
  have hsa := AuxK2.hasSum_pieces (g := f) hi
  -- the finite partial sums of |f| are bounded by C
  have hbd : ∀ n, ∫ ω, (∑ k ∈ Finset.range n, A k ω) ^ 2 ∂P ≤ C := by
    intro n
    rw [AuxK2.fin hd hfa hia hia2 n]
    simp_rw [sq_abs]
    have h1 : ∑ k ∈ Finset.range n, ∫ x in prmPiece m k, f x ^ 2 ∂m ≤ ∫ x, f x ^ 2 ∂m :=
      sum_le_hasSum _ (fun k _ => setIntegral_nonneg measurableSet_prmPiece
        fun x _ => sq_nonneg _) hsq
    have h2' : ∑ k ∈ Finset.range n, ∫ x in prmPiece m k, |f x| ∂m ≤ ∫ x, |f x| ∂m :=
      sum_le_hasSum _ (fun k _ => setIntegral_nonneg measurableSet_prmPiece
        fun x _ => abs_nonneg _) hab
    have h0 : 0 ≤ ∑ k ∈ Finset.range n, ∫ x in prmPiece m k, |f x| ∂m :=
      Finset.sum_nonneg fun k _ => setIntegral_nonneg measurableSet_prmPiece
        fun x _ => abs_nonneg _
    have := pow_le_pow_left₀ h0 h2' 2
    linarith
  -- partial sums in ENNReal
  have hpart : ∀ n ω, (∑ k ∈ Finset.range n, ENNReal.ofReal (A k ω)) ^ 2
      = ENNReal.ofReal ((∑ k ∈ Finset.range n, A k ω) ^ 2) := by
    intro n ω
    rw [ENNReal.ofReal_pow (Finset.sum_nonneg fun k _ => hAnn k ω),
      ENNReal.ofReal_sum_of_nonneg fun k _ => hAnn k ω]
  have hW2 : ∫⁻ ω, W ω ^ 2 ∂P ≤ ENNReal.ofReal C := by
    have hlim : ∀ ω, Tendsto (fun n => (∑ k ∈ Finset.range n, ENNReal.ofReal (A k ω)) ^ 2)
        atTop (𝓝 (W ω ^ 2)) := fun ω =>
      ((ENNReal.continuous_pow 2).tendsto _).comp (ENNReal.tendsto_nat_tsum _)
    calc ∫⁻ ω, W ω ^ 2 ∂P
        = ∫⁻ ω, liminf (fun n => (∑ k ∈ Finset.range n, ENNReal.ofReal (A k ω)) ^ 2) atTop ∂P :=
          lintegral_congr fun ω => ((hlim ω).liminf_eq).symm
      _ ≤ liminf (fun n => ∫⁻ ω, (∑ k ∈ Finset.range n, ENNReal.ofReal (A k ω)) ^ 2 ∂P) atTop :=
          lintegral_liminf_le fun n =>
            (Finset.measurable_sum _ fun k _ => (hAm k).ennreal_ofReal).pow_const 2
      _ ≤ ENNReal.ofReal C := by
          refine liminf_le_of_frequently_le' (Frequently.of_forall fun n => ?_)
          simp_rw [hpart]
          have hint : Integrable (fun ω => (∑ k ∈ Finset.range n, A k ω) ^ 2) P := by
            have hL2 : ∀ k, MemLp (A k) 2 P := fun k =>
              (memLp_two_iff_integrable_sq (hAm k).aestronglyMeasurable).2
                (integrable_sq_pieceSum hd hfa hia.restrict hia2.restrict)
            exact (memLp_finset_sum (Finset.range n) fun k _ => hL2 k).integrable_sq
          rw [← ofReal_integral_eq_lintegral_ofReal hint
            (Eventually.of_forall fun ω => sq_nonneg _)]
          exact ENNReal.ofReal_le_ofReal (hbd n)
  have hW2fin : ∫⁻ ω, W ω ^ 2 ∂P ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hW2
  have hWae : ∀ᵐ ω ∂P, W ω ^ 2 < ∞ := ae_lt_top (hWm.pow_const 2) hW2fin
  have hbint : Integrable (fun ω => (W ω ^ 2).toReal) P :=
    integrable_toReal_of_lintegral_ne_top (hWm.pow_const 2).aemeasurable hW2fin
  set T : ℕ → Ω → ℝ := fun n ω => (∑ k ∈ Finset.range n, pieceSum K Y f k ω) ^ 2
  have hT : Tendsto (fun n => ∫ ω, T n ω ∂P) atTop
      (𝓝 (∫ ω, (∫ x, f x ∂(poissonRandomMeasure K Y ω)) ^ 2 ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun ω => (W ω ^ 2).toReal)
      (fun n => ((Finset.measurable_sum _ fun k _ => hSm k).pow_const 2).aestronglyMeasurable)
      hbint ?_ ?_
    · intro n
      filter_upwards [hWae] with ω hω
      have hWne : W ω ≠ ∞ := by
        intro h; rw [h] at hω; simp at hω
      have hsumA : Summable fun k => A k ω := by
        have := ENNReal.summable_toReal hWne
        simpa [ENNReal.toReal_ofReal (hAnn _ ω)] using this
      have hWr : (W ω).toReal = ∑' k, A k ω := by
        rw [ENNReal.tsum_toReal_eq (fun k => ENNReal.ofReal_ne_top)]
        exact tsum_congr fun k => ENNReal.toReal_ofReal (hAnn k ω)
      have hle : |∑ k ∈ Finset.range n, pieceSum K Y f k ω| ≤ (W ω).toReal := by
        rw [hWr]
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine (Finset.sum_le_sum fun k _ => Finset.abs_sum_le_sum_abs _ _).trans ?_
        exact hsumA.sum_le_tsum _ (fun k _ => hAnn k ω)
      rw [Real.norm_eq_abs, ENNReal.toReal_pow, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) hle 2
    · filter_upwards [hWae] with ω hω
      have hWne : W ω ≠ ∞ := by
        intro h; rw [h] at hω; simp at hω
      have hsumA : Summable fun k => A k ω := by
        have := ENNReal.summable_toReal hWne
        simpa [ENNReal.toReal_ofReal (hAnn _ ω)] using this
      have hsumS : Summable fun k => pieceSum K Y f k ω :=
        Summable.of_norm_bounded hsumA fun k => by
          rw [Real.norm_eq_abs]; exact Finset.abs_sum_le_sum_abs _ _
      rw [(AuxK2.pointwise hf ω hWne).2]
      exact (hsumS.hasSum.tendsto_sum_nat).pow 2
  have hR : Tendsto (fun n => ∫ ω, T n ω ∂P) atTop
      (𝓝 ((∫ x, f x ^ 2 ∂m) + (∫ x, f x ∂m) ^ 2)) := by
    have e : (fun n => ∫ ω, T n ω ∂P) = fun n =>
        (∑ k ∈ Finset.range n, ∫ x in prmPiece m k, f x ^ 2 ∂m)
          + (∑ k ∈ Finset.range n, ∫ x in prmPiece m k, f x ∂m) ^ 2 :=
      funext fun n => AuxK2.fin hd hf hi hi2 n
    rw [e]
    exact hsq.tendsto_sum_nat.add (hsa.tendsto_sum_nat.pow 2)
  exact tendsto_nhds_unique hT hR

end Kyprianou
