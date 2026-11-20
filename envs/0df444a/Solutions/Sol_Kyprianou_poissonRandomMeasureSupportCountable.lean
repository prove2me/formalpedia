-- Prove2me | solution 1 for Kyprianou.poissonRandomMeasureSupportCountable
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T07:23:21.533082+00:00
-- url     : https://prove2.me/submissions/2fd62399-cd1b-4889-a260-5b8414838817

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

namespace AuxSC

theorem rat_seq (x : ℝ) : ∃ a b : ℕ → ℚ,
    Antitone (fun j => Set.Ioc (a j : ℝ) (b j)) ∧ ⋂ j, Set.Ioc (a j : ℝ) (b j) = {x} := by
  have ha : ∀ j : ℕ, ∃ q : ℚ, x - 1 / ((j : ℝ) + 1) < q ∧ (q : ℝ) < x - 1 / ((j : ℝ) + 2) := by
    intro j
    apply exists_rat_btwn
    have : 1 / ((j : ℝ) + 2) < 1 / ((j : ℝ) + 1) :=
      one_div_lt_one_div_of_lt (by positivity) (by linarith)
    linarith
  have hb : ∀ j : ℕ, ∃ q : ℚ, x + 1 / ((j : ℝ) + 2) < q ∧ (q : ℝ) < x + 1 / ((j : ℝ) + 1) := by
    intro j
    apply exists_rat_btwn
    have : 1 / ((j : ℝ) + 2) < 1 / ((j : ℝ) + 1) :=
      one_div_lt_one_div_of_lt (by positivity) (by linarith)
    linarith
  choose a ha using ha
  choose b hb using hb
  refine ⟨a, b, ?_, ?_⟩
  · intro i j hij
    rcases hij.lt_or_eq with h | h
    · have hle : 1 / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 2) := by
        apply one_div_le_one_div_of_le (by positivity)
        have : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
        linarith
      apply Set.Ioc_subset_Ioc
      · linarith [(ha i).2, (ha j).1]
      · linarith [(hb i).1, (hb j).2]
    · subst h; exact le_rfl
  · ext y
    simp only [Set.mem_iInter, Set.mem_Ioc, Set.mem_singleton_iff]
    constructor
    · intro hy
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · obtain ⟨j, hj⟩ := exists_nat_one_div_lt (sub_pos.2 h)
        have := (hy j).1
        have := (ha j).1
        linarith
      · obtain ⟨j, hj⟩ := exists_nat_one_div_lt (sub_pos.2 h)
        have := (hy j).2
        have := (hb j).2
        linarith
    · rintro rfl j
      have h1 : 0 < 1 / ((j : ℝ) + 2) := by positivity
      exact ⟨by linarith [(ha j).2], by linarith [(hb j).1]⟩

theorem box_seq (z : ℝ × ℝ) : ∃ q : ℕ → ℚ × ℚ × ℚ × ℚ,
    Antitone (fun j => Set.Ioc ((q j).1 : ℝ) (q j).2.1 ×ˢ Set.Ioc ((q j).2.2.1 : ℝ) (q j).2.2.2) ∧
    ⋂ j, (Set.Ioc ((q j).1 : ℝ) (q j).2.1 ×ˢ Set.Ioc ((q j).2.2.1 : ℝ) (q j).2.2.2) = {z} := by
  obtain ⟨a, b, hab, hi⟩ := rat_seq z.1
  obtain ⟨c, d, hcd, hi'⟩ := rat_seq z.2
  refine ⟨fun j => (a j, b j, c j, d j), fun i j h => Set.prod_mono (hab h) (hcd h), ?_⟩
  ext w
  have e1 := Set.ext_iff.1 hi w.1
  have e2 := Set.ext_iff.1 hi' w.2
  simp only [Set.mem_iInter, Set.mem_singleton_iff, Set.mem_prod] at e1 e2 ⊢
  rw [forall_and, e1, e2, Prod.ext_iff]

end AuxSC

namespace Kyprianou

theorem AuxSC.finite {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (levyMeasure : Measure ℝ) [SigmaFinite levyMeasure]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure)
    (A : Set (ℝ × ℝ)) (hA : MeasurableSet A)
    (hAf : LevyStochCalc.Poisson.referenceIntensity levyMeasure A < ⊤) :
    ∀ᵐ ω ∂P, Set.Finite {z : ℝ × ℝ | z ∈ A ∧ N.N ω {z} ≠ 0} := by
  classical
  set B : ℚ × ℚ × ℚ × ℚ → Set (ℝ × ℝ) := fun q =>
    A ∩ (Set.Ioc (q.1 : ℝ) q.2.1 ×ˢ Set.Ioc (q.2.2.1 : ℝ) q.2.2.2) with hB
  have hBm : ∀ q, MeasurableSet (B q) := fun q =>
    hA.inter (measurableSet_Ioc.prod measurableSet_Ioc)
  have hBf : ∀ q, LevyStochCalc.Poisson.referenceIntensity levyMeasure (B q) ≠ ⊤ := fun q =>
    ne_top_of_le_ne_top hAf.ne (measure_mono Set.inter_subset_left)
  have h1 : ∀ᵐ ω ∂P, ∀ q, ∃ n : ℕ, N.N ω (B q) = n :=
    ae_all_iff.2 fun q => N.integer_valued (hBm q) (hBf q)
  filter_upwards [h1, N.integer_valued hA hAf.ne] with ω hω ⟨n, hn⟩
  -- every atom in A has mass ≥ 1
  have hatom : ∀ z ∈ A, N.N ω {z} ≠ 0 → 1 ≤ N.N ω {z} := by
    intro z hz h0
    obtain ⟨q, hqa, hqi⟩ := AuxSC.box_seq z
    have hanti : Antitone (fun j => B (q j)) := fun i j h =>
      Set.inter_subset_inter_right _ (hqa h)
    have hlim := tendsto_measure_iInter_atTop (μ := N.N ω)
      (fun j => (hBm (q j)).nullMeasurableSet) hanti
      ⟨0, ne_top_of_le_ne_top (by rw [hn]; exact ENNReal.natCast_ne_top n)
        (measure_mono Set.inter_subset_left)⟩
    have hI : ⋂ j, B (q j) = {z} := by
      rw [hB]; simp only []
      rw [← Set.inter_iInter, hqi, Set.inter_eq_right.2 (Set.singleton_subset_iff.2 hz)]
    rw [hI] at hlim
    have hcl : IsClosed ({0} ∪ Set.Ici (1 : ℝ≥0∞)) := isClosed_singleton.union isClosed_Ici
    have hmem := hcl.mem_of_tendsto hlim (Eventually.of_forall fun j => by
      obtain ⟨k, hk⟩ := hω (q j)
      simp only [Function.comp_apply, hk]
      rcases Nat.eq_zero_or_pos k with h | h
      · left; simp [h]
      · right; show (1 : ℝ≥0∞) ≤ k; exact_mod_cast h)
    rcases hmem with h | h
    · exact absurd h h0
    · exact h
  by_contra hinf
  obtain ⟨s, hsF, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf (n + 1)
  have hsum : ((n + 1 : ℕ) : ℝ≥0∞) ≤ N.N ω (s : Set (ℝ × ℝ)) := by
    rw [← sum_measure_singleton, ← hcard]
    calc ((s.card : ℕ) : ℝ≥0∞) = ∑ _b ∈ s, (1 : ℝ≥0∞) := by simp
      _ ≤ ∑ b ∈ s, N.N ω {b} := Finset.sum_le_sum fun b hb =>
          hatom b (hsF hb).1 (hsF hb).2
  have hsub : N.N ω (s : Set (ℝ × ℝ)) ≤ N.N ω A :=
    measure_mono fun b hb => (hsF hb).1
  rw [hn] at hsub
  have := hsum.trans hsub
  norm_cast at this
  omega

theorem _root_.solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (levyMeasure : Measure ℝ) [SigmaFinite levyMeasure]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure) :
    (∀ᵐ ω ∂P,
      Set.Countable {z : ℝ × ℝ | N.N ω {z} ≠ 0}) ∧
    ∀ (A : Set (ℝ × ℝ)), MeasurableSet A →
      LevyStochCalc.Poisson.referenceIntensity levyMeasure A < ⊤ →
      ∀ᵐ ω ∂P,
        Set.Finite {z : ℝ × ℝ | z ∈ A ∧ N.N ω {z} ≠ 0} := by
  refine ⟨?_, fun A hA hAf => AuxSC.finite P levyMeasure N A hA hAf⟩
  set R := LevyStochCalc.Poisson.referenceIntensity levyMeasure with hR
  haveI : SigmaFinite R := by rw [hR]; unfold LevyStochCalc.Poisson.referenceIntensity; infer_instance
  have h := ae_all_iff.2 fun k => AuxSC.finite P levyMeasure N (spanningSets R k)
    (measurableSet_spanningSets R k) (measure_spanningSets_lt_top R k)
  filter_upwards [h] with ω hω
  have e : {z : ℝ × ℝ | N.N ω {z} ≠ 0}
      = ⋃ k, {z : ℝ × ℝ | z ∈ spanningSets R k ∧ N.N ω {z} ≠ 0} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro hz
      have : z ∈ ⋃ k, spanningSets R k := by rw [iUnion_spanningSets]; trivial
      obtain ⟨k, hk⟩ := Set.mem_iUnion.1 this
      exact ⟨k, hk, hz⟩
    · rintro ⟨k, -, hz⟩; exact hz
  rw [e]
  exact Set.countable_iUnion fun k => (hω k).countable

end Kyprianou
