-- Prove2me | solution 1 for GreedyColoringLCA969.LowerBound.lemma_3_4
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T23:48:04.614705+00:00
-- url     : https://prove2.me/submissions/9c63902b-0f0f-4059-9dfc-55c5d8960f5d

import Definitions.Def_GreedyColoringLCA969_LowerBound_Distribution

open scoped ENNReal BigOperators Classical
open MeasureTheory
namespace GreedyColoringLCA969.LowerBound

local instance : MeasurableSpace Config := ⊤
local instance : DiscreteMeasurableSpace Config := ⟨fun _ => MeasurableSpace.measurableSet_top⟩

private theorem measurable_step {m : OracleMode} {n : ℕ} (A : Algorithm m)
    (R : Representation n) (v : Fin n) (s : Config) :
    Measurable (fun r => step A R r v s) := by
  rcases s with ⟨h, k, o⟩
  cases o with
  | some a => exact measurable_const
  | none =>
    cases ha : A n v h with
    | halt a => simpa only [step, ha] using (measurable_const (a := (h, k, some a)))
    | query q => simp only [step, ha]; exact measurable_const
    | tick => simp only [step, ha]; exact measurable_const
    | readBit j =>
      simp only [step, ha]
      have hf : Measurable (fun b : Bool => (show Config from (h ++ [.inr (.inl b)], k, none))) :=
        measurable_of_countable _
      exact hf.comp (show Measurable (fun r : Tape => r j) from measurable_pi_apply j)


private theorem measurable_run {m : OracleMode} {n : ℕ} (A : Algorithm m)
    (R : Representation n) (v : Fin n) (t : ℕ) : Measurable (fun r => run A R r v t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    have hstep : Measurable (fun p : Tape × Config => step A R p.1 v p.2) :=
      measurable_from_prod_countable_left (fun s => measurable_step A R v s)
    exact hstep.comp (measurable_id.prodMk ih)

private theorem measurable_cost {m : OracleMode} {n : ℕ} (A : Algorithm m)
    (R : Representation n) (v : Fin n) : Measurable (fun r => queryCost A R r v) := by
  classical
  have hterm : MeasurableSet {r | ∃ t, (run A R r v t).2.2 ≠ none} := by
    simp only [Set.ofPred_exists]
    exact MeasurableSet.iUnion fun t => (MeasurableSet.of_discrete : MeasurableSet {s : Config | s.2.2 ≠ none}).preimage (measurable_run A R v t)
  apply Measurable.ite hterm _ measurable_const
  exact Measurable.iSup fun t => (measurable_of_countable (fun s : Config => (s.2.1 : ℝ≥0∞))).comp
    (measurable_run A R v t)

private theorem measurable_returns {m : OracleMode} {n : ℕ} (A : Algorithm m)
    (R : Representation n) (v : Fin n) (c : ℕ+) : MeasurableSet {r | Returns A R r v c} := by
  simp only [Returns, Set.ofPred_exists]
  exact MeasurableSet.iUnion fun t => (MeasurableSet.of_discrete : MeasurableSet {s : Config | s.2.2 = some c}).preimage (measurable_run A R v t)

private theorem measurable_success {m : OracleMode} {n : ℕ} (A : Algorithm m)
    (R : Representation n) : MeasurableSet (successEvent A R) := by
  simp only [successEvent, Set.ofPred_exists, Set.ofPred_and, Set.ofPred_forall]
  apply MeasurableSet.iUnion
  intro c
  apply MeasurableSet.inter
  · by_cases hc : IsGreedy R.graph c <;> simp [hc]
  · exact MeasurableSet.iInter fun v => measurable_returns A R v (c v)

private theorem measurable_success_indicator {m : OracleMode} (A : Algorithm m) :
    Measurable (fun p : Tape × Input => if p.1 ∈ successEvent A p.2.2 then (1 : ℝ≥0∞) else 0) := by
  classical
  apply measurable_from_prod_countable_left
  intro R
  exact Measurable.ite (measurable_success A R.2) measurable_const measurable_const

private theorem distributionalSuccess_integral {m : OracleMode} (A : Algorithm m)
    (μ : Measure Input) (r : Tape) :
    distributionalSuccess (A, r) μ =
      ∫⁻ R, if r ∈ successEvent A R.2 then (1 : ℝ≥0∞) else 0 ∂μ := by
  classical
  rw [distributionalSuccess, ← lintegral_indicator_one (Set.to_countable _).measurableSet]
  congr

private theorem measurable_distributionalSuccess {m : OracleMode} (A : Algorithm m)
    (μ : Measure Input) [IsProbabilityMeasure μ] :
    Measurable (fun r => distributionalSuccess (A, r) μ) := by
  simp_rw [distributionalSuccess_integral]
  exact (measurable_success_indicator A).lintegral_prod_right

private theorem average_success {m : OracleMode} (A : Algorithm m)
    (μ : Measure Input) [IsProbabilityMeasure μ] :
    (∫⁻ r, distributionalSuccess (A, r) μ ∂tapeLaw) = ∫⁻ R, successProbability A R.2 ∂μ := by
  classical
  simp_rw [distributionalSuccess_integral]
  rw [lintegral_lintegral_swap (measurable_success_indicator A).aemeasurable]
  apply lintegral_congr
  intro R
  exact lintegral_indicator_one (measurable_success A R.2)

private theorem efficient_seeds {m : OracleMode} {n : ℕ} (A : Algorithm m)
    (R : Representation n) (Q ε t : ℝ) (hQ : 0 < Q) (ht : 0 < t)
    (hEff : Efficient A R Q ε) :
    ∃ E : Set Tape, MeasurableSet E ∧ tapeLaw Eᶜ ≤ ENNReal.ofReal (2 * t / 3) ∧
      ∀ r ∈ E, DeterministicEfficient (A, r) R (3 * Q / t) (ε / 2) := by
  classical
  let S := Finset.univ.filter (fun v => 0 ≤ Q ∧ expectedQueries A R v ≤ ENNReal.ofReal Q)
  have hS : ε * (n : ℝ) ≤ S.card := hEff
  let M := 3 * Q / t
  have hM : 0 < M := by dsimp [M]; positivity
  by_cases hS0 : S.card = 0
  · refine ⟨Set.univ, MeasurableSet.univ, by simp, ?_⟩
    intro r _
    unfold DeterministicEfficient
    have hh : ε / 2 * n ≤ 0 := by rw [hS0, Nat.cast_zero] at hS; linarith
    exact hh.trans (by positivity)
  have hSp : (0 : ℝ) < S.card := by exact_mod_cast (Nat.pos_of_ne_zero hS0)
  let f (r : Tape) := ∑ v ∈ S, queryCost A R r v
  have hf : Measurable f := by
    exact Finset.measurable_sum S (fun v _ => measurable_cost A R v)
  let a := M * S.card / 2
  have ha : 0 < a := by dsimp [a]; positivity
  have hint : (∫⁻ r, f r ∂tapeLaw) ≤ ENNReal.ofReal (Q * S.card) := by
    rw [show (fun r => f r) = (fun r => ∑ v ∈ S, queryCost A R r v) from rfl,
      lintegral_finsetSum S (fun v _ => measurable_cost A R v)]
    calc
      _ ≤ ∑ _v ∈ S, ENNReal.ofReal Q := Finset.sum_le_sum (fun v hv => (Finset.mem_filter.mp hv).2.2)
      _ = ENNReal.ofReal (Q * S.card) := by simp [ENNReal.ofReal_mul hQ.le, mul_comm]
  refine ⟨{r | f r ≤ ENNReal.ofReal a}, measurableSet_le hf measurable_const, ?_, ?_⟩
  · have hsub : {r | f r ≤ ENNReal.ofReal a}ᶜ ⊆ {r | ENNReal.ofReal a ≤ f r} := by
      intro r hr
      exact (lt_of_not_ge (show ¬ f r ≤ ENNReal.ofReal a from hr)).le
    calc
      _ ≤ tapeLaw {r | ENNReal.ofReal a ≤ f r} := measure_mono hsub
      _ ≤ (∫⁻ r, f r ∂tapeLaw) / ENNReal.ofReal a :=
        meas_ge_le_lintegral_div hf.aemeasurable (ne_of_gt (ENNReal.ofReal_pos.mpr ha)) ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (Q * S.card) / ENNReal.ofReal a := ENNReal.div_le_div_right hint _
      _ = ENNReal.ofReal (2 * t / 3) := by
        rw [← ENNReal.ofReal_div_of_pos ha]
        congr 1
        dsimp [a, M]
        field_simp [hQ.ne', hSp.ne', ht.ne']
        <;> ring
  · intro r hr
    let Cheap := S.filter (fun v => queryCost A R r v ≤ ENNReal.ofReal M)
    let Expensive := S.filter (fun v => ¬queryCost A R r v ≤ ENNReal.ofReal M)
    have hsum : ENNReal.ofReal (M * Expensive.card) ≤ f r := by
      calc
        _ = ∑ _v ∈ Expensive, ENNReal.ofReal M := by simp [ENNReal.ofReal_mul hM.le, mul_comm]
        _ ≤ ∑ v ∈ Expensive, queryCost A R r v := Finset.sum_le_sum (fun v hv =>
          (lt_of_not_ge (Finset.mem_filter.mp hv).2).le)
        _ ≤ f r := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => zero_le)
    have hcount : M * (Expensive.card : ℝ) ≤ a :=
      (ENNReal.ofReal_le_ofReal_iff ha.le).mp (hsum.trans hr)
    have hpartition : Cheap.card + Expensive.card = S.card := Finset.card_filter_add_card_filter_not _
    have hpart : (Cheap.card : ℝ) + Expensive.card = S.card := by exact_mod_cast hpartition
    have hcheap : ε / 2 * (n : ℝ) ≤ Cheap.card := by
      dsimp [a] at hcount
      nlinarith
    apply hcheap.trans
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro v hv
    have hv' := Finset.mem_filter.mp hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hM.le, hv'.2⟩

private theorem success_lower_average {m : OracleMode} (A : Algorithm m)
    (μ : Measure Input) [IsProbabilityMeasure μ] (δ : ℝ)
    (h : ∀ R : Input, InSupport μ R → ENNReal.ofReal δ ≤ successProbability A R.2) :
    ENNReal.ofReal δ ≤ ∫⁻ r, distributionalSuccess (A, r) μ ∂tapeLaw := by
  rw [average_success]
  have hae : ∀ᵐ R ∂μ, ENNReal.ofReal δ ≤ successProbability A R.2 :=
    ae_iff_of_countable.mpr (fun R hR => h R (lt_of_le_of_ne zero_le (Ne.symm hR)))
  simpa only [lintegral_const, measure_univ, mul_one] using lintegral_mono_ae hae

private theorem bound_average_by_good_set {X : Type} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (f : X → ℝ≥0∞) (hf : Measurable f)
    (hfone : ∀ x, f x ≤ 1) (E : Set X) (hE : MeasurableSet E) (b : ℝ≥0∞)
    (hgood : ∀ x ∈ E, f x ≤ b) :
    (∫⁻ x, f x ∂μ) ≤ b + μ Eᶜ := by
  classical
  calc
    _ ≤ ∫⁻ x, b + Eᶜ.indicator 1 x ∂μ := by
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ E
      · simpa [hx] using hgood x hx
      · simpa [hx] using (hfone x).trans (le_add_left le_rfl)
    _ = b + μ Eᶜ := by rw [lintegral_add_left measurable_const, lintegral_const,
      lintegral_indicator_one hE.compl, measure_univ, mul_one]

end GreedyColoringLCA969.LowerBound

open GreedyColoringLCA969.LowerBound

theorem solution (m : OracleMode) (μ : Measure Input)
    [IsProbabilityMeasure μ] (Rhat : Input) (hhat : InSupport μ Rhat)
    (Q ε : ℝ) (hQ : 0 < Q) (hε : 0 < ε) :
    (∀ η δ : ℝ, 0 < η → η < δ → δ ≤ 1 →
      (∀ B : DeterministicLCA m,
        DeterministicEfficient B Rhat.2 (3 * Q / η) (ε / 2) →
          distributionalSuccess B μ < ENNReal.ofReal (δ - η)) →
      ∀ A : Algorithm m, Efficient A Rhat.2 Q ε →
        ∃ R : Input, InSupport μ R ∧ successProbability A R.2 < ENNReal.ofReal δ) ∧
    ((∀ B : DeterministicLCA m,
        DeterministicEfficient B Rhat.2 (3 * Q) (ε / 2) →
          distributionalSuccess B μ < 1) →
      ∀ A : Algorithm m, Efficient A Rhat.2 Q ε →
        ∃ R : Input, InSupport μ R ∧ successProbability A R.2 < 1) := by
  classical
  constructor
  · intro η δ hη hηδ hδ hdet A hA
    by_contra hNo
    have hAll : ∀ R : Input, InSupport μ R → ENNReal.ofReal δ ≤ successProbability A R.2 := by
      intro R hR
      exact le_of_not_gt (fun h => hNo ⟨R, hR, h⟩)
    have hlow := success_lower_average A μ δ hAll
    obtain ⟨E, hE, hbad, hseed⟩ := efficient_seeds A Rhat.2 Q ε η hQ hη hA
    have hupp := bound_average_by_good_set tapeLaw (fun r => distributionalSuccess (A, r) μ)
      (measurable_distributionalSuccess A μ) (fun _ => prob_le_one) E hE (ENNReal.ofReal (δ - η))
      (fun r hr => (hdet (A, r) (hseed r hr)).le)
    have hsum : ENNReal.ofReal δ ≤ ENNReal.ofReal (δ - η) + ENNReal.ofReal (2 * η / 3) :=
      hlow.trans (hupp.trans (add_le_add le_rfl hbad))
    rw [← ENNReal.ofReal_add (by linarith) (by positivity)] at hsum
    have hlt : ENNReal.ofReal (δ - η + 2 * η / 3) < ENNReal.ofReal δ :=
      (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
    exact (not_le_of_gt hlt) hsum
  · intro hdet A hA
    by_contra hNo
    have hAll : ∀ R : Input, InSupport μ R → ENNReal.ofReal 1 ≤ successProbability A R.2 := by
      intro R hR
      exact le_of_not_gt (fun h => hNo ⟨R, hR, by simpa using h⟩)
    have hlow : 1 ≤ ∫⁻ r, distributionalSuccess (A, r) μ ∂tapeLaw := by
      simpa using success_lower_average A μ 1 hAll
    obtain ⟨E, hE, hbad, hseed⟩ := efficient_seeds A Rhat.2 Q ε 1 hQ zero_lt_one hA
    have hle : (fun r => distributionalSuccess (A, r) μ) ≤ᵐ[tapeLaw] (fun _ => (1 : ℝ≥0∞)) :=
      ae_of_all _ (fun _ => prob_le_one)
    have hfin : (∫⁻ r, distributionalSuccess (A, r) μ ∂tapeLaw) ≠ ⊤ := by
      apply ne_of_lt
      exact (lintegral_mono_ae hle).trans_lt (by simp)
    have hae : (fun r => distributionalSuccess (A, r) μ) =ᵐ[tapeLaw] (fun _ => (1 : ℝ≥0∞)) :=
      ae_eq_of_ae_le_of_lintegral_le hle hfin measurable_const.aemeasurable (by simpa using hlow)
    have hE0 : tapeLaw E = 0 := by
      apply measure_mono_null (t := {r | distributionalSuccess (A, r) μ ≠ 1}) _ (ae_iff.mp hae)
      intro r hr
      exact ne_of_lt (hdet (A, r) (by simpa using hseed r hr))
    have hEc : tapeLaw Eᶜ = 1 := by rw [measure_compl hE (by simp [hE0]), measure_univ, hE0, tsub_zero]
    rw [hEc] at hbad
    norm_num at hbad
