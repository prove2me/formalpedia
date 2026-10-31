-- Prove2me | solution 1 for MinBuying.finite_affiliated_coarsening
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T18:09:41.013439+00:00
-- url     : https://prove2.me/submissions/b43c5f86-6c4f-4fc9-a2a3-6c516f3628df

import Theorems.Thm_MinBuying_integrable_four_functions

open MeasureTheory Set MinBuying
open scoped BigOperators FinsetFamily
noncomputable section

private lemma four_functions_summable {α : Type*} [DistribLattice α]
    (a b c d : α → ℝ)
    (ha : ∀ x,0 ≤ a x) (hb : ∀ x,0 ≤ b x) (hc : ∀ x,0 ≤ c x) (hd : ∀ x,0 ≤ d x)
    (h : ∀ x y,a x*b y ≤ c (x ⊓ y)*d (x ⊔ y))
    (sa : Summable a) (sb : Summable b) (sc : Summable c) (sd : Summable d) :
    (∑' x,a x)*(∑' x,b x) ≤ (∑' x,c x)*(∑' x,d x) := by
  classical
  apply le_of_tendsto' (Filter.Tendsto.mul sa.hasSum sb.hasSum)
  intro s
  have hfour := four_functions_theorem a b c d ha hb hc hd h s s
  have hsc : (∑ x ∈ s ⊼ s,c x) ≤ ∑' x,c x :=
    Summable.sum_le_tsum _ (fun x _ => hc x) sc
  have hsd : (∑ x ∈ s ⊻ s,d x) ≤ ∑' x,d x :=
    Summable.sum_le_tsum _ (fun x _ => hd x) sd
  exact hfour.trans (mul_le_mul hsc hsd (Finset.sum_nonneg (fun x _ => hd x)) (tsum_nonneg hc))

private lemma indicator_nonnegative {α : Type*} (w : α → ℝ) (hw : ∀ x,0 ≤ w x)
    (s : Set α) (x : α) : 0 ≤ s.indicator w x := by
  classical
  by_cases hx : x ∈ s <;> simp [hx,hw]

private lemma density_integrable {n : ℕ} (w : Valuations n → ℝ)
    (hw : Measurable w) (hw0 : ∀ v,0 ≤ w v)
    [IsFiniteMeasure (volume.withDensity (fun v => ENNReal.ofReal (w v)))] :
    Integrable w volume := by
  have h1 : Integrable (fun _ : Valuations n => (1:ℝ))
      (volume.withDensity (fun v => ENNReal.ofReal (w v))) := integrable_const 1
  have hh := (integrable_withDensity_iff_integrable_smul' hw.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))).mp h1
  simpa only [smul_eq_mul,mul_one,ENNReal.toReal_ofReal (hw0 _)] using hh

private lemma density_event {n : ℕ} (w : Valuations n → ℝ)
    (hw : Measurable w) (hw0 : ∀ v,0 ≤ w v) (s : Set (Valuations n)) (hs : MeasurableSet s) :
    ((volume.withDensity (fun v => ENNReal.ofReal (w v))) s).toReal =
      ∫ v, s.indicator w v := by
  have he := integral_indicator_const (μ := volume.withDensity (fun v => ENNReal.ofReal (w v)))
    (1:ℝ) hs
  simp only [smul_eq_mul,mul_one,Measure.real] at he
  rw [← he,integral_withDensity_eq_integral_toReal_smul hw.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  apply ae_of_all
  intro v
  by_cases hv : v ∈ s <;> simp [Set.indicator,hv,hw0]

private lemma pmf_event {n : ℕ} (w : PMF (Valuations n)) (s : Set (Valuations n))
    (hs : MeasurableSet s) :
    (w.toMeasure s).toReal = ∑' v, s.indicator (fun z => (w z).toReal) v := by
  classical
  rw [w.toMeasure_apply hs,ENNReal.tsum_toReal_eq (fun v => ?_)]
  · apply tsum_congr
    intro v
    by_cases hv : v ∈ s <;> simp [hv]
  · by_cases hv : v ∈ s <;> simp [hv,w.apply_ne_top]

private def Q {n : ℕ} (q : ℝ → ℝ) (v : Valuations n) : Valuations n := fun i => q (v i)

private lemma Q_measurable {n : ℕ} {q : ℝ → ℝ} (hq : Measurable q) : Measurable (Q (n := n) q) :=
  measurable_pi_lambda _ (fun i => hq.comp (measurable_pi_apply i))

private def cell {n : ℕ} (q : ℝ → ℝ) (y : Valuations n) : Set (Valuations n) := {v | Q q v = y}

private lemma cell_measurable {n : ℕ} {q : ℝ → ℝ} (hq : Measurable q) (y : Valuations n) :
    MeasurableSet (cell q y) := measurableSet_eq_fun (Q_measurable hq) measurable_const

private lemma cell_four {n : ℕ} (w : Valuations n → ℝ) (hw : ∀ v,0 ≤ w v)
    (hmtp : MTP2 w) (q : ℝ → ℝ) (hq : Monotone q) (y z : Valuations n) :
    ∀ v r : Valuations n,
      ((cell q y).indicator w v)*((cell q z).indicator w r) ≤
        ((cell q (fun i => min (y i) (z i))).indicator w (fun i => min (v i) (r i)))*
          ((cell q (fun i => max (y i) (z i))).indicator w (fun i => max (v i) (r i))) := by
  classical
  intro v r
  by_cases hv : v ∈ cell q y
  · by_cases hr : r ∈ cell q z
    · have hmin : (fun i => min (v i) (r i)) ∈ cell q (fun i => min (y i) (z i)) := by
        funext i
        change q (min (v i) (r i)) = min (y i) (z i)
        rw [hq.map_min]
        exact congrArg₂ min (congrFun hv i) (congrFun hr i)
      have hmax : (fun i => max (v i) (r i)) ∈ cell q (fun i => max (y i) (z i)) := by
        funext i
        change q (max (v i) (r i)) = max (y i) (z i)
        rw [hq.map_max]
        exact congrArg₂ max (congrFun hv i) (congrFun hr i)
      simpa only [Set.indicator_of_mem hv,Set.indicator_of_mem hr,
        Set.indicator_of_mem hmin,Set.indicator_of_mem hmax,mul_comm] using hmtp v r
    · rw [Set.indicator_of_notMem hr,mul_zero]
      exact mul_nonneg (indicator_nonnegative w hw _ _) (indicator_nonnegative w hw _ _)
  · rw [Set.indicator_of_notMem hv,zero_mul]
    exact mul_nonneg (indicator_nonnegative w hw _ _) (indicator_nonnegative w hw _ _)

private lemma coarse_atoms_mtp2 (n : ℕ) (μ : JointLaw n) (hμ : IsProbabilityMeasure μ)
    (haff : Affiliated μ) (q : ℝ → ℝ) (hq : Monotone q) :
    MTP2 (fun y : Valuations n => ((Measure.map (Q q) μ) {y}).toReal) := by
  classical
  intro y z
  simp only [Measure.map_apply (Q_measurable hq.measurable) (measurableSet_singleton _)]
  change (μ (cell q y)).toReal * (μ (cell q z)).toReal ≤
    (μ (cell q (fun i => max (y i) (z i)))).toReal *
      (μ (cell q (fun i => min (y i) (z i)))).toReal
  rw [mul_comm ((μ (cell q (fun i => max (y i) (z i)))).toReal)]
  rcases haff with ⟨w,hw,hw0,hmtp,rfl⟩ | ⟨w,rfl,hmtp⟩
  · letI : IsProbabilityMeasure (volume.withDensity (fun v => ENNReal.ofReal (w v))) := hμ
    have hi := density_integrable w hw hw0
    rw [density_event w hw hw0 _ (cell_measurable hq.measurable y),
      density_event w hw hw0 _ (cell_measurable hq.measurable z),
      density_event w hw hw0 _ (cell_measurable hq.measurable _),
      density_event w hw hw0 _ (cell_measurable hq.measurable _)]
    apply integrable_four_functions n _ _ _ _
      (indicator_nonnegative w hw0 _) (indicator_nonnegative w hw0 _)
      (indicator_nonnegative w hw0 _) (indicator_nonnegative w hw0 _)
      (cell_four w hw0 hmtp q hq y z)
    all_goals exact hi.indicator (cell_measurable hq.measurable _)
  · let W : Valuations n → ℝ := fun v => (w v).toReal
    have hW0 : ∀ v,0 ≤ W v := fun _ => ENNReal.toReal_nonneg
    have hWs : Summable W := ENNReal.summable_toReal w.tsum_coe_ne_top
    rw [pmf_event w _ (cell_measurable hq.measurable y),
      pmf_event w _ (cell_measurable hq.measurable z),
      pmf_event w _ (cell_measurable hq.measurable _),
      pmf_event w _ (cell_measurable hq.measurable _)]
    apply four_functions_summable _ _ _ _
      (indicator_nonnegative W hW0 _) (indicator_nonnegative W hW0 _)
      (indicator_nonnegative W hW0 _) (indicator_nonnegative W hW0 _)
      (cell_four W hW0 hmtp q hq y z)
    all_goals exact hWs.indicator _

private lemma finite_map_pmf {n : ℕ} (μ : JointLaw n) [IsProbabilityMeasure μ]
    (q : ℝ → ℝ) (hq : Measurable q) (hfin : (Set.range q).Finite) :
    ∃ w : PMF (Valuations n), w.toMeasure = Measure.map (Q q) μ := by
  classical
  letI : Fintype (Set.range q) := hfin.fintype
  let R := Fin n → Set.range q
  let r : Valuations n → R := fun v i => ⟨q (v i), ⟨v i,rfl⟩⟩
  have hr : Measurable r := by
    exact measurable_pi_lambda _ (fun i =>
      (hq.comp (measurable_pi_apply i : Measurable (fun v : Valuations n => v i))).subtype_mk)
  let ν := Measure.map r μ
  letI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hr.aemeasurable
  let c : R → Valuations n := fun v i => (v i).val
  have hc : Measurable c := by
    apply measurable_pi_lambda
    intro i
    exact measurable_subtype_coe.comp (measurable_pi_apply i)
  refine ⟨ν.toPMF.map c,?_⟩
  rw [← PMF.toMeasure_map c ν.toPMF hc,Measure.toPMF_toMeasure]
  exact Measure.map_map hc hr

private def gridFloor (S : Finset ℝ) (x : ℝ) : ℝ :=
  (insert 0 (S.filter (fun r => r ≤ x))).max' (Finset.insert_nonempty _ _)

private lemma gridFloor_nonneg (S : Finset ℝ) (x : ℝ) : 0 ≤ gridFloor S x :=
  Finset.le_max' _ _ (Finset.mem_insert_self _ _)

private lemma gridFloor_mono (S : Finset ℝ) : Monotone (gridFloor S) := by
  intro x y hxy
  apply Finset.max'_subset
  intro z hz
  rcases Finset.mem_insert.mp hz with rfl | hz
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hz).1,(Finset.mem_filter.mp hz).2.trans hxy⟩)

private lemma gridFloor_le (S : Finset ℝ) (x : ℝ) (hx : 0 ≤ x) : gridFloor S x ≤ x := by
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_insert.mp hz with rfl | hz
  · exact hx
  · exact (Finset.mem_filter.mp hz).2

private lemma gridFloor_compare (S : Finset ℝ) (t : ℝ) (ht : t ∈ S)
    (x : ℝ) (hx : 0 ≤ x) : t ≤ gridFloor S x ↔ t ≤ x := by
  constructor
  · exact fun h => h.trans (gridFloor_le S x hx)
  · intro h
    exact Finset.le_max' _ _ (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨ht,h⟩))

private lemma gridFloor_finite (S : Finset ℝ) : (Set.range (gridFloor S)).Finite := by
  apply (insert 0 S).finite_toSet.subset
  rintro y ⟨x,rfl⟩
  have h := Finset.max'_mem (insert 0 (S.filter (fun r => r ≤ x))) (Finset.insert_nonempty _ _)
  rcases Finset.mem_insert.mp h with h | h
  · exact Finset.mem_insert.mpr (Or.inl h)
  · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mp h).1)

theorem solution (n : ℕ) (μ : JointLaw n) (hμ : ValidLaw μ)
    (hex : Exchangeable μ) (haff : Affiliated μ) (S : Finset ℝ) :
    ∃ q : ℝ → ℝ, ∃ w : PMF (Valuations n),
      Measurable q ∧ (∀ x,0 ≤ q x) ∧
      (∀ t ∈ S, ∀ x,0 ≤ x → (t ≤ q x ↔ t ≤ x)) ∧
      w.toMeasure = Measure.map (fun v : Valuations n => fun i => q (v i)) μ ∧
      ValidLaw w.toMeasure ∧ Exchangeable w.toMeasure ∧ MTP2 (fun v => (w v).toReal) := by
  classical
  letI : IsProbabilityMeasure μ := hμ.1
  let q := gridFloor S
  have hq := (gridFloor_mono S).measurable
  obtain ⟨w,hw⟩ := finite_map_pmf μ q hq (gridFloor_finite S)
  refine ⟨q,w,hq,gridFloor_nonneg S,gridFloor_compare S,hw,?_,?_,?_⟩
  · constructor
    · infer_instance
    · rw [hw]
      have hN : MeasurableSet {v : Valuations n | ∀ i,0 ≤ v i} := by
        simp only [setOf_forall]
        exact MeasurableSet.iInter (fun i => measurableSet_le measurable_const (measurable_pi_apply i))
      apply (ae_map_iff (Q_measurable hq).aemeasurable hN).mpr
      exact ae_of_all _ (fun v i => gridFloor_nonneg S (v i))
  · intro σ
    rw [hw]
    have hp : Measurable (permuteCoordinates σ) :=
      measurable_pi_lambda _ (fun i => measurable_pi_apply (σ i))
    rw [Measure.map_map hp (Q_measurable hq)]
    have he : permuteCoordinates σ ∘ Q q = Q q ∘ permuteCoordinates σ := rfl
    rw [he,← Measure.map_map (Q_measurable hq) hp,hex σ]
  · have hm := coarse_atoms_mtp2 n μ hμ.1 haff q (gridFloor_mono S)
    simpa only [← hw,PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)] using hm
