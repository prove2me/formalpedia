-- Prove2me | solution 1 for LeviBalancing.TripleBalancing.lemma_6_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-21T23:28:04.581807+00:00
-- url     : https://prove2.me/submissions/9790e332-a66b-45fc-8067-a81b6fa279a7

import Mathlib
import Definitions.Def_LeviBalancing_TripleBalancing_Model
import Definitions.Def_LeviBalancing_TripleBalancing_Policy
import Definitions.Def_LeviBalancing_TripleBalancing_TBPolicy

open MeasureTheory ProbabilityTheory


namespace LeviBalancing.TripleBalancing

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Basic identities -/

lemma levelBefore_succ (M : LotSizingModel Ω) (Q : ℕ → Ω → ℝ) (t : ℕ) (ht : 1 ≤ t) (ω : Ω) :
    levelBefore M Q (t + 1) ω = levelBefore M Q t ω + (Q t ω - M.D t ω) := by
  unfold levelBefore
  rw [Finset.sum_Ico_succ_top ht]; ring

lemma levelBefore_one (M : LotSizingModel Ω) (Q : ℕ → Ω → ℝ) (ω : Ω) :
    levelBefore M Q 1 ω = M.x₁ := by
  simp [levelBefore]

/-- `y_t - D_t = x_a + ∑_{j=a}^{t} (Q_j - D_j)` for `1 ≤ a ≤ t`. -/
lemma levelAfter_sub_eq (M : LotSizingModel Ω) (Q : ℕ → Ω → ℝ) (a : ℕ) (ha : 1 ≤ a) (ω : Ω) :
    ∀ t, a ≤ t → levelAfter M Q t ω - M.D t ω =
      levelBefore M Q a ω + ∑ j ∈ Finset.Icc a t, (Q j ω - M.D j ω) := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => simp [levelAfter]; ring
  | succ t hat ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ← add_assoc, ← ih]
    unfold levelAfter
    rw [levelBefore_succ M Q t (by omega)]
    ring

lemma marginal_term_le (q x D y : ℝ) (hy : x + q - D ≤ y) :
    max (q - max (D - x) 0) 0 ≤ max y 0 := by
  rcases le_or_gt 0 (D - x) with h | h
  · rw [max_eq_left h]
    exact max_le_max (by linarith) le_rfl
  · rw [max_eq_right h.le]
    exact max_le_max (by linarith) le_rfl

/-! ### lastOrder -/

lemma lastOrder_lt (Q : ℕ → Ω → ℝ) (s : ℕ) (hs : 1 ≤ s) (ω : Ω) : lastOrder Q s ω < s := by
  unfold lastOrder
  rcases ((Finset.Ico 1 s).filter (fun t => 0 < Q t ω)).eq_empty_or_nonempty with h | h
  · rw [h, Finset.sup_empty]; exact hs
  · obtain ⟨i, hi, hsup⟩ := Finset.exists_mem_eq_sup _ h id
    rw [hsup]; exact (Finset.mem_Ico.mp (Finset.mem_filter.mp hi).1).2

lemma le_lastOrder (Q : ℕ → Ω → ℝ) (s t : ℕ) (ω : Ω) (ht : t ∈ Finset.Ico 1 s) (hQ : 0 < Q t ω) :
    t ≤ lastOrder Q s ω :=
  Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨ht, hQ⟩)

lemma lastOrder_spec (Q : ℕ → Ω → ℝ) (s : ℕ) (ω : Ω) :
    (lastOrder Q s ω = 0 ∧ ∀ t ∈ Finset.Ico 1 s, ¬ 0 < Q t ω) ∨
    (lastOrder Q s ω ∈ Finset.Ico 1 s ∧ 0 < Q (lastOrder Q s ω) ω ∧
      ∀ t ∈ Finset.Ico 1 s, lastOrder Q s ω < t → ¬ 0 < Q t ω) := by
  unfold lastOrder
  rcases ((Finset.Ico 1 s).filter (fun t => 0 < Q t ω)).eq_empty_or_nonempty with h | h
  · left
    refine ⟨by rw [h, Finset.sup_empty]; rfl, ?_⟩
    intro t ht hQ
    have : t ∈ (Finset.Ico 1 s).filter (fun t => 0 < Q t ω) := Finset.mem_filter.mpr ⟨ht, hQ⟩
    rw [h] at this; simp at this
  · right
    obtain ⟨i, hi, hsup⟩ := Finset.exists_mem_eq_sup _ h id
    rw [hsup]
    obtain ⟨hi1, hi2⟩ := Finset.mem_filter.mp hi
    refine ⟨hi1, hi2, ?_⟩
    intro t ht hlt hQ
    have := Finset.le_sup (f := id) (s := (Finset.Ico 1 s).filter (fun t => 0 < Q t ω))
      (Finset.mem_filter.mpr ⟨ht, hQ⟩)
    rw [hsup] at this; exact absurd hlt (not_lt.mpr this)

lemma lastOrder_eq_of (Q : ℕ → Ω → ℝ) (s r : ℕ) (ω : Ω) (hr : r ∈ Finset.Ico 1 s)
    (hQ : 0 < Q r ω) (hno : ∀ t ∈ Finset.Ico 1 s, r < t → ¬ 0 < Q t ω) :
    lastOrder Q s ω = r := by
  apply le_antisymm
  · unfold lastOrder
    apply Finset.sup_le
    intro t ht
    obtain ⟨ht1, ht2⟩ := Finset.mem_filter.mp ht
    by_contra hc; push Not at hc
    exact hno t ht1 hc ht2
  · exact le_lastOrder Q s r ω hr hQ

lemma lastOrder_eq_zero_of (Q : ℕ → Ω → ℝ) (s : ℕ) (ω : Ω)
    (hno : ∀ t ∈ Finset.Ico 1 s, ¬ 0 < Q t ω) : lastOrder Q s ω = 0 := by
  unfold lastOrder
  have : (Finset.Ico 1 s).filter (fun t => 0 < Q t ω) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro t ht; exact hno t ht
  rw [this, Finset.sup_empty]; rfl

/-- fibers of `lastOrder`. -/
lemma lastOrder_fiber (Q : ℕ → Ω → ℝ) (s r : ℕ) :
    {ω | lastOrder Q s ω = r} =
      if r = 0 then {ω | ∀ t ∈ Finset.Ico 1 s, ¬ 0 < Q t ω}
      else {ω | r ∈ Finset.Ico 1 s ∧ 0 < Q r ω ∧ ∀ t ∈ Finset.Ico 1 s, r < t → ¬ 0 < Q t ω} := by
  ext ω
  split_ifs with hr
  · subst hr
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h
      rcases lastOrder_spec Q s ω with ⟨_, h2⟩ | ⟨h1, _, _⟩
      · exact h2
      · rw [h] at h1; simp at h1
    · intro h; exact lastOrder_eq_zero_of Q s ω h
  · simp only [Set.mem_setOf_eq]
    constructor
    · intro h
      rcases lastOrder_spec Q s ω with ⟨h1, _⟩ | ⟨h1, h2, h3⟩
      · exact absurd (h ▸ h1) hr
      · rw [h] at h1 h2 h3; exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact lastOrder_eq_of Q s r ω h1 h2 h3

/-! ### Measurability -/

lemma measurable_D (M : LotSizingModel Ω) (t : ℕ) : Measurable (M.D t) :=
  (M.D_known t).mono (M.ℱ.le t) le_rfl

lemma measurable_demandPath (M : LotSizingModel Ω) : Measurable M.demandPath :=
  measurable_pi_iff.mpr fun t => measurable_D M t

lemma measurable_Q (M : LotSizingModel Ω) (Q : ℕ → Ω → ℝ) (hQ : IsFeasiblePolicy M Q) (t : ℕ) :
    Measurable (Q t) :=
  (hQ.2 t).mono (M.ℱ.le t) le_rfl

lemma measurableF_levelBefore (M : LotSizingModel Ω) (Q : ℕ → Ω → ℝ) (hQ : IsFeasiblePolicy M Q)
    (t : ℕ) : Measurable[M.ℱ t] (levelBefore M Q t) := by
  unfold levelBefore
  refine Measurable.const_add ?_ _
  refine Finset.measurable_sum _ ?_
  intro j hj
  have hjt : j ≤ t := (Finset.mem_Ico.mp hj).2.le
  exact ((hQ.2 j).mono (M.ℱ.mono hjt) le_rfl).sub ((M.D_known j).mono (M.ℱ.mono hjt) le_rfl)

lemma measurableF_levelAfter (M : LotSizingModel Ω) (Q : ℕ → Ω → ℝ) (hQ : IsFeasiblePolicy M Q)
    (t : ℕ) : Measurable[M.ℱ t] (levelAfter M Q t) :=
  (measurableF_levelBefore M Q hQ t).add (hQ.2 t)

lemma measurable_levelBefore (M : LotSizingModel Ω) (Q : ℕ → Ω → ℝ) (hQ : IsFeasiblePolicy M Q)
    (t : ℕ) : Measurable (levelBefore M Q t) :=
  (measurableF_levelBefore M Q hQ t).mono (M.ℱ.le t) le_rfl

lemma measurable_levelAfter (M : LotSizingModel Ω) (Q : ℕ → Ω → ℝ) (hQ : IsFeasiblePolicy M Q)
    (t : ℕ) : Measurable (levelAfter M Q t) :=
  (measurableF_levelAfter M Q hQ t).mono (M.ℱ.le t) le_rfl

lemma continuous_marginalHolding (M : LotSizingModel Ω) (r : ℕ) :
    Continuous (fun p : ℝ × ℝ × (ℕ → ℝ) => marginalHolding M r p.1 p.2.1 p.2.2) := by
  unfold marginalHolding
  fun_prop

lemma measurable_marginalHolding (M : LotSizingModel Ω) (r : ℕ) :
    Measurable (fun p : ℝ × ℝ × (ℕ → ℝ) => marginalHolding M r p.1 p.2.1 p.2.2) :=
  (continuous_marginalHolding M r).measurable

lemma measurableSet_lastOrder_fiber (M : LotSizingModel Ω) (Q : ℕ → Ω → ℝ)
    (hQ : IsFeasiblePolicy M Q) (s r : ℕ) : MeasurableSet {ω | lastOrder Q s ω = r} := by
  rw [lastOrder_fiber]
  have hA : ∀ (S : Finset ℕ) (p : ℕ → Prop), MeasurableSet {ω | ∀ t ∈ S, p t → ¬ 0 < Q t ω} := by
    intro S p
    have : {ω | ∀ t ∈ S, p t → ¬ 0 < Q t ω} = ⋂ t ∈ S, ⋂ (_ : p t), {ω | ¬ 0 < Q t ω} := by
      ext ω; simp
    rw [this]
    refine Finset.measurableSet_biInter S fun t _ => ?_
    refine MeasurableSet.iInter fun _ => ?_
    exact (measurableSet_lt measurable_const (measurable_Q M Q hQ t)).compl
  split_ifs with hr
  · have := hA (Finset.Ico 1 s) (fun _ => True)
    simpa using this
  · by_cases hrs : r ∈ Finset.Ico 1 s
    · have : {ω | r ∈ Finset.Ico 1 s ∧ 0 < Q r ω ∧ ∀ t ∈ Finset.Ico 1 s, r < t → ¬ 0 < Q t ω}
          = {ω | 0 < Q r ω} ∩ {ω | ∀ t ∈ Finset.Ico 1 s, r < t → ¬ 0 < Q t ω} := by
        ext ω; simp [hrs]
      rw [this]
      exact (measurableSet_lt measurable_const (measurable_Q M Q hQ r)).inter (hA _ _)
    · have : {ω | r ∈ Finset.Ico 1 s ∧ 0 < Q r ω ∧ ∀ t ∈ Finset.Ico 1 s, r < t → ¬ 0 < Q t ω}
          = ∅ := by
        ext ω; simp [hrs]
      rw [this]; exact MeasurableSet.empty


/-! ### Saturation of the balancing rule -/

lemma marginalHolding_add_le (M : LotSizingModel Ω) (r : ℕ) (q x δ : ℝ) (hδ : 0 ≤ δ) (d : ℕ → ℝ) :
    marginalHolding M r (q + δ) x d ≤
      marginalHolding M r q x d + δ * ∑ j ∈ Finset.Icc r M.T, M.h j := by
  unfold marginalHolding
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j hj
  have h0 := M.h_nonneg j
  have : max (q + δ - max ((∑ i ∈ Finset.Icc r j, d i) - x) 0) 0 ≤
      max (q - max ((∑ i ∈ Finset.Icc r j, d i) - x) 0) 0 + δ := by
    rcases le_or_gt 0 (q - max ((∑ i ∈ Finset.Icc r j, d i) - x) 0) with h | h
    · rw [max_eq_left h, max_eq_left (by linarith)]; ring_nf; rfl
    · rw [max_eq_right h.le]; exact max_le (by linarith) (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left this h0]

lemma condMarginalHolding_add_le (M : LotSizingModel Ω) (I : ℕ → Kernel Ω (ℕ → ℝ))
    (hI : M.IsCondDemandLaw I) (Q : ℕ → Ω → ℝ) (r : ℕ) (ω : Ω) (q δ : ℝ) (hδ : 0 ≤ δ) :
    condMarginalHolding M I Q r (q + δ) ω ≤
      condMarginalHolding M I Q r q ω + ENNReal.ofReal (δ * ∑ j ∈ Finset.Icc r M.T, M.h j) := by
  haveI := hI.1 r
  unfold condMarginalHolding
  calc ∫⁻ d, ENNReal.ofReal (marginalHolding M r (q + δ) (levelBefore M Q r ω) d) ∂(I r ω)
      ≤ ∫⁻ d, (ENNReal.ofReal (marginalHolding M r q (levelBefore M Q r ω) d)
          + ENNReal.ofReal (δ * ∑ j ∈ Finset.Icc r M.T, M.h j)) ∂(I r ω) := by
        apply lintegral_mono
        intro d
        exact (ENNReal.ofReal_le_ofReal (marginalHolding_add_le M r q _ δ hδ d)).trans
          ENNReal.ofReal_add_le
    _ = _ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]

lemma saturation (M : LotSizingModel Ω) (I : ℕ → Kernel Ω (ℕ → ℝ))
    (hI : M.IsCondDemandLaw I) (Q : ℕ → Ω → ℝ) (r : ℕ) (ω : Ω) (q : ℝ)
    (hq : IsGreatest {q : ℝ | 0 ≤ q ∧ condMarginalHolding M I Q r q ω ≤ ENNReal.ofReal M.K} q) :
    ENNReal.ofReal M.K ≤ condMarginalHolding M I Q r q ω := by
  by_contra hlt
  push Not at hlt
  set c := condMarginalHolding M I Q r q ω with hc
  have hcne : c ≠ ⊤ := ne_top_of_lt hlt
  set c' := c.toReal with hc'
  have hcc' : c = ENNReal.ofReal c' := (ENNReal.ofReal_toReal hcne).symm
  have hc'0 : 0 ≤ c' := ENNReal.toReal_nonneg
  have hc'K : c' < M.K := by
    rw [hcc'] at hlt
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hc'0).mp hlt
  set S := ∑ j ∈ Finset.Icc r M.T, M.h j with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => M.h_nonneg j
  set δ := (M.K - c') / (2 * (S + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  have hq0 : 0 ≤ q := hq.1.1
  have hnot : q + δ ∉ {q : ℝ | 0 ≤ q ∧ condMarginalHolding M I Q r q ω ≤ ENNReal.ofReal M.K} := by
    intro hmem
    have := hq.2 hmem
    linarith
  have hbig : ENNReal.ofReal M.K < condMarginalHolding M I Q r (q + δ) ω := by
    by_contra h
    push Not at h
    exact hnot ⟨by linarith, h⟩
  have hle := condMarginalHolding_add_le M I hI Q r ω q δ hδpos.le
  have hδS : δ * S ≤ (M.K - c') / 2 := by
    rw [hδ, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have : condMarginalHolding M I Q r (q + δ) ω ≤ ENNReal.ofReal M.K := by
    calc condMarginalHolding M I Q r (q + δ) ω
        ≤ c + ENNReal.ofReal (δ * S) := hle
      _ = ENNReal.ofReal (c' + δ * S) := by
          rw [hcc', ENNReal.ofReal_add hc'0 (by positivity)]
      _ ≤ ENNReal.ofReal M.K := ENNReal.ofReal_le_ofReal (by linarith)
  exact absurd hbig (not_lt.mpr this)

/-! ### Disintegration -/

theorem disint_core (M : LotSizingModel Ω) (I : ℕ → Kernel Ω (ℕ → ℝ))
    (hI : M.IsCondDemandLaw I) (s : ℕ) (F : Ω → (ℕ → ℝ) → ENNReal)
    (hF : Measurable[(M.ℱ s).prod inferInstance] (Function.uncurry F)) :
    ∫⁻ ω, F ω (M.demandPath ω) ∂M.μ = ∫⁻ ω, ∫⁻ d, F ω d ∂(I s ω) ∂M.μ := by
  classical
  have hm : M.ℱ s ≤ ‹MeasurableSpace Ω› := M.ℱ.le s
  have hκmeas : @Measurable Ω (Measure (ℕ → ℝ)) (M.ℱ s) _ (fun ω => I s ω) := by
    refine @Measure.measurable_of_measurable_coe (ℕ → ℝ) Ω _ (M.ℱ s) (fun ω => I s ω) ?_
    intro A hA; exact hI.2.1 s A hA
  let κ : @Kernel Ω (ℕ → ℝ) (M.ℱ s) _ := @Kernel.mk Ω (ℕ → ℝ) (M.ℱ s) _ (fun ω => I s ω) hκmeas
  have hκM : @IsMarkovKernel Ω (ℕ → ℝ) (M.ℱ s) _ κ :=
    @IsMarkovKernel.mk _ _ (M.ℱ s) _ κ (fun ω => (hI.1 s).isProbabilityMeasure ω)
  have hκS : @IsSFiniteKernel Ω (ℕ → ℝ) (M.ℱ s) _ κ := by infer_instance
  let μ' : @Measure Ω (M.ℱ s) := M.μ.trim hm
  have hμ'F : @IsFiniteMeasure Ω (M.ℱ s) μ' := isFiniteMeasure_trim hm
  have hμ'S : @SFinite Ω (M.ℱ s) μ' := by infer_instance
  let mp : MeasurableSpace (Ω × (ℕ → ℝ)) := (M.ℱ s).prod inferInstance
  let g : Ω → Ω × (ℕ → ℝ) := fun ω => (ω, M.demandPath ω)
  have hD : Measurable M.demandPath := measurable_demandPath M
  have hg : @Measurable Ω (Ω × (ℕ → ℝ)) _ mp g :=
    Measurable.prodMk (measurable_id'' hm) hD
  let ν₁ : @Measure (Ω × (ℕ → ℝ)) mp := @Measure.map Ω (Ω × (ℕ → ℝ)) _ mp g M.μ
  let ν₂ : @Measure (Ω × (ℕ → ℝ)) mp := @Measure.compProd Ω (ℕ → ℝ) (M.ℱ s) _ μ' κ
  have hrect : ∀ B A, MeasurableSet[M.ℱ s] B → MeasurableSet A → ν₁ (B ×ˢ A) = ν₂ (B ×ˢ A) := by
    intro B A hB hA
    have h1 : ν₁ (B ×ˢ A) = M.μ (B ∩ M.demandPath ⁻¹' A) := by
      rw [@Measure.map_apply Ω (Ω × (ℕ → ℝ)) _ mp M.μ g hg _ (@MeasurableSet.prod _ _ (M.ℱ s) _ _ _ hB hA)]
      rfl
    have h2 : ν₂ (B ×ˢ A) = ∫⁻ ω in B, I s ω A ∂M.μ := by
      rw [@Measure.compProd_apply_prod Ω (ℕ → ℝ) (M.ℱ s) _ μ' κ _ _ B A hB hA]
      exact setLIntegral_trim hm (hI.2.1 s A hA) hB
    rw [h1, h2]; exact hI.2.2.1 s A B hA hB
  have hfin : @IsFiniteMeasure (Ω × (ℕ → ℝ)) mp ν₁ :=
    @Measure.isFiniteMeasure_map Ω (Ω × (ℕ → ℝ)) mp _ M.μ _ g
  have hν : ν₁ = ν₂ := by
    refine @ext_of_generate_finite (Ω × (ℕ → ℝ)) mp ν₁ ν₂ _ (@generateFrom_prod Ω (ℕ → ℝ) (M.ℱ s) _).symm
      (@isPiSystem_prod Ω (ℕ → ℝ) (M.ℱ s) _) hfin ?_ ?_
    · rintro _ ⟨B, hB, A, hA, rfl⟩
      exact hrect B A hB hA
    · rw [← Set.univ_prod_univ]
      exact hrect _ _ MeasurableSet.univ MeasurableSet.univ
  calc ∫⁻ ω, F ω (M.demandPath ω) ∂M.μ
      = ∫⁻ z, Function.uncurry F z ∂ν₁ :=
        (@lintegral_map Ω (Ω × (ℕ → ℝ)) _ mp M.μ (Function.uncurry F) g hF hg).symm
    _ = ∫⁻ z, Function.uncurry F z ∂ν₂ := by rw [hν]
    _ = ∫⁻ ω, ∫⁻ d, F ω d ∂(κ ω) ∂μ' :=
        @Measure.lintegral_compProd Ω (ℕ → ℝ) (M.ℱ s) _ μ' κ _ _ (Function.uncurry F) hF
    _ = ∫⁻ ω, ∫⁻ d, F ω d ∂(I s ω) ∂M.μ := by
        refine lintegral_trim hm ?_
        exact @Measurable.lintegral_kernel_prod_right Ω (ℕ → ℝ) (M.ℱ s) _ κ _ F hF

/-- The conditional-expectation identity for the marginal holding cost with random
`ℱ r`-measurable order quantity and inventory level, on an `ℱ r`-measurable event. -/
theorem cond_marginal_eq (M : LotSizingModel Ω) (I : ℕ → Kernel Ω (ℕ → ℝ))
    (hI : M.IsCondDemandLaw I) (r : ℕ) (A : Set Ω) (hA : MeasurableSet[M.ℱ r] A)
    (q x : Ω → ℝ) (hq : Measurable[M.ℱ r] q) (hx : Measurable[M.ℱ r] x) :
    ∫⁻ ω, A.indicator (fun ω => ENNReal.ofReal (marginalHolding M r (q ω) (x ω) (M.demandPath ω))) ω ∂M.μ
      = ∫⁻ ω in A, ∫⁻ d, ENNReal.ofReal (marginalHolding M r (q ω) (x ω) d) ∂(I r ω) ∂M.μ := by
  let F : Ω → (ℕ → ℝ) → ENNReal := fun ω d =>
    A.indicator (fun ω => ENNReal.ofReal (marginalHolding M r (q ω) (x ω) d)) ω
  have hm : M.ℱ r ≤ ‹MeasurableSpace Ω› := M.ℱ.le r
  have hF : Measurable[(M.ℱ r).prod inferInstance] (Function.uncurry F) := by
    have h1 : Measurable[(M.ℱ r).prod inferInstance]
        (fun z : Ω × (ℕ → ℝ) => (q z.1, x z.1, z.2)) := by
      refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)
      · exact hq.comp (@measurable_fst Ω (ℕ → ℝ) (M.ℱ r) _)
      · exact hx.comp (@measurable_fst Ω (ℕ → ℝ) (M.ℱ r) _)
      · exact @measurable_snd Ω (ℕ → ℝ) (M.ℱ r) _
    have h2 : Measurable[(M.ℱ r).prod inferInstance]
        (fun z : Ω × (ℕ → ℝ) => ENNReal.ofReal (marginalHolding M r (q z.1) (x z.1) z.2)) :=
      ENNReal.measurable_ofReal.comp ((measurable_marginalHolding M r).comp h1)
    have h3 : MeasurableSet[(M.ℱ r).prod inferInstance] (Prod.fst ⁻¹' A : Set (Ω × (ℕ → ℝ))) :=
      (@measurable_fst Ω (ℕ → ℝ) (M.ℱ r) _) hA
    have : Function.uncurry F = (Prod.fst ⁻¹' A).indicator
        (fun z : Ω × (ℕ → ℝ) => ENNReal.ofReal (marginalHolding M r (q z.1) (x z.1) z.2)) := by
      ext z
      simp only [Function.uncurry, F, Set.indicator, Set.mem_preimage]
      rfl
    rw [this]
    exact h2.indicator h3
  have := disint_core M I hI r F hF
  have key : ∫⁻ ω, A.indicator (fun ω => ENNReal.ofReal (marginalHolding M r (q ω) (x ω) (M.demandPath ω))) ω ∂M.μ
      = ∫⁻ ω, F ω (M.demandPath ω) ∂M.μ :=
    lintegral_congr (fun ω => by by_cases hω : ω ∈ A <;> simp [F, hω])
  rw [key, this]
  simp only [F]
  rw [← lintegral_indicator (hm _ hA)]
  congr 1
  ext ω
  by_cases hω : ω ∈ A
  · simp [Set.indicator_of_mem hω]
  · simp [Set.indicator_of_notMem hω]

/-! ### Pointwise charging -/

lemma Icc_succ_left_nat (a b : ℕ) : Finset.Icc (a + 1) b = Finset.Ioc a b := by
  ext t; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega

lemma marginalHolding_nonneg (M : LotSizingModel Ω) (r : ℕ) (q x : ℝ) (d : ℕ → ℝ) :
    0 ≤ marginalHolding M r q x d :=
  Finset.sum_nonneg fun j _ => mul_nonneg (M.h_nonneg j) (le_max_right _ _)

lemma sum_D_mono (M : LotSizingModel Ω) (ω : Ω) (r j t : ℕ) (hjt : j ≤ t) :
    ∑ i ∈ Finset.Icc r j, M.D i ω ≤ ∑ i ∈ Finset.Icc r t, M.D i ω :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl hjt)
    (fun i _ _ => M.D_nonneg i ω)

/-- the demand accumulated over `[r, j]` exceeds the level after the order of period `r`
whenever the next order period `u` with `lastOrder u = r` has accumulated backlog `> K`. -/
lemma demand_exceeds (M : LotSizingModel Ω) (Q : ℕ → Ω → ℝ) (ω : Ω) (r u : ℕ) (hr : 1 ≤ r)
    (hlo : lastOrder Q u ω = r) (hacc : M.K < accBacklog M Q u ω) :
    ∃ j ∈ Finset.Icc r u, levelBefore M Q r ω + Q r ω < ∑ i ∈ Finset.Icc r j, M.D i ω := by
  unfold accBacklog at hacc
  rw [hlo] at hacc
  have hK := M.K_nonneg
  have hpos : (0 : ℝ) < ∑ j ∈ Finset.Icc (r + 1) u,
      M.p j * max ((∑ i ∈ Finset.Icc (r + 1) j, M.D i ω) - levelBefore M Q (r + 1) ω) 0 := by
    linarith
  obtain ⟨j, hj, hjpos⟩ := Finset.exists_lt_of_sum_lt (f := fun _ => (0:ℝ)) (by simpa using hpos)
  refine ⟨j, ?_, ?_⟩
  · have := Finset.mem_Icc.mp hj
    exact Finset.mem_Icc.mpr ⟨by omega, this.2⟩
  · have hmax : 0 < max ((∑ i ∈ Finset.Icc (r + 1) j, M.D i ω) - levelBefore M Q (r + 1) ω) 0 := by
      by_contra h
      push Not at h
      have := mul_nonpos_of_nonneg_of_nonpos (M.p_nonneg j) h
      linarith
    have h1 : levelBefore M Q (r + 1) ω < ∑ i ∈ Finset.Icc (r + 1) j, M.D i ω := by
      rcases le_or_gt (∑ i ∈ Finset.Icc (r + 1) j, M.D i ω) (levelBefore M Q (r + 1) ω) with h | h
      · rw [max_eq_right (by linarith)] at hmax; exact absurd hmax (lt_irrefl _)
      · exact h
    rw [levelBefore_succ M Q r hr] at h1
    have hrj : r ≤ j := by have := Finset.mem_Icc.mp hj; omega
    rw [Icc_succ_left_nat] at h1
    rw [← Finset.sum_Ioc_add_eq_sum_Icc hrj]
    linarith

lemma holding_charge (M : LotSizingModel Ω) (Q P : ℕ → Ω → ℝ) (hP : IsFeasiblePolicy M P)
    (hT1 : ∀ s ∈ Finset.Icc 1 M.T, ∀ ω, 0 < Q s ω → M.K < accBacklog M Q s ω) (ω : Ω) :
    ∑ r ∈ (Finset.Ico 1 M.T).filter
        (fun r => 0 < Q r ω ∧ levelAfter M Q r ω < levelAfter M P r ω),
      marginalHolding M r (Q r ω) (levelBefore M Q r ω) (M.demandPath ω)
      ≤ ∑ t ∈ Finset.Icc 1 M.T, M.h t * max (levelAfter M P t ω - M.D t ω) 0 := by
  classical
  set R := (Finset.Ico 1 M.T).filter
    (fun r => 0 < Q r ω ∧ levelAfter M Q r ω < levelAfter M P r ω) with hR
  let J : ℕ → Finset ℕ := fun r =>
    (Finset.Icc r M.T).filter (fun t => ∀ u ∈ Finset.Ioc r t, ¬ 0 < Q u ω)
  let g : ℕ → ℝ := fun t => M.h t * max (levelAfter M P t ω - M.D t ω) 0
  have hg0 : ∀ t, 0 ≤ g t := fun t => mul_nonneg (M.h_nonneg t) (le_max_right _ _)
  -- step 1
  have step1 : ∀ r ∈ R, marginalHolding M r (Q r ω) (levelBefore M Q r ω) (M.demandPath ω)
      ≤ ∑ t ∈ J r, g t := by
    intro r hr
    obtain ⟨hrI, hQr, hG⟩ := Finset.mem_filter.mp hr
    have hr1 : 1 ≤ r := (Finset.mem_Ico.mp hrI).1
    have hrT : r < M.T := (Finset.mem_Ico.mp hrI).2
    unfold marginalHolding
    have hvan : ∀ t ∈ Finset.Icc r M.T, t ∉ J r →
        M.h t * max (Q r ω - max ((∑ i ∈ Finset.Icc r t, M.demandPath ω i)
          - levelBefore M Q r ω) 0) 0 = 0 := by
      intro t ht htJ
      have hex : ∃ u, (r < u ∧ u ≤ t) ∧ 0 < Q u ω := by
        by_contra hne
        push Not at hne
        apply htJ
        refine Finset.mem_filter.mpr ⟨ht, ?_⟩
        intro u hu
        exact not_lt.mpr (hne u (Finset.mem_Ioc.mp hu))
      let u₀ := Nat.find hex
      have hu₀ := Nat.find_spec hex
      have hmin : ∀ v, v < u₀ → ¬ ((r < v ∧ v ≤ t) ∧ 0 < Q v ω) := fun v hv => Nat.find_min hex hv
      have hlo : lastOrder Q u₀ ω = r := by
        apply lastOrder_eq_of Q u₀ r ω (Finset.mem_Ico.mpr ⟨hr1, hu₀.1.1⟩) hQr
        intro v hv hrv hQv
        have hvu : v < u₀ := (Finset.mem_Ico.mp hv).2
        exact hmin v hvu ⟨⟨hrv, by omega⟩, hQv⟩
      have hu₀T : u₀ ∈ Finset.Icc 1 M.T := by
        refine Finset.mem_Icc.mpr ⟨by omega, ?_⟩
        have := (Finset.mem_Icc.mp ht).2; omega
      have hacc := hT1 u₀ hu₀T ω hu₀.2
      obtain ⟨j, hj, hjlt⟩ := demand_exceeds M Q ω r u₀ hr1 hlo hacc
      have hjt : j ≤ t := by have := Finset.mem_Icc.mp hj; omega
      have hDt : levelBefore M Q r ω + Q r ω < ∑ i ∈ Finset.Icc r t, M.demandPath ω i :=
        lt_of_lt_of_le hjlt (sum_D_mono M ω r j t hjt)
      have : max (Q r ω - max ((∑ i ∈ Finset.Icc r t, M.demandPath ω i)
          - levelBefore M Q r ω) 0) 0 = 0 := by
        apply max_eq_right
        have := le_max_left ((∑ i ∈ Finset.Icc r t, M.demandPath ω i) - levelBefore M Q r ω) 0
        linarith
      rw [this, mul_zero]
    rw [← Finset.sum_subset (Finset.filter_subset _ _) hvan]
    apply Finset.sum_le_sum
    intro t ht
    obtain ⟨htI, _⟩ := Finset.mem_filter.mp ht
    have hrt : r ≤ t := (Finset.mem_Icc.mp htI).1
    apply mul_le_mul_of_nonneg_left _ (M.h_nonneg t)
    apply marginal_term_le
    have h1 := levelAfter_sub_eq M P r hr1 ω t hrt
    rw [Finset.sum_sub_distrib] at h1
    have h2 : P r ω ≤ ∑ j ∈ Finset.Icc r t, P j ω :=
      Finset.single_le_sum (f := fun j => P j ω) (fun j _ => hP.1 j ω)
        (Finset.mem_Icc.mpr ⟨le_rfl, hrt⟩)
    have h3 : levelAfter M P r ω = levelBefore M P r ω + P r ω := rfl
    have h4 : levelAfter M Q r ω = levelBefore M Q r ω + Q r ω := rfl
    show levelBefore M Q r ω + Q r ω - ∑ i ∈ Finset.Icc r t, M.D i ω ≤ _
    linarith
  -- step 2
  have hdisj : (↑R : Set ℕ).PairwiseDisjoint J := by
    intro r hr r' hr' hne
    have key : ∀ a b, a ∈ R → b ∈ R → a < b → Disjoint (J a) (J b) := by
      intro a b ha hb hab
      rw [Finset.disjoint_left]
      intro t hta htb
      obtain ⟨htaI, htaJ⟩ := Finset.mem_filter.mp hta
      obtain ⟨htbI, _⟩ := Finset.mem_filter.mp htb
      have hbt : b ≤ t := (Finset.mem_Icc.mp htbI).1
      have hQb : 0 < Q b ω := (Finset.mem_filter.mp hb).2.1
      exact htaJ b (Finset.mem_Ioc.mpr ⟨hab, hbt⟩) hQb
    rcases lt_or_gt_of_ne hne with h | h
    · exact key r r' hr hr' h
    · exact (key r' r hr' hr h).symm
  calc ∑ r ∈ R, marginalHolding M r (Q r ω) (levelBefore M Q r ω) (M.demandPath ω)
      ≤ ∑ r ∈ R, ∑ t ∈ J r, g t := Finset.sum_le_sum step1
    _ = ∑ t ∈ R.biUnion J, g t := (Finset.sum_biUnion hdisj).symm
    _ ≤ ∑ t ∈ Finset.Icc 1 M.T, g t := by
        apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun t _ _ => hg0 t)
        intro t ht
        obtain ⟨r, hr, htr⟩ := Finset.mem_biUnion.mp ht
        obtain ⟨htI, _⟩ := Finset.mem_filter.mp htr
        have hr1 : 1 ≤ r := (Finset.mem_Ico.mp (Finset.mem_filter.mp hr).1).1
        have := Finset.mem_Icc.mp htI
        exact Finset.mem_Icc.mpr ⟨by omega, this.2⟩

lemma ordback_charge (M : LotSizingModel Ω) (Q P : ℕ → Ω → ℝ) (hP : IsFeasiblePolicy M P)
    (hT1 : ∀ s ∈ Finset.Icc 1 M.T, ∀ ω, 0 < Q s ω → M.K < accBacklog M Q s ω) (ω : Ω) :
    ∑ s ∈ (Finset.Icc 1 M.T).filter (fun s => 0 < Q s ω ∧
        ¬ (1 ≤ lastOrder Q s ω ∧
          levelAfter M Q (lastOrder Q s ω) ω < levelAfter M P (lastOrder Q s ω) ω)), M.K
      ≤ ∑ t ∈ Finset.Icc 1 M.T,
          ((if 0 < P t ω then M.K else 0) + M.p t * max (M.D t ω - levelAfter M P t ω) 0) := by
  classical
  set S := (Finset.Icc 1 M.T).filter (fun s => 0 < Q s ω ∧
        ¬ (1 ≤ lastOrder Q s ω ∧
          levelAfter M Q (lastOrder Q s ω) ω < levelAfter M P (lastOrder Q s ω) ω)) with hS
  let Iv : ℕ → Finset ℕ := fun s => Finset.Ioc (lastOrder Q s ω) s
  let c : ℕ → ℝ := fun t =>
    (if 0 < P t ω then M.K else 0) + M.p t * max (M.D t ω - levelAfter M P t ω) 0
  have hK := M.K_nonneg
  have hc0 : ∀ t, 0 ≤ c t := fun t => by
    apply add_nonneg
    · split_ifs <;> linarith
    · exact mul_nonneg (M.p_nonneg t) (le_max_right _ _)
  have step1 : ∀ s ∈ S, M.K ≤ ∑ t ∈ Iv s, c t := by
    intro s hs
    obtain ⟨hsI, hQs, hnG⟩ := Finset.mem_filter.mp hs
    have hs1 : 1 ≤ s := (Finset.mem_Icc.mp hsI).1
    set r := lastOrder Q s ω with hr
    have hrs : r < s := lastOrder_lt Q s hs1 ω
    by_cases hord : ∃ t ∈ Iv s, 0 < P t ω
    · obtain ⟨t, ht, hPt⟩ := hord
      have h1 : M.K ≤ c t := by
        simp only [c, if_pos hPt]
        have := mul_nonneg (M.p_nonneg t) (le_max_right (M.D t ω - levelAfter M P t ω) 0)
        linarith
      exact h1.trans (Finset.single_le_sum (f := c) (fun t _ => hc0 t) ht)
    · push Not at hord
      have hP0 : ∀ t ∈ Iv s, P t ω = 0 := fun t ht => le_antisymm (hord t ht) (hP.1 t ω)
      have hlev : levelBefore M P (r + 1) ω ≤ levelBefore M Q (r + 1) ω := by
        rcases Nat.eq_zero_or_pos r with h0 | hpos
        · rw [h0, levelBefore_one, levelBefore_one]
        · have hnG' : levelAfter M P r ω ≤ levelAfter M Q r ω := by
            by_contra h; push Not at h; exact hnG ⟨hpos, h⟩
          rw [levelBefore_succ M P r hpos, levelBefore_succ M Q r hpos]
          have h3 : levelAfter M P r ω = levelBefore M P r ω + P r ω := rfl
          have h4 : levelAfter M Q r ω = levelBefore M Q r ω + Q r ω := rfl
          linarith
      have hacc := hT1 s hsI ω hQs
      unfold accBacklog at hacc
      rw [← hr] at hacc
      calc M.K ≤ ∑ j ∈ Finset.Icc (r + 1) s,
            M.p j * max ((∑ i ∈ Finset.Icc (r + 1) j, M.D i ω) - levelBefore M Q (r + 1) ω) 0 :=
            hacc.le
        _ ≤ ∑ t ∈ Finset.Icc (r + 1) s, M.p t * max (M.D t ω - levelAfter M P t ω) 0 := by
            apply Finset.sum_le_sum
            intro t ht
            apply mul_le_mul_of_nonneg_left _ (M.p_nonneg t)
            apply max_le_max _ le_rfl
            have ht' := Finset.mem_Icc.mp ht
            have h1 := levelAfter_sub_eq M P (r + 1) (by omega) ω t ht'.1
            have h2 : ∑ j ∈ Finset.Icc (r + 1) t, (P j ω - M.D j ω)
                = - ∑ j ∈ Finset.Icc (r + 1) t, M.D j ω := by
              rw [Finset.sum_sub_distrib]
              have : ∑ j ∈ Finset.Icc (r + 1) t, P j ω = 0 := by
                apply Finset.sum_eq_zero
                intro j hj
                have hj' := Finset.mem_Icc.mp hj
                exact hP0 j (Finset.mem_Ioc.mpr ⟨by omega, by omega⟩)
              rw [this]; ring
            rw [h2] at h1
            linarith
        _ ≤ ∑ t ∈ Finset.Icc (r + 1) s, c t := by
            apply Finset.sum_le_sum
            intro t _
            simp only [c]
            split_ifs <;> linarith
        _ = ∑ t ∈ Iv s, c t := by
            simp only [Iv]; rw [Icc_succ_left_nat]
  have hdisj : (↑S : Set ℕ).PairwiseDisjoint Iv := by
    intro s hs s' hs' hne
    have key : ∀ a b, a ∈ S → b ∈ S → a < b → Disjoint (Iv a) (Iv b) := by
      intro a b ha hb hab
      rw [Finset.disjoint_left]
      intro t hta htb
      have h1 : t ≤ a := (Finset.mem_Ioc.mp hta).2
      have h2 : lastOrder Q b ω < t := (Finset.mem_Ioc.mp htb).1
      have ha1 : 1 ≤ a := (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).1
      have hQa : 0 < Q a ω := (Finset.mem_filter.mp ha).2.1
      have := le_lastOrder Q b a ω (Finset.mem_Ico.mpr ⟨ha1, hab⟩) hQa
      omega
    rcases lt_or_gt_of_ne hne with h | h
    · exact key s s' hs hs' h
    · exact (key s' s hs' hs h).symm
  calc ∑ s ∈ S, M.K ≤ ∑ s ∈ S, ∑ t ∈ Iv s, c t := Finset.sum_le_sum step1
    _ = ∑ t ∈ S.biUnion Iv, c t := (Finset.sum_biUnion hdisj).symm
    _ ≤ ∑ t ∈ Finset.Icc 1 M.T, c t := by
        apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun t _ _ => hc0 t)
        intro t ht
        obtain ⟨s, hs, hts⟩ := Finset.mem_biUnion.mp ht
        have hsT : s ≤ M.T := (Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1).2
        have := Finset.mem_Ioc.mp hts
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩

lemma counting (M : LotSizingModel Ω) (Q P : ℕ → Ω → ℝ) (ω : Ω) :
    numOrders M Q ω ≤
      ((Finset.Ico 1 M.T).filter
        (fun r => 0 < Q r ω ∧ levelAfter M Q r ω < levelAfter M P r ω)).card +
      ((Finset.Icc 1 M.T).filter (fun s => 0 < Q s ω ∧
        ¬ (1 ≤ lastOrder Q s ω ∧
          levelAfter M Q (lastOrder Q s ω) ω < levelAfter M P (lastOrder Q s ω) ω))).card := by
  classical
  unfold numOrders
  set O := (Finset.Icc 1 M.T).filter (fun t => 0 < Q t ω) with hO
  let cS : ℕ → Prop := fun s => ¬ (1 ≤ lastOrder Q s ω ∧
          levelAfter M Q (lastOrder Q s ω) ω < levelAfter M P (lastOrder Q s ω) ω)
  have h1 : (Finset.Icc 1 M.T).filter (fun s => 0 < Q s ω ∧ cS s) = O.filter cS := by
    rw [hO, Finset.filter_filter]
  rw [h1, ← Finset.card_filter_add_card_filter_not (s := O) cS, add_comm]
  refine add_le_add ?_ le_rfl
  apply Finset.card_le_card_of_injOn (fun s => lastOrder Q s ω)
  · intro s hs
    obtain ⟨hsO, hcs⟩ := Finset.mem_filter.mp hs
    obtain ⟨hsI, hQs⟩ := Finset.mem_filter.mp hsO
    simp only [cS, not_not] at hcs
    have hs1 : 1 ≤ s := (Finset.mem_Icc.mp hsI).1
    have hrs := lastOrder_lt Q s hs1 ω
    have hsT := (Finset.mem_Icc.mp hsI).2
    show lastOrder Q s ω ∈ _
    refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hcs.1, by omega⟩, ?_, hcs.2⟩
    rcases lastOrder_spec Q s ω with ⟨h0, _⟩ | ⟨_, hQr, _⟩
    · omega
    · exact hQr
  · intro s hs s' hs' heq
    simp only at heq
    by_contra hne
    have key : ∀ a b, a ∈ (O.filter fun s => ¬ cS s) → b ∈ (O.filter fun s => ¬ cS s) →
        a < b → lastOrder Q a ω = lastOrder Q b ω → False := by
      intro a b ha hb hab hlo
      have ha1 : 1 ≤ a := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).1).1
      have hQa : 0 < Q a ω := (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2
      have h1 := le_lastOrder Q b a ω (Finset.mem_Ico.mpr ⟨ha1, hab⟩) hQa
      have h2 := lastOrder_lt Q a ha1 ω
      omega
    rcases lt_or_gt_of_ne hne with h | h
    · exact key s s' hs hs' h heq
    · exact key s' s hs' hs h heq.symm

/-! ### Lemma 6.1 -/

theorem lemma_6_1_core (M : LotSizingModel Ω)
    (I : ℕ → Kernel Ω (ℕ → ℝ)) (hI : M.IsCondDemandLaw I)
    (TB : ℕ → Ω → ℝ) (hTB : IsTripleBalancing M I TB)
    (P : ℕ → Ω → ℝ) (hP : IsFeasiblePolicy M P) :
    ENNReal.ofReal M.K * ∫⁻ ω, (numOrders M TB ω : ENNReal) ∂M.μ ≤ expectedCost M P := by
  classical
  have hQ := hTB.1
  have hT1 : ∀ s ∈ Finset.Icc 1 M.T, ∀ ω, 0 < TB s ω → M.K < accBacklog M TB s ω := by
    intro s hs ω hpos
    by_contra h; push Not at h
    have := (hTB.2 s hs ω).1 h; linarith
  have hT2 : ∀ r ∈ Finset.Ico 1 M.T, ∀ ω, 0 < TB r ω →
      IsGreatest {q : ℝ | 0 ≤ q ∧ condMarginalHolding M I TB r q ω ≤ ENNReal.ofReal M.K}
        (TB r ω) := by
    intro r hr ω hpos
    have hr' : r ∈ Finset.Icc 1 M.T :=
      Finset.mem_Icc.mpr ⟨(Finset.mem_Ico.mp hr).1, (Finset.mem_Ico.mp hr).2.le⟩
    exact ((hTB.2 r hr' ω).2 (hT1 r hr' ω hpos)).1 (Finset.mem_Ico.mp hr).2
  -- sets
  let AR : ℕ → Set Ω := fun r => {ω | 0 < TB r ω ∧ levelAfter M TB r ω < levelAfter M P r ω}
  let AS : ℕ → Set Ω := fun s => {ω | 0 < TB s ω ∧ ¬ (1 ≤ lastOrder TB s ω ∧
      levelAfter M TB (lastOrder TB s ω) ω < levelAfter M P (lastOrder TB s ω) ω)}
  have hARF : ∀ r, MeasurableSet[M.ℱ r] (AR r) := fun r =>
    (measurableSet_lt measurable_const (hQ.2 r)).inter
      (measurableSet_lt (measurableF_levelAfter M TB hQ r) (measurableF_levelAfter M P hP r))
  have hAR : ∀ r, MeasurableSet (AR r) := fun r => M.ℱ.le r _ (hARF r)
  have hAS : ∀ s, 1 ≤ s → MeasurableSet (AS s) := by
    intro s hs
    have : AS s = {ω | 0 < TB s ω} ∩ ⋃ r ∈ Finset.range s, ({ω | lastOrder TB s ω = r} ∩
        {ω | ¬ (1 ≤ r ∧ levelAfter M TB r ω < levelAfter M P r ω)}) := by
      ext ω
      simp only [AS, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iUnion, Finset.mem_range,
        exists_prop]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, lastOrder TB s ω, lastOrder_lt TB s hs ω, rfl, h2⟩
      · rintro ⟨h1, r, _, hr, h2⟩
        exact ⟨h1, hr ▸ h2⟩
    rw [this]
    refine (measurableSet_lt measurable_const (measurable_Q M TB hQ s)).inter ?_
    refine Finset.measurableSet_biUnion _ fun r _ => ?_
    refine (measurableSet_lastOrder_fiber M TB hQ s r).inter ?_
    by_cases h1 : 1 ≤ r
    · have : {ω | ¬ (1 ≤ r ∧ levelAfter M TB r ω < levelAfter M P r ω)} =
          {ω | levelAfter M TB r ω < levelAfter M P r ω}ᶜ := by ext ω; simp [h1]
      rw [this]
      exact (measurableSet_lt (measurable_levelAfter M TB hQ r)
        (measurable_levelAfter M P hP r)).compl
    · have : {ω | ¬ (1 ≤ r ∧ levelAfter M TB r ω < levelAfter M P r ω)} = Set.univ := by
        ext ω; simp [h1]
      rw [this]; exact MeasurableSet.univ
  let H : ℕ → Ω → ENNReal := fun r ω =>
    ENNReal.ofReal (marginalHolding M r (TB r ω) (levelBefore M TB r ω) (M.demandPath ω))
  have hH : ∀ r, Measurable (H r) := fun r =>
    ENNReal.measurable_ofReal.comp ((measurable_marginalHolding M r).comp
      ((measurable_Q M TB hQ r).prodMk
        ((measurable_levelBefore M TB hQ r).prodMk (measurable_demandPath M))))
  -- pointwise bounds
  have hPW : ∀ ω, (∑ r ∈ Finset.Ico 1 M.T, (AR r).indicator (H r) ω)
      + ∑ s ∈ Finset.Icc 1 M.T, (AS s).indicator (fun _ => ENNReal.ofReal M.K) ω
      ≤ ENNReal.ofReal (totalCost M P ω) := by
    intro ω
    have e1 : ∑ r ∈ Finset.Ico 1 M.T, (AR r).indicator (H r) ω =
        ENNReal.ofReal (∑ r ∈ (Finset.Ico 1 M.T).filter
          (fun r => 0 < TB r ω ∧ levelAfter M TB r ω < levelAfter M P r ω),
          marginalHolding M r (TB r ω) (levelBefore M TB r ω) (M.demandPath ω)) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun r _ => marginalHolding_nonneg M r _ _ _),
        Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro r _
      simp only [Set.indicator_apply, AR, Set.mem_setOf_eq, H]
    have e2 : ∑ s ∈ Finset.Icc 1 M.T, (AS s).indicator (fun _ => ENNReal.ofReal M.K) ω =
        ENNReal.ofReal (∑ s ∈ (Finset.Icc 1 M.T).filter (fun s => 0 < TB s ω ∧
          ¬ (1 ≤ lastOrder TB s ω ∧
            levelAfter M TB (lastOrder TB s ω) ω < levelAfter M P (lastOrder TB s ω) ω)),
            M.K) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun s _ => M.K_nonneg), Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro s _
      simp only [Set.indicator_apply, AS, Set.mem_setOf_eq]
    rw [e1, e2, ← ENNReal.ofReal_add
      (Finset.sum_nonneg (fun r _ => marginalHolding_nonneg M r _ _ _))
      (Finset.sum_nonneg (fun s _ => M.K_nonneg))]
    apply ENNReal.ofReal_le_ofReal
    have h1 := holding_charge M TB P hP hT1 ω
    have h2 := ordback_charge M TB P hP hT1 ω
    have h3 : totalCost M P ω =
        (∑ t ∈ Finset.Icc 1 M.T, M.h t * max (levelAfter M P t ω - M.D t ω) 0)
        + ∑ t ∈ Finset.Icc 1 M.T,
          ((if 0 < P t ω then M.K else 0) + M.p t * max (M.D t ω - levelAfter M P t ω) 0) := by
      unfold totalCost periodCost
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro t _; ring
    rw [h3]; linarith
  have hCount : ∀ ω, ENNReal.ofReal M.K * (numOrders M TB ω : ENNReal) ≤
      (∑ r ∈ Finset.Ico 1 M.T, (AR r).indicator (fun _ => ENNReal.ofReal M.K) ω)
      + ∑ s ∈ Finset.Icc 1 M.T, (AS s).indicator (fun _ => ENNReal.ofReal M.K) ω := by
    intro ω
    have hc := counting M TB P ω
    have e1 : ∑ r ∈ Finset.Ico 1 M.T, (AR r).indicator (fun _ => ENNReal.ofReal M.K) ω =
        ENNReal.ofReal M.K * (((Finset.Ico 1 M.T).filter
          (fun r => 0 < TB r ω ∧ levelAfter M TB r ω < levelAfter M P r ω)).card : ENNReal) := by
      rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      simp only [Set.indicator_apply, AR, Set.mem_setOf_eq]
      split_ifs <;> simp
    have e2 : ∑ s ∈ Finset.Icc 1 M.T, (AS s).indicator (fun _ => ENNReal.ofReal M.K) ω =
        ENNReal.ofReal M.K * (((Finset.Icc 1 M.T).filter (fun s => 0 < TB s ω ∧
          ¬ (1 ≤ lastOrder TB s ω ∧
            levelAfter M TB (lastOrder TB s ω) ω < levelAfter M P (lastOrder TB s ω) ω))).card
            : ENNReal) := by
      rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      simp only [Set.indicator_apply, AS, Set.mem_setOf_eq]
      split_ifs <;> simp
    rw [e1, e2, ← mul_add]
    gcongr
    exact_mod_cast hc
  -- measurability of the sums
  have hmAR : ∀ r, Measurable ((AR r).indicator (H r)) := fun r => (hH r).indicator (hAR r)
  have hmARc : ∀ r, Measurable ((AR r).indicator (fun _ => ENNReal.ofReal M.K)) := fun r =>
    measurable_const.indicator (hAR r)
  have hmASc : ∀ s ∈ Finset.Icc 1 M.T,
      Measurable ((AS s).indicator (fun _ => ENNReal.ofReal M.K)) :=
    fun s hs => measurable_const.indicator (hAS s (Finset.mem_Icc.mp hs).1)
  -- per-r lower bound
  have hper : ∀ r ∈ Finset.Ico 1 M.T,
      ∫⁻ ω, (AR r).indicator (fun _ => ENNReal.ofReal M.K) ω ∂M.μ ≤
      ∫⁻ ω, (AR r).indicator (H r) ω ∂M.μ := by
    intro r hr
    rw [lintegral_indicator (hAR r)]
    have := cond_marginal_eq M I hI r (AR r) (hARF r) (TB r) (levelBefore M TB r) (hQ.2 r)
      (measurableF_levelBefore M TB hQ r)
    simp only [H]
    rw [this]
    apply setLIntegral_mono' (hAR r)
    intro ω hω
    exact saturation M I hI TB r ω (TB r ω) (hT2 r hr ω hω.1)
  calc ENNReal.ofReal M.K * ∫⁻ ω, (numOrders M TB ω : ENNReal) ∂M.μ
      = ∫⁻ ω, ENNReal.ofReal M.K * (numOrders M TB ω : ENNReal) ∂M.μ :=
        (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ ≤ ∫⁻ ω, ((∑ r ∈ Finset.Ico 1 M.T, (AR r).indicator (fun _ => ENNReal.ofReal M.K) ω)
          + ∑ s ∈ Finset.Icc 1 M.T, (AS s).indicator (fun _ => ENNReal.ofReal M.K) ω) ∂M.μ :=
        lintegral_mono hCount
    _ = (∑ r ∈ Finset.Ico 1 M.T, ∫⁻ ω, (AR r).indicator (fun _ => ENNReal.ofReal M.K) ω ∂M.μ)
          + ∑ s ∈ Finset.Icc 1 M.T,
            ∫⁻ ω, (AS s).indicator (fun _ => ENNReal.ofReal M.K) ω ∂M.μ := by
        rw [lintegral_add_left (Finset.measurable_sum _ (fun r _ => hmARc r)),
          lintegral_finsetSum _ (fun r _ => hmARc r), lintegral_finsetSum _ hmASc]
    _ ≤ (∑ r ∈ Finset.Ico 1 M.T, ∫⁻ ω, (AR r).indicator (H r) ω ∂M.μ)
          + ∑ s ∈ Finset.Icc 1 M.T,
            ∫⁻ ω, (AS s).indicator (fun _ => ENNReal.ofReal M.K) ω ∂M.μ :=
        add_le_add (Finset.sum_le_sum hper) le_rfl
    _ = ∫⁻ ω, ((∑ r ∈ Finset.Ico 1 M.T, (AR r).indicator (H r) ω)
          + ∑ s ∈ Finset.Icc 1 M.T, (AS s).indicator (fun _ => ENNReal.ofReal M.K) ω) ∂M.μ := by
        rw [lintegral_add_left (Finset.measurable_sum _ (fun r _ => hmAR r)),
          lintegral_finsetSum _ (fun r _ => hmAR r), lintegral_finsetSum _ hmASc]
    _ ≤ ∫⁻ ω, ENNReal.ofReal (totalCost M P ω) ∂M.μ := lintegral_mono hPW
    _ = expectedCost M P := rfl

end LeviBalancing.TripleBalancing

open LeviBalancing.TripleBalancing


theorem solution {Ω : Type*} [MeasurableSpace Ω] (M : LotSizingModel Ω)
    (I : ℕ → Kernel Ω (ℕ → ℝ)) (hI : M.IsCondDemandLaw I)
    (TB : ℕ → Ω → ℝ) (hTB : IsTripleBalancing M I TB)
    (P : ℕ → Ω → ℝ) (hP : IsFeasiblePolicy M P) :
    ENNReal.ofReal M.K * ∫⁻ ω, (numOrders M TB ω : ENNReal) ∂M.μ ≤ expectedCost M P := by
  exact lemma_6_1_core M I hI TB hTB P hP
