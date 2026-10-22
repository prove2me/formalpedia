-- Prove2me | solution 1 for LogMeanVar.Complete.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T01:00:50.042617+00:00
-- url     : https://prove2.me/submissions/ef05e45c-12a4-4f70-ac1d-a3506cde04c1

import Mathlib
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Definitions.Def_LogMeanVar_Complete_Market
import Definitions.Def_LogMeanVar_Complete_LogReturn
import Definitions.Def_LogMeanVar_Complete_Equilibrium

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace LMVAux

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma indepFun_of_le {P : Measure Ω} {G : MeasurableSpace Ω} {X f : Ω → ℝ}
    (hind : Indep G (MeasurableSpace.comap X inferInstance) P) (hf : Measurable[G] f) :
    IndepFun f X P := by
  rw [IndepFun_iff_Indep]
  exact indep_of_indep_of_le_left hind hf.comap_le

/-- Discrete Lenglart-type inequality for martingale transforms. -/
theorem lenglart (P : Measure Ω) [IsProbabilityMeasure P]
    (G : ℕ → MeasurableSpace Ω) (hG : Monotone G) (hGle : ∀ k, G k ≤ mΩ)
    (X : ℕ → Ω → ℝ) (hXm : ∀ k, Measurable[G (k+1)] (X k))
    (hXind : ∀ k, Indep (G k) (MeasurableSpace.comap (X k) inferInstance) P)
    (hX0 : ∀ k, ∫ ω, X k ω ∂P = 0) (hXL2 : ∀ k, MemLp (X k) 2 P)
    (δ : ℝ) (hX2 : ∀ k, ∫ ω, X k ω ^ 2 ∂P = δ) (hδ : 0 ≤ δ)
    (c : ℕ → Ω → ℝ) (hcm : ∀ k, Measurable[G k] (c k)) (C : ℕ → ℝ)
    (hcb : ∀ k ω, |c k ω| ≤ C k)
    (N : ℕ) (η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
    P.real {ω | ε ≤ |∑ k ∈ Finset.range N, c k ω * X k ω|} ≤
      η / ε ^ 2 + P.real {ω | η < ∑ k ∈ Finset.range N, c k ω ^ 2 * δ} := by
  classical
  set S : ℕ → Ω → ℝ := fun k ω => ∑ j ∈ Finset.range (k+1), c j ω ^ 2 * δ with hS
  set ct : ℕ → Ω → ℝ := fun k ω => if S k ω ≤ η then c k ω else 0 with hct
  set M : ℕ → Ω → ℝ := fun m ω => ∑ k ∈ Finset.range m, ct k ω * X k ω with hM
  have hcmG : ∀ j k, j ≤ k → Measurable[G k] (c j) := fun j k h => (hcm j).mono (hG h) le_rfl
  have hSm : ∀ k, Measurable[G k] (S k) := by
    intro k
    apply Finset.measurable_sum
    intro j hj
    exact ((hcmG j k (by simp at hj; omega)).pow_const 2).mul_const δ
  have hctm : ∀ k, Measurable[G k] (ct k) := fun k =>
    Measurable.ite (measurableSet_le (hSm k) measurable_const) (hcm k) measurable_const
  have hctb : ∀ k ω, |ct k ω| ≤ |C k| := by
    intro k ω
    simp only [hct]
    split_ifs
    · exact (hcb k ω).trans (le_abs_self _)
    · simp
  have hXmeas : ∀ k, Measurable (X k) := fun k => (hXm k).mono (hGle _) le_rfl
  have hctmeas : ∀ k, Measurable (ct k) := fun k => (hctm k).mono (hGle _) le_rfl
  have hMm : ∀ m, Measurable[G m] (M m) := by
    intro m
    apply Finset.measurable_sum
    intro k hk
    have hk' : k + 1 ≤ m := by simp at hk; omega
    exact ((hctm k).mono (hG (by omega)) le_rfl).mul ((hXm k).mono (hG hk') le_rfl)
  have hMmeas : ∀ m, Measurable (M m) := fun m => (hMm m).mono (hGle _) le_rfl
  have hctX : ∀ k, MemLp (fun ω => ct k ω * X k ω) 2 P := by
    intro k
    refine ((hXL2 k).const_mul |C k|).of_le ((hctmeas k).mul (hXmeas k)).aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    simp only [norm_mul, Real.norm_eq_abs, abs_abs]
    exact mul_le_mul_of_nonneg_right (hctb k ω) (abs_nonneg _)
  have hML2 : ∀ m, MemLp (M m) 2 P := by
    intro m
    have := memLp_finset_sum' (Finset.range m) (fun k _ => hctX k) (μ := P) (p := 2)
    convert this using 1
    ext ω; simp [hM, Finset.sum_apply]
  have hctL2 : ∀ k, MemLp (ct k) 2 P := fun k =>
    MemLp.of_bound (hctmeas k).aestronglyMeasurable |C k|
      (Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hctb k ω)
  -- second moment identity
  have hmom : ∀ m, ∫ ω, M m ω ^ 2 ∂P =
      ∑ k ∈ Finset.range m, (∫ ω, ct k ω ^ 2 ∂P) * δ := by
    intro m
    induction m with
    | zero => simp [hM]
    | succ m ih =>
      have e : (fun ω => M (m+1) ω ^ 2) = fun ω => (M m ω ^ 2 +
          2 * ((M m ω * ct m ω) * X m ω)) + ct m ω ^ 2 * X m ω ^ 2 := by
        ext ω; simp only [hM, Finset.sum_range_succ]; ring
      have hMct : MemLp (fun ω => M m ω * ct m ω) 2 P := by
        refine ((hML2 m).const_mul |C m|).of_le
          ((hMmeas m).mul (hctmeas m)).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
        simp only [norm_mul, Real.norm_eq_abs, abs_abs]
        rw [mul_comm |C m|]
        exact mul_le_mul_of_nonneg_left (hctb m ω) (abs_nonneg _)
      have i1 : Integrable (fun ω => M m ω ^ 2) P := (hML2 m).integrable_sq
      have i2 : Integrable (fun ω => (M m ω * ct m ω) * X m ω) P :=
        hMct.integrable_mul (hXL2 m)
      have i3 : Integrable (fun ω => ct m ω ^ 2 * X m ω ^ 2) P := by
        have := (hctX m).integrable_sq
        convert this using 1; ext ω; ring
      have ind1 : IndepFun (fun ω => M m ω * ct m ω) (X m) P :=
        indepFun_of_le (hXind m) ((hMm m).mul (hctm m))
      have ind2 : IndepFun (fun ω => ct m ω ^ 2) (fun ω => X m ω ^ 2) P := by
        have h0 : IndepFun (ct m) (X m) P := indepFun_of_le (hXind m) (hctm m)
        exact h0.comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)
      have i12 : Integrable (fun ω => M m ω ^ 2 + 2 * ((M m ω * ct m ω) * X m ω)) P :=
        i1.add (i2.const_mul 2)
      have i2' : Integrable (fun ω => 2 * ((M m ω * ct m ω) * X m ω)) P := i2.const_mul 2
      rw [e, integral_add i12 i3, integral_add i1 i2',
        integral_const_mul, ind1.integral_fun_mul_eq_mul_integral
          ((hMmeas m).mul (hctmeas m)).aestronglyMeasurable (hXmeas m).aestronglyMeasurable,
        ind2.integral_fun_mul_eq_mul_integral
          ((hctmeas m).pow_const 2).aestronglyMeasurable
          ((hXmeas m).pow_const 2).aestronglyMeasurable, ih, Finset.sum_range_succ]
      simp only [hX0, hX2]
      ring
  -- pathwise bound
  have hpath : ∀ ω, ∀ n, (∑ k ∈ Finset.range n, ct k ω ^ 2 * δ) ≤ η ∧
      (∑ k ∈ Finset.range n, ct k ω ^ 2 * δ) ≤ ∑ k ∈ Finset.range n, c k ω ^ 2 * δ := by
    intro ω n
    induction n with
    | zero => simp [hη.le]
    | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      by_cases hs : S n ω ≤ η
      · have : ct n ω = c n ω := by simp [hct, hs]
        rw [this]
        have hSn : S n ω = (∑ k ∈ Finset.range n, c k ω ^ 2 * δ) + c n ω ^ 2 * δ := by
          simp [hS, Finset.sum_range_succ]
        constructor <;> linarith [ih.2]
      · have : ct n ω = 0 := by simp [hct, hs]
        rw [this]
        have : 0 ≤ c n ω ^ 2 * δ := by positivity
        constructor <;> simp <;> linarith [ih.1, ih.2]
  have hE : ∫ ω, M N ω ^ 2 ∂P ≤ η := by
    rw [hmom]
    have : ∑ k ∈ Finset.range N, (∫ ω, ct k ω ^ 2 ∂P) * δ =
        ∫ ω, ∑ k ∈ Finset.range N, ct k ω ^ 2 * δ ∂P := by
      rw [integral_finset_sum]
      · congr 1; ext k; rw [integral_mul_const]
      · intro k _; exact ((hctL2 k).integrable_sq).mul_const δ
    rw [this]
    calc ∫ ω, ∑ k ∈ Finset.range N, ct k ω ^ 2 * δ ∂P ≤ ∫ _ω, η ∂P :=
          integral_mono_of_nonneg (Eventually.of_forall fun ω => by positivity)
            (integrable_const _) (Eventually.of_forall fun ω => (hpath ω N).1)
      _ = η := by simp
  have hcheb : P.real {ω | ε ≤ |M N ω|} ≤ η / ε ^ 2 := by
    have h1 := mul_meas_ge_le_integral_of_nonneg (μ := P) (f := fun ω => M N ω ^ 2)
      (Eventually.of_forall fun ω => by positivity) (hML2 N).integrable_sq (ε ^ 2)
    have hset : {ω | ε ≤ |M N ω|} = {ω | ε ^ 2 ≤ M N ω ^ 2} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      rw [← sq_abs (M N ω), sq_le_sq₀ hε.le (abs_nonneg _)]
    rw [hset, le_div_iff₀ (by positivity)]
    linarith
  have hsub : {ω | ε ≤ |∑ k ∈ Finset.range N, c k ω * X k ω|} ⊆
      {ω | ε ≤ |M N ω|} ∪ {ω | η < ∑ k ∈ Finset.range N, c k ω ^ 2 * δ} := by
    intro ω hω
    by_cases hlt : η < ∑ k ∈ Finset.range N, c k ω ^ 2 * δ
    · exact Or.inr hlt
    · left
      push_neg at hlt
      have heq : M N ω = ∑ k ∈ Finset.range N, c k ω * X k ω := by
        simp only [hM]
        apply Finset.sum_congr rfl
        intro k hk
        have hk' : k + 1 ≤ N := by simp at hk; omega
        have : S k ω ≤ η := by
          refine le_trans ?_ hlt
          simp only [hS]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hk')
            (fun j _ _ => by positivity)
        simp [hct, this]
      simp only [Set.mem_setOf_eq, heq]
      exact hω
  calc P.real {ω | ε ≤ |∑ k ∈ Finset.range N, c k ω * X k ω|}
      ≤ P.real ({ω | ε ≤ |M N ω|} ∪ {ω | η < ∑ k ∈ Finset.range N, c k ω ^ 2 * δ}) :=
        measureReal_mono hsub
    _ ≤ P.real {ω | ε ≤ |M N ω|} + P.real {ω | η < ∑ k ∈ Finset.range N, c k ω ^ 2 * δ} :=
        measureReal_union_le _ _
    _ ≤ _ := by linarith

end LMVAux


open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace LMVAux

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- natural filtration of a process -/
def natFilt (W : ℝ≥0 → Ω → ℝ) : ℝ≥0 → MeasurableSpace Ω :=
  fun u => ⨆ (w : ℝ≥0) (_ : w ≤ u), MeasurableSpace.comap (W w) (by infer_instance)

lemma natFilt_le {W : ℝ≥0 → Ω → ℝ} (hWm : ∀ s, Measurable (W s)) (u : ℝ≥0) :
    natFilt W u ≤ mΩ :=
  iSup₂_le fun w _ => (hWm w).comap_le

lemma natFilt_mono (W : ℝ≥0 → Ω → ℝ) : Monotone (natFilt W) := fun _ v huv =>
  iSup₂_le fun w hw =>
    le_iSup₂ (f := fun w (_ : w ≤ v) => MeasurableSpace.comap (W w) inferInstance) w
      (hw.trans huv)

lemma meas_natFilt (W : ℝ≥0 → Ω → ℝ) {w u : ℝ≥0} (h : w ≤ u) :
    Measurable[natFilt W u] (W w) :=
  (comap_measurable (W w)).mono
    (le_iSup₂ (f := fun w (_ : w ≤ u) => MeasurableSpace.comap (W w) inferInstance) w h) le_rfl

lemma indep_incr {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ} (hW : IsPreBrownianReal W P)
    {s a b : ℝ≥0} (hsa : s ≤ a) (hsb : s ≤ b) :
    Indep (natFilt W s) (MeasurableSpace.comap (fun ω => W b ω - W a ω) inferInstance) P := by
  have h := hW.indepFun_shift s
  rw [IndepFun_iff_Indep] at h
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left h.symm ?_) ?_
  · refine iSup₂_le fun w hw => ?_
    have : W w = (fun x : (Set.Iic s → ℝ) => x ⟨w, hw⟩) ∘ (fun ω (t : Set.Iic s) => W t ω) :=
      rfl
    rw [this, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_pi_apply _).comap_le
  · have : (fun ω => W b ω - W a ω) = (fun x : ℝ≥0 → ℝ => x (b - s) - x (a - s)) ∘
        (fun ω t => W (s + t) ω - W s ω) := by
      ext ω; simp [add_tsub_cancel_of_le hsa, add_tsub_cancel_of_le hsb]
    rw [this, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (Measurable.comap_le (by fun_prop))

lemma incr_moments {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ} (hW : IsPreBrownianReal W P)
    {a b : ℝ≥0} (hab : a ≤ b) :
    ∫ ω, (W b ω - W a ω) ∂P = 0 ∧ ∫ ω, (W b ω - W a ω) ^ 2 ∂P = (b : ℝ) - a ∧
      MemLp (fun ω => W b ω - W a ω) 2 P := by
  have hl := hW.hasLaw_sub b a
  have hm : MemLp (fun ω => W b ω - W a ω) 2 P :=
    hW.isGaussianProcess.hasGaussianLaw_fun_sub.memLp_two
  have h0 : ∫ ω, (W b ω - W a ω) ∂P = 0 := by
    have := hl.integral_eq
    rw [integral_id_gaussianReal] at this
    exact this
  refine ⟨h0, ?_, hm⟩
  have hv := hl.variance_eq
  rw [variance_id_gaussianReal] at hv
  have h2 : variance (fun ω => W b ω - W a ω) P = ∫ ω, (W b ω - W a ω) ^ 2 ∂P :=
    variance_of_integral_eq_zero hm.aestronglyMeasurable.aemeasurable h0
  rw [← h2]
  change variance (W b - W a) P = _
  rw [hv]
  simp only [coe_nndist]
  rw [Real.dist_eq]
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  exact abs_of_nonneg (sub_nonneg.mpr hab')

end LMVAux


open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace LMVAux

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

open EthierKurtz

lemma ii_bdd {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ u, |f u| ≤ C) (a b : ℝ) :
    IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff]
  exact Measure.integrableOn_of_bounded (M := C) (by rw [uIoc]; exact measure_Ioc_lt_top.ne)
    hf.aestronglyMeasurable (Eventually.of_forall fun u => by simpa [Real.norm_eq_abs] using hC u)

lemma step_meas (t : ℝ≥0) (n : ℕ) (b : ℕ → Ω → ℝ) (ω : Ω) :
    Measurable (fun u => itoStepValue t n b u ω) := by
  unfold itoStepValue
  apply Finset.measurable_sum
  intro k _
  exact Measurable.ite (measurableSet_Ioc (a := (k : ℝ) * t.val / 2 ^ n)
    (b := ((k : ℝ) + 1) * t.val / 2 ^ n)) measurable_const measurable_const

lemma step_bdd (t : ℝ≥0) (n : ℕ) (b : ℕ → Ω → ℝ) (ω : Ω) (u : ℝ) :
    |itoStepValue t n b u ω| ≤ ∑ k ∈ Finset.range (2 ^ n), |b k ω| := by
  unfold itoStepValue
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  split_ifs <;> simp

lemma step_sub (t : ℝ≥0) (n : ℕ) (b b' : ℕ → Ω → ℝ) (ω : Ω) (u : ℝ) :
    itoStepValue t n b u ω - itoStepValue t n b' u ω =
      itoStepValue t n (fun k ω => b k ω - b' k ω) u ω := by
  unfold itoStepValue
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp

lemma cell_uniq (t : ℝ≥0) (n j k : ℕ) (u : ℝ)
    (hj : (j : ℝ) * t.val / 2 ^ n < u ∧ u ≤ ((j : ℝ) + 1) * t.val / 2 ^ n)
    (hk : (k : ℝ) * t.val / 2 ^ n < u ∧ u ≤ ((k : ℝ) + 1) * t.val / 2 ^ n) : j = k := by
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have ht : (0 : ℝ) < t.val := by
    rcases (show (0:ℝ) ≤ t.val from t.2).lt_or_eq with h | h
    · exact h
    · exfalso
      have h1 := hj.1.trans_le hj.2
      rw [← h] at h1
      simp at h1
  have a1 : (j : ℝ) * t.val < ((k : ℝ) + 1) * t.val := by
    have := hj.1.trans_le hk.2
    rwa [div_lt_div_iff_of_pos_right h2] at this
  have a2 : (k : ℝ) * t.val < ((j : ℝ) + 1) * t.val := by
    have := hk.1.trans_le hj.2
    rwa [div_lt_div_iff_of_pos_right h2] at this
  have b1 : (j : ℝ) < k + 1 := lt_of_mul_lt_mul_right a1 ht.le
  have b2 : (k : ℝ) < j + 1 := lt_of_mul_lt_mul_right a2 ht.le
  have c1 : j < k + 1 := by exact_mod_cast b1
  have c2 : k < j + 1 := by exact_mod_cast b2
  omega

lemma step_sq (t : ℝ≥0) (n : ℕ) (b : ℕ → Ω → ℝ) (ω : Ω) (u : ℝ) :
    (itoStepValue t n b u ω) ^ 2 = itoStepValue t n (fun k ω => b k ω ^ 2) u ω := by
  classical
  unfold itoStepValue
  by_cases h : ∃ k ∈ Finset.range (2 ^ n),
      (k : ℝ) * t.val / 2 ^ n < u ∧ u ≤ ((k : ℝ) + 1) * t.val / 2 ^ n
  · obtain ⟨k0, hk0, hc⟩ := h
    have uniq : ∀ j, j ≠ k0 →
        ¬ ((j : ℝ) * t.val / 2 ^ n < u ∧ u ≤ ((j : ℝ) + 1) * t.val / 2 ^ n) :=
      fun j hne hj => hne (cell_uniq t n j k0 u hj hc)
    rw [Finset.sum_eq_single k0 (fun j _ hne => if_neg (uniq j hne)) (fun h => absurd hk0 h),
      Finset.sum_eq_single k0 (fun j _ hne => if_neg (uniq j hne)) (fun h => absurd hk0 h),
      if_pos hc, if_pos hc]
  · push_neg at h
    rw [Finset.sum_eq_zero (fun j hj => if_neg (by
        intro hc; exact absurd hc.2 (not_le.mpr (h j hj hc.1)))),
      Finset.sum_eq_zero (fun j hj => if_neg (by
        intro hc; exact absurd hc.2 (not_le.mpr (h j hj hc.1))))]
    simp

lemma step_int (t : ℝ≥0) (n : ℕ) (b : ℕ → Ω → ℝ) (ω : Ω) :
    ∫ u in (0 : ℝ)..t.val, itoStepValue t n b u ω =
      ∑ k ∈ Finset.range (2 ^ n), b k ω * (t.val / 2 ^ n) := by
  unfold itoStepValue
  rw [intervalIntegral.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro k hk
    have hk' : (k : ℝ) + 1 ≤ 2 ^ n := by
      have := Finset.mem_range.mp hk
      exact_mod_cast this
    have h2 : (0 : ℝ) < 2 ^ n := by positivity
    have e : (fun u : ℝ => if (k : ℝ) * t.val / 2 ^ n < u ∧ u ≤ ((k : ℝ) + 1) * t.val / 2 ^ n
        then b k ω else 0) = Set.indicator (Ioc ((k : ℝ) * t.val / 2 ^ n)
          (((k : ℝ) + 1) * t.val / 2 ^ n)) (fun _ => b k ω) := by
      ext u; rw [Set.indicator_apply]; simp only [Set.mem_Ioc]
    have hsub : Ioc ((k : ℝ) * t.val / 2 ^ n) (((k : ℝ) + 1) * t.val / 2 ^ n) ⊆
        Ioc 0 t.val := by
      apply Ioc_subset_Ioc
      · exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) t.2) h2.le
      · rw [div_le_iff₀ h2]
        nlinarith [t.2]
    rw [e, intervalIntegral.integral_of_le t.2, integral_indicator_const _ measurableSet_Ioc,
      smul_eq_mul, measureReal_def, Measure.restrict_apply measurableSet_Ioc,
      inter_eq_left.mpr hsub, Real.volume_Ioc, ENNReal.toReal_ofReal]
    · ring
    · rw [sub_nonneg, div_le_div_iff_of_pos_right h2]
      nlinarith [t.2]
  · intro k _
    refine ii_bdd (C := |b k ω|) (Measurable.ite (measurableSet_Ioc
      (a := (k : ℝ) * t.val / 2 ^ n) (b := ((k : ℝ) + 1) * t.val / 2 ^ n))
      measurable_const measurable_const) (fun u => ?_) _ _
    split_ifs <;> simp

lemma step_sq_int (t : ℝ≥0) (n : ℕ) (b : ℕ → Ω → ℝ) (ω : Ω) :
    ∫ u in (0 : ℝ)..t.val, (itoStepValue t n b u ω) ^ 2 =
      ∑ k ∈ Finset.range (2 ^ n), b k ω ^ 2 * (t.val / 2 ^ n) := by
  simp_rw [step_sq]
  exact step_int t n (fun k ω => b k ω ^ 2) ω

end LMVAux


open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace LMVAux

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

open EthierKurtz

lemma tim_sub {P : Measure Ω} {S S' : ℕ → Ω → ℝ} {J J' : Ω → ℝ}
    (h1 : TendstoInMeasure P S atTop J) (h2 : TendstoInMeasure P S' atTop J') :
    TendstoInMeasure P (fun n ω => S n ω - S' n ω) atTop (fun ω => J ω - J' ω) := by
  rw [tendstoInMeasure_iff_norm] at *
  intro ε hε
  have a := h1 (ε / 2) (by linarith)
  have b := h2 (ε / 2) (by linarith)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using a.add b) (fun _ => bot_le) (fun n => ?_)
  refine (measure_mono ?_).trans (measure_union_le _ _)
  intro ω hω
  simp only [Set.mem_setOf_eq, Set.mem_union] at *
  by_contra hc
  push_neg at hc
  have : ‖S n ω - S' n ω - (J ω - J' ω)‖ ≤ ‖S n ω - J ω‖ + ‖S' n ω - J' ω‖ := by
    rw [show S n ω - S' n ω - (J ω - J' ω) = (S n ω - J ω) - (S' n ω - J' ω) by ring]
    exact norm_sub_le _ _
  simp only [Real.norm_eq_abs] at this hω
  linarith [hc.1, hc.2]

lemma ii_sq_diff (t : ℝ≥0) (n : ℕ) (b : ℕ → Ω → ℝ) (ω : Ω) (H : ℝ → ℝ) (hH : Measurable H)
    (hsq : IntervalIntegrable (fun u => H u ^ 2) volume 0 t.val) :
    IntervalIntegrable (fun u => (itoStepValue t n b u ω - H u) ^ 2) volume 0 t.val := by
  have hs : IntervalIntegrable (fun u => (itoStepValue t n b u ω) ^ 2) volume 0 t.val := by
    refine ii_bdd ((step_meas t n b ω).pow_const 2) (C := (∑ k ∈ Finset.range (2 ^ n),
      |b k ω|) ^ 2) (fun u => ?_) _ _
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (step_bdd t n b ω u) 2
  refine (((hs.const_mul 2).add (hsq.const_mul 2))).mono_fun
    (((step_meas t n b ω).sub hH).pow_const 2).aestronglyMeasurable
    (Eventually.of_forall fun u => ?_)
  simp only [Real.norm_eq_abs, Pi.add_apply]
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  nlinarith [sq_nonneg (itoStepValue t n b u ω + H u)]

theorem ito_unique (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsPreBrownianReal W P) (hWm : ∀ s, Measurable (W s))
    (H J J' : ℝ≥0 → Ω → ℝ) (hH : ∀ ω, Measurable fun u : ℝ => H u.toNNReal ω)
    (h1 : HasBrownianItoIntegral P (natFilt W) W H J)
    (h2 : HasBrownianItoIntegral P (natFilt W) W H J') (t : ℝ≥0) : J t =ᵐ[P] J' t := by
  classical
  obtain ⟨hsq, h1⟩ := h1
  obtain ⟨-, h2⟩ := h2
  obtain ⟨a, ham, hab, hconv, hsum⟩ := h1 t
  obtain ⟨a', ham', hab', hconv', hsum'⟩ := h2 t
  have hD := tim_sub hsum hsum'
  suffices h0 : TendstoInMeasure P (fun n ω => itoStepSum W t n (a n) ω -
      itoStepSum W t n (a' n) ω) atTop (fun _ => 0) by
    have := tendstoInMeasure_ae_unique hD h0
    filter_upwards [this] with ω hω
    exact sub_eq_zero.mp hω
  rw [tendstoInMeasure_iff_measureReal_norm]
  rw [tendstoInMeasure_iff_measureReal_norm] at hconv hconv'
  intro ε hε
  rw [Metric.tendsto_atTop]
  intro e he
  set η := e * ε ^ 2 / 3 with hηdef
  have hη : 0 < η := by positivity
  obtain ⟨N1, hN1⟩ := Metric.tendsto_atTop.mp (hconv (η / 4) (by positivity)) (e / 3)
    (by positivity)
  obtain ⟨N2, hN2⟩ := Metric.tendsto_atTop.mp (hconv' (η / 4) (by positivity)) (e / 3)
    (by positivity)
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have hn1 := hN1 n (le_of_max_le_left hn)
  have hn2 := hN2 n (le_of_max_le_right hn)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] at hn1 hn2
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  obtain ⟨C1, hC1⟩ := hab n
  obtain ⟨C2, hC2⟩ := hab' n
  -- Lenglart data
  set δ : ℝ := t.val / 2 ^ n with hδ
  set G : ℕ → MeasurableSpace Ω := fun k => natFilt W ((k : ℝ≥0) * t / 2 ^ n) with hG
  set X : ℕ → Ω → ℝ := fun k ω => W (((k : ℝ≥0) + 1) * t / 2 ^ n) ω -
    W ((k : ℝ≥0) * t / 2 ^ n) ω with hX
  set c : ℕ → Ω → ℝ := fun k ω => if k < 2 ^ n then a n k ω - a' n k ω else 0 with hc
  have hGmono : Monotone G := by
    intro i j hij
    apply natFilt_mono
    have : (i : ℝ≥0) ≤ j := by exact_mod_cast hij
    gcongr
  have hgrid : ∀ k : ℕ, (k : ℝ≥0) * t / 2 ^ n ≤ ((k : ℝ≥0) + 1) * t / 2 ^ n := by
    intro k; gcongr; exact le_self_add
  have hXm : ∀ k, Measurable[G (k+1)] (X k) := by
    intro k
    have e1 : ((k + 1 : ℕ) : ℝ≥0) * t / 2 ^ n = ((k : ℝ≥0) + 1) * t / 2 ^ n := by push_cast; rfl
    show Measurable[natFilt W (((k + 1 : ℕ) : ℝ≥0) * t / 2 ^ n)]
      (fun ω => W (((k : ℝ≥0) + 1) * t / 2 ^ n) ω - W ((k : ℝ≥0) * t / 2 ^ n) ω)
    rw [e1]
    exact Measurable.sub (meas_natFilt W le_rfl) (meas_natFilt W (hgrid k))
  have hXind : ∀ k, Indep (G k) (MeasurableSpace.comap (X k) inferInstance) P :=
    fun k => indep_incr hW le_rfl (hgrid k)
  have hmom : ∀ k, ∫ ω, X k ω ∂P = 0 ∧ ∫ ω, X k ω ^ 2 ∂P = δ ∧ MemLp (X k) 2 P := by
    intro k
    obtain ⟨m1, m2, m3⟩ := incr_moments hW (hgrid k)
    refine ⟨m1, ?_, m3⟩
    rw [m2, hδ]
    push_cast
    simp only [NNReal.val_eq_coe]
    ring
  have hcm : ∀ k, Measurable[G k] (c k) := by
    intro k
    simp only [hc]
    split_ifs with hk
    · exact (ham n k hk).sub (ham' n k hk)
    · exact measurable_const
  have hcb : ∀ k ω, |c k ω| ≤ C1 + C2 := by
    intro k ω
    simp only [hc]
    split_ifs with hk
    · exact (abs_sub _ _).trans (add_le_add (hC1 k hk ω) (hC2 k hk ω))
    · simp only [abs_zero]
      have h0 := hC1 0 (by positivity) ω
      have h0' := hC2 0 (by positivity) ω
      linarith [abs_nonneg (a n 0 ω), abs_nonneg (a' n 0 ω)]
  have hL := lenglart P G hGmono (fun k => natFilt_le hWm _) X hXm hXind
    (fun k => (hmom k).1) (fun k => (hmom k).2.2) δ (fun k => (hmom k).2.1)
    (div_nonneg t.2 (by positivity)) c hcm (fun _ => C1 + C2) hcb (2 ^ n) η ε hη hε
  have hDeq : ∀ ω, itoStepSum W t n (a n) ω - itoStepSum W t n (a' n) ω =
      ∑ k ∈ Finset.range (2 ^ n), c k ω * X k ω := by
    intro ω
    unfold itoStepSum
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [hc, hX, if_pos (Finset.mem_range.mp hk)]
    ring
  -- the quadratic variation bound
  set A : ℕ → Ω → ℝ := fun n ω => ∫ u in (0 : ℝ)..t.val,
    (itoStepValue t n (a n) u ω - H u.toNNReal ω) ^ 2 with hA
  set A' : ℕ → Ω → ℝ := fun n ω => ∫ u in (0 : ℝ)..t.val,
    (itoStepValue t n (a' n) u ω - H u.toNNReal ω) ^ 2 with hA'
  have hQ : ∀ ω, ∑ k ∈ Finset.range (2 ^ n), c k ω ^ 2 * δ ≤ 2 * A n ω + 2 * A' n ω := by
    intro ω
    have e1 : ∑ k ∈ Finset.range (2 ^ n), c k ω ^ 2 * δ =
        ∫ u in (0 : ℝ)..t.val, (itoStepValue t n (a n) u ω - itoStepValue t n (a' n) u ω) ^ 2 := by
      simp_rw [step_sub]
      rw [step_sq_int]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [hc, if_pos (Finset.mem_range.mp hk), hδ, NNReal.val_eq_coe]
    rw [e1]
    have i1 := ii_sq_diff t n (a n) ω (fun u => H u.toNNReal ω) (hH ω) (hsq t ω)
    have i2 := ii_sq_diff t n (a' n) ω (fun u => H u.toNNReal ω) (hH ω) (hsq t ω)
    have i3 : IntervalIntegrable (fun u => (itoStepValue t n (a n) u ω -
        itoStepValue t n (a' n) u ω) ^ 2) volume 0 t.val := by
      simp_rw [step_sub]
      refine ii_bdd ((step_meas t n _ ω).pow_const 2) (C := (∑ k ∈ Finset.range (2 ^ n),
        |a n k ω - a' n k ω|) ^ 2) (fun u => ?_) _ _
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (step_bdd t n _ ω u) 2
    rw [hA, hA', ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (i1.const_mul 2) (i2.const_mul 2)]
    refine intervalIntegral.integral_mono_on t.2 i3 ((i1.const_mul 2).add (i2.const_mul 2))
      (fun u _ => ?_)
    nlinarith [sq_nonneg (itoStepValue t n (a n) u ω + itoStepValue t n (a' n) u ω -
      2 * H u.toNNReal ω)]
  have hsub : {ω | η < ∑ k ∈ Finset.range (2 ^ n), c k ω ^ 2 * δ} ⊆
      {ω | η / 4 ≤ ‖A n ω - 0‖} ∪ {ω | η / 4 ≤ ‖A' n ω - 0‖} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Set.mem_union, sub_zero, Real.norm_eq_abs] at *
    by_contra hcon
    push_neg at hcon
    have := hQ ω
    linarith [le_abs_self (A n ω), le_abs_self (A' n ω), hcon.1, hcon.2]
  have hm := (measureReal_mono (μ := P) hsub (measure_ne_top P _)).trans (measureReal_union_le _ _)
  have hset : {x | ε ≤ ‖itoStepSum W t n (a n) x - itoStepSum W t n (a' n) x - 0‖} =
      {ω | ε ≤ |∑ k ∈ Finset.range (2 ^ n), c k ω * X k ω|} := by
    ext ω; simp [hDeq ω, Real.norm_eq_abs]
  rw [hset]
  have : η / ε ^ 2 = e / 3 := by rw [hηdef]; field_simp
  calc _ ≤ η / ε ^ 2 + P.real {ω | η < ∑ k ∈ Finset.range (2 ^ n), c k ω ^ 2 * δ} := hL
    _ < e := by
      rw [this]
      have h1' : P.real {ω | η / 4 ≤ ‖A n ω - 0‖} < e / 3 := hn1
      have h2' : P.real {ω | η / 4 ≤ ‖A' n ω - 0‖} < e / 3 := hn2
      linarith

end LMVAux


open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace LMVAux

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

open EthierKurtz

/-- right-continuous step function -/
noncomputable def stepG {m : ℕ} (d : Fin m → ℝ) (s : Fin m → ℝ≥0) (u : ℝ≥0) : ℝ :=
  ∑ i, d i * (if s i ≤ u then 1 else 0)

lemma stepG_bdd {m : ℕ} (d : Fin m → ℝ) (s : Fin m → ℝ≥0) (u : ℝ≥0) :
    |stepG d s u| ≤ ∑ i, |d i| := by
  unfold stepG
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  split_ifs <;> simp

lemma stepG_meas {m : ℕ} (d : Fin m → ℝ) (s : Fin m → ℝ≥0) :
    Measurable (fun u : ℝ => stepG d s u.toNNReal) := by
  unfold stepG
  apply Finset.measurable_sum
  intro i _
  apply Measurable.const_mul
  exact Measurable.ite (measurableSet_le measurable_const measurable_real_toNNReal)
    measurable_const measurable_const

lemma step_eq_single (t : ℝ≥0) (n : ℕ) (b : ℕ → Ω → ℝ) (ω : Ω) (u : ℝ) (k0 : ℕ)
    (hk0 : k0 < 2 ^ n)
    (hc : (k0 : ℝ) * t.val / 2 ^ n < u ∧ u ≤ ((k0 : ℝ) + 1) * t.val / 2 ^ n) :
    itoStepValue t n b u ω = b k0 ω := by
  classical
  unfold itoStepValue
  have uniq : ∀ j, j ≠ k0 →
      ¬ ((j : ℝ) * t.val / 2 ^ n < u ∧ u ≤ ((j : ℝ) + 1) * t.val / 2 ^ n) :=
    fun j hne hj => hne (cell_uniq t n j k0 u hj hc)
  rw [Finset.sum_eq_single k0 (fun j _ hne => if_neg (uniq j hne))
    (fun h => absurd (Finset.mem_range.mpr hk0) h), if_pos hc]

lemma step_cell_exists (t : ℝ≥0) (n : ℕ) (u : ℝ) (hu : 0 < u) (hut : u ≤ t.val) :
    ∃ k : ℕ, k < 2 ^ n ∧ (k : ℝ) * t.val / 2 ^ n < u ∧ u ≤ ((k : ℝ) + 1) * t.val / 2 ^ n := by
  have ht : 0 < t.val := hu.trans_le hut
  have h2 : (0:ℝ) < 2 ^ n := by positivity
  set y := u * 2 ^ n / t.val with hy
  have hy0 : 0 < y := by positivity
  have hyN : y ≤ 2 ^ n := by rw [hy, div_le_iff₀ ht]; nlinarith
  have hc1 : 1 ≤ ⌈y⌉₊ := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hy0).ne'
  refine ⟨⌈y⌉₊ - 1, ?_, ?_, ?_⟩
  · have : ⌈y⌉₊ ≤ 2 ^ n := Nat.ceil_le.mpr (by exact_mod_cast hyN)
    omega
  · have hlt : (⌈y⌉₊ : ℝ) < y + 1 := Nat.ceil_lt_add_one hy0.le
    have hcast : ((⌈y⌉₊ - 1 : ℕ) : ℝ) = (⌈y⌉₊ : ℝ) - 1 := by rw [Nat.cast_sub hc1]; simp
    rw [hcast, div_lt_iff₀ h2]
    have : ((⌈y⌉₊ : ℝ) - 1) < u * 2 ^ n / t.val := by linarith
    rw [lt_div_iff₀ ht] at this
    linarith
  · have hle : y ≤ (⌈y⌉₊ : ℝ) := Nat.le_ceil y
    have hcast : ((⌈y⌉₊ - 1 : ℕ) : ℝ) + 1 = (⌈y⌉₊ : ℝ) := by rw [Nat.cast_sub hc1]; simp
    rw [hcast, le_div_iff₀ h2]
    rw [hy, div_le_iff₀ ht] at hle
    linarith

lemma step_bdd' (t : ℝ≥0) (n : ℕ) (b : ℕ → Ω → ℝ) (ω : Ω) (u : ℝ) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ k, |b k ω| ≤ C) : |itoStepValue t n b u ω| ≤ C := by
  classical
  by_cases h : ∃ k : ℕ, k < 2 ^ n ∧
      (k : ℝ) * t.val / 2 ^ n < u ∧ u ≤ ((k : ℝ) + 1) * t.val / 2 ^ n
  · obtain ⟨k, hk, hc⟩ := h
    rw [step_eq_single t n b ω u k hk hc]; exact hC k
  · push_neg at h
    unfold itoStepValue
    rw [Finset.sum_eq_zero (fun j hj => if_neg (by
        intro hc; exact absurd hc.2 (not_le.mpr (h j (Finset.mem_range.mp hj) hc.1))))]
    simpa using hC0

lemma telesc (f : ℕ → ℝ) (m N : ℕ) :
    ∑ k ∈ Finset.range N, (if m ≤ k then f (k+1) - f k else 0) = f N - f (min m N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases h : m ≤ N
    · rw [if_pos h, min_eq_left h, min_eq_left (by omega)]; ring
    · rw [if_neg h, min_eq_right (by omega), min_eq_right (by omega)]; ring

lemma tim_const {P : Measure Ω} {c : ℕ → ℝ} (hc : Tendsto c atTop (𝓝 0)) :
    TendstoInMeasure P (fun n (_ : Ω) => c n) atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have : ∀ᶠ n in atTop, ‖c n‖ < ε := by
    have := (tendsto_norm_zero.comp hc)
    exact (tendsto_order.1 this).2 ε hε
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [this] with n hn
  have : {x : Ω | ε ≤ ‖c n - 0‖} = ∅ := by
    ext x; simp only [sub_zero, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
    exact hn
  rw [this, measure_empty]

lemma grid_tendsto (τ s : ℝ≥0) (hτ : 0 < τ) :
    Tendsto (fun n : ℕ => ((min ⌈s * 2 ^ n / τ⌉₊ (2 ^ n) : ℕ) : ℝ≥0) * τ / 2 ^ n) atTop
      (𝓝 (min s τ)) := by
  have e : ∀ n : ℕ, ((min ⌈s * 2 ^ n / τ⌉₊ (2 ^ n) : ℕ) : ℝ≥0) * τ / 2 ^ n =
      min ((⌈s * 2 ^ n / τ⌉₊ : ℝ≥0) * τ / 2 ^ n) τ := by
    intro n
    have h2 : (0 : ℝ≥0) < 2 ^ n := by positivity
    rw [Nat.cast_min]
    have hm : Monotone (fun x : ℝ≥0 => x * τ / 2 ^ n) := fun a b hab => by
      simp only; gcongr
    rw [hm.map_min]
    congr 1
    push_cast
    field_simp
  simp_rw [e]
  refine Tendsto.min ?_ tendsto_const_nhds
  rw [← NNReal.tendsto_coe]
  have hτr : (0 : ℝ) < τ := hτ
  have lo : ∀ n : ℕ, (s : ℝ) ≤ (((⌈s * 2 ^ n / τ⌉₊ : ℝ≥0) * τ / 2 ^ n : ℝ≥0) : ℝ) := by
    intro n
    have h1 : s * 2 ^ n / τ ≤ (⌈s * 2 ^ n / τ⌉₊ : ℝ≥0) := Nat.le_ceil _
    have h1r : (s : ℝ) * 2 ^ n / τ ≤ (⌈s * 2 ^ n / τ⌉₊ : ℝ) := by exact_mod_cast h1
    push_cast
    rw [le_div_iff₀ (by positivity)]
    rw [div_le_iff₀ hτr] at h1r
    linarith
  have hi : ∀ n : ℕ, (((⌈s * 2 ^ n / τ⌉₊ : ℝ≥0) * τ / 2 ^ n : ℝ≥0) : ℝ) ≤
      (s : ℝ) + τ * (1 / 2) ^ n := by
    intro n
    have h1 : (⌈s * 2 ^ n / τ⌉₊ : ℝ≥0) < s * 2 ^ n / τ + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have h1r : (⌈s * 2 ^ n / τ⌉₊ : ℝ) < (s : ℝ) * 2 ^ n / τ + 1 := by exact_mod_cast h1
    push_cast
    rw [div_le_iff₀ (by positivity)]
    have : (⌈s * 2 ^ n / τ⌉₊ : ℝ) * τ < (s : ℝ) * 2 ^ n + τ := by
      have := mul_lt_mul_of_pos_right h1r hτr
      rw [add_mul, div_mul_cancel₀ _ hτr.ne'] at this
      linarith
    have e2 : ((s : ℝ) + τ * (1 / 2) ^ n) * 2 ^ n = (s : ℝ) * 2 ^ n + τ := by
      rw [add_mul, mul_assoc, ← mul_pow]; norm_num
    rw [e2]; linarith
  have hlim : Tendsto (fun n : ℕ => (s : ℝ) + τ * (1 / 2) ^ n) atTop (𝓝 (s : ℝ)) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul (τ : ℝ)
    simpa using tendsto_const_nhds.add this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim lo hi

end LMVAux


open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology Interval

namespace LMVAux

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

open EthierKurtz

lemma tendsto_grid_width (τ : ℝ≥0) :
    Tendsto (fun n : ℕ => τ.val / 2 ^ n) atTop (𝓝 0) := by
  have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)).const_mul τ.val
  simp only [mul_zero] at this
  refine this.congr fun n => ?_
  rw [one_div_pow, mul_one_div]

lemma step_pointwise (τ : ℝ≥0) {m : ℕ} (d : Fin m → ℝ) (s : Fin m → ℝ≥0) (u : ℝ)
    (hu : 0 < u) (huτ : u ≤ τ.val) (hus : ∀ i, (s i : ℝ) ≠ u) :
    ∀ᶠ n in atTop, itoStepValue (Ω := Unit) τ n
      (fun k _ => stepG d s ((k : ℝ≥0) * τ / 2 ^ n)) u () = stepG d s u.toNNReal := by
  have hev : ∀ᶠ n in atTop, ∀ i, (s i : ℝ) < u → τ.val / 2 ^ n < u - s i := by
    rw [Filter.eventually_all]
    intro i
    by_cases h : (s i : ℝ) < u
    · have := (tendsto_order.1 (tendsto_grid_width τ)).2 (u - s i) (by linarith)
      filter_upwards [this] with n hn
      intro _; exact hn
    · exact Eventually.of_forall fun n hn => absurd hn h
  filter_upwards [hev] with n hn
  obtain ⟨k, hk, hc⟩ := step_cell_exists τ n u hu huτ
  rw [step_eq_single τ n _ () u k hk hc]
  unfold stepG
  apply Finset.sum_congr rfl
  intro i _
  have hiff : s i ≤ (k : ℝ≥0) * τ / 2 ^ n ↔ s i ≤ u.toNNReal := by
    rw [Real.le_toNNReal_iff_coe_le hu.le, ← NNReal.coe_le_coe]
    push_cast
    simp only [NNReal.val_eq_coe] at hc hn
    have h2 : (0 : ℝ) < 2 ^ n := by positivity
    have e1 : ((k : ℝ) + 1) * (τ : ℝ) / 2 ^ n = (k : ℝ) * τ / 2 ^ n + τ / 2 ^ n := by ring
    rcases lt_or_gt_of_ne (hus i) with h | h
    · have := hn i h
      constructor <;> intro <;> linarith [hc.2, e1]
    · constructor <;> intro <;> linarith [hc.1]
  by_cases h1 : s i ≤ (k : ℝ≥0) * τ / 2 ^ n
  · rw [if_pos h1, if_pos (hiff.mp h1)]
  · rw [if_neg h1, if_neg (fun h => h1 (hiff.mpr h))]

lemma stepsum_formula (W : ℝ≥0 → Ω → ℝ) (τ : ℝ≥0) (hτ : 0 < τ) (n : ℕ) {m : ℕ}
    (d : Fin m → ℝ) (s : Fin m → ℝ≥0) (ω : Ω) :
    itoStepSum W τ n (fun k _ => stepG d s ((k : ℝ≥0) * τ / 2 ^ n)) ω =
      ∑ i, d i * (W τ ω - W (((min ⌈s i * 2 ^ n / τ⌉₊ (2 ^ n) : ℕ) : ℝ≥0) * τ / 2 ^ n) ω) := by
  unfold itoStepSum stepG
  simp_rw [Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_sum]
  congr 1
  set f : ℕ → ℝ := fun k => W ((k : ℝ≥0) * τ / 2 ^ n) ω with hf
  have h2 : (0 : ℝ≥0) < 2 ^ n := by positivity
  have hterm : ∀ k ∈ Finset.range (2 ^ n), (if s i ≤ (k : ℝ≥0) * τ / 2 ^ n then (1 : ℝ) else 0) *
      (W (((k : ℝ≥0) + 1) * τ / 2 ^ n) ω - W ((k : ℝ≥0) * τ / 2 ^ n) ω) =
      if ⌈s i * 2 ^ n / τ⌉₊ ≤ k then f (k + 1) - f k else 0 := by
    intro k _
    have hiff : s i ≤ (k : ℝ≥0) * τ / 2 ^ n ↔ ⌈s i * 2 ^ n / τ⌉₊ ≤ k := by
      rw [Nat.ceil_le, div_le_iff₀ hτ, le_div_iff₀ h2]
    have hc : ((k + 1 : ℕ) : ℝ≥0) = (k : ℝ≥0) + 1 := by push_cast; rfl
    by_cases h : s i ≤ (k : ℝ≥0) * τ / 2 ^ n
    · rw [if_pos h, if_pos (hiff.mp h), one_mul, hf]
      simp only [hc]
    · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h')), zero_mul]
  rw [Finset.sum_congr rfl hterm, telesc]
  have hN : ((2 ^ n : ℕ) : ℝ≥0) * τ / 2 ^ n = τ := by
    push_cast; field_simp
  simp only [hf, hN]

theorem ito_step_exists (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsBrownianReal W P) (hWm : ∀ s, Measurable (W s))
    {m : ℕ} (d : Fin m → ℝ) (s : Fin m → ℝ≥0) (H : ℝ≥0 → Ω → ℝ) (e : ℝ≥0)
    (hH : ∀ u ω, u ≠ e → H u ω = stepG d s u) :
    HasBrownianItoIntegral P (natFilt W) W H
      (fun u ω => ∑ i, d i * (W u ω - W (min u (s i)) ω)) := by
  set D := ∑ i, |d i| with hD
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hae : ∀ (τ : ℝ≥0) (ω : Ω), ∀ᵐ u ∂volume, u ∈ Ι 0 τ.val →
      H u.toNNReal ω = stepG d s u.toNNReal := by
    intro τ ω
    filter_upwards [(Set.countable_singleton (e : ℝ)).ae_notMem volume] with u hu hmem
    apply hH
    intro heq
    have hpos : 0 < u := by
      rcases Set.mem_uIoc.mp hmem with h | h
      · exact h.1
      · exfalso; linarith [h.1, h.2, τ.2]
    apply hu
    rw [Set.mem_singleton_iff, ← heq, Real.coe_toNNReal u hpos.le]
  refine ⟨fun τ ω => ?_, fun τ => ?_⟩
  · have hg : IntervalIntegrable (fun u : ℝ => stepG d s u.toNNReal ^ 2) volume 0 τ.val := by
      refine ii_bdd ((stepG_meas d s).pow_const 2) (C := D ^ 2) (fun u => ?_) _ _
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (stepG_bdd d s _) 2
    refine hg.congr_ae ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [hae τ ω] with u hu hmem
    rw [hu hmem]
  refine ⟨fun n k _ => stepG d s ((k : ℝ≥0) * τ / 2 ^ n), fun n k _ => measurable_const,
    fun n => ⟨D, fun k _ ω => stepG_bdd d s _⟩, ?_, ?_⟩
  · -- integrand convergence
    set c : ℕ → ℝ := fun n => ∫ u in (0 : ℝ)..τ.val,
      (itoStepValue (Ω := Unit) τ n (fun k _ => stepG d s ((k : ℝ≥0) * τ / 2 ^ n)) u () -
        stepG d s u.toNNReal) ^ 2 with hc
    have hfun : (fun n ω => ∫ u in (0 : ℝ)..τ.val, (itoStepValue τ n
        (fun k (_ : Ω) => stepG d s ((k : ℝ≥0) * τ / 2 ^ n)) u ω - H u.toNNReal ω) ^ 2) =
        fun n _ => c n := by
      funext n ω
      rw [hc]
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hae τ ω] with u hu hmem
      rw [hu hmem]
      rfl
    rw [hfun]
    apply tim_const
    have hlim := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (a := 0) (b := τ.val) (l := atTop) (f := fun _ => (0 : ℝ))
      (F := fun n u => (itoStepValue (Ω := Unit) τ n
        (fun k _ => stepG d s ((k : ℝ≥0) * τ / 2 ^ n)) u () - stepG d s u.toNNReal) ^ 2)
      (fun _ => (2 * D) ^ 2)
      (Eventually.of_forall fun n =>
        (((step_meas τ n _ ()).sub (stepG_meas d s)).pow_const 2).aestronglyMeasurable)
      (Eventually.of_forall fun n => Eventually.of_forall fun u _ => by
        rw [Real.norm_eq_abs, abs_pow]
        apply pow_le_pow_left₀ (abs_nonneg _)
        have h1 := step_bdd' τ n (fun k (_ : Unit) => stepG d s ((k : ℝ≥0) * τ / 2 ^ n)) () u D
          hD0 (fun k => stepG_bdd d s _)
        have h2 := stepG_bdd d s u.toNNReal
        calc |_ - _| ≤ |itoStepValue (Ω := Unit) τ n
              (fun k _ => stepG d s ((k : ℝ≥0) * τ / 2 ^ n)) u ()| +
              |stepG d s u.toNNReal| := abs_sub _ _
          _ ≤ 2 * D := by linarith)
      intervalIntegrable_const
      (by
        filter_upwards [(Set.finite_range (fun i => (s i : ℝ))).countable.ae_notMem volume]
          with u hu hmem
        have hpos : 0 < u := by
          rcases Set.mem_uIoc.mp hmem with h | h
          · exact h.1
          · exfalso; linarith [h.1, h.2, τ.2]
        have huτ : u ≤ τ.val := by
          rcases Set.mem_uIoc.mp hmem with h | h
          · exact h.2
          · exfalso; linarith [h.1, h.2, τ.2]
        have hus : ∀ i, (s i : ℝ) ≠ u := fun i h => hu ⟨i, h⟩
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [step_pointwise τ d s u hpos huτ hus] with n hn
        simp only [hn, sub_self]
        norm_num)
    simp only [intervalIntegral.integral_zero] at hlim
    exact hlim
  · -- step sums converge
    rcases eq_zero_or_pos τ with hτ | hτ
    swap
    · refine tendstoInMeasure_of_tendsto_ae (fun n => ?_) ?_
      · unfold itoStepSum
        exact (Finset.measurable_sum _ fun k _ =>
          measurable_const.mul ((hWm _).sub (hWm _))).aestronglyMeasurable
      · filter_upwards [hW.cont] with ω hω
        simp_rw [stepsum_formula W τ hτ _ d s ω]
        apply tendsto_finset_sum
        intro i _
        refine Tendsto.const_mul _ (Tendsto.sub tendsto_const_nhds ?_)
        rw [min_comm]
        exact (hω.tendsto _).comp (grid_tendsto τ (s i) hτ)
    · subst hτ
      have h0 : ∀ n, itoStepSum W 0 n (fun k _ => stepG d s ((k : ℝ≥0) * 0 / 2 ^ n)) =
          fun ω => ∑ i, d i * (W 0 ω - W (min 0 (s i)) ω) := by
        intro n; funext ω
        unfold itoStepSum
        simp
      simp_rw [h0]
      exact tendstoInMeasure_of_tendsto_ae (fun n => by
        exact (Finset.measurable_sum _ fun i _ =>
          measurable_const.mul ((hWm _).sub (hWm _))).aestronglyMeasurable)
        (Eventually.of_forall fun ω => tendsto_const_nhds)

end LMVAux


open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology Interval

namespace LMVAux
open LogMeanVar.Complete EthierKurtz

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

noncomputable def Istar (W : ℝ≥0 → Ω → ℝ) {m : ℕ} (d : Fin m → ℝ) (sj : Fin m → ℝ≥0)
    (u : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i, d i * (W u ω - W (min u (sj i)) ω)

noncomputable def Rstar (M : Market) (B : ℝ≥0 → Ω → ℝ) (p : ℝ → ℝ) (t0 y : ℝ) {m : ℕ}
    (d : Fin m → ℝ) (sj : Fin m → ℝ≥0) : ℝ → Ω → ℝ :=
  fun s ω => y + (∫ τ in t0..s, (M.r + (M.μ - M.r) * p τ - M.σ ^ 2 * (p τ) ^ 2 / 2))
    + Istar (shiftBM B t0) d sj (s - t0).toNNReal ω

lemma shift_brownian {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (t0 : ℝ) :
    IsBrownianReal (shiftBM B t0) P := hB.shift t0.toNNReal

lemma shift_meas {B : ℝ≥0 → Ω → ℝ} (hBm : ∀ s, Measurable (B s)) (t0 : ℝ) (u : ℝ≥0) :
    Measurable (shiftBM B t0 u) := (hBm _).sub (hBm _)

lemma Istar_meas (W : ℝ≥0 → Ω → ℝ) {m : ℕ} (d : Fin m → ℝ) (sj : Fin m → ℝ≥0) (u : ℝ≥0) :
    Measurable[natFilt W u] (Istar W d sj u) := by
  unfold Istar
  apply Finset.measurable_sum
  intro i _
  exact measurable_const.mul ((meas_natFilt W le_rfl).sub (meas_natFilt W (min_le_left _ _)))

lemma integrand_meas (M : Market) (p : ℝ → ℝ) (hp : Measurable p) (t0 : ℝ)
    (R : ℝ → Ω → ℝ) (ω : Ω) :
    Measurable fun u : ℝ => logReturnIntegrand M (fun τ _ => p τ) t0 R u.toNNReal ω := by
  unfold logReturnIntegrand
  by_cases hII : IntervalIntegrable (fun τ => p τ ^ 2) volume t0 M.T
  · simp only [hII, and_true]
    refine Measurable.ite ?_ (measurable_const.mul (hp.comp ?_)) measurable_const
    · exact measurableSet_le (by fun_prop) measurable_const
    · fun_prop
  · simp only [hII, and_false, if_false]
    exact measurable_const

theorem det_solution (M : Market) (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (hBm : ∀ s, Measurable (B s))
    (p : ℝ → ℝ) (hp : Measurable p) (K : ℝ) (hK : ∀ τ, |p τ| ≤ K) (t0 y : ℝ) {m : ℕ}
    (d : Fin m → ℝ) (sj : Fin m → ℝ≥0) (e : ℝ≥0)
    (hrep : ∀ u : ℝ≥0, u ≠ e →
      (if t0 + (u : ℝ) ≤ M.T then M.σ * p (t0 + u) else 0) = stepG d sj u) :
    IsLogReturn M P B (fun τ _ => p τ) t0 y (Rstar M B p t0 y d sj) ∧
    ∀ R, IsLogReturn M P B (fun τ _ => p τ) t0 y R →
      ∀ s ∈ Icc t0 M.T, R s =ᵐ[P] Rstar M B p t0 y d sj s := by
  have hWB := shift_brownian hB t0
  have hWm := shift_meas hBm t0
  have hII : ∀ a b, IntervalIntegrable (fun τ => p τ ^ 2) volume a b := fun a b =>
    ii_bdd (hp.pow_const 2) (C := K ^ 2) (fun τ => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hK τ) 2) a b
  have hII1 : ∀ a b, IntervalIntegrable p volume a b := fun a b => ii_bdd hp hK a b
  have hdrift : ∀ a b, IntervalIntegrable
      (fun τ => M.r + (M.μ - M.r) * p τ - M.σ ^ 2 * (p τ) ^ 2 / 2) volume a b :=
    fun a b => (intervalIntegrable_const.add ((hII1 a b).const_mul _)).sub
      (((hII a b).const_mul (M.σ ^ 2)).div_const 2)
  have hHrep : ∀ (R : ℝ → Ω → ℝ) u ω, u ≠ e →
      logReturnIntegrand M (fun τ _ => p τ) t0 R u ω = stepG d sj u := by
    intro R u ω hu
    rw [← hrep u hu]
    unfold logReturnIntegrand
    simp [hII t0 M.T]
  have hIto := ito_step_exists P (shiftBM B t0) hWB hWm d sj
    (logReturnIntegrand M (fun τ _ => p τ) t0 (Rstar M B p t0 y d sj)) e (hHrep _)
  constructor
  · refine ⟨?_, ?_, ?_, Istar (shiftBM B t0) d sj, hIto, ?_⟩
    · intro s _
      have : Measurable[natFilt (shiftBM B t0) (s - t0).toNNReal]
          (Rstar M B p t0 y d sj s) :=
        measurable_const.add (Istar_meas _ d sj _)
      exact this.aestronglyMeasurable
    · filter_upwards [hB.cont] with ω hω
      apply Continuous.continuousOn
      have hprim := intervalIntegral.continuous_primitive hdrift t0
      unfold Rstar Istar shiftBM
      refine (continuous_const.add hprim).add (continuous_finset_sum _ fun i _ => ?_)
      refine continuous_const.mul (Continuous.sub ?_ ?_)
      · exact ((hω.comp (continuous_const.add (continuous_real_toNNReal.comp
          (continuous_id.sub continuous_const)))).sub continuous_const)
      · exact ((hω.comp (continuous_const.add ((continuous_real_toNNReal.comp
          (continuous_id.sub continuous_const)).min continuous_const))).sub continuous_const)
    · exact Eventually.of_forall fun ω => ⟨hII1 _ _, hII _ _⟩
    · intro s _
      exact Eventually.of_forall fun ω => rfl
  · intro R hR s hs
    obtain ⟨-, -, -, I, hI, heq⟩ := hR
    have hI' : HasBrownianItoIntegral P (natFilt (shiftBM B t0)) (shiftBM B t0)
        (logReturnIntegrand M (fun τ _ => p τ) t0 (Rstar M B p t0 y d sj)) I := hI
    have hu := ito_unique P (shiftBM B t0) hWB.toIsPreBrownianReal hWm _ I
      (Istar (shiftBM B t0) d sj) (integrand_meas M p hp t0 _) hI' hIto ((s - t0).toNNReal)
    filter_upwards [heq s hs, hu] with ω h1 h2
    rw [h1, h2]
    rfl

end LMVAux


open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology Interval

namespace LMVAux
open LogMeanVar.Complete EthierKurtz

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma Rstar_memLp (M : Market) (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (p : ℝ → ℝ) (t0 y : ℝ) {m : ℕ}
    (d : Fin m → ℝ) (sj : Fin m → ℝ≥0) (s : ℝ) :
    MemLp (Rstar M B p t0 y d sj s) 2 P := by
  have hWB := shift_brownian hB t0
  have h2 : MemLp (fun ω => ∑ i, d i * (shiftBM B t0 (s - t0).toNNReal ω -
      shiftBM B t0 (min (s - t0).toNNReal (sj i)) ω)) 2 P :=
    memLp_finsetSum _ fun i _ =>
      (incr_moments hWB.toIsPreBrownianReal (min_le_left _ (sj i))).2.2.const_mul (d i)
  have h3 := (memLp_const (μ := P) (p := 2)
    (y + ∫ τ in t0..s, (M.r + (M.μ - M.r) * p τ - M.σ ^ 2 * (p τ) ^ 2 / 2))).add h2
  exact h3

theorem det_admissible_at (M : Market) (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (hBm : ∀ s, Measurable (B s))
    (p : ℝ → ℝ) (hp : Measurable p) (K : ℝ) (hK : ∀ τ, |p τ| ≤ K) (t0 y : ℝ)
    (ht0 : t0 ∈ Ico 0 M.T) {m : ℕ}
    (d : Fin m → ℝ) (sj : Fin m → ℝ≥0) (e : ℝ≥0)
    (hrep : ∀ u : ℝ≥0, u ≠ e →
      (if t0 + (u : ℝ) ≤ M.T then M.σ * p (t0 + u) else 0) = stepG d sj u) :
    (∃ R, IsLogReturn M P B (fun τ _ => p τ) t0 y R) ∧
    (∀ R R', IsLogReturn M P B (fun τ _ => p τ) t0 y R →
      IsLogReturn M P B (fun τ _ => p τ) t0 y R' →
      ∀ᵐ ω ∂P, ∀ s ∈ Icc t0 M.T, R s ω = R' s ω) ∧
    (∀ R, IsLogReturn M P B (fun τ _ => p τ) t0 y R →
      (∫⁻ ω, (∫⁻ s in Icc t0 M.T, ‖M.σ * (fun τ (_ : ℝ) => p τ) s (R s ω)‖ₑ ^ 2) ∂P) < ∞) ∧
    (∀ R, IsLogReturn M P B (fun τ _ => p τ) t0 y R → MemLp (R M.T) 2 P) := by
  have hsol := det_solution M P B hB hBm p hp K hK t0 y d sj e hrep
  refine ⟨⟨_, hsol.1⟩, ?_, ?_, ?_⟩
  · intro R R' hR hR'
    have hRR' : ∀ s ∈ Icc t0 M.T, R s =ᵐ[P] R' s := fun s hs =>
      (hsol.2 R hR s hs).trans (hsol.2 R' hR' s hs).symm
    have hq : ∀ᵐ ω ∂P, ∀ q : ℚ, (q : ℝ) ∈ Icc t0 M.T → R q ω = R' q ω := by
      rw [ae_all_iff]
      intro q
      by_cases hq : (q : ℝ) ∈ Icc t0 M.T
      · filter_upwards [hRR' q hq] with ω h _ using h
      · exact Eventually.of_forall fun ω h => absurd h hq
    filter_upwards [hq, hR.2.1, hR'.2.1] with ω hq hc hc'
    intro s hs
    refine Set.EqOn.of_subset_closure (s := Ioo t0 M.T ∩ range ((↑) : ℚ → ℝ))
      (t := Icc t0 M.T) (f := fun s => R s ω) (g := fun s => R' s ω) ?_ hc hc' ?_ ?_ hs
    · rintro x ⟨hx, q, rfl⟩
      exact hq q (Ioo_subset_Icc_self hx)
    · exact inter_subset_left.trans Ioo_subset_Icc_self
    · rw [← closure_Ioo ht0.2.ne]
      exact closure_minimal (Dense.open_subset_closure_inter Rat.denseRange_cast isOpen_Ioo)
        isClosed_closure
  · intro R _
    set C : ℝ≥0∞ := ENNReal.ofReal ((|M.σ| * K) ^ 2) with hC
    have hpt : ∀ s, ‖M.σ * p s‖ₑ ^ 2 ≤ C := by
      intro s
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      rw [abs_mul]
      exact pow_le_pow_left₀ (by positivity)
        (mul_le_mul_of_nonneg_left (hK s) (abs_nonneg _)) 2
    have hin : ∀ ω, (∫⁻ s in Icc t0 M.T, ‖M.σ * (fun τ (_ : ℝ) => p τ) s (R s ω)‖ₑ ^ 2) ≤
        C * volume (Icc t0 M.T) := by
      intro ω
      calc (∫⁻ s in Icc t0 M.T, ‖M.σ * (fun τ (_ : ℝ) => p τ) s (R s ω)‖ₑ ^ 2)
          ≤ ∫⁻ s in Icc t0 M.T, C := lintegral_mono fun s => hpt s
        _ = C * volume (Icc t0 M.T) := setLIntegral_const _ _
    calc (∫⁻ ω, (∫⁻ s in Icc t0 M.T, ‖M.σ * (fun τ (_ : ℝ) => p τ) s (R s ω)‖ₑ ^ 2) ∂P)
        ≤ ∫⁻ _ω, C * volume (Icc t0 M.T) ∂P := lintegral_mono hin
      _ = C * volume (Icc t0 M.T) := by simp
      _ < ∞ := by
        rw [Real.volume_Icc]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  · intro R hR
    exact (Rstar_memLp M P B hB p t0 y d sj M.T).ae_eq
      (hsol.2 R hR M.T ⟨ht0.2.le, le_rfl⟩).symm

theorem det_J (M : Market) (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (hBm : ∀ s, Measurable (B s))
    (p : ℝ → ℝ) (hp : Measurable p) (K : ℝ) (hK : ∀ τ, |p τ| ≤ K) (t0 y : ℝ)
    (ht0 : t0 ∈ Ico 0 M.T) {m : ℕ}
    (d : Fin m → ℝ) (sj : Fin m → ℝ≥0) (e : ℝ≥0)
    (hrep : ∀ u : ℝ≥0, u ≠ e →
      (if t0 + (u : ℝ) ≤ M.T then M.σ * p (t0 + u) else 0) = stepG d sj u) :
    J M P B (fun τ _ => p τ) t0 y =
      (y + ∫ τ in t0..M.T, (M.r + (M.μ - M.r) * p τ - M.σ ^ 2 * (p τ) ^ 2 / 2)) -
        M.γ / 2 * variance (Istar (shiftBM B t0) d sj (M.T - t0).toNNReal) P := by
  have hsol := det_solution M P B hB hBm p hp K hK t0 y d sj e hrep
  have hWB := shift_brownian hB t0
  unfold J
  simp only
  have hR := Classical.epsilon_spec (p := fun R => IsLogReturn M P B (fun τ _ => p τ) t0 y R)
    ⟨_, hsol.1⟩
  have h := hsol.2 _ hR M.T ⟨ht0.2.le, le_rfl⟩
  rw [integral_congr_ae h, variance_congr h]
  have hIm : ∀ i, MemLp (fun ω => d i * (shiftBM B t0 (M.T - t0).toNNReal ω -
      shiftBM B t0 (min (M.T - t0).toNNReal (sj i)) ω)) 2 P := fun i =>
    (incr_moments hWB.toIsPreBrownianReal (min_le_left _ (sj i))).2.2.const_mul (d i)
  have hImeas : AEStronglyMeasurable (Istar (shiftBM B t0) d sj (M.T - t0).toNNReal) P := by
    unfold Istar
    exact (memLp_finsetSum _ fun i _ => hIm i).aestronglyMeasurable
  unfold Rstar
  rw [variance_const_add hImeas]
  congr 1
  rw [integral_add (integrable_const _)]
  · simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
    unfold Istar
    rw [integral_finsetSum _ fun i _ => (hIm i).integrable one_le_two]
    simp only [integral_const_mul]
    rw [Finset.sum_eq_zero fun i _ => by
      rw [(incr_moments hWB.toIsPreBrownianReal (min_le_left _ (sj i))).1, mul_zero], add_zero]
  · unfold Istar
    exact integrable_finsetSum _ fun i _ => (hIm i).integrable one_le_two

end LMVAux


open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology Interval

namespace LMVAux
open LogMeanVar.Complete EthierKurtz

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- the deterministic profile of the spike strategy -/
noncomputable def spikeP (c t h v : ℝ) : ℝ → ℝ := fun τ => spike (fun _ _ => c) t h v τ 0

lemma spikeP_eq (c t h v τ : ℝ) :
    spikeP c t h v τ = if t ≤ τ ∧ τ < t + h then v else c := by
  unfold spikeP spike
  by_cases hτ : τ ∈ Ico t (t + h)
  · rw [if_pos hτ, if_pos (Set.mem_Ico.mp hτ)]
  · rw [if_neg hτ, if_neg (by simpa [Set.mem_Ico] using hτ)]

lemma spikeP_meas (c t h v : ℝ) : Measurable (spikeP c t h v) := by
  have : spikeP c t h v = fun τ => if τ ∈ Ico t (t + h) then v else c := by
    funext τ; rw [spikeP_eq]; simp [Set.mem_Ico]
  rw [this]
  exact Measurable.ite measurableSet_Ico measurable_const measurable_const

lemma spikeP_bdd (c t h v τ : ℝ) : |spikeP c t h v τ| ≤ max |v| |c| := by
  rw [spikeP_eq]; split_ifs
  · exact le_max_left _ _
  · exact le_max_right _ _

lemma spike_strategy (c t h v : ℝ) :
    spike (fun _ _ => c) t h v = fun τ (_ : ℝ) => spikeP c t h v τ := rfl

lemma spike_rep (M : Market) (c v t h t0 : ℝ) (hh : 0 < h) (ht0 : t0 < M.T) :
    ∀ u : ℝ≥0, u ≠ (M.T - t0).toNNReal →
      (if t0 + (u : ℝ) ≤ M.T then M.σ * spikeP c t h v (t0 + u) else 0) =
      stepG ![M.σ * c, M.σ * (v - c), -(M.σ * (v - c)), -(M.σ * c)]
        ![0, min (t - t0).toNNReal (M.T - t0).toNNReal,
          min (t + h - t0).toNNReal (M.T - t0).toNNReal, (M.T - t0).toNNReal] u := by
  intro u hu
  have hL : ((M.T - t0).toNNReal : ℝ) = M.T - t0 := Real.coe_toNNReal _ (by linarith)
  have hu0 : (0 : ℝ) ≤ u := u.2
  unfold stepG
  simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  rw [spikeP_eq, ite_and]
  rcases lt_or_gt_of_ne hu with h1 | h1
  · have hU : (u : ℝ) < M.T - t0 := by rw [← hL]; exact_mod_cast h1
    have c1 : ∀ a : ℝ, (min a.toNNReal (M.T - t0).toNNReal ≤ u ↔ a ≤ u) := by
      intro a
      rw [min_le_iff, Real.toNNReal_le_iff_le_coe]
      constructor
      · rintro (h | h)
        · exact h
        · exact absurd h (not_le.mpr h1)
      · exact Or.inl
    have c2 : ¬ ((M.T - t0).toNNReal ≤ u) := not_le.mpr h1
    simp only [c1, c2, zero_le, if_true, if_false]
    rw [if_pos (by linarith)]
    split_ifs <;> first | ring1 | (exfalso; linarith)
  · have hU : M.T - t0 < (u : ℝ) := by rw [← hL]; exact_mod_cast h1
    have c3 : ∀ a : ℝ≥0, min a (M.T - t0).toNNReal ≤ u := fun a => (min_le_right _ _).trans h1.le
    simp only [c3, h1.le, zero_le, if_true]
    rw [if_neg (by linarith)]
    ring

end LMVAux

namespace LMVAux
open LogMeanVar.Complete EthierKurtz

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

theorem spike_admissible (M : Market) (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (hBm : ∀ s, Measurable (B s))
    (c t h v : ℝ) (hh : 0 < h) :
    Admissible M P B (spike (fun _ _ => c) t h v) := by
  rw [spike_strategy]
  intro t0 ht0 y
  exact det_admissible_at M P B hB hBm (spikeP c t h v) (spikeP_meas c t h v) (max |v| |c|)
    (spikeP_bdd c t h v) t0 y ht0 _ _ _ (spike_rep M c v t h t0 hh ht0.2)

lemma const_eq_spike (c t h : ℝ) : (fun (_ _ : ℝ) => c) = spike (fun _ _ => c) t h c := by
  funext τ y
  unfold spike
  split_ifs <;> rfl

lemma var_two (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
    (hW : IsPreBrownianReal W P) (a b : ℝ) (h' L : ℝ≥0) (hhL : h' ≤ L) :
    variance (fun ω => a * (W h' ω - W 0 ω) + b * (W L ω - W h' ω)) P =
      a ^ 2 * h' + b ^ 2 * ((L : ℝ) - h') := by
  obtain ⟨mX0, mX2, mXL⟩ := incr_moments hW (zero_le : (0 : ℝ≥0) ≤ h')
  obtain ⟨mY0, mY2, mYL⟩ := incr_moments hW hhL
  have ind : IndepFun (fun ω => W h' ω - W 0 ω) (fun ω => W L ω - W h' ω) P :=
    indepFun_of_le (indep_incr hW le_rfl hhL)
      ((meas_natFilt W le_rfl).sub (meas_natFilt W (zero_le : (0 : ℝ≥0) ≤ h')))
  have hXY : ∫ ω, (W h' ω - W 0 ω) * (W L ω - W h' ω) ∂P = 0 := by
    rw [ind.integral_fun_mul_eq_mul_integral mXL.aestronglyMeasurable mYL.aestronglyMeasurable]
    simp only [mX0, zero_mul]
  have iX := mXL.integrable one_le_two
  have iY := mYL.integrable one_le_two
  have hm : MemLp (fun ω => a * (W h' ω - W 0 ω) + b * (W L ω - W h' ω)) 2 P :=
    (mXL.const_mul a).add (mYL.const_mul b)
  have h0 : ∫ ω, (a * (W h' ω - W 0 ω) + b * (W L ω - W h' ω)) ∂P = 0 := by
    rw [integral_add (iX.const_mul a) (iY.const_mul b), integral_const_mul, integral_const_mul,
      mX0, mY0]
    ring
  rw [variance_of_integral_eq_zero hm.aestronglyMeasurable.aemeasurable h0]
  have e : (fun ω => (a * (W h' ω - W 0 ω) + b * (W L ω - W h' ω)) ^ 2) = fun ω =>
      (a ^ 2 * (W h' ω - W 0 ω) ^ 2 + (2 * a * b) * ((W h' ω - W 0 ω) * (W L ω - W h' ω)))
        + b ^ 2 * (W L ω - W h' ω) ^ 2 := by
    ext ω; ring
  have iX2 := mXL.integrable_sq
  have iY2 := mYL.integrable_sq
  have iXY : Integrable (fun ω => (W h' ω - W 0 ω) * (W L ω - W h' ω)) P :=
    mXL.integrable_mul mYL
  have j1 : Integrable (fun ω => a ^ 2 * (W h' ω - W 0 ω) ^ 2) P := iX2.const_mul _
  have j2 : Integrable (fun ω => (2 * a * b) * ((W h' ω - W 0 ω) * (W L ω - W h' ω))) P :=
    iXY.const_mul _
  have j3 : Integrable (fun ω => b ^ 2 * (W L ω - W h' ω) ^ 2) P := iY2.const_mul _
  have j12 : Integrable (fun ω => a ^ 2 * (W h' ω - W 0 ω) ^ 2 +
      (2 * a * b) * ((W h' ω - W 0 ω) * (W L ω - W h' ω))) P := j1.add j2
  rw [e, integral_add j12 j3, integral_add j1 j2, integral_const_mul, integral_const_mul,
    integral_const_mul, mX2, mY2, hXY]
  push_cast
  ring

/-- the drift integrand -/
noncomputable def Dr (M : Market) (q : ℝ) : ℝ := M.r + (M.μ - M.r) * q - M.σ ^ 2 * q ^ 2 / 2

lemma spike_drift_integral (M : Market) (c t h v : ℝ) (hh : 0 < h) (ht : t < M.T) :
    ∫ τ in t..M.T, (M.r + (M.μ - M.r) * spikeP c t h v τ - M.σ ^ 2 * (spikeP c t h v τ) ^ 2 / 2)
      = min h (M.T - t) * Dr M v + (M.T - t - min h (M.T - t)) * Dr M c := by
  set h' := min h (M.T - t) with hh'
  have hh'0 : 0 ≤ h' := le_min hh.le (by linarith)
  have hh'T : t + h' ≤ M.T := by have := min_le_right h (M.T - t); linarith
  have hdr : ∀ a b, IntervalIntegrable (fun τ => M.r + (M.μ - M.r) * spikeP c t h v τ -
      M.σ ^ 2 * (spikeP c t h v τ) ^ 2 / 2) volume a b := by
    intro a b
    have hp := spikeP_meas c t h v
    refine ii_bdd (by fun_prop) (C := |M.r| + |M.μ - M.r| * max |v| |c| +
      M.σ ^ 2 * (max |v| |c|) ^ 2 / 2) (fun τ => ?_) a b
    have hb := spikeP_bdd c t h v τ
    have h1 : |M.σ ^ 2 * spikeP c t h v τ ^ 2 / 2| ≤ M.σ ^ 2 * (max |v| |c|) ^ 2 / 2 := by
      rw [abs_div, abs_mul, abs_pow, abs_pow, abs_two, sq_abs]
      gcongr
    have h2 : |(M.μ - M.r) * spikeP c t h v τ| ≤ |M.μ - M.r| * max |v| |c| := by
      rw [abs_mul]; gcongr
    calc _ ≤ |M.r + (M.μ - M.r) * spikeP c t h v τ| + |M.σ ^ 2 * spikeP c t h v τ ^ 2 / 2| :=
          abs_sub _ _
      _ ≤ |M.r| + |(M.μ - M.r) * spikeP c t h v τ| + |M.σ ^ 2 * spikeP c t h v τ ^ 2 / 2| := by
          gcongr; exact abs_add_le _ _
      _ ≤ _ := by linarith
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := t + h') (hdr _ _) (hdr _ _)]
  have e1 : ∫ τ in t..(t + h'), (M.r + (M.μ - M.r) * spikeP c t h v τ -
      M.σ ^ 2 * (spikeP c t h v τ) ^ 2 / 2) = ∫ τ in t..(t + h'), Dr M v := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [(Set.countable_singleton (t + h')).ae_notMem volume] with x hx hmem
    rw [Set.uIoc_of_le (by linarith)] at hmem
    have hx' : x ≠ t + h' := hx
    have hlt : x < t + h' := lt_of_le_of_ne hmem.2 hx'
    rw [spikeP_eq, if_pos ⟨hmem.1.le, by linarith [min_le_left h (M.T - t)]⟩]
    rfl
  have e2 : ∫ τ in (t + h')..M.T, (M.r + (M.μ - M.r) * spikeP c t h v τ -
      M.σ ^ 2 * (spikeP c t h v τ) ^ 2 / 2) = ∫ τ in (t + h')..M.T, Dr M c := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with x hmem
    rw [Set.uIoc_of_le hh'T] at hmem
    have hge : t + h ≤ x := by
      rcases le_total h (M.T - t) with hle | hle
      · have : h' = h := min_eq_left hle
        linarith [hmem.1]
      · have : h' = M.T - t := min_eq_right hle
        linarith [hmem.1, hmem.2]
    rw [spikeP_eq, if_neg (fun hc => by linarith [hc.2])]
    rfl
  rw [e1, e2, intervalIntegral.integral_const, intervalIntegral.integral_const, smul_eq_mul,
    smul_eq_mul]
  ring

end LMVAux


open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology Interval

namespace LMVAux
open LogMeanVar.Complete EthierKurtz

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

theorem spike_J (M : Market) (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (hBm : ∀ s, Measurable (B s))
    (c t h v y : ℝ) (hh : 0 < h) (ht : t ∈ Ico 0 M.T) :
    J M P B (spike (fun _ _ => c) t h v) t y =
      (y + (min h (M.T - t) * Dr M v + (M.T - t - min h (M.T - t)) * Dr M c)) -
      M.γ / 2 * ((M.σ * v) ^ 2 * min h (M.T - t) +
        (M.σ * c) ^ 2 * (M.T - t - min h (M.T - t))) := by
  rw [spike_strategy, det_J M P B hB hBm (spikeP c t h v) (spikeP_meas c t h v) (max |v| |c|)
    (spikeP_bdd c t h v) t y ht _ _ _ (spike_rep M c v t h t hh ht.2),
    spike_drift_integral M c t h v hh ht.2]
  congr 2
  set L := (M.T - t).toNNReal with hLdef
  set h' := min (t + h - t).toNNReal L with hh'def
  have hIs : Istar (shiftBM B t) ![M.σ * c, M.σ * (v - c), -(M.σ * (v - c)), -(M.σ * c)]
      ![0, min (t - t).toNNReal L, h', L] L = fun ω =>
        (M.σ * v) * (shiftBM B t h' ω - shiftBM B t 0 ω) +
        (M.σ * c) * (shiftBM B t L ω - shiftBM B t h' ω) := by
    funext ω
    unfold Istar
    have m1 : min L h' = h' := min_eq_right (min_le_right _ _)
    simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
      sub_self, Real.toNNReal_zero, min_self, m1]
    have m0 : min L 0 = 0 := min_eq_right (zero_le : (0 : ℝ≥0) ≤ L)
    have m0' : min (0 : ℝ≥0) L = 0 := min_eq_left (zero_le : (0 : ℝ≥0) ≤ L)
    rw [m0', m0]
    ring
  rw [hIs, var_two P _ (shift_brownian hB t).toIsPreBrownianReal _ _ h' L (min_le_right _ _)]
  have hL : (L : ℝ) = M.T - t := Real.coe_toNNReal _ (by linarith [ht.2])
  have hh' : (h' : ℝ) = min h (M.T - t) := by
    rw [hh'def, NNReal.coe_min, hL, Real.coe_toNNReal _ (by linarith)]
    congr 1; ring
  rw [hL, hh']

theorem spike_le (M : Market) (hM : M.Standing) (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (hBm : ∀ s, Measurable (B s))
    (t : ℝ) (ht : t ∈ Ico 0 M.T) (y v h : ℝ) (hh : 0 < h) :
    J M P B (spike (fun _ _ => piHat M) t h v) t y ≤ J M P B (fun _ _ => piHat M) t y := by
  obtain ⟨hσ, hγ, -⟩ := hM
  have e := spike_J M P B hB hBm (piHat M) t h (piHat M) y hh ht
  rw [← const_eq_spike] at e
  rw [e, spike_J M P B hB hBm (piHat M) t h v y hh ht]
  have hp : piHat M * ((1 + M.γ) * M.σ ^ 2) = M.μ - M.r := by
    unfold piHat; field_simp
  have h0 : 0 ≤ min h (M.T - t) := le_min hh.le (by linarith [ht.2])
  have key : ((y + (min h (M.T - t) * Dr M (piHat M) + (M.T - t - min h (M.T - t)) *
      Dr M (piHat M))) - M.γ / 2 * ((M.σ * piHat M) ^ 2 * min h (M.T - t) +
        (M.σ * piHat M) ^ 2 * (M.T - t - min h (M.T - t)))) -
      ((y + (min h (M.T - t) * Dr M v + (M.T - t - min h (M.T - t)) * Dr M (piHat M))) -
      M.γ / 2 * ((M.σ * v) ^ 2 * min h (M.T - t) +
        (M.σ * piHat M) ^ 2 * (M.T - t - min h (M.T - t)))) =
      min h (M.T - t) * ((1 + M.γ) * M.σ ^ 2 / 2 * (v - piHat M) ^ 2) := by
    unfold Dr
    rw [← hp]
    ring
  have : 0 ≤ min h (M.T - t) * ((1 + M.γ) * M.σ ^ 2 / 2 * (v - piHat M) ^ 2) := by
    apply mul_nonneg h0
    have : 0 < 1 + M.γ := by linarith
    positivity
  linarith

lemma Rstar_integral (M : Market) (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (p : ℝ → ℝ) (t0 y : ℝ) {m : ℕ}
    (d : Fin m → ℝ) (sj : Fin m → ℝ≥0) (s : ℝ) :
    ∫ ω, Rstar M B p t0 y d sj s ω ∂P =
      y + ∫ τ in t0..s, (M.r + (M.μ - M.r) * p τ - M.σ ^ 2 * (p τ) ^ 2 / 2) := by
  have hWB := shift_brownian hB t0
  have hIm : ∀ i, MemLp (fun ω => d i * (shiftBM B t0 (s - t0).toNNReal ω -
      shiftBM B t0 (min (s - t0).toNNReal (sj i)) ω)) 2 P := fun i =>
    (incr_moments hWB.toIsPreBrownianReal (min_le_left _ (sj i))).2.2.const_mul (d i)
  unfold Rstar
  rw [integral_add (integrable_const _)]
  · simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
    unfold Istar
    rw [integral_finsetSum _ fun i _ => (hIm i).integrable one_le_two]
    simp only [integral_const_mul]
    rw [Finset.sum_eq_zero fun i _ => by
      rw [(incr_moments hWB.toIsPreBrownianReal (min_le_left _ (sj i))).1, mul_zero], add_zero]
  · unfold Istar
    exact integrable_finsetSum _ fun i _ => (hIm i).integrable one_le_two

theorem main_theorem (M : Market) (hM : M.Standing) (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (hBm : ∀ s, Measurable (B s)) :
    (Admissible M P B (fun _ _ => piHat M) ∧
      (∀ t ∈ Ico 0 M.T, ∀ h > (0 : ℝ), ∀ v : ℝ,
        Admissible M P B (spike (fun _ _ => piHat M) t h v)) ∧
      IsEquilibrium M P B (fun _ _ => piHat M)) ∧
    (∀ t ∈ Ico 0 M.T, ∀ y : ℝ, ∀ R : ℝ → Ω → ℝ,
      IsLogReturn M P B (fun _ _ => piHat M) t y R →
        Integrable (R M.T) P ∧ (∫ ω, (R M.T ω - y) ∂P) / (M.T - t) = aHat M) ∧
    (M.μ ≠ M.r → M.r < aHat M ∧ aHat M < M.r + theta M ^ 2 / 2) := by
  have hadm : Admissible M P B (fun _ _ => piHat M) := by
    rw [const_eq_spike (piHat M) 0 1]
    exact spike_admissible M P B hB hBm _ 0 1 _ one_pos
  refine ⟨⟨hadm, fun t _ h hh v => spike_admissible M P B hB hBm _ t h v hh, hadm, ?_⟩, ?_, ?_⟩
  · intro t ht y v _ ε hε
    filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
    have h1 := spike_le M hM P B hB hBm t ht y v h hh
    have h2 : 0 ≤ (J M P B (fun _ _ => piHat M) t y -
        J M P B (spike (fun _ _ => piHat M) t h v) t y) / h :=
      div_nonneg (by linarith) hh.le
    linarith
  · intro t ht y R hR
    have hR' : IsLogReturn M P B (fun τ _ => spikeP (piHat M) 0 1 (piHat M) τ) t y R := by
      rwa [← spike_strategy, ← const_eq_spike]
    have hsol := det_solution M P B hB hBm _ (spikeP_meas _ _ _ _) _ (spikeP_bdd _ _ _ _) t y
      _ _ _ (spike_rep M (piHat M) (piHat M) 0 1 t one_pos ht.2)
    have h := hsol.2 R hR' M.T ⟨ht.2.le, le_rfl⟩
    have hint : Integrable (R M.T) P :=
      ((Rstar_memLp M P B hB _ t y _ _ M.T).ae_eq h.symm).integrable one_le_two
    refine ⟨hint, ?_⟩
    have hc : ∀ τ, spikeP (piHat M) 0 1 (piHat M) τ = piHat M := fun τ => by
      rw [spikeP_eq]; split_ifs <;> rfl
    rw [integral_sub hint (integrable_const y), integral_const, integral_congr_ae h,
      Rstar_integral M P B hB _ t y _ _ M.T]
    simp only [hc, intervalIntegral.integral_const, smul_eq_mul, measureReal_def, measure_univ,
      ENNReal.toReal_one, one_mul]
    have hT : M.T - t ≠ 0 := by linarith [ht.2]
    obtain ⟨hσ, hγ, -⟩ := hM
    have h1γ : (1 + M.γ) ≠ 0 := by linarith
    have hσ0 : M.σ ≠ 0 := hσ.ne'
    unfold aHat theta piHat
    field_simp
    ring
  · intro hμr
    obtain ⟨hσ, hγ, -⟩ := hM
    have hθ : 0 < theta M ^ 2 := by
      unfold theta
      have : (M.μ - M.r) / M.σ ≠ 0 := div_ne_zero (sub_ne_zero.mpr hμr) hσ.ne'
      positivity
    set x := 1 / (1 + M.γ) with hx
    have hx0 : 0 < x := by positivity
    have hx1 : x < 1 := by rw [hx, div_lt_one (by linarith)]; linarith
    have e : aHat M = M.r + (x - 1 / 2 * x ^ 2) * theta M ^ 2 := by
      unfold aHat; rw [hx, div_pow, one_pow]
    rw [e]
    constructor
    · have : 0 < x - 1 / 2 * x ^ 2 := by nlinarith
      nlinarith
    · have : x - 1 / 2 * x ^ 2 < 1 / 2 := by nlinarith [sq_nonneg (x - 1)]
      nlinarith

end LMVAux


open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
open LogMeanVar.Complete

theorem solution (M : Market) (hM : M.Standing) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (hBm : ∀ s, Measurable (B s)) :
    (Admissible M P B (fun _ _ => piHat M) ∧
      (∀ t ∈ Ico 0 M.T, ∀ h > (0 : ℝ), ∀ v : ℝ,
        Admissible M P B (spike (fun _ _ => piHat M) t h v)) ∧
      IsEquilibrium M P B (fun _ _ => piHat M)) ∧
    (∀ t ∈ Ico 0 M.T, ∀ y : ℝ, ∀ R : ℝ → Ω → ℝ,
      IsLogReturn M P B (fun _ _ => piHat M) t y R →
        Integrable (R M.T) P ∧ (∫ ω, (R M.T ω - y) ∂P) / (M.T - t) = aHat M) ∧
    (M.μ ≠ M.r → M.r < aHat M ∧ aHat M < M.r + theta M ^ 2 / 2) :=
  LMVAux.main_theorem M hM P B hB hBm
