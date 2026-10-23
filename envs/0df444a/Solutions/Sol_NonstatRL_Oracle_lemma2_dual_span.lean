-- Prove2me | solution 1 for NonstatRL.Oracle.lemma2_dual_span
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T18:15:43.958327+00:00
-- url     : https://prove2.me/submissions/3a245bf2-592d-40ac-9eb9-9da666eb61b5

import Mathlib
import Definitions.Def_FiniteMDPLearning
import Definitions.Def_NonstatRL_Oracle_Model

open BanditAlgorithm ENNReal MeasureTheory ProbabilityTheory

namespace NonstatRL.Oracle

theorem l2s_step_integral {S A : ℕ} (M : FiniteMDP S A) (μ0 : MDPStateDistribution S)
    (π : MDPPolicy S A) (n : ℕ) (φ : MDPTrajectory S A (n + 1) → ℝ) :
    ∫ h, φ h ∂(mdpMeasure M μ0 π (n + 1)) =
      ∫ h, ∫ p, φ (Fin.snoc (α := fun _ => Fin S × Fin A) h p) ∂(mdpStepKernel M μ0 π n h)
        ∂(mdpMeasure M μ0 π n) := by
  rw [mdpMeasure, integral_map measurable_mdpTrajectorySnoc.aemeasurable
    (measurable_of_countable φ).aestronglyMeasurable]
  rw [Measure.integral_compProd Integrable.of_finite]

theorem l2s_inner_fst {S A : ℕ} (M : FiniteMDP S A) (μ0 : MDPStateDistribution S)
    (π : MDPPolicy S A) (n : ℕ) (h : MDPTrajectory S A n) (g : Fin S → ℝ) :
    ∫ p, g p.1 ∂(mdpStepKernel M μ0 π n h) = ∫ s, g s ∂(mdpStateKernel M μ0 n h) := by
  rw [← integral_map measurable_fst.aemeasurable (measurable_of_countable g).aestronglyMeasurable]
  rw [← Kernel.fst_apply, mdpStepKernel, Kernel.fst_compProd]

theorem l2s_dist_integral {S : ℕ} (P : MDPStateDistribution S) (f : Fin S → ℝ) :
    ∫ s, f s ∂P.toMeasure = ∑ s', (P.prob s' : ℝ) * f s' := by
  rw [MDPStateDistribution.toMeasure, integral_finsetSum_measure]
  · apply Finset.sum_congr rfl; intro s' _
    rw [integral_smul_measure, integral_dirac]
    simp
  · intro i _; exact Integrable.smul_measure Integrable.of_finite ENNReal.coe_ne_top

theorem l2s_state_kernel_succ {S A : ℕ} (M : FiniteMDP S A) (μ0 : MDPStateDistribution S)
    (n : ℕ) (h : MDPTrajectory S A (n + 1)) :
    mdpStateKernel M μ0 (n + 1) h =
      (M.transitionDist (h (Fin.last n)).1 (h (Fin.last n)).2).toMeasure := by
  rw [mdpStateKernel, Kernel.comap_apply, mdpTransitionKernel]; rfl

theorem l2s_last_allowed {S A : ℕ} (M : FiniteMDP S A) (μ0 : MDPStateDistribution S)
    (As : Fin S → Finset (Fin A)) (f : Fin S → Fin A) (hf : ∀ x, f x ∈ As x) (n : ℕ) :
    ∀ᵐ h ∂(mdpMeasure M μ0 (mdpMemorylessDetPolicy f) (n + 1)),
      (h (Fin.last n)).2 ∈ As (h (Fin.last n)).1 := by
  rw [ae_iff, mdpMeasure,
    Measure.map_apply measurable_mdpTrajectorySnoc (Set.toFinite _).measurableSet,
    Measure.compProd_apply (Set.toFinite _).measurableSet]
  have hz : ∀ h : MDPTrajectory S A n,
      mdpStepKernel M μ0 (mdpMemorylessDetPolicy f) n h
        (Prod.mk h ⁻¹' ((fun p : MDPTrajectory S A n × (Fin S × Fin A) =>
          Fin.snoc (α := fun _ => Fin S × Fin A) p.1 p.2) ⁻¹'
          {h' : MDPTrajectory S A (n + 1) |
            ¬ (h' (Fin.last n)).2 ∈ As (h' (Fin.last n)).1})) = 0 := by
    intro h
    have hpre : (Prod.mk h ⁻¹' ((fun p : MDPTrajectory S A n × (Fin S × Fin A) =>
          Fin.snoc (α := fun _ => Fin S × Fin A) p.1 p.2) ⁻¹'
          {h' : MDPTrajectory S A (n + 1) |
            ¬ (h' (Fin.last n)).2 ∈ As (h' (Fin.last n)).1})) =
        {p : Fin S × Fin A | p.2 ∉ As p.1} := by
      ext p; simp [Fin.snoc_last]
    rw [hpre, mdpStepKernel, Kernel.compProd_apply (Set.toFinite _).measurableSet]
    refine (lintegral_congr (fun b => ?_)).trans lintegral_zero
    simp only [mdpMemorylessDetPolicy, Kernel.deterministic_apply]
    rw [Measure.dirac_apply]
    simp [hf b]
  simp_rw [hz]
  exact lintegral_zero

theorem l2s_alive_snoc {S A : ℕ} (s' : Fin S) (n : ℕ) (h : MDPTrajectory S A (n + 1))
    (p : Fin S × Fin A) :
    (∀ i : Fin (n + 1 + 1), i ≠ 0 →
        ((Fin.snoc (α := fun _ => Fin S × Fin A) h p : MDPTrajectory S A (n + 1 + 1)) i).1 ≠ s') ↔
      ((∀ i : Fin (n + 1), i ≠ 0 → (h i).1 ≠ s') ∧ p.1 ≠ s') := by
  rw [Fin.forall_fin_succ']
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i hi => h1 i ?_, h2 (by simp)⟩
    intro hc; apply hi; exact Fin.castSucc_injective _ (by simpa using hc)
  · rintro ⟨h1, h2⟩
    refine ⟨fun i hi => h1 i ?_, fun _ => h2⟩
    intro hc; apply hi; rw [hc]; rfl

theorem l2s_potential {S A : ℕ} (M : FiniteMDP S A)
    (As : Fin S → Finset (Fin A)) (ρ : ℝ) (γ : Fin S → ℝ)
    (hfeas : DualFeasible M.r (fun s a s' => (M.P s a s' : ℝ)) As ρ γ)
    (f : Fin S → Fin A) (hf : ∀ x, f x ∈ As x) (x s' : Fin S)
    (hH : hitTime M f x s' ≠ ⊤) :
    γ s' - γ x ≤ max ρ 0 * (hitTime M f x s').toReal := by
  set μ : (n : ℕ) → Measure (MDPTrajectory S A n) :=
    fun n => mdpMeasure M (mdpStateDirac x) (mdpMemorylessDetPolicy f) n with hμ
  set u : Fin S → ℝ := fun y => γ y - γ s' with hu
  set E : (n : ℕ) → Set (MDPTrajectory S A (n + 1)) :=
    fun n => {h | ∀ i : Fin (n + 1), i ≠ 0 → (h i).1 ≠ s'} with hE
  set p : ℕ → ℝ := fun n => (μ (n + 1) (E n)).toReal with hp
  set Z : ℕ → ℝ := fun n =>
    ∫ h, (E n).indicator (fun h => u (h (Fin.last n)).1) h ∂(μ (n + 1)) with hZ
  have hPsum : ∀ s a, (∑ y : Fin S, (M.P s a y : ℝ)) = 1 := by
    intro s a; rw [← NNReal.coe_sum, M.P_sum_one s a]; simp
  have hharm : ∀ s a, a ∈ As s → (∑ y : Fin S, (M.P s a y : ℝ) * u y) ≤ u s + ρ := by
    intro s a ha
    have h1 := hfeas s a ha
    have h2 := (M.r_mem_Icc s a).1
    have : (∑ y : Fin S, (M.P s a y : ℝ) * u y) =
        (∑ y : Fin S, (M.P s a y : ℝ) * γ y) - γ s' := by
      simp only [hu, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hPsum, one_mul]
    rw [this]; simp only [hu]; simp only at h1; linarith
  -- Z step
  have hstep : ∀ n, Z (n + 1) ≤ Z n + ρ * p n := by
    intro n
    have e1 : Z (n + 1) = ∫ h, (E n).indicator
        (fun h => ∑ y : Fin S, (M.P (h (Fin.last n)).1 (h (Fin.last n)).2 y : ℝ) * u y) h
        ∂(μ (n + 1)) := by
      simp only [hZ, hμ]
      rw [l2s_step_integral]
      apply integral_congr_ae
      filter_upwards with h
      by_cases ha : h ∈ E n
      · rw [Set.indicator_of_mem ha]
        have : (fun q : Fin S × Fin A => (E (n + 1)).indicator
            (fun h => u (h (Fin.last (n + 1))).1)
            (Fin.snoc (α := fun _ => Fin S × Fin A) h q)) = fun q => u q.1 := by
          funext q
          by_cases hq : q.1 = s'
          · have : Fin.snoc (α := fun _ => Fin S × Fin A) h q ∉ E (n + 1) := by
              simp only [hE, Set.mem_setOf_eq]
              rw [l2s_alive_snoc]; tauto
            rw [Set.indicator_of_notMem this, hq]; simp [hu]
          · have : Fin.snoc (α := fun _ => Fin S × Fin A) h q ∈ E (n + 1) := by
              simp only [hE, Set.mem_setOf_eq]
              rw [l2s_alive_snoc]; exact ⟨ha, hq⟩
            rw [Set.indicator_of_mem this, Fin.snoc_last]
        rw [this, l2s_inner_fst M _ _ (n + 1) h u, l2s_state_kernel_succ, l2s_dist_integral]
        rfl
      · rw [Set.indicator_of_notMem ha]
        have : (fun q : Fin S × Fin A => (E (n + 1)).indicator
            (fun h => u (h (Fin.last (n + 1))).1)
            (Fin.snoc (α := fun _ => Fin S × Fin A) h q)) = fun _ => 0 := by
          funext q
          have : Fin.snoc (α := fun _ => Fin S × Fin A) h q ∉ E (n + 1) := by
            simp only [hE, Set.mem_setOf_eq]
            rw [l2s_alive_snoc]; tauto
          rw [Set.indicator_of_notMem this]
        rw [this, integral_zero]
    rw [e1]
    calc (∫ h, (E n).indicator
          (fun h => ∑ y : Fin S, (M.P (h (Fin.last n)).1 (h (Fin.last n)).2 y : ℝ) * u y) h
          ∂(μ (n + 1)))
        ≤ ∫ h, (E n).indicator (fun h => u (h (Fin.last n)).1 + ρ) h ∂(μ (n + 1)) := by
          apply integral_mono_ae Integrable.of_finite Integrable.of_finite
          filter_upwards [l2s_last_allowed M (mdpStateDirac x) As f hf n] with h hh
          apply Set.indicator_le_indicator
          exact hharm _ _ hh
      _ = Z n + ρ * p n := by
          have : (E n).indicator (fun h : MDPTrajectory S A (n + 1) => u (h (Fin.last n)).1 + ρ) =
              fun h => (E n).indicator (fun h => u (h (Fin.last n)).1) h +
                (E n).indicator (fun _ => ρ) h := by
            funext h; by_cases hh : h ∈ E n <;> simp [Set.indicator, hh]
          rw [this, integral_add Integrable.of_finite Integrable.of_finite,
            integral_indicator_const _ (Set.toFinite _).measurableSet]
          simp only [hZ, hp, smul_eq_mul, measureReal_def]
          ring
  -- Z 0
  have hZ0 : Z 0 = u x := by
    have hE0 : E 0 = Set.univ := by
      ext h; simp only [hE, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      intro i hi; exact absurd (Fin.ext (by omega)) hi
    simp only [hZ, hE0, Set.indicator_univ, hμ]
    rw [l2s_step_integral]
    have : ∀ h0 : MDPTrajectory S A 0,
        (∫ q, u ((Fin.snoc (α := fun _ => Fin S × Fin A) h0 q : MDPTrajectory S A 1)
          (Fin.last 0)).1 ∂(mdpStepKernel M (mdpStateDirac x) (mdpMemorylessDetPolicy f) 0 h0))
          = u x := by
      intro h0
      simp only [Fin.snoc_last]
      rw [l2s_inner_fst, mdpStateKernel, Kernel.const_apply, l2s_dist_integral]
      rw [Finset.sum_eq_single x]
      · simp [mdpStateDirac]
      · intro b _ hb; simp [mdpStateDirac, hb]
      · intro hx; exact absurd (Finset.mem_univ x) hx
    simp_rw [this]
    simp
  -- lower bound
  set C : ℝ := ∑ y : Fin S, |u y| with hC
  have hZlow : ∀ n, -C * p n ≤ Z n := by
    intro n
    have : -C * p n = ∫ h, (E n).indicator (fun _ => -C) h ∂(μ (n + 1)) := by
      rw [integral_indicator_const _ (Set.toFinite _).measurableSet]
      simp only [hp, smul_eq_mul, measureReal_def]; ring
    rw [this]
    apply integral_mono Integrable.of_finite Integrable.of_finite
    intro h
    apply Set.indicator_le_indicator
    have h1 : |u (h (Fin.last n)).1| ≤ C :=
      Finset.single_le_sum (f := fun y => |u y|) (fun y _ => abs_nonneg _) (Finset.mem_univ _)
    have h2 := neg_abs_le (u (h (Fin.last n)).1)
    linarith
  -- induction
  have hind : ∀ n, Z n ≤ u x + ρ * ∑ k ∈ Finset.range n, p k := by
    intro n
    induction n with
    | zero => simp [hZ0]
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have := hstep n
      nlinarith
  -- hitting time
  have hHdef : hitTime M f x s' = ∑' k, μ (k + 1) (E k) := rfl
  have hp0 : ∀ k, 0 ≤ p k := fun k => ENNReal.toReal_nonneg
  have hfin : ∀ k, μ (k + 1) (E k) ≠ ⊤ := fun k => measure_ne_top _ _
  have hsumle : ∀ n, ∑ k ∈ Finset.range n, p k ≤ (hitTime M f x s').toReal := by
    intro n
    simp only [hp]
    rw [← ENNReal.toReal_sum (fun k _ => hfin k), hHdef]
    exact ENNReal.toReal_mono (by rw [← hHdef]; exact hH) (ENNReal.sum_le_tsum _)
  have hbound : ∀ n, γ s' - γ x ≤ max ρ 0 * (hitTime M f x s').toReal + C * p n := by
    intro n
    have h1 := hind n
    have h2 := hZlow n
    have h3 : ρ * ∑ k ∈ Finset.range n, p k ≤ max ρ 0 * (hitTime M f x s').toReal := by
      calc ρ * ∑ k ∈ Finset.range n, p k ≤ max ρ 0 * ∑ k ∈ Finset.range n, p k :=
            mul_le_mul_of_nonneg_right (le_max_left _ _)
              (Finset.sum_nonneg fun k _ => hp0 k)
        _ ≤ _ := mul_le_mul_of_nonneg_left (hsumle n) (le_max_right _ _)
    have : u x = γ x - γ s' := rfl
    linarith
  have htend : Filter.Tendsto p Filter.atTop (nhds 0) := by
    have h1 := ENNReal.tendsto_atTop_zero_of_tsum_ne_top (f := fun k => μ (k + 1) (E k))
      (by rw [← hHdef]; exact hH)
    have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    exact h2
  have htend2 : Filter.Tendsto (fun n => max ρ 0 * (hitTime M f x s').toReal + C * p n)
      Filter.atTop (nhds (max ρ 0 * (hitTime M f x s').toReal + C * 0)) :=
    tendsto_const_nhds.add (htend.const_mul C)
  rw [mul_zero, add_zero] at htend2
  exact ge_of_tendsto' htend2 hbound

end NonstatRL.Oracle

namespace NonstatRL.Oracle

theorem l2s_one_le_diameter {S A : ℕ} (M : FiniteMDP S A)
    (As : Fin S → Finset (Fin A)) (hS : 0 < S) : 1 ≤ diameter M As := by
  unfold diameter
  refine le_iSup_of_le ⟨0, hS⟩ (le_iSup_of_le ⟨0, hS⟩ (le_iInf fun f => le_iInf fun _ => ?_))
  unfold hitTime
  refine le_trans ?_ (ENNReal.le_tsum 0)
  have hset : {h : MDPTrajectory S A (0 + 1) | ∀ i : Fin (0 + 1), i ≠ 0 → (h i).1 ≠ ⟨0, hS⟩}
      = Set.univ := by
    ext h; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    intro i hi; exact absurd (Fin.ext (by omega)) hi
  rw [hset, measure_univ]

end NonstatRL.Oracle

open NonstatRL.Oracle

theorem solution {S A : ℕ} (M : FiniteMDP S A)
    (As : Fin S → Finset (Fin A)) (D : ℝ)
    (hD : diameter M As ≤ ENNReal.ofReal D) (ρ : ℝ) (γ : Fin S → ℝ)
    (hfeas : DualFeasible M.r (fun s a s' => (M.P s a s' : ℝ)) As ρ γ)
    (hρ : ρ ≤ 1) :
    ∀ s s' : Fin S, γ s - γ s' ≤ 2 * D := by
  intro s s'
  have hS : 0 < S := Fin.pos s
  have hD1 : 1 ≤ D := (ENNReal.one_le_ofReal).mp (le_trans (l2s_one_le_diameter M As hS) hD)
  have hinf : (⨅ f : Fin S → Fin A, ⨅ (_ : ∀ x, f x ∈ As x), hitTime M f s' s) ≤
      ENNReal.ofReal D :=
    le_trans (le_iSup_of_le s' (le_iSup (fun t => ⨅ f : Fin S → Fin A, ⨅ (_ : ∀ x, f x ∈ As x), hitTime M f s' t) s)) hD
  have key : ∀ ε : ℝ, 0 < ε → γ s - γ s' ≤ D + ε := by
    intro ε hε
    have hlt : (⨅ f : Fin S → Fin A, ⨅ (_ : ∀ x, f x ∈ As x), hitTime M f s' s) <
        ENNReal.ofReal (D + ε) := by
      refine lt_of_le_of_lt hinf ?_
      rw [ENNReal.ofReal_lt_ofReal_iff (by linarith)]; linarith
    obtain ⟨f, hf⟩ := iInf_lt_iff.mp hlt
    have hall : ∀ x, f x ∈ As x := by
      by_contra hc
      rw [iInf_neg hc] at hf
      exact absurd hf (not_lt.mpr le_top)
    rw [iInf_pos hall] at hf
    have hne : hitTime M f s' s ≠ ⊤ := ne_top_of_lt hf
    have hle : (hitTime M f s' s).toReal ≤ D + ε :=
      ENNReal.toReal_le_of_le_ofReal (by linarith) hf.le
    have hpot := l2s_potential M As ρ γ hfeas f hall s' s hne
    have hm : max ρ 0 ≤ 1 := max_le hρ zero_le_one
    have hH0 : 0 ≤ (hitTime M f s' s).toReal := ENNReal.toReal_nonneg
    have : max ρ 0 * (hitTime M f s' s).toReal ≤ 1 * (D + ε) :=
      mul_le_mul hm hle hH0 zero_le_one
    linarith
  have : γ s - γ s' ≤ D := le_of_forall_pos_le_add (fun ε hε => key ε hε)
  linarith
