-- Prove2me | solution 1 for GhadimiLanAudit.TwoPhase.two_phase_oracle_complexity
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-08T02:36:09.512031+00:00
-- url     : https://prove2.me/submissions/1f7df455-c218-4293-ac0a-46ec88c917ec

import Mathlib
import Definitions.Def_GhadimiLanAudit_TwoPhase_Sampling

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace RealInnerProductSpace

namespace GLA7f

open GhadimiLanAudit.TwoPhase

theorem collectExec_trace_length {n : ℕ} {Ξ α : Type*} (l : List (Execution n Ξ α)) :
    (collectExec l).trace.length = (l.map (fun a => a.trace.length)).sum := by
  induction l with
  | nil => simp [collectExec, pureExec]
  | cons a as ih => simp [collectExec, bindExec, pureExec, ih]

theorem collectExec_value_length {n : ℕ} {Ξ α : Type*} (l : List (Execution n Ξ α)) :
    (collectExec l).value.length = l.length := by
  induction l with
  | nil => simp [collectExec, pureExec]
  | cons a as ih => simp [collectExec, bindExec, pureExec, ih]

theorem rsgPrefix_trace_length {n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] (P : Problem n Ξ)
    (γ : ℝ) (ξ : ℕ → Ξ) (m : ℕ) : (rsgPrefix P γ ξ m).trace.length = m := by
  induction m with
  | zero => simp [rsgPrefix, pureExec]
  | succ m ih => simp [rsgPrefix, bindExec, queryExec, pureExec, ih]

theorem validationSum_trace_length {n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] (P : Problem n Ξ)
    (x : GhadimiLan.RSG.E n) (η : ℕ → Ξ) (m : ℕ) :
    (validationSum P x η m).trace.length = m := by
  induction m with
  | zero => simp [validationSum, pureExec]
  | succ m ih => simp [validationSum, bindExec, queryExec, pureExec, ih]

theorem sum_map_le_mul {β : Type*} (l : List β) (f : β → ℕ) (c : ℕ)
    (h : ∀ b ∈ l, f b ≤ c) : (l.map f).sum ≤ l.length * c := by
  have := List.sum_le_card_nsmul (l.map f) c (by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hx
    exact h b hb)
  simpa using this

theorem calls_twoPhase_le {n S N T : ℕ} {Ξ Ω : Type*} [MeasurableSpace Ξ]
    (P : Problem n Ξ) (A : Input P S N Ω) (ω : Ω) :
    calls (twoPhaseExec (T := T) P A ω) ≤ S * (N + T) := by
  classical
  unfold twoPhaseExec calls
  by_cases hN : N = 0
  · simp [hN, pureExec]
  · simp only [hN, dite_false, bindExec, pureExec, List.append_nil, List.length_append,
      collectExec_trace_length, List.map_map]
    refine le_trans (add_le_add (sum_map_le_mul _ _ N ?_) (sum_map_le_mul _ _ T ?_)) ?_
    · intro b _
      simp [candidateExec, rsgPrefix_trace_length]
    · intro b _
      by_cases hσ : P.σ = 0
      · simp [hσ]
      · simp [hσ, validationExec, bindExec, pureExec, validationSum_trace_length]
    · simp [collectExec_value_length, Nat.mul_add]

/-- Orthogonality: if `u` is `m`-measurable and `E[v | m] = 0`, then `E⟪u, v⟫ = 0`. -/
theorem integral_inner_eq_zero_of_condExp_zero {Ω : Type*} {m m0 : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] {n : ℕ} (hm : m ≤ m0)
    {u v : Ω → GhadimiLan.RSG.E n} (hu : StronglyMeasurable[m] u)
    (huv : Integrable (fun ω => ⟪u ω, v ω⟫_ℝ) μ) (hv : Integrable v μ)
    (hc : μ[v | m] =ᵐ[μ] 0) : ∫ ω, ⟪u ω, v ω⟫_ℝ ∂μ = 0 := by
  have huv' : Integrable (fun ω => innerSL ℝ (u ω) (v ω)) μ := by simpa using huv
  have h1 := condExp_bilin_of_stronglyMeasurable_left (m := m) (innerSL ℝ) hu huv' hv
  have h2 : ∫ ω, ⟪u ω, v ω⟫_ℝ ∂μ = ∫ ω, (μ[fun ω => innerSL ℝ (u ω) (v ω) | m]) ω ∂μ := by
    rw [integral_condExp hm]; simp
  rw [h2, integral_congr_ae h1]
  have h3 : (fun ω => innerSL ℝ (u ω) ((μ[v | m]) ω)) =ᵐ[μ] fun _ => (0 : ℝ) := by
    filter_upwards [hc] with ω hω
    simp [hω]
  rw [integral_congr_ae h3]
  simp

theorem integrable_inner_of_sq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n : ℕ}
    {f g : Ω → GhadimiLan.RSG.E n} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (hf2 : Integrable (fun ω => ‖f ω‖ ^ 2) μ)
    (hg2 : Integrable (fun ω => ‖g ω‖ ^ 2) μ) :
    Integrable (fun ω => ⟪f ω, g ω⟫_ℝ) μ := by
  refine Integrable.mono' ((hf2.add hg2).div_const 2) (hf.inner hg) ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs]
  have h1 := abs_real_inner_le_norm (f ω) (g ω)
  have h2 : ‖f ω‖ * ‖g ω‖ ≤ (‖f ω‖ ^ 2 + ‖g ω‖ ^ 2) / 2 := by
    nlinarith [sq_nonneg (‖f ω‖ - ‖g ω‖)]
  simp only [Pi.add_apply]
  linarith

/-- Martingale-difference second moment: `E‖Σ_{k=1}^T δ_k‖² ≤ T σ²`. -/
theorem mds_sum_sq_bound {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {n : ℕ}
    (𝒢 : Filtration ℕ m0) (δ : ℕ → Ω → GhadimiLan.RSG.E n) (K : ℕ) (σ : ℝ)
    (hmeas : ∀ k, 1 ≤ k → k ≤ K → StronglyMeasurable[𝒢 k] (δ k))
    (hint : ∀ k, 1 ≤ k → k ≤ K → Integrable (δ k) μ)
    (hc : ∀ k, 1 ≤ k → k ≤ K → μ[δ k | 𝒢 (k - 1)] =ᵐ[μ] 0)
    (hsq : ∀ k, 1 ≤ k → k ≤ K → Integrable (fun ω => ‖δ k ω‖ ^ 2) μ)
    (hvar : ∀ k, 1 ≤ k → k ≤ K → ∫ ω, ‖δ k ω‖ ^ 2 ∂μ ≤ σ ^ 2) :
    ∀ T, T ≤ K → StronglyMeasurable[𝒢 T] (fun ω => ∑ k ∈ Finset.range T, δ (k + 1) ω) ∧
      Integrable (fun ω => ‖∑ k ∈ Finset.range T, δ (k + 1) ω‖ ^ 2) μ ∧
      ∫ ω, ‖∑ k ∈ Finset.range T, δ (k + 1) ω‖ ^ 2 ∂μ ≤ T * σ ^ 2 := by
  intro T
  induction T with
  | zero =>
    intro _
    refine ⟨?_, ?_, ?_⟩
    · simp only [Finset.range_zero, Finset.sum_empty]
      exact stronglyMeasurable_const
    · simp
    · simp
  | succ T ih =>
    intro hT
    obtain ⟨hS, hS2, hSi⟩ := ih (by omega)
    have h1 : 1 ≤ T + 1 := by omega
    have hδm := hmeas (T + 1) h1 hT
    have hSm' : StronglyMeasurable[𝒢 (T + 1)]
        (fun ω => ∑ k ∈ Finset.range T, δ (k + 1) ω) := hS.mono (𝒢.mono (Nat.le_succ T))
    have hSae : AEStronglyMeasurable (fun ω => ∑ k ∈ Finset.range T, δ (k + 1) ω) μ :=
      (hS.mono (𝒢.le T)).aestronglyMeasurable
    have hδae : AEStronglyMeasurable (δ (T + 1)) μ := (hδm.mono (𝒢.le (T + 1))).aestronglyMeasurable
    have hinner : Integrable (fun ω => ⟪∑ k ∈ Finset.range T, δ (k + 1) ω, δ (T + 1) ω⟫_ℝ) μ :=
      integrable_inner_of_sq hSae hδae hS2 (hsq _ h1 hT)
    have horth : ∫ ω, ⟪∑ k ∈ Finset.range T, δ (k + 1) ω, δ (T + 1) ω⟫_ℝ ∂μ = 0 := by
      apply integral_inner_eq_zero_of_condExp_zero (𝒢.le T) hS hinner (hint _ h1 hT)
      simpa using hc (T + 1) h1 hT
    have hexp : (fun ω => ‖∑ k ∈ Finset.range (T + 1), δ (k + 1) ω‖ ^ 2) = fun ω =>
        ‖∑ k ∈ Finset.range T, δ (k + 1) ω‖ ^ 2 +
          2 * ⟪∑ k ∈ Finset.range T, δ (k + 1) ω, δ (T + 1) ω⟫_ℝ + ‖δ (T + 1) ω‖ ^ 2 := by
      funext ω; rw [Finset.sum_range_succ]; exact norm_add_sq_real _ _
    have hA : Integrable (fun ω => ‖∑ k ∈ Finset.range T, δ (k + 1) ω‖ ^ 2 +
        2 * ⟪∑ k ∈ Finset.range T, δ (k + 1) ω, δ (T + 1) ω⟫_ℝ) μ := hS2.add (hinner.const_mul 2)
    refine ⟨?_, ?_, ?_⟩
    · have : (fun ω => ∑ k ∈ Finset.range (T + 1), δ (k + 1) ω) =
          fun ω => (∑ k ∈ Finset.range T, δ (k + 1) ω) + δ (T + 1) ω := by
        funext ω; rw [Finset.sum_range_succ]
      rw [this]; exact hSm'.add hδm
    · rw [hexp]; exact hA.add (hsq _ h1 hT)
    · rw [hexp, integral_add hA (hsq _ h1 hT), integral_add hS2 (hinner.const_mul 2),
        integral_const_mul, horth]
      have := hvar _ h1 hT
      push_cast
      linarith


section Det
variable {n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]

theorem rsgPrefix_value_succ (P : Problem n Ξ) (γ : ℝ) (ξ : ℕ → Ξ) (m : ℕ) :
    (rsgPrefix P γ ξ (m + 1)).value =
      (rsgPrefix P γ ξ m).value - γ • P.G (rsgPrefix P γ ξ m).value (ξ (m + 1)) := by
  simp [rsgPrefix, bindExec, queryExec, pureExec]

theorem rsgPrefix_trace_succ (P : Problem n Ξ) (γ : ℝ) (ξ : ℕ → Ξ) (m : ℕ) :
    (rsgPrefix P γ ξ (m + 1)).trace = (rsgPrefix P γ ξ m).trace ++
      [⟨(rsgPrefix P γ ξ m).value, ξ (m + 1), P.G (rsgPrefix P γ ξ m).value (ξ (m + 1))⟩] := by
  simp [rsgPrefix, bindExec, queryExec, pureExec]

theorem rsgPrefix_trace_length' (P : Problem n Ξ)
    (γ : ℝ) (ξ : ℕ → Ξ) (m : ℕ) : (rsgPrefix P γ ξ m).trace.length = m := by
  induction m with
  | zero => simp [rsgPrefix, pureExec]
  | succ m ih => simp [rsgPrefix, bindExec, queryExec, pureExec, ih]

theorem rsgPrefix_trace_get (P : Problem n Ξ) (γ : ℝ) (ξ : ℕ → Ξ) :
    ∀ m j, j < m → (rsgPrefix P γ ξ m).trace[j]? =
      some ⟨(rsgPrefix P γ ξ j).value, ξ (j + 1), P.G (rsgPrefix P γ ξ j).value (ξ (j + 1))⟩ := by
  intro m
  induction m with
  | zero => intro j hj; omega
  | succ m ih =>
    intro j hj
    rw [rsgPrefix_trace_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
    · rw [List.getElem?_append_left (by rw [rsgPrefix_trace_length']; exact h)]
      exact ih j h
    · subst h
      rw [List.getElem?_append_right (by rw [rsgPrefix_trace_length'])]
      simp [rsgPrefix_trace_length']

theorem candidateExec_value (P : Problem n Ξ) {Ω : Type*} (N : ℕ) (ξ : ℕ → Ω → Ξ)
    (R : Ω → ℕ) (ω : Ω) (hR : R ω ∈ Finset.Icc 1 N) :
    (candidateExec P N ξ R ω).value = (trajectory P N ξ (R ω) ω,
      P.G (trajectory P N ξ (R ω) ω) (ξ (R ω) ω)) := by
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hR
  have := rsgPrefix_trace_get P (completedStep P N) (fun k => ξ k ω) N (R ω - 1) (by omega)
  have e : R ω - 1 + 1 = R ω := by omega
  rw [e] at this
  simp [candidateExec, cachedCandidate, trajectory, this]

theorem validationSum_value (P : Problem n Ξ) (x : GhadimiLan.RSG.E n) (η : ℕ → Ξ) (m : ℕ) :
    (validationSum P x η m).value = ∑ k ∈ Finset.range m, P.G x (η (k + 1)) := by
  induction m with
  | zero => simp [validationSum, pureExec]
  | succ m ih =>
    simp [validationSum, bindExec, queryExec, pureExec, ih, Finset.sum_range_succ]

theorem collectExec_value {α : Type*} (l : List (Execution n Ξ α)) :
    (collectExec l).value = l.map (fun a => a.value) := by
  induction l with
  | nil => simp [collectExec, pureExec]
  | cons a as ih => simp [collectExec, bindExec, pureExec, ih]

/-- The explicit list of (candidate, estimate) pairs scanned by the selection step. -/
noncomputable def pairFn {S N T : ℕ} {Ω : Type*} (P : Problem n Ξ) (B : ActiveInput P S Ω)
    (s : Fin S) (ω : Ω) : GhadimiLan.RSG.E n × GhadimiLan.RSG.E n :=
  if hσ : P.σ = 0 then (candidateExec P N (B.ξ s) (B.R s) ω).value
  else ((candidateExec P N (B.ξ s) (B.R s) ω).value.1,
    (T : ℝ)⁻¹ • ∑ k ∈ Finset.range T,
      P.G (candidateExec P N (B.ξ s) (B.R s) ω).value.1 (B.η hσ s (k + 1) ω))

theorem twoPhase_value_eq {S N T : ℕ} {Ω : Type*} (P : Problem n Ξ) (A : Input P S N Ω)
    (ω : Ω) (hN : N ≠ 0) :
    (twoPhaseExec (T := T) P A ω).value =
      selectCandidate P.x1 ((List.finRange S).map (fun s => pairFn (N := N) (T := T) P (A hN) s ω)) := by
  unfold twoPhaseExec
  rw [dif_neg hN]
  simp only [bindExec, pureExec, collectExec_value, List.map_map]
  congr 1
  apply List.map_congr_left
  intro s _
  by_cases hσ : P.σ = 0
  · simp [hσ, pairFn]
  · simp [hσ, pairFn, validationExec, bindExec, pureExec, validationSum_value]

end Det

section Select
variable {n : ℕ}

theorem foldl_select_spec (a : GhadimiLan.RSG.E n × GhadimiLan.RSG.E n)
    (as : List (GhadimiLan.RSG.E n × GhadimiLan.RSG.E n)) :
    as.foldl (fun best x => if ‖x.2‖ < ‖best.2‖ then x else best) a ∈ a :: as ∧
      ∀ q ∈ a :: as,
        ‖(as.foldl (fun best x => if ‖x.2‖ < ‖best.2‖ then x else best) a).2‖ ≤ ‖q.2‖ := by
  induction as generalizing a with
  | nil => simp
  | cons b bs ih =>
    simp only [List.foldl_cons]
    obtain ⟨h1, h2⟩ := ih (if ‖b.2‖ < ‖a.2‖ then b else a)
    have hFa : ‖(if ‖b.2‖ < ‖a.2‖ then b else a).2‖ ≤ ‖a.2‖ := by
      split_ifs with h
      · exact h.le
      · exact le_rfl
    have hFb : ‖(if ‖b.2‖ < ‖a.2‖ then b else a).2‖ ≤ ‖b.2‖ := by
      split_ifs with h
      · exact le_rfl
      · exact not_lt.1 h
    have hmem : (if ‖b.2‖ < ‖a.2‖ then b else a) ∈ a :: b :: bs := by
      split_ifs <;> simp
    have hr := h2 (if ‖b.2‖ < ‖a.2‖ then b else a) (List.mem_cons.2 (Or.inl rfl))
    refine ⟨?_, ?_⟩
    · rcases List.mem_cons.1 h1 with h | h
      · rw [h]; exact hmem
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)
    · intro q hq
      rcases List.mem_cons.1 hq with h | h
      · rw [h]; exact hr.trans hFa
      · rcases List.mem_cons.1 h with h' | h'
        · rw [h']; exact hr.trans hFb
        · exact h2 q (List.mem_cons_of_mem _ h')

theorem selectCandidate_spec (x1 : GhadimiLan.RSG.E n)
    (xs : List (GhadimiLan.RSG.E n × GhadimiLan.RSG.E n)) (h : xs ≠ []) :
    ∃ p ∈ xs, selectCandidate x1 xs = p.1 ∧ ∀ q ∈ xs, ‖p.2‖ ≤ ‖q.2‖ := by
  cases xs with
  | nil => exact absurd rfl h
  | cons a as =>
    obtain ⟨h1, h2⟩ := foldl_select_spec a as
    exact ⟨_, h1, rfl, h2⟩

theorem measurable_foldl_select {Ω : Type*} [MeasurableSpace Ω]
    (fs : List (Ω → GhadimiLan.RSG.E n × GhadimiLan.RSG.E n)) :
    (∀ f ∈ fs, Measurable f) → ∀ a : Ω → GhadimiLan.RSG.E n × GhadimiLan.RSG.E n,
      Measurable a → Measurable (fun ω => (fs.map (fun f => f ω)).foldl
        (fun best x => if ‖x.2‖ < ‖best.2‖ then x else best) (a ω)) := by
  induction fs with
  | nil => intro _ a ha; simpa using ha
  | cons f fs ih =>
    intro hfs a ha
    simp only [List.map_cons, List.foldl_cons]
    have hf : Measurable f := hfs f (by simp)
    apply ih (fun g hg => hfs g (List.mem_cons_of_mem _ hg))
    exact Measurable.ite (measurableSet_lt hf.snd.norm ha.snd.norm) hf ha

theorem measurable_selectCandidate {Ω : Type*} [MeasurableSpace Ω] (x1 : GhadimiLan.RSG.E n)
    (fs : List (Ω → GhadimiLan.RSG.E n × GhadimiLan.RSG.E n)) (hfs : ∀ f ∈ fs, Measurable f) :
    Measurable (fun ω => selectCandidate x1 (fs.map (fun f => f ω))) := by
  cases fs with
  | nil => simp only [List.map_nil, selectCandidate]; exact measurable_const
  | cons f fs =>
    simp only [List.map_cons, selectCandidate]
    exact (measurable_foldl_select fs (fun g hg => hfs g (List.mem_cons_of_mem _ hg)) f
      (hfs f (by simp))).fst

end Select

section Meas
variable {n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]

theorem measurable_rsgPrefix_value {Ω : Type*} [MeasurableSpace Ω] (P : Problem n Ξ) (γ : ℝ)
    (ξ : ℕ → Ω → Ξ) : ∀ m, (∀ k, 1 ≤ k → k ≤ m → Measurable (ξ k)) →
      Measurable (fun ω => (rsgPrefix P γ (fun j => ξ j ω) m).value) := by
  intro m
  induction m with
  | zero => intro _; simp only [rsgPrefix, pureExec]; exact measurable_const
  | succ m ih =>
    intro hξ
    have hv := ih (fun k h1 h2 => hξ k h1 (by omega))
    simp only [rsgPrefix_value_succ]
    have hG : Measurable (fun ω =>
        P.G ((rsgPrefix P γ (fun j => ξ j ω) m).value) (ξ (m + 1) ω)) :=
      P.oracle_measurable.comp (hv.prodMk (hξ (m + 1) (by omega) le_rfl))
    exact hv.sub (hG.const_smul γ)

theorem measurable_candidateExec_value {Ω : Type*} [MeasurableSpace Ω] (P : Problem n Ξ)
    (N : ℕ) (ξ : ℕ → Ω → Ξ) (R : Ω → ℕ)
    (hξ : ∀ k, 1 ≤ k → k ≤ N → Measurable (ξ k)) (hR : Measurable R)
    (hRr : ∀ ω, R ω ∈ Finset.Icc 1 N) :
    Measurable (fun ω => (candidateExec P N ξ R ω).value) := by
  classical
  let H : ℕ → Ω → GhadimiLan.RSG.E n × GhadimiLan.RSG.E n := fun k ω =>
    if k ∈ Finset.Icc 1 N then
      (trajectory P N ξ k ω, P.G (trajectory P N ξ k ω) (ξ k ω)) else (P.x1, 0)
  have hH : ∀ k, Measurable (H k) := by
    intro k
    by_cases hk : k ∈ Finset.Icc 1 N
    · simp only [H, hk, if_true]
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hk
      have ht : Measurable (fun ω => trajectory P N ξ k ω) :=
        measurable_rsgPrefix_value P _ ξ (k - 1) (fun j hj1 hj2 => hξ j hj1 (by omega))
      exact ht.prodMk (P.oracle_measurable.comp (ht.prodMk (hξ k h1 h2)))
    · simp only [H, hk, if_false]; exact measurable_const
  have hU : Measurable (fun p : Ω × ℕ => H p.2 p.1) :=
    measurable_from_prod_countable_left (fun k => hH k)
  have hc : Measurable (fun ω => H (R ω) ω) := hU.comp (measurable_id.prodMk hR)
  have e : (fun ω => (candidateExec P N ξ R ω).value) = fun ω => H (R ω) ω := by
    funext ω
    simp only [H, hRr ω, if_true]
    exact candidateExec_value P N ξ R ω (hRr ω)
  rw [e]; exact hc

/-- N = 0 branch: zero iterations force `D_f = 0`, so `x1` is a global minimiser. -/
theorem g_x1_eq_zero_of_iter_zero (P : Problem n Ξ) (ε : ℝ) (hε : 0 < ε)
    (h : iterationCount P ε = 0) : P.g P.x1 = 0 := by
  unfold iterationCount at h
  have h0 := Nat.ceil_eq_zero.1 h
  have h1 : 32 * P.L ^ 2 * distanceScale P ^ 2 / ε ≤ 0 := le_trans (le_max_left _ _) h0
  have hL := P.L_pos
  have hD2 : distanceScale P ^ 2 = 0 := by
    by_contra hne
    have hpos : 0 < distanceScale P ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hne)
    have : 0 < 32 * P.L ^ 2 * distanceScale P ^ 2 / ε :=
      div_pos (mul_pos (mul_pos (by norm_num) (pow_pos hL 2)) hpos) hε
    linarith
  have hsq : distanceScale P = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 hD2
  unfold distanceScale GhadimiLan.RSG.Df at hsq
  rw [Real.sqrt_eq_zero'] at hsq
  have hle : P.f P.x1 ≤ optimalValue P := by
    by_contra hc
    have hc := lt_of_not_ge hc
    have : 0 < 2 * (P.f P.x1 - optimalValue P) / P.L := by
      apply div_pos _ hL; linarith
    linarith
  have hmin : IsLocalMin P.f P.x1 := by
    apply Filter.Eventually.of_forall
    intro y
    exact hle.trans (csInf_le P.bounded_below ⟨y, rfl⟩)
  have hg := P.smooth.2.1 P.x1
  rw [hasGradientAt_iff_hasFDerivAt] at hg
  have := hmin.hasFDerivAt_eq_zero hg
  simpa using this

end Meas


theorem ag_line_deriv {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] {F : V → ℝ} {G : V → V} (hF : ∀ x, HasGradientAt F (G x) x)
    (x w : V) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F (x + s • w)) ⟪G (x + t • w), w⟫ t := by
  have hl : HasDerivAt (fun s : ℝ => x + s • w) w t := by
    simpa using ((hasDerivAt_id t).smul_const w).const_add x
  have h1 := (hasGradientAt_iff_hasFDerivAt.mp (hF (x + t • w))).comp_hasDerivAt t hl
  rw [InnerProductSpace.toDual_apply_apply] at h1
  exact h1

theorem ag_descent {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] {F : V → ℝ} {G : V → V} {L : ℝ} (hF : ∀ x, HasGradientAt F (G x) x)
    (hG : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖) (x y : V) :
    F y ≤ F x + ⟪G x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2 := by
  set w := y - x
  let g : ℝ → ℝ := fun t => F (x + t • w) - t * ⟪G x, w⟫ - L / 2 * t ^ 2 * ‖w‖ ^ 2
  have hg : ∀ t, HasDerivAt g (⟪G (x + t • w), w⟫ - ⟪G x, w⟫
      - L / 2 * (2 * t) * ‖w‖ ^ 2) t := by
    intro t
    have h1 := ag_line_deriv hF x w t
    have h2 : HasDerivAt (fun s : ℝ => s * ⟪G x, w⟫) ⟪G x, w⟫ t := by
      simpa using (hasDerivAt_id t).mul_const ⟪G x, w⟫
    have h3 : HasDerivAt (fun s : ℝ => L / 2 * s ^ 2 * ‖w‖ ^ 2) (L / 2 * (2 * t) * ‖w‖ ^ 2) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (L / 2)).mul_const (‖w‖ ^ 2)
      simpa using this
    exact (h1.sub h2).sub h3
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope g _ (zero_lt_one' ℝ)
    (fun t _ => (hg t).continuousAt.continuousWithinAt) (fun t _ => hg t)
  have hle : ⟪G (x + c • w), w⟫ - ⟪G x, w⟫ - L / 2 * (2 * c) * ‖w‖ ^ 2 ≤ 0 := by
    have e1 : ⟪G (x + c • w), w⟫ - ⟪G x, w⟫ = ⟪G (x + c • w) - G x, w⟫ := by
      rw [inner_sub_left]
    have e2 := real_inner_le_norm (G (x + c • w) - G x) w
    have e3 := hG (x + c • w) x
    have e4 : ‖x + c • w - x‖ = c * ‖w‖ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hc.1]
    rw [e4] at e3
    have : ‖G (x + c • w) - G x‖ * ‖w‖ ≤ L * (c * ‖w‖) * ‖w‖ :=
      mul_le_mul_of_nonneg_right e3 (norm_nonneg _)
    nlinarith
  rw [hcd] at hle
  have : g 1 ≤ g 0 := by
    have := hle; simp only [sub_zero, div_one] at this; linarith
  simp only [g, one_smul, zero_smul, add_zero, one_mul, zero_mul, one_pow, sub_zero,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at this
  have hw : x + w = y := by simp [w]
  rw [hw] at this
  linarith

/-- Tower property for an inner product with an `m`-measurable left factor. -/
theorem cross_eq {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ m0) {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] {Y Z W : Ω → V}
    (hY : AEStronglyMeasurable[m] Y μ)
    (hYZ : Integrable (fun ω => ⟪Y ω, Z ω⟫) μ) (hZ : Integrable Z μ)
    (hce : μ[Z|m] =ᵐ[μ] W) :
    ∫ ω, ⟪Y ω, Z ω⟫ ∂μ = ∫ ω, ⟪Y ω, W ω⟫ ∂μ := by
  have h1 : μ[fun ω => ⟪Y ω, Z ω⟫|m] =ᵐ[μ] fun ω => ⟪Y ω, μ[Z|m] ω⟫ :=
    condExp_bilin_of_aestronglyMeasurable_left (innerSL ℝ) hY hYZ hZ
  rw [← integral_condExp hm]
  refine integral_congr_ae ?_
  filter_upwards [h1, hce] with ω h1 h2
  rw [h1, h2]

/-- Averaging over an independent random index. -/
theorem avg_R {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {S : Type*} [MeasurableSpace S] (X : Ω → S) (R : Ω → ℕ) (hR : Measurable R)
    (hind : IndepFun R X μ) (N : ℕ) (hRN : ∀ ω, R ω ∈ Finset.Icc 1 N)
    (F : ℕ → S → ℝ) (hF : ∀ k, Measurable (F k))
    (hint : ∀ k ∈ Finset.Icc 1 N, Integrable (fun ω => F k (X ω)) μ) :
    Integrable (fun ω => F (R ω) (X ω)) μ ∧
    ∫ ω, F (R ω) (X ω) ∂μ =
      ∑ k ∈ Finset.Icc 1 N, μ.real {ω | R ω = k} * ∫ ω, F k (X ω) ∂μ := by
  have hdecomp : (fun ω => F (R ω) (X ω)) = fun ω => ∑ k ∈ Finset.Icc 1 N,
      (if R ω = k then (1:ℝ) else 0) * F k (X ω) := by
    funext ω
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    simp [hRN ω]
  have hmeasS : ∀ k, MeasurableSet {ω | R ω = k} := fun k => hR (measurableSet_singleton k)
  have hind_k : ∀ k, (fun ω => {ω | R ω = k}.indicator (1 : Ω → ℝ) ω) =
      fun ω => (if R ω = k then (1:ℝ) else 0) := by
    intro k; funext ω; simp [Set.indicator_apply]
  have hterm : ∀ k ∈ Finset.Icc 1 N,
      Integrable (fun ω => (if R ω = k then (1:ℝ) else 0) * F k (X ω)) μ := by
    intro k hk
    have : (fun ω => (if R ω = k then (1:ℝ) else 0) * F k (X ω)) =
        {ω | R ω = k}.indicator (fun ω => F k (X ω)) := by
      funext ω; by_cases h : R ω = k <;> simp [h]
    rw [this]; exact (hint k hk).indicator (hmeasS k)
  refine ⟨?_, ?_⟩
  · rw [hdecomp]; exact integrable_finset_sum _ hterm
  · rw [hdecomp, integral_finset_sum _ hterm]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hφ : Measurable fun r : ℕ => if r = k then (1:ℝ) else 0 := measurable_of_countable _
    have hind' : IndepFun (fun ω => if R ω = k then (1:ℝ) else 0) (fun ω => F k (X ω)) μ :=
      hind.comp hφ (hF k)
    have hm1 : AEStronglyMeasurable (fun ω => if R ω = k then (1:ℝ) else 0) μ :=
      (hφ.comp hR).aestronglyMeasurable
    have := hind'.integral_mul_eq_mul_integral hm1 (hint k hk).aestronglyMeasurable
    simp only [Pi.mul_apply] at this
    rw [this, ← hind_k k, integral_indicator_one (hmeasS k)]

/-- Inner products of two square-integrable vectors are integrable. -/
theorem int_inner {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Y Z : Ω → V}
    (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ) : Integrable (fun ω => ⟪Y ω, Z ω⟫) μ := by
  have hY2 := (memLp_two_iff_integrable_sq_norm hY.1).1 hY
  have hZ2 := (memLp_two_iff_integrable_sq_norm hZ.1).1 hZ
  refine Integrable.mono' (hY2.add hZ2) (hY.1.inner hZ.1) (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs]
  have h1 := abs_real_inner_le_norm (Y ω) (Z ω)
  have h2 := norm_nonneg (Y ω)
  have h3 := norm_nonneg (Z ω)
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (‖Y ω‖ - ‖Z ω‖)]

theorem int_sq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {V : Type*}
    [NormedAddCommGroup V] {Y : Ω → V}
    (hY : MemLp Y 2 μ) : Integrable (fun ω => ‖Y ω‖ ^ 2) μ :=
  (memLp_two_iff_integrable_sq_norm hY.1).1 hY

/-- Lipschitz images of square-integrable vectors are square-integrable. -/
theorem memLp_lip {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {g : V → V} {L : ℝ} (hL : 0 ≤ L)
    (hg : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) {X : Ω → V} (hX : MemLp X 2 μ) :
    MemLp (fun ω => g (X ω)) 2 μ := by
  have hcont : Continuous g := by
    refine (LipschitzWith.of_dist_le' (K := L) fun x y => ?_).continuous
    rw [dist_eq_norm, dist_eq_norm]; exact hg x y
  have hb1 : MemLp (fun _ : Ω => ‖g 0‖) 2 μ := memLp_const _
  have hb2 : MemLp (fun ω => L * ‖X ω‖) 2 μ := hX.norm.const_mul L
  have hb := hb1.add hb2
  refine hb.of_le (hcont.comp_aestronglyMeasurable hX.1) (ae_of_all _ fun ω => ?_)
  simp only [Pi.add_apply]
  have h1 := hg (X ω) 0
  rw [sub_zero] at h1
  have h2 : ‖g (X ω)‖ ≤ ‖g 0‖ + ‖g (X ω) - g 0‖ := by
    have := norm_add_le (g 0) (g (X ω) - g 0)
    rwa [add_sub_cancel] at this
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  linarith


section RSG
variable {n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]

theorem sum_Icc_one_eq_range (h : ℕ → ℝ) : ∀ N : ℕ,
    ∑ k ∈ Finset.Icc 1 N, h k = ∑ j ∈ Finset.range N, h (j + 1)
  | 0 => by simp
  | N + 1 => by
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, sum_Icc_one_eq_range h N]

/-- One smooth step with a perturbed gradient `G = g x + d`. -/
theorem descent_step {f : GhadimiLan.RSG.E n → ℝ} {g : GhadimiLan.RSG.E n → GhadimiLan.RSG.E n}
    {L : ℝ} (hs : ConvexOptAlg.SmoothGD.IsBetaSmooth f g L) (x d : GhadimiLan.RSG.E n) (γ : ℝ) :
    (γ - L * γ ^ 2 / 2) * ‖g x‖ ^ 2 ≤ (f x - f (x - γ • (g x + d))) +
      ((L * γ ^ 2 - γ) * ⟪g x, d⟫ + L * γ ^ 2 / 2 * ‖d‖ ^ 2) := by
  have h := ag_descent hs.2.1 hs.2.2 x (x - γ • (g x + d))
  have e1 : x - γ • (g x + d) - x = -(γ • (g x + d)) := by abel
  have e2 : ⟪g x, -(γ • (g x + d))⟫ = -γ * ‖g x‖ ^ 2 - γ * ⟪g x, d⟫ := by
    rw [inner_neg_right, real_inner_smul_right, inner_add_right, real_inner_self_eq_norm_sq]
    ring
  have e3 : ‖-(γ • (g x + d))‖ ^ 2 = γ ^ 2 * (‖g x‖ ^ 2 + 2 * ⟪g x, d⟫ + ‖d‖ ^ 2) := by
    rw [norm_neg, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, norm_add_sq_real]
  rw [e1, e2, e3] at h
  linear_combination h

/-- L3: expected squared gradient at the random output of one RSG run. -/
theorem rsg_run_bound (P : Problem n Ξ) {Ω : Type*} [m0 : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : ℕ) (hN : 1 ≤ N) (ξ : ℕ → Ω → Ξ) (R : Ω → ℕ) (hlaw : RunLaw P μ N ξ R)
    (hγ0 : 0 < completedStep P N) (hγL : completedStep P N ≤ 1 / P.L) :
    Integrable (fun ω => ‖P.g (trajectory P N ξ (R ω) ω)‖ ^ 2) μ ∧
    ∫ ω, ‖P.g (trajectory P N ξ (R ω) ω)‖ ^ 2 ∂μ ≤
      2 * (P.f P.x1 - optimalValue P) / (N * completedStep P N) +
        P.L * completedStep P N * P.σ ^ 2 := by
  classical
  obtain ⟨⟨ℱ, hA1⟩, ⟨hRm, hRr, hRp⟩, hind⟩ := hlaw
  set γ := completedStep P N with hγdef
  set x : ℕ → Ω → GhadimiLan.RSG.E n := trajectory P N ξ with hx
  have hL := P.L_pos
  have hLγ : P.L * γ ≤ 1 := by
    have := (le_div_iff₀ hL).1 hγL; linarith
  have hgL : ∀ a b, ‖P.g a - P.g b‖ ≤ P.L * ‖a - b‖ := P.smooth.2.2
  have hgc : Continuous P.g := (LipschitzWith.of_dist_le' (K := P.L) fun a b => by
    rw [dist_eq_norm, dist_eq_norm]; exact hgL a b).continuous
  have hstep : ∀ k, 1 ≤ k → ∀ ω, x (k + 1) ω = x k ω - γ • P.G (x k ω) (ξ k ω) := by
    intro k hk ω
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    show (rsgPrefix P γ (fun i => ξ i ω) (j + 1 + 1 - 1)).value =
      (rsgPrefix P γ (fun i => ξ i ω) (j + 1 - 1)).value -
        γ • P.G (rsgPrefix P γ (fun i => ξ i ω) (j + 1 - 1)).value (ξ (j + 1) ω)
    simp only [Nat.add_sub_cancel]
    exact rsgPrefix_value_succ P γ (fun i => ξ i ω) j
  have hx1 : ∀ ω, x 1 ω = P.x1 := by
    intro ω; show (rsgPrefix P γ (fun i => ξ i ω) (1 - 1)).value = P.x1
    simp [rsgPrefix, pureExec]
  have hξm : ∀ k, 1 ≤ k → k ≤ N → Measurable (ξ k) := fun k h1 h2 =>
    ((hA1 k (Finset.mem_Icc.2 ⟨h1, h2⟩)).2.1).mono (ℱ.le k) le_rfl
  have hxm : ∀ k, k ≤ N + 1 → Measurable (x k) := fun k hk =>
    measurable_rsgPrefix_value P γ ξ (k - 1) (fun j h1 h2 => hξm j h1 (by omega))
  have hGae : ∀ k, 1 ≤ k → k ≤ N →
      AEStronglyMeasurable (fun ω => P.G (x k ω) (ξ k ω)) μ := fun k h1 h2 =>
    (P.oracle_measurable.comp ((hxm k (by omega)).prodMk (hξm k h1 h2))).aestronglyMeasurable
  -- square integrability along the run
  have hmem : ∀ k, 1 ≤ k → k ≤ N + 1 → MemLp (x k) 2 μ := by
    intro k
    induction k with
    | zero => intro h; omega
    | succ k ih =>
      intro _ hk
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · subst h0
        have : x (0 + 1) = fun _ => P.x1 := funext hx1
        rw [this]; exact memLp_const _
      · have hxk := ih hpos (by omega)
        have hk' : k ∈ Finset.Icc 1 N := Finset.mem_Icc.2 ⟨hpos, by omega⟩
        obtain ⟨-, -, -, -, hsq, -⟩ := hA1 k hk'
        have hgk : MemLp (fun ω => P.g (x k ω)) 2 μ := memLp_lip hL.le hgL hxk
        have hδ : MemLp (fun ω => P.G (x k ω) (ξ k ω) - P.g (x k ω)) 2 μ :=
          (memLp_two_iff_integrable_sq_norm ((hGae k hpos (by omega)).sub hgk.1)).2 hsq
        have eG : (fun ω => P.G (x k ω) (ξ k ω)) =
            (fun ω => P.G (x k ω) (ξ k ω) - P.g (x k ω)) + (fun ω => P.g (x k ω)) := by
          funext ω; simp only [Pi.add_apply, sub_add_cancel]
        have hG : MemLp (fun ω => P.G (x k ω) (ξ k ω)) 2 μ := by rw [eG]; exact hδ.add hgk
        have e : x (k + 1) = fun ω => x k ω - γ • P.G (x k ω) (ξ k ω) := funext (hstep k hpos)
        rw [e]; exact hxk.sub (hG.const_smul γ)
  set D : ℕ → Ω → GhadimiLan.RSG.E n := fun k ω => P.G (x k ω) (ξ k ω) - P.g (x k ω) with hD
  have hgm : ∀ k, 1 ≤ k → k ≤ N → MemLp (fun ω => P.g (x k ω)) 2 μ := fun k h1 h2 =>
    memLp_lip hL.le hgL (hmem k h1 (by omega))
  have hDm : ∀ k, 1 ≤ k → k ≤ N → MemLp (D k) 2 μ := fun k h1 h2 =>
    (memLp_two_iff_integrable_sq_norm ((hGae k h1 h2).sub (hgm k h1 h2).1)).2
      (hA1 k (Finset.mem_Icc.2 ⟨h1, h2⟩)).2.2.2.2.1
  -- cross term vanishes
  have hcross : ∀ k, 1 ≤ k → k ≤ N → ∫ ω, ⟪P.g (x k ω), D k ω⟫ ∂μ = 0 := by
    intro k h1 h2
    obtain ⟨hxk, -, hGi, hce, -, -⟩ := hA1 k (Finset.mem_Icc.2 ⟨h1, h2⟩)
    have hY : AEStronglyMeasurable[ℱ (k - 1)] (fun ω => P.g (x k ω)) μ :=
      ((hgc.measurable.comp hxk).stronglyMeasurable).aestronglyMeasurable
    have hGm : MemLp (fun ω => P.G (x k ω) (ξ k ω)) 2 μ := by
      have eG : (fun ω => P.G (x k ω) (ξ k ω)) = D k + (fun ω => P.g (x k ω)) := by
        funext ω; simp only [hD, Pi.add_apply, sub_add_cancel]
      rw [eG]; exact (hDm k h1 h2).add (hgm k h1 h2)
    have hYZ := int_inner (hgm k h1 h2) hGm
    have hc := cross_eq (ℱ.le (k - 1)) hY hYZ hGi hce
    have hgg := int_inner (hgm k h1 h2) (hgm k h1 h2)
    have e : (fun ω => ⟪P.g (x k ω), D k ω⟫) =
        fun ω => ⟪P.g (x k ω), P.G (x k ω) (ξ k ω)⟫ - ⟪P.g (x k ω), P.g (x k ω)⟫ := by
      funext ω; simp only [hD, inner_sub_right]
    rw [e, integral_sub hYZ hgg, hc, sub_self]
  -- pointwise telescoped descent
  set C : ℕ → Ω → ℝ := fun k ω =>
    (P.L * γ ^ 2 - γ) * ⟪P.g (x k ω), D k ω⟫ + P.L * γ ^ 2 / 2 * ‖D k ω‖ ^ 2 with hC
  have hone : ∀ k, 1 ≤ k → ∀ ω, (γ - P.L * γ ^ 2 / 2) * ‖P.g (x k ω)‖ ^ 2 ≤
      (P.f (x k ω) - P.f (x (k + 1) ω)) + C k ω := by
    intro k hk ω
    have h := descent_step P.smooth (x k ω) (D k ω) γ
    have e : P.g (x k ω) + D k ω = P.G (x k ω) (ξ k ω) := by
      simp only [hD, add_sub_cancel]
    rw [e, ← hstep k hk ω] at h
    exact h
  have hpt : ∀ ω, (γ - P.L * γ ^ 2 / 2) * ∑ j ∈ Finset.range N, ‖P.g (x (j + 1) ω)‖ ^ 2 ≤
      (P.f P.x1 - optimalValue P) + ∑ j ∈ Finset.range N, C (j + 1) ω := by
    intro ω
    have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.range N) => hone (j + 1) (by omega) ω)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
    have tel := Finset.sum_range_sub' (fun j => P.f (x (j + 1) ω)) N
    have hfs : optimalValue P ≤ P.f (x (N + 1) ω) := csInf_le P.bounded_below ⟨_, rfl⟩
    have h1 : x (0 + 1) ω = P.x1 := hx1 ω
    rw [h1] at tel
    linarith
  -- integrate
  have hgsq : ∀ k, 1 ≤ k → k ≤ N → Integrable (fun ω => ‖P.g (x k ω)‖ ^ 2) μ := fun k h1 h2 =>
    int_sq (hgm k h1 h2)
  have hCi : ∀ k, 1 ≤ k → k ≤ N → Integrable (C k) μ := fun k h1 h2 =>
    ((int_inner (hgm k h1 h2) (hDm k h1 h2)).const_mul _).add
      ((int_sq (hDm k h1 h2)).const_mul _)
  have hCint : ∀ k, 1 ≤ k → k ≤ N → ∫ ω, C k ω ∂μ ≤ P.L * γ ^ 2 / 2 * P.σ ^ 2 := by
    intro k h1 h2
    have hv := (hA1 k (Finset.mem_Icc.2 ⟨h1, h2⟩)).2.2.2.2.2
    have hi1 := (int_inner (hgm k h1 h2) (hDm k h1 h2)).const_mul (P.L * γ ^ 2 - γ)
    have hi2 := (int_sq (hDm k h1 h2)).const_mul (P.L * γ ^ 2 / 2)
    simp only [hC]
    rw [integral_add hi1 hi2, integral_const_mul, integral_const_mul, hcross k h1 h2]
    have hc0 : 0 ≤ P.L * γ ^ 2 / 2 := by positivity
    have : ∫ ω, ‖D k ω‖ ^ 2 ∂μ ≤ P.σ ^ 2 := hv
    nlinarith
  set Ssum := ∑ j ∈ Finset.range N, ∫ ω, ‖P.g (x (j + 1) ω)‖ ^ 2 ∂μ with hSsum
  have hLHSi : Integrable (fun ω => (γ - P.L * γ ^ 2 / 2) *
      ∑ j ∈ Finset.range N, ‖P.g (x (j + 1) ω)‖ ^ 2) μ :=
    (integrable_finset_sum _ fun j hj => hgsq (j + 1) (by omega)
      (by simp at hj; omega)).const_mul _
  have hRHSi : Integrable (fun ω => (P.f P.x1 - optimalValue P) +
      ∑ j ∈ Finset.range N, C (j + 1) ω) μ :=
    (integrable_const _).add (integrable_finset_sum _ fun j hj => hCi (j + 1) (by omega)
      (by simp at hj; omega))
  have hmono := integral_mono hLHSi hRHSi hpt
  have hc1 : ∫ _ : Ω, (P.f P.x1 - optimalValue P) ∂μ = P.f P.x1 - optimalValue P := by simp
  rw [integral_const_mul, integral_finset_sum _ (fun j hj => hgsq (j + 1) (by omega)
      (by simp at hj; omega)), integral_add (integrable_const _)
      (integrable_finset_sum _ fun j hj => hCi (j + 1) (by omega) (by simp at hj; omega)),
      hc1, integral_finset_sum _ (fun j hj => hCi (j + 1) (by omega)
      (by simp at hj; omega))] at hmono
  have hCsum : ∑ j ∈ Finset.range N, ∫ ω, C (j + 1) ω ∂μ ≤ N * (P.L * γ ^ 2 / 2 * P.σ ^ 2) := by
    have := Finset.sum_le_sum (fun j (hj : j ∈ Finset.range N) =>
      hCint (j + 1) (by omega) (by simp at hj; omega))
    simpa using this
  have hS0 : 0 ≤ Ssum := Finset.sum_nonneg fun j _ => integral_nonneg fun ω => by positivity
  have key : γ * Ssum ≤ 2 * (P.f P.x1 - optimalValue P) + N * (P.L * γ ^ 2 * P.σ ^ 2) := by
    nlinarith [mul_nonneg (mul_nonneg hγ0.le hS0) (sub_nonneg.2 hLγ)]
  -- averaging over the random index
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hpmf : ∀ k ∈ Finset.Icc 1 N, μ.real {ω | R ω = k} = 1 / N := by
    intro k hk
    rw [measureReal_def, hRp k hk, GhadimiLan.RSG.rsgPMF, Finset.sum_const, Nat.card_Icc,
      nsmul_eq_mul]
    have hq : 0 < 2 * γ - P.L * γ ^ 2 := by nlinarith
    rw [ENNReal.toReal_ofReal (by positivity)]
    simp only [Nat.add_sub_cancel]
    field_simp
    exact div_self (by nlinarith : (0:ℝ) < 2 - γ * P.L).ne'
  let F : ℕ → (ℕ → Ξ) → ℝ := fun k s => ‖P.g ((rsgPrefix P γ s (k - 1)).value)‖ ^ 2
  have hF : ∀ k, Measurable (F k) := fun k =>
    ((hgc.measurable.comp (measurable_rsgPrefix_value P γ (fun j (s : ℕ → Ξ) => s j) (k - 1)
      (fun j _ _ => measurable_pi_apply j))).norm).pow_const 2
  have havg := avg_R (fun ω k => ξ k ω) R hRm hind N hRr F hF
    (fun k hk => hgsq k (Finset.mem_Icc.1 hk).1 (Finset.mem_Icc.1 hk).2)
  refine ⟨havg.1, ?_⟩
  have e : ∫ ω, ‖P.g (trajectory P N ξ (R ω) ω)‖ ^ 2 ∂μ = 1 / N * Ssum := by
    rw [show (fun ω => ‖P.g (trajectory P N ξ (R ω) ω)‖ ^ 2) =
      fun ω => F (R ω) ((fun ω k => ξ k ω) ω) from rfl, havg.2,
      Finset.sum_congr rfl (fun k hk => by rw [hpmf k hk]), ← Finset.mul_sum]
    congr 1
    exact sum_Icc_one_eq_range (fun k => ∫ ω, F k ((fun ω k => ξ k ω) ω) ∂μ) N
  rw [e]
  have hγN : 0 < (N : ℝ) * γ := by positivity
  calc 1 / (N : ℝ) * Ssum = (γ * Ssum) / (N * γ) := by field_simp
    _ ≤ (2 * (P.f P.x1 - optimalValue P) + N * (P.L * γ ^ 2 * P.σ ^ 2)) / (N * γ) :=
        div_le_div_of_nonneg_right key hγN.le
    _ = 2 * (P.f P.x1 - optimalValue P) / (N * γ) + P.L * γ * P.σ ^ 2 := by
        field_simp

end RSG


/-- Constants (2.25): per-run bound `2Δ/(Nγ) + Lγσ² ≤ ε/16` with `0 < γ ≤ 1/L`. -/
theorem rsg_const_bound {n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] (P : Problem n Ξ) (ε : ℝ)
    (hε : 0 < ε) (hN : iterationCount P ε ≠ 0) :
    0 < completedStep P (iterationCount P ε) ∧ completedStep P (iterationCount P ε) ≤ 1 / P.L ∧
    2 * (P.f P.x1 - optimalValue P) /
        ((iterationCount P ε : ℝ) * completedStep P (iterationCount P ε)) +
      P.L * completedStep P (iterationCount P ε) * P.σ ^ 2 ≤ ε / 16 := by
  have hNc : max (32 * P.L ^ 2 * distanceScale P ^ 2 / ε)
      ((32 * P.L * (P.Dt + distanceScale P ^ 2 / P.Dt) * P.σ / ε) ^ 2) ≤
        (iterationCount P ε : ℝ) := Nat.le_ceil _
  set N := iterationCount P ε with hNdef
  set D := distanceScale P with hDdef
  have hL := P.L_pos
  have hDt := P.Dt_pos
  have hfs : optimalValue P ≤ P.f P.x1 := csInf_le P.bounded_below ⟨_, rfl⟩
  have hD2 : D ^ 2 = 2 * (P.f P.x1 - optimalValue P) / P.L := by
    simp only [hDdef, distanceScale, GhadimiLan.RSG.Df]
    rw [Real.sq_sqrt (by apply div_nonneg <;> linarith)]
  have hΔ : 2 * (P.f P.x1 - optimalValue P) = P.L * D ^ 2 := by
    rw [hD2]; field_simp
  have hN1 : 32 * P.L ^ 2 * D ^ 2 ≤ N * ε := by
    have := le_trans (le_max_left _ _) hNc
    rwa [div_le_iff₀ hε] at this
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hspos : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
  have hss : Real.sqrt N ^ 2 = N := Real.sq_sqrt hNpos.le
  rw [hΔ]
  by_cases hσ : P.σ = 0
  · have hγ : completedStep P N = 1 / P.L := by rw [completedStep, if_pos hσ]
    rw [hγ, hσ]
    refine ⟨by positivity, le_rfl, ?_⟩
    have e : P.L * D ^ 2 / (N * (1 / P.L)) = P.L ^ 2 * D ^ 2 / N := by field_simp
    rw [e]
    have : P.L ^ 2 * D ^ 2 / N ≤ ε / 32 := by
      rw [div_le_iff₀ hNpos]; nlinarith
    nlinarith
  · have hσp : 0 < P.σ := lt_of_le_of_ne P.sigma_nonneg (Ne.symm hσ)
    have hγ : completedStep P N = min (1 / P.L) (P.Dt / (P.σ * Real.sqrt N)) := by
      rw [completedStep, if_neg hσ, GhadimiLan.TwoPhase.rsgStep]
    rw [hγ]
    have hγ0 : 0 < min (1 / P.L) (P.Dt / (P.σ * Real.sqrt N)) :=
      lt_min (by positivity) (by positivity)
    refine ⟨hγ0, min_le_left _ _, ?_⟩
    set s := Real.sqrt N with hs
    set γ := min (1 / P.L) (P.Dt / (P.σ * s)) with hγd
    have hN2 : 32 * P.L * (P.Dt + D ^ 2 / P.Dt) * P.σ ≤ s * ε := by
      have h1 := le_trans (le_max_right _ _) hNc
      have h2 : 32 * P.L * (P.Dt + D ^ 2 / P.Dt) * P.σ / ε ≤ s :=
        le_trans (le_abs_self _) (Real.abs_le_sqrt h1)
      exact (div_le_iff₀ hε).1 h2
    have hK : 1 ≤ γ * (P.L + P.σ * s / P.Dt) := by
      by_cases hle : 1 / P.L ≤ P.Dt / (P.σ * s)
      · have e : γ = 1 / P.L := min_eq_left hle
        rw [e, mul_add, one_div_mul_cancel hL.ne']
        have : 0 ≤ 1 / P.L * (P.σ * s / P.Dt) := by positivity
        linarith
      · have e : γ = P.Dt / (P.σ * s) := min_eq_right (le_of_not_ge hle)
        rw [e, mul_add]
        have e2 : P.Dt / (P.σ * s) * (P.σ * s / P.Dt) = 1 := by field_simp
        have : 0 ≤ P.Dt / (P.σ * s) * P.L := by positivity
        linarith
    have hγb : γ * (P.σ * s) ≤ P.Dt := by
      have := min_le_right (1 / P.L) (P.Dt / (P.σ * s))
      rwa [le_div_iff₀ (by positivity)] at this
    have hinv : 1 / γ ≤ P.L + P.σ * s / P.Dt := by
      rw [div_le_iff₀ hγ0]; linarith
    have t1 : P.L * D ^ 2 / (N * γ) ≤ P.L * D ^ 2 / N * (P.L + P.σ * s / P.Dt) := by
      rw [show P.L * D ^ 2 / (N * γ) = P.L * D ^ 2 / N * (1 / γ) by field_simp]
      exact mul_le_mul_of_nonneg_left hinv (by positivity)
    have t2 : P.L * γ * P.σ ^ 2 ≤ P.L * P.σ * P.Dt / s := by
      rw [le_div_iff₀ hspos]
      nlinarith [mul_le_mul_of_nonneg_left hγb (by positivity : 0 ≤ P.L * P.σ)]
    have e : P.L * D ^ 2 / N * (P.L + P.σ * s / P.Dt) + P.L * P.σ * P.Dt / s =
        P.L ^ 2 * D ^ 2 / s ^ 2 + P.L * (P.Dt + D ^ 2 / P.Dt) * P.σ / s := by
      rw [← hss]; field_simp; ring
    have b1 : P.L ^ 2 * D ^ 2 / s ^ 2 ≤ ε / 32 := by
      rw [div_le_iff₀ (by positivity), hss]; nlinarith
    have b2 : P.L * (P.Dt + D ^ 2 / P.Dt) * P.σ / s ≤ ε / 32 := by
      rw [div_le_iff₀ hspos]; nlinarith
    linarith


/-- Deterministic selection: a good candidate plus uniformly accurate estimates. -/
theorem select_good {n S : ℕ} (x1 : GhadimiLan.RSG.E n)
    (g : GhadimiLan.RSG.E n → GhadimiLan.RSG.E n)
    (p : Fin S → GhadimiLan.RSG.E n × GhadimiLan.RSG.E n) (ε : ℝ) (hε : 0 < ε)
    (h1 : ∃ s, ‖g (p s).1‖ ^ 2 ≤ ε / 8) (h2 : ∀ s, ‖(p s).2 - g (p s).1‖ ^ 2 < ε / 12) :
    ‖g (selectCandidate x1 ((List.finRange S).map p))‖ ^ 2 ≤ ε := by
  obtain ⟨s0, hs0⟩ := h1
  have hmem0 : p s0 ∈ (List.finRange S).map p := List.mem_map_of_mem (List.mem_finRange s0)
  have hne : (List.finRange S).map p ≠ [] := by
    intro h; rw [h] at hmem0; simp at hmem0
  obtain ⟨q, hq, hv, hmin⟩ := selectCandidate_spec x1 _ hne
  obtain ⟨s1, -, rfl⟩ := List.mem_map.1 hq
  rw [hv]
  have hm := hmin (p s0) hmem0
  have ha : ‖g (p s1).1‖ ≤ ‖(p s1).2‖ + ‖(p s1).2 - g (p s1).1‖ := by
    have := norm_sub_le (p s1).2 ((p s1).2 - g (p s1).1)
    rwa [sub_sub_cancel] at this
  have hb : ‖(p s0).2‖ ≤ ‖g (p s0).1‖ + ‖(p s0).2 - g (p s0).1‖ := by
    have := norm_add_le (g (p s0).1) ((p s0).2 - g (p s0).1)
    rwa [add_sub_cancel] at this
  have e0 := h2 s0
  have e1 := h2 s1
  set u := ‖g (p s0).1‖
  set a0 := ‖(p s0).2 - g (p s0).1‖
  set a1 := ‖(p s1).2 - g (p s1).1‖
  set w := ‖g (p s1).1‖
  have hu : 0 ≤ u := norm_nonneg _
  have ha0 : 0 ≤ a0 := norm_nonneg _
  have ha1 : 0 ≤ a1 := norm_nonneg _
  have hw : 0 ≤ w := norm_nonneg _
  have hw2 : w ≤ u + a0 + a1 := by linarith
  have hsq : w ^ 2 ≤ (u + a0 + a1) ^ 2 := pow_le_pow_left₀ hw hw2 2
  nlinarith [sq_nonneg (u - a0), sq_nonneg (u - a1), sq_nonneg (a0 - a1)]

/-- Markov in the form used twice. -/
theorem markov_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (X : Ω → ℝ) (hX0 : ∀ ω, 0 ≤ X ω) (hXi : Integrable X μ) (a b : ℝ) (ha : 0 < a)
    (hb : ∫ ω, X ω ∂μ ≤ b) : μ {ω | a ≤ X ω} ≤ ENNReal.ofReal (b / a) := by
  have h := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ hX0) hXi a
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
  apply ENNReal.ofReal_le_ofReal
  rw [le_div_iff₀ ha]
  have : a * μ.real {ω | a ≤ X ω} ≤ b := h.trans hb
  rw [measureReal_def] at this
  linarith

/-- Independent candidates: all fail with probability at most `q ^ S`. -/
theorem all_fail_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {S : ℕ} {β : Type*} [MeasurableSpace β] (c : Fin S → Ω → β) (hind : iIndepFun c μ)
    (B : Set β) (hB : MeasurableSet B) (q : ENNReal) (hq : ∀ s, μ (c s ⁻¹' B) ≤ q) :
    μ (⋂ s, c s ⁻¹' B) ≤ q ^ S := by
  have := hind.measure_inter_preimage_eq_mul Finset.univ (sets := fun _ => B) (fun _ _ => hB)
  simp only [Finset.mem_univ, Set.iInter_true] at this
  rw [this]
  calc ∏ s, μ (c s ⁻¹' B) ≤ ∏ _s : Fin S, q :=
        Finset.prod_le_prod (fun _ _ => zero_le) (fun s _ => hq s)
    _ = q ^ S := by simp

/-- (2.24): `S ≥ 1` and `2^{-S} ≤ Λ/2`. -/
theorem runCount_bound (Λ : ℝ) (hΛ0 : 0 < Λ) (hΛ1 : Λ < 1) :
    1 ≤ runCount Λ ∧ (1 / 2 : ℝ) ^ runCount Λ ≤ Λ / 2 := by
  have h2 : 1 < 2 / Λ := by rw [lt_div_iff₀ hΛ0]; linarith
  have hlog : 0 < Real.logb 2 (2 / Λ) := Real.logb_pos (by norm_num) h2
  have hS : Real.logb 2 (2 / Λ) ≤ (runCount Λ : ℝ) := Nat.le_ceil _
  refine ⟨?_, ?_⟩
  · have : 0 < runCount Λ := Nat.ceil_pos.2 hlog
    omega
  · have hp : 2 / Λ ≤ (2 : ℝ) ^ (runCount Λ : ℝ) := by
      calc 2 / Λ = (2 : ℝ) ^ Real.logb 2 (2 / Λ) :=
            (Real.rpow_logb (by norm_num) (by norm_num) (by positivity)).symm
        _ ≤ (2 : ℝ) ^ (runCount Λ : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hS
    rw [Real.rpow_natCast] at hp
    rw [div_pow, one_pow, div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hΛ0] at hp
    linarith


section Valid
variable {n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]

/-- Validation error of one candidate: `E‖T⁻¹ΣG(c,η_k) - g c‖² ≤ σ²/T`. -/
theorem validation_bound (P : Problem n Ξ) {Ω : Type*} [m0 : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ) (hT : 1 ≤ T)
    (c : Ω → GhadimiLan.RSG.E n) (η : ℕ → Ω → Ξ) (𝒢 : Filtration ℕ m0)
    (hc : Measurable[𝒢 0] c) (hA : FiniteA1 P μ 𝒢 (fun _ => c) η T) :
    Integrable (fun ω => ‖(T : ℝ)⁻¹ • ∑ k ∈ Finset.range T, P.G (c ω) (η (k + 1) ω) -
      P.g (c ω)‖ ^ 2) μ ∧
    ∫ ω, ‖(T : ℝ)⁻¹ • ∑ k ∈ Finset.range T, P.G (c ω) (η (k + 1) ω) - P.g (c ω)‖ ^ 2 ∂μ ≤
      P.σ ^ 2 / T := by
  have hgL : ∀ a b, ‖P.g a - P.g b‖ ≤ P.L * ‖a - b‖ := P.smooth.2.2
  have hgc : Continuous P.g := (LipschitzWith.of_dist_le' (K := P.L) fun a b => by
    rw [dist_eq_norm, dist_eq_norm]; exact hgL a b).continuous
  set δ : ℕ → Ω → GhadimiLan.RSG.E n := fun k ω => P.G (c ω) (η k ω) - P.g (c ω) with hδ
  have hck : ∀ k, Measurable[𝒢 k] c := fun k => hc.mono (𝒢.mono (Nat.zero_le k)) le_rfl
  have hgi : ∀ k, 1 ≤ k → k ≤ T → Integrable (fun ω => P.g (c ω)) μ := fun k h1 h2 =>
    integrable_condExp.congr (hA k (Finset.mem_Icc.2 ⟨h1, h2⟩)).2.2.2.1
  have hmeas : ∀ k, 1 ≤ k → k ≤ T → StronglyMeasurable[𝒢 k] (δ k) := by
    intro k h1 h2
    have hGk : Measurable[𝒢 k] (fun ω => P.G (c ω) (η k ω)) :=
      P.oracle_measurable.comp ((hck k).prodMk (hA k (Finset.mem_Icc.2 ⟨h1, h2⟩)).2.1)
    have hgk : Measurable[𝒢 k] (fun ω => P.g (c ω)) := hgc.measurable.comp (hck k)
    exact (hGk.sub hgk).stronglyMeasurable
  have hint : ∀ k, 1 ≤ k → k ≤ T → Integrable (δ k) μ := fun k h1 h2 =>
    (hA k (Finset.mem_Icc.2 ⟨h1, h2⟩)).2.2.1.sub (hgi k h1 h2)
  have hce : ∀ k, 1 ≤ k → k ≤ T → μ[δ k | 𝒢 (k - 1)] =ᵐ[μ] 0 := by
    intro k h1 h2
    have hAk := hA k (Finset.mem_Icc.2 ⟨h1, h2⟩)
    have e : δ k = (fun ω => P.G (c ω) (η k ω)) - (fun ω => P.g (c ω)) := rfl
    have hgs : μ[(fun ω => P.g (c ω)) | 𝒢 (k - 1)] = fun ω => P.g (c ω) :=
      condExp_of_stronglyMeasurable (𝒢.le (k - 1))
        ((hgc.measurable.comp (hck (k - 1))).stronglyMeasurable) (hgi k h1 h2)
    rw [e]
    filter_upwards [condExp_sub hAk.2.2.1 (hgi k h1 h2) (𝒢 (k - 1)), hAk.2.2.2.1] with ω ha hb
    rw [ha, hgs]
    simp [hb]
  have hsq : ∀ k, 1 ≤ k → k ≤ T → Integrable (fun ω => ‖δ k ω‖ ^ 2) μ := fun k h1 h2 =>
    (hA k (Finset.mem_Icc.2 ⟨h1, h2⟩)).2.2.2.2.1
  have hvar : ∀ k, 1 ≤ k → k ≤ T → ∫ ω, ‖δ k ω‖ ^ 2 ∂μ ≤ P.σ ^ 2 := fun k h1 h2 =>
    (hA k (Finset.mem_Icc.2 ⟨h1, h2⟩)).2.2.2.2.2
  obtain ⟨-, hI, hB⟩ := mds_sum_sq_bound 𝒢 δ T P.σ hmeas hint hce hsq hvar T le_rfl
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have e : (fun ω => ‖(T : ℝ)⁻¹ • ∑ k ∈ Finset.range T, P.G (c ω) (η (k + 1) ω) -
      P.g (c ω)‖ ^ 2) = fun ω => ((T : ℝ)⁻¹) ^ 2 * ‖∑ k ∈ Finset.range T, δ (k + 1) ω‖ ^ 2 := by
    funext ω
    have e1 : (T : ℝ)⁻¹ • ∑ k ∈ Finset.range T, δ (k + 1) ω =
        (T : ℝ)⁻¹ • ∑ k ∈ Finset.range T, P.G (c ω) (η (k + 1) ω) - P.g (c ω) := by
      calc (T : ℝ)⁻¹ • ∑ k ∈ Finset.range T, δ (k + 1) ω =
            (T : ℝ)⁻¹ • (∑ k ∈ Finset.range T, P.G (c ω) (η (k + 1) ω) - (T : ℝ) • P.g (c ω)) := by
            congr 1; simp [hδ, Finset.sum_sub_distrib]
            exact (Nat.cast_smul_eq_nsmul ℝ T (P.g (c ω))).symm
        _ = _ := by rw [smul_sub, smul_smul, inv_mul_cancel₀ hTpos.ne', one_smul]
    rw [← e1, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [e]
  refine ⟨hI.const_mul _, ?_⟩
  rw [integral_const_mul]
  calc ((T : ℝ)⁻¹) ^ 2 * ∫ ω, ‖∑ k ∈ Finset.range T, δ (k + 1) ω‖ ^ 2 ∂μ ≤
        ((T : ℝ)⁻¹) ^ 2 * (T * P.σ ^ 2) := mul_le_mul_of_nonneg_left hB (by positivity)
    _ = P.σ ^ 2 / T := by field_simp

/-- Zero noise: the stored reply is the true gradient almost surely. -/
theorem reply_ae_eq_of_sigma_zero (P : Problem n Ξ) {Ω : Type*} [m0 : MeasurableSpace Ω]
    (μ : Measure Ω) (N : ℕ) (ξ : ℕ → Ω → Ξ) (R : Ω → ℕ)
    (hlaw : RunLaw P μ N ξ R) (hσ : P.σ = 0) :
    ∀ᵐ ω ∂μ, (candidateExec P N ξ R ω).value.2 = P.g (candidateExec P N ξ R ω).value.1 := by
  obtain ⟨⟨ℱ, hA1⟩, ⟨-, hRr, -⟩, -⟩ := hlaw
  have hk : ∀ k, ∀ᵐ ω ∂μ, k ∈ Finset.Icc 1 N →
      P.G (trajectory P N ξ k ω) (ξ k ω) = P.g (trajectory P N ξ k ω) := by
    intro k
    by_cases hkm : k ∈ Finset.Icc 1 N
    · obtain ⟨-, -, -, -, hsq, hv⟩ := hA1 k hkm
      rw [hσ] at hv
      have h0 : ∫ ω, ‖P.G (trajectory P N ξ k ω) (ξ k ω) - P.g (trajectory P N ξ k ω)‖ ^ 2 ∂μ
          = 0 := le_antisymm (by simpa using hv) (integral_nonneg fun ω => by positivity)
      have hae := (integral_eq_zero_iff_of_nonneg (fun ω => by positivity) hsq).1 h0
      filter_upwards [hae] with ω hω _
      have : ‖P.G (trajectory P N ξ k ω) (ξ k ω) - P.g (trajectory P N ξ k ω)‖ ^ 2 = 0 := hω
      have := pow_eq_zero_iff (two_ne_zero) |>.1 this
      exact sub_eq_zero.1 (norm_eq_zero.1 this)
    · exact Filter.Eventually.of_forall fun ω h => absurd h hkm
  filter_upwards [ae_all_iff.2 hk] with ω hω
  rw [candidateExec_value P N ξ R ω (hRr ω)]
  exact hω (R ω) (hRr ω)

end Valid


end GLA7f

open GLA7f

set_option maxHeartbeats 1000000 in
open MeasureTheory ProbabilityTheory GhadimiLanAudit.TwoPhase in
theorem solution {n : ℕ} {Ξ Ω : Type*}
    [MeasurableSpace Ξ] [MeasurableSpace Ω]
    (P : Problem n Ξ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ε Λ : ℝ) (hε : 0 < ε) (hΛ0 : 0 < Λ) (hΛ1 : Λ < 1)
    (A : Input P (runCount Λ) (iterationCount P ε) Ω)
    (hlaw : SamplingLaw (T := validationCount P ε Λ) P μ A) :
    let result := fun ω => twoPhaseExec (T := validationCount P ε Λ) P A ω
    Measurable (fun ω => (result ω).value) ∧
    MeasurableSet {ω | ‖P.g (result ω).value‖ ^ 2 ≤ ε} ∧
    ENNReal.ofReal (1 - Λ) ≤ μ {ω | ‖P.g (result ω).value‖ ^ 2 ≤ ε} ∧
    ∀ ω, calls (result ω) ≤ runCount Λ * (iterationCount P ε + validationCount P ε Λ) := by
  intro result
  have hgL : ∀ a b, ‖P.g a - P.g b‖ ≤ P.L * ‖a - b‖ := P.smooth.2.2
  have hgc : Continuous P.g := (LipschitzWith.of_dist_le' (K := P.L) fun a b => by
    rw [dist_eq_norm, dist_eq_norm]; exact hgL a b).continuous
  have hcalls : ∀ ω, calls (result ω) ≤
      runCount Λ * (iterationCount P ε + validationCount P ε Λ) :=
    fun ω => calls_twoPhase_le P A ω
  by_cases hN : iterationCount P ε = 0
  · have hv : ∀ ω, (result ω).value = P.x1 := by
      intro ω
      show (twoPhaseExec (T := validationCount P ε Λ) P A ω).value = P.x1
      unfold twoPhaseExec
      rw [dif_pos hN]
      rfl
    have hg0 := g_x1_eq_zero_of_iter_zero P ε hε hN
    have hset : {ω | ‖P.g (result ω).value‖ ^ 2 ≤ ε} = Set.univ := by
      ext ω; simp [hv ω, hg0, hε.le]
    refine ⟨?_, ?_, ?_, hcalls⟩
    · have e : (fun ω => (result ω).value) = fun _ => P.x1 := funext hv
      rw [e]; exact measurable_const
    · rw [hset]; exact MeasurableSet.univ
    · rw [hset, measure_univ]; exact ENNReal.ofReal_le_one.2 (by linarith)
  · obtain ⟨hrun, hind, hval⟩ := hlaw hN
    have hN1 : 1 ≤ (iterationCount P ε) := Nat.one_le_iff_ne_zero.2 hN
    have hv : ∀ ω, (result ω).value =
        selectCandidate P.x1 ((List.finRange (runCount Λ)).map (fun s => pairFn (N := (iterationCount P ε)) (T := (validationCount P ε Λ)) P (A hN) s ω)) :=
      fun ω => by
        show (twoPhaseExec (T := (validationCount P ε Λ)) P A ω).value = _
        exact twoPhase_value_eq P A ω hN
    have hRm : ∀ s, Measurable ((A hN).R s) := by
      intro s; obtain ⟨-, ⟨h, -, -⟩, -⟩ := hrun s; exact h
    have hRr : ∀ s ω, (A hN).R s ω ∈ Finset.Icc 1 (iterationCount P ε) := by
      intro s; obtain ⟨-, ⟨-, h, -⟩, -⟩ := hrun s; exact h
    have hξm : ∀ s k, 1 ≤ k → k ≤ (iterationCount P ε) → Measurable ((A hN).ξ s k) := by
      intro s k h1 h2
      obtain ⟨⟨ℱ, hA1⟩, -, -⟩ := hrun s
      exact ((hA1 k (Finset.mem_Icc.2 ⟨h1, h2⟩)).2.1).mono (ℱ.le k) le_rfl
    have hcm : ∀ s, Measurable (fun ω => (candidateExec P (iterationCount P ε) ((A hN).ξ s) ((A hN).R s) ω).value) :=
      fun s => measurable_candidateExec_value P (iterationCount P ε) ((A hN).ξ s) ((A hN).R s) (hξm s) (hRm s) (hRr s)
    have hp1 : ∀ s ω, (pairFn (N := (iterationCount P ε)) (T := (validationCount P ε Λ)) P (A hN) s ω).1 = candidate (N := (iterationCount P ε)) P (A hN) s ω := by
      intro s ω
      by_cases hσ : P.σ = 0
      · simp only [pairFn, dif_pos hσ, candidate]
      · simp only [pairFn, dif_neg hσ, candidate]
    have hpm : ∀ s, Measurable (pairFn (N := (iterationCount P ε)) (T := (validationCount P ε Λ)) P (A hN) s) := by
      intro s
      have hc := hcm s
      by_cases hσ : P.σ = 0
      · have e : pairFn (N := (iterationCount P ε)) (T := (validationCount P ε Λ)) P (A hN) s =
            fun ω => (candidateExec P (iterationCount P ε) ((A hN).ξ s) ((A hN).R s) ω).value := by
          funext ω; simp only [pairFn, dif_pos hσ]
        rw [e]; exact hc
      · obtain ⟨𝒢, -, hA⟩ := hval hσ s
        have hη : ∀ k ∈ Finset.range (validationCount P ε Λ), Measurable ((A hN).η hσ s (k + 1)) := fun k hk =>
          ((hA (k + 1) (Finset.mem_Icc.2 ⟨by omega, by simp at hk; omega⟩)).2.1).mono
            (𝒢.le _) le_rfl
        have e : pairFn (N := (iterationCount P ε)) (T := (validationCount P ε Λ)) P (A hN) s = fun ω =>
            ((candidateExec P (iterationCount P ε) ((A hN).ξ s) ((A hN).R s) ω).value.1, ((validationCount P ε Λ) : ℝ)⁻¹ • ∑ k ∈ Finset.range (validationCount P ε Λ),
              P.G (candidateExec P (iterationCount P ε) ((A hN).ξ s) ((A hN).R s) ω).value.1 ((A hN).η hσ s (k + 1) ω)) := by
          funext ω; simp only [pairFn, dif_neg hσ]
        rw [e]
        exact hc.fst.prodMk ((measurable_const (a := ((validationCount P ε Λ : ℝ)⁻¹))).smul
          (Finset.measurable_sum _ fun k hk =>
            P.oracle_measurable.comp (hc.fst.prodMk (hη k hk))))
    have hmeasV : Measurable (fun ω => (result ω).value) := by
      have e : (fun ω => (result ω).value) = fun ω => selectCandidate P.x1
          (((List.finRange (runCount Λ)).map (fun s => pairFn (N := (iterationCount P ε)) (T := (validationCount P ε Λ)) P (A hN) s)).map
            (fun f => f ω)) := by
        funext ω; rw [hv ω, List.map_map]; rfl
      rw [e]
      exact measurable_selectCandidate P.x1 _ (fun f hf => by
        obtain ⟨s, -, rfl⟩ := List.mem_map.1 hf; exact hpm s)
    have hmeasG : MeasurableSet {ω | ‖P.g (result ω).value‖ ^ 2 ≤ ε} :=
      measurableSet_le ((hgc.measurable.comp hmeasV).norm.pow_const 2) measurable_const
    -- event 1: some run is good
    have hconst := rsg_const_bound P ε hε hN
    have hE1 : μ {ω | ¬ ∃ s, ‖P.g (candidate (N := (iterationCount P ε)) P (A hN) s ω)‖ ^ 2 ≤ ε / 8} ≤
        ENNReal.ofReal (Λ / 2) := by
      have hset : {ω | ¬ ∃ s, ‖P.g (candidate (N := (iterationCount P ε)) P (A hN) s ω)‖ ^ 2 ≤ ε / 8} =
          ⋂ s, (fun ω => candidate (N := (iterationCount P ε)) P (A hN) s ω) ⁻¹' {x | ε / 8 < ‖P.g x‖ ^ 2} := by
        ext ω; simp [not_le]
      rw [hset]
      have hBm : MeasurableSet {x : GhadimiLan.RSG.E n | ε / 8 < ‖P.g x‖ ^ 2} :=
        measurableSet_lt measurable_const (hgc.measurable.norm.pow_const 2)
      refine (all_fail_le _ hind _ hBm (ENNReal.ofReal (1 / 2)) (fun s => ?_)).trans ?_
      · have hcs : ∀ ω, candidate (N := (iterationCount P ε)) P (A hN) s ω = trajectory P (iterationCount P ε) ((A hN).ξ s) ((A hN).R s ω) ω := by
          intro ω
          simp only [candidate]
          rw [candidateExec_value P (iterationCount P ε) ((A hN).ξ s) ((A hN).R s) ω (hRr s ω)]
        obtain ⟨hI, hE⟩ := rsg_run_bound P μ (iterationCount P ε) hN1 ((A hN).ξ s) ((A hN).R s) (hrun s) hconst.1 hconst.2.1
        have hX : ∫ ω, ‖P.g (trajectory P (iterationCount P ε) ((A hN).ξ s) ((A hN).R s ω) ω)‖ ^ 2 ∂μ ≤ ε / 16 :=
          hE.trans hconst.2.2
        calc μ ((fun ω => candidate (N := (iterationCount P ε)) P (A hN) s ω) ⁻¹' {x | ε / 8 < ‖P.g x‖ ^ 2})
            ≤ μ {ω | ε / 8 ≤ ‖P.g (trajectory P (iterationCount P ε) ((A hN).ξ s) ((A hN).R s ω) ω)‖ ^ 2} := by
              apply measure_mono
              intro ω hω
              simp only [Set.mem_preimage, Set.mem_setOf_eq] at hω ⊢
              rw [hcs ω] at hω
              exact hω.le
          _ ≤ ENNReal.ofReal ((ε / 16) / (ε / 8)) :=
              markov_le _ (fun ω => by positivity) hI _ _ (by positivity) hX
          _ = ENNReal.ofReal (1 / 2) := by
              congr 1
              rw [div_div_div_eq, div_eq_iff (by positivity)]
              ring
      · rw [← ENNReal.ofReal_pow (by norm_num)]
        exact ENNReal.ofReal_le_ofReal (runCount_bound Λ hΛ0 hΛ1).2
    -- event 2: all estimates accurate
    have hE2 : μ {ω | ¬ ∀ s, ‖(pairFn (N := (iterationCount P ε)) (T := (validationCount P ε Λ)) P (A hN) s ω).2 -
        P.g (pairFn (N := (iterationCount P ε)) (T := (validationCount P ε Λ)) P (A hN) s ω).1‖ ^ 2 < ε / 12} ≤ ENNReal.ofReal (Λ / 2) := by
      by_cases hσ : P.σ = 0
      · have hae : ∀ᵐ ω ∂μ, ∀ s, (pairFn (N := (iterationCount P ε)) (T := (validationCount P ε Λ)) P (A hN) s ω).2 =
            P.g (pairFn (N := (iterationCount P ε)) (T := (validationCount P ε Λ)) P (A hN) s ω).1 := by
          rw [ae_all_iff]
          intro s
          filter_upwards [reply_ae_eq_of_sigma_zero P μ (iterationCount P ε) ((A hN).ξ s) ((A hN).R s) (hrun s) hσ] with ω hω
          simp only [pairFn, dif_pos hσ]
          exact hω
        have h0 : μ {ω | ¬ ∀ s, ‖(pairFn (N := (iterationCount P ε)) (T := (validationCount P ε Λ)) P (A hN) s ω).2 -
            P.g (pairFn (N := (iterationCount P ε)) (T := (validationCount P ε Λ)) P (A hN) s ω).1‖ ^ 2 < ε / 12} = 0 := by
          apply measure_mono_null _ (ae_iff.1 hae)
          intro ω hω
          simp only [Set.mem_setOf_eq] at hω ⊢
          intro hall
          apply hω
          intro s
          rw [hall s, sub_self, norm_zero]
          have : (0 : ℝ) < ε / 12 := by positivity
          simpa using this
        rw [h0]; exact zero_le
      · have hσp : 0 < P.σ := lt_of_le_of_ne P.sigma_nonneg (Ne.symm hσ)
        have hTge : 24 * (((runCount Λ) : ℝ) + 1) * P.σ ^ 2 / (Λ * ε) ≤ (validationCount P ε Λ) := Nat.le_ceil _
        have hTpos' : (0 : ℝ) < (validationCount P ε Λ) := lt_of_lt_of_le (by positivity) hTge
        have hT1 : 1 ≤ (validationCount P ε Λ) := by
          have : 0 < (validationCount P ε Λ) := by exact_mod_cast hTpos'
          omega
        have hset : {ω | ¬ ∀ s, ‖(pairFn (N := (iterationCount P ε)) (T := (validationCount P ε Λ)) P (A hN) s ω).2 -
            P.g (pairFn (N := (iterationCount P ε)) (T := (validationCount P ε Λ)) P (A hN) s ω).1‖ ^ 2 < ε / 12} =
            ⋃ s, {ω | ε / 12 ≤ ‖(pairFn (N := (iterationCount P ε)) (T := (validationCount P ε Λ)) P (A hN) s ω).2 -
              P.g (pairFn (N := (iterationCount P ε)) (T := (validationCount P ε Λ)) P (A hN) s ω).1‖ ^ 2} := by
          ext ω; simp [not_lt]
        rw [hset]
        refine (measure_iUnion_fintype_le _ _).trans ?_
        have hs : ∀ s, μ {ω | ε / 12 ≤ ‖(pairFn (N := (iterationCount P ε)) (T := (validationCount P ε Λ)) P (A hN) s ω).2 -
            P.g (pairFn (N := (iterationCount P ε)) (T := (validationCount P ε Λ)) P (A hN) s ω).1‖ ^ 2} ≤
              ENNReal.ofReal ((P.σ ^ 2 / (validationCount P ε Λ)) / (ε / 12)) := by
          intro s
          obtain ⟨𝒢, h𝒢0, hA⟩ := hval hσ s
          have hVB := validation_bound P μ (validationCount P ε Λ) hT1 (candidate (N := (iterationCount P ε)) P (A hN) s) ((A hN).η hσ s) 𝒢 h𝒢0 hA
          have e : ∀ ω, (pairFn (N := (iterationCount P ε)) (T := (validationCount P ε Λ)) P (A hN) s ω).2 -
              P.g (pairFn (N := (iterationCount P ε)) (T := (validationCount P ε Λ)) P (A hN) s ω).1 =
              ((validationCount P ε Λ) : ℝ)⁻¹ • ∑ k ∈ Finset.range (validationCount P ε Λ), P.G (candidate (N := (iterationCount P ε)) P (A hN) s ω)
                ((A hN).η hσ s (k + 1) ω) - P.g (candidate (N := (iterationCount P ε)) P (A hN) s ω) := by
            intro ω; simp only [pairFn, dif_neg hσ, candidate]
          simp only [e]
          exact markov_le _ (fun ω => by positivity) hVB.1 _ _ (by positivity) hVB.2
        refine (Finset.sum_le_sum fun s _ => hs s).trans ?_
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have key : ((runCount Λ) : ℝ) * (P.σ ^ 2 / (validationCount P ε Λ) / (ε / 12)) = 12 * (runCount Λ) * P.σ ^ 2 / ((validationCount P ε Λ) * ε) := by
          field_simp
        have hTge' : 24 * (((runCount Λ) : ℝ) + 1) * P.σ ^ 2 ≤ (validationCount P ε Λ) * (Λ * ε) :=
          (div_le_iff₀ (by positivity)).1 hTge
        rw [key, div_le_iff₀ (by positivity)]
        nlinarith [sq_nonneg P.σ]
    -- combine
    have hgoodsub : {ω | ‖P.g (result ω).value‖ ^ 2 ≤ ε}ᶜ ⊆
        {ω | ¬ ∃ s, ‖P.g (candidate (N := (iterationCount P ε)) P (A hN) s ω)‖ ^ 2 ≤ ε / 8} ∪
        {ω | ¬ ∀ s, ‖(pairFn (N := (iterationCount P ε)) (T := (validationCount P ε Λ)) P (A hN) s ω).2 -
          P.g (pairFn (N := (iterationCount P ε)) (T := (validationCount P ε Λ)) P (A hN) s ω).1‖ ^ 2 < ε / 12} := by
      intro ω hω
      by_contra hc
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
      obtain ⟨h1, h2⟩ := hc
      apply hω
      simp only [Set.mem_setOf_eq]
      rw [hv ω]
      apply select_good P.x1 P.g (fun s => pairFn (N := (iterationCount P ε)) (T := (validationCount P ε Λ)) P (A hN) s ω) ε hε
      · obtain ⟨s, hs⟩ := h1
        refine ⟨s, ?_⟩
        show ‖P.g (pairFn (N := (iterationCount P ε)) (T := (validationCount P ε Λ)) P (A hN) s ω).1‖ ^ 2 ≤ ε / 8
        rw [hp1]; exact hs
      · exact h2
    have hcomp : μ {ω | ‖P.g (result ω).value‖ ^ 2 ≤ ε}ᶜ ≤ ENNReal.ofReal Λ := by
      calc μ {ω | ‖P.g (result ω).value‖ ^ 2 ≤ ε}ᶜ ≤ _ := measure_mono hgoodsub
        _ ≤ _ := measure_union_le _ _
        _ ≤ ENNReal.ofReal (Λ / 2) + ENNReal.ofReal (Λ / 2) := add_le_add hE1 hE2
        _ = ENNReal.ofReal Λ := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
    refine ⟨hmeasV, hmeasG, ?_, hcalls⟩
    have h1 := prob_compl_eq_one_sub (μ := μ) hmeasG.compl
    rw [compl_compl] at h1
    rw [h1, ENNReal.ofReal_sub _ hΛ0.le, ENNReal.ofReal_one]
    exact tsub_le_tsub_left hcomp 1
