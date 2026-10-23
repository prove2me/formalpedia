-- Prove2me | solution 1 for NonstatRL.PerStep.lemma2_span_le_two_diameter
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T17:23:07.39714+00:00
-- url     : https://prove2.me/submissions/f0a827a3-e065-4e5b-93ef-e52bd5c85b70

import Mathlib
import Definitions.Def_NonstatRL_Oracle_Model

open BanditAlgorithm MeasureTheory ProbabilityTheory ENNReal NNReal

namespace SwucrlAux

/-- killed transition operator on ENNReal functions -/
noncomputable def QE {S A : ℕ} (M : FiniteMDP S A) (f : Fin S → Fin A) (tgt : Fin S)
    (φ : Fin S → ℝ≥0∞) (y : Fin S) : ℝ≥0∞ :=
  ∑ z, (M.P y (f y) z : ℝ≥0∞) * (if z = tgt then 0 else φ z)

def survSet {S A : ℕ} (tgt : Fin S) (n : ℕ) : Set (MDPTrajectory S A (n + 1)) :=
  {h | ∀ i : Fin (n + 1), i ≠ 0 → (h i).1 ≠ tgt}

lemma trans_apply {S A : ℕ} (M : FiniteMDP S A) (p : Fin S × Fin A) :
    mdpTransitionKernel M p = (M.transitionDist p.1 p.2).toMeasure := rfl

lemma lintegral_toMeasure {S : ℕ} (d : MDPStateDistribution S) (g : Fin S → ℝ≥0∞) :
    ∫⁻ x, g x ∂ d.toMeasure = ∑ x, (d.prob x : ℝ≥0∞) * g x := by
  rw [MDPStateDistribution.toMeasure, lintegral_finset_sum_measure]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [lintegral_smul_measure, lintegral_dirac]
  rfl

lemma step_lintegral {S A : ℕ} (M : FiniteMDP S A) (μ0 : MDPStateDistribution S)
    (f : Fin S → Fin A) (n : ℕ) (h : MDPTrajectory S A n)
    (ψ : Fin S × Fin A → ℝ≥0∞) :
    ∫⁻ p, ψ p ∂ (mdpStepKernel M μ0 (mdpMemorylessDetPolicy f) n h) =
      ∫⁻ x, ψ (x, f x) ∂ (mdpStateKernel M μ0 n h) := by
  rw [mdpStepKernel, Kernel.lintegral_compProd _ _ _ (Measurable.of_discrete)]
  refine lintegral_congr fun x => ?_
  simp only [mdpMemorylessDetPolicy]
  rw [Kernel.deterministic_apply, lintegral_dirac]

lemma surv_lintegral {S A : ℕ} (M : FiniteMDP S A) (f : Fin S → Fin A)
    (x0 tgt : Fin S) (n : ℕ) :
    ∀ ψ : Fin S × Fin A → ℝ≥0∞,
    ∫⁻ h, (survSet (A := A) tgt n).indicator (fun h => ψ (h (Fin.last n))) h
      ∂ mdpMeasure M (mdpStateDirac x0) (mdpMemorylessDetPolicy f) (n + 1) =
      (QE M f tgt)^[n] (fun y => ψ (y, f y)) x0 := by
  induction n with
  | zero =>
    intro ψ
    rw [mdpMeasure, lintegral_map Measurable.of_discrete measurable_mdpTrajectorySnoc,
      Measure.lintegral_compProd Measurable.of_discrete]
    rw [mdpMeasure, lintegral_dirac]
    rw [step_lintegral]
    simp only [mdpStateKernel, Kernel.const_apply]
    rw [lintegral_toMeasure]
    have : ∀ x : Fin S, (survSet (A := A) tgt 0).indicator
        (fun h => ψ (h (Fin.last 0)))
        (Fin.snoc (α := fun _ ↦ Fin S × Fin A) (fun t ↦ t.elim0) (x, f x)) = ψ (x, f x) := by
      intro x
      rw [Set.indicator_of_mem]
      · rfl
      · intro i hi
        exact absurd (Subsingleton.elim (α := Fin 1) i 0) hi
    simp only [this, mdpStateDirac, Function.iterate_zero, id]
    rw [Finset.sum_eq_single x0 (fun b _ hb => by simp [hb]) (by simp)]
    simp
  | succ n ih =>
    intro ψ
    rw [mdpMeasure, lintegral_map Measurable.of_discrete measurable_mdpTrajectorySnoc,
      Measure.lintegral_compProd Measurable.of_discrete]
    set ψ' : Fin S × Fin A → ℝ≥0∞ := fun yb =>
      ∑ z, (M.P yb.1 yb.2 z : ℝ≥0∞) * (if z = tgt then 0 else ψ (z, f z)) with hψ'
    have key : ∀ h : MDPTrajectory S A (n + 1),
        ∫⁻ p, (survSet (A := A) tgt (n + 1)).indicator
          (fun h => ψ (h (Fin.last (n + 1))))
          (Fin.snoc (α := fun _ ↦ Fin S × Fin A) h p)
          ∂ (mdpStepKernel M (mdpStateDirac x0) (mdpMemorylessDetPolicy f) (n + 1) h) =
        (survSet (A := A) tgt n).indicator (fun h => ψ' (h (Fin.last n))) h := by
      intro h
      rw [step_lintegral]
      simp only [mdpStateKernel]
      rw [Kernel.comap_apply, trans_apply, FiniteMDP.transitionDist,
        lintegral_toMeasure]
      by_cases hh : h ∈ survSet (A := A) tgt n
      · rw [Set.indicator_of_mem hh, hψ']
        refine Finset.sum_congr rfl fun z _ => ?_
        congr 1
        by_cases hz : z = tgt
        · rw [if_pos hz, Set.indicator_of_notMem]
          intro hmem
          exact hmem (Fin.last (n + 1)) (Fin.ext_iff.not.mpr (by simp)) (by simpa using hz)
        · rw [if_neg hz, Set.indicator_of_mem]
          · simp
          · intro i hi
            induction i using Fin.lastCases with
            | last => simpa using hz
            | cast j =>
              intro hj
              rw [Fin.snoc_castSucc] at hj
              exact hh j (by rintro rfl; exact hi (by simp)) hj
      · rw [Set.indicator_of_notMem hh]
        refine Finset.sum_eq_zero fun z _ => ?_
        rw [Set.indicator_of_notMem]
        · simp
        · intro hmem
          apply hh
          intro j hj
          have := hmem (Fin.castSucc j) (by
            intro h0; apply hj; exact Fin.castSucc_injective _ (by simpa using h0))
          simpa [Fin.snoc_castSucc] using this
    simp_rw [key]
    rw [ih ψ', Function.iterate_succ_apply]
    congr 1

end SwucrlAux

namespace SwucrlAux

/-- real survival probabilities -/
noncomputable def U {S A : ℕ} (M : FiniteMDP S A) (f : Fin S → Fin A) (tgt : Fin S) :
    ℕ → Fin S → ℝ
  | 0 => fun _ => 1
  | k + 1 => fun y => ∑ z, (M.P y (f y) z : ℝ) * ((if z = tgt then 0 else 1) * U M f tgt k z)

lemma U_nonneg {S A : ℕ} (M : FiniteMDP S A) (f : Fin S → Fin A) (tgt : Fin S) :
    ∀ k y, 0 ≤ U M f tgt k y := by
  intro k
  induction k with
  | zero => intro y; simp [U]
  | succ k ih =>
    intro y
    simp only [U]
    refine Finset.sum_nonneg fun z _ => mul_nonneg (by positivity) (mul_nonneg ?_ (ih z))
    split_ifs <;> norm_num

lemma QE_iter_eq {S A : ℕ} (M : FiniteMDP S A) (f : Fin S → Fin A) (tgt : Fin S) :
    ∀ k y, (QE M f tgt)^[k] (fun _ => 1) y = ENNReal.ofReal (U M f tgt k y) := by
  intro k
  induction k with
  | zero => intro y; simp [U]
  | succ k ih =>
    intro y
    rw [Function.iterate_succ_apply', QE, U, ENNReal.ofReal_sum_of_nonneg]
    · refine Finset.sum_congr rfl fun z _ => ?_
      rw [ih, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal]
      congr 1
      split_ifs <;> simp
    · intro z _
      refine mul_nonneg (by positivity) (mul_nonneg ?_ (U_nonneg M f tgt k z))
      split_ifs <;> norm_num

lemma hitTime_eq {S A : ℕ} (M : FiniteMDP S A) (f : Fin S → Fin A) (x tgt : Fin S) :
    NonstatRL.Oracle.hitTime M f x tgt = ∑' k, ENNReal.ofReal (U M f tgt k x) := by
  rw [NonstatRL.Oracle.hitTime]
  congr 1
  funext k
  have h := surv_lintegral M f x tgt k (fun _ => 1)
  rw [lintegral_indicator_const MeasurableSet.of_discrete, one_mul] at h
  rw [← QE_iter_eq, ← h]
  rfl

/-- the core hitting-time estimate -/
lemma gap_le {S A : ℕ} (M : FiniteMDP S A) (f : Fin S → Fin A) (tgt x : Fin S)
    (γ : Fin S → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hineq : ∀ y, ∑ z, (M.P y (f y) z : ℝ) * γ z ≤ c + γ y)
    (hfin : NonstatRL.Oracle.hitTime M f x tgt ≠ ⊤) :
    γ tgt - γ x ≤ c * (NonstatRL.Oracle.hitTime M f x tgt).toReal := by
  set g : Fin S → ℝ := fun y => γ tgt - γ y with hg
  set w : Fin S → ℝ := fun z => if z = tgt then 0 else 1 with hw
  have hwg : ∀ z, w z * g z = g z := by
    intro z; by_cases hz : z = tgt
    · simp [hw, hg, hz]
    · simp [hw, hz]
  have hPsum : ∀ y, ∑ z, (M.P y (f y) z : ℝ) = 1 := by
    intro y
    have := M.P_sum_one y (f y)
    exact_mod_cast this
  have hstep : ∀ y, g y ≤ ∑ z, (M.P y (f y) z : ℝ) * (w z * g z) + c := by
    intro y
    rw [Finset.sum_congr rfl (fun z _ => by rw [hwg z])]
    simp only [hg, mul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_mul, hPsum, one_mul]
    linarith [hineq y]
  set B : ℝ := ∑ y, |g y| with hB
  have hgB : ∀ y, g y ≤ B := fun y =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun y => |g y|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ y))
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hw0 : ∀ z, 0 ≤ w z := by intro z; simp only [hw]; split_ifs <;> norm_num
  have main : ∀ n y, g y ≤ B * U M f tgt n y +
      c * ∑ k ∈ Finset.range n, U M f tgt k y := by
    intro n
    induction n with
    | zero => intro y; simpa [U] using hgB y
    | succ n ih =>
      intro y
      calc g y ≤ ∑ z, (M.P y (f y) z : ℝ) * (w z * g z) + c := hstep y
        _ ≤ ∑ z, (M.P y (f y) z : ℝ) * (w z * (B * U M f tgt n z +
              c * ∑ k ∈ Finset.range n, U M f tgt k z)) + c := by
          apply add_le_add_left
          apply Finset.sum_le_sum
          intro z _
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left (ih z) (hw0 z)
        _ = B * U M f tgt (n + 1) y +
              c * ∑ k ∈ Finset.range (n + 1), U M f tgt k y := by
          have e : ∀ z, (M.P y (f y) z : ℝ) * (w z * (B * U M f tgt n z +
              c * ∑ k ∈ Finset.range n, U M f tgt k z)) =
              B * ((M.P y (f y) z : ℝ) * (w z * U M f tgt n z)) +
              c * ∑ k ∈ Finset.range n, (M.P y (f y) z : ℝ) * (w z * U M f tgt k z) := by
            intro z
            rw [show (M.P y (f y) z : ℝ) * (w z * (B * U M f tgt n z +
              c * ∑ k ∈ Finset.range n, U M f tgt k z)) =
              B * ((M.P y (f y) z : ℝ) * (w z * U M f tgt n z)) +
              c * ((M.P y (f y) z : ℝ) * (w z * ∑ k ∈ Finset.range n, U M f tgt k z)) by ring,
              Finset.mul_sum, Finset.mul_sum]
          rw [Finset.sum_congr rfl (fun z _ => e z), Finset.sum_add_distrib,
            ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm, Finset.sum_range_succ']
          simp only [U, hw]
          ring
  have hnn : ∀ k, 0 ≤ U M f tgt k x := fun k => U_nonneg M f tgt k x
  rw [hitTime_eq] at hfin ⊢
  have hsum : Summable fun k => U M f tgt k x := by
    have := ENNReal.summable_toReal hfin
    simpa [ENNReal.toReal_ofReal (hnn _)] using this
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn hsum, ENNReal.toReal_ofReal (tsum_nonneg hnn)]
  set H := ∑' k, U M f tgt k x
  have hlim : Filter.Tendsto (fun n => B * U M f tgt n x + c * H) Filter.atTop
      (nhds (B * 0 + c * H)) :=
    (hsum.tendsto_atTop_zero.const_mul B).add_const _
  have := ge_of_tendsto' hlim (fun n => (main n x).trans (by
    gcongr
    exact hsum.sum_le_tsum _ (fun k _ => hnn k)))
  simp only [mul_zero, zero_add] at this
  exact this

end SwucrlAux

namespace SwucrlAux

lemma one_le_hitTime {S A : ℕ} (M : FiniteMDP S A) (f : Fin S → Fin A) (x tgt : Fin S) :
    1 ≤ NonstatRL.Oracle.hitTime M f x tgt := by
  rw [hitTime_eq]
  refine le_trans ?_ (ENNReal.le_tsum 0)
  simp [U]

lemma span_le {S A : ℕ} (As : Fin S → Finset (Fin A)) (Mw : FiniteMDP S A) (D c : ℝ)
    (γ : Fin S → ℝ) (hc0 : 0 ≤ c) (hc2 : c ≤ 2)
    (hdiam : NonstatRL.Oracle.diameter Mw As ≤ ENNReal.ofReal D)
    (hineq : ∀ y a, a ∈ As y → ∑ z, (Mw.P y a z : ℝ) * γ z ≤ c + γ y) :
    ∀ s s' : Fin S, γ s - γ s' ≤ 2 * D := by
  intro s s'
  have hinf : (⨅ f : Fin S → Fin A, ⨅ (_ : ∀ x, f x ∈ As x),
      NonstatRL.Oracle.hitTime Mw f s' s) ≤ ENNReal.ofReal D := by
    refine le_trans ?_ hdiam
    rw [NonstatRL.Oracle.diameter]
    exact le_iSup₂ (f := fun a b => ⨅ f : Fin S → Fin A, ⨅ (_ : ∀ x, f x ∈ As x),
      NonstatRL.Oracle.hitTime Mw f a b) s' s
  have hD : 1 ≤ D := by
    have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal D :=
      le_trans (le_iInf₂ fun f _ => one_le_hitTime Mw f s' s) hinf
    exact (ENNReal.one_le_ofReal).1 h1
  by_contra hlt
  push_neg at hlt
  set ε := (γ s - γ s' - 2 * D) / 4 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  have hlt2 : (⨅ f : Fin S → Fin A, ⨅ (_ : ∀ x, f x ∈ As x),
      NonstatRL.Oracle.hitTime Mw f s' s) < ENNReal.ofReal (D + ε) :=
    lt_of_le_of_lt hinf ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith))
  obtain ⟨f, hf⟩ := iInf_lt_iff.1 hlt2
  obtain ⟨hfA, hfT⟩ := iInf_lt_iff.1 hf
  have hgap := gap_le Mw f s s' γ c hc0 (fun y => hineq y (f y) (hfA y)) (ne_top_of_lt hfT)
  have hH : (NonstatRL.Oracle.hitTime Mw f s' s).toReal < D + ε :=
    ENNReal.toReal_lt_of_lt_ofReal hfT
  have hH0 : 0 ≤ (NonstatRL.Oracle.hitTime Mw f s' s).toReal := ENNReal.toReal_nonneg
  have : c * (NonstatRL.Oracle.hitTime Mw f s' s).toReal ≤ 2 * (D + ε) :=
    mul_le_mul hc2 hH.le hH0 (by norm_num)
  linarith

end SwucrlAux

theorem solution {S A : ℕ} (hS : 0 < S)
    (r : Fin S → Fin A → ℝ) (As : Fin S → Finset (Fin A))
    (hAs : ∀ s, (As s).Nonempty)
    (hr : ∀ s a, a ∈ As s → 0 ≤ r s a)
    (Mw : FiniteMDP S A) (D ρ : ℝ) (γ : Fin S → ℝ)
    (hdiam : NonstatRL.Oracle.diameter Mw As ≤ ENNReal.ofReal D)
    (hdual : NonstatRL.Oracle.DualFeasible r (fun s a s' => (Mw.P s a s' : ℝ)) As ρ γ)
    (hρ : ρ ≤ 2) :
    ∀ s s' : Fin S, γ s - γ s' ≤ 2 * D := by
  refine SwucrlAux.span_le As Mw D (max ρ 0) γ (le_max_right _ _) (max_le hρ (by norm_num))
    hdiam ?_
  intro y a ha
  have h1 := hdual y a ha
  have h2 := hr y a ha
  have h3 := le_max_left ρ 0
  simp only at h1
  linarith

