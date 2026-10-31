-- Prove2me | solution 1 for MostlyExplorationFree.GreedyBandit.theorem_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T18:44:59.318686+00:00
-- url     : https://prove2.me/submissions/0a82ad20-7da8-4ff0-853b-f93859c9b17e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MostlyExplorationFree_GreedyBandit_Model
import Theorems.Thm_MostlyExplorationFree_GreedyBandit_lemma_4
import Theorems.Thm_MostlyExplorationFree_GreedyBandit_lemma_6

open Matrix MeasureTheory ProbabilityTheory

namespace MEFGreedyAux
open MostlyExplorationFree.GreedyBandit

theorem armSeq_eq {d : ℕ} (β : Fin 2 → Fin d → ℝ) (x : ℕ → Fin d → ℝ)
    (e : Fin 2 → ℕ → ℝ) (w : ℕ → Bool) (t : ℕ) :
    armSeq β x e w t = greedyChoice (x t)
      (estOf β x e (fun s => if s < t then armSeq β x e w s else 0) 0 (t - 1))
      (estOf β x e (fun s => if s < t then armSeq β x e w s else 0) 1 (t - 1)) (w t) := by
  rw [armSeq, Nat.strongRec]
  simp only [dite_eq_ite]
  rfl

theorem continuous_lambdaMin {d : ℕ} :
    Continuous (fun M : Matrix (Fin d) (Fin d) ℝ => lambdaMin M) := by
  have hS : IsCompact {v : Fin d → ℝ | v ⬝ᵥ v = 1} := by
    apply IsCompact.of_isClosed_subset
      (isCompact_univ_pi (fun _ : Fin d => isCompact_Icc (a := (-1:ℝ)) (b := 1)))
    · exact isClosed_eq (continuous_id.dotProduct continuous_id) continuous_const
    · intro v hv
      simp only [Set.mem_ofPred_eq] at hv
      simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, true_implies]
      intro i
      have h1 : v i ^ 2 ≤ v ⬝ᵥ v := by
        simp only [dotProduct]
        have := Finset.single_le_sum (f := fun j => v j * v j)
          (fun j _ => mul_self_nonneg (v j)) (Finset.mem_univ i)
        nlinarith [this]
      rw [hv] at h1
      have := (sq_le_one_iff_abs_le_one (v i)).mp h1
      exact abs_le.mp this
  have := hS.continuous_sInf
    (f := fun (M : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) => v ⬝ᵥ (M *ᵥ v))
    (continuous_snd.dotProduct (continuous_fst.matrix_mulVec continuous_snd))
  convert this using 2 with M
  rw [sInf_image']
  rfl

theorem meas_of_matrix_cont {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {Y : Type*}
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (F : Matrix (Fin d) (Fin d) ℝ → Y) (hF : Continuous F) (G : Ω → Matrix (Fin d) (Fin d) ℝ)
    (hG : ∀ p q, Measurable fun ω => G ω p q) : Measurable fun ω => F (G ω) := by
  have h1 : Measurable (fun ω => (fun p q => G ω p q : Fin d → Fin d → ℝ)) :=
    measurable_pi_lambda _ (fun p => measurable_pi_lambda _ (fun q => hG p q))
  have h2 : Continuous (fun f : Fin d → Fin d → ℝ => F f) := hF
  exact h2.measurable.comp h1


section Meas
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

theorem measurable_gramOf_entry (X : ℕ → Ω → Fin d → ℝ) (hX : ∀ t, Measurable (X t))
    (a : Ω → ℕ → Fin 2) (ha : ∀ s, Measurable fun ω => a ω s) (i : Fin 2) (t : ℕ) (p q : Fin d) :
    Measurable fun ω => gramOf (fun s => X s ω) (a ω) i t p q := by
  have hXc : ∀ s p, Measurable fun ω => X s ω p := fun s p => (measurable_pi_apply p).comp (hX s)
  have hset : ∀ s, MeasurableSet {ω | a ω s = i} := fun s => (ha s) (measurableSet_singleton i)
  have : (fun ω => gramOf (fun s => X s ω) (a ω) i t p q) =
      fun ω => ∑ s ∈ Finset.Icc 1 t, if a ω s = i then X s ω p * X s ω q else 0 := by
    funext ω
    simp [gramOf, playedOf, Finset.sum_filter, Matrix.sum_apply, Matrix.vecMulVec_apply]
  rw [this]
  refine Finset.measurable_sum _ (fun s _ => ?_)
  exact Measurable.ite (hset s) ((hXc s p).mul (hXc s q)) measurable_const

theorem measurable_estOf (β : Fin 2 → Fin d → ℝ) (X : ℕ → Ω → Fin d → ℝ)
    (ε : Fin 2 → ℕ → Ω → ℝ)
    (hX : ∀ t, Measurable (X t)) (hε : ∀ i t, Measurable (ε i t))
    (a : Ω → ℕ → Fin 2) (ha : ∀ s, Measurable fun ω => a ω s) (i : Fin 2) (t : ℕ) :
    Measurable fun ω => estOf β (fun s => X s ω) (fun j s => ε j s ω) (a ω) i t := by
  have hXc : ∀ s p, Measurable fun ω => X s ω p := fun s p => (measurable_pi_apply p).comp (hX s)
  have hset : ∀ s, MeasurableSet {ω | a ω s = i} := fun s => (ha s) (measurableSet_singleton i)
  have hG := measurable_gramOf_entry X hX a ha i t
  have hv : ∀ l, Measurable fun ω => (∑ s ∈ playedOf (a ω) i t,
      rewardOf β (fun s => X s ω) (fun j s => ε j s ω) (a ω) s • X s ω) l := by
    intro l
    have : (fun ω => (∑ s ∈ playedOf (a ω) i t,
        rewardOf β (fun s => X s ω) (fun j s => ε j s ω) (a ω) s • X s ω) l) =
        fun ω => ∑ s ∈ Finset.Icc 1 t,
          if a ω s = i then (X s ω ⬝ᵥ β i + ε i s ω) * X s ω l else 0 := by
      funext ω
      simp only [playedOf, Finset.sum_filter, Finset.sum_apply, rewardOf]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      split_ifs with h
      · simp [h]
      · simp
    rw [this]
    refine Finset.measurable_sum _ (fun s _ => ?_)
    refine Measurable.ite (hset s) (Measurable.mul ?_ (hXc s l)) measurable_const
    refine Measurable.add ?_ (hε i s)
    simp only [dotProduct]
    exact Finset.measurable_sum _ (fun k _ => (hXc s k).mul measurable_const)
  have hdet : Measurable fun ω => (gramOf (fun s => X s ω) (a ω) i t).det :=
    meas_of_matrix_cont (fun M => M.det) (continuous_id.matrix_det) _ hG
  have hadj : ∀ k l, Measurable fun ω => (gramOf (fun s => X s ω) (a ω) i t).adjugate k l :=
    fun k l => meas_of_matrix_cont (fun M => M.adjugate k l)
      ((continuous_apply_apply k l).comp continuous_id.matrix_adjugate) _ hG
  unfold estOf
  refine Measurable.ite ?_ ?_ measurable_const
  · exact hdet (measurableSet_singleton 0).compl
  · refine measurable_pi_lambda _ (fun k => ?_)
    simp only [mulVec, dotProduct, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
    exact Finset.measurable_sum _ (fun l _ => ((hdet.inv.mul (hadj k l)).mul (hv l)))

theorem measurable_arm (β : Fin 2 → Fin d → ℝ) (X : ℕ → Ω → Fin d → ℝ)
    (ε : Fin 2 → ℕ → Ω → ℝ) (W : ℕ → Ω → Bool)
    (hX : ∀ t, Measurable (X t)) (hε : ∀ i t, Measurable (ε i t)) (hW : ∀ t, Measurable (W t))
    (t : ℕ) : Measurable (arm β X ε W t) := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
  have ha : ∀ s, Measurable fun ω => (if s < t then arm β X ε W s ω else 0 : Fin 2) := by
    intro s
    by_cases h : s < t
    · simp only [h, if_true]; exact ih s h
    · simp only [h, if_false]; exact measurable_const
  have e0 := measurable_estOf β X ε hX hε (fun ω s => if s < t then arm β X ε W s ω else 0) ha
    0 (t-1)
  have e1 := measurable_estOf β X ε hX hε (fun ω s => if s < t then arm β X ε W s ω else 0) ha
    1 (t-1)
  have hdot : ∀ (f : Ω → Fin d → ℝ), Measurable f → Measurable fun ω => X t ω ⬝ᵥ f ω :=
    fun f hf => (continuous_fst.dotProduct continuous_snd).measurable.comp ((hX t).prodMk hf)
  have : arm β X ε W t = fun ω => greedyChoice (X t ω)
      (estOf β (fun s => X s ω) (fun j s => ε j s ω)
        (fun s => if s < t then arm β X ε W s ω else 0) 0 (t-1))
      (estOf β (fun s => X s ω) (fun j s => ε j s ω)
        (fun s => if s < t then arm β X ε W s ω else 0) 1 (t-1)) (W t ω) := by
    funext ω
    unfold arm
    rw [armSeq_eq]
  rw [this]
  unfold greedyChoice
  refine Measurable.ite (measurableSet_lt (hdot _ e1) (hdot _ e0)) measurable_const
    (Measurable.ite (measurableSet_lt (hdot _ e0) (hdot _ e1)) measurable_const
      (Measurable.ite ((hW t) (measurableSet_singleton true)) measurable_const measurable_const))

theorem measurable_lambdaMin_gram (β : Fin 2 → Fin d → ℝ) (X : ℕ → Ω → Fin d → ℝ)
    (ε : Fin 2 → ℕ → Ω → ℝ) (W : ℕ → Ω → Bool)
    (hX : ∀ t, Measurable (X t)) (hε : ∀ i t, Measurable (ε i t)) (hW : ∀ t, Measurable (W t))
    (i : Fin 2) (t : ℕ) : Measurable fun ω => lambdaMin (gram β X ε W i t ω) := by
  exact meas_of_matrix_cont (fun M => lambdaMin M) continuous_lambdaMin _
    (measurable_gramOf_entry X hX (fun ω s => arm β X ε W s ω)
      (fun s => measurable_arm β X ε W hX hε hW s) i t)

end Meas


theorem harmonic_bound (n : ℕ) :
    ∑ k ∈ Finset.range n, 1 / ((k:ℝ) + 1) ≤ 1 + Real.log n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · have hn : (0:ℝ) < n := by exact_mod_cast h
      have hl := Real.one_sub_inv_le_log_of_pos (x := ((n:ℝ)+1)/n) (by positivity)
      rw [Real.log_div (by positivity) hn.ne'] at hl
      have : 1 - (((n:ℝ) + 1) / n)⁻¹ = 1 / ((n:ℝ)+1) := by field_simp; ring
      push_cast
      linarith

theorem geom_bound (c : ℝ) (hc : 0 < c) (n : ℕ) :
    ∑ k ∈ Finset.range n, Real.exp (-c * ((k:ℝ) + 1)) ≤ 1 / c := by
  set q := Real.exp (-c) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by rw [hq, ← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  have hterm : ∀ k : ℕ, Real.exp (-c * ((k:ℝ) + 1)) = q ^ (k+1) := by
    intro k; rw [hq, ← Real.exp_nat_mul]; push_cast; ring_nf
  simp only [hterm]
  have hid : ∀ m : ℕ, (∑ k ∈ Finset.range m, q ^ (k+1)) * (1 - q) = q - q ^ (m+1) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, add_mul, ih]; ring
  have h1 : (∑ k ∈ Finset.range n, q ^ (k+1)) ≤ q / (1 - q) := by
    rw [le_div_iff₀ (by linarith), hid]
    have : 0 ≤ q ^ (n+1) := by positivity
    linarith
  have h2 : q / (1 - q) ≤ 1 / c := by
    rw [div_le_div_iff₀ (by linarith) hc]
    have he : c + 1 ≤ Real.exp c := Real.add_one_le_exp c
    have : q * Real.exp c = 1 := by rw [hq, ← Real.exp_add]; simp
    nlinarith
  linarith

theorem abs_dot_le {d : ℕ} (x y : Fin d → ℝ) : |x ⬝ᵥ y| ≤ l2norm x * l2norm y := by
  unfold l2norm
  have h0 : (0:ℝ) ≤ x ⬝ᵥ x := Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))
  rw [← Real.sqrt_mul h0]
  apply Real.abs_le_sqrt
  have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x y
  simpa [dotProduct, sq] using this

end MEFGreedyAux

open MostlyExplorationFree.GreedyBandit MEFGreedyAux

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {d : ℕ} (hd : 2 ≤ d)
    (μ : Measure (Fin d → ℝ)) (X : ℕ → Ω → Fin d → ℝ) (ε : Fin 2 → ℕ → Ω → ℝ)
    (W : ℕ → Ω → Bool) (σ : ℝ) (hσ : 0 < σ) (β : Fin 2 → Fin d → ℝ)
    (xmax bmax C0 lam0 : ℝ)
    (hmodel : IsGreedyModel P μ X ε W σ) (hA1 : ParameterSet μ β xmax bmax)
    (hA2 : MarginCondition μ β C0) (hA3 : CovariateDiversity μ lam0)
    (T : ℕ) (hT : 3 ≤ T) :
    regret β X ε W P T
      ≤ 128 * C0 * Cbar d * xmax ^ 4 * σ ^ 2 * d * Real.log d ^ (3 / 2 : ℝ) / lam0 ^ 2
          * Real.log T
        + (128 * C0 * Cbar d * xmax ^ 4 * σ ^ 2 * d * Real.log d ^ (3 / 2 : ℝ) / lam0 ^ 2
          + 160 * bmax * xmax ^ 3 * d / lam0 + 2 * xmax * bmax) := by
  have := hmodel.isProbability
  obtain ⟨hxmax, hXb, hβb⟩ := hA1
  have hC0 := hA2.1
  have hlam0 := hA3.1
  have hbmax : 0 ≤ bmax := le_trans (Real.sqrt_nonneg _) (hβb 0)
  have hdpos : (0:ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hlogd : 0 < Real.log d := Real.log_pos (by exact_mod_cast (by omega : 1 < d))
  have hCbar : 0 ≤ Cbar d := by unfold Cbar; positivity
  set A := 128 * C0 * Cbar d * xmax ^ 4 * σ ^ 2 * d * Real.log d ^ (3 / 2 : ℝ) / lam0 ^ 2
    with hA
  have hA0 : 0 ≤ A := by positivity
  set c1 := C1 lam0 xmax with hc1def
  have hc1 : 0 < c1 := by rw [hc1def]; unfold C1; positivity
  have hXm := hmodel.measurable_X
  have hεm := hmodel.measurable_ε
  have hWm := hmodel.measurable_W
  -- Step 1: the per-period bound for t = k + 2 (Lemma 6 combined with Lemma 4).
  have hstep : ∀ k : ℕ, instRegret β X ε W P (k + 2)
      ≤ A * (1 / ((k:ℝ) + 1)) + 4 * bmax * xmax * (d * Real.exp (-c1 * ((k:ℝ) + 1))) := by
    intro k
    have h6 := lemma_6 P hd μ X ε W σ hσ β xmax bmax C0 lam0 hlam0 hmodel
      ⟨hxmax, hXb, hβb⟩ hA2 (k + 2) (by omega)
    have hcast : ((k + 2 : ℕ) : ℝ) - 1 = (k:ℝ) + 1 := by push_cast; ring
    have hk : k + 2 - 1 = k + 1 := by omega
    rw [hcast, hk] at h6
    have hprob : ∀ i : Fin 2,
        (P {ω | lambdaMin (gram β X ε W i (k + 1) ω) < lam0 * ((k:ℝ) + 1) / 4}).toReal
          ≤ d * Real.exp (-c1 * ((k:ℝ) + 1)) := by
      intro i
      have h4 := lemma_4 P (by omega) μ X ε W σ β xmax bmax lam0 hmodel ⟨hxmax, hXb, hβb⟩
        hA3 i (k + 1) (by omega)
      set S := {ω | lam0 * ((k + 1 : ℕ) : ℝ) / 4 ≤ lambdaMin (gram β X ε W i (k + 1) ω)}
        with hS
      have hmeas : MeasurableSet S :=
        measurableSet_le measurable_const (measurable_lambdaMin_gram β X ε W hXm hεm hWm i (k + 1))
      have hc := measure_add_measure_compl (μ := P) hmeas
      rw [measure_univ] at hc
      have hset : {ω | lambdaMin (gram β X ε W i (k + 1) ω) < lam0 * ((k:ℝ) + 1) / 4} = Sᶜ := by
        ext ω
        simp only [hS, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]
        push_cast
        rfl
      rw [hset]
      have hsum : (P S).toReal + (P Sᶜ).toReal = 1 := by
        rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), hc]
        simp
      have hexp : Real.exp (Real.log d - c1 * ((k + 1 : ℕ) : ℝ))
          = d * Real.exp (-c1 * ((k:ℝ) + 1)) := by
        rw [Real.exp_sub, Real.exp_log hdpos, div_eq_mul_inv, ← Real.exp_neg]
        push_cast
        ring_nf
      rw [hexp] at h4
      linarith
    have hmax := max_le (hprob 0) (hprob 1)
    have hfirst : 4 * C0 * Cbar d * xmax ^ 2 * Real.log d ^ (3 / 2 : ℝ) / C3 lam0 d σ xmax = A := by
      unfold C3
      rw [hA]
      field_simp
      ring
    rw [hfirst] at h6
    have := mul_le_mul_of_nonneg_left hmax (by positivity : (0:ℝ) ≤ 4 * bmax * xmax)
    linarith
  -- Step 2: the first period costs at most 2 x_max b_max.
  have hr1 : instRegret β X ε W P 1 ≤ 2 * xmax * bmax := by
    unfold instRegret
    have hae : ∀ᵐ ω ∂P, l2norm (X 1 ω) ≤ xmax := by
      have h := hXb
      rw [← hmodel.law_X 1 le_rfl] at h
      exact ae_of_ae_map (hXm 1).aemeasurable h
    have hb := norm_integral_le_of_norm_le_const (μ := P) (C := 2 * xmax * bmax)
      (f := fun ω => max (X 1 ω ⬝ᵥ β 0) (X 1 ω ⬝ᵥ β 1) - X 1 ω ⬝ᵥ β (arm β X ε W 1 ω)) ?_
    · simp only [probReal_univ, mul_one] at hb
      exact le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using hb)
    · filter_upwards [hae] with ω hω
      have hj : ∀ j, |X 1 ω ⬝ᵥ β j| ≤ xmax * bmax := fun j =>
        (abs_dot_le _ _).trans (mul_le_mul hω (hβb j) (Real.sqrt_nonneg _) hxmax.le)
      rw [Real.norm_eq_abs]
      have h0 := abs_le.mp (hj 0)
      have h1 := abs_le.mp (hj 1)
      have hj' := abs_le.mp (hj (arm β X ε W 1 ω))
      rw [abs_le]
      constructor
      · have := le_max_left (X 1 ω ⬝ᵥ β 0) (X 1 ω ⬝ᵥ β 1)
        linarith
      · have := max_le_iff.mpr (⟨by linarith, by linarith⟩ :
          X 1 ω ⬝ᵥ β 0 ≤ xmax * bmax ∧ X 1 ω ⬝ᵥ β 1 ≤ xmax * bmax)
        linarith
  -- Step 3: summation.
  obtain ⟨n, rfl⟩ : ∃ n, T = n + 1 := ⟨T - 1, by omega⟩
  have hreg : regret β X ε W P (n + 1)
      = instRegret β X ε W P 1 + ∑ k ∈ Finset.range n, instRegret β X ε W P (k + 2) := by
    unfold regret
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel,
      Finset.sum_range_succ']
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl (fun k _ => ?_)
    congr 1
    omega
  rw [hreg]
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range n) => hstep k)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hH := harmonic_bound n
  have hG := geom_bound c1 hc1 n
  have hn : (1:ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hlog : Real.log n ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
    Real.log_le_log (by linarith) (by push_cast; linarith)
  have hAH := mul_le_mul_of_nonneg_left hH hA0
  have hBG := mul_le_mul_of_nonneg_left hG (by positivity : (0:ℝ) ≤ 4 * bmax * xmax * d)
  have hBval : 4 * bmax * xmax * d * (1 / c1) = 160 * bmax * xmax ^ 3 * d / lam0 := by
    rw [hc1def]; unfold C1; field_simp; ring
  have hAlog := mul_le_mul_of_nonneg_left hlog hA0
  nlinarith
