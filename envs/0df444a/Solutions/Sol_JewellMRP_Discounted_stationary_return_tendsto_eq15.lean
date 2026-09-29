-- Prove2me | solution 1 for JewellMRP.Discounted.stationary_return_tendsto_eq15
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:08:07.55498+00:00
-- url     : https://prove2.me/submissions/a1eb8a18-6363-4d35-b225-528db99940c6

import Mathlib
import Definitions.Def_JewellMRP_Discounted_MRP
import Definitions.Def_JewellMRP_Discounted_PolicyIteration

open Filter Topology

namespace JewellMRP.Discounted

open MeasureTheory

lemma aux_sre15_ae_pos {S A : Type*} [Fintype S] (M : MRP S A) (z : A) (i j : S) :
    ∀ᵐ t ∂(M.F z i j), t ∈ Set.Ioi (0 : ℝ) := by
  rw [ae_iff]
  have h : {a : ℝ | ¬ a ∈ Set.Ioi (0 : ℝ)} = Set.Iic 0 := by
    ext a; simp
  rw [h]
  exact M.F_Iic_zero z i j

lemma aux_sre15_restrict_eq {S A : Type*} [Fintype S] (M : MRP S A) (z : A) (i j : S) :
    (M.F z i j).restrict (Set.Ioi 0) = M.F z i j :=
  Measure.restrict_eq_self_of_ae_mem (aux_sre15_ae_pos M z i j)

lemma aux_sre15_ftilde_nonneg {S A : Type*} [Fintype S] (M : MRP S A) (z : A) (i j : S)
    (s : ℝ) : 0 ≤ ftilde M z i j s := by
  unfold ftilde
  exact integral_nonneg (fun t => (Real.exp_pos _).le)

lemma aux_sre15_ftilde_lt_one {S A : Type*} [Fintype S] (M : MRP S A) (z : A) (i j : S)
    {α : ℝ} (hα : 0 < α) : ftilde M z i j α < 1 := by
  have := M.F_prob z i j
  have hr := aux_sre15_restrict_eq M z i j
  have hae := aux_sre15_ae_pos M z i j
  unfold ftilde
  rw [hr]
  have hint : Integrable (fun t : ℝ => Real.exp (-(α * t))) (M.F z i j) := by
    refine Integrable.of_bound (by fun_prop) 1 ?_
    filter_upwards [hae] with t ht
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    have : 0 < α * t := mul_pos hα ht
    linarith
  have hpos : 0 < ∫ t, (1 - Real.exp (-(α * t))) ∂(M.F z i j) := by
    rw [integral_pos_iff_support_of_nonneg_ae]
    · have hsub : Set.Ioi (0 : ℝ) ⊆
          Function.support (fun t : ℝ => 1 - Real.exp (-(α * t))) := by
        intro t ht
        simp only [Function.mem_support]
        have : Real.exp (-(α * t)) < 1 := by
          rw [Real.exp_lt_one_iff]
          have := mul_pos hα ht
          linarith
        linarith
      have h1 : M.F z i j (Set.Ioi 0) = 1 := by
        rw [← Measure.restrict_apply_univ, hr, measure_univ]
      exact lt_of_lt_of_le (by rw [h1]; exact one_pos) (measure_mono hsub)
    · filter_upwards [hae] with t ht
      simp only [Pi.zero_apply, sub_nonneg]
      apply Real.exp_le_one_iff.mpr
      have : 0 < α * t := mul_pos hα ht
      linarith
    · exact (integrable_const 1).sub hint
  rw [integral_sub (integrable_const 1) hint] at hpos
  simp at hpos
  linarith

noncomputable def aux_sre15_T {S A : Type*} [Fintype S] (M : MRP S A) (α : ℝ) (d : S → A)
    (v : S → ℝ) : S → ℝ :=
  fun i => test M α (d i) i v

lemma aux_sre15_iter {S A : Type*} [Fintype S] (M : MRP S A) (α : ℝ) (d : S → A)
    (V0 : S → ℝ) (n : ℕ) :
    policyReturn M α (fun _ => d) V0 n = (aux_sre15_T M α d)^[n] V0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ← ih]
    rfl

lemma aux_sre15_contracting {S A : Type*} [Fintype S] (M : MRP S A) {α : ℝ} (hα : 0 < α)
    (d : S → A) :
    ∃ K : NNReal, ContractingWith K (aux_sre15_T M α d) := by
  classical
  let K : NNReal :=
    Finset.univ.sup (fun ij : S × S => (ftilde M (d ij.1) ij.1 ij.2 α).toNNReal)
  have hK1 : K < 1 := by
    rw [Finset.sup_lt_iff (by simp)]
    intro ij _
    exact Real.toNNReal_lt_one.mpr (aux_sre15_ftilde_lt_one M _ _ _ hα)
  have hK : ∀ i j, ftilde M (d i) i j α ≤ (K : ℝ) := by
    intro i j
    refine le_trans (Real.le_coe_toNNReal _) ?_
    have : (ftilde M (d (i, j).1) (i, j).1 (i, j).2 α).toNNReal ≤ K :=
      Finset.le_sup (f := fun ij : S × S => (ftilde M (d ij.1) ij.1 ij.2 α).toNNReal)
        (Finset.mem_univ (i, j))
    exact_mod_cast this
  have key : ∀ u v : S → ℝ, ∀ i,
      |aux_sre15_T M α d u i - aux_sre15_T M α d v i| ≤ K * dist u v := by
    intro u v i
    have e : aux_sre15_T M α d u i - aux_sre15_T M α d v i =
        ∑ j, qtilde M α (d i) i j * (u j - v j) := by
      simp only [aux_sre15_T, test, mul_sub, Finset.sum_sub_distrib]
      ring
    rw [e]
    calc |∑ j, qtilde M α (d i) i j * (u j - v j)|
        ≤ ∑ j, |qtilde M α (d i) i j * (u j - v j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, M.p (d i) i j * (K * dist u v) := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul, qtilde,
          abs_of_nonneg (mul_nonneg (M.p_nonneg _ _ _) (aux_sre15_ftilde_nonneg M _ _ _ _)),
          mul_assoc]
        apply mul_le_mul_of_nonneg_left _ (M.p_nonneg _ _ _)
        apply mul_le_mul (hK i j) _ (abs_nonneg _) K.coe_nonneg
        rw [← Real.dist_eq]
        exact dist_le_pi_dist u v j
      _ = K * dist u v := by rw [← Finset.sum_mul, M.p_sum, one_mul]
  refine ⟨K, hK1, LipschitzWith.of_dist_le_mul fun u v => ?_⟩
  refine (dist_pi_le_iff (by positivity)).2 fun i => ?_
  rw [Real.dist_eq]
  exact key u v i

end JewellMRP.Discounted

open JewellMRP.Discounted

theorem solution {S A : Type*} [Fintype S] (M : MRP S A) {α : ℝ}
    (hα : 0 < α) (d : S → A) (V0 : S → ℝ) :
    ∃ v : S → ℝ, SolvesEval M α d v ∧
      Tendsto (fun n => policyReturn M α (fun _ => d) V0 n) atTop (𝓝 v) := by
  obtain ⟨K, hc⟩ := aux_sre15_contracting M hα d
  refine ⟨ContractingWith.fixedPoint _ hc, ?_, ?_⟩
  · intro i
    have hfix := hc.fixedPoint_isFixedPt
    exact (congrFun hfix i).symm
  · have : (fun n => policyReturn M α (fun _ => d) V0 n) =
        fun n => (aux_sre15_T M α d)^[n] V0 := funext (aux_sre15_iter M α d V0)
    rw [this]
    exact hc.tendsto_iterate_fixedPoint V0
