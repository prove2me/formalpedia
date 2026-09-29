-- Prove2me | solution 1 for JewellMRP.Discounted.optValue_tendsto_eq14
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:08:17.558589+00:00
-- url     : https://prove2.me/submissions/80bdc59d-6f20-4fec-ab97-ba3cb6e45b34

import Mathlib
import Definitions.Def_JewellMRP_Discounted_MRP
import Definitions.Def_JewellMRP_Discounted_PolicyIteration

open Filter Topology

namespace JewellMRP.Discounted

open MeasureTheory

lemma aux_oe14_ftilde_nonneg {S A : Type*} [Fintype S] (M : MRP S A) (z : A) (i j : S)
    (s : ℝ) : 0 ≤ ftilde M z i j s := by
  unfold ftilde
  exact setIntegral_nonneg measurableSet_Ioi (fun t _ => (Real.exp_pos _).le)

lemma aux_oe14_ftilde_lt_one {S A : Type*} [Fintype S] (M : MRP S A) (z : A) (i j : S)
    {α : ℝ} (hα : 0 < α) : ftilde M z i j α < 1 := by
  have := M.F_prob z i j
  set μ := M.F z i j with hμ
  have hIoi : μ (Set.Ioi 0) = 1 := by
    have h1 : μ (Set.Iic 0) + μ (Set.Ioi 0) = 1 := by
      rw [← measure_union (Set.disjoint_left.2 fun x hx hx' => by
          simp only [Set.mem_Iic, Set.mem_Ioi] at hx hx'; linarith) measurableSet_Ioi,
        Set.Iic_union_Ioi, measure_univ]
    rw [hμ, M.F_Iic_zero, zero_add] at h1
    exact h1
  have hint1 : IntegrableOn (fun t : ℝ => Real.exp (-(α * t))) (Set.Ioi 0) μ := by
    refine Integrable.of_bound (by fun_prop : Continuous fun t : ℝ => Real.exp (-(α * t))).aestronglyMeasurable 1 ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have ht' : (0:ℝ) < t := ht
    exact Real.exp_le_one_iff.2 (by nlinarith)
  have hint2 : IntegrableOn (fun _ : ℝ => (1:ℝ)) (Set.Ioi 0) μ := integrable_const _
  have hpos : 0 < ∫ t in Set.Ioi (0:ℝ), (1 - Real.exp (-(α * t))) ∂μ := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae]
    · have : Function.support (fun t : ℝ => 1 - Real.exp (-(α * t))) ∩ Set.Ioi 0
          = Set.Ioi 0 := by
        ext t
        simp only [Set.mem_inter_iff, Function.mem_support, Set.mem_Ioi, and_iff_right_iff_imp]
        intro ht
        have : Real.exp (-(α * t)) < 1 := Real.exp_lt_one_iff.2 (by nlinarith)
        linarith
      rw [this, hIoi]
      exact one_pos
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht' : (0:ℝ) < t := ht
      have : Real.exp (-(α * t)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
      simp only [Pi.zero_apply]
      linarith
    · exact hint2.sub hint1
  rw [integral_sub hint2 hint1, setIntegral_const] at hpos
  have hreal : μ.real (Set.Ioi 0) = 1 := by simp [Measure.real, hIoi]
  rw [hreal] at hpos
  unfold ftilde
  rw [← hμ]
  simp only [smul_eq_mul, mul_one] at hpos
  linarith

lemma aux_oe14_bound {S A : Type*} [Fintype S] [Fintype A] (M : MRP S A) {α : ℝ}
    (hα : 0 < α) : ∃ β : ℝ, 0 ≤ β ∧ β < 1 ∧ ∀ z i j, ftilde M z i j α ≤ β := by
  by_cases h : Nonempty (A × S × S)
  · obtain ⟨x0, hx0⟩ := Finite.exists_max (fun x : A × S × S => ftilde M x.1 x.2.1 x.2.2 α)
    exact ⟨_, aux_oe14_ftilde_nonneg M _ _ _ _, aux_oe14_ftilde_lt_one M _ _ _ hα,
      fun z i j => hx0 (z, i, j)⟩
  · exact ⟨0, le_rfl, one_pos, fun z i j => (h ⟨(z, i, j)⟩).elim⟩

lemma aux_oe14_lip {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] (M : MRP S A)
    {α β : ℝ} (hβ : ∀ z i j, ftilde M z i j α ≤ β) (v w : S → ℝ) (i : S) :
    maxTest M α v i ≤ maxTest M α w i + β * dist v w := by
  unfold maxTest
  apply Finset.sup'_le
  intro z _
  have key : test M α z i v ≤ test M α z i w + β * dist v w := by
    unfold test
    have : ∑ j, qtilde M α z i j * v j ≤ ∑ j, qtilde M α z i j * w j + β * dist v w := by
      calc ∑ j, qtilde M α z i j * v j
          = ∑ j, qtilde M α z i j * w j + ∑ j, qtilde M α z i j * (v j - w j) := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun j _ => ?_
            ring
        _ ≤ ∑ j, qtilde M α z i j * w j + ∑ j, M.p z i j * (β * dist v w) := by
            refine add_le_add le_rfl (Finset.sum_le_sum fun j _ => ?_)
            unfold qtilde
            have h1 : v j - w j ≤ dist v w :=
              (le_abs_self _).trans (by rw [← Real.dist_eq]; exact dist_le_pi_dist v w j)
            have hp := M.p_nonneg z i j
            have hf := aux_oe14_ftilde_nonneg M z i j α
            calc M.p z i j * ftilde M z i j α * (v j - w j)
                ≤ M.p z i j * ftilde M z i j α * dist v w :=
                  mul_le_mul_of_nonneg_left h1 (mul_nonneg hp hf)
              _ ≤ M.p z i j * (β * dist v w) := by
                  rw [mul_assoc]
                  exact mul_le_mul_of_nonneg_left
                    (mul_le_mul_of_nonneg_right (hβ z i j) dist_nonneg) hp
        _ = ∑ j, qtilde M α z i j * w j + β * dist v w := by
            rw [← Finset.sum_mul, M.p_sum, one_mul]
    linarith
  exact key.trans (add_le_add
    (Finset.le_sup' (fun z => test M α z i w) (Finset.mem_univ z)) le_rfl)

end JewellMRP.Discounted

open JewellMRP.Discounted

theorem solution {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
    (M : MRP S A) {α : ℝ} (hα : 0 < α) :
    ∃ v : S → ℝ, (∀ i, v i = maxTest M α v i) ∧
      ∀ V0 : S → ℝ, Tendsto (optValue M α V0) atTop (𝓝 v) := by
  obtain ⟨β, hβ0, hβ1, hβ⟩ := aux_oe14_bound M hα
  have hlip : LipschitzWith β.toNNReal (maxTest M α) := by
    refine LipschitzWith.of_dist_le_mul fun v w => ?_
    rw [Real.coe_toNNReal _ hβ0]
    refine (dist_pi_le_iff (mul_nonneg hβ0 dist_nonneg)).2 fun i => ?_
    rw [Real.dist_eq, abs_le]
    have h1 := aux_oe14_lip M hβ v w i
    have h2 := aux_oe14_lip M hβ w v i
    rw [dist_comm] at h2
    constructor <;> linarith
  have hK : ContractingWith β.toNNReal (maxTest M α) := by
    refine ⟨?_, hlip⟩
    exact Real.toNNReal_lt_one.2 hβ1
  refine ⟨ContractingWith.fixedPoint _ hK, fun i => ?_, fun V0 => ?_⟩
  · exact (congrFun hK.fixedPoint_isFixedPt i).symm
  · have heq : optValue M α V0 = fun n => (maxTest M α)^[n] V0 := by
      funext n
      induction n with
      | zero => rfl
      | succ n ih => rw [Function.iterate_succ_apply', ← ih]; rfl
    rw [heq]
    exact hK.tendsto_iterate_fixedPoint V0
