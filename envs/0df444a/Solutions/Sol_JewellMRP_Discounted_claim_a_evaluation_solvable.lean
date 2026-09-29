-- Prove2me | solution 1 for JewellMRP.Discounted.claim_a_evaluation_solvable
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:47:12.09991+00:00
-- url     : https://prove2.me/submissions/fdc92975-16fa-4790-8db0-1ac865704378

import Mathlib
import Definitions.Def_JewellMRP_Discounted_MRP
import Definitions.Def_JewellMRP_Discounted_PolicyIteration

open Filter Topology

namespace JewellMRP.Discounted

open MeasureTheory

lemma aux_ce_zero {S : Type*} [Fintype S] (Q : S → S → ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (hrow : ∀ i, ∑ j, Q i j < 1) (w : S → ℝ) (hw : ∀ i, w i = ∑ j, Q i j * w j) : w = 0 := by
  funext k
  have : Nonempty S := ⟨k⟩
  obtain ⟨i, hi⟩ := Finite.exists_max (fun i => |w i|)
  have h1 : |w i| ≤ (∑ j, Q i j) * |w i| := by
    calc |w i| = |∑ j, Q i j * w j| := by rw [← hw i]
      _ ≤ ∑ j, |Q i j * w j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, Q i j * |w j| := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [abs_mul, abs_of_nonneg (hQ i j)]
      _ ≤ ∑ j, Q i j * |w i| := by
          refine Finset.sum_le_sum (fun j _ => ?_)
          exact mul_le_mul_of_nonneg_left (hi j) (hQ i j)
      _ = (∑ j, Q i j) * |w i| := by rw [Finset.sum_mul]
  have h2 : |w i| ≤ 0 := by
    have := hrow i
    nlinarith [abs_nonneg (w i)]
  have h3 : |w k| ≤ 0 := le_trans (hi k) h2
  simpa using abs_nonpos_iff.mp h3

lemma aux_ce_ftilde_nonneg {S A : Type*} [Fintype S] (M : MRP S A) (z : A) (i j : S) (s : ℝ) :
    0 ≤ ftilde M z i j s := by
  unfold ftilde
  exact setIntegral_nonneg measurableSet_Ioi (fun t _ => (Real.exp_pos _).le)

lemma aux_ce_ftilde_lt_one {S A : Type*} [Fintype S] (M : MRP S A) (z : A) (i j : S) {s : ℝ}
    (hs : 0 < s) : ftilde M z i j s < 1 := by
  have := M.F_prob z i j
  have hIoi : M.F z i j (Set.Ioi 0) = 1 := by
    rw [← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, M.F_Iic_zero, tsub_zero]
  have hIoiR : (M.F z i j).real (Set.Ioi 0) = 1 := by
    rw [measureReal_def, hIoi, ENNReal.toReal_one]
  have hint1 : IntegrableOn (fun t : ℝ => Real.exp (-(s * t))) (Set.Ioi 0) (M.F z i j) := by
    refine Integrable.mono' (g := fun _ => (1 : ℝ)) (integrable_const _) ?_ ?_
    · exact (Continuous.aestronglyMeasurable (by fun_prop))
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall ?_)
      intro t ht
      have ht' : (0 : ℝ) < t := ht
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      rw [Real.exp_le_one_iff]
      nlinarith
  have hint2 : IntegrableOn (fun t : ℝ => 1 - Real.exp (-(s * t))) (Set.Ioi 0) (M.F z i j) :=
    (integrable_const _).sub hint1
  have hpos : 0 < ∫ t in Set.Ioi (0 : ℝ), (1 - Real.exp (-(s * t))) ∂(M.F z i j) := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae _ hint2]
    · have hsub : Set.Ioi (0 : ℝ) ⊆ Function.support (fun t : ℝ => 1 - Real.exp (-(s * t))) ∩
          Set.Ioi 0 := by
        intro t ht
        have ht' : (0 : ℝ) < t := ht
        refine ⟨?_, ht⟩
        rw [Function.mem_support]
        have : Real.exp (-(s * t)) < 1 := by
          have h := Real.exp_lt_exp.mpr (show -(s * t) < 0 by nlinarith)
          rwa [Real.exp_zero] at h
        linarith
      have := measure_mono (μ := M.F z i j) hsub
      rw [hIoi] at this
      exact lt_of_lt_of_le zero_lt_one this
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall ?_)
      intro t ht
      have ht' : (0 : ℝ) < t := ht
      have : Real.exp (-(s * t)) ≤ 1 := by
        rw [Real.exp_le_one_iff]; nlinarith
      simp only [Pi.zero_apply]
      linarith
  rw [integral_sub (integrable_const _) hint1, setIntegral_const, hIoiR] at hpos
  unfold ftilde
  simp only [smul_eq_mul, one_mul] at hpos
  linarith

lemma aux_ce_row {S A : Type*} [Fintype S] (M : MRP S A) {α : ℝ} (hα : 0 < α) (z : A) (i : S) :
    ∑ j, qtilde M α z i j < 1 := by
  unfold qtilde
  have hex : ∃ j, 0 < M.p z i j := by
    by_contra h
    push Not at h
    have : ∑ j, M.p z i j = 0 :=
      Finset.sum_eq_zero (fun j _ => le_antisymm (h j) (M.p_nonneg z i j))
    rw [M.p_sum] at this
    exact one_ne_zero this
  obtain ⟨j0, hj0⟩ := hex
  calc ∑ j, M.p z i j * ftilde M z i j α < ∑ j, M.p z i j := by
        apply Finset.sum_lt_sum
        · intro j _
          exact mul_le_of_le_one_right (M.p_nonneg z i j) (aux_ce_ftilde_lt_one M z i j hα).le
        · exact ⟨j0, Finset.mem_univ _, mul_lt_of_lt_one_right hj0 (aux_ce_ftilde_lt_one M z i j0 hα)⟩
    _ = 1 := M.p_sum z i

end JewellMRP.Discounted

open JewellMRP.Discounted
open Filter Topology

theorem solution {S A : Type*} [Fintype S] (M : MRP S A) {α : ℝ}
    (hα : 0 < α) (d : S → A) : ∃! v : S → ℝ, SolvesEval M α d v := by
  set Q : Matrix S S ℝ := fun i j => qtilde M α (d i) i j with hQdef
  have hQ : ∀ i j, 0 ≤ Q i j := fun i j =>
    mul_nonneg (M.p_nonneg _ _ _) (aux_ce_ftilde_nonneg M _ _ _ _)
  have hrow : ∀ i, ∑ j, Q i j < 1 := fun i => aux_ce_row M hα (d i) i
  set r : S → ℝ := fun i => rhoState M α (d i) i with hrdef
  have hsolve : ∀ v : S → ℝ, SolvesEval M α d v ↔ ∀ i, v i = r i + ∑ j, Q i j * v j := by
    intro v
    rfl
  let L : (S → ℝ) →ₗ[ℝ] (S → ℝ) := LinearMap.id - Matrix.mulVecLin Q
  have hL : ∀ v i, L v i = v i - ∑ j, Q i j * v j := by
    intro v i
    simp [L, Matrix.mulVec, dotProduct]
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    apply aux_ce_zero Q hQ hrow w
    intro i
    have := congrFun hw i
    rw [hL] at this
    simp only [Pi.zero_apply] at this
    linarith
  have hsurj : Function.Surjective L := LinearMap.injective_iff_surjective.mp hinj
  obtain ⟨v, hv⟩ := hsurj r
  refine ⟨v, ?_, ?_⟩
  · refine (hsolve v).mpr ?_
    intro i
    have := congrFun hv i
    rw [hL] at this
    linarith
  · intro u hu
    replace hu := (hsolve u).mp hu
    apply hinj
    funext i
    rw [hL, hv]
    have := hu i
    linarith
