-- Prove2me | solution 1 for MultistageStab.Value.display_10
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T19:03:56.864696+00:00
-- url     : https://prove2.me/submissions/57b0d781-9869-4e1a-b91c-0c70a6ed0dad

import Mathlib
import Definitions.Def_MultistageStab_Value_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MultistageStab.Value.SolAux
open MultistageStab.Value

lemma Xc_add {D : Data} {t : ℕ} {x y : E (D.m t)} (hx : x ∈ Xc D t) (hy : y ∈ Xc D t) :
    x + y ∈ Xc D t := by
  intro i
  rw [inner_add_right]
  linarith [hx i, hy i]

lemma Xc_smul {D : Data} {t : ℕ} {x : E (D.m t)} (hx : x ∈ Xc D t) {c : ℝ} (hc : 0 ≤ c) :
    c • x ∈ Xc D t := by
  intro i
  rw [inner_smul_right]
  exact mul_nonpos_of_nonneg_of_nonpos hc (hx i)

lemma Xc_zero {D : Data} {t : ℕ} : (0 : E (D.m t)) ∈ Xc D t := by
  intro i; simp

lemma Xc_sum {D : Data} {t : ℕ} {ι : Type*} (s : Finset ι) (f : ι → E (D.m t))
    (hf : ∀ i ∈ s, f i ∈ Xc D t) : ∑ i ∈ s, f i ∈ Xc D t := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Xc_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact Xc_add (hf a (Finset.mem_insert_self _ _))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

lemma Xc_isClosed (D : Data) (t : ℕ) : IsClosed (Xc D t) := by
  have : Xc D t = ⋂ i, {x : E (D.m t) | inner ℝ (D.C t i) x ≤ 0} := by
    ext x; simp [Xc]
  rw [this]
  exact isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const

lemma Xc_convex (D : Data) (t : ℕ) : Convex ℝ (Xc D t) := by
  intro x hx y hy a c ha hc _
  exact Xc_add (Xc_smul hx ha) (Xc_smul hy hc)

lemma max_sub_max_neg (a : ℝ) : max a 0 - max (-a) 0 = a := by
  rcases le_total a 0 with h | h
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring

/-- A continuous, positively homogeneous right inverse of `A_{t,0}` with values in `X_t`. -/
lemma recourse_selector (D : Data) (hA1 : CompleteRecourse D) (t : ℕ)
    (ht : t ∈ Finset.Icc 2 D.T) :
    ∃ Z : E (D.n t) → E (D.m t), Continuous Z ∧ (∀ w, Z w ∈ Xc D t) ∧
      (∀ w, D.A₀ t (Z w) = w) ∧ ∃ C : NNReal, ∀ w, ‖Z w‖ ≤ C * ‖w‖ := by
  have hp : ∀ i : Fin (D.n t), ∃ z ∈ Xc D t, D.A₀ t z = EuclideanSpace.single i (1 : ℝ) :=
    fun i => hA1 t ht _
  have hm : ∀ i : Fin (D.n t), ∃ z ∈ Xc D t, D.A₀ t z = -EuclideanSpace.single i (1 : ℝ) :=
    fun i => hA1 t ht _
  choose zp hzp hAzp using hp
  choose zm hzm hAzm using hm
  refine ⟨fun w => ∑ i, (max (w i) 0 • zp i + max (-(w i)) 0 • zm i), ?_, ?_, ?_, ?_⟩
  · fun_prop
  · intro w
    exact Xc_sum _ _ fun i _ =>
      Xc_add (Xc_smul (hzp i) (le_max_right _ _)) (Xc_smul (hzm i) (le_max_right _ _))
  · intro w
    simp only [map_sum, map_add, map_smul, hAzp, hAzm, smul_neg]
    have : ∀ i : Fin (D.n t), max (w i) 0 • EuclideanSpace.single i (1 : ℝ) +
        -(max (-(w i)) 0 • EuclideanSpace.single i (1 : ℝ)) =
        w i • EuclideanSpace.single i (1 : ℝ) := by
      intro i
      rw [← sub_eq_add_neg, ← sub_smul, max_sub_max_neg]
    simp_rw [this]
    have := (EuclideanSpace.basisFun (Fin (D.n t)) ℝ).sum_repr w
    simpa using this
  · refine ⟨∑ i, (‖zp i‖₊ + ‖zm i‖₊), fun w => ?_⟩
    calc ‖∑ i, (max (w i) 0 • zp i + max (-(w i)) 0 • zm i)‖
        ≤ ∑ i, ‖max (w i) 0 • zp i + max (-(w i)) 0 • zm i‖ := norm_sum_le _ _
      _ ≤ ∑ i, ‖w‖ * (‖zp i‖ + ‖zm i‖) := by
          gcongr with i
          have hwi : |w i| ≤ ‖w‖ := by
            have := PiLp.norm_apply_le w i
            simpa [Real.norm_eq_abs] using this
          have h1 : max (w i) 0 ≤ ‖w‖ := max_le ((le_abs_self _).trans hwi) (norm_nonneg _)
          have h2 : max (-(w i)) 0 ≤ ‖w‖ :=
            max_le ((neg_le_abs _).trans hwi) (norm_nonneg _)
          calc _ ≤ ‖max (w i) 0 • zp i‖ + ‖max (-(w i)) 0 • zm i‖ := norm_add_le _ _
            _ = max (w i) 0 * ‖zp i‖ + max (-(w i)) 0 * ‖zm i‖ := by
                rw [norm_smul, norm_smul, Real.norm_of_nonneg (le_max_right _ _),
                  Real.norm_of_nonneg (le_max_right _ _)]
            _ ≤ ‖w‖ * ‖zp i‖ + ‖w‖ * ‖zm i‖ := by gcongr
            _ = _ := by ring
      _ = (↑(∑ i, (‖zp i‖₊ + ‖zm i‖₊)) : ℝ) * ‖w‖ := by
          rw [← Finset.mul_sum, mul_comm]; push_cast; rfl

end MultistageStab.Value.SolAux

open MultistageStab.Value MultistageStab.Value.SolAux in
theorem solution (D : MultistageStab.Value.Data) (hA1 : MultistageStab.Value.CompleteRecourse D) :
    ∀ t ∈ Finset.Icc 2 D.T, ∃ l : ℝ, 0 < l ∧
      ∀ ubar util : MultistageStab.Value.E (D.n t), ∀ x ∈ {x : MultistageStab.Value.E (D.m t) | x ∈ MultistageStab.Value.Xc D t ∧ D.A₀ t x = ubar},
        Metric.infDist x {x : MultistageStab.Value.E (D.m t) | x ∈ MultistageStab.Value.Xc D t ∧ D.A₀ t x = util} ≤ l * ‖ubar - util‖ := by
  intro t ht
  obtain ⟨Z, -, hZX, hZA, C, hC⟩ := recourse_selector D hA1 t ht
  refine ⟨C + 1, by positivity, fun ubar util x hx => ?_⟩
  have hy : x + Z (util - ubar) ∈ {x : E (D.m t) | x ∈ Xc D t ∧ D.A₀ t x = util} := by
    refine ⟨Xc_add hx.1 (hZX _), ?_⟩
    rw [map_add, hZA, hx.2]; abel
  calc Metric.infDist x _ ≤ dist x (x + Z (util - ubar)) := Metric.infDist_le_dist_of_mem hy
    _ = ‖Z (util - ubar)‖ := by rw [dist_eq_norm]; simp
    _ ≤ C * ‖util - ubar‖ := hC _
    _ ≤ (C + 1) * ‖ubar - util‖ := by
        rw [norm_sub_rev]; gcongr; linarith
