-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.integral_expRevenue_mul_next_event_indicator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T06:56:28.144049+00:00
-- url     : https://prove2.me/submissions/85d16884-7e63-4137-9734-dc34a64bb0a5

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_revenue_abs_bound
import Theorems.Thm_revenue_joint_measurable
import Theorems.Thm_NestedSeatAlloc_IntPolicy_revenue_extensional_on_prefix
import Definitions.Def_extendFinitePrefix

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ) (hM : IsSeatModel P X f)
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (hp : ∀ i, 0 ≤ p i)
    (E : Set ℝ) (hE : MeasurableSet E) :
    ∫ ω, revenue f p (fun i => X i ω) k t *
        (if X (k + 1) ω ∈ E then (1 : ℝ) else 0) ∂P =
      expRevenue P X f p k t * P.real (X (k + 1) ⁻¹' E) := by
  let S : Finset ℕ := Finset.Icc 1 k
  let T : Finset ℕ := {k + 1}
  let U : Ω → S → ℝ := fun ω j => X j.1 ω
  let F : (S → ℝ) → ℝ := fun z =>
    revenue f p (extendFinitePrefix S z) k t
  let G : (T → ℝ) → ℝ := fun z =>
    if z ⟨k + 1, by simp [T]⟩ ∈ E then 1 else 0
  let FU : Ω → ℝ := fun ω => F (U ω)
  let I : Ω → ℝ := fun ω =>
    if X (k + 1) ω ∈ E then 1 else 0
  have hST : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro i hi hmem
    have hik : i ≤ k := (Finset.mem_Icc.mp (by simpa [S] using hi)).2
    have hnext : i = k + 1 := by simpa [T] using hmem
    omega
  have htuple : IndepFun U (fun ω (j : T) => X j.1 ω) P :=
    iIndepFun.indepFun_finset S T hST hM.indep hM.meas
  have hseq : Measurable (fun z : S → ℝ => extendFinitePrefix S z) := by
    apply measurable_pi_iff.mpr
    intro i
    by_cases hi : i ∈ S
    · simp only [extendFinitePrefix, dif_pos hi]
      exact measurable_pi_apply (⟨i, hi⟩ : S)
    · simp [extendFinitePrefix, hi]
  have hF : Measurable F := by
    exact (revenue_joint_measurable f p k).comp
      (Measurable.prodMk hseq measurable_const)
  have hU : Measurable U := by
    have hcoords : ∀ j : {i : ℕ // i ∈ S}, Measurable (fun ω => U ω j) := by
      intro j
      exact hM.meas j.val
    exact measurable_pi_iff.mpr hcoords
  have hFU : Measurable FU := hF.comp hU
  let jnext : T := ⟨k + 1, by simp [T]⟩
  have hG : Measurable G := by
    have hEval : Measurable (fun z : T → ℝ => z jnext) :=
      measurable_pi_apply jnext
    have hPre : MeasurableSet {z : T → ℝ | z jnext ∈ E} :=
      hE.preimage hEval
    have hEq : G = ({z : T → ℝ | z jnext ∈ E}).indicator
        (fun _ => (1 : ℝ)) := by
      funext z
      by_cases hz : z jnext ∈ E <;>
        simp [G, jnext, hz, Set.indicator_apply]
    rw [hEq]
    exact measurable_const.indicator hPre
  have hI : Measurable I := by
    have hEq : I = (X (k + 1) ⁻¹' E).indicator (fun _ => (1 : ℝ)) := by
      funext ω
      by_cases hω : X (k + 1) ω ∈ E <;>
        simp [I, hω, Set.indicator_apply]
    rw [hEq]
    exact measurable_const.indicator (hM.meas (k + 1) hE)
  have hEqI : (fun ω => G (fun (j : T) => X j.1 ω)) = I := by
    funext ω
    simp [G, I, T, jnext]
  have hind : IndepFun FU I P := by
    rw [← hEqI]
    exact htuple.comp hF hG
  have hprefix_nonneg : ∀ i ω, 0 ≤ extendFinitePrefix S (U ω) i := by
    intro i ω
    by_cases hi : i ∈ S
    · simpa [extendFinitePrefix, U, hi] using hM.nonneg i ω
    · simp [extendFinitePrefix, hi]
  let Mfare : ℝ := ∑ j ∈ S, |f j|
  have hMfare : 0 ≤ Mfare := by
    dsimp [Mfare]
    exact Finset.sum_nonneg fun j hj => abs_nonneg (f j)
  have hfare : ∀ j, 1 ≤ j → j ≤ k → |f j| ≤ Mfare := by
    intro j hj hjk
    have hjS : j ∈ S := by simp [S, Finset.mem_Icc, hj, hjk]
    change |f j| ≤ ∑ i ∈ S, |f i|
    exact Finset.single_le_sum (fun i hi => abs_nonneg (f i)) hjS
  have hC : 0 ≤ (k : ℝ) * Mfare * t := by positivity
  have hbound : ∀ ω, |FU ω| ≤ (k : ℝ) * Mfare * t := by
    intro ω
    have hb := revenue_abs_bound f p
      (fun i => extendFinitePrefix S (U ω) i) Mfare hMfare
      (fun i hi => hp i) (hprefix_nonneg · ω) k t ht hfare
    simpa [FU, F, U, Mfare] using hb
  letI : IsProbabilityMeasure P := hM.isProb
  have hmajorant : Integrable (fun _ : Ω => (k : ℝ) * Mfare * t) P :=
    integrable_const _
  have hdom : ∀ᵐ ω ∂P, ‖FU ω‖ ≤ (k : ℝ) * Mfare * t := by
    filter_upwards [] with ω
    simpa [Real.norm_eq_abs] using hbound ω
  have hFUint : Integrable FU P :=
    hmajorant.mono' hFU.aestronglyMeasurable hdom
  have hindFactor := hind.integral_fun_mul_eq_mul_integral
    hFU.aestronglyMeasurable hI.aestronglyMeasurable
  have hIeq : I = (X (k + 1) ⁻¹' E).indicator (fun _ => (1 : ℝ)) := by
    funext ω
    by_cases hω : X (k + 1) ω ∈ E <;>
      simp [I, Set.indicator_apply, hω]
  have hIint : ∫ ω, I ω ∂P = P.real (X (k + 1) ⁻¹' E) := by
    rw [hIeq]
    calc
      ∫ ω, (X (k + 1) ⁻¹' E).indicator (fun _ => (1 : ℝ)) ω ∂P =
          P.real (X (k + 1) ⁻¹' E) • (1 : ℝ) := by
            simpa using (integral_indicator_const (μ := P) (e := (1 : ℝ))
              (hM.meas (k + 1) hE))
      _ = P.real (X (k + 1) ⁻¹' E) := by simp
  have hprefix : ∫ ω, FU ω ∂P = expRevenue P X f p k t := by
    rw [expRevenue]
    apply integral_congr_ae
    filter_upwards [] with ω
    exact revenue_extensional_on_prefix f p
      (extendFinitePrefix S (U ω)) (fun i => X i ω) k
      (by intro i hi; simp [extendFinitePrefix, S, U, hi]) t
  have hrealized (ω : Ω) :
      FU ω = revenue f p (fun i => X i ω) k t := by
    exact revenue_extensional_on_prefix f p
      (extendFinitePrefix S (U ω)) (fun i => X i ω) k
      (by intro i hi; simp [extendFinitePrefix, S, U, hi]) t
  calc
    ∫ ω, revenue f p (fun i => X i ω) k t * I ω ∂P =
        ∫ ω, FU ω * I ω ∂P := by
          apply integral_congr_ae
          filter_upwards [] with ω
          rw [hrealized ω]
    _ = (∫ ω, FU ω ∂P) * P.real (X (k + 1) ⁻¹' E) := by
          rw [hindFactor, hIint]
    _ = expRevenue P X f p k t * P.real (X (k + 1) ⁻¹' E) := by
          rw [hprefix]
