-- Prove2me | solution 1 for GlobalTheory.exists_entire_dirichlet_of_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:18:11.2142+00:00
-- url     : https://prove2.me/submissions/ff75a426-f6bf-467f-9616-311002bf73c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LatticeThetaAsymptoticsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LatticeEpsteinZetaContinuation
import Theorems.Thm_GlobalTheory_summable_exp_neg_pi_mul_of_summable_rpow
import Theorems.Thm_GlobalTheory_continuousOn_tsum_exp_neg_pi_mul
import Theorems.Thm_GlobalTheory_isBigO_exp_neg_div_rpow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Asymptotics
open GlobalTheory
open Set MeasureTheory
open scoped Topology
namespace GlobalTheory
theorem _root_.solution {ι : Type*} [Countable ι] {q : ι → ℝ}
    (hq : ∀ i, 0 < q i) (hs : ∀ σ : ℝ, 1 < σ → Summable fun i => q i ^ (-σ)) {V c : ℝ}
    (hc : 0 < c)
    (htop : (fun t : ℝ => ∑' i, Real.exp (-Real.pi * t * q i)) =O[atTop]
      (fun t => Real.exp (-c * t)))
    (hbot : (fun t : ℝ => (∑' i, Real.exp (-Real.pi * t * q i)) - 1 / (t * V)) =O[𝓝[>] 0]
      (fun t => Real.exp (-c / t))) :
    ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧ Z 1 = (Real.pi / V : ℝ) ∧ Z (-1) = 0 ∧
      ∀ s : ℂ, 1 < s.re → Summable (fun i => ((q i : ℝ) : ℂ) ^ (-s)) ∧
        Z s = (s - 1) * ∑' i, ((q i : ℝ) : ℂ) ^ (-s) := by
  set θ : ℝ → ℝ := fun t => ∑' i, Real.exp (-Real.pi * t * q i) with hθ
  have hθc : ContinuousOn θ (Ioi 0) := continuousOn_tsum_exp_neg_pi_mul hq (hs 2 one_lt_two)
  let g : ℝ → ℂ := indicator (Ioc 0 1) (fun t => (t : ℂ) ^ (-1 : ℂ))
  let A : ℂ := (V : ℂ)⁻¹
  let f : ℝ → ℂ := fun t => (θ t : ℂ) - A • g t
  have hfc : LocallyIntegrableOn f (Ioi 0) := by
    refine LocallyIntegrableOn.sub
      ((continuous_ofReal.comp_continuousOn hθc).locallyIntegrableOn measurableSet_Ioi)
      (LocallyIntegrableOn.smul ?_ A)
    have h0 : LocallyIntegrableOn (fun t : ℝ => (t : ℂ) ^ (-1 : ℂ)) (Ioi 0) :=
      ContinuousOn.locallyIntegrableOn (continuousOn_of_forall_continuousAt fun t ht =>
        continuousAt_ofReal_cpow_const _ _ (Or.inr <| ne_of_gt ht)) measurableSet_Ioi
    intro x hx
    obtain ⟨u, hu, hu'⟩ := h0 x hx
    exact ⟨u, hu, hu'.indicator measurableSet_Ioc⟩
  have hftop : f =O[atTop] fun t => Real.exp (-c * t) := by
    refine (isBigO_ofReal_left.mpr htop).congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop 1] with t ht
    simp [f, g, indicator_of_notMem (fun h : t ∈ Ioc (0:ℝ) 1 => h.2.not_gt ht)]
  have hfbot : ∀ b : ℝ, f =O[𝓝[>] 0] fun t => t ^ (-b) := by
    intro b
    refine ((isBigO_ofReal_left.mpr hbot).congr' ?_ EventuallyEq.rfl).trans
      (isBigO_exp_neg_div_rpow hc b)
    filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
    simp only [f, g, A, indicator_of_mem ht, cpow_neg_one, smul_eq_mul, θ]
    push_cast
    ring
  have hdiff : Differentiable ℂ (mellin f) := fun s =>
    mellin_differentiableAt_of_isBigO_rpow_exp hc hfc hftop (hfbot (s.re - 1)) (sub_one_lt _)
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  refine ⟨fun s => (Real.pi : ℂ) ^ s * (Gamma s)⁻¹ * ((s - 1) * mellin f s + A), ?_, ?_, ?_, ?_⟩
  · refine (Differentiable.mul (differentiable_id.const_cpow (Or.inl hpi))
      differentiable_one_div_Gamma).mul ?_
    exact ((differentiable_id.sub_const 1).mul hdiff).add_const A
  · simp [A, div_eq_mul_inv]
  · have : Gamma (-1) = 0 := by simpa using Gamma_neg_nat_eq_zero 1
    simp [this]
  · intro s hs1
    have hs0 : 0 < s.re := by linarith
    have hsum : HasSum (fun i => (Real.pi : ℂ) ^ (-s) * Gamma s * (1 : ℂ) / (q i : ℂ) ^ s)
        (mellin (fun t => (θ t : ℂ)) s) := by
      refine hasSum_mellin_pi_mul (a := fun _ => 1) (fun i => Or.inr (hq i)) hs0
        (fun t ht => ?_) ?_
      · have := (summable_exp_neg_pi_mul_of_summable_rpow hq (hs 2 one_lt_two) ht).hasSum
        rw [← hasSum_ofReal] at this
        convert this using 3 with i
        rw [one_mul]; congr 2; ring
      · refine (hs s.re hs1).congr fun i => ?_
        rw [Real.rpow_neg (hq i).le, norm_one, one_div]
    have hg := hasMellin_cpow_Ioc (-1) (s := s) (by simp; linarith)
    have hgA := hasMellin_const_smul hg.1 A
    have hfm : MellinConvergent f s :=
      mellinConvergent_of_isBigO_rpow_exp hc hfc hftop (hfbot 0) hs0
    have hadd := (hasMellin_add hfm hgA.1).2
    have e1 : (fun t => f t + A • g t) = fun t => (θ t : ℂ) := by
      funext t; simp [f]
    rw [hgA.2, hg.2] at hadd
    have hadd' : mellin (fun t => (θ t : ℂ)) s = mellin f s + A • (1 / (s + -1)) := by
      rw [← e1]; exact hadd
    have hG : Gamma s ≠ 0 := Gamma_ne_zero_of_re_pos hs0
    have hp : (Real.pi : ℂ) ^ s ≠ 0 := by simp [cpow_eq_zero_iff]
    have hs1' : s - 1 ≠ 0 := by
      intro h0; rw [sub_eq_zero.mp h0] at hs1; simp at hs1
    have hsum2 : HasSum (fun i => ((q i : ℝ) : ℂ) ^ (-s))
        ((Real.pi : ℂ) ^ s * (Gamma s)⁻¹ * mellin (fun t => (θ t : ℂ)) s) := by
      refine HasSum.congr_fun (hsum.mul_left ((Real.pi : ℂ) ^ s * (Gamma s)⁻¹)) fun i => ?_
      rw [cpow_neg, cpow_neg]
      field_simp
    refine ⟨hsum2.summable, ?_⟩
    rw [hsum2.tsum_eq, hadd', ← sub_eq_add_neg, smul_eq_mul]
    field_simp
end GlobalTheory
