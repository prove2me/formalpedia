-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DiracComb.eq_mul_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:37:38.491935+00:00
-- url     : https://prove2.me/submissions/4a69c02a-3aa8-4d0c-9507-3942521e5238

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_DenseHasCompactSupport
import Theorems.Thm_GlobalTheory_CompanionTheory_DiracComb_exists_comb
import Theorems.Thm_GlobalTheory_CompanionTheory_DiracComb_exists_partition
import Theorems.Thm_GlobalTheory_CompanionTheory_DiracComb_dense_hasCompactSupport
import Theorems.Thm_GlobalTheory_CompanionTheory_DiracComb_exists_div

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open scoped Real ContDiff
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DiracComb
namespace GlobalTheory.CompanionTheory.DiracComb
theorem _root_.solution : ∀ (n : ℕ) (T : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ), (∀ (i : Fin n) (f g : SchwartzMap (Fin n → ℝ) ℂ), (∀ x, g x = cexp (2 * π * I * x i) * f x) → T g = T f) → (∀ (m : Fin n → ℤ) (f g : SchwartzMap (Fin n → ℝ) ℂ), (∀ x, g x = f (x + fun i => (m i : ℝ))) → T g = T f) → ∃ a : ℂ, ∀ f : SchwartzMap (Fin n → ℝ) ℂ, T f = a * ∑' m : Fin n → ℤ, f (fun i => (m i : ℝ)) := by
  intro n T hχ hτ
  obtain ⟨S, hS⟩ := exists_comb n
  have hA : ∀ f : SchwartzMap (Fin n → ℝ) ℂ, tsupport (f : (Fin n → ℝ) → ℂ) ⊆ Metric.ball 0 1 →
      f 0 = 0 → T f = 0 := by
    intro f hf h0
    obtain ⟨g, hg, hg'⟩ := exists_div n f hf h0
    have hsm : ∀ i, ContDiff ℝ ∞ (fun x : Fin n → ℝ => cexp (2 * π * I * x i) * g i x) := by
      intro i
      refine ContDiff.mul ?_ ((g i).smooth ⊤)
      exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ i))).cexp
    have hcs : ∀ i, HasCompactSupport (fun x : Fin n → ℝ => cexp (2 * π * I * x i) * g i x) :=
      fun i => (hg i).mul_left
    have e : f = ∑ i, ((hcs i).toSchwartzMap (hsm i) - g i) := by
      ext x
      rw [hg' x, sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      show _ = cexp (2 * π * I * x i) * g i x - g i x
      ring
    rw [e, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_sub, hχ i (g i) _ (fun x => rfl), sub_self]
  let b : ContDiffBump (0 : Fin n → ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  have h₁ : HasCompactSupport (Complex.ofRealCLM ∘ (b : (Fin n → ℝ) → ℝ)) :=
    b.hasCompactSupport.comp_left rfl
  let ψ : SchwartzMap (Fin n → ℝ) ℂ :=
    h₁.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)
  have hψ : ∀ x, ψ x = (b x : ℂ) := fun x => rfl
  have hψ0 : ψ 0 = 1 := by
    rw [hψ, b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)]; simp
  have hψs : tsupport (ψ : (Fin n → ℝ) → ℂ) ⊆ Metric.ball 0 1 := by
    refine (closure_mono ?_).trans (b.tsupport_eq.subset.trans
      (Metric.closedBall_subset_ball (by show (1 / 2 : ℝ) < 1; norm_num)))
    intro x hx h
    exact hx (by rw [hψ, h]; simp)
  have hB : ∀ f : SchwartzMap (Fin n → ℝ) ℂ, tsupport (f : (Fin n → ℝ) → ℂ) ⊆ Metric.ball 0 1 →
      T f = T ψ * f 0 := by
    intro f hf
    have := hA (f - f 0 • ψ) ?_ ?_
    · rw [map_sub, map_smul, sub_eq_zero, smul_eq_mul] at this
      rw [this, mul_comm]
    · have hsub : Function.support (⇑(f - f 0 • ψ)) ⊆
          tsupport (f : (Fin n → ℝ) → ℂ) ∪ tsupport (ψ : (Fin n → ℝ) → ℂ) := by
        intro x hx
        by_contra hc
        rw [Set.mem_union, not_or] at hc
        apply hx
        show f x - f 0 • ψ x = 0
        rw [image_eq_zero_of_notMem_tsupport hc.1, image_eq_zero_of_notMem_tsupport hc.2]
        simp
      exact (closure_minimal hsub ((isClosed_tsupport _).union (isClosed_tsupport _))).trans
        (Set.union_subset hf hψs)
    · show f 0 - f 0 • ψ 0 = 0
      rw [hψ0]; simp
  have hC : ∀ (m : Fin n → ℤ) (f : SchwartzMap (Fin n → ℝ) ℂ),
      tsupport (f : (Fin n → ℝ) → ℂ) ⊆ Metric.ball (fun i => (m i : ℝ)) 1 → T f = T ψ * S f := by
    intro m f hf
    set c : Fin n → ℝ := fun i => (m i : ℝ) with hc
    let g := SchwartzMap.compSubConstCLM ℂ (-c) f
    have hg : ∀ x, g x = f (x + c) := fun x => by
      simp only [g, SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add]
    have hgs : tsupport (g : (Fin n → ℝ) → ℂ) ⊆ Metric.ball 0 1 := by
      have hsub : Function.support (g : (Fin n → ℝ) → ℂ) ⊆
          (fun x => x + c) ⁻¹' tsupport (f : (Fin n → ℝ) → ℂ) := by
        intro x hx
        exact subset_tsupport _ (by rwa [Function.mem_support, hg] at hx)
      refine (closure_minimal hsub ((isClosed_tsupport _).preimage (by fun_prop))).trans ?_
      intro x hx
      have := hf hx
      simpa [Metric.mem_ball, dist_eq_norm] using this
    rw [← hτ m f g hg, hB g hgs, hg, zero_add, hS, tsum_eq_single m]
    intro k hk
    refine image_eq_zero_of_notMem_tsupport fun h => hk ?_
    have h1 := hf h
    funext i
    have h2 := (dist_le_pi_dist (fun i => (k i : ℝ)) c i).trans_lt h1
    rw [Real.dist_eq] at h2
    have h3 : |k i - m i| < 1 := by
      simp only [hc] at h2
      exact_mod_cast h2
    exact sub_eq_zero.1 (Int.abs_lt_one_iff.1 h3)
  refine ⟨T ψ, fun f => ?_⟩
  rw [← hS]
  have hcl : IsClosed {f : SchwartzMap (Fin n → ℝ) ℂ | T f = T ψ * S f} :=
    isClosed_eq T.continuous (continuous_const.mul S.continuous)
  refine closure_minimal (t := {f : SchwartzMap (Fin n → ℝ) ℂ | T f = T ψ * S f}) ?_ hcl (dense_hasCompactSupport n f)
  intro f hf
  obtain ⟨s, g, hg, rfl⟩ := exists_partition n f hf
  show T _ = T ψ * S _
  rw [map_sum, map_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => hC m (g m) (hg m)
end GlobalTheory.CompanionTheory.DiracComb
