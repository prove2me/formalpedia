-- Prove2me | solution 1 for GlobalTheory.FinWeil.intertwiner_fixes_of_local_vacuum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:07:50.736172+00:00
-- url     : https://prove2.me/submissions/4a8fb7b1-4e66-4567-9065-bf89a4570a23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntertwinerFixesOfLocalVacuum
import Theorems.Thm_GlobalTheory_FinWeil_IsHeis_comm
import Theorems.Thm_GlobalTheory_FinWeil_IsHeis_ne_zero
import Theorems.Thm_GlobalTheory_FinWeil_IsHeis_swap_eq_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical GlobalTheory.FinWeil
open scoped BigOperators
open GlobalTheory GlobalTheory.FinWeil
namespace GlobalTheory.FinWeil
theorem _root_.solution {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
    {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} (h : IsHeis σ w γ W) (A : Submodule R X) (hA : SelfDual γ A)
    (hspan : Submodule.span ℂ {m : M | ∃ x e, Fixes W A e ∧ m = W x e} = ⊤) (φ : X →ₗ[R] X) (T : M →ₗ[ℂ] M)
    (hT : ∀ x v, T (W x v) = W (φ x) (T v)) (hTe : ∀ e, Fixes W A e → T e = e) (P : X →ₗ[R] X)
    (hP : ∀ x y, γ (P x) y = γ x (P y)) (hPA : ∀ a ∈ A, P a ∈ A) (hφ : ∀ x, φ (x - P x) = x - P x)
    (m : M) (hm : ∀ a ∈ A, W (P a) m = m) : T m = m := by
  have hsm : ∀ (c : ℂ) e, Fixes W A e → Fixes W A (c • e) := fun c e he a ha => by rw [map_smul, he a ha]
  have key : ∀ {ι : Type} (x : ι → X) (s : Finset ι) (e : ι → M), (∀ i, Fixes W A (e i)) →
      (∀ a ∈ A, W (P a) (∑ i ∈ s, W (x i) (e i)) = ∑ i ∈ s, W (x i) (e i)) →
      T (∑ i ∈ s, W (x i) (e i)) = ∑ i ∈ s, W (x i) (e i) := by
    intro ι x s
    induction s using Finset.strongInduction with
    | H s ih =>
      intro e he hfix
      by_cases hall : ∀ i ∈ s, P (x i) ∈ A
      · rw [map_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        have h1 := h.comp (x i - P (x i)) (P (x i)) (e i)
        rw [he i _ (hall i hi), sub_add_cancel] at h1
        have h2 : T (W (x i - P (x i)) (e i)) = W (x i - P (x i)) (e i) := by rw [hT, hφ, hTe _ (he i)]
        rw [h1, map_smul] at h2
        exact smul_right_injective M (h.ne_zero _ _) h2
      · push Not at hall
        obtain ⟨j, hj, hjA⟩ := hall
        rw [hA] at hjA
        push Not at hjA
        obtain ⟨a, ha, hz⟩ := hjA
        have hz' : γ (P a) (x j) ≠ 1 := by
          intro h0
          rw [hP] at h0
          exact hz (h.swap_eq_one h0)
        set z := γ (P a) (x j) with hzdef
        have hact : ∀ i, W (P a) (W (x i) (e i)) = γ (P a) (x i) • W (x i) (e i) := fun i => by
          rw [h.comm, he i _ (hPA a ha)]
        have hsum : (1 - z) • ∑ i ∈ s, W (x i) (e i) = ∑ i ∈ s.erase j, W (x i) ((γ (P a) (x i) - z) • e i) := by
          rw [Finset.sum_erase s (by simp [hzdef]), sub_smul, one_smul]
          have h4 : ∑ i ∈ s, W (x i) (e i) = ∑ i ∈ s, γ (P a) (x i) • W (x i) (e i) := by
            rw [← hfix a ha, map_sum]
            exact Finset.sum_congr rfl fun i _ => hact i
          calc _ = ∑ i ∈ s, γ (P a) (x i) • W (x i) (e i) - ∑ i ∈ s, z • W (x i) (e i) := by
                rw [← h4, Finset.smul_sum]
            _ = _ := by
                rw [← Finset.sum_sub_distrib]
                exact Finset.sum_congr rfl fun i _ => by rw [map_smul, sub_smul]
        have h3 := ih (s.erase j) (Finset.erase_ssubset hj) (fun i => (γ (P a) (x i) - z) • e i)
          (fun i => hsm _ _ (he i)) (fun b hb => by rw [← hsum, map_smul, hfix b hb])
        rw [← hsum, map_smul] at h3
        exact smul_right_injective M (sub_ne_zero.2 hz'.symm) h3
  have hmem : m ∈ Submodule.span ℂ {m : M | ∃ x e, Fixes W A e ∧ m = W x e} := by rw [hspan]; trivial
  obtain ⟨n, c, g, hg⟩ := Submodule.mem_span_set'.1 hmem
  choose x e he hge using fun i => (g i).2
  have hm' : m = ∑ i, W (x i) (c i • e i) := by
    rw [← hg]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, hge i]
  rw [hm'] at hm ⊢
  exact key x Finset.univ _ (fun i => hsm _ _ (he i)) hm
end GlobalTheory.FinWeil
