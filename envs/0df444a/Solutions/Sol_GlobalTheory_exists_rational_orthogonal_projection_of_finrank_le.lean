-- Prove2me | solution 1 for GlobalTheory.exists_rational_orthogonal_projection_of_finrank_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:33:22.749326+00:00
-- url     : https://prove2.me/submissions/ec263ba3-54fd-46b3-a9a3-eea5c28f2bb1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRationalOrthogonalProjectionSemilinear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (K : Type) [Field K] (σ : K →+* ℂ) (W : Type)
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] (n : ℕ) (j : (Fin n → K) →ₛₗ[σ] W)
    (hj : ∀ x y, ⟪j x, j y⟫_ℂ ∈ Set.range σ) :
    ∀ (d : ℕ) (N : Submodule K (Fin n → K)), Module.finrank K N ≤ d → ∀ (x : Fin n → K),
      ∃ y ∈ N, ∀ m ∈ N, ⟪j m, j x - j y⟫_ℂ = 0 := by
  intro d
  induction d with
  | zero =>
    intro N hN x
    refine ⟨0, N.zero_mem, ?_⟩
    have hb : N = ⊥ := by
      rw [← Submodule.finrank_eq_zero]; omega
    intro m hm
    subst hb
    rw [Submodule.mem_bot] at hm
    subst hm
    simp
  | succ d ih =>
    intro N hN x
    by_cases h : ∃ v ∈ N, j v ≠ 0
    · obtain ⟨v, hvN, hv⟩ := h
      let f : (Fin n → K) →ₛₗ[σ] ℂ := (innerₛₗ ℂ (j v)).comp j
      have hf : ∀ z, f z = ⟪j v, j z⟫_ℂ := fun z => rfl
      let N' := N ⊓ LinearMap.ker f
      have hvv : ⟪j v, j v⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr hv
      have hlt : N' < N := by
        refine lt_of_le_of_ne inf_le_left ?_
        intro heq
        have hvN' : v ∈ N' := heq ▸ hvN
        have h2 : f v = 0 := hvN'.2
        rw [hf] at h2
        exact hvv h2
      have hN' : Module.finrank K N' ≤ d := by
        have := Submodule.finrank_lt_finrank_of_lt hlt
        omega
      obtain ⟨a, ha⟩ := hj v v
      obtain ⟨b, hb⟩ := hj v x
      have hsa : σ a ≠ 0 := by rw [ha]; exact hvv
      obtain ⟨y', hy'N, hy'⟩ := ih N' hN' (x - (b / a) • v)
      refine ⟨(b / a) • v + y', N.add_mem (N.smul_mem _ hvN) (inf_le_left (a := N) hy'N), ?_⟩
      have key : j x - j ((b / a) • v + y') = j (x - (b / a) • v) - j y' := by
        simp only [map_add, map_sub]; abel
      rw [key]
      have hy'k : ⟪j v, j y'⟫_ℂ = 0 := by
        have : f y' = 0 := hy'N.2
        rwa [hf] at this
      have hv0 : ⟪j v, j (x - (b / a) • v) - j y'⟫_ℂ = 0 := by
        rw [inner_sub_right, map_sub, inner_sub_right, hy'k, map_smulₛₗ, inner_smul_right, ← ha, ← hb,
          map_div₀, div_mul_cancel₀ _ hsa]
        ring
      intro m hm
      obtain ⟨e, he⟩ := hj v m
      have hm' : m - (e / a) • v ∈ N' := by
        refine ⟨N.sub_mem hm (N.smul_mem _ hvN), ?_⟩
        show f (m - (e / a) • v) = 0
        rw [hf, map_sub, inner_sub_right, map_smulₛₗ, inner_smul_right, ← ha, ← he, map_div₀,
          div_mul_cancel₀ _ hsa, sub_self]
      have hsplit : j m = σ (e / a) • j v + j (m - (e / a) • v) := by
        rw [map_sub, map_smulₛₗ]; abel
      rw [hsplit, inner_add_left, inner_smul_left, hv0, mul_zero, zero_add]
      exact hy' _ hm'
    · push_neg at h
      refine ⟨0, N.zero_mem, ?_⟩
      intro m hm
      rw [h m hm, inner_zero_left]
end GlobalTheory
