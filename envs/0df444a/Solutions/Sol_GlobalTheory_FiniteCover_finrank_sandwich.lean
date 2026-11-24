-- Prove2me | solution 1 for GlobalTheory.FiniteCover.finrank_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:27:12.799947+00:00
-- url     : https://prove2.me/submissions/057a7469-b2a7-4254-afa1-832025fd8df1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCommonMultiple
import Theorems.Thm_GlobalTheory_FiniteCover_finrank_le_of_range_le
import Theorems.Thm_GlobalTheory_FiniteCover_exists_common_multiple

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory GlobalTheory.FiniteCover
namespace GlobalTheory.FiniteCover
theorem _root_.solution {K F F' I : Type*} [Field K] [Field F] [Field F'] [Algebra K F]
    [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Fintype I] {d : ℕ} (e : Basis (Fin d) F F')
    (A : I → Subring F) (C : I → Subring F') (ρ c : I → F)
    (hρ : ∀ i, ρ i ≠ 0) (hc : ∀ i, c i ≠ 0) (hr : ∀ i k, ρ i / ρ k ∈ A k)
    (hext : ∀ i k, ∃ m : ℕ, c i * (ρ i / ρ k) ^ m ∈ A k)
    (hAC : ∀ i, ∀ a ∈ A i, algebraMap F F' a ∈ C i)
    (hc₁ : ∀ i j, ∀ y ∈ C i, c i * e.repr y j ∈ A i) (hc₂ : ∀ i j, c i • e j ∈ C i)
    (V W : ℕ → Type*) [∀ t, AddCommGroup (V t)] [∀ t, Module K (V t)] [∀ t, AddCommGroup (W t)]
    [∀ t, Module K (W t)] (hV : ∀ t, Module.Finite K (V t)) (hW : ∀ t, Module.Finite K (W t))
    (α : ∀ t, V t →ₗ[K] F) (β : ∀ t, W t →ₗ[K] F') (hα : ∀ t, Function.Injective (α t))
    (hβ : ∀ t, Function.Injective (β t))
    (rα : ∀ t x, (∃ v, α t v = x) ↔ ∀ i, ∃ a ∈ A i, x = a * ρ i ^ t)
    (rβ : ∀ t y, (∃ w, β t w = y) ↔ ∀ i, ∃ a ∈ C i, y = a * algebraMap F F' (ρ i ^ t)) :
    ∃ a : ℕ, ∀ t : ℕ, d * finrank K (V t) ≤ finrank K (W (t + a)) ∧
      finrank K (W t) ≤ d * finrank K (V (t + a)) := by
  obtain ⟨a, u, hu, hub⟩ := exists_common_multiple A ρ c hρ hc hr hext
  have hpi : ∀ t, finrank K (Fin d → V t) = d * finrank K (V t) := fun t => by
    rw [Module.finrank_pi_fintype]
    simp
  refine ⟨a, fun t => ⟨?_, ?_⟩⟩
  · rw [← hpi]
    let L : (Fin d → V t) →ₗ[K] F' :=
      ((e.equivFun.symm.toLinearMap.restrictScalars K).comp
        (((LinearMap.mulLeft K u).comp (α t)).compLeft (Fin d)))
    have hL : ∀ v, L v = ∑ j, (u * α t (v j)) • e j := fun v => e.equivFun_symm_apply _
    refine finrank_le_of_range_le L ?_ (β (t + a)) fun v => (rβ _ _).2 fun i => ?_
    · intro v w h
      have h' := e.equivFun.symm.injective h
      funext j
      exact hα t (mul_left_cancel₀ hu (congrFun h' j))
    · obtain ⟨b, hb, rfl⟩ := hub i
      choose x hx hx' using fun j => (rα t _).1 ⟨v j, rfl⟩ i
      refine ⟨∑ j, algebraMap F F' (b * x j) * (c i • e j),
        sum_mem fun j _ => mul_mem (hAC i _ (mul_mem hb (hx j))) (hc₂ i j), ?_⟩
      rw [hL, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hx' j]
      simp only [Algebra.smul_def, map_mul, map_pow, pow_add]
      ring
  · rw [← hpi]
    let L : W t →ₗ[K] (Fin d → F) := ((LinearMap.mulLeft K u).compLeft (Fin d)).comp
      ((e.equivFun.toLinearMap.restrictScalars K).comp (β t))
    have hL : ∀ w j, L w j = u * e.repr (β t w) j := fun w j => rfl
    refine finrank_le_of_range_le L ?_ ((α (t + a)).compLeft (Fin d)) fun w => ?_
    · intro v w h
      refine hβ t (e.equivFun.injective (funext fun j => ?_))
      exact mul_left_cancel₀ hu (congrFun h j)
    · have key : ∀ j, ∃ v, α (t + a) v = L w j := fun j => (rα _ _).2 fun i => by
        obtain ⟨b, hb, hub⟩ := hub i
        obtain ⟨y, hy, hy'⟩ := (rβ t _).1 ⟨w, rfl⟩ i
        refine ⟨b * (c i * e.repr y j), mul_mem hb (hc₁ i j y hy), ?_⟩
        rw [hL, hy', mul_comm y, ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul, hub,
          pow_add]
        ring
      choose v hv using key
      exact ⟨v, funext hv⟩
end GlobalTheory.FiniteCover
