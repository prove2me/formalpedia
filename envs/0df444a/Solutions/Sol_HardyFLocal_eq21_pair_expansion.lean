-- Prove2me | solution 1 for HardyFLocal.eq21_pair_expansion
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T02:06:47.914997+00:00
-- url     : https://prove2.me/submissions/bf60d943-2d00-4f14-a7b0-c1942f9d70fc

import Mathlib
import Definitions.Def_HardyFLocal_Superoperator
import Definitions.Def_HardyFLocal_FiducialFamily

set_option autoImplicit false

open HardyFLocal in
theorem solution (S : FiducialFamily) (l' l : Ω) :
    S.map l' ∘ₗ S.map l = ∑ k, pairTable S l' l k • S.map k ∧
    (∀ c : Ω → ℝ, S.map l' ∘ₗ S.map l = ∑ k, c k • S.map k → c = pairTable S l' l) ∧
    S.map l' ∘ₗ S.map l = ∑ p ∈ ({0} : Finset Ω) ×ˢ (Finset.univ : Finset Ω),
      pairTable S l' l p.2 • (S.map p.1 ∘ₗ S.map p.2) := by
  have hmem : ∀ k, S.map k ∈ hpMaps (Fin 2) := by
    intro k
    rw [← S.span_eq]
    exact Submodule.subset_span (Set.mem_range_self k)
  have hcomp : S.map l' ∘ₗ S.map l ∈ hpMaps (Fin 2) := by
    intro A hA
    exact hmem l' _ (hmem l A hA)
  rw [← S.span_eq, Submodule.mem_span_range_iff_exists_fun] at hcomp
  obtain ⟨c0, hc0⟩ := hcomp
  have hex : ∃ c : Ω → ℝ, S.map l' ∘ₗ S.map l = ∑ i, c i • S.map i := ⟨c0, hc0.symm⟩
  have h1 : S.map l' ∘ₗ S.map l = ∑ k, pairTable S l' l k • S.map k := by
    have : pairTable S l' l = hex.choose := by
      unfold pairTable coordsOf
      rw [dif_pos hex]
    rw [this]
    exact hex.choose_spec
  refine ⟨h1, ?_, ?_⟩
  · intro c hc
    funext k
    exact (Fintype.linearIndependent_iffₛ).mp S.linearIndependent c (pairTable S l' l)
      (hc.symm.trans h1) k
  · simp only [Finset.sum_product, Finset.sum_singleton, S.map_zero, LinearMap.id_comp]
    exact h1
