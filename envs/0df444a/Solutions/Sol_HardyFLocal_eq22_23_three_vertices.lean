-- Prove2me | solution 1 for HardyFLocal.eq22_23_three_vertices
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T04:43:31.359363+00:00
-- url     : https://prove2.me/submissions/0b0ea417-4ddf-4ec5-804f-91e75ec8b8c1

import Mathlib
import Definitions.Def_HardyFLocal_Superoperator
import Definitions.Def_HardyFLocal_FiducialFamily

set_option autoImplicit false

open HardyFLocal in
theorem solution (S : FiducialFamily) (l'' l' l : Ω) :
    S.map l'' ∘ₗ S.map l' ∘ₗ S.map l =
      ∑ k, (∑ a, pairTable S l'' l' a * pairTable S a l k) • S.map k ∧
    (∀ k, coordsOf S.map (S.map l'' ∘ₗ S.map l' ∘ₗ S.map l) k =
      ∑ a, pairTable S l'' l' a * pairTable S a l k) ∧
    (∀ c : Ω → ℝ, S.map l'' ∘ₗ S.map l' ∘ₗ S.map l = ∑ k, c k • S.map k →
      ∀ k, c k = ∑ a, pairTable S l'' l' a * pairTable S a l k) ∧
    S.map l'' ∘ₗ S.map l' ∘ₗ S.map l =
      ∑ p ∈ ({0} : Finset Ω) ×ˢ ({0} : Finset Ω) ×ˢ (Finset.univ : Finset Ω),
        (∑ a, pairTable S l'' l' a * pairTable S a l p.2.2) •
          (S.map p.1 ∘ₗ S.map p.2.1 ∘ₗ S.map p.2.2) := by
  have hmem : ∀ k, S.map k ∈ hpMaps (Fin 2) := fun k =>
    S.span_eq ▸ Submodule.subset_span ⟨k, rfl⟩
  have hspan : ∀ Φ : Op (Fin 2), Φ ∈ hpMaps (Fin 2) → ∃ c : Ω → ℝ, Φ = ∑ i, c i • S.map i := by
    intro Φ hΦ
    rw [← S.span_eq, Submodule.mem_span_range_iff_exists_fun] at hΦ
    obtain ⟨c, hc⟩ := hΦ
    exact ⟨c, hc.symm⟩
  have hcomp : ∀ Φ Ψ : Op (Fin 2), Φ ∈ hpMaps (Fin 2) → Ψ ∈ hpMaps (Fin 2) →
      Φ ∘ₗ Ψ ∈ hpMaps (Fin 2) := by
    intro Φ Ψ hΦ hΨ
    have hΦ' : ∀ A : Matrix (Fin 2) (Fin 2) ℂ, A.IsHermitian → (Φ A).IsHermitian := hΦ
    have hΨ' : ∀ A : Matrix (Fin 2) (Fin 2) ℂ, A.IsHermitian → (Ψ A).IsHermitian := hΨ
    show ∀ A : Matrix (Fin 2) (Fin 2) ℂ, A.IsHermitian → ((Φ ∘ₗ Ψ) A).IsHermitian
    intro A hA
    exact hΦ' _ (hΨ' A hA)
  have hcoords : ∀ Φ : Op (Fin 2), Φ ∈ hpMaps (Fin 2) → Φ = ∑ i, coordsOf S.map Φ i • S.map i := by
    intro Φ hΦ
    have h := hspan Φ hΦ
    unfold coordsOf
    rw [dif_pos h]
    exact h.choose_spec
  have huniq : ∀ c c' : Ω → ℝ, ∑ i, c i • S.map i = ∑ i, c' i • S.map i → c = c' := by
    intro c c' h
    have h0 := Fintype.linearIndependent_iff.mp S.linearIndependent (c - c') (by
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h, sub_self])
    funext i
    have := h0 i
    simp only [Pi.sub_apply] at this
    linarith
  have hpair : ∀ a b, S.map a ∘ₗ S.map b = ∑ k, pairTable S a b k • S.map k :=
    fun a b => hcoords _ (hcomp _ _ (hmem a) (hmem b))
  have h1 : S.map l'' ∘ₗ S.map l' ∘ₗ S.map l =
      ∑ k, (∑ a, pairTable S l'' l' a * pairTable S a l k) • S.map k := by
    apply LinearMap.ext
    intro A
    have e1 : S.map l'' (S.map l' (S.map l A)) = ∑ a, pairTable S l'' l' a • S.map a (S.map l A) := by
      have := congrArg (fun F : Op (Fin 2) => F (S.map l A)) (hpair l'' l')
      simpa [LinearMap.sum_apply, LinearMap.smul_apply] using this
    have e2 : ∀ a, S.map a (S.map l A) = ∑ k, pairTable S a l k • S.map k A := by
      intro a
      have := congrArg (fun F : Op (Fin 2) => F A) (hpair a l)
      simpa [LinearMap.sum_apply, LinearMap.smul_apply] using this
    rw [LinearMap.comp_apply, LinearMap.comp_apply, e1, LinearMap.sum_apply]
    simp_rw [e2, Finset.smul_sum, smul_smul, LinearMap.smul_apply, Finset.sum_smul]
    exact Finset.sum_comm
  have hmem3 : S.map l'' ∘ₗ S.map l' ∘ₗ S.map l ∈ hpMaps (Fin 2) :=
    hcomp _ _ (hmem l'') (hcomp _ _ (hmem l') (hmem l))
  refine ⟨h1, fun k => ?_, fun c hc k => ?_, ?_⟩
  · have := huniq _ _ ((hcoords _ hmem3).symm.trans h1)
    exact congrFun this k
  · have := huniq _ _ (hc.symm.trans h1)
    exact congrFun this k
  · simp only [Finset.sum_product, Finset.sum_singleton, S.map_zero, LinearMap.id_comp]
    exact h1
