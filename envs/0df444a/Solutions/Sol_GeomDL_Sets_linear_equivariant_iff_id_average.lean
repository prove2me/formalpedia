-- Prove2me | solution 1 for GeomDL.Sets.linear_equivariant_iff_id_average
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T15:58:39.751806+00:00
-- url     : https://prove2.me/submissions/af149c05-2b65-4fe6-859d-22dc9bfd12c0

import Mathlib
import Definitions.Def_GeomDL_Sets_Defs

open GeomDL.Sets

theorem solution {n : ℕ} (hn : 0 < n)
    (F : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) :
    (∀ (σ : Equiv.Perm (Fin n)) (x : Fin n → ℝ), F (permVec σ x) = permVec σ (F x)) ↔
      ∃ α β : ℝ, ∀ x : Fin n → ℝ, F x = α • x + β • average x := by
  constructor
  · intro hF
    set e : Fin n → Fin n → ℝ := fun v j => if v = j then (1 : ℝ) else 0 with he
    have hperm : ∀ (σ : Equiv.Perm (Fin n)) v, permVec σ (e v) = e (σ v) := by
      intro σ v
      funext u
      simp only [permVec, he]
      congr 1
      exact propext ⟨fun h => by rw [h]; simp, fun h => by rw [← h]; simp⟩
    have hFe : ∀ (σ : Equiv.Perm (Fin n)) v u, F (e (σ v)) u = F (e v) (σ.symm u) := by
      intro σ v u
      rw [← hperm, hF]
      rfl
    set z : Fin n := ⟨0, hn⟩
    set c : Fin n → ℝ := fun w => F (e z) w with hc
    have hcol : ∀ v u, F (e v) u = c (Equiv.swap z v u) := by
      intro v u
      have := hFe (Equiv.swap z v) z u
      rw [Equiv.swap_apply_left, Equiv.symm_swap] at this
      exact this
    have hconst : ∀ w w', w ≠ z → w' ≠ z → c w = c w' := by
      intro w w' hw hw'
      have := hFe (Equiv.swap w w') z w
      rw [Equiv.swap_apply_of_ne_of_ne hw.symm hw'.symm, Equiv.symm_swap,
        Equiv.swap_apply_left] at this
      exact this
    let b : ℝ := if h : 1 < n then c ⟨1, h⟩ else 0
    have hb : ∀ w, w ≠ z → c w = b := by
      intro w hw
      have h1 : 1 < n := by
        by_contra h
        apply hw
        ext
        simp [z]
        omega
      simp only [b, dif_pos h1]
      apply hconst w _ hw
      intro h
      have := congrArg Fin.val h
      simp [z] at this
    refine ⟨c z - b, b * n, ?_⟩
    intro x
    funext u
    rw [LinearMap.pi_apply_eq_sum_univ F x]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply, average]
    have hsplit : ∀ v, x v * F (fun j => if v = j then (1:ℝ) else 0) u =
        (if v = u then x v * (c z - b) else 0) + x v * b := by
      intro v
      have : F (fun j => if v = j then (1:ℝ) else 0) u = F (e v) u := rfl
      rw [this, hcol]
      by_cases hvu : v = u
      · subst hvu
        simp
        ring
      · rw [if_neg hvu, hb]
        · ring
        · intro h
          apply hvu
          have := congrArg (Equiv.swap z v) h
          simp only [Equiv.swap_apply_self, Equiv.swap_apply_left] at this
          exact this.symm
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ u, if_pos (Finset.mem_univ _),
      ← Finset.sum_mul]
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
  · rintro ⟨α, β, h⟩ σ x
    have havg : average (permVec σ x) = average x := by
      funext u
      simp only [average, permVec]
      congr 1
      exact Equiv.sum_comp σ.symm x
    rw [h, h, havg]
    funext u
    simp [permVec, average]
