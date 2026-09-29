-- Prove2me | solution 1 for LinearMap.finrank_even_eq_finrank_odd_of_nineTerm_exact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/867fd72a-672f-5346-ae0c-b9fd890f5703

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LinearMap_finrank_even_eq_finrank_odd_of_nineTerm_exact

set_option autoImplicit false

universe u

open Module

theorem solution {k : Type u} [Field k]
    {V₀ V₁ V₂ V₃ V₄ V₅ V₆ V₇ V₈ : Type u}
    [AddCommGroup V₀] [Module k V₀] [AddCommGroup V₁] [Module k V₁]
    [AddCommGroup V₂] [Module k V₂] [AddCommGroup V₃] [Module k V₃]
    [AddCommGroup V₄] [Module k V₄] [AddCommGroup V₅] [Module k V₅]
    [AddCommGroup V₆] [Module k V₆] [AddCommGroup V₇] [Module k V₇]
    [AddCommGroup V₈] [Module k V₈]
    [FiniteDimensional k V₀] [FiniteDimensional k V₁] [FiniteDimensional k V₂]
    [FiniteDimensional k V₃] [FiniteDimensional k V₄] [FiniteDimensional k V₅]
    [FiniteDimensional k V₆] [FiniteDimensional k V₇]
    (d₀ : V₀ →ₗ[k] V₁) (d₁ : V₁ →ₗ[k] V₂) (d₂ : V₂ →ₗ[k] V₃) (d₃ : V₃ →ₗ[k] V₄)
    (d₄ : V₄ →ₗ[k] V₅) (d₅ : V₅ →ₗ[k] V₆) (d₆ : V₆ →ₗ[k] V₇) (d₇ : V₇ →ₗ[k] V₈)
    (e₀ : LinearMap.ker d₀ = ⊥)
    (e₁ : LinearMap.range d₀ = LinearMap.ker d₁) (e₂ : LinearMap.range d₁ = LinearMap.ker d₂)
    (e₃ : LinearMap.range d₂ = LinearMap.ker d₃) (e₄ : LinearMap.range d₃ = LinearMap.ker d₄)
    (e₅ : LinearMap.range d₄ = LinearMap.ker d₅) (e₆ : LinearMap.range d₅ = LinearMap.ker d₆)
    (e₇ : LinearMap.range d₆ = LinearMap.ker d₇) (e₈ : LinearMap.range d₇ = ⊤) :
    Module.finrank k V₀ + Module.finrank k V₂ + Module.finrank k V₄ + Module.finrank k V₆ + Module.finrank k V₈
      = Module.finrank k V₁ + Module.finrank k V₃ + Module.finrank k V₅ + Module.finrank k V₇ := by

  have h₀ : Module.finrank k (LinearMap.range d₀) + Module.finrank k (LinearMap.ker d₀) = Module.finrank k V₀ :=
    LinearMap.finrank_range_add_finrank_ker d₀
  rw [e₀, finrank_bot] at h₀
  have h₁ := LinearMap.finrank_range_add_finrank_ker d₁
  have h₂ := LinearMap.finrank_range_add_finrank_ker d₂
  have h₃ := LinearMap.finrank_range_add_finrank_ker d₃
  have h₄ := LinearMap.finrank_range_add_finrank_ker d₄
  have h₅ := LinearMap.finrank_range_add_finrank_ker d₅
  have h₆ := LinearMap.finrank_range_add_finrank_ker d₆
  have h₇ := LinearMap.finrank_range_add_finrank_ker d₇
  rw [← e₁] at h₁; rw [← e₂] at h₂; rw [← e₃] at h₃; rw [← e₄] at h₄
  rw [← e₅] at h₅; rw [← e₆] at h₆; rw [← e₇] at h₇
  have h₈ : Module.finrank k (LinearMap.range d₇) = Module.finrank k V₈ := by
    rw [e₈]; simp only [finrank_top]
  omega

end S_LinearMap_finrank_even_eq_finrank_odd_of_nineTerm_exact
end P2MW
export P2MW.S_LinearMap_finrank_even_eq_finrank_odd_of_nineTerm_exact (solution)
