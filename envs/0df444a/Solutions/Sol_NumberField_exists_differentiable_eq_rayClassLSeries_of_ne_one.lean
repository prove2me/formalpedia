-- Prove2me | solution 1 for NumberField.exists_differentiable_eq_rayClassLSeries_of_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/42847cbc-0ee3-598d-a3a9-61b805155743

import Mathlib
import Definitions.Def_NumberField_CompletedRayL
import Definitions.Def_NumberField_RayCharacterData
import Theorems.Thm_M4aTorus_completedRayL_fe
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_exists_differentiable_eq_rayClassLSeries_of_ne_one

set_option autoImplicit false

noncomputable section

namespace P2mHeckeEntire

open NumberField NumberField.InfinitePlace Complex Deep.NTSupply

def recipFactor (x : ℝ) (a b c : ℕ) (s : ℂ) : ℂ :=
  Complex.exp (-(Complex.log (x : ℂ) * (s / 2))) *
    ((Gammaℝ s)⁻¹) ^ a * ((Gammaℝ (s + 1))⁻¹) ^ b * ((Gammaℝ s)⁻¹ * (Gammaℝ (s + 1))⁻¹) ^ c

theorem differentiable_recipFactor (x : ℝ) (a b c : ℕ) :
    Differentiable ℂ (recipFactor x a b c) := by
  unfold recipFactor
  have h1 : Differentiable ℂ fun s : ℂ => Complex.exp (-(Complex.log (x : ℂ) * (s / 2))) := by
    apply Differentiable.cexp
    apply Differentiable.neg
    apply Differentiable.const_mul
    exact Differentiable.div_const differentiable_id 2
  have h2 : Differentiable ℂ fun s : ℂ => (Gammaℝ s)⁻¹ := differentiable_Gammaℝ_inv
  have h3 : Differentiable ℂ fun s : ℂ => (Gammaℝ (s + 1))⁻¹ :=
    differentiable_Gammaℝ_inv.comp (differentiable_id.add_const 1)
  exact ((h1.mul (h2.pow a)).mul (h3.pow b)).mul ((h2.mul h3).pow c)

theorem factor_mul_recipFactor {x : ℝ} (hx : 0 < x) (a b c : ℕ) {s : ℂ} (hs : 0 < s.re) :
    ((x : ℂ) ^ (s / 2) * Gammaℝ s ^ a * Gammaℝ (s + 1) ^ b * Gammaℂ s ^ c) *
      recipFactor x a b c s = 1 := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hΓ1 : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs
  have hΓ2 : Gammaℝ (s + 1) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  have hcpow : (x : ℂ) ^ (s / 2) = Complex.exp (Complex.log (x : ℂ) * (s / 2)) :=
    Complex.cpow_def_of_ne_zero hx0 _
  have hexp : Complex.exp (Complex.log (x : ℂ) * (s / 2)) *
      Complex.exp (-(Complex.log (x : ℂ) * (s / 2))) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hΓℂ : Gammaℂ s = Gammaℝ s * Gammaℝ (s + 1) := (Gammaℝ_mul_Gammaℝ_add_one s).symm
  unfold recipFactor
  rw [hcpow, hΓℂ]
  calc Complex.exp (Complex.log ↑x * (s / 2)) * s.Gammaℝ ^ a * (s + 1).Gammaℝ ^ b *
        (s.Gammaℝ * (s + 1).Gammaℝ) ^ c *
        (Complex.exp (-(Complex.log ↑x * (s / 2))) * s.Gammaℝ⁻¹ ^ a * (s + 1).Gammaℝ⁻¹ ^ b *
          (s.Gammaℝ⁻¹ * (s + 1).Gammaℝ⁻¹) ^ c)
      = (Complex.exp (Complex.log ↑x * (s / 2)) * Complex.exp (-(Complex.log ↑x * (s / 2)))) *
          (s.Gammaℝ * s.Gammaℝ⁻¹) ^ a * ((s + 1).Gammaℝ * (s + 1).Gammaℝ⁻¹) ^ b *
          ((s.Gammaℝ * s.Gammaℝ⁻¹) * ((s + 1).Gammaℝ * (s + 1).Gammaℝ⁻¹)) ^ c := by ring
    _ = 1 := by
      rw [hexp, mul_inv_cancel₀ hΓ1, mul_inv_cancel₀ hΓ2]
      simp

theorem main (K : Type) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥)
    (χ : NarrowRayClassGroup K 𝔣 →* ℂ) (hχ : χ ≠ 1)
    (S : Finset {w : InfinitePlace K // w.IsReal}) (hpar : M4aP2.IsParity K 𝔣 χ S) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
      ∀ s : ℂ, 1 < s.re → g s = M4aTorus.rayClassLSeries K 𝔣 χ s := by
  obtain ⟨F, G, -, -, hFeq, -, -, hent⟩ := M4aTorus.completedRayL_fe K 𝔣 χ S hpar
  obtain ⟨hF, -⟩ := hent hχ
  set x : ℝ := |(discr K : ℝ)| * (Ideal.absNorm 𝔣 : ℝ) with hxdef
  have hx : 0 < x := by
    have h1 : (0 : ℝ) < |(discr K : ℝ)| := abs_pos.mpr (by exact_mod_cast discr_ne_zero K)
    have h2 : (0 : ℝ) < (Ideal.absNorm 𝔣 : ℝ) := by
      have : Ideal.absNorm 𝔣 ≠ 0 := by
        rw [Ne, Ideal.absNorm_eq_zero_iff]
        exact h𝔣
      exact_mod_cast Nat.pos_of_ne_zero this
    exact mul_pos h1 h2
  set a : ℕ := nrRealPlaces K - S.card
  set b : ℕ := S.card
  set c : ℕ := nrComplexPlaces K
  refine ⟨fun s => F s * recipFactor x a b c s, hF.mul (differentiable_recipFactor x a b c), ?_⟩
  intro s hs
  have hs0 : 0 < s.re := by linarith
  simp only
  rw [hFeq s hs, M4aTorus.completedRayL]
  have key := factor_mul_recipFactor hx a b c hs0
  have hxcast : (((|(discr K : ℝ)| * (Ideal.absNorm 𝔣 : ℝ) : ℝ)) : ℂ) = (x : ℂ) := by rw [hxdef]
  rw [hxcast]
  calc (x : ℂ) ^ (s / 2) * s.Gammaℝ ^ a * (s + 1).Gammaℝ ^ b * s.Gammaℂ ^ c *
        M4aTorus.rayClassLSeries K 𝔣 χ s * recipFactor x a b c s
      = ((x : ℂ) ^ (s / 2) * s.Gammaℝ ^ a * (s + 1).Gammaℝ ^ b * s.Gammaℂ ^ c *
          recipFactor x a b c s) * M4aTorus.rayClassLSeries K 𝔣 χ s := by ring
    _ = M4aTorus.rayClassLSeries K 𝔣 χ s := by rw [key, one_mul]

end P2mHeckeEntire

end

open NumberField NumberField.InfinitePlace Deep.NTSupply in
theorem solution
    (K : Type) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥)
    (χ : NarrowRayClassGroup K 𝔣 →* ℂ) (hχ : χ ≠ 1)
    (S : Finset {w : InfinitePlace K // w.IsReal}) (hpar : M4aP2.IsParity K 𝔣 χ S) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
      ∀ s : ℂ, 1 < s.re → g s = M4aTorus.rayClassLSeries K 𝔣 χ s :=
  P2mHeckeEntire.main K 𝔣 h𝔣 χ hχ S hpar

end S_NumberField_exists_differentiable_eq_rayClassLSeries_of_ne_one
end P2MW
export P2MW.S_NumberField_exists_differentiable_eq_rayClassLSeries_of_ne_one (solution)
