-- Prove2me | solution 1 for GlobalTheory.SW.RowExt.exists_unitary_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:44:33.195766+00:00
-- url     : https://prove2.me/submissions/33d4495c-9079-40d0-808b-f826fa423597

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitaryExt
import Theorems.Thm_GlobalTheory_SW_RowExt_exists_right_inv
import Theorems.Thm_GlobalTheory_SW_RowExt_ccT_eq
import Theorems.Thm_GlobalTheory_SW_RowExt_intM_mul
import Theorems.Thm_GlobalTheory_SW_RowExt_intM_conj
import Theorems.Thm_GlobalTheory_SW_RowExt_intM_nat
import Theorems.Thm_GlobalTheory_SW_RowExt_intM_J
import Theorems.Thm_GlobalTheory_SW_RowExt_J_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.RowExt
namespace GlobalTheory.SW.RowExt
theorem _root_.solution :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N c : ℕ), 0 < c → ∃ c' : ℕ, 0 < c' ∧
      ∀ W : Matrix (Fin N) (Fin N ⊕ Fin N) E, IntM W → LinearIndependent E (fun i => W i) →
        W * Matrix.J (Fin N) E * ccT W = 0 →
        (∀ t : Fin N → E, (∀ j, IsIntegral ℤ ((t ᵥ* W) j)) → ∀ i, IsIntegral ℤ ((c : E) * t i)) →
        ∃ γ ∈ UU E N, Den c' γ ∧ ∀ a, γ (Sum.inr a) = W a := by
  intro E _ _ _ N c hc
  refine ⟨2 * c * c, by positivity, fun W hW hli hiso hprim => ?_⟩
  obtain ⟨X, hX, hWX⟩ := exists_right_inv (c : E) W hW hli hprim
  rw [ccT_eq] at hiso
  have hc0 : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  set J := Matrix.J (Fin N) E with hJ
  have hJJ : J * J = -1 := Matrix.J_squared _ _
  have hJc : Jᴴ = -J := J_conj
  have hJi : IntM J := intM_J
  obtain ⟨V₀, hV₀⟩ : ∃ V₀ : Matrix (Fin N) (Fin N ⊕ Fin N) E, V₀ = (c : E)⁻¹ • (Xᴴ * J) := ⟨_, rfl⟩
  have hcV : (c : E) • V₀ = Xᴴ * J := by rw [hV₀, smul_smul, mul_inv_cancel₀ hc0, one_smul]
  have hVi : IntM ((c : E) • V₀) := hcV ▸ intM_mul (intM_conj hX) hJi
  have h1 : V₀ * J * Wᴴ = -1 := by
    rw [hV₀, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_assoc Xᴴ, hJJ, Matrix.mul_neg,
      Matrix.mul_one, Matrix.neg_mul, ← Matrix.conjTranspose_mul, hWX]
    simp [smul_smul, hc0]
  have skew : ∀ A B : Matrix (Fin N) (Fin N ⊕ Fin N) E, (A * J * Bᴴ)ᴴ = -(B * J * Aᴴ) := by
    intro A B
    simp [Matrix.conjTranspose_mul, hJc, Matrix.mul_assoc]
  have h2 : W * J * V₀ᴴ = 1 := by
    have := skew V₀ W
    rw [h1] at this
    simpa using this.symm
  obtain ⟨S, hS⟩ : ∃ S, S = V₀ * J * V₀ᴴ := ⟨_, rfl⟩
  have hSc : Sᴴ = -S := hS ▸ skew V₀ V₀
  obtain ⟨T, hT⟩ : ∃ T, T = (-(2 : E)⁻¹) • S := ⟨_, rfl⟩
  have hTc : Tᴴ = -T := by
    rw [hT, Matrix.conjTranspose_smul, hSc]; simp
  obtain ⟨V, hV⟩ : ∃ V, V = V₀ + T * W := ⟨_, rfl⟩
  have k2 : W * J * Vᴴ = 1 := by
    rw [hV, Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.mul_add, h2,
      ← Matrix.mul_assoc, hiso, Matrix.zero_mul, add_zero]
  have k1 : V * J * Wᴴ = -1 := by
    have := skew W V
    rw [k2] at this
    rw [← neg_neg (V * J * Wᴴ), ← this]; simp
  have k0 : V * J * Vᴴ = 0 := by
    have e : V * J * V₀ᴴ = S + T := by
      rw [hV, Matrix.add_mul, Matrix.add_mul, ← hS, Matrix.mul_assoc T, Matrix.mul_assoc T, h2,
        Matrix.mul_one]
    conv_lhs => rw [show Vᴴ = V₀ᴴ + Wᴴ * Tᴴ by
      rw [hV, Matrix.conjTranspose_add, Matrix.conjTranspose_mul]]
    rw [Matrix.mul_add, e, ← Matrix.mul_assoc, k1, hTc, hT]
    simp only [Matrix.neg_mul, Matrix.one_mul, neg_neg]
    rw [add_assoc, ← add_smul, show (-(2 : E)⁻¹ + -(2 : E)⁻¹) = -1 by norm_num]
    simp
  have key : Matrix.fromRows V W * J * (Matrix.fromRows V W)ᴴ = J := by
    rw [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromRows_mul,
      Matrix.fromRows_mul_fromCols, k0, k1, k2, hiso]
    rfl
  refine ⟨Matrix.fromRows V W, ?_, ?_, fun a => rfl⟩
  · generalize Matrix.fromRows V W = g at key
    show gᴴ * J * g = J
    have e1 : g * (J * gᴴ * -J) = 1 := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, key, Matrix.mul_neg, hJJ, neg_neg]
    have e2 := mul_eq_one_comm.mp e1
    have e3 : J * (J * gᴴ * -J * g) = J := by rw [e2, Matrix.mul_one]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hJJ] at e3
    simpa using e3
  · have hVV : ((2 * c * c : ℕ) : E) • V = ((2 * c : ℕ) : E) • ((c : E) • V₀) -
        ((c : E) • V₀) * J * ((c : E) • V₀)ᴴ * W := by
      rw [hV, hT, hS]
      simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul,
        star_natCast, sub_eq_add_neg, ← neg_smul]
      congr 2
      · push_cast; ring
      · push_cast; field_simp
    have i1 := intM_nat (2 * c) hVi
    have i2 := intM_mul (intM_mul (intM_mul hVi hJi) (intM_conj hVi)) hW
    rintro (a | a) b
    · show IsIntegral ℤ ((((2 * c * c : ℕ) : E) • V) a b)
      rw [hVV]
      exact (i1 a b).sub (i2 a b)
    · exact intM_nat (2 * c * c) hW a b
end GlobalTheory.SW.RowExt
