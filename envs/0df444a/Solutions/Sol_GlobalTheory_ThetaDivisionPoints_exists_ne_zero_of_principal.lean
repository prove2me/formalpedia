-- Prove2me | solution 1 for GlobalTheory.ThetaDivisionPoints.exists_ne_zero_of_principal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:09:30.246426+00:00
-- url     : https://prove2.me/submissions/9612c123-2766-4ff3-b4da-2284fc9dc0e9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfLagrangian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsThetaDivisionPointNeZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ThetaFunctionNeZeroAtDivisionPointSelfDual
import Theorems.Thm_GlobalTheory_SiegelNormalForm_exists_normal_form
import Theorems.Thm_GlobalTheory_T_exists_theta_division_point_ne_zero
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk
attribute [local simp] GlobalTheory.thetaLevelBasis_apply
attribute [local simp] GlobalTheory.thetaLevelCharBasis_apply



set_option autoImplicit false
open Complex Matrix
open GlobalTheory GlobalTheory.ThetaDivisionPoints
namespace GlobalTheory.ThetaDivisionPoints
theorem _root_.solution {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ))
    (hd : DiscreteTopology Λ) (hs : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ) (Ef : LinearMap.BilinForm ℤ Λ)
    (hH : Hm.IsHermitian) (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re)
    (hχ : ∀ l, ‖χ l‖ = 1)
    (hE : ∀ l m : Λ, (Ef l m : ℝ) = ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im)
    (hbij : Function.Bijective Ef) (n : ℕ) (hn : 2 ≤ n) (f : (Fin g → ℂ) → ℂ)
    (hdf : Differentiable ℂ f) (h0 : f ≠ 0)
    (hf : ∀ (l : Λ) z, f (z + l) = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) +
      Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) ^ n * f z) :
    ∃ l ∈ Λ, f ((n : ℂ)⁻¹ • l) ≠ 0 := by
  obtain ⟨φ, τ, Q, b, hτ, hτp, hΛ, hQ, -, hb, h1, h2⟩ :=
    GlobalTheory.SiegelNormalForm.exists_normal_form g Λ hd hs Hm χ Ef hH hpos hχ hE hbij
  have hφ : Differentiable ℂ (fun z => φ z) :=
    (LinearMap.toContinuousLinearMap φ.toLinearMap).differentiable
  have key := GlobalTheory.T.exists_theta_division_point_ne_zero g n τ (fun j => b j ^ n) (fun z => f (φ z) * cexp (-(n * Q z))) hτ hτp hn
    (fun j => pow_ne_zero _ (hb j)) ((hdf.comp hφ).mul ((hQ.const_mul (n : ℂ)).neg.cexp)) ?_ ?_ ?_
  · obtain ⟨m, k, h⟩ := key
    refine ⟨φ _, (hΛ _).2 ⟨m, k, rfl⟩, ?_⟩
    rw [← map_smul]
    exact left_ne_zero_of_mul h
  · intro h
    apply h0
    ext w
    have h := congrFun h (φ.symm w)
    simp only [Pi.zero_apply, LinearEquiv.apply_symm_apply] at h ⊢
    exact (mul_eq_zero.1 h).resolve_right (Complex.exp_ne_zero _)
  · intro i z
    have hm : φ (Pi.single i 1) ∈ Λ := by
      refine (hΛ _).2 ⟨Pi.single i 1, 0, ?_⟩
      ext a
      by_cases h : a = i
      · subst h; simp [Matrix.mulVec, dotProduct]
      · simp [h, Matrix.mulVec, dotProduct]
    have e := hf ⟨_, hm⟩ (φ z)
    rw [h1 i ⟨_, hm⟩ z rfl] at e
    simp only [map_add]
    rw [e, ← Complex.exp_nat_mul, mul_right_comm, ← Complex.exp_add, mul_comm]
    congr 2
    ring
  · intro j z
    have hm : φ (τ.mulVec (Pi.single j 1)) ∈ Λ := by
      refine (hΛ _).2 ⟨0, Pi.single j 1, ?_⟩
      have : (fun i => (((Pi.single j 1 : Fin g → ℤ) i : ℤ) : ℂ)) = Pi.single j 1 := by
        ext a
        by_cases h : a = j
        · subst h; simp
        · simp [h]
      rw [this]
      ext a
      simp
    have e := hf ⟨_, hm⟩ (φ z)
    rw [h2 j ⟨_, hm⟩ z rfl] at e
    simp only [map_add]
    rw [e, mul_pow, mul_pow, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    have : cexp (n * (Q (z + τ.mulVec (Pi.single j 1)) - Q z)) *
        cexp (-(n * Q (z + τ.mulVec (Pi.single j 1)))) = cexp (-(n * Q z)) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [← this, show (n : ℂ) * (-(2 * Real.pi * I) * z j) = -(2 * Real.pi * I) * n * z j by ring]
    ring
end GlobalTheory.ThetaDivisionPoints
