-- Prove2me | solution 1 for GlobalTheory.norm_sq_adjoint_add_ge_of_joint_eigenspaces
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:34:31.876145+00:00
-- url     : https://prove2.me/submissions/5e6f5fe4-9cb0-4814-ac32-d4a2569b465a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NormSqAdjointAddGeOfJointEigenspaces

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open scoped InnerProductSpace
namespace GlobalTheory
theorem _root_.solution (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp] (Vm : Type) [NormedAddCommGroup Vm] [InnerProductSpace ℂ Vm] [FiniteDimensional ℂ Vm] (ι : Type) (S : ι → Submodule ℂ V) (A : Vp →L[ℂ] V) (B : Vm →L[ℂ] V) (wp wm : ι → ℝ) (c : ℝ) (hS : (⨆ i, S i) = ⊤)
    (hw : ∀ i, ∀ v ∈ S i, A (ContinuousLinearMap.adjoint A v) = (wp i : ℂ) • v ∧ B (ContinuousLinearMap.adjoint B v) = (wm i : ℂ) • v)
    (hc : ∀ i, c ≤ wp i ∨ c ≤ wm i) (v : V) :
    c * ‖v‖ ^ 2 ≤ ‖ContinuousLinearMap.adjoint A v‖ ^ 2 + ‖ContinuousLinearMap.adjoint B v‖ ^ 2 := by
  have hA : ∀ x : V, (⟪A (ContinuousLinearMap.adjoint A x), x⟫_ℂ).re = ‖ContinuousLinearMap.adjoint A x‖ ^ 2 := by
    intro x
    rw [← ContinuousLinearMap.adjoint_inner_right]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  have hB : ∀ x : V, (⟪B (ContinuousLinearMap.adjoint B x), x⟫_ℂ).re = ‖ContinuousLinearMap.adjoint B x‖ ^ 2 := by
    intro x
    rw [← ContinuousLinearMap.adjoint_inner_right]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  have hsm : ∀ (r : ℝ) (x : V), (⟪(r : ℂ) • x, x⟫_ℂ).re = r * ‖x‖ ^ 2 := by
    intro r x
    rw [inner_smul_left, Complex.conj_ofReal, Complex.re_ofReal_mul]
    congr 1
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  let X : V →ₗ[ℂ] V := (A ∘L ContinuousLinearMap.adjoint A + B ∘L ContinuousLinearMap.adjoint B : V →L[ℂ] V).toLinearMap
  have hX : ∀ x, X x = A (ContinuousLinearMap.adjoint A x) + B (ContinuousLinearMap.adjoint B x) := fun x => rfl
  have hsym : X.IsSymmetric := by
    intro x y
    rw [hX, hX, inner_add_left, inner_add_right]
    rw [← ContinuousLinearMap.adjoint_inner_right A, ← ContinuousLinearMap.adjoint_inner_right B,
      ← ContinuousLinearMap.adjoint_inner_left A, ← ContinuousLinearMap.adjoint_inner_left B]
  have hge : ∀ i, ∀ x ∈ S i, x ≠ 0 → c ≤ wp i + wm i := by
    intro i x hx hx0
    have hn : 0 < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx0) 2
    have h1 := hA x
    have h2 := hB x
    rw [(hw i x hx).1, hsm] at h1
    rw [(hw i x hx).2, hsm] at h2
    have p1 : 0 ≤ wp i := by
      have : 0 ≤ wp i * ‖x‖ ^ 2 := by rw [h1]; positivity
      exact nonneg_of_mul_nonneg_left this hn
    have p2 : 0 ≤ wm i := by
      have : 0 ≤ wm i * ‖x‖ ^ 2 := by rw [h2]; positivity
      exact nonneg_of_mul_nonneg_left this hn
    rcases hc i with h | h <;> linarith
  have hev : ∀ (μ : ℝ) (e : V), X e = (μ : ℂ) • e → e ≠ 0 → c ≤ μ := by
    intro μ e he he0
    by_contra hlt
    apply he0
    have hmem : e ∈ (⨆ i, S i)ᗮ := by
      rw [← Submodule.iInf_orthogonal, Submodule.mem_iInf]
      intro i
      rw [Submodule.mem_orthogonal]
      intro x hx
      by_cases hx0 : x = 0
      · simp [hx0]
      have hle := hge i x hx hx0
      have hXx : X x = ((wp i + wm i : ℝ) : ℂ) • x := by
        rw [hX, (hw i x hx).1, (hw i x hx).2, ← add_smul]; push_cast; rfl
      have h := hsym x e
      rw [hXx, he, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at h
      have hne : ((wp i + wm i : ℝ) : ℂ) ≠ (μ : ℂ) := by
        intro h'
        have := Complex.ofReal_injective h'
        apply hlt; linarith
      by_contra h0
      exact hne (mul_right_cancel₀ h0 h)
    rw [hS, Submodule.top_orthogonal_eq_bot] at hmem
    exact (Submodule.mem_bot ℂ).mp hmem
  have hn : Module.finrank ℂ V = Module.finrank ℂ V := rfl
  set b := hsym.eigenvectorBasis hn with hb
  have hμ : ∀ j, c ≤ hsym.eigenvalues hn j := fun j =>
    hev _ (b j) (hsym.apply_eigenvectorBasis hn j) (b.orthonormal.ne_zero j)
  rw [← hA, ← hB, ← Complex.add_re, ← inner_add_left, ← hX]
  rw [← b.sum_inner_mul_inner (X v) v, Complex.re_sum, ← b.sum_sq_norm_inner_right v, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have h1 : ⟪X v, b j⟫_ℂ = (hsym.eigenvalues hn j : ℂ) * ⟪v, b j⟫_ℂ := by
    rw [hsym v (b j), hb, hsym.apply_eigenvectorBasis hn j, inner_smul_right]; rfl
  rw [h1, mul_assoc, Complex.re_ofReal_mul, ← inner_conj_symm v (b j), Complex.conj_mul']
  have : ((‖⟪b j, v⟫_ℂ‖ : ℂ) ^ 2).re = ‖⟪b j, v⟫_ℂ‖ ^ 2 := by
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  rw [this]
  exact mul_le_mul_of_nonneg_right (hμ j) (sq_nonneg _)
end GlobalTheory
