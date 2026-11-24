-- Prove2me | solution 1 for GlobalTheory.siegel_fock_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:33:44.30757+00:00
-- url     : https://prove2.me/submissions/2a9ccd2e-be7f-4187-b033-d0e2f22ff22a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSiegelFockFormOfComplexStructure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (J : (V × V) →ₗ[ℝ] (V × V)), (∀ x y, β x y = β y x) → (∀ w, J (J w) = -w) →
    (∀ w w', β (J w).1 (J w').2 - β (J w').1 (J w).2 = β w.1 w'.2 - β w'.1 w.2) →
    (∀ w, w ≠ 0 → 0 < β w.1 (J w).2 - β (J w).1 w.2) →
    ∃ (Q : V →L[ℝ] V →L[ℝ] ℂ) (c : ℝ), 0 < c ∧ (∀ x, c * ‖x‖ ^ 2 ≤ (Q x x).re) ∧ (∀ x y, Q x y = Q y x) ∧
      ∀ w x, Q x (J w).1 + (Real.pi : ℂ) * Complex.I * (β x (J w).2 : ℂ) = Complex.I * (Q x w.1 + (Real.pi : ℂ) * Complex.I * (β x w.2 : ℂ)) := by
  intro V _ _ _ β J hsym hJJ hJ hpos
  set Φ : (V × V) →ₗ[ℝ] (V × V) :=
    LinearMap.inr ℝ V V ∘ₗ LinearMap.fst ℝ V V + J ∘ₗ LinearMap.inr ℝ V V ∘ₗ LinearMap.snd ℝ V V with hΦdef
  have hΦ : ∀ u : V × V, Φ u = (0, u.1) + J (0, u.2) := by
    intro u; simp [hΦdef]
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    rw [hΦ] at hu
    have h1 : (J (0, u.2)).1 = 0 := by
      have := congrArg Prod.fst hu; simpa using this
    have hb : u.2 = 0 := by
      by_contra hne
      have := hpos (0, u.2) (by simpa using hne)
      simp [h1] at this
    have hJ0 : J (0, 0) = 0 := J.map_zero
    have ha : u.1 = 0 := by
      have := congrArg Prod.snd hu; simpa [hb, hJ0] using this
    exact Prod.ext ha hb
  set E := LinearEquiv.ofInjectiveEndo Φ hinj with hEdef
  have hE : ∀ w, Φ (E.symm w) = w := fun w => by
    show E (E.symm w) = w
    exact E.apply_symm_apply w
  have hJ0 : J (0, 0) = 0 := J.map_zero
  set A : V →ₗ[ℝ] V := LinearMap.fst ℝ V V ∘ₗ E.symm.toLinearMap ∘ₗ LinearMap.inl ℝ V V with hAdef
  set B : V →ₗ[ℝ] V := LinearMap.snd ℝ V V ∘ₗ E.symm.toLinearMap ∘ₗ LinearMap.inl ℝ V V with hBdef
  have hAB : ∀ p, E.symm (p, 0) = (A p, B p) := fun p => by simp [hAdef, hBdef]
  have hP0 : ∀ q, E.symm (0, q) = (q, 0) := fun q => by
    apply E.injective
    rw [E.apply_symm_apply]
    show (0, q) = Φ (q, 0)
    rw [hΦ]; simp [hJ0]
  have hsplit : ∀ w : V × V, E.symm w = (A w.1 + w.2, B w.1) := fun w => by
    have hw : w = (w.1, 0) + (0, w.2) := by simp
    rw [hw, map_add, hAB, hP0]; simp
  have hJB : ∀ p, J (0, B p) = (p, -A p) := fun p => by
    have := hE (p, 0)
    rw [hAB, hΦ] at this
    have h2 : J (0, B p) = (p, 0) - (0, A p) := by rw [← this]; abel
    rw [h2]; simp
  have hPJ : ∀ w : V × V, E.symm (J w) = (-(E.symm w).2, (E.symm w).1) := fun w => by
    apply E.injective
    rw [E.apply_symm_apply]
    show J w = Φ _
    conv_lhs => rw [← hE w]
    rw [hΦ, hΦ, map_add, hJJ]
    ext <;> simp <;> abel
  have hAsym : ∀ x y, β x (A y) = β y (A x) := fun x y => by
    have := hJ (0, B x) (0, B y)
    rw [hJB, hJB] at this
    simp at this
    linarith
  have hBsym : ∀ x y, β x (B y) = β y (B x) := fun x y => by
    have := hJ (J (0, B x)) (0, B y)
    rw [hJJ, hJB, hJB] at this
    simp at this
    linarith
  have hBpos : ∀ x, x ≠ 0 → 0 < -β x (B x) := fun x hx => by
    have hne : ((0 : V), B x) ≠ 0 := by
      intro h0
      have h1 : J (0, B x) = 0 := by rw [h0]; exact J.map_zero
      rw [hJB] at h1
      exact hx (congrArg Prod.fst h1)
    have := hpos (0, B x) hne
    rw [hJB] at this
    simpa using this
  let Q' : V →ₗ[ℝ] V →ₗ[ℝ] ℂ := LinearMap.mk₂ ℝ
    (fun x y => ((Real.pi * β x (A y) : ℝ) : ℂ) * Complex.I - ((Real.pi * β x (B y) : ℝ) : ℂ))
    (fun m₁ m₂ n => by simp; ring)
    (fun c m n => by simp; ring)
    (fun m n₁ n₂ => by simp; ring)
    (fun c m n => by simp; ring)
  let Q : V →L[ℝ] V →L[ℝ] ℂ := LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (V →ₗ[ℝ] ℂ) ≃ₗ[ℝ] (V →L[ℝ] ℂ)).toLinearMap ∘ₗ Q')
  have hQ : ∀ x y, Q x y = ((Real.pi * β x (A y) : ℝ) : ℂ) * Complex.I - ((Real.pi * β x (B y) : ℝ) : ℂ) :=
    fun x y => rfl
  have hre : ∀ x, (Q x x).re = Real.pi * -β x (B x) := fun x => by
    rw [hQ]; simp
  have hscale : ∀ (t : ℝ) (y : V), Real.pi * -β (t • y) (B (t • y)) = t ^ 2 * (Real.pi * -β y (B y)) :=
    fun t y => by simp; ring
  have hcont : Continuous fun x => (Q x x).re := by fun_prop
  have hsym' : ∀ x y, Q x y = Q y x := fun x y => by rw [hQ, hQ, hAsym x y, hBsym x y]
  have hfock : ∀ w x, Q x (J w).1 + (Real.pi : ℂ) * Complex.I * (β x (J w).2 : ℂ) =
      Complex.I * (Q x w.1 + (Real.pi : ℂ) * Complex.I * (β x w.2 : ℂ)) := fun w x => by
    have e1 := hsplit (J w)
    rw [hPJ, hsplit w] at e1
    have h1 : A (J w).1 + (J w).2 = -(B w.1) := (congrArg Prod.fst e1).symm
    have h2 : B (J w).1 = A w.1 + w.2 := (congrArg Prod.snd e1).symm
    have hb1 : β x (A (J w).1) = -β x (B w.1) - β x (J w).2 := by
      have := congrArg (β x) h1; simp at this; linarith
    have hb2 : β x (B (J w).1) = β x (A w.1) + β x w.2 := by rw [h2]; simp
    rw [hQ, hQ, hb1, hb2]
    push_cast
    linear_combination (-((Real.pi : ℂ) * (β x (A w.1) : ℂ) + (Real.pi : ℂ) * (β x w.2 : ℂ))) * Complex.I_sq
  by_cases hs : (Metric.sphere (0 : V) 1).Nonempty
  · obtain ⟨u, hu, hmin⟩ := (isCompact_sphere (0 : V) 1).exists_isMinOn hs hcont.continuousOn
    have hu0 : u ≠ 0 := by
      intro h; rw [h] at hu; simp at hu
    refine ⟨Q, (Q u u).re, ?_, ?_, hsym', hfock⟩
    · rw [hre]; exact mul_pos Real.pi_pos (hBpos u hu0)
    · intro x
      by_cases hx : x = 0
      · subst hx; simp
      · have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
        have hu' : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : V) 1 := by
          rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
        have hm : (Q u u).re ≤ (Q (‖x‖⁻¹ • x) (‖x‖⁻¹ • x)).re := hmin hu'
        have key : Real.pi * -β x (B x) = ‖x‖ ^ 2 * (Real.pi * -β (‖x‖⁻¹ • x) (B (‖x‖⁻¹ • x))) := by
          rw [hscale]; field_simp
        rw [hre, hre] at hm
        rw [hre u, hre x, key]
        have := mul_le_mul_of_nonneg_left hm (sq_nonneg ‖x‖)
        linarith
  · refine ⟨Q, 1, one_pos, ?_, hsym', hfock⟩
    intro x
    by_cases hx : x = 0
    · subst hx; simp
    · exfalso
      apply hs
      refine ⟨‖x‖⁻¹ • x, ?_⟩
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_pos_iff.mpr hx).ne']
end GlobalTheory
