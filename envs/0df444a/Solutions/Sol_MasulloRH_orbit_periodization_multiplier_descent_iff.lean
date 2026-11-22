-- Prove2me | solution 1 for MasulloRH.orbit_periodization_multiplier_descent_iff
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T10:22:51.974184+00:00
-- url     : https://prove2.me/submissions/89c445ea-3768-41ad-9951-314ec20e9ba3

import Mathlib

theorem solution (G : Type*) [Group G] (D : Subgroup G) (m : G → ℂ) :
    let P : (G → ℂ) → G → ℂ := fun f x => ∑' d : D, f ((d : G) * x)
    (∀ (f : G → ℂ) (s : D), P (fun y => f ((s : G)*y)) = P f) ∧
    (∀ (f : G → ℂ) (s : D), P f ≠ 0 →
      (∀ y, m y * f y = f y) → (∀ y, m y * f ((s:G)*y) = 0) →
      ¬ ∃ T : (G → ℂ) → G → ℂ,
        T (P f) = P (fun y => m y * f y) ∧
        T (P (fun y => f ((s:G)*y))) = P (fun y => m y * f ((s:G)*y))) ∧
    ((∃ T : (G → ℂ) → G → ℂ, ∀ f : G → ℂ, (Function.support f).Finite →
        T (P f) = P (fun y => m y * f y)) ↔ ∀ (d : D) (x : G), m ((d:G)*x) = m x) := by
  classical
  let P : (G → ℂ) → G → ℂ := fun f x => ∑' d : D, f ((d : G)*x)
  have peri (f : G → ℂ) (s : D) : P (fun y => f ((s:G)*y)) = P f := by
    funext x
    have e := (Equiv.mulLeft s).tsum_eq (fun d : D => f ((d:G)*x))
    change (∑' d : D, f (((s : G)*(d : G))*x)) = ∑' d : D, f ((d:G)*x) at e
    simpa only [P,mul_assoc] using e
  refine ⟨peri, ?_, ?_⟩
  · intro f s hnon hfix hkill ⟨T,h₁,h₂⟩
    change T (P f) = _ at h₁
    change T (P (fun y => f ((s:G)*y))) = _ at h₂
    rw [peri] at h₂
    have eqn := h₁.symm.trans h₂
    apply hnon
    change P (fun y => m y * f y) = P (fun y => m y * f ((s:G)*y)) at eqn
    funext x
    simpa only [hfix,hkill,P,tsum_zero,Pi.zero_apply] using congrFun eqn x
  · constructor
    · rintro ⟨T,hT⟩ d x
      let δ (z y : G) : ℂ := if y = z then 1 else 0
      have hfin (z : G) : (Function.support (δ z)).Finite := by
        apply (Set.finite_singleton z).subset
        intro y hy
        by_contra h
        exact hy (if_neg (by simpa using h))
      have trans : P (δ ((d:G)*x)) = P (δ x) := by
        have hh : δ ((d:G)*x) = fun y => δ x (((d⁻¹:D):G)*y) := by
          funext y
          simp only [δ, Subgroup.coe_inv, inv_mul_eq_iff_eq_mul]
        rw [hh]
        exact peri (δ x) (d⁻¹)
      have eqn := congrFun (((hT _ (hfin ((d:G)*x))).symm.trans
        ((congrArg T trans).trans (hT _ (hfin x))))) x
      have val (s : D) : P (fun y => m y * δ ((s:G)*x) y) x = m ((s:G)*x) := by
        change (∑' r : D, m ((r:G)*x) * δ ((s:G)*x) ((r:G)*x)) = _
        rw [tsum_eq_single s]
        · simp [δ]
        · intro r hr
          have he : (r:G)*x ≠ (s:G)*x := fun h => hr (Subtype.ext (mul_right_cancel h))
          simp [δ,he]
      change P (fun y => m y * δ ((d:G)*x) y) x = P (fun y => m y * δ x y) x at eqn
      rw [val d] at eqn
      simpa using eqn.trans (by simpa using val (1:D))
    · intro hm
      refine ⟨fun g x => m x * g x, ?_⟩
      intro f hf
      funext x
      change m x * (∑' d : D, f ((d:G)*x)) = ∑' d : D, m ((d:G)*x) * f ((d:G)*x)
      simp only [hm, tsum_mul_left]
