-- Prove2me | solution 1 for GlobalTheory.NonUnitShift.isUnit_aeval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:13:33.278809+00:00
-- url     : https://prove2.me/submissions/d99a3d7a-8df6-46c8-b0f5-57570dcc1efa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LinearIndependentResolvent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NonUnitShift
open Polynomial
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.NonUnitShift
theorem _root_.solution (T : Module.End ℂ V)
    (h : ∀ c : ℂ, IsUnit (T - algebraMap ℂ (Module.End ℂ V) c)) :
    ∀ (n : ℕ) (p : ℂ[X]), p.natDegree = n → p ≠ 0 → IsUnit (aeval T p) := by
  intro n
  induction n with
  | zero =>
    intro p hp hp0
    have hc : p.coeff 0 ≠ 0 := by
      intro h0
      apply hp0
      rw [Polynomial.eq_C_of_natDegree_eq_zero hp, h0, map_zero]
    rw [Polynomial.eq_C_of_natDegree_eq_zero hp, Polynomial.aeval_C]
    exact (isUnit_iff_ne_zero.2 hc).map (algebraMap ℂ (Module.End ℂ V))
  | succ n ih =>
    intro p hp hp0
    have hdeg : 0 < p.degree := by
      rw [Polynomial.degree_eq_natDegree hp0, hp]
      exact_mod_cast Nat.succ_pos n
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_root p hdeg.ne'
    obtain ⟨q, hq⟩ := Polynomial.dvd_iff_isRoot.2 hr
    have hq0 : q ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hq
      exact hp0 hq
    have hqdeg : q.natDegree = n := by
      have h2 := congrArg Polynomial.natDegree hq
      rw [Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero r) hq0, Polynomial.natDegree_X_sub_C, hp] at h2
      omega
    rw [hq, map_mul]
    refine IsUnit.mul ?_ (ih q hqdeg hq0)
    simpa [map_sub] using h r
end GlobalTheory.NonUnitShift
