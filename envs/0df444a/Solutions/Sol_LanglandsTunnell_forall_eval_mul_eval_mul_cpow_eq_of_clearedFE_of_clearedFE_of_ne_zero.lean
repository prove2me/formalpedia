-- Prove2me | solution 1 for LanglandsTunnell.forall_eval_mul_eval_mul_cpow_eq_of_clearedFE_of_clearedFE_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/b7501cb2-c1c4-5ea9-b28a-6a7f950d9fc2

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_forall_eval_mul_eval_mul_cpow_eq_of_clearedFE_of_clearedFE_of_ne_zero

set_option autoImplicit false

namespace LanglandsTunnell
namespace RatAux

open Filter Topology

theorem forall_eq_zero_or_of_mul {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (h : ∀ s, f s * g s = 0) : (∀ s, f s = 0) ∨ (∀ s, g s = 0) := by
  by_contra hcon
  rw [not_or, not_forall, not_forall] at hcon
  obtain ⟨⟨s₁, hs₁⟩, ⟨s₂, hs₂⟩⟩ := hcon
  have hfa : AnalyticOnNhd ℂ f Set.univ := hf.differentiableOn.analyticOnNhd isOpen_univ
  have hev : ∀ᶠ z in 𝓝 s₂, g z ≠ 0 := hg.continuous.continuousAt.eventually_ne hs₂
  have hev' : ∀ᶠ z in 𝓝[≠] s₂, f z = 0 := by
    refine (hev.filter_mono nhdsWithin_le_nhds).mono fun z hz => ?_
    rcases mul_eq_zero.mp (h z) with h1 | h1
    · exact h1
    · exact absurd h1 hz
  have := hfa.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ (Set.mem_univ s₂) hev'.frequently
  exact hs₁ (this (Set.mem_univ s₁))

theorem differentiable_cpow (N : ℕ) (hN : 1 < N) {g : ℂ → ℂ} (hg : Differentiable ℂ g) :
    Differentiable ℂ (fun s => (N : ℂ) ^ g s) := by
  have hNz : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  simp_rw [Complex.cpow_def_of_ne_zero hNz]
  exact (hg.const_mul _).cexp

theorem differentiable_eval_cpow (N : ℕ) (hN : 1 < N) (R : Polynomial ℂ) {g : ℂ → ℂ} (hg : Differentiable ℂ g) :
    Differentiable ℂ (fun s => R.eval ((N : ℂ) ^ g s)) :=
  (Polynomial.differentiable R).comp (differentiable_cpow N hN hg)

theorem injective_natCast_pow (N : ℕ) (hN : 1 < N) : Function.Injective (fun n : ℕ => ((N : ℂ) ^ n)) := by
  intro a b h
  have : ((N ^ a : ℕ) : ℂ) = ((N ^ b : ℕ) : ℂ) := by push_cast; exact h
  exact Nat.pow_right_injective (by omega : 2 ≤ N) (Nat.cast_injective this)

theorem not_forall_eval_cpow_eq_zero (N : ℕ) (hN : 1 < N) (R : Polynomial ℂ) (hR : R ≠ 0) :
    ¬ ∀ s : ℂ, R.eval ((N : ℂ) ^ s) = 0 := by
  intro h
  apply hR
  apply Polynomial.eq_zero_of_infinite_isRoot
  refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective (injective_natCast_pow N hN))
  rintro _ ⟨n, rfl⟩
  show R.eval ((N : ℂ) ^ n) = 0
  rw [← Complex.cpow_natCast]
  exact h n

theorem not_forall_eval_cpow_neg_eq_zero (N : ℕ) (hN : 1 < N) (R : Polynomial ℂ) (hR : R ≠ 0) :
    ¬ ∀ s : ℂ, R.eval ((N : ℂ) ^ (-s)) = 0 := by
  intro h
  apply not_forall_eval_cpow_eq_zero N hN R hR
  intro s
  have := h (-s)
  rwa [neg_neg] at this

theorem not_forall_cpow_mul_neg_eq_zero (N : ℕ) (m : ℤ) : ¬ ∀ s : ℂ, (N : ℂ) ^ ((m : ℂ) * -s) = 0 := by
  intro h
  have := h 0
  rw [neg_zero, mul_zero, Complex.cpow_zero] at this
  exact one_ne_zero this

end LanglandsTunnell.RatAux

open LanglandsTunnell.RatAux in
theorem solution
    (N : ℕ) (hN : 1 < N)
    (RA₁ RA₂ RB₁ RB₂ : Polynomial ℂ) (rA rB : ℤ)
    (P Pd Q Qd : Polynomial ℂ) (m md : ℤ) (hP : P ≠ 0) (hQd : Qd ≠ 0)
    (hA : ∀ s : ℂ, (RA₂).eval ((N : ℂ) ^ s) * (((N : ℂ) ^ ((md : ℂ) * s)) * Pd.eval ((N : ℂ) ^ (-s))) * Q.eval ((N : ℂ) ^ s) =
          ((RA₁).eval ((N : ℂ) ^ s) * (N : ℂ) ^ ((rA : ℂ) * s)) * (((N : ℂ) ^ ((m : ℂ) * (-s))) * P.eval ((N : ℂ) ^ s)) * Qd.eval ((N : ℂ) ^ (-s)))
    (hB : ∀ s : ℂ, (RB₂).eval ((N : ℂ) ^ s) * (((N : ℂ) ^ ((md : ℂ) * s)) * Pd.eval ((N : ℂ) ^ (-s))) * Q.eval ((N : ℂ) ^ s) =
          ((RB₁).eval ((N : ℂ) ^ s) * (N : ℂ) ^ ((rB : ℂ) * s)) * (((N : ℂ) ^ ((m : ℂ) * (-s))) * P.eval ((N : ℂ) ^ s)) * Qd.eval ((N : ℂ) ^ (-s))) :
    ∀ s : ℂ, RB₂.eval ((N : ℂ) ^ s) * (RA₁.eval ((N : ℂ) ^ s) * (N : ℂ) ^ ((rA : ℂ) * s)) =
      RA₂.eval ((N : ℂ) ^ s) * (RB₁.eval ((N : ℂ) ^ s) * (N : ℂ) ^ ((rB : ℂ) * s)) := by
  have hF : Differentiable ℂ (fun s : ℂ => RB₂.eval ((N : ℂ) ^ s) * (RA₁.eval ((N : ℂ) ^ s) * (N : ℂ) ^ ((rA : ℂ) * s)) -
      RA₂.eval ((N : ℂ) ^ s) * (RB₁.eval ((N : ℂ) ^ s) * (N : ℂ) ^ ((rB : ℂ) * s))) :=
    ((differentiable_eval_cpow N hN RB₂ differentiable_id).mul
      ((differentiable_eval_cpow N hN RA₁ differentiable_id).mul (differentiable_cpow N hN (differentiable_id.const_mul _)))).sub
    ((differentiable_eval_cpow N hN RA₂ differentiable_id).mul
      ((differentiable_eval_cpow N hN RB₁ differentiable_id).mul (differentiable_cpow N hN (differentiable_id.const_mul _))))
  have h1 : Differentiable ℂ (fun s : ℂ => (N : ℂ) ^ ((m : ℂ) * -s)) := differentiable_cpow N hN (differentiable_id.neg.const_mul _)
  have h2 : Differentiable ℂ (fun s : ℂ => P.eval ((N : ℂ) ^ s)) := differentiable_eval_cpow N hN P differentiable_id
  have h3 : Differentiable ℂ (fun s : ℂ => Qd.eval ((N : ℂ) ^ (-s))) := differentiable_eval_cpow N hN Qd differentiable_id.neg
  have hFC : ∀ s : ℂ, (RB₂.eval ((N : ℂ) ^ s) * (RA₁.eval ((N : ℂ) ^ s) * (N : ℂ) ^ ((rA : ℂ) * s)) -
      RA₂.eval ((N : ℂ) ^ s) * (RB₁.eval ((N : ℂ) ^ s) * (N : ℂ) ^ ((rB : ℂ) * s))) *
      (((N : ℂ) ^ ((m : ℂ) * -s) * P.eval ((N : ℂ) ^ s)) * Qd.eval ((N : ℂ) ^ (-s))) = 0 := fun s => by
    linear_combination (-(RB₂.eval ((N : ℂ) ^ s))) * hA s + (RA₂.eval ((N : ℂ) ^ s)) * hB s
  rcases forall_eq_zero_or_of_mul hF ((h1.mul h2).mul h3) hFC with h | h
  · intro s; exact sub_eq_zero.mp (h s)
  · exfalso
    rcases forall_eq_zero_or_of_mul (h1.mul h2) h3 h with h' | h'
    · rcases forall_eq_zero_or_of_mul h1 h2 h' with h'' | h''
      · exact not_forall_cpow_mul_neg_eq_zero N m h''
      · exact not_forall_eval_cpow_eq_zero N hN P hP h''
    · exact not_forall_eval_cpow_neg_eq_zero N hN Qd hQd h'

end S_LanglandsTunnell_forall_eval_mul_eval_mul_cpow_eq_of_clearedFE_of_clearedFE_of_ne_zero
end P2MW
export P2MW.S_LanglandsTunnell_forall_eval_mul_eval_mul_cpow_eq_of_clearedFE_of_clearedFE_of_ne_zero (solution)
