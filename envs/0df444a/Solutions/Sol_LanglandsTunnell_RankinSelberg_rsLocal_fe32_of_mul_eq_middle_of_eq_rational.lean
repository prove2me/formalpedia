-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.rsLocal_fe32_of_mul_eq_middle_of_eq_rational
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/6fd5fed8-a593-5dc5-8d8a-6ed3d9ca3f99

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_rsLocal_fe32_of_mul_eq_middle_of_eq_rational

set_option autoImplicit false

namespace MatchAlg

open Polynomial

theorem differentiable_const_cpow (N : ℕ) (hN : 1 < N) {g : ℂ → ℂ} (hg : Differentiable ℂ g) :
    Differentiable ℂ fun s : ℂ => (N : ℂ) ^ (g s) := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  exact fun s => (hg s).const_cpow (Or.inl hN0)

theorem differentiable_eval_comp (P : Polynomial ℂ) {g : ℂ → ℂ} (hg : Differentiable ℂ g) :
    Differentiable ℂ fun s : ℂ => P.eval (g s) :=
  (Polynomial.differentiable P).comp hg

theorem eq_zero_of_forall_lt_re (F : ℂ → ℂ) (hF : Differentiable ℂ F) (σ : ℝ)
    (h : ∀ s : ℂ, σ < s.re → F s = 0) : ∀ s : ℂ, F s = 0 := by
  have hA : AnalyticOnNhd ℂ F Set.univ := hF.differentiableOn.analyticOnNhd isOpen_univ
  set z₀ : ℂ := ((σ + 1 : ℝ) : ℂ) with hz₀
  have hopen : IsOpen {s : ℂ | σ < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmem : z₀ ∈ {s : ℂ | σ < s.re} := by
    show σ < z₀.re; simp only [hz₀, Complex.ofReal_re]; linarith
  have hev : F =ᶠ[nhds z₀] 0 :=
    Filter.eventuallyEq_of_mem (hopen.mem_nhds hmem) fun s hs => h s hs
  have := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ z₀) hev
  intro s
  exact this (Set.mem_univ s)

theorem eq_zero_of_forall_lt_re_one_sub (F : ℂ → ℂ) (hF : Differentiable ℂ F) (σ : ℝ)
    (h : ∀ s : ℂ, σ < (1 - s).re → F s = 0) : ∀ s : ℂ, F s = 0 := by
  have h' : ∀ s : ℂ, σ < s.re → F (1 - s) = 0 := fun s hs => h (1 - s) (by simpa using hs)
  have := eq_zero_of_forall_lt_re (fun s => F (1 - s)) (hF.comp (differentiable_const _ |>.sub differentiable_id)) σ h'
  intro s
  simpa using this (1 - s)

theorem countable_eval_cpow_eq_zero (N : ℕ) (hN : 1 < N) (q : Polynomial ℂ) (hq : q ≠ 0)
    (ℓ : ℂ → ℂ) (hℓ : Function.Injective ℓ) :
    {s : ℂ | q.eval ((N : ℂ) ^ (ℓ s)) = 0}.Countable := by
  have hNpos : 0 < N := by omega
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hNpos.ne'
  have hlog : Complex.log (N : ℂ) ≠ 0 := by
    rw [← Complex.natCast_log]
    exact_mod_cast (Real.log_pos (by exact_mod_cast hN)).ne'
  have hcpow : ∀ s : ℂ, (N : ℂ) ^ (ℓ s) = Complex.exp (Complex.log N * ℓ s) := fun s => by
    rw [Complex.cpow_def, if_neg hN0]
  have hsub : {s : ℂ | q.eval ((N : ℂ) ^ (ℓ s)) = 0} ⊆
      (fun s => Complex.log N * ℓ s) ⁻¹' (Complex.exp ⁻¹' {z : ℂ | q.eval z = 0}) := by
    intro s hs
    simpa [hcpow s] using hs
  refine Set.Countable.mono hsub ?_
  refine Set.Countable.preimage ?_ ?_
  · rw [Complex.countable_preimage_exp]
    exact (q.roots.toFinset.finite_toSet).countable.mono fun z hz => by
      simpa [Multiset.mem_toFinset, Polynomial.mem_roots hq] using hz
  · intro a b hab
    exact hℓ (mul_left_cancel₀ hlog hab)

end MatchAlg

open MatchAlg Polynomial in
theorem solution
    (N : ℕ) (hN : 1 < N) (Z D : ℂ → ℂ) (E Ed : Polynomial ℂ) (ε a₁ a₂ : ℂ)
    (p q pd qd : Polynomial ℂ) (σ₂ σ₃ : ℝ) (hq : q ≠ 0) (hqd : qd ≠ 0)
    (hZ : ∀ s : ℂ, σ₂ < s.re → Z s * q.eval ((N : ℂ) ^ (-s)) = p.eval ((N : ℂ) ^ (-s)))
    (hD : ∀ s : ℂ, σ₃ < (1 - s).re →
      D s * qd.eval ((N : ℂ) ^ (-(1 - s))) = pd.eval ((N : ℂ) ^ (-(1 - s))))

    (m₁ m₂ : Polynomial ℂ) (k : ℤ) (hm₂ : m₂ ≠ 0)
    (σP σD : ℝ)
    (hP : ∀ s : ℂ, σP < s.re →
      Z s * E.eval (a₁ * (N : ℂ) ^ (-(s + 1 / 2))) * E.eval (a₂ * (N : ℂ) ^ (-(s + 1 / 2))) *
          m₂.eval ((N : ℂ) ^ (-s)) =
        m₁.eval ((N : ℂ) ^ (-s)) * (N : ℂ) ^ ((k : ℂ) * s))
    (hDM : ∀ s : ℂ, σD < (1 - s).re →
      D s * Ed.eval (a₁⁻¹ * (N : ℂ) ^ (-(1 / 2 - s))) * Ed.eval (a₂⁻¹ * (N : ℂ) ^ (-(1 / 2 - s))) *
          m₂.eval ((N : ℂ) ^ (-s)) =
        ε ^ 2 * (m₁.eval ((N : ℂ) ^ (-s)) * (N : ℂ) ^ ((k : ℂ) * s))) :
    ∀ s : ℂ,
      pd.eval ((N : ℂ) ^ (-(1 - s))) * q.eval ((N : ℂ) ^ (-s)) *
          Ed.eval (a₁⁻¹ * (N : ℂ) ^ (-(1 / 2 - s))) *
          Ed.eval (a₂⁻¹ * (N : ℂ) ^ (-(1 / 2 - s))) =
        p.eval ((N : ℂ) ^ (-s)) * qd.eval ((N : ℂ) ^ (-(1 - s))) *
          E.eval (a₁ * (N : ℂ) ^ (-(s + 1 / 2))) *
          E.eval (a₂ * (N : ℂ) ^ (-(s + 1 / 2))) *
          ε ^ 2 := by
  have hNpos : 0 < N := by omega
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hNpos.ne'

  have d1 : Differentiable ℂ fun s : ℂ => (N : ℂ) ^ (-s) := differentiable_const_cpow N hN differentiable_neg
  have d2 : Differentiable ℂ fun s : ℂ => (N : ℂ) ^ (-(1 - s)) :=
    differentiable_const_cpow N hN ((differentiable_const _ |>.sub differentiable_id).neg)
  have d3 : Differentiable ℂ fun s : ℂ => (N : ℂ) ^ (-(1 / 2 - s)) :=
    differentiable_const_cpow N hN ((differentiable_const _ |>.sub differentiable_id).neg)
  have d4 : Differentiable ℂ fun s : ℂ => (N : ℂ) ^ (-(s + 1 / 2)) :=
    differentiable_const_cpow N hN ((differentiable_id.add (differentiable_const _)).neg)
  have d5 : Differentiable ℂ fun s : ℂ => (N : ℂ) ^ ((k : ℂ) * s) :=
    differentiable_const_cpow N hN ((differentiable_const _).mul differentiable_id)

  have hI : ∀ s : ℂ,
      p.eval ((N : ℂ) ^ (-s)) * E.eval (a₁ * (N : ℂ) ^ (-(s + 1 / 2))) * E.eval (a₂ * (N : ℂ) ^ (-(s + 1 / 2))) *
          m₂.eval ((N : ℂ) ^ (-s)) -
        q.eval ((N : ℂ) ^ (-s)) * (m₁.eval ((N : ℂ) ^ (-s)) * (N : ℂ) ^ ((k : ℂ) * s)) = 0 := by
    refine eq_zero_of_forall_lt_re _ ?_ (max σ₂ σP) ?_
    · have e1 := differentiable_eval_comp p d1
      have e2 := differentiable_eval_comp E ((differentiable_const a₁).mul d4)
      have e3 := differentiable_eval_comp E ((differentiable_const a₂).mul d4)
      have e4 := differentiable_eval_comp m₂ d1
      have e5 := differentiable_eval_comp q d1
      have e6 := differentiable_eval_comp m₁ d1
      exact (((e1.mul e2).mul e3).mul e4).sub (e5.mul (e6.mul d5))
    · intro s hs
      have e1 := hZ s (lt_of_le_of_lt (le_max_left _ _) hs)
      have e2 := hP s (lt_of_le_of_lt (le_max_right _ _) hs)
      linear_combination (-(E.eval (a₁ * (N : ℂ) ^ (-(s + 1 / 2))) * E.eval (a₂ * (N : ℂ) ^ (-(s + 1 / 2))) *
          m₂.eval ((N : ℂ) ^ (-s)))) * e1 + q.eval ((N : ℂ) ^ (-s)) * e2

  have hII : ∀ s : ℂ,
      pd.eval ((N : ℂ) ^ (-(1 - s))) * Ed.eval (a₁⁻¹ * (N : ℂ) ^ (-(1 / 2 - s))) *
          Ed.eval (a₂⁻¹ * (N : ℂ) ^ (-(1 / 2 - s))) * m₂.eval ((N : ℂ) ^ (-s)) -
        qd.eval ((N : ℂ) ^ (-(1 - s))) * (ε ^ 2 * (m₁.eval ((N : ℂ) ^ (-s)) * (N : ℂ) ^ ((k : ℂ) * s))) = 0 := by
    refine eq_zero_of_forall_lt_re_one_sub _ ?_ (max σ₃ σD) ?_
    · have e1 := differentiable_eval_comp pd d2
      have e2 := differentiable_eval_comp Ed ((differentiable_const a₁⁻¹).mul d3)
      have e3 := differentiable_eval_comp Ed ((differentiable_const a₂⁻¹).mul d3)
      have e4 := differentiable_eval_comp m₂ d1
      have e5 := differentiable_eval_comp qd d2
      have e6 := differentiable_eval_comp m₁ d1
      exact (((e1.mul e2).mul e3).mul e4).sub (e5.mul ((differentiable_const _).mul (e6.mul d5)))
    · intro s hs
      have e1 := hD s (lt_of_le_of_lt (le_max_left _ _) hs)
      have e2 := hDM s (lt_of_le_of_lt (le_max_right _ _) hs)
      linear_combination (-(Ed.eval (a₁⁻¹ * (N : ℂ) ^ (-(1 / 2 - s))) *
          Ed.eval (a₂⁻¹ * (N : ℂ) ^ (-(1 / 2 - s))) * m₂.eval ((N : ℂ) ^ (-s)))) * e1 +
        qd.eval ((N : ℂ) ^ (-(1 - s))) * e2

  let L : ℂ → ℂ := fun s =>
    pd.eval ((N : ℂ) ^ (-(1 - s))) * q.eval ((N : ℂ) ^ (-s)) *
      Ed.eval (a₁⁻¹ * (N : ℂ) ^ (-(1 / 2 - s))) * Ed.eval (a₂⁻¹ * (N : ℂ) ^ (-(1 / 2 - s)))
  let R : ℂ → ℂ := fun s =>
    p.eval ((N : ℂ) ^ (-s)) * qd.eval ((N : ℂ) ^ (-(1 - s))) *
      E.eval (a₁ * (N : ℂ) ^ (-(s + 1 / 2))) * E.eval (a₂ * (N : ℂ) ^ (-(s + 1 / 2))) * ε ^ 2

  have hGF : ∀ s : ℂ, m₂.eval ((N : ℂ) ^ (-s)) * (L s - R s) = 0 := by
    intro s
    have e1 := hI s
    have e2 := hII s
    simp only [L, R]
    linear_combination q.eval ((N : ℂ) ^ (-s)) * e2 - (qd.eval ((N : ℂ) ^ (-(1 - s))) * ε ^ 2) * e1

  set S : Set ℂ := {s : ℂ | m₂.eval ((N : ℂ) ^ (-s)) = 0} with hS
  have hSc : S.Countable := countable_eval_cpow_eq_zero N hN m₂ hm₂ (fun s => -s) neg_injective
  have hdense : Dense Sᶜ := Set.Countable.dense_compl ℂ hSc
  have hzero : Set.EqOn (fun s => L s - R s) (fun _ => 0) Sᶜ := by
    intro s hs
    have hs' : m₂.eval ((N : ℂ) ^ (-s)) ≠ 0 := by
      simpa only [hS, Set.mem_compl_iff, Set.mem_setOf_eq] using hs
    exact (mul_eq_zero.1 (hGF s)).resolve_left hs'
  have hcont : Continuous fun s => L s - R s := by
    simp only [L, R]
    have c1 := d1.continuous
    have c2 := d2.continuous
    have c3 := d3.continuous
    have c4 := d4.continuous
    fun_prop [Polynomial.continuous]
  have hall : Set.EqOn (fun s => L s - R s) (fun _ => 0) (closure Sᶜ) :=
    hzero.closure hcont continuous_const
  intro s
  have := hall (by rw [hdense.closure_eq]; exact Set.mem_univ s)
  exact sub_eq_zero.1 this

end S_LanglandsTunnell_RankinSelberg_rsLocal_fe32_of_mul_eq_middle_of_eq_rational
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_rsLocal_fe32_of_mul_eq_middle_of_eq_rational (solution)
