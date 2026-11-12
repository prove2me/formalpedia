-- Prove2me | solution 1 for HDXConc.eq_13
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:38:09.317743+00:00
-- url     : https://prove2.me/submissions/e0354105-0df2-4800-b0ca-a09f54c81646

import Mathlib
import Definitions.Def_SteurerHDX_IsPure
import Definitions.Def_HDXConc_IsTopDensity
import Definitions.Def_HDXConc_IsTopLinkExpander
import Definitions.Def_HDXConc_logMGF
import Theorems.Thm_HDXConc_tilted_variance_le

section
set_option autoImplicit false
namespace HDXConc.Dev.Eq13
open HDXConc

theorem taylor_pos (ψ : ℝ → ℝ) (hs : ContDiff ℝ 2 ψ) (h0 : ψ 0 = 0) (h1 : deriv ψ 0 = 0)
    (t : ℝ) (ht : 0 ≤ t) : ∃ θ : ℝ, θ ∈ Set.Icc (0:ℝ) 1 ∧
      ψ t = (1 / 2) * t ^ 2 * iteratedDeriv 2 ψ (θ * t) := by
  rcases ht.eq_or_lt with h | h
  · subst h; exact ⟨0, by simp, by simp [h0]⟩
  · have hne : (0:ℝ) ≠ t := h.ne
    have hu : Set.uIcc (0:ℝ) t = Set.Icc 0 t := Set.uIcc_of_le ht
    have hu' : Set.uIoo (0:ℝ) t = Set.Ioo 0 t := Set.uIoo_of_le ht
    have hc : ∀ n : ℕ, n ≤ 2 → ContDiff ℝ n ψ := fun n hn => hs.of_le (by exact_mod_cast hn)
    have hU : UniqueDiffOn ℝ (Set.Icc (0:ℝ) t) := uniqueDiffOn_Icc h
    have hde : ∀ (k : ℕ), k ≤ 2 → ∀ (x : ℝ), x ∈ Set.Icc (0:ℝ) t →
        iteratedDerivWithin k ψ (Set.Icc 0 t) x = iteratedDeriv k ψ x := fun k hk x hx =>
      iteratedDerivWithin_eq_iteratedDeriv hU ((hc k hk).contDiffAt) hx
    have hd1 : Differentiable ℝ (deriv ψ) := by
      have := (contDiff_succ_iff_deriv (n := 1) (f := ψ)).1 (by exact_mod_cast hs)
      exact (this.2.2).differentiable (by simp)
    obtain ⟨x', hx', hr⟩ := taylor_mean_remainder_lagrange (n := 1) hne
      (by rw [hu]; exact (hc 1 (by norm_num)).contDiffOn) (by
        rw [hu, hu']
        have : DifferentiableOn ℝ (deriv ψ) (Set.Icc 0 t) := hd1.differentiableOn
        refine (this.congr (fun x hx => ?_)).mono Set.Ioo_subset_Icc_self
        rw [hde 1 (by norm_num) x hx, iteratedDeriv_one])
    rw [hu'] at hx'
    rw [hu, taylor_within_apply] at hr
    have hx'' : x' ∈ Set.Icc (0:ℝ) t := Set.Ioo_subset_Icc_self hx'
    rw [hde 2 le_rfl x' hx''] at hr
    have e0 : iteratedDerivWithin 0 ψ (Set.Icc 0 t) 0 = 0 := by
      rw [iteratedDerivWithin_zero]; exact h0
    have e1 : iteratedDerivWithin 1 ψ (Set.Icc 0 t) 0 = 0 := by
      rw [hde 1 (by norm_num) 0 ⟨le_rfl, ht⟩, iteratedDeriv_one]; exact h1
    refine ⟨x' / t, ⟨div_nonneg hx'.1.le ht, (div_le_one h).2 hx'.2.le⟩, ?_⟩
    rw [div_mul_cancel₀ _ h.ne']
    simp [Finset.sum_range_succ, e0, e1] at hr
    linarith


section gen
variable {ι : Type*} (S : Finset ι) (p a : ι → ℝ)

noncomputable def G (k : ℕ) (t : ℝ) : ℝ := ∑ σ ∈ S, p σ * a σ ^ k * Real.exp (t * a σ)

theorem hasDerivAt_G (k : ℕ) (t : ℝ) : HasDerivAt (G S p a k) (G S p a (k+1) t) t := by
  unfold G
  have : HasDerivAt (fun t => ∑ σ ∈ S, p σ * a σ ^ k * Real.exp (t * a σ))
      (∑ σ ∈ S, p σ * a σ ^ k * (Real.exp (t * a σ) * a σ)) t := by
    refine HasDerivAt.fun_sum (fun σ _ => ?_)
    have h := ((hasDerivAt_id t).mul_const (a σ)).exp.const_mul (p σ * a σ ^ k)
    simpa using h
  refine this.congr_deriv (Finset.sum_congr rfl (fun σ _ => ?_))
  ring

theorem contDiff_G (k : ℕ) : ContDiff ℝ ⊤ (G S p a k) := by
  unfold G
  fun_prop


variable {S p a}

theorem G0_pos (hp : ∀ σ ∈ S, 0 < p σ) (hS : S.Nonempty) (t : ℝ) : 0 < G S p a 0 t := by
  unfold G
  exact Finset.sum_pos (fun σ hσ => by have := hp σ hσ; positivity) hS

theorem hasDerivAt_psi (hp : ∀ σ ∈ S, 0 < p σ) (hS : S.Nonempty) (t : ℝ) :
    HasDerivAt (fun t => Real.log (G S p a 0 t)) (G S p a 1 t / G S p a 0 t) t :=
  (hasDerivAt_G S p a 0 t).log (G0_pos hp hS t).ne'

theorem deriv_psi (hp : ∀ σ ∈ S, 0 < p σ) (hS : S.Nonempty) :
    deriv (fun t => Real.log (G S p a 0 t)) = fun t => G S p a 1 t / G S p a 0 t :=
  funext fun t => (hasDerivAt_psi hp hS t).deriv

theorem iter2_psi (hp : ∀ σ ∈ S, 0 < p σ) (hS : S.Nonempty) (t : ℝ) :
    iteratedDeriv 2 (fun t => Real.log (G S p a 0 t)) t
      = G S p a 2 t / G S p a 0 t - (G S p a 1 t / G S p a 0 t) ^ 2 := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, deriv_psi hp hS]
  have h0 := G0_pos (a := a) hp hS t
  have := ((hasDerivAt_G S p a 1 t).div (hasDerivAt_G S p a 0 t) h0.ne')
  have e : deriv (fun t => G S p a 1 t / G S p a 0 t) t = _ := this.deriv
  rw [e]
  simp only [zero_add, Nat.reduceAdd]
  field_simp

theorem contDiff_psi (hp : ∀ σ ∈ S, 0 < p σ) (hS : S.Nonempty) :
    ContDiff ℝ 2 (fun t => Real.log (G S p a 0 t)) := by
  have := (contDiff_G S p a 0).of_le (show (2 : WithTop ℕ∞) ≤ ⊤ from le_top)
  exact this.log (fun t => (G0_pos hp hS t).ne')

end gen

section bridge
variable {V : Type*}

theorem topVar_tilt_eq {X : Finset (Finset V)} {d : ℕ} {π : Finset V → ℝ} (f : V → ℝ)
    (hπ : IsTopDensity X d π) (t : ℝ) :
    topVar X d (tilt X d π f t) (topSum f)
      = iteratedDeriv 2 (logMGF X d π f) t := by
  set S := SteurerHDX.faces X d with hSdef
  set m := topMean X d π (topSum f) with hm
  set a : Finset V → ℝ := fun σ => topSum f σ - m with ha
  have hS : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have := hπ.sum_eq_one
    rw [← hSdef, h] at this
    simp at this
  have hp : ∀ σ ∈ S, 0 < π σ := hπ.pos
  have hψ : logMGF X d π f = fun t => Real.log (G S π a 0 t) := by
    funext t
    simp [logMGF, G, ha, hSdef, hm]
  rw [hψ, iter2_psi hp hS]
  have h0 := G0_pos (a := a) hp hS t
  set Z := ∑ σ ∈ S, π σ * Real.exp (t * topSum f σ) with hZ
  have hZG : Z = G S π a 0 t * Real.exp (t * m) := by
    simp only [hZ, G, Finset.sum_mul, ha]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [pow_zero, mul_one, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hw : ∀ σ ∈ S, tilt X d π f t σ = π σ * Real.exp (t * a σ) / G S π a 0 t := by
    intro σ _
    have : tilt X d π f t σ = π σ * Real.exp (t * topSum f σ) / Z := rfl
    rw [this, hZG]
    have : Real.exp (t * topSum f σ) = Real.exp (t * a σ) * Real.exp (t * m) := by
      rw [← Real.exp_add]; congr 1; simp only [ha]; ring
    rw [this]
    have := Real.exp_pos (t * m)
    field_simp
  set c := G S π a 1 t / G S π a 0 t with hc
  have hsum1 : ∑ σ ∈ S, tilt X d π f t σ = 1 := by
    rw [Finset.sum_congr rfl hw, ← Finset.sum_div]
    have : ∑ σ ∈ S, π σ * Real.exp (t * a σ) = G S π a 0 t := by
      simp [G]
    rw [this, div_self h0.ne']
  have hmean : topMean X d (tilt X d π f t) (topSum f) = c + m := by
    unfold topMean
    rw [← hSdef]
    have : ∀ σ ∈ S, tilt X d π f t σ * topSum f σ
        = tilt X d π f t σ * a σ + m * tilt X d π f t σ := by
      intro σ _; simp only [ha]; ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, ← Finset.mul_sum, hsum1]
    have : ∑ σ ∈ S, tilt X d π f t σ * a σ = c := by
      rw [Finset.sum_congr rfl (fun σ hσ => by rw [hw σ hσ]), hc]
      simp only [G, pow_one, div_mul_eq_mul_div, ← Finset.sum_div]
      congr 1
      refine Finset.sum_congr rfl (fun σ _ => by ring)
    rw [this]; ring
  have hvar : topVar X d (tilt X d π f t) (topSum f)
      = ∑ σ ∈ S, tilt X d π f t σ * (a σ - c) ^ 2 := by
    unfold topVar
    rw [hmean, ← hSdef]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    simp only [ha]; ring
  rw [hvar, Finset.sum_congr rfl (fun σ hσ => by rw [hw σ hσ])]
  have : ∀ σ ∈ S, π σ * Real.exp (t * a σ) / G S π a 0 t * (a σ - c) ^ 2
      = (π σ * a σ ^ 2 * Real.exp (t * a σ) - 2 * c * (π σ * a σ ^ 1 * Real.exp (t * a σ))
        + c ^ 2 * (π σ * a σ ^ 0 * Real.exp (t * a σ))) / G S π a 0 t := by
    intro σ _; ring
  rw [Finset.sum_congr rfl this, ← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]
  change (G S π a 2 t - 2 * c * G S π a 1 t + c ^ 2 * G S π a 0 t) / G S π a 0 t = _
  rw [hc]
  field_simp
  ring

theorem psi_zero {X : Finset (Finset V)} {d : ℕ} {π : Finset V → ℝ} (f : V → ℝ)
    (hπ : IsTopDensity X d π) : logMGF X d π f 0 = 0 ∧ deriv (logMGF X d π f) 0 = 0 := by
  set S := SteurerHDX.faces X d with hSdef
  set m := topMean X d π (topSum f) with hm
  set a : Finset V → ℝ := fun σ => topSum f σ - m with ha
  have hS : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have := hπ.sum_eq_one
    rw [← hSdef, h] at this
    simp at this
  have hp : ∀ σ ∈ S, 0 < π σ := hπ.pos
  have hψ : logMGF X d π f = fun t => Real.log (G S π a 0 t) := by
    funext t
    simp [logMGF, G, ha, hSdef, hm]
  have hG0 : G S π a 0 0 = 1 := by simpa [G] using hπ.sum_eq_one
  have hG1 : G S π a 1 0 = 0 := by
    have : ∑ σ ∈ S, π σ * (topSum f σ - m) = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
      have : ∑ σ ∈ S, π σ * topSum f σ = m := rfl
      have h1 : ∑ σ ∈ S, π σ = 1 := hπ.sum_eq_one
      rw [this, h1]; ring
    simpa [G, ha] using this
  rw [hψ]
  refine ⟨by simp [hG0], ?_⟩
  rw [deriv_psi hp hS]
  simp [hG0, hG1]

theorem contDiff_logMGF {X : Finset (Finset V)} {d : ℕ} {π : Finset V → ℝ} (f : V → ℝ)
    (hπ : IsTopDensity X d π) : ContDiff ℝ 2 (logMGF X d π f) := by
  set S := SteurerHDX.faces X d with hSdef
  set m := topMean X d π (topSum f) with hm
  set a : Finset V → ℝ := fun σ => topSum f σ - m with ha
  have hS : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have := hπ.sum_eq_one
    rw [← hSdef, h] at this
    simp at this
  have hψ : logMGF X d π f = fun t => Real.log (G S π a 0 t) := by
    funext t
    simp [logMGF, G, ha, hSdef, hm]
  rw [hψ]
  exact contDiff_psi hπ.pos hS

end bridge

end HDXConc.Dev.Eq13

namespace HDXConc
open HDXConc.Dev.Eq13 in
theorem chk_eq_13 {V : Type*} [Fintype V] [DecidableEq V] {d : ℕ} (hd : 2 ≤ d) {η : ℝ} (hη0 : 0 < η)
    (hη1 : η ≤ 1) {X : Finset (Finset V)} {π : Finset V → ℝ} (hX : SteurerHDX.IsPure X d)
    (hπ : IsTopDensity X d π) (hexp : IsTopLinkExpander X d π ((1 - η) / ((d : ℝ) - 1)))
    (f : V → ℝ) (hf : ∀ v, ({v} : Finset V) ∈ X → 0 ≤ f v ∧ f v ≤ 1) {t : ℝ} (ht : |t| ≤ η / 2) :
    (∃ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 ∧
      logMGF X d π f t = (1 / 2) * t ^ 2 * iteratedDeriv 2 (logMGF X d π f) (θ * t)) ∧
    logMGF X d π f t ≤ (d : ℝ) * t ^ 2 / (4 * η) := by
  have h0 := psi_zero (X := X) (d := d) f hπ
  have hc := contDiff_logMGF (X := X) (d := d) f hπ
  have hvar : ∀ θ : ℝ, θ ∈ Set.Icc (0:ℝ) 1 → iteratedDeriv 2 (logMGF X d π f) (θ * t) ≤ (d : ℝ) / (2 * η) := by
    intro θ hθ
    rw [← topVar_tilt_eq f hπ]
    refine tilted_variance_le hd hη0 hη1 hX hπ hexp f hf ?_
    rw [abs_mul, abs_of_nonneg hθ.1]
    calc θ * |t| ≤ 1 * |t| := by gcongr; exact hθ.2
      _ ≤ η / 2 := by simpa using ht
  have hex : ∃ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 ∧
      logMGF X d π f t = (1 / 2) * t ^ 2 * iteratedDeriv 2 (logMGF X d π f) (θ * t) := by
    rcases le_total 0 t with h | h
    · exact taylor_pos _ hc h0.1 h0.2 t h
    · set ψ' : ℝ → ℝ := fun s => logMGF X d π f (-s) with hψ'
      have hc' : ContDiff ℝ 2 ψ' := hc.comp contDiff_neg
      have e1 : ψ' 0 = 0 := by simp [hψ', h0.1]
      have e2 : deriv ψ' 0 = 0 := by
        have := deriv_comp_neg (logMGF X d π f) 0
        simp only [hψ']
        rw [this]; simp [h0.2]
      obtain ⟨θ, hθ, he⟩ := taylor_pos ψ' hc' e1 e2 (-t) (by linarith)
      refine ⟨θ, hθ, ?_⟩
      have h2 : iteratedDeriv 2 ψ' (θ * -t) = iteratedDeriv 2 (logMGF X d π f) (θ * t) := by
        have := iteratedDeriv_comp_neg 2 (logMGF X d π f) (θ * -t)
        simp only [hψ']
        rw [this]; simp
      rw [h2] at he
      simpa [hψ'] using he
  refine ⟨hex, ?_⟩
  obtain ⟨θ, hθ, he⟩ := hex
  rw [he]
  have := hvar θ hθ
  have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
  calc (1 / 2) * t ^ 2 * iteratedDeriv 2 (logMGF X d π f) (θ * t)
      ≤ (1 / 2) * t ^ 2 * ((d : ℝ) / (2 * η)) := by gcongr
    _ = (d : ℝ) * t ^ 2 / (4 * η) := by field_simp; ring
end HDXConc
end

theorem solution : type_of% @HDXConc.chk_eq_13 := @HDXConc.chk_eq_13
