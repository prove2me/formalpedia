-- Prove2me | solution 1 for KonyaginUnitVectors.Alon.fourier_system
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T14:26:58.627497+00:00
-- url     : https://prove2.me/submissions/059ea614-1073-4ccd-af73-ca0c84afebca

import Mathlib
import Definitions.Def_KonyaginUnitVectors_AlonConstruction

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
Fourier construction of the vector system (Alon-type construction over `GF(2^k)`): for `S ⊆ F³` and `κ` with
`1 + κ Σ_{s ∈ S} ψ_w(s) ≥ 0` for all `w`, the vectors `u_g(w) = √((1 + κ λ_w)/n) ψ_w(g)` have Gram matrix
`[g = h] + κ [g + h ∈ S]` and `‖Σ_g u_g‖² = n (1 + κ |S|)`, `n = q³`.
-/

namespace KonyaginUnitVectors.Alon

section aux

open scoped Classical

variable (F : Type*) [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

omit [Fintype F] [CharP F 2] in
theorem pk_psi_zero : psi F 0 = 1 := by simp [psi]

theorem pk_psi_add (y z : F) : psi F (y + z) = psi F y * psi F z := by
  unfold psi
  rw [map_add]
  generalize Algebra.trace (ZMod 2) F y = a
  generalize Algebra.trace (ZMod 2) F z = b
  have h2 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rcases h2 a with rfl | rfl <;> rcases h2 b with rfl | rfl <;> simp [h11]

theorem pk_exists_trace_ne_zero (z : F) (hz : z ≠ 0) :
    ∃ b : F, Algebra.trace (ZMod 2) F (b * z) ≠ 0 := by
  have h := (traceForm_nondegenerate (ZMod 2) F).1 z
  by_contra hcon
  push Not at hcon
  apply hz
  apply h
  intro n
  simpa [Algebra.traceForm_apply, mul_comm] using hcon n

theorem pk_sum_psi_mul (z : F) :
    ∑ x : F, psi F (x * z) = if z = 0 then (Fintype.card F : ℝ) else 0 := by
  by_cases hz : z = 0
  · simp [hz, pk_psi_zero]
  · obtain ⟨b, hb⟩ := pk_exists_trace_ne_zero F z hz
    have hpb : psi F (b * z) = -1 := by unfold psi; rw [if_neg hb]
    have h1 : ∑ x : F, psi F (x * z) = - ∑ x : F, psi F (x * z) := by
      calc ∑ x : F, psi F (x * z) = ∑ x : F, psi F ((x + b) * z) :=
            (Equiv.sum_comp (Equiv.addRight b) (fun x => psi F (x * z))).symm
        _ = ∑ x : F, psi F (x * z) * psi F (b * z) := by
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [add_mul, pk_psi_add]
        _ = - ∑ x : F, psi F (x * z) := by
            rw [← Finset.sum_mul, hpb]; ring
    rw [if_neg hz]
    linarith

theorem pk_card_pos : (0 : ℝ) < (Fintype.card F : ℝ) := by
  exact_mod_cast Fintype.card_pos

/-- In `F × F × F` (characteristic 2): `a + b = 0 ↔ a = b`. -/
theorem pk_add_eq_zero_iff_G (a b : F × F × F) : a + b = 0 ↔ a = b := by
  have hneg : ∀ x : F × F × F, -x = x := by
    intro x
    ext <;> simp [CharTwo.neg_eq]
  rw [add_eq_zero_iff_eq_neg, hneg]

theorem pk_chi_add_right (w g h : F × F × F) : chi F w (g + h) = chi F w g * chi F w h := by
  unfold chi
  rw [← pk_psi_add]
  congr 1
  simp only [Prod.fst_add, Prod.snd_add]
  ring

theorem pk_sum_chi (g : F × F × F) :
    ∑ w : F × F × F, chi F w g = if g = 0 then (Fintype.card F : ℝ) ^ 3 else 0 := by
  obtain ⟨g1, g2, g3⟩ := g
  have e : ∀ w : F × F × F, chi F w (g1, g2, g3) =
      psi F (w.1 * g1) * psi F (w.2.1 * g2) * psi F (w.2.2 * g3) := by
    intro w
    unfold chi
    simp only
    rw [pk_psi_add, pk_psi_add]
  simp_rw [e]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  rw [pk_sum_psi_mul, pk_sum_psi_mul, pk_sum_psi_mul]
  by_cases h1 : g1 = 0 <;> by_cases h2 : g2 = 0 <;> by_cases h3 : g3 = 0 <;>
    simp [h1, h2, h3, Prod.ext_iff] <;> ring

end aux

end KonyaginUnitVectors.Alon

open KonyaginUnitVectors.Alon

open Classical in
theorem solution (F : Type*) [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
    (S : Finset (F × F × F)) (κ : ℝ)
    (hκ : ∀ w : F × F × F, 0 ≤ 1 + κ * ∑ s ∈ S, chi F w s) :
    ∃ u : F × F × F → EuclideanSpace ℝ (F × F × F),
      (∀ g h : F × F × F, inner ℝ (u g) (u h) = (if g = h then (1 : ℝ) else 0) + κ * (if g + h ∈ S then 1 else 0)) ∧
      ‖∑ g, u g‖ ^ 2 = (Fintype.card F : ℝ) ^ 3 * (1 + κ * (S.card : ℝ)) := by
  have hnpos : (0 : ℝ) < (Fintype.card F : ℝ) ^ 3 := pow_pos (pk_card_pos F) 3
  obtain ⟨n, hn⟩ : ∃ n : ℝ, n = (Fintype.card F : ℝ) ^ 3 := ⟨_, rfl⟩
  rw [← hn] at hnpos ⊢
  obtain ⟨lam, hlam⟩ : ∃ lam : F × F × F → ℝ, ∀ w, lam w = ∑ s ∈ S, chi F w s :=
    ⟨fun w => ∑ s ∈ S, chi F w s, fun w => rfl⟩
  obtain ⟨coef, hcoef⟩ : ∃ coef : F × F × F → ℝ, ∀ w, coef w = Real.sqrt ((1 + κ * lam w) / n) :=
    ⟨fun w => Real.sqrt ((1 + κ * lam w) / n), fun w => rfl⟩
  have hcc : ∀ w, coef w * coef w = (1 + κ * lam w) / n := fun w => by
    rw [hcoef, Real.mul_self_sqrt]
    exact div_nonneg (by rw [hlam]; exact hκ w) hnpos.le
  obtain ⟨u, hu⟩ : ∃ u : F × F × F → EuclideanSpace ℝ (F × F × F),
      ∀ g, u g = WithLp.toLp 2 (fun w => coef w * chi F w g) := ⟨fun g => _, fun g => rfl⟩
  have hgram : ∀ g h : F × F × F, inner ℝ (u g) (u h) =
      (if g = h then (1 : ℝ) else 0) + κ * (if g + h ∈ S then 1 else 0) := by
    intro g h
    have e1 : inner ℝ (u g) (u h) = ∑ w, ((1 + κ * lam w) / n) * chi F w (g + h) := by
      rw [hu, hu, PiLp.inner_apply]
      refine Finset.sum_congr rfl fun w _ => ?_
      simp only [RCLike.inner_apply, conj_trivial]
      rw [pk_chi_add_right, ← hcc w]
      ring
    have e2 : ∑ w, ((1 + κ * lam w) / n) * chi F w (g + h)
        = (∑ w, chi F w (g + h)) / n + κ / n * ∑ w, lam w * chi F w (g + h) := by
      rw [Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun w _ => ?_
      ring
    have e3 : ∑ w, lam w * chi F w (g + h) = if g + h ∈ S then n else 0 := by
      calc ∑ w, lam w * chi F w (g + h) = ∑ w, ∑ s ∈ S, chi F w (s + (g + h)) := by
            refine Finset.sum_congr rfl fun w _ => ?_
            rw [hlam, Finset.sum_mul]
            exact Finset.sum_congr rfl fun s _ => (pk_chi_add_right F w s (g + h)).symm
        _ = ∑ s ∈ S, ∑ w, chi F w (s + (g + h)) := Finset.sum_comm
        _ = ∑ s ∈ S, (if s + (g + h) = 0 then n else 0) := by
            refine Finset.sum_congr rfl fun s _ => ?_
            rw [pk_sum_chi, hn]
        _ = ∑ s ∈ S, (if s = g + h then n else 0) := by
            refine Finset.sum_congr rfl fun s _ => ?_
            simp only [pk_add_eq_zero_iff_G F]
        _ = if g + h ∈ S then n else 0 := by rw [Finset.sum_ite_eq']
    have h0 : g + h = 0 ↔ g = h := pk_add_eq_zero_iff_G F g h
    have e4 : (if g + h = 0 then n else 0) = if g = h then n else 0 := by simp only [h0]
    rw [e1, e2, e3, pk_sum_chi, ← hn, e4]
    have hn0 : n ≠ 0 := hnpos.ne'
    by_cases h1 : g = h <;> by_cases h2 : g + h ∈ S
    · rw [if_pos h1, if_pos h2, if_pos h1, if_pos h2]; field_simp
    · rw [if_pos h1, if_neg h2, if_pos h1, if_neg h2]; field_simp; ring
    · rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2]; field_simp; ring
    · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]; simp
  refine ⟨u, hgram, ?_⟩
  have hsum : ‖∑ g, u g‖ ^ 2 = ∑ g, ∑ h, inner ℝ (u g) (u h) := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    exact Finset.sum_congr rfl fun g _ => inner_sum _ _ _
  rw [hsum]
  simp_rw [hgram]
  have hcardG : (Fintype.card (F × F × F) : ℝ) = n := by
    rw [hn]; simp [Fintype.card_prod]; ring
  have hS : ∀ g : F × F × F, ∑ h : F × F × F, (if g + h ∈ S then (1 : ℝ) else 0) = S.card := by
    intro g
    rw [Fintype.sum_equiv (Equiv.addLeft g) (fun h => if g + h ∈ S then (1 : ℝ) else 0)
      (fun t => if t ∈ S then (1 : ℝ) else 0) (fun h => rfl)]
    simp
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hS]
  simp
  subst hn
  ring

#print axioms solution
