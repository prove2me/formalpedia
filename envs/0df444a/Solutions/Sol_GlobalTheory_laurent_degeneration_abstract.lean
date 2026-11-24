-- Prove2me | solution 1 for GlobalTheory.laurent_degeneration_abstract
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:14:55.027872+00:00
-- url     : https://prove2.me/submissions/cb5c09f4-4f79-42b1-a838-bd7da22f8043

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LaurentDegenerationFirstOrderKernel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (k : Type) [Field k] (K : Type) [Field K] [Algebra k K] (σ : K)
    (O : K → Prop) (π0 π1 : K →ₗ[k] k) (h0 : ∀ z, O z → π0 (σ * z) = 0)
    (h1 : ∀ z, π1 (σ * z) = π0 z) (hone : π0 1 = 1)
    (hnorm : ∀ (a : ℕ) (y : Fin a → K), y ≠ 0 → ∃ (f : K) (c0 : Fin a), f * y c0 = 1 ∧ ∀ c, O (f * y c))
    (a e : ℕ) (V : Submodule k (Fin a → k)) (U : Type) [AddCommGroup U] [Module k U]
    (t u : V →ₗ[k] U) (he : e ≤ 1)
    (H : ∀ x0 x1 : Fin (e + 1) → V, (∀ j, t (x0 j) = 0 ∧ t (x1 j) = u (x0 j)) →
      ¬ LinearIndependent k x0)
    (y : Fin (e + 1) → Fin a → K)
    (hy : ∀ j (π : K →ₗ[k] k), ∃ x x' : V, (∀ c, x.1 c = π (y j c)) ∧
      (∀ c, x'.1 c = π (σ * y j c)) ∧ t x = u x') :
    ¬ LinearIndependent K y := by
  let P : (Fin a → K) → Prop := fun z => ∀ (π : K →ₗ[k] k), ∃ x x' : V, (∀ c, x.1 c = π (z c)) ∧
      (∀ c, x'.1 c = π (σ * z c)) ∧ t x = u x'
  have Psmul : ∀ (f : K) z, P z → P (f • z) := by
    intro f z hz π
    obtain ⟨x, x', h, h', h''⟩ := hz (π ∘ₗ LinearMap.mulLeft k f)
    refine ⟨x, x', fun c => by simpa using h c, fun c => ?_, h''⟩
    rw [h' c]
    simp [mul_left_comm]
  have Psub : ∀ z w, P z → P w → P (z - w) := by
    intro z w hz hw π
    obtain ⟨x, x', h, h', h''⟩ := hz π
    obtain ⟨v, v', g, g', g''⟩ := hw π
    refine ⟨x - v, x' - v', fun c => by simp [h c, g c], fun c => by simp [h' c, g' c, mul_sub],
      by simp [h'', g'']⟩
  have key : ∀ z, P z → z ≠ 0 → ∃ (f : K) (c0 : Fin a) (x0 x1 : V), f * z c0 = 1 ∧
      (∀ c, x0.1 c = π0 (f * z c)) ∧ t x0 = 0 ∧ t x1 = u x0 := by
    intro z hz hz0
    obtain ⟨f, c0, hf, hO⟩ := hnorm a z hz0
    have hP := Psmul f z hz
    obtain ⟨x, x', h, h', h''⟩ := hP π0
    obtain ⟨v, v', g, g', g''⟩ := hP π1
    have hx' : x' = 0 := by
      ext c
      rw [h' c]
      simpa using h0 _ (hO c)
    have hv' : v' = x := by
      ext c
      rw [g' c, h c, h1]
    refine ⟨f, c0, x, v, hf, fun c => by simpa using h c, by rw [h'', hx', map_zero],
      by rw [g'', hv']⟩
  intro hli
  obtain rfl | rfl : e = 0 ∨ e = 1 := by omega
  · obtain ⟨f, c0, x0, x1, hf, hx, ht, ht'⟩ := key (y 0) (hy 0) (hli.ne_zero 0)
    refine H (fun _ => x0) (fun _ => x1) (fun _ => ⟨ht, ht'⟩) ?_
    have hne : x0 ≠ 0 := by
      intro h
      have := hx c0
      rw [h, hf, hone] at this
      simp at this
    exact (linearIndependent_unique_iff (ι := Fin 1) (v := fun _ => x0)).2 hne
  · obtain ⟨f, c0, x0, x1, hf, hx, ht, ht'⟩ := key (y 0) (hy 0) (hli.ne_zero 0)
    have hw : y 1 - (y 1 c0 * f) • y 0 ≠ 0 := by
      intro h
      have hy2 : y = ![y 0, y 1] := by
        ext i : 1
        fin_cases i <;> rfl
      rw [hy2, LinearIndependent.pair_iff] at hli
      have := (hli (-(y 1 c0 * f)) 1 (by rw [← h]; simp [sub_eq_neg_add])).2
      exact one_ne_zero this
    obtain ⟨g, c1, z0, z1, hg, hz, hs, hs'⟩ :=
      key _ (Psub _ _ (hy 1) (Psmul (y 1 c0 * f) _ (hy 0))) hw
    have e1 : x0.1 c0 = 1 := by rw [hx, hf, hone]
    have e2 : z0.1 c0 = 0 := by
      rw [hz]
      simp [mul_assoc, hf]
    have e3 : z0.1 c1 = 1 := by rw [hz, hg, hone]
    refine H ![x0, z0] ![x1, z1] (fun j => by fin_cases j <;> simp [ht, ht', hs, hs']) ?_
    rw [LinearIndependent.pair_iff]
    intro s r h
    have a0 := congrArg (fun v : V => v.1 c0) h
    have a1 := congrArg (fun v : V => v.1 c1) h
    simp [e1, e2] at a0
    simp [a0, e3] at a1
    exact ⟨a0, a1⟩
end GlobalTheory
