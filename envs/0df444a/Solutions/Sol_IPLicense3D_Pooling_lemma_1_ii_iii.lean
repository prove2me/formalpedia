-- Prove2me | solution 1 for IPLicense3D.Pooling.lemma_1_ii_iii
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:55:13.211992+00:00
-- url     : https://prove2.me/submissions/eca35d11-4d1e-4e77-908f-81b521055bd3

import Mathlib
import Definitions.Def_IPLicense3D_Pooling_Model

namespace Aux_IPL3

lemma key (s : Set ℝ) (hs : Convex ℝ s) (A a b q : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hq : ∀ t ∈ s, 0 ≤ t + q) :
    StrictAntiOn (fun t => A - a * (t + q) - Real.sqrt (b * (t + q))) s ∧
      StrictConvexOn ℝ s (fun t => A - a * (t + q) - Real.sqrt (b * (t + q))) := by
  refine ⟨?_, hs, ?_⟩
  · intro x hx y hy hxy
    have h1 : Real.sqrt (b * (x + q)) ≤ Real.sqrt (b * (y + q)) :=
      Real.sqrt_le_sqrt (by nlinarith)
    show A - a * (y + q) - Real.sqrt (b * (y + q)) < A - a * (x + q) - Real.sqrt (b * (x + q))
    nlinarith
  · intro x hx y hy hxy u v hu hv huv
    have hX : b * (x + q) ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr (mul_nonneg hb.le (hq x hx))
    have hY : b * (y + q) ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr (mul_nonneg hb.le (hq y hy))
    have hXY : b * (x + q) ≠ b * (y + q) := by
      intro h; apply hxy
      have := mul_left_cancel₀ hb.ne' h
      linarith
    have hc := Real.strictConcaveOn_sqrt.2 hX hY hXY hu hv huv
    simp only [smul_eq_mul] at hc ⊢
    have e : u * (b * (x + q)) + v * (b * (y + q)) = b * (u * x + v * y + q) := by
      have : v = 1 - u := by linarith
      subst this; ring
    rw [e] at hc
    have e2 : u * x + v * y + q = (u * x + v * y) + q := rfl
    have hv' : v = 1 - u := by linarith
    subst hv'
    nlinarith

end Aux_IPL3

open IPLicense3D.Pooling Model in
theorem solution {n : ℕ} (M : Model n) (hM : M.Standing) (i : Fin n) :
    (∀ f r : ℝ, M.surplus i f r = M.surplus i 0 r - f) ∧
    (∀ f : ℝ, StrictAntiOn (fun r => M.surplus i f r) (Set.Ici 0) ∧
      StrictConvexOn ℝ (Set.Ici 0) (fun r => M.surplus i f r)) ∧
    (∀ f r : ℝ, 0 ≤ r →
      StrictAntiOn (fun p' => surplusF M.h M.w p' M.kT M.kA M.ellT M.ellA M.z (M.lam i) f r) (Set.Ioi 0) ∧
      StrictConvexOn ℝ (Set.Ioi 0)
        (fun p' => surplusF M.h M.w p' M.kT M.kA M.ellT M.ellA M.z (M.lam i) f r)) ∧
    (∀ f r δ : ℝ, surplusF M.h M.w M.p M.kT M.kA M.ellT M.ellA M.z (M.lam i) f (r + δ) =
      surplusF M.h M.w (M.p + δ) M.kT M.kA M.ellT M.ellA M.z (M.lam i) f r) := by
  obtain ⟨hh, hw, hp, hkA, hkAT, hlA, hlAT, hz, hlam⟩ := hM
  have hl := hlam i
  set lam := M.lam i with hlamdef
  set a := M.h * (lam * M.ellA + M.z * Real.sqrt (lam * M.ellA)) + lam with ha
  have ha0 : 0 < a := by
    have : 0 ≤ M.z * Real.sqrt (lam * M.ellA) := mul_nonneg hz (Real.sqrt_nonneg _)
    have : 0 < lam * M.ellA := mul_pos hl hlA
    rw [ha]; nlinarith
  set b := 2 * M.h * lam * M.kA with hb
  have hb0 : 0 < b := by rw [hb]; positivity
  have hform : ∀ f p' r : ℝ, surplusF M.h M.w p' M.kT M.kA M.ellT M.ellA M.z lam f r
      = (costTF M.h M.w M.kT M.ellT M.z lam - f) - a * (r + p') - Real.sqrt (b * (r + p')) := by
    intro f p' r
    unfold surplusF costAF
    rw [show 2 * M.h * (r + p') * lam * M.kA = b * (r + p') by rw [hb]; ring, ha]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro f r
    unfold surplus surplusL
    rw [hform, hform]
    ring
  · intro f
    have e : (fun r => M.surplus i f r)
        = fun t => (costTF M.h M.w M.kT M.ellT M.z lam - f) - a * (t + M.p)
            - Real.sqrt (b * (t + M.p)) := by
      funext t
      unfold surplus surplusL
      rw [hform]
    rw [e]
    exact Aux_IPL3.key (Set.Ici 0) (convex_Ici 0) _ a b M.p ha0 hb0
      (fun t ht => by have := Set.mem_Ici.mp ht; linarith)
  · intro f r hr
    have e : (fun p' => surplusF M.h M.w p' M.kT M.kA M.ellT M.ellA M.z lam f r)
        = fun t => (costTF M.h M.w M.kT M.ellT M.z lam - f) - a * (t + r)
            - Real.sqrt (b * (t + r)) := by
      funext t
      rw [hform]
      ring_nf
    rw [e]
    exact Aux_IPL3.key (Set.Ioi 0) (convex_Ioi 0) _ a b r ha0 hb0
      (fun t ht => by have := Set.mem_Ioi.mp ht; linarith)
  · intro f r δ
    rw [hform, hform]
    ring_nf
