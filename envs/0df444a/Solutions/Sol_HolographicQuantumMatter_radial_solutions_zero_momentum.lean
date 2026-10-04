-- Prove2me | solution 1 for HolographicQuantumMatter.radial_solutions_zero_momentum
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T13:10:08.377976+00:00
-- url     : https://prove2.me/submissions/a7a4ab19-f270-409e-8e8c-b0262945287f

import Mathlib
import Definitions.Def_HolographicQuantumMatter_ScalarAdS

set_option autoImplicit false

open HolographicQuantumMatter in
/-- For roots `p, q` of the indicial equation, `r^(-q) (r φ' - p φ)` is constant on `r > 0`. -/
theorem f9998ed1_const (d : ℕ) (msq L p q : ℝ) (hpq : p + q = (d : ℝ) + 1)
    (hpq2 : p * q = -(msq * L ^ 2)) (φ : ℝ → ℝ)
    (hφ : ContDiffOn ℝ 2 φ (Set.Ioi 0))
    (hode : ∀ r : ℝ, 0 < r → radialOperator d 0 0 msq L φ r = 0) :
    ∃ K : ℝ, ∀ r ∈ Set.Ioi (0 : ℝ), r ^ (-q) * (r * deriv φ r - p * φ r) = K := by
  have h2 := (contDiffOn_succ_iff_deriv_of_isOpen (𝕜 := ℝ) (f := φ) (n := 1) isOpen_Ioi).1
    (by exact hφ)
  have hd1 : DifferentiableOn ℝ φ (Set.Ioi 0) := h2.1
  have hd2 : DifferentiableOn ℝ (deriv φ) (Set.Ioi 0) := h2.2.2.differentiableOn one_ne_zero
  have key : ∀ r : ℝ, 0 < r → HasDerivAt
      (fun x : ℝ => x ^ (-q) * (x * deriv φ x - p * φ x)) 0 r := by
    intro r hr
    have hA : HasDerivAt φ (deriv φ r) r :=
      (hd1.differentiableAt (Ioi_mem_nhds hr)).hasDerivAt
    have hB : HasDerivAt (deriv φ) (deriv (deriv φ) r) r :=
      (hd2.differentiableAt (Ioi_mem_nhds hr)).hasDerivAt
    have hR : HasDerivAt (fun x : ℝ => x ^ (-q)) ((-q) * r ^ (-q - 1)) r :=
      Real.hasDerivAt_rpow_const (Or.inl hr.ne')
    refine (hR.mul (((hasDerivAt_id' r).mul hB).sub (hA.const_mul p))).congr_deriv ?_
    have hO := hode r hr
    unfold radialOperator at hO
    have hc : msq * L ^ 2 = -(p * q) := by linarith
    have hd : ((d : ℕ) : ℝ) = p + q - 1 := by linarith
    rw [hc, hd] at hO
    have hD2 : deriv (deriv φ) r = (p + q - 1) / r * deriv φ r - (p * q) / r ^ 2 * φ r := by
      linear_combination hO
    have hrne : r ≠ 0 := hr.ne'
    try simp only [Pi.mul_apply, Pi.sub_apply]
    rw [hD2, Real.rpow_sub_one hrne]
    field_simp
    ring
  have hdiff : DifferentiableOn ℝ (fun x : ℝ => x ^ (-q) * (x * deriv φ x - p * φ x))
      (Set.Ioi 0) := fun r hr => (key r hr).differentiableAt.differentiableWithinAt
  exact isOpen_Ioi.exists_is_const_of_deriv_eq_zero isPreconnected_Ioi hdiff
    (fun r hr => (key r hr).deriv)

open HolographicQuantumMatter in
theorem solution (d : ℕ) (msq L : ℝ) (hL : 0 < L)
    (hBF : -(((d : ℝ) + 1) ^ 2) / 4 < msq * L ^ 2) (φ : ℝ → ℝ) :
    IsRadialSolution d 0 0 msq L φ ↔
      ∃ A B : ℝ, ∀ r : ℝ, 0 < r →
        φ r = A * r ^ deltaMinus d msq L + B * r ^ deltaPlus d msq L := by
  set s := Real.sqrt (((d : ℝ) + 1) ^ 2 / 4 + msq * L ^ 2) with hs_def
  have hrad : 0 < ((d : ℝ) + 1) ^ 2 / 4 + msq * L ^ 2 := by linarith
  have hs : 0 < s := Real.sqrt_pos.2 hrad
  have hs2 : s ^ 2 = ((d : ℝ) + 1) ^ 2 / 4 + msq * L ^ 2 := Real.sq_sqrt hrad.le
  have ha : deltaMinus d msq L = ((d : ℝ) + 1) / 2 - s := rfl
  have hb : deltaPlus d msq L = ((d : ℝ) + 1) / 2 + s := rfl
  set a := deltaMinus d msq L
  set b := deltaPlus d msq L
  have hab : a + b = (d : ℝ) + 1 := by rw [ha, hb]; ring
  have hab2 : a * b = -(msq * L ^ 2) := by rw [ha, hb]; linear_combination -hs2
  have hba : b - a ≠ 0 := by rw [ha, hb]; linarith
  constructor
  · rintro ⟨hφ, hode⟩
    obtain ⟨E, hE⟩ := f9998ed1_const d msq L a b hab hab2 φ hφ hode
    obtain ⟨F, hF⟩ := f9998ed1_const d msq L b a (by linarith) (by linarith) φ hφ hode
    refine ⟨-F / (b - a), E / (b - a), fun r hr => ?_⟩
    have hE1 := hE r hr
    have hF1 := hF r hr
    rw [Real.rpow_neg hr.le] at hE1 hF1
    have hY : 0 < r ^ b := Real.rpow_pos_of_pos hr b
    have hZ : 0 < r ^ a := Real.rpow_pos_of_pos hr a
    have hE2 : r * deriv φ r - a * φ r = E * r ^ b := by
      rw [← hE1]; field_simp
    have hF2 : r * deriv φ r - b * φ r = F * r ^ a := by
      rw [← hF1]; field_simp
    field_simp
    linear_combination hE2 - hF2
  · rintro ⟨A, B, hAB⟩
    have ha2 : a ^ 2 - ((d : ℝ) + 1) * a - msq * L ^ 2 = 0 := by
      linear_combination a * hab - hab2
    have hb2 : b ^ 2 - ((d : ℝ) + 1) * b - msq * L ^ 2 = 0 := by
      linear_combination b * hab - hab2
    let f : ℝ → ℝ := fun x => A * x ^ a + B * x ^ b
    let g : ℝ → ℝ := fun x => A * (a * x ^ (a - 1)) + B * (b * x ^ (b - 1))
    let h : ℝ → ℝ := fun x => A * (a * ((a - 1) * x ^ (a - 1 - 1)))
      + B * (b * ((b - 1) * x ^ (b - 1 - 1)))
    have hf : ∀ x : ℝ, 0 < x → HasDerivAt f (g x) x := by
      intro x hx
      exact ((Real.hasDerivAt_rpow_const (p := a) (Or.inl hx.ne')).const_mul A).add
        ((Real.hasDerivAt_rpow_const (p := b) (Or.inl hx.ne')).const_mul B)
    have hg : ∀ x : ℝ, 0 < x → HasDerivAt g (h x) x := by
      intro x hx
      exact (((Real.hasDerivAt_rpow_const (p := a - 1) (Or.inl hx.ne')).const_mul a).const_mul
        A).add
        (((Real.hasDerivAt_rpow_const (p := b - 1) (Or.inl hx.ne')).const_mul b).const_mul B)
    have hφf : ∀ x : ℝ, 0 < x → φ =ᶠ[nhds x] f := by
      intro x hx
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact hAB y hy
    have hφd : ∀ x : ℝ, 0 < x → HasDerivAt φ (g x) x := fun x hx =>
      (hf x hx).congr_of_eventuallyEq (hφf x hx)
    have hdφ : ∀ x : ℝ, 0 < x → deriv φ x = g x := fun x hx => (hφd x hx).deriv
    have hφdd : ∀ x : ℝ, 0 < x → HasDerivAt (deriv φ) (h x) x := by
      intro x hx
      refine (hg x hx).congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact hdφ y hy
    refine ⟨?_, ?_⟩
    · have hfc : ContDiffOn ℝ 2 f (Set.Ioi 0) := by
        intro x hx
        have hx' : x ≠ 0 := (Set.mem_Ioi.1 hx).ne'
        exact (((Real.contDiffAt_rpow_const_of_ne (p := a) hx').const_smul A).add
          ((Real.contDiffAt_rpow_const_of_ne (p := b) hx').const_smul B)).contDiffWithinAt
      exact hfc.congr (fun x hx => hAB x hx)
    · intro r hr
      unfold radialOperator
      rw [(hφdd r hr).deriv, hdφ r hr, hAB r hr]
      have hrne : r ≠ 0 := hr.ne'
      simp only [h, g]
      rw [Real.rpow_sub_one hrne, Real.rpow_sub_one hrne, Real.rpow_sub_one hrne,
        Real.rpow_sub_one hrne]
      linear_combination (A * r ^ a / r ^ 2) * ha2 + (B * r ^ b / r ^ 2) * hb2
