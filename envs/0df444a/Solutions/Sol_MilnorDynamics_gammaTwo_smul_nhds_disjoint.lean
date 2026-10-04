-- Prove2me | solution 1 for MilnorDynamics.gammaTwo_smul_nhds_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-10-02T15:52:02.014387+00:00
-- url     : https://prove2.me/submissions/f122c797-4ceb-420c-b3de-6a0afae6b017

import Mathlib

open Set Topology UpperHalfPlane
open scoped MatrixGroups

/-- Integer core: a matrix in `Γ(2)` with a fixed point in `ℍ` has entries `a = d = ±1`,
`b = c = 0`.  Stated on the real and imaginary parts of the fixed-point equation. -/
private lemma gammaTwo_int_core (a b c d : ℤ) (x y : ℝ) (hy : 0 < y)
    (hdet : a * d - b * c = 1)
    (ha : 2 ∣ a - 1) (hb : 2 ∣ b) (hc : 2 ∣ c) (hd : 2 ∣ d - 1)
    (hre : (a : ℝ) * x + b = c * (x ^ 2 - y ^ 2) + d * x)
    (him : (a : ℝ) * y = c * (2 * x * y) + d * y) :
    b = 0 ∧ c = 0 ∧ a = d ∧ (a = 1 ∨ a = -1) := by
  have him' : (a : ℝ) = 2 * c * x + d := by
    have : ((a : ℝ) - (2 * c * x + d)) * y = 0 := by linear_combination him
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith
  have hb' : (b : ℝ) = - c * (x ^ 2 + y ^ 2) := by
    have := hre
    rw [him'] at this
    linear_combination this
  have hdetR : (a : ℝ) * d - b * c = 1 := by exact_mod_cast hdet
  -- (a + d)^2 = 4 - 4 c^2 y^2
  have htr : ((a : ℝ) + d) ^ 2 = 4 - 4 * (c : ℝ) ^ 2 * y ^ 2 := by
    have h1 : ((a : ℝ) + d) ^ 2 = ((a : ℝ) - d) ^ 2 + 4 * (a * d) := by ring
    rw [h1, show (a : ℝ) * d = 1 + b * c by linarith, hb', him']
    ring
  by_cases hc0 : c = 0
  · subst hc0
    have hb0 : b = 0 := by exact_mod_cast (by simpa using hb' : (b : ℝ) = 0)
    have had : a = d := by exact_mod_cast (by simpa using him' : (a : ℝ) = d)
    subst hb0 had
    refine ⟨rfl, rfl, rfl, ?_⟩
    have : a * a = 1 := by linarith
    exact Int.eq_one_or_neg_one_of_mul_eq_one this
  · exfalso
    have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc0
    have hlt : ((a : ℝ) + d) ^ 2 < 4 := by
      have : 0 < (c : ℝ) ^ 2 * y ^ 2 := by positivity
      linarith
    have hltZ : (a + d) ^ 2 < 4 := by exact_mod_cast hlt
    obtain ⟨k, hk⟩ := ha
    obtain ⟨l, hl⟩ := hd
    obtain ⟨b', rfl⟩ := hb
    obtain ⟨c', rfl⟩ := hc
    have hsum : a + d = 2 * (k + l + 1) := by omega
    have hkl : k + l + 1 = 0 := by
      rw [hsum] at hltZ
      nlinarith
    have hd' : d = -a := by omega
    subst hd'
    have ha' : a = 2 * k + 1 := by omega
    subst ha'
    have h4 : 4 * (k ^ 2 + k + b' * c') = -2 := by linear_combination -hdet
    omega

/-- Fixed points: an element of `Γ(2)` fixing a point of `ℍ` is `±1`. -/
private lemma gammaTwo_eq_one_or_neg_one_of_smul_eq {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma 2) {τ : ℍ} (hfix : γ • τ = τ) : γ = 1 ∨ γ = -1 := by
  rw [CongruenceSubgroup.Gamma_mem] at hγ
  obtain ⟨h00, h01, h10, h11⟩ := hγ
  have dvd_of_eq_one : ∀ n : ℤ, ((n : ZMod 2) = 1) → 2 ∣ n - 1 := by
    intro n hn
    have : ((n - 1 : ℤ) : ZMod 2) = 0 := by push_cast; rw [hn]; ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp this
  have dvd_of_eq_zero : ∀ n : ℤ, ((n : ZMod 2) = 0) → 2 ∣ n := by
    intro n hn
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hn
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.2
    rw [Matrix.det_fin_two] at this
    exact this
  have heq := congrArg UpperHalfPlane.coe hfix
  rw [coe_specialLinearGroup_apply] at heq
  simp only [algebraMap_int_eq, eq_intCast] at heq
  have hden : ((γ 1 0 : ℝ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℝ) : ℂ) ≠ 0 := by
    have := UpperHalfPlane.denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ
    simpa [UpperHalfPlane.denom, Matrix.SpecialLinearGroup.mapGL] using this
  rw [div_eq_iff hden] at heq
  have hre := congrArg Complex.re heq
  have him := congrArg Complex.im heq
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_im, Complex.mul_im, zero_mul, sub_zero, add_zero] at hre him
  obtain ⟨hb, hc, had, ha⟩ := gammaTwo_int_core (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)
    τ.re τ.im τ.im_pos hdet (dvd_of_eq_one _ h00) (dvd_of_eq_zero _ h01)
    (dvd_of_eq_zero _ h10) (dvd_of_eq_one _ h11)
    (by simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at hre ⊢; nlinarith [hre])
    (by simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at him ⊢; nlinarith [him])
  rcases ha with ha | ha
  · left
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb, hc, ← had, ha]
  · right
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb, hc, ← had, ha]

theorem solution (τ : ℍ) :
    ∃ U ∈ 𝓝 τ, ∀ γ ∈ CongruenceSubgroup.Gamma 2,
      (∃ σ ∈ U, γ • σ ∈ U) → γ = 1 ∨ γ = -1 := by
  obtain ⟨U, hU, hUg⟩ := ProperlyDiscontinuousSMul.exists_nhds_image_smul_eq_self (Γ := 𝒮ℒ) τ
  refine ⟨U, hU, fun γ hγ ⟨σ, hσU, hγσ⟩ => ?_⟩
  have hfix : γ • τ = τ :=
    hUg ⟨Matrix.SpecialLinearGroup.mapGL ℝ γ, γ, rfl⟩ ⟨γ • σ, ⟨σ, hσU, rfl⟩, hγσ⟩
  exact gammaTwo_eq_one_or_neg_one_of_smul_eq hγ hfix
