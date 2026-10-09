-- Prove2me | solution 1 for OAI.SevenEighths.HeckeDetectorFrequency.dyadic_frequency_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T02:10:37.331718+00:00
-- url     : https://prove2.me/submissions/781a5355-6696-4b45-a61a-13d52fc1c270

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B016

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Mellin.LogProfiles
namespace OAI

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology

open MeasureTheory Real
open scoped FourierTransform SchwartzMap

open scoped ContDiff

namespace FourierBridge

theorem exp_argument_derivative_bound
    (R a y H : ℝ) (i : ℕ)
    (hR : 0 ≤ R) (hH : 1 ≤ H)
    (ha : |a| ≤ H) (hexp : Real.exp (a * y) ≤ H)
    (hi : 1 ≤ i) :
    ‖iteratedFDeriv ℝ i (fun z : ℝ => R * Real.exp (a * z)) y‖ ≤
      (H ^ 2 * (1 + R)) ^ i := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  simp only [iteratedDeriv_const_mul_field, iteratedDeriv_exp_const_mul]
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hR,
    abs_of_pos (Real.exp_pos _), abs_pow]
  have hpowH : H ≤ H ^ i := by
    calc H = H ^ 1 := by ring
         _ ≤ H ^ i := pow_le_pow_right₀ hH hi
  have hpowR : R ≤ (1 + R) ^ i := by
    calc R ≤ 1 + R := by linarith
         _ = (1 + R) ^ 1 := by ring
         _ ≤ (1 + R) ^ i := pow_le_pow_right₀ (by linarith) hi
  calc
    R * (|a| ^ i * Real.exp (a * y)) ≤ R * (H ^ i * H) := by gcongr
    _ ≤ (1 + R) ^ i * (H ^ i * H ^ i) := by gcongr
    _ = (H ^ 2 * (1 + R)) ^ i := by simp only [mul_pow, pow_two]; ring

theorem coupled_factor_derivative_bound
    (F : ℝ → ℂ) (R a y H CF : ℝ) (A n j : ℕ)
    (hF : ContDiff ℝ ∞ F)
    (hR : 0 ≤ R) (hH : 1 ≤ H)
    (ha : |a| ≤ H) (hexp : Real.exp (a * y) ≤ H)
    (hj : j ≤ n)
    (_hCF : 0 ≤ CF)
    (hFdecay : ∀ i ≤ n, ∀ u, 0 ≤ u →
      (1 + u) ^ (A + n) * ‖iteratedFDeriv ℝ i F u‖ ≤ CF) :
    ‖iteratedFDeriv ℝ j (fun z : ℝ => F (R * Real.exp (a * z))) y‖ ≤
      j.factorial * (CF / (1 + R * Real.exp (a * y)) ^ (A + n)) *
        (H ^ 2 * (1 + R)) ^ j := by
  have harg : ContDiff ℝ ∞ (fun z : ℝ => R * Real.exp (a * z)) := by fun_prop
  have hu : 0 ≤ R * Real.exp (a * y) := by positivity
  have hden : 0 < (1 + R * Real.exp (a * y)) ^ (A + n) := by positivity
  apply norm_iteratedFDeriv_comp_le hF harg (by simp) y
  · intro i hi
    apply (le_div_iff₀ hden).mpr
    simpa [mul_comm] using hFdecay i (hi.trans hj) _ hu
  · intro i hi₁ hi₂
    exact exp_argument_derivative_bound R a y H i hR hH ha hexp hi₁

theorem derivative_scale_absorption
    (R u m H CF : ℝ) (A n j : ℕ)
    (hR : 0 ≤ R) (hm : 0 < m)
    (_hH : 0 ≤ H) (hCF : 0 ≤ CF)
    (hu : 0 ≤ u) (hlower : m * (1 + R) ≤ 1 + u)
    (hj : j ≤ n) :
    m ^ (A + n) * (1 + R) ^ A *
      ((j.factorial : ℝ) * (CF / (1 + u) ^ (A + n)) *
        (H ^ 2 * (1 + R)) ^ j) ≤
      (j.factorial : ℝ) * CF * (H ^ 2) ^ j := by
  have hRp : 1 ≤ 1 + R := by linarith
  have hden : 0 < (1 + u) ^ (A + n) := by positivity
  have hpowR : (1 + R) ^ (A + j) ≤ (1 + R) ^ (A + n) :=
    pow_le_pow_right₀ hRp (Nat.add_le_add_left hj A)
  have hscale : m ^ (A + n) * (1 + R) ^ A * (1 + R) ^ j ≤
      (1 + u) ^ (A + n) := by
    calc
      m ^ (A + n) * (1 + R) ^ A * (1 + R) ^ j =
          m ^ (A + n) * (1 + R) ^ (A + j) := by rw [pow_add]; ring
      _ ≤ m ^ (A + n) * (1 + R) ^ (A + n) :=
        mul_le_mul_of_nonneg_left hpowR (by positivity)
      _ = (m * (1 + R)) ^ (A + n) := by rw [mul_pow]
      _ ≤ (1 + u) ^ (A + n) := by gcongr
  let Q : ℝ := (j.factorial : ℝ) * CF * (H ^ 2) ^ j
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hQscale : Q * (m ^ (A + n) * (1 + R) ^ A * (1 + R) ^ j) ≤
      Q * (1 + u) ^ (A + n) := mul_le_mul_of_nonneg_left hscale hQ
  calc
    m ^ (A + n) * (1 + R) ^ A *
        ((j.factorial : ℝ) * (CF / (1 + u) ^ (A + n)) *
          (H ^ 2 * (1 + R)) ^ j) =
      Q * (m ^ (A + n) * (1 + R) ^ A * (1 + R) ^ j) /
        (1 + u) ^ (A + n) := by dsimp [Q]; rw [mul_pow]; ring
    _ ≤ Q := (div_le_iff₀ hden).mpr (by simpa [mul_comm, mul_left_comm, mul_assoc] using hQscale)
    _ = (j.factorial : ℝ) * CF * (H ^ 2) ^ j := rfl

theorem coupled_factor_uniform_derivative
    (F : ℝ → ℂ) (R a y m H CF : ℝ) (A n j : ℕ)
    (hF : ContDiff ℝ ∞ F)
    (hR : 0 ≤ R) (hm : 0 < m) (hm1 : m ≤ 1)
    (hH : 1 ≤ H) (ha : |a| ≤ H)
    (hexpLower : m ≤ Real.exp (a * y))
    (hexpUpper : Real.exp (a * y) ≤ H)
    (hj : j ≤ n) (hCF : 0 ≤ CF)
    (hFdecay : ∀ i ≤ n, ∀ u, 0 ≤ u →
      (1 + u) ^ (A + n) * ‖iteratedFDeriv ℝ i F u‖ ≤ CF) :
    m ^ (A + n) * (1 + R) ^ A *
      ‖iteratedFDeriv ℝ j (fun z : ℝ => F (R * Real.exp (a * z))) y‖ ≤
        (j.factorial : ℝ) * CF * (H ^ 2) ^ j := by
  have hcomp := coupled_factor_derivative_bound F R a y H CF A n j hF hR hH
    ha hexpUpper hj hCF hFdecay
  have hscale : 0 ≤ m ^ (A + n) * (1 + R) ^ A := by positivity
  have hlower : m * (1 + R) ≤ 1 + R * Real.exp (a * y) := by
    nlinarith [mul_nonneg hR (sub_nonneg.mpr hexpLower)]
  exact (mul_le_mul_of_nonneg_left hcomp hscale).trans
    (derivative_scale_absorption R (R * Real.exp (a * y)) m H CF A n j
      hR hm (by linarith) hCF (by positivity) hlower hj)

theorem schwartzDerivativeDecayConstant_nonneg
    (F : 𝓢(ℝ, ℂ)) (M K : ℕ) :
    0 ≤ schwartzDerivativeDecayConstant F M K := by
  unfold schwartzDerivativeDecayConstant
  positivity

theorem schwartz_derivative_decay_finite
    (F : 𝓢(ℝ, ℂ)) (A K j i : ℕ) (u : ℝ)
    (hj : j ≤ K) (hi : i ≤ j) (hu : 0 ≤ u) :
    (1 + u) ^ (A + j) * ‖iteratedFDeriv ℝ i F u‖ ≤
      schwartzDerivativeDecayConstant F (A + K) K := by
  let M := A + K
  let T : ℝ := (SchwartzMap.seminorm ℝ 0 i) F +
    (SchwartzMap.seminorm ℝ M i) F
  let N : ℝ := ‖iteratedFDeriv ℝ i F u‖
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hpow : (1 + u) ^ (A + j) ≤ (1 + u) ^ M :=
    pow_le_pow_right₀ (by linarith) (by dsimp [M]; omega)
  have hadd := add_pow_le (show (0 : ℝ) ≤ 1 by norm_num) hu M
  have htwo : (2 : ℝ) ^ (M - 1) ≤ (2 : ℝ) ^ M :=
    pow_le_pow_right₀ (by norm_num) (Nat.sub_le M 1)
  have hsum : (1 + u) ^ M * N ≤ (2 : ℝ) ^ M *
      (N + u ^ M * N) := by
    calc
      (1 + u) ^ M * N ≤
          (2 : ℝ) ^ (M - 1) * (1 ^ M + u ^ M) * N :=
        mul_le_mul_of_nonneg_right hadd hN
      _ ≤ (2 : ℝ) ^ M * (1 ^ M + u ^ M) * N := by
        gcongr
      _ = (2 : ℝ) ^ M * (N + u ^ M * N) := by
        simp; ring
  have h0 : N ≤ (SchwartzMap.seminorm ℝ 0 i) F := by
    simpa [N] using SchwartzMap.le_seminorm ℝ 0 i F u
  have hM : u ^ M * N ≤ (SchwartzMap.seminorm ℝ M i) F := by
    simpa [N, Real.norm_eq_abs, abs_of_nonneg hu] using
      SchwartzMap.le_seminorm ℝ M i F u
  have hT : N + u ^ M * N ≤ T := add_le_add h0 hM
  have hTnonneg : 0 ≤ T := by dsimp [T]; positivity
  have hTsum : T ≤ ∑ k ∈ Finset.range (K + 1),
      ((SchwartzMap.seminorm ℝ 0 k) F +
        (SchwartzMap.seminorm ℝ M k) F) := by
    apply Finset.single_le_sum
      (f := fun k : ℕ =>
        (SchwartzMap.seminorm ℝ 0 k) F +
          (SchwartzMap.seminorm ℝ M k) F)
      (a := i)
    · intro k hk
      positivity
    · exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (hi.trans hj))
  calc
    (1 + u) ^ (A + j) * N ≤ (1 + u) ^ M * N :=
      mul_le_mul_of_nonneg_right hpow hN
    _ ≤ (2 : ℝ) ^ M * (N + u ^ M * N) := hsum
    _ ≤ (2 : ℝ) ^ M * T :=
      mul_le_mul_of_nonneg_left hT (by positivity)
    _ ≤ (2 : ℝ) ^ M *
        (∑ k ∈ Finset.range (K + 1),
          ((SchwartzMap.seminorm ℝ 0 k) F +
            (SchwartzMap.seminorm ℝ M k) F)) :=
      mul_le_mul_of_nonneg_left hTsum (by positivity)
    _ = schwartzDerivativeDecayConstant F (A + K) K := rfl

end FourierBridge

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorProfiles
namespace OAI

namespace SevenEighths.HeckeDetectorProfiles
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
noncomputable section

lemma expNeg_hasDerivAt (x : ℝ) : HasDerivAt expNeg (-expNeg x) x := by
  have h := ((Complex.ofRealCLM.hasDerivAt (x := x)).neg).cexp
  convert! (preTransparency := .instances) h using 1; simp [expNeg]

lemma iteratedDeriv_expNeg (n : ℕ) :
    iteratedDeriv n expNeg = fun x => (-1 : ℂ)^n*expNeg x := by
  induction n with
  | zero => ext x; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    rw [deriv_const_mul_field, (expNeg_hasDerivAt x).deriv, pow_succ]
    ring

lemma expNeg_derivative_norm (n : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ n expNeg x‖ = Real.exp (-x) := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_expNeg]
  simp [expNeg, norm_pow, Complex.norm_exp]

lemma expNeg_derivative_decay (n i : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    (1+x)^n*‖iteratedFDeriv ℝ i expNeg x‖ ≤ (n.factorial : ℝ)*Real.exp 1 := by
  rw [expNeg_derivative_norm]
  have hf : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hp := (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp (1+x) (by linarith : 0 ≤ 1+x) n)
  calc
    _ ≤ (Real.exp (1+x)*(n.factorial : ℝ))*Real.exp (-x) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = _ := by
      rw [mul_right_comm, ← Real.exp_add, show (1+x)+(-x) = 1 by ring]
      ring

end
end SevenEighths.HeckeDetectorProfiles

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorProfilesBounds
namespace OAI

namespace SevenEighths.HeckeDetectorProfiles
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
noncomputable section

theorem scaled_derivatives_of_decay (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (L : ℝ) (hL : 0 ≤ L) (K : ℕ) (CF : ℝ) (hCF : 0 ≤ CF)
    (hdecay : ∀ i ≤ K, ∀ u : ℝ, 0 ≤ u →
      (1+u)^K*‖iteratedFDeriv ℝ i F u‖ ≤ CF) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 ≤ R → ∀ j ≤ K, ∀ y : ℝ, |y| ≤ L →
      ‖iteratedFDeriv ℝ j (fun z => F (R*Real.exp z)) y‖ ≤ C := by
  let m := Real.exp (-L)
  let H := Real.exp L
  let S : ℝ := ∑ j ∈ Finset.range (K+1), (j.factorial : ℝ)*CF*(H^2)^j
  have hm : 0 < m := Real.exp_pos _
  have hH : 1 ≤ H := Real.one_le_exp_iff.mpr hL
  have hS : 0 ≤ S := by dsimp [S]; positivity
  refine ⟨S/m^K,by positivity,?_⟩
  intro R hR j hj y hy
  have hh := FourierBridge.coupled_factor_uniform_derivative F R 1 y m H CF 0 K j hF
    hR hm (Real.exp_le_one_iff.mpr (by linarith)) hH (by simpa using hH)
    (Real.exp_le_exp.mpr (by simpa using (abs_le.mp hy).1))
    (Real.exp_le_exp.mpr (by simpa using (abs_le.mp hy).2))
    hj hCF (by simpa using hdecay)
  simp only [zero_add, pow_zero, mul_one, one_mul] at hh
  have hs : (j.factorial : ℝ)*CF*(H^2)^j ≤ S := by
    dsimp only [S]
    apply Finset.single_le_sum (s := Finset.range (K+1))
      (f := fun i => (i.factorial : ℝ)*CF*(H^2)^i) (a := j)
    · intro i hi; positivity
    · exact Finset.mem_range.mpr (by omega)
  exact (le_div_iff₀ (pow_pos hm K)).mpr (by simpa [mul_comm] using hh.trans hs)

theorem scaled_schwartz_derivatives (F : SchwartzMap ℝ ℂ)
    (L : ℝ) (hL : 0 ≤ L) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 ≤ R → ∀ j ≤ K, ∀ y : ℝ, |y| ≤ L →
      ‖iteratedFDeriv ℝ j (fun z => F (R*Real.exp z)) y‖ ≤ C := by
  apply scaled_derivatives_of_decay F (F.smooth ⊤) L hL K
    (FourierBridge.schwartzDerivativeDecayConstant F K K)
    (FourierBridge.schwartzDerivativeDecayConstant_nonneg F K K)
  intro i hi u hu
  simpa using FourierBridge.schwartz_derivative_decay_finite F 0 K K i u le_rfl hi hu

theorem scaled_expNeg_derivatives (L : ℝ) (hL : 0 ≤ L) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 ≤ R → ∀ j ≤ K, ∀ y : ℝ, |y| ≤ L →
      ‖iteratedFDeriv ℝ j (fun z => expNeg (R*Real.exp z)) y‖ ≤ C := by
  apply scaled_derivatives_of_decay expNeg expNeg_smooth L hL K
    ((K.factorial : ℝ)*Real.exp 1) (by positivity)
  intro i hi u hu
  exact expNeg_derivative_decay K i u hu

lemma const_one_derivative_norm (j : ℕ) (y : ℝ) :
    ‖iteratedFDeriv ℝ j (fun _ : ℝ => (1 : ℂ)) y‖ ≤ 1 := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_const]
  split_ifs <;> simp

lemma complement_derivative_bound (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (C : ℝ) (j : ℕ) (y : ℝ) (hbound : ‖iteratedFDeriv ℝ j F y‖ ≤ C) :
    ‖iteratedFDeriv ℝ j (fun z => 1-F z) y‖ ≤ 1+C := by
  change ‖iteratedFDeriv ℝ j ((fun _ : ℝ => (1 : ℂ)) - F) y‖ ≤ _
  rw [iteratedFDeriv_sub contDiff_const (hF.of_le (by simp))]
  change ‖iteratedFDeriv ℝ j (fun _ : ℝ => (1 : ℂ)) y - iteratedFDeriv ℝ j F y‖ ≤ _
  exact (norm_sub_le _ _).trans (add_le_add (const_one_derivative_norm j y) hbound)

lemma product_derivative_bound (F G : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hG : ContDiff ℝ ∞ G) (CF CG : ℝ) (hCF : 0 ≤ CF) (hCG : 0 ≤ CG)
    (K j : ℕ) (hj : j ≤ K) (y : ℝ)
    (hFb : ∀ i ≤ K, ‖iteratedFDeriv ℝ i F y‖ ≤ CF)
    (hGb : ∀ i ≤ K, ‖iteratedFDeriv ℝ i G y‖ ≤ CG) :
    ‖iteratedFDeriv ℝ j (fun z => F z*G z) y‖ ≤ (2 : ℝ)^K*CF*CG := by
  apply (norm_iteratedFDeriv_mul_le hF hG y (n := j) (by simp)).trans
  calc
    _ ≤ ∑ i ∈ Finset.range (j+1), (j.choose i : ℝ)*CF*CG := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ j := by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hFb i (hi'.trans hj)) (by positivity))
        (hGb (j-i) ((Nat.sub_le j i).trans hj)) (norm_nonneg _) (by positivity)
    _ = (2 : ℝ)^j*CF*CG := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      congr 2
      exact_mod_cast Nat.sum_range_choose j
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hCF) hCG

end
end SevenEighths.HeckeDetectorProfiles

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorProfilesUniform
namespace OAI

namespace SevenEighths.HeckeDetectorProfiles
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
noncomputable section

lemma logSource_support (Ω V T : ℝ → ℂ) (A B C : ℝ) :
    tsupport (logSourceFun Ω V T A B C) ⊆ tsupport Ω :=
  tsupport_mul_subset_left.trans (tsupport_mul_subset_left.trans tsupport_mul_subset_left)

theorem logSource_window_derivatives (Ω : ℝ → ℂ) (V T : SchwartzMap ℝ ℂ)
    (hΩc : HasCompactSupport Ω) (hΩ : ContDiff ℝ ∞ Ω)
    (L : ℝ) (hL : 0 ≤ L) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A B D : ℝ, 0 ≤ A → 0 ≤ B → 0 ≤ D →
      ∀ j ≤ K, ∀ y : ℝ, |y| ≤ L →
      ‖iteratedFDeriv ℝ j (logSourceFun Ω V T A B D) y‖ ≤ C := by
  obtain ⟨CΩ,hCΩ,hbΩ⟩ := hΩc.exists_bound_iteratedFDeriv hΩ K
  obtain ⟨CV,hCV,hbV⟩ := scaled_schwartz_derivatives V L hL K
  obtain ⟨CT,hCT,hbT⟩ := scaled_schwartz_derivatives T L hL K
  obtain ⟨CE,hCE,hbE⟩ := scaled_expNeg_derivatives L hL K
  let P := (2 : ℝ)^K
  refine ⟨P*(P*(P*CΩ*(1+CV))*CE)*CT,by dsimp [P]; positivity,?_⟩
  intro A B D hA hB hD j hj y hy
  let v : ℝ → ℂ := fun z => V (A*Real.exp z)
  let e : ℝ → ℂ := fun z => expNeg (B*Real.exp z)
  let t : ℝ → ℂ := fun z => T (D*Real.exp z)
  have hv : ContDiff ℝ ∞ v := (V.smooth ⊤).comp (by fun_prop)
  have he : ContDiff ℝ ∞ e := expNeg_smooth.comp (by fun_prop)
  have ht : ContDiff ℝ ∞ t := (T.smooth ⊤).comp (by fun_prop)
  have hcv : ContDiff ℝ ∞ (fun z => 1-v z) := contDiff_const.sub hv
  have hcomp (i : ℕ) (hi : i ≤ K) : ‖iteratedFDeriv ℝ i (fun z => 1-v z) y‖ ≤ 1+CV :=
    complement_derivative_bound v hv CV i y (hbV A hA i hi y hy)
  have hfirst (i : ℕ) (hi : i ≤ K) :
      ‖iteratedFDeriv ℝ i (fun z => Ω z*(1-v z)) y‖ ≤ P*CΩ*(1+CV) :=
    product_derivative_bound Ω _ hΩ hcv CΩ (1+CV) hCΩ (by positivity) K i hi y
      (fun q hq => hbΩ q hq y) hcomp
  have hsecond (i : ℕ) (hi : i ≤ K) :
      ‖iteratedFDeriv ℝ i (fun z => Ω z*(1-v z)*e z) y‖ ≤ P*(P*CΩ*(1+CV))*CE :=
    product_derivative_bound _ e (hΩ.mul hcv) he _ CE (by dsimp [P]; positivity) hCE
      K i hi y hfirst (fun q hq => hbE B hB q hq y hy)
  exact product_derivative_bound _ t ((hΩ.mul hcv).mul he) ht _ CT
    (by dsimp [P]; positivity) hCT K j hj y hsecond (fun q hq => hbT D hD q hq y hy)

theorem logSource_uniform_seminorm (Ω : ℝ → ℂ) (V T : SchwartzMap ℝ ℂ)
    (hΩc : HasCompactSupport Ω) (hΩ : ContDiff ℝ ∞ Ω)
    (L : ℝ) (hL : 0 ≤ L) (hwindow : tsupport Ω ⊆ Set.Icc (-L) L) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A B D : ℝ, 0 ≤ A → 0 ≤ B → 0 ≤ D →
      ∀ k j : ℕ, j ≤ K →
      SchwartzMap.seminorm ℝ k j (logSource Ω V T hΩc hΩ (V.smooth ⊤) (T.smooth ⊤) A B D)
        ≤ L^k*C := by
  obtain ⟨C,hC,hb⟩ := logSource_window_derivatives Ω V T hΩc hΩ L hL K
  refine ⟨C,hC,?_⟩
  intro A B D hA hB hD k j hj
  apply SchwartzMap.seminorm_le_bound' ℝ k j _ (by positivity)
  intro y
  change ‖y‖^k*‖iteratedDeriv j (logSourceFun Ω V T A B D) y‖ ≤ L^k*C
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  by_cases hz : ‖iteratedFDeriv ℝ j (logSourceFun Ω V T A B D) y‖ = 0
  · rw [hz, mul_zero]; positivity
  have hys : y ∈ tsupport Ω := logSource_support Ω V T A B D
    ((support_iteratedFDeriv_subset j) (by simpa [Function.mem_support] using hz))
  have hy : |y| ≤ L := abs_le.mpr (hwindow hys)
  exact mul_le_mul (by simpa [Real.norm_eq_abs] using pow_le_pow_left₀ (abs_nonneg y) hy k)
    (hb A B D hA hB hD j hj y hy) (norm_nonneg _) (pow_nonneg hL k)

end
end SevenEighths.HeckeDetectorProfiles

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorFourier
namespace OAI

namespace SevenEighths.HeckeDetectorFourier
open MeasureTheory
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
open HeckeDetectorProfiles
noncomputable section

theorem uniform_fourier_moment (Ω : ℝ → ℂ) (V T : SchwartzMap ℝ ℂ)
    (hΩc : HasCompactSupport Ω) (hΩ : ContDiff ℝ ∞ Ω)
    (L : ℝ) (hL : 0 ≤ L) (hwindow : tsupport Ω ⊆ Set.Icc (-L) L) (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A B D : ℝ, 0 ≤ A → 0 ≤ B → 0 ≤ D →
      (∫ t : ℝ, (1+‖t‖)^J *
        ‖(𝓕 (logSource Ω V T hΩc hΩ (V.smooth ⊤) (T.smooth ⊤) A B D)) t‖) ≤ C := by
  let p := (volume : Measure ℝ).integrablePower
  obtain ⟨C,hC,hb⟩ := logSource_uniform_seminorm Ω V T hΩc hΩ L hL hwindow (J+p)
  let C' := (1+L^p)*C
  have hC' : 0 ≤ C' := by dsimp [C']; positivity
  refine ⟨(2 : ℝ)^J*(FourierBridge.coefficientMomentBound 0 C'+
    FourierBridge.coefficientMomentBound J C'),?_,?_⟩
  · exact mul_nonneg (by positivity) (add_nonneg
      (FourierBridge.coefficientMomentBound_nonneg 0 C' hC')
      (FourierBridge.coefficientMomentBound_nonneg J C' hC'))
  intro A B D hA hB hD
  have hh := FourierBridge.uniform_fourier_one_plus_moment
    (logSource Ω V T hΩc hΩ (V.smooth ⊤) (T.smooth ⊤) A B D) J 1 C'
    (by norm_num) hC' (by
      intro i hi
      have h0 := hb A B D hA hB hD 0 i hi
      have hp := hb A B D hA hB hD p i hi
      simp only [pow_zero, one_mul] at h0 ⊢
      dsimp only [C']
      linarith)
  simpa only [one_mul] using hh

theorem schwartz_weighted_tail (g : SchwartzMap ℝ ℂ) (J N : ℕ)
    (R : ℝ) (hR : 0 < R) :
    R^N*(∫ t : ℝ in {t | R < ‖t‖}, (1+‖t‖)^J*‖(𝓕 g) t‖) ≤
      ∫ t : ℝ, (1+‖t‖)^(J+N)*‖(𝓕 g) t‖ := by
  have hiJ := AnalyticBridge.schwartz_fourier_one_plus_integrable g J
  have hiN := AnalyticBridge.schwartz_fourier_one_plus_integrable g (J+N)
  have hs : MeasurableSet {t : ℝ | R < ‖t‖} := measurableSet_lt measurable_const continuous_norm.measurable
  rw [← integral_const_mul]
  apply (setIntegral_mono_on (hiJ.const_mul _).integrableOn hiN.integrableOn hs ?_).trans
    (setIntegral_le_integral hiN (Filter.Eventually.of_forall (by intro t; positivity)))
  intro t ht
  have hp : R^N ≤ (1+‖t‖)^N := pow_le_pow_left₀ hR.le (by change R < ‖t‖ at ht; linarith) N
  calc
    _ ≤ (1+‖t‖)^N*((1+‖t‖)^J*‖(𝓕 g) t‖) :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ = _ := by rw [pow_add]; ring

end
end SevenEighths.HeckeDetectorFourier

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorFourierSeparation
namespace OAI

namespace SevenEighths.HeckeDetectorFourier
open MeasureTheory
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
noncomputable section

lemma phasePolynomial_continuous {α : Type*} (S : Finset α) (a : α → ℂ) (x : α → ℝ) :
    Continuous (phasePolynomial S a x) := by
  apply continuous_finsetSum
  intro i hi
  exact continuous_const.mul (FourierBridge.logPhase_continuous_left _)

lemma phasePolynomial_norm {α : Type*} (S : Finset α) (a : α → ℂ) (x : α → ℝ) (t : ℝ) :
    ‖phasePolynomial S a x t‖ ≤ ∑ i ∈ S, ‖a i‖ := by
  calc
    _ ≤ ∑ i ∈ S, ‖a i*FourierBridge.logPhase t (x i)‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_mul, FourierBridge.logPhase_norm, mul_one]

lemma separated_pair_integrable {α β : Type*} (S : Finset α) (T : Finset β)
    (a : α → ℂ) (b : β → ℂ) (x : α → ℝ) (y : β → ℝ) (g : SchwartzMap ℝ ℂ) :
    Integrable (fun t => (𝓕 g) t*phasePolynomial S a x t*phasePolynomial T b y t) := by
  have hmeas : AEStronglyMeasurable (fun t => phasePolynomial S a x t*phasePolynomial T b y t) volume :=
    ((phasePolynomial_continuous S a x).mul
    (phasePolynomial_continuous T b y)).aestronglyMeasurable
  have hh := (𝓕 g).integrable.mul_bdd hmeas (Filter.Eventually.of_forall (fun t =>
    (norm_mul _ _).le.trans (mul_le_mul (phasePolynomial_norm S a x t)
      (phasePolynomial_norm T b y t) (norm_nonneg _) (Finset.sum_nonneg (fun i hi => norm_nonneg _)))))
  simpa only [mul_assoc] using hh

lemma schwartz_product_inversion (g : SchwartzMap ℝ ℂ) (x y : ℝ) :
    g (x+y) = ∫ t : ℝ,
      (𝓕 g) t*FourierBridge.logPhase t x*FourierBridge.logPhase t y := by
  rw [FourierBridge.schwartz_log_inversion g (x+y)]
  apply integral_congr_ae
  filter_upwards [] with t
  have hp : Complex.exp (↑(2*Real.pi*inner ℝ t (x+y))*Complex.I) =
      FourierBridge.logPhase t x*FourierBridge.logPhase t y := by
    rw [← FourierBridge.logPhase_add]
    simp only [FourierBridge.logPhase, RCLike.inner_apply, conj_trivial]
    congr 2
    ring_nf
  rw [hp]
  ring

theorem finite_pair_separation {α β : Type*} (S : Finset α) (T : Finset β)
    (a : α → ℂ) (b : β → ℂ) (x : α → ℝ) (y : β → ℝ) (g : SchwartzMap ℝ ℂ) :
    (∑ i ∈ S, ∑ j ∈ T, a i*b j*g (x i+y j)) =
      ∫ t : ℝ, (𝓕 g) t*phasePolynomial S a x t*phasePolynomial T b y t := by
  have hterm (i : α) (j : β) : Integrable (fun t : ℝ =>
      (𝓕 g) t*(a i*FourierBridge.logPhase t (x i))*(b j*FourierBridge.logPhase t (y j))) := by
    simpa only [phasePolynomial, Finset.sum_singleton] using
      separated_pair_integrable {i} {j} a b x y g
  have hsum (t : ℝ) : (𝓕 g) t*phasePolynomial S a x t*phasePolynomial T b y t =
      ∑ i ∈ S, ∑ j ∈ T,
        (𝓕 g) t*(a i*FourierBridge.logPhase t (x i))*(b j*FourierBridge.logPhase t (y j)) := by
    simp only [phasePolynomial, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_comm
  simp_rw [hsum]
  rw [integral_finsetSum S (fun i hi => integrable_finsetSum T (fun j hj => hterm i j))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum T (fun j hj => hterm i j)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [schwartz_product_inversion g (x i) (y j), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  ring

end
end SevenEighths.HeckeDetectorFourier

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorFourierActual
namespace OAI

namespace SevenEighths.HeckeDetectorFourier
open MeasureTheory
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
open HeckeFamily HeckeDetectorProfiles
noncomputable section

lemma scaled_exp_log_product (x y D N R : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hD : 0 < D) (hN : 0 < N) :
    (D*N/R)*Real.exp (Real.log (x/D)+Real.log (y/N)) = x*y/R := by
  rw [Real.exp_add, Real.exp_log (div_pos hx hD), Real.exp_log (div_pos hy hN)]
  field_simp

theorem actual_pair_profile (χ : Character) (Ω V T W₁ W₂ : ℝ → ℂ)
    (Dstar D N Y U : ℝ) (hD : 0 < D) (hN : 0 < N) (s : ℂ)
    (I J : Ideal O) (hI : I ≠ 0) (hJ : J ≠ 0)
    (hΩ : W₁ ((Ideal.absNorm I : ℝ)/D) ≠ 0 → W₂ ((Ideal.absNorm J : ℝ)/N) ≠ 0 →
      Ω (Real.log ((Ideal.absNorm I : ℝ)/D)+Real.log ((Ideal.absNorm J : ℝ)/N)) = 1) :
    HeckeDetectorPartition.pairCoefficient χ V T Dstar Y U s (I,J)*
      W₁ ((Ideal.absNorm I : ℝ)/D)*W₂ ((Ideal.absNorm J : ℝ)/N) =
      inverseCoefficient χ V W₁ Dstar D s I*plainCoefficient χ W₂ N s J*
        logSourceFun Ω V T (2*D*N/Dstar) (D*N/Y) (D*N/U)
          (Real.log ((Ideal.absNorm I : ℝ)/D)+Real.log ((Ideal.absNorm J : ℝ)/N)) := by
  by_cases hW₁ : W₁ ((Ideal.absNorm I : ℝ)/D) = 0
  · simp [hW₁, inverseCoefficient]
  by_cases hW₂ : W₂ ((Ideal.absNorm J : ℝ)/N) = 0
  · simp [hW₂, plainCoefficient]
  have hx : 0 < (Ideal.absNorm I : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hy : 0 < (Ideal.absNorm J : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  have hscale (R : ℝ) := scaled_exp_log_product (Ideal.absNorm I) (Ideal.absNorm J) D N R hx hy hD hN
  have htwo : (2*D*N/Dstar)*Real.exp
      (Real.log ((Ideal.absNorm I : ℝ)/D)+Real.log ((Ideal.absNorm J : ℝ)/N)) =
        2*((Ideal.absNorm I : ℝ)*(Ideal.absNorm J : ℝ))/Dstar := by
    calc
      _ = 2*((D*N/Dstar)*Real.exp
        (Real.log ((Ideal.absNorm I : ℝ)/D)+Real.log ((Ideal.absNorm J : ℝ)/N))) := by ring
      _ = _ := by rw [hscale]; ring
  unfold HeckeDetectorPartition.pairCoefficient inverseCoefficient plainCoefficient logSourceFun
  rw [hΩ hW₁ hW₂, one_mul, htwo, hscale Y, hscale U, map_mul]
  simp only [map_mul, Nat.cast_mul, expNeg]
  push_cast
  ring_nf

end
end SevenEighths.HeckeDetectorFourier

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorTail
namespace OAI

noncomputable section
open scoped BigOperators Classical Topology
open Filter
namespace SevenEighths.HeckeDetectorTail
open HeckeFamily HeckeDetectorWitnessArithmetic CompletedGauss
open IdealMobiusDivisorSum UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O

lemma weighted_norm_le_one (χ : Character) (s : ℂ) (hs : 0 ≤ s.re) (I : Ideal O) :
    ‖IdealEuler.weighted (idealCoeff χ) s I‖ ≤ 1 := by
  by_cases hI : I = 0
  · subst I
    rw [map_zero, norm_zero]
    norm_num
  have hN : 1 ≤ (Ideal.absNorm I : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  change ‖idealCoeff χ I*CubicEisenstein.fullIdealWeight s I‖ ≤ 1
  rw [norm_mul,CubicEisenstein.fullIdealWeight,if_neg hI]
  have hc : (Ideal.absNorm I : ℂ) = ((Ideal.absNorm I : ℝ) : ℂ) := by norm_cast
  rw [hc,Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : (0 : ℝ)<Ideal.absNorm I)]
  calc
    _ ≤ (1 : ℝ)*(Ideal.absNorm I : ℝ)^(-s.re) := by
      exact mul_le_mul_of_nonneg_right (idealCoeff_norm_le_one χ I) (by positivity)
    _ ≤ 1 := by
      simpa using Real.rpow_le_one_of_one_le_of_nonpos hN (neg_nonpos.mpr hs)

end SevenEighths.HeckeDetectorTail

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorCoefficientBounds
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.HeckeDetectorCoefficientBounds
open HeckeFamily HeckeDetectorFourier HeckeDetectorTail
open ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

lemma annular_norm_le_two (V : ℝ → ℂ) (hV : ∀ x, ‖V x‖ ≤ 1) (x : ℝ) :
    ‖DyadicTransfer.annularCutoff V x‖ ≤ 2 := by
  exact (norm_sub_le _ _).trans (by linarith [hV x,hV (2*x)])

lemma inverseCoefficient_norm_le_two (χ : Character) (V : ℝ → ℂ)
    (hV : ∀ x, ‖V x‖ ≤ 1) (Dstar D : ℝ) (s : ℂ) (hs : 0 ≤ s.re) (I : Ideal O) :
    ‖inverseCoefficient χ V (DyadicTransfer.annularCutoff V) Dstar D s I‖ ≤ 2 := by
  simp only [inverseCoefficient,norm_mul]
  calc
    _ ≤ (1 : ℝ)*1*1*2 := by
      gcongr
      · exact CubicEisenstein.norm_ideal_moebius_le_one I
      · exact weighted_norm_le_one χ s hs I
      · exact hV _
      · exact annular_norm_le_two V hV _
    _ = _ := by norm_num

lemma plainCoefficient_norm_le_two (χ : Character) (V : ℝ → ℂ)
    (hV : ∀ x, ‖V x‖ ≤ 1) (N : ℝ) (s : ℂ) (hs : 0 ≤ s.re) (I : Ideal O) :
    ‖plainCoefficient χ (DyadicTransfer.annularCutoff V) N s I‖ ≤ 2 := by
  simp only [plainCoefficient,norm_mul]
  calc
    _ ≤ (1 : ℝ)*2 := mul_le_mul (weighted_norm_le_one χ s hs I)
      (annular_norm_le_two V hV _) (norm_nonneg _) (by norm_num)
    _ = _ := by norm_num

lemma expandedSet_count (U : ℝ) (hU : 1 ≤ U) :
    ((expandedSet U).card : ℝ) ≤ 4096*U^21 := by
  have hp : 1 ≤ U^21 := one_le_pow₀ hU
  have hc : (1 : ℝ) ≤ ⌈16*U^21⌉₊ := (by linarith : (1 : ℝ) ≤ 16*U^21).trans (Nat.le_ceil _)
  have h := DescentFiberCost.finite_ideal_count_real (expandedSet U) (⌈16*U^21⌉₊ : ℝ) hc
    (fun I hI => Ideal.absNorm_eq_zero_iff.not.mp (by have := (mem_idealsUpTo.mp hI).1; omega))
    (fun I hI => by exact_mod_cast (mem_idealsUpTo.mp hI).2)
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ 16*U^21 by positivity)
  linarith

theorem coefficient_mass (χ : Character) (V : ℝ → ℂ) (hV : ∀ x, ‖V x‖ ≤ 1)
    (U Dstar D N : ℝ) (hU : 1 ≤ U) (s : ℂ) (hs : 0 ≤ s.re) :
    ((∑ I ∈ expandedSet U, ‖inverseCoefficient χ V (DyadicTransfer.annularCutoff V) Dstar D s I‖)*
      (∑ I ∈ expandedSet U, ‖plainCoefficient χ (DyadicTransfer.annularCutoff V) N s I‖)) ≤
      67108864*U^42 := by
  have hi : (∑ I ∈ expandedSet U,
      ‖inverseCoefficient χ V (DyadicTransfer.annularCutoff V) Dstar D s I‖) ≤ 8192*U^21 := by
    have h := Finset.sum_le_sum (s := expandedSet U)
      (fun I hI => inverseCoefficient_norm_le_two χ V hV Dstar D s hs I)
    simp only [Finset.sum_const, nsmul_eq_mul] at h
    linarith [expandedSet_count U hU]
  have hp : (∑ I ∈ expandedSet U,
      ‖plainCoefficient χ (DyadicTransfer.annularCutoff V) N s I‖) ≤ 8192*U^21 := by
    have h := Finset.sum_le_sum (s := expandedSet U)
      (fun I hI => plainCoefficient_norm_le_two χ V hV N s hs I)
    simp only [Finset.sum_const,nsmul_eq_mul] at h
    linarith [expandedSet_count U hU]
  have hh := mul_le_mul hi hp
    (Finset.sum_nonneg (fun I hI => norm_nonneg _)) (by positivity)
  apply hh.trans_eq
  ring

end SevenEighths.HeckeDetectorCoefficientBounds

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorFinite
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.HeckeDetectorFinite
open HeckeFamily HeckeDetectorWitnessArithmetic HeckeDetectorTail HeckeDetectorPartition
open CompletedGauss ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

lemma pairCoefficient_zero_left (χ : Character) (V T : ℝ → ℂ) (D Y U : ℝ) (s : ℂ) (J : Ideal O) :
    pairCoefficient χ V T D Y U s (0,J) = 0 := by
  simp only [pairCoefficient,zero_mul,map_zero,mul_zero]

lemma pairCoefficient_zero_right (χ : Character) (V T : ℝ → ℂ) (D Y U : ℝ) (s : ℂ) (J : Ideal O) :
    pairCoefficient χ V T D Y U s (J,0) = 0 := by
  simp only [pairCoefficient,mul_zero,map_zero,zero_mul]

theorem pairCoefficient_support (χ : Character) (V T : ℝ → ℂ) (D Y U : ℝ)
    (hU : 0 < U) (hT : ∀ x : ℝ, 2 ≤ x → T x = 0) (s : ℂ)
    (p : Ideal O × Ideal O) (hp : p ∉ pairSet U) :
    pairCoefficient χ V T D Y U s p = 0 := by
  by_cases h1 : p.1 = 0
  · change pairCoefficient χ V T D Y U s (p.1,p.2) = 0
    rw [h1]
    exact pairCoefficient_zero_left χ V T D Y U s p.2
  by_cases h2 : p.2 = 0
  · change pairCoefficient χ V T D Y U s (p.1,p.2) = 0
    rw [h2]
    exact pairCoefficient_zero_right χ V T D Y U s p.1
  have hprod : p.1*p.2 ≠ 0 := mul_ne_zero h1 h2
  have hnpos : 0 < Ideal.absNorm (p.1*p.2) := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hprod)
  have hnorm : 2*U ≤ (Ideal.absNorm (p.1*p.2) : ℝ) := by
    by_contra h
    have hb : Ideal.absNorm (p.1*p.2) ≤ ⌈2*U⌉₊ := by
      exact_mod_cast (le_trans (lt_of_not_ge h).le (Nat.le_ceil (2*U)))
    have hh1 : Ideal.absNorm p.1 ≤ Ideal.absNorm (p.1*p.2) :=
      Nat.le_of_dvd hnpos (map_dvd Ideal.absNorm (dvd_mul_right p.1 p.2))
    have hh2 : Ideal.absNorm p.2 ≤ Ideal.absNorm (p.1*p.2) :=
      Nat.le_of_dvd hnpos (map_dvd Ideal.absNorm (dvd_mul_left p.2 p.1))
    apply hp
    exact Finset.mem_product.mpr
      ⟨mem_idealsUpTo.mpr ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr h1),hh1.trans hb⟩,
       mem_idealsUpTo.mpr ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr h2),hh2.trans hb⟩⟩
  have hz := hT ((Ideal.absNorm (p.1*p.2) : ℝ)/U) ((le_div_iff₀ hU).mpr hnorm)
  simp only [pairCoefficient,hz,mul_zero]

end SevenEighths.HeckeDetectorFinite

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorDyadicSupport
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.HeckeDetectorDyadicBridge
open HeckeFamily HeckeDetectorFinite HeckeDetectorPartition
open CompletedGauss ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

lemma fourierSet_nonzero (U : ℝ) (J : Ideal O) (hJ : J∈fourierSet U) : J≠0 := by
  have hn := (mem_idealsUpTo.mp hJ).1
  exact Ideal.absNorm_eq_zero_iff.not.mp (by omega)

lemma pairSet_subset_fourier (U : ℝ) (hU : 0≤U) :
    pairSet U ⊆ fourierSet U ×ˢ fourierSet U := by
  intro p hp
  obtain ⟨h1,h2⟩ := Finset.mem_product.mp hp
  have hb : ⌈2*U⌉₊ ≤ ⌈16*U⌉₊ := Nat.ceil_mono (by linarith)
  exact Finset.mem_product.mpr
    ⟨mem_idealsUpTo.mpr ⟨(mem_idealsUpTo.mp h1).1,(mem_idealsUpTo.mp h1).2.trans hb⟩,
     mem_idealsUpTo.mpr ⟨(mem_idealsUpTo.mp h2).1,(mem_idealsUpTo.mp h2).2.trans hb⟩⟩

theorem dyadicBlock_eq_fourier_rectangle (χ : Character) (V T : ℝ→ℂ)
    (D Y U : ℝ) (hU : 0<U) (hT : ∀ x : ℝ, 2≤x → T x=0)
    (s : ℂ) (j k : ℕ) :
    dyadicBlock χ V T D Y U s j k =
      ∑ J∈fourierSet U, ∑ K∈fourierSet U,
        pairCoefficient χ V T D Y U s (J,K)*
          DyadicTransfer.annularCutoff V ((J.absNorm : ℝ)/(2 : ℝ)^j)*
          DyadicTransfer.annularCutoff V ((K.absNorm : ℝ)/(2 : ℝ)^k) := by
  unfold dyadicBlock
  calc
    _ = ∑ p∈fourierSet U ×ˢ fourierSet U,
        pairCoefficient χ V T D Y U s p *
          DyadicTransfer.annularCutoff V ((p.1.absNorm : ℝ)/(2 : ℝ)^j) *
          DyadicTransfer.annularCutoff V ((p.2.absNorm : ℝ)/(2 : ℝ)^k) := by
      apply Finset.sum_subset (pairSet_subset_fourier U hU.le)
      intro p hp hn
      rw [pairCoefficient_support χ V T D Y U hU hT s p hn, zero_mul, zero_mul]
    _ = _ := Finset.sum_product _ _ _

end SevenEighths.HeckeDetectorDyadicBridge

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorFourierWitness
namespace OAI

namespace SevenEighths.HeckeDetectorFourier
open MeasureTheory
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
noncomputable section

lemma frequency_interval_compl (R : ℝ) :
    (Set.Icc (-R) R)ᶜ = {t : ℝ | R < ‖t‖} := by
  ext t
  simp only [Set.mem_compl_iff, Set.mem_Icc, Set.mem_ofPred_eq, Real.norm_eq_abs,
    ← abs_le, not_le]

private lemma exists_interval_norm_product (f h : ℝ → ℂ) (hf : Continuous f)
    (hh : Integrable h) (hprod : Integrable (fun u => h u * f u))
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ t : ℝ, ‖t‖ ≤ R ∧
      ‖∫ u : ℝ in Set.Icc (-R) R, h u * f u‖ ≤ (∫ u : ℝ, ‖h u‖) * ‖f t‖ := by
  obtain ⟨t, ht, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Set.Icc (-R) R).Nonempty from ⟨0, by constructor <;> linarith⟩)
    hf.norm.continuousOn
  refine ⟨t, by simpa only [Real.norm_eq_abs, abs_le, Set.mem_Icc] using ht, ?_⟩
  have hb : Integrable (fun u => ‖h u‖ * ‖f t‖) := hh.norm.mul_const _
  calc
    _ ≤ ∫ u : ℝ in Set.Icc (-R) R, ‖h u * f u‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u : ℝ in Set.Icc (-R) R, ‖h u‖ * ‖f t‖ := by
      apply setIntegral_mono_on hprod.norm.integrableOn hb.integrableOn measurableSet_Icc
      intro u hu
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hmax hu) (norm_nonneg _)
    _ ≤ ∫ u : ℝ, ‖h u‖ * ‖f t‖ :=
      setIntegral_le_integral hb (Filter.Eventually.of_forall (by intro u; positivity))
    _ = _ := integral_mul_const _ _

theorem exists_interval_frequency {α β : Type*} (S : Finset α) (T : Finset β)
    (a : α → ℂ) (b : β → ℂ) (x : α → ℝ) (y : β → ℝ)
    (g : SchwartzMap ℝ ℂ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ t : ℝ, ‖t‖ ≤ R ∧
      ‖∫ u : ℝ in Set.Icc (-R) R,
        (𝓕 g) u*phasePolynomial S a x u*phasePolynomial T b y u‖ ≤
        (∫ u : ℝ, ‖(𝓕 g) u‖)*
          ‖phasePolynomial S a x t*phasePolynomial T b y t‖ := by
  have hf : Continuous (fun u => phasePolynomial S a x u * phasePolynomial T b y u) :=
    (phasePolynomial_continuous S a x).mul (phasePolynomial_continuous T b y)
  have hi : Integrable (fun u => (𝓕 g) u *
      (phasePolynomial S a x u * phasePolynomial T b y u)) := by
    simpa only [mul_assoc] using separated_pair_integrable S T a b x y g
  obtain ⟨t, ht, hb⟩ := exists_interval_norm_product
    (fun u => phasePolynomial S a x u * phasePolynomial T b y u)
    (fun u => (𝓕 g) u) hf (𝓕 g).integrable hi R hR
  exact ⟨t, ht, by simpa only [mul_assoc] using hb⟩

private theorem integral_sub_interval_norm_le (f w : ℝ → ℂ) (E R : ℝ)
    (hf : Integrable f) (hw : Integrable w)
    (hbound : ∀ u, ‖f u‖ ≤ E * ‖w u‖) :
    ‖(∫ u : ℝ, f u) - (∫ u : ℝ in Set.Icc (-R) R, f u)‖ ≤
      E * (∫ u : ℝ in {u | R < ‖u‖}, ‖w u‖) := by
  have hsplit := integral_add_compl (s := Set.Icc (-R) R) measurableSet_Icc hf
  have heq : (∫ u : ℝ, f u) - (∫ u : ℝ in Set.Icc (-R) R, f u) =
      ∫ u : ℝ in {u | R < ‖u‖}, f u := by
    rw [← hsplit, frequency_interval_compl]
    abel
  rw [heq]
  have hm : MeasurableSet {u : ℝ | R < ‖u‖} :=
    measurableSet_lt measurable_const continuous_norm.measurable
  calc
    _ ≤ ∫ u : ℝ in {u | R < ‖u‖}, ‖f u‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u : ℝ in {u | R < ‖u‖}, E * ‖w u‖ :=
      setIntegral_mono_on hf.norm.integrableOn (hw.norm.const_mul E).integrableOn hm
        (fun u _ => hbound u)
    _ = _ := integral_const_mul _ _

private theorem separated_pair_norm_le {α β : Type*} (S : Finset α) (T : Finset β)
    (a : α → ℂ) (b : β → ℂ) (x : α → ℝ) (y : β → ℝ) (z : ℂ) (u : ℝ) :
    ‖z * phasePolynomial S a x u * phasePolynomial T b y u‖ ≤
      ((∑ i ∈ S, ‖a i‖) * (∑ j ∈ T, ‖b j‖)) * ‖z‖ := by
  rw [mul_assoc, norm_mul, norm_mul, mul_comm ‖z‖]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg z)
  exact mul_le_mul (phasePolynomial_norm S a x u) (phasePolynomial_norm T b y u)
    (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))

private theorem schwartz_tail_le (g : SchwartzMap ℝ ℂ) (R : ℝ)
    (hR : 0 < R) (N : ℕ) :
    (∫ u : ℝ in {u | R < ‖u‖}, ‖(𝓕 g) u‖) ≤
      (∫ u : ℝ, (1+‖u‖)^N * ‖(𝓕 g) u‖) / R^N := by
  apply (le_div_iff₀ (pow_pos hR N)).mpr
  simpa only [pow_zero, one_mul, Nat.zero_add, mul_comm] using
    schwartz_weighted_tail g 0 N R hR

private theorem separated_pair_tail_of_bound {α β : Type*} (S : Finset α) (T : Finset β)
    (a : α → ℂ) (b : β → ℂ) (x : α → ℝ) (y : β → ℝ)
    (w : ℝ → ℂ) (R M : ℝ) (N : ℕ)
    (hi : Integrable (fun u => w u * phasePolynomial S a x u * phasePolynomial T b y u))
    (hw : Integrable w) (hbound : (∫ u : ℝ in {u | R < ‖u‖}, ‖w u‖) ≤ M / R^N) :
    ‖(∫ u : ℝ, w u * phasePolynomial S a x u * phasePolynomial T b y u) -
      (∫ u : ℝ in Set.Icc (-R) R,
        w u * phasePolynomial S a x u * phasePolynomial T b y u)‖ ≤
      ((∑ i ∈ S, ‖a i‖) * (∑ j ∈ T, ‖b j‖)) / R^N * M := by
  let E := (∑ i ∈ S, ‖a i‖) * (∑ j ∈ T, ‖b j‖)
  have hE : 0 ≤ E := mul_nonneg
    (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
    (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  have htail := integral_sub_interval_norm_le
    (fun u => w u * phasePolynomial S a x u * phasePolynomial T b y u)
    w E R hi hw (fun u => separated_pair_norm_le S T a b x y (w u) u)
  calc
    _ ≤ E * (∫ u : ℝ in {u | R < ‖u‖}, ‖w u‖) := htail
    _ ≤ E * (M / R^N) := mul_le_mul_of_nonneg_left hbound hE
    _ = _ := by rw [div_mul_eq_mul_div, mul_div_assoc]

theorem separated_pair_tail {α β : Type*} (S : Finset α) (T : Finset β)
    (a : α → ℂ) (b : β → ℂ) (x : α → ℝ) (y : β → ℝ)
    (g : SchwartzMap ℝ ℂ) (R : ℝ) (hR : 0 < R) (N : ℕ) :
    ‖(∫ u : ℝ, (𝓕 g) u*phasePolynomial S a x u*phasePolynomial T b y u) -
      (∫ u : ℝ in Set.Icc (-R) R,
        (𝓕 g) u*phasePolynomial S a x u*phasePolynomial T b y u)‖ ≤
      ((∑ i ∈ S, ‖a i‖)*(∑ j ∈ T, ‖b j‖))/R^N *
        (∫ u : ℝ, (1+‖u‖)^N*‖(𝓕 g) u‖) := by
  exact separated_pair_tail_of_bound S T a b x y (fun u : ℝ => (𝓕 g : SchwartzMap ℝ ℂ) u)
    R (∫ u : ℝ, (1+‖u‖)^N * ‖(𝓕 g) u‖) N
    (separated_pair_integrable S T a b x y g) (𝓕 g).integrable
    (schwartz_tail_le g R hR N)

theorem exists_bounded_frequency {α β : Type*} (S : Finset α) (T : Finset β)
    (a : α → ℂ) (b : β → ℂ) (x : α → ℝ) (y : β → ℝ)
    (g : SchwartzMap ℝ ℂ) (R : ℝ) (hR : 0 < R) (N : ℕ) :
    ∃ t : ℝ, ‖t‖ ≤ R ∧
      ‖∑ i ∈ S, ∑ j ∈ T, a i*b j*g (x i+y j)‖ ≤
      ((∑ i ∈ S, ‖a i‖)*(∑ j ∈ T, ‖b j‖))/R^N *
        (∫ u : ℝ, (1+‖u‖)^N*‖(𝓕 g) u‖) +
      (∫ u : ℝ, ‖(𝓕 g) u‖)*
        ‖phasePolynomial S a x t*phasePolynomial T b y t‖ := by
  obtain ⟨t,ht,hb⟩ := exists_interval_frequency S T a b x y g R hR.le
  refine ⟨t,ht,?_⟩
  rw [finite_pair_separation]
  have htail := separated_pair_tail S T a b x y g R hR N
  exact (norm_le_norm_sub_add _ _).trans (add_le_add htail hb)

end
end SevenEighths.HeckeDetectorFourier

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorProfilesCutoffs
namespace OAI

namespace SevenEighths.HeckeDetectorProfiles
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
noncomputable section

lemma cutoff_norm_le (x : ℝ) : ‖cutoff x‖ ≤ 1 := by
  rw [QuadraticInitialBound.sieveCutoff_apply, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg QuadraticInitialBound.sieveBump.nonneg]
  exact QuadraticInitialBound.sieveBump.le_one

end
end SevenEighths.HeckeDetectorProfiles

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorFrequency
namespace OAI

noncomputable section
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
open MeasureTheory
namespace SevenEighths.HeckeDetectorFrequency
open HeckeFamily HeckeDetectorProfiles HeckeDetectorFourier
open HeckeDetectorCoefficientBounds HeckeDetectorFinite HeckeDetectorDyadicBridge
local notation "O" => HeckeFamily.O

theorem dyadic_frequency_bound_oai (Ω : ℝ → ℂ)
    (hΩc : HasCompactSupport Ω) (hΩ : ContDiff ℝ ∞ Ω)
    (L : ℝ) (hL : 0 ≤ L) (hwindow : tsupport Ω ⊆ Set.Icc (-L) L)
    (hΩone : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
      DyadicTransfer.annularCutoff cutoff x ≠ 0 →
      DyadicTransfer.annularCutoff cutoff y ≠ 0 → Ω (Real.log x+Real.log y)=1)
    (n : ℕ) :
    ∃ C₀ Cn : ℝ, 1 ≤ C₀ ∧ 0 ≤ Cn ∧ ∀ (U Dstar F : ℝ),
      1 ≤ U → 0 < Dstar → 0 < F → ∀ (χ : Character) (s : ℂ), 0 ≤ s.re →
      ∀ j k : ℕ, ∃ t : ℝ, ‖t‖ ≤ F ∧
        ‖dyadicBlock χ cutoff cutoff Dstar (U^20) (U^21) s j k‖ ≤
          (67108864*U^42)*Cn/F^n + C₀*
            ‖phasePolynomial (expandedSet U)
                (inverseCoefficient χ cutoff (DyadicTransfer.annularCutoff cutoff) Dstar ((2 : ℝ)^j) s)
                (fun I => Real.log ((Ideal.absNorm I : ℝ)/(2 : ℝ)^j)) t *
              phasePolynomial (expandedSet U)
                (plainCoefficient χ (DyadicTransfer.annularCutoff cutoff) ((2 : ℝ)^k) s)
                (fun I => Real.log ((Ideal.absNorm I : ℝ)/(2 : ℝ)^k)) t‖ := by
  obtain ⟨C₀,hC₀,hb₀⟩ := uniform_fourier_moment Ω cutoff cutoff hΩc hΩ L hL hwindow 0
  obtain ⟨Cn,hCn,hbn⟩ := uniform_fourier_moment Ω cutoff cutoff hΩc hΩ L hL hwindow n
  refine ⟨1+C₀,Cn,by linarith,hCn,?_⟩
  intro U Dstar F hU hDstar hF χ s hs j k
  let D : ℝ := (2 : ℝ)^j
  let N : ℝ := (2 : ℝ)^k
  let a := inverseCoefficient χ cutoff (DyadicTransfer.annularCutoff cutoff) Dstar D s
  let b := plainCoefficient χ (DyadicTransfer.annularCutoff cutoff) N s
  let x := fun I : Ideal O => Real.log ((Ideal.absNorm I : ℝ)/D)
  let y := fun I : Ideal O => Real.log ((Ideal.absNorm I : ℝ)/N)
  let g := logSource Ω cutoff cutoff hΩc hΩ (cutoff.smooth ⊤) (cutoff.smooth ⊤)
    (2*D*N/Dstar) (D*N/U^20) (D*N/U^21)
  have hUpos : 0 < U := by linarith
  have hD : 0 < D := by dsimp [D]; positivity
  have hN : 0 < N := by dsimp [N]; positivity
  have heq : dyadicBlock χ cutoff cutoff Dstar (U^20) (U^21) s j k =
      ∑ I ∈ expandedSet U, ∑ J ∈ expandedSet U, a I*b J*g (x I+y J) := by
    rw [dyadicBlock_eq_fourier_rectangle χ cutoff cutoff Dstar (U^20) (U^21)
      (by positivity) cutoff_zero s j k]
    apply Finset.sum_congr rfl
    intro I hI
    apply Finset.sum_congr rfl
    intro J hJ
    exact actual_pair_profile χ Ω cutoff cutoff (DyadicTransfer.annularCutoff cutoff)
      (DyadicTransfer.annularCutoff cutoff) Dstar D N (U^20) (U^21) hD hN s I J
      (fourierSet_nonzero _ I hI) (fourierSet_nonzero _ J hJ)
      (hΩone _ _ (by positivity) (by positivity))
  obtain ⟨t,ht,hb⟩ := exists_bounded_frequency (expandedSet U) (expandedSet U) a b x y g F hF n
  refine ⟨t,ht,?_⟩
  rw [heq]
  have hg₀ : (∫ t : ℝ, ‖(𝓕 g) t‖) ≤ C₀ := by
    simpa only [pow_zero,one_mul] using hb₀ (2*D*N/Dstar) (D*N/U^20) (D*N/U^21)
      (by positivity) (by positivity) (by positivity)
  have hgn : (∫ t : ℝ, (1+‖t‖)^n*‖(𝓕 g) t‖) ≤ Cn :=
    hbn (2*D*N/Dstar) (D*N/U^20) (D*N/U^21) (by positivity) (by positivity) (by positivity)
  have hmass := coefficient_mass χ cutoff cutoff_norm_le U Dstar D N hU s hs
  apply hb.trans
  apply add_le_add
  · calc
      _ ≤ ((67108864*U^42)/F^n)*Cn := by
        apply mul_le_mul
        · exact div_le_div_of_nonneg_right hmass (by positivity)
        · exact hgn
        · exact integral_nonneg (fun t => by positivity)
        · positivity
      _ = _ := by ring
  · exact mul_le_mul_of_nonneg_right (hg₀.trans (by linarith)) (norm_nonneg _)

end SevenEighths.HeckeDetectorFrequency

end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.HeckeDetectorFrequency.dyadic_frequency_bound_oai := @OAI.SevenEighths.HeckeDetectorFrequency.dyadic_frequency_bound_oai
