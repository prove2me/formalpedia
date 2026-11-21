-- Prove2me | solution 2 for MasulloRH.trace_formula_rational_full_strip
-- status  : ACCEPTED   (prove)
-- author  : @smmercuri
-- created : 2026-11-20T22:30:24.558903+00:00
-- url     : https://prove2.me/submissions/ece5dd50-7b49-412f-b844-2b2b3d986c61

import Definitions.Def_MasulloRH_RationalTrace
import Theorems.Thm_ConnesRZ_explicit_formula_C2
import Theorems.Thm_ConnesRZ_archTerm_eq_neg_setIntegral_of_apply_zero

set_option autoImplicit false

open MeasureTheory Set
open scoped Topology
open MasulloRH

namespace MasulloRHHalf

open ConnesRZ

/-- Mellin transform in exponential coordinates. -/
theorem mellin_eq_integral_exp (φ : ℝ → ℂ) (s : ℂ) :
    mellin φ s = ∫ x : ℝ, φ (Real.exp x) * Complex.exp (s * x) := by
  rw [mellin, ← Real.range_exp, ← Set.image_univ,
    integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn,
    setIntegral_univ]
  congr 1
  funext x
  have hx : (Real.exp x : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos x).ne'
  rw [abs_of_pos (Real.exp_pos x), Complex.cpow_def_of_ne_zero hx,
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]
  simp only [Complex.real_smul, smul_eq_mul, Complex.ofReal_exp]
  rw [← mul_assoc, ← Complex.exp_add, mul_comm]
  congr 2
  ring

theorem mellinHat_eq (φ : ℝ → ℂ) (z : ℂ) :
    mellinHat (fun x => φ (Real.exp x)) z = mellin φ (z - 1 / 2) := by
  rw [mellin_eq_integral_exp]
  rfl

theorem isTest (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    IsTest (fun x => φ (Real.exp x)) := by
  obtain ⟨hs, hc, hsub, _⟩ := hφ
  refine ⟨hs.comp Real.contDiff_exp, ?_⟩
  refine HasCompactSupport.intro (K := Real.log '' tsupport φ)
    (hc.isCompact.image_of_continuousOn
      (Real.continuousOn_log.mono fun t ht => (hsub ht).ne')) ?_
  intro x hx
  by_contra h
  exact hx ⟨Real.exp x, subset_tsupport _ h, Real.log_exp x⟩

theorem exists_bound (g : ℝ → ℂ) (hg : HasCompactSupport g) :
    ∃ R : ℝ, ∀ x, R < |x| → g x = 0 := by
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1 hg.isCompact.isBounded
  refine ⟨r, fun x hx => image_eq_zero_of_notMem_tsupport fun h => ?_⟩
  have := hr h
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
  linarith

theorem prime_hasSum (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    HasSum (primePowerTraceTerm φ) (primeSum (fun x => φ (Real.exp x))) := by
  set F : ℕ → ℂ := fun n => ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
    (φ (Real.exp (Real.log n)) + φ (Real.exp (-Real.log n))) with hF
  obtain ⟨R, hR⟩ := exists_bound _ (isTest φ hφ).2
  have hFs : Summable F := by
    obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp R)
    refine summable_of_ne_finset_zero (s := Finset.range (N + 1)) fun n hn => ?_
    simp only [Finset.mem_range, not_lt] at hn
    have hn' : (N : ℝ) + 1 ≤ n := by exact_mod_cast hn
    have hlog : R < Real.log n := by
      rw [Real.lt_log_iff_exp_lt (by linarith)]
      linarith
    have h1 : φ (Real.exp (Real.log n)) = 0 := hR (Real.log n) (hlog.trans_le (le_abs_self _))
    have h2 : φ (Real.exp (-Real.log n)) = 0 :=
      hR (-Real.log n) (by rw [abs_neg]; exact hlog.trans_le (le_abs_self _))
    simp only [hF, h1, h2, add_zero, mul_zero]
  have he : Function.Injective (fun i : Nat.Primes × ℕ => (i.1 : ℕ) ^ (i.2 + 1)) := by
    rintro ⟨p, k⟩ ⟨q, j⟩ h
    obtain ⟨h1, h2⟩ := Nat.Prime.pow_inj p.2 q.2 h
    exact Prod.ext (Subtype.ext h1) h2
  have hrange : ∀ n ∉ Set.range (fun i : Nat.Primes × ℕ => (i.1 : ℕ) ^ (i.2 + 1)),
      F n = 0 := by
    intro n hn
    have : ArithmeticFunction.vonMangoldt n = 0 := by
      rw [ArithmeticFunction.vonMangoldt_eq_zero_iff, isPrimePow_nat_iff]
      rintro ⟨p, k, hp, hk, rfl⟩
      exact hn ⟨(⟨p, hp⟩, k - 1), by simp only; rw [Nat.sub_add_cancel hk]⟩
    simp [hF, this]
  have hcomp : F ∘ (fun i : Nat.Primes × ℕ => (i.1 : ℕ) ^ (i.2 + 1)) =
      primePowerTraceTerm φ := by
    funext ⟨p, k⟩
    have hp : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
    have hx : (0 : ℝ) < ((p : ℕ) : ℝ) ^ (k + 1) := pow_pos hp _
    simp only [Function.comp, hF, primePowerTraceTerm, Nat.cast_pow]
    rw [Real.exp_log hx, Real.exp_neg, Real.exp_log hx,
      ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero k),
      ArithmeticFunction.vonMangoldt_apply_prime p.2]
  rw [← hcomp, he.hasSum_iff hrange]
  exact hFs.hasSum

theorem key_real (x : ℝ) (hx : 0 < x) :
    Real.exp x * (Real.sqrt (Real.exp x) / (Real.exp x ^ 2 - 1)) =
      Real.exp (-x / 2) / (1 - Real.exp (-2 * x)) := by
  have hy : 1 < Real.exp (x / 2) := Real.one_lt_exp_iff.2 (by linarith)
  have hsq : Real.sqrt (Real.exp x) = Real.exp (x / 2) := (Real.exp_half x).symm
  have he : Real.exp x = Real.exp (x / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hn : Real.exp (-x / 2) = (Real.exp (x / 2))⁻¹ := by
    rw [← Real.exp_neg]; congr 1; ring
  have hn2 : Real.exp (-2 * x) = (Real.exp (x / 2) ^ 4)⁻¹ := by
    rw [← Real.exp_nat_mul, ← Real.exp_neg]; congr 1; push_cast; ring
  rw [hsq, hn, hn2, he]
  set y := Real.exp (x / 2)
  have h4 : y ^ 4 ≠ 1 := by
    have : 1 < y ^ 4 := one_lt_pow₀ hy (by norm_num)
    exact this.ne'
  have h4' : (y ^ 2) ^ 2 - 1 ≠ 0 := by
    intro h; apply h4; linear_combination h
  have hy0 : y ≠ 0 := by positivity
  have h5 : 1 - (y ^ 4)⁻¹ ≠ 0 := by
    intro h; apply h4
    field_simp at h
    linear_combination h
  field_simp

theorem arch (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    IntegrableOn (realTraceIntegrand φ) (Ioi 1) ∧
      ∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t = -archTerm (fun x => φ (Real.exp x)) := by
  have hT := isTest φ hφ
  have h0 : (fun x => φ (Real.exp x)) 0 = 0 := by simp [hφ.2.2.2]
  obtain ⟨hint, heq⟩ := archTerm_eq_neg_setIntegral_of_apply_zero _ hT h0
  have hpt : ∀ x ∈ Ioi (0 : ℝ), Real.exp x • realTraceIntegrand φ (Real.exp x) =
      (φ (Real.exp x) + φ (Real.exp (-x))) *
        ((Real.exp (-x / 2) / (1 - Real.exp (-2 * x)) : ℝ) : ℂ) := by
    intro x hx
    rw [realTraceIntegrand, ← Real.exp_neg, Complex.real_smul, ← key_real x hx]
    push_cast
    ring
  have hint' : IntegrableOn (fun x => Real.exp x • realTraceIntegrand φ (Real.exp x)) (Ioi 0) :=
    hint.congr_fun (fun x hx => (hpt x hx).symm) measurableSet_Ioi
  have hI := (integrableOn_comp_exp_Ioi (realTraceIntegrand φ) 0).1 hint'
  rw [Real.exp_zero] at hI
  refine ⟨hI, ?_⟩
  have := integral_comp_exp_Ioi (realTraceIntegrand φ) 0
  rw [Real.exp_zero] at this
  rw [← this, heq, neg_neg]
  exact setIntegral_congr_fun measurableSet_Ioi hpt

theorem zeros (α : ℝ) (hα : 1 / 2 ≤ α) (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    HasSum (zetaTraceTerm φ α) (weilDistribution (fun x => φ (Real.exp x))) := by
  have hT := isTest φ hφ
  have H := explicit_formula_C2 _ (hT.1.of_le (WithTop.coe_le_coe.2 le_top)) hT.2
  let e : ZetaZerosInTraceStrip α ≃ {s : ℂ // IsCriticalZero s} :=
    Equiv.subtypeEquivRight (fun s => ⟨fun h => ⟨h.1, h.2.1, h.2.2.1⟩,
      fun h => ⟨h.1, h.2.1, h.2.2, by
        rw [abs_lt]; constructor <;> linarith [h.2.1, h.2.2]⟩⟩)
  rw [← e.hasSum_iff] at H
  convert H using 1
  funext ρ
  simp only [Function.comp, zetaTraceTerm, e, Equiv.subtypeEquivRight_apply_coe, zeroMult,
    mellinHat_eq]

end MasulloRHHalf

theorem MasulloRHHalf.main (α : ℝ) (hα : 1 / 2 ≤ α) (φ : ℝ → ℂ)
    (hφ : IsRationalTraceTest φ) :
    IntegrableOn (realTraceIntegrand φ) (Ioi 1) ∧
    Summable (primePowerTraceTerm φ) ∧
    Summable (zetaTraceTerm φ α) ∧
    (∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) +
      (∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i) =
      mellin φ (1 / 2) + mellin φ (-1 / 2) -
        ∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ := by
  obtain ⟨hI, hIeq⟩ := MasulloRHHalf.arch φ hφ
  have hP := MasulloRHHalf.prime_hasSum φ hφ
  have hZ := MasulloRHHalf.zeros α hα φ hφ
  refine ⟨hI, hP.summable, hZ.summable, ?_⟩
  have h0 : ConnesRZ.mellinHat (fun x => φ (Real.exp x)) 0 = mellin φ (-1 / 2) := by
    rw [MasulloRHHalf.mellinHat_eq]; congr 1; ring
  have h1 : ConnesRZ.mellinHat (fun x => φ (Real.exp x)) 1 = mellin φ (1 / 2) := by
    rw [MasulloRHHalf.mellinHat_eq]; congr 1; ring
  rw [hIeq, hP.tsum_eq, hZ.tsum_eq, ConnesRZ.weilDistribution, h0, h1]
  ring

theorem solution (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    IntegrableOn (realTraceIntegrand φ) (Ioi 1) ∧
    Summable (primePowerTraceTerm φ) ∧
    Summable (zetaTraceTerm φ (1 / 2)) ∧
    (∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) +
      (∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i) =
      mellin φ (1 / 2) + mellin φ (-1 / 2) -
        ∑' ρ : ZetaZerosInTraceStrip (1 / 2), zetaTraceTerm φ (1 / 2) ρ :=
  MasulloRHHalf.main (1 / 2) le_rfl φ hφ
